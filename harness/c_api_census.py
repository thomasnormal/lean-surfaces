#!/usr/bin/env python3
"""Static census of the CPython C API surface used by candidate extension modules.

For each candidate module: every Py*/_Py*/METH_* identifier referenced by
Clang's AST or the source-attributed preprocessor stream, deduplicated, filtered
against the identifiers exposed by the pinned Include/ headers, bucketed; plus
libc calls, float usage, and file-scope mutable state. No C source text is
parsed with a hand-written regex.
"""
import hashlib
import json, re, sys, os
from pathlib import Path

from c_frontend import ast as clang_ast, source_macros, source_nodes, run as clang_run

SRC = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(os.environ.get("PYTHON39_SRC", "."))

MODULES = {
    "_bisect":      ["Modules/_bisectmodule.c"],
    "_heapq":       ["Modules/_heapqmodule.c"],
    "_struct":      ["Modules/_struct.c"],
    "binascii":     ["Modules/binascii.c"],
    "_json":        ["Modules/_json.c"],
    "_contextvars": ["Modules/_contextvarsmodule.c"],
    "context.c":    ["Python/context.c"],  # the real _contextvars implementation
    "_sre":         ["Modules/_sre.c", "Modules/sre.h", "Modules/sre_constants.h", "Modules/sre_lib.h"],
    "math":         ["Modules/mathmodule.c", "Modules/_math.c", "Modules/_math.h"],
    "_datetime":    ["Modules/_datetimemodule.c"],
    "_random":      ["Modules/_randommodule.c"],
    "zlib":         ["Modules/zlibmodule.c"],
    "_socket":      ["Modules/socketmodule.c", "Modules/socketmodule.h"],
}

# --- 1. API identifier universe: everything declared in Include/ ------------
if not (SRC / "Include").is_dir():
    raise SystemExit("c_api_census: source tree must contain Include/; "
                     "pass the pinned Python 3.9 tree explicitly")
headers = sorted(SRC.glob("Include/**/*.h"))
include_text = "\n".join('#include "%s"' % h for h in headers)
universe_pp = clang_run(["-E", "-dD", "-x", "c", "-"], input=include_text)
if universe_pp.returncode:
    raise SystemExit("c_api_census: clang could not preprocess Include/: " + universe_pp.stderr[:1000])
IDENT = re.compile(r"\b_?Py[A-Za-z0-9_]+\b|\bMETH_[A-Z_]+\b")
api_universe = set(IDENT.findall(universe_pp.stdout))
TMEMBER = set(re.findall(r"\bT_[A-Z_]+\b", universe_pp.stdout))

# --- 2. Buckets --------------------------------------------------------------
BUCKETS = [
    # (bucket, class, predicate) — first match wins
    ("core-substrate", "boilerplate", lambda s: s in ("PyObject","Py_ssize_t","Py_hash_t","Py_UNUSED","Py_STRINGIFY",
                                                  "Py_MIN","Py_MAX","Py_ARRAY_LENGTH","Py_SAFE_DOWNCAST","Py_UNREACHABLE",
                                                  "Py_BUILD_CORE_BUILTIN","Py_BUILD_CORE_MODULE","Py_DEBUG","Py_ALIGNED",
                                                  "PyListObject","PyLongObject","PyFloatObject","PyHamtObject",
                                                  "PyMappingMethods","PySequenceMethods","Py_IS_TYPE","Py_SET_TYPE")),
    ("c-utils",   "boilerplate", lambda s: s in ("Py_ISSPACE","Py_ISALNUM","Py_ISALPHA","Py_ISDIGIT","Py_ISLOWER",
                                                  "Py_ISUPPER","Py_TOLOWER","Py_TOUPPER","Py_CHARMASK")),
    ("interning", "boilerplate", lambda s: s == "_Py_IDENTIFIER"),
    ("argparse",  "boilerplate", lambda s: s.startswith(("PyArg_", "_PyArg_")) or s in ("Py_BuildValue", "Py_VaBuildValue",
                                                  "Py_CLEANUP_SUPPORTED")),
    ("refcount",  "boilerplate", lambda s: s in ("Py_INCREF","Py_DECREF","Py_XINCREF","Py_XDECREF","Py_CLEAR",
                                                  "Py_SETREF","Py_XSETREF","Py_REFCNT","Py_NewRef","_Py_NewRef")),
    ("typeobj/module", "boilerplate", lambda s: s.startswith(("PyModule", "PyModuleDef", "PyType_", "PyMODINIT",
                                                  "PyDoc_", "PyState_", "PyCFunction", "PyGetSetDef", "METH_",
                                                  "PyMethodDef", "PyMemberDef", "PyVarObject_HEAD", "PyObject_HEAD",
                                                  "_PyArg_UnpackKeywords"))
                                      or s in ("PyTypeObject","PyType_Ready","Py_TPFLAGS_DEFAULT","PyDescr_NewGetSet",
                                               "PyDescr_NewMethod","_PyType_Name","_PyType_GetModuleByDef")
                                      or s.startswith(("Py_TPFLAGS","Py_tp_","Py_nb_","Py_sq_","Py_mp_","Py_mod_"))),
    ("gil/thread", "boilerplate", lambda s: s.startswith(("PyGILState_","PyThread","PyEval_","PyThreadState"))
                                      or s in ("Py_BEGIN_ALLOW_THREADS","Py_END_ALLOW_THREADS",
                                               "Py_BLOCK_THREADS","Py_UNBLOCK_THREADS")),
    ("alloc/gc",  "boilerplate", lambda s: s.startswith(("PyMem_","PyObject_GC_","_PyObject_GC_","PyGC_"))
                                      or s in ("Py_VISIT","PyObject_New","PyObject_Del","PyObject_Free",
                                               "PyObject_Malloc","PyObject_Realloc","PyObject_INIT",
                                               "_PyObject_New","PyObject_IS_GC")),
    ("exceptions","semantic",    lambda s: s.startswith(("PyErr_","PyExc_","_PyErr_"))),
    ("numbers",   "semantic",    lambda s: s.startswith(("PyLong_","_PyLong_","PyFloat_","_PyFloat_","PyNumber_",
                                                  "PyBool_","PyIndex_","PyComplex_","_Py_dg_"))
                                      or s in ("Py_IS_NAN","Py_IS_INFINITY","Py_IS_FINITE","Py_HUGE_VAL",
                                               "Py_NAN","Py_MATH_PI","Py_MATH_E","_Py_SET_53BIT_PRECISION_HEADER",
                                               "_Py_SET_53BIT_PRECISION_START","_Py_SET_53BIT_PRECISION_END")),
    ("str/bytes", "semantic",    lambda s: s.startswith(("PyUnicode_","_PyUnicode","PyBytes_","_PyBytes",
                                                  "PyByteArray_","_PyByteArray","Py_UNICODE","Py_UCS"))),
    ("containers","semantic",    lambda s: s.startswith(("PyList_","PyTuple_","PyDict_","_PyDict_","PySet_",
                                                  "PyFrozenSet_","_PyTuple_","_PyList_","PySlice_"))),
    ("buffer",    "semantic",    lambda s: s.startswith(("PyBuffer_","PyBUF_")) or s in ("Py_buffer",
                                                  "PyObject_GetBuffer","PyObject_CheckBuffer","PyMemoryView_FromMemory")),
    ("objprotocol","semantic",   lambda s: s.startswith(("PyObject_","_PyObject_","PySequence_","PyMapping_",
                                                  "PyIter_","PyCallable_","PyCallIter_","PyWeakref_"))
                                      or s in ("Py_TYPE","Py_SIZE","Py_SET_SIZE","Py_None","Py_True","Py_False",
                                               "Py_NotImplemented","Py_RETURN_NONE","Py_RETURN_TRUE","Py_RETURN_FALSE",
                                               "Py_RETURN_NOTIMPLEMENTED","Py_RETURN_RICHCOMPARE","Py_EQ","Py_NE",
                                               "Py_LT","Py_LE","Py_GT","Py_GE","Py_EnterRecursiveCall",
                                               "Py_LeaveRecursiveCall","Py_ReprEnter","Py_ReprLeave")),
]

def classify(name):
    for bucket, klass, pred in BUCKETS:
        if pred(name): return bucket, klass
    return "misc/other", "semantic"

# --- 3. libc + float + state -------------------------------------------------
LIBC = ("memcpy memmove memset memcmp memchr strlen strcmp strncmp strcpy strncpy strchr strrchr strstr "
        "strcat strncat strtol strtoul strtod sprintf snprintf sscanf qsort abs labs malloc free realloc calloc "
        "floor ceil fabs fmod pow sqrt exp log log2 log10 log1p expm1 sin cos tan asin acos atan atan2 sinh cosh "
        "tanh asinh acosh atanh erf erfc lgamma tgamma hypot copysign round nextafter frexp ldexp modf isalpha "
        "isdigit isspace toupper tolower time localtime gmtime mktime strftime getenv").split()
def analyze(files):
    raw = "\n".join((SRC / f).read_text(errors="replace") for f in files)
    loc = sum(1 for line in raw.splitlines() if line.strip())
    refs, tmem, libc, floats, state = set(), set(), set(), 0, []
    for relative in files:
        path = SRC / relative
        tree = clang_ast(path)
        for node in source_nodes(tree, path):
            kind = node.get("kind")
            if kind == "DeclRefExpr":
                name = (node.get("referencedDecl") or {}).get("name")
                if name:
                    refs.add(name)
            if kind == "TypeRef":
                name = node.get("name")
                if name:
                    refs.add(name)
            if kind == "CallExpr":
                kids = [c for c in (node.get("inner") or []) if isinstance(c, dict)]
                head = kids[0] if kids else {}
                while head.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
                    head = next((c for c in (head.get("inner") or []) if isinstance(c, dict)), {})
                name = (head.get("referencedDecl") or {}).get("name")
                if name in LIBC:
                    libc.add(name)
            if kind == "FloatingLiteral":
                floats += 1
            qual = (node.get("type") or {}).get("qualType", "")
            if "float" in qual or "double" in qual:
                floats += 1
            if kind == "VarDecl" and node.get("storageClass") == "static":
                if "const" not in qual and node.get("name"):
                    state.append(node["name"])
        for macro in source_macros(path):
            refs.update(IDENT.findall(macro))
            tmem.update(re.findall(r"\bT_[A-Z_]+\b", macro))
    refs &= api_universe
    tmem &= TMEMBER
    buckets, semantic, boiler = {}, set(), set()
    for name in refs:
        b, k = classify(name)
        buckets.setdefault(b, []).append(name)
        (semantic if k == "semantic" else boiler).add(name)
    return {
        "files": files, "loc_nonblank": loc,
        "api_total": len(refs) + len(tmem),
        "api_semantic": sorted(semantic),
        "api_boilerplate": sorted(boiler | tmem),
        "buckets": {b: sorted(v) for b, v in sorted(buckets.items())},
        "libc": sorted(libc), "float_mentions": floats,
        "static_mutable": sorted(set(state)),
    }

analyzed = {m: analyze(fs) for m, fs in MODULES.items()}

# --- union curve: greedy best-first over SEMANTIC api names, bridgeable set --
CURVE_SET = ["_bisect", "_heapq", "_contextvars", "_struct", "binascii", "_json", "_random", "_sre"]
remaining, covered, curve = set(CURVE_SET), set(), []
while remaining:
    best = min(remaining, key=lambda m: (len(set(analyzed[m]["api_semantic"]) - covered), m))
    new = set(analyzed[best]["api_semantic"]) - covered
    covered |= new
    curve.append({"module": best, "new_semantic": len(new), "union": len(covered)})
    remaining.discard(best)

# --- census join: files import-clean when strict_c ⊆ executed set -----------
census = json.load(open(Path(__file__).resolve().parent.parent / "docs/import-ceiling-census.json"))
rows = census["rows"]
def clean(S):
    return sorted(r["module"] for r in rows if r["verdict"] in ("C-BLOCKED","PURE-ACCEL")
                  and set(r["strict_c"]) <= S)
CAND = {"_bisect","_heapq","_struct","binascii","_json","_contextvars","_sre","_random","_datetime"}
INTR = {"sys","_locale"}  # the intrinsics memo's pass-2 constant slice
joins = {}
S = set()
for step in ["_contextvars","_struct","_sre","_heapq","_bisect","_json","binascii","_random","_datetime"]:
    S = S | {step}
    joins["+" + step] = clean(set(S))
joins["all-9"] = clean(set(CAND))
joins["all-9 + intrinsics(sys,_locale)"] = clean(CAND | INTR)
joins["all-9 + sys,_locale,builtins,itertools,_weakref"] = clean(CAND | INTR | {"builtins","itertools","_weakref"})

# Provenance is COMPUTED from the tree actually read, never transcribed: a
# hardcoded sha is a claim about a file this run may not have opened.

def _tree_sha256(root):
    """A deterministic digest of the tree actually read: every regular file's
    path and bytes, in sorted path order.  Replaces a transcribed constant
    that described a tarball this script never opens."""
    h = hashlib.sha256()
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames.sort()
        for name in sorted(filenames):
            fp = os.path.join(dirpath, name)
            rel = os.path.relpath(fp, root)
            h.update(rel.encode("utf-8", "replace"))
            try:
                with open(fp, "rb") as fh:
                    h.update(fh.read())
            except OSError as e:
                raise SystemExit("c_api_census: cannot read %s: %s" % (fp, e))
    return h.hexdigest()


result = {"source": os.path.basename(os.path.normpath(SRC)),
          "sha256": _tree_sha256(SRC),
          "api_universe_size": len(api_universe),
          "modules": analyzed,
          "semantic_union_curve": curve,
          "import_clean_join": joins}

out = Path(sys.argv[2]) if len(sys.argv) > 2 else Path("c-extension-bridge-census.json")
out.write_text(json.dumps(result, indent=1))

# summary table
print(f"{'module':14} {'LoC':>5} {'API':>4} {'sem':>4} {'boil':>4} {'libc':>4} {'flt':>4} {'state':>5}")
for m, r in result["modules"].items():
    print(f"{m:14} {r['loc_nonblank']:>5} {r['api_total']:>4} {len(r['api_semantic']):>4} "
          f"{len(r['api_boilerplate']):>4} {len(r['libc']):>4} {r['float_mentions']:>4} {len(r['static_mutable']):>5}")
print("\nunion curve:")
for c in curve: print(f"  {c['module']:14} +{c['new_semantic']:>3} -> {c['union']}")
print("\njoins:")
for k, v in joins.items(): print(f"  {k:45} {len(v):>3}  {v}")
