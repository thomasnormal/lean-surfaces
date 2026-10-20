#!/usr/bin/env python3
"""Focused tooling tests, not C++ semantic admission or execution tests.

Run explicitly with LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY set to the
matching frontend and built probe library. No build or CI registration occurs.
Temporary translation fixtures establish tooling behavior only.
"""

import importlib.util
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import unittest


PRICING_SPEC = importlib.util.spec_from_file_location(
    "cpp_canonical_probe_pricing_under_test", pathlib.Path(__file__).with_name("price_declarations.py"),
)
pricing = importlib.util.module_from_spec(PRICING_SPEC)
sys.modules[PRICING_SPEC.name] = pricing
PRICING_SPEC.loader.exec_module(pricing)

SOURCE = """namespace model {
struct Box;
struct Box {
    Box() = default;
    Box(const Box&) = delete;
    int read() const;
};
int Box::read() const { return 7; }
int pick(int);
int pick(double);
int pick(int value) { return value; }
int pick(double value) { return static_cast<int>(value); }
extern int declaration_only;
int defined = 3;
extern "C" {
    int c_function(int);
    extern int c_variable;
}
}
namespace model {
int c_function(int value) { return value; }
int another() { return 11; }
}
"""

TEMPLATE_SOURCE = """namespace evidence {
int plain(int);
int plain(int value) { return value; }
extern int global_value;
int global_value = 3;
struct Ordinary;
struct Ordinary {};
enum Tag { tag };
template<class Type> Type templated(Type value) { return value; }
template<> int templated<int>(int value) { return value; }
int use_templated() { return static_cast<int>(templated(1.0)); }
template<class Type> int variable = 1;
template<> int variable<int> = 2;
int use_variable() { return variable<double>; }
template<class Type> struct Record { Type item; };
template<> struct Record<int> { int item; };
Record<double> instance;
template<class Type> struct Outer {
    static int member;
    struct Nested { Type value; };
    enum MemberEnum { member_value };
    int plain_member() { return 1; }
    template<class Value> Value member_template(Value value) { return value; }
};
template<class Type> int Outer<Type>::member = 1;
template<> int Outer<int>::member = 2;
Outer<int>::Nested nested_instance;
Outer<int>::MemberEnum enum_instance = Outer<int>::member_value;
int member_call() {
    Outer<int> value;
    return value.member_template(3) + value.plain_member() + Outer<double>::member;
}
template<class Type> using Alias = Record<Type>;
Alias<char> alias_instance;
}
"""

MEMBER_ENUM_SOURCE = """template<class Element> struct Box {
    enum Implicit : int { zero };
    enum Specialized : int;
};
Box<int>::Implicit ordinary_value;
template<> enum Box<int>::Specialized : int { one };
"""

FUNCTION_SHAPE_SOURCE = """int later_body(int);
int later_body(int value) { return value; }
int try_body(int value) try { return value; } catch (...) { return -1; }
int deleted_function(int) = delete;
[[deprecated]] int attributed_declaration(int);
[[nodiscard]] int attributed_body(int value) { return value; }
int alias_target() { return 1; }
[[gnu::alias("_Z12alias_targetv")]] int defining_attribute();
"""

TYPE_EVIDENCE_SOURCE = """struct Box { int field; };
enum Color { red };
int scalar;
const int qualified = 0;
volatile int volatile_qualified;
int *pointer;
int &reference = scalar;
int &&rreference = 0;
Box box;
Color color = red;
int callable(int value, Box *box);
int variadic(int value, ...);
"""

EXPRESSION_EVIDENCE_SOURCE = """int add(int left, int right) { return left + right; }
short narrow(short left, short right) { return left + right; }
int run() { int value = add(1, 2); return value * 3; }
"""

OUT_OF_DUMP_EXPRESSION_SOURCE = """int buffer[1 + 1];
int identity(int value) { return value; }
"""

POINTER_ID = re.compile(r"0x[0-9a-fA-F]+\Z")
DECLARATION_KINDS = {
    "NamespaceDecl", "CXXRecordDecl", "CXXMethodDecl", "CXXConstructorDecl",
    "FunctionDecl", "VarDecl",
}


def normalize_pointers(value):
    identifiers = {}

    def normalize(current):
        if isinstance(current, dict):
            return {key: normalize(child) for key, child in current.items()}
        if isinstance(current, list):
            return [normalize(child) for child in current]
        if isinstance(current, str) and POINTER_ID.fullmatch(current):
            if current not in identifiers:
                identifiers[current] = "declaration-{}".format(len(identifiers))
            return identifiers[current]
        return current

    return normalize(value)


def declaration_occurrences(ast):
    occurrences = {}
    pending = [(ast, ())]
    while pending:
        node, path = pending.pop()
        if isinstance(node, dict):
            kind = node.get("kind")
            identifier = node.get("id")
            if isinstance(kind, str) and kind.endswith("Decl") and isinstance(identifier, str):
                occurrences.setdefault(identifier, []).append((path, node))
            for key, child in reversed(list(node.items())):
                pending.append((child, path + (key,)))
        elif isinstance(node, list):
            for index, child in reversed(list(enumerate(node))):
                pending.append((child, path + (index,)))
    return occurrences


def witnessed_relationships(probe):
    occurrences = declaration_occurrences(probe["ast"])

    def witness(identifier):
        if identifier is None:
            return ("no-reference",)
        matches = occurrences.get(identifier, [])
        if not matches:
            return ("unindexed-reference",)
        return tuple(path for path, node in matches)

    result = []
    for record in probe["metadata"]["declarations"]:
        if record.get("kind") not in DECLARATION_KINDS:
            continue
        if record.get("name") not in {
            "model", "Box", "read", "pick", "declaration_only", "defined",
            "c_function", "c_variable", "another",
        }:
            continue
        relationships = tuple(
            (field, witness(record.get(field)))
            for field in (
                "canonical", "previous", "semantic_context", "lexical_context",
                "original_namespace", "represented_class",
            )
        )
        result.append((
            witness(record["id"]), record["kind"], record.get("name"),
            record["implicit"], record.get("injected_class_name"), relationships,
            record["definition"], record.get("variable_definition_kind"),
            record.get("language_linkage"),
        ))
    return result


class CanonicalProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        requested = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            raise RuntimeError("set LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY explicitly")
        cls.clang = shutil.which(requested)
        cls.library = pathlib.Path(library).resolve()
        if cls.clang is None or not cls.library.is_file():
            raise RuntimeError("the selected frontend and compiled probe library must exist")

    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-canonical-probe-test-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)
        self.source = self.root / "input.cpp"
        self.source.write_text(SOURCE, encoding="utf-8")

    def run_frontend(self, plugin=True, plugin_arguments=(), library=None,
                     frontend_arguments=()):
        arguments = [
            self.clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", "-x", "c++", str(self.source),
        ]
        arguments.extend(frontend_arguments)
        if plugin:
            arguments.extend([
                "-Xclang", "-load", "-Xclang", str(library or self.library),
                "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
            ])
            for argument in plugin_arguments:
                arguments.extend([
                    "-Xclang", "-plugin-arg-leancpp-canonical-probe", "-Xclang", argument,
                ])
        else:
            arguments.extend(["-Xclang", "-ast-dump=json"])
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        return subprocess.run(
            arguments, cwd=self.root, env=environment, capture_output=True,
            text=True, timeout=30,
        )

    def probe(self):
        result = self.run_frontend()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout, "a successful probe must publish its evidence")
        return json.loads(result.stdout)

    def records(self, probe, kind, name):
        records = [
            record for record in probe["metadata"]["declarations"]
            if record["kind"] == kind and record.get("name") == name
        ]
        self.assertTrue(records, "no {} records for {}".format(kind, name))
        return records

    def template_probe(self):
        self.source.write_text(TEMPLATE_SOURCE, encoding="utf-8")
        return self.probe()

    def test_method_static_getter_covers_declarations_and_out_of_line_bodies(self):
        self.source.write_text("""struct Methods {
  static int inline_static(int value) { return value; }
  static int outside(int value);
  int instance(int value) { return value; }
  virtual int dynamic(int value) { return value; }
};
int Methods::outside(int value) { return value; }
""", encoding="utf-8")
        probe = self.probe()
        methods = [row for row in probe["metadata"]["declarations"]
                   if row["kind"] == "CXXMethodDecl" and row.get("name") in
                   {"inline_static", "outside", "instance", "dynamic"}]
        self.assertEqual(len(methods), 5)
        for row in methods:
            self.assertEqual(row["method_static_api"], "CXXMethodDecl.isStatic")
            self.assertIs(row["method_static"], row["name"] in {"inline_static", "outside"})
        outside = [row for row in methods if row["name"] == "outside"]
        definition = next(row for row in outside if row["body_present"])
        self.assertNotEqual(definition["id"], definition["canonical"])
        self.assertIsNotNone(definition["previous"])
        self.assertEqual(next(row for row in outside if not row["body_present"])["id"],
                         definition["canonical"])

    def test_function_origins_use_physical_expansion_and_spelling_locations(self):
        header = self.root / "origin.h"
        header.write_text('''inline int dependency() { return 1; }
#define DECLARE_FUNCTION int from_macro() { return 2; }
''', encoding="utf-8")
        source = '''#include "origin.h"
DECLARE_FUNCTION
#line 900 "pretend.cpp"
int ordinary() { return dependency(); }
struct Box { int method() { return 3; } };
'''
        self.source.write_text(source, encoding="utf-8")
        probe = self.probe()
        for kind, name, expansion_file, spelling_file in (
            ("FunctionDecl", "dependency", header, header),
            ("FunctionDecl", "from_macro", self.source, header),
            ("FunctionDecl", "ordinary", self.source, self.source),
            ("CXXMethodDecl", "method", self.source, self.source),
        ):
            with self.subTest(name=name):
                row, = self.records(probe, kind, name)
                self.assertEqual(row["source_origin_api"],
                                 "SourceManager expansion/spelling file locations v1")
                for mode, expected in (("expansion", expansion_file), ("spelling", spelling_file)):
                    location = row["source_origin"][mode]
                    self.assertEqual(pathlib.Path(location["file"]).resolve(), expected.resolve())
                    self.assertIs(type(location["offset"]), int)
                    self.assertLess(location["offset"], expected.stat().st_size)
                    token = "DECLARE_FUNCTION" if name == "from_macro" and mode == "expansion" else name
                    self.assertTrue(expected.read_bytes()[location["offset"]:].startswith(token.encode()))

    def assert_specialization_api(self, record, family):
        self.assertIs(type(record["template_specialization_kind"]), int)
        self.assertIn(record["template_specialization_kind"], range(5))
        self.assertEqual(record["template_specialization_kind_api"],
                         family + ".getTemplateSpecializationKind")

    def assert_function_shape_api(self, record):
        for field, api in (
            ("function_has_skipped_body", "FunctionDecl.hasSkippedBody"),
            ("function_will_have_body", "FunctionDecl.willHaveBody"),
            ("function_has_defining_attr", "FunctionDecl.hasDefiningAttr"),
            ("function_late_template_parsed", "FunctionDecl.isLateTemplateParsed"),
            ("function_explicitly_defaulted", "FunctionDecl.isExplicitlyDefaulted"),
        ):
            self.assertIs(type(record[field]), bool)
            self.assertEqual(record[field + "_api"], api)
        self.assertIs(type(record["function_attribute_count"]), int)
        self.assertGreaterEqual(record["function_attribute_count"], 0)
        self.assertEqual(record["function_attribute_count_api"], "Decl.hasAttrs/Decl.getAttrs.size")
        self.assertEqual(record["own_body_api"], "FunctionDecl.getBody")

    def variable_probe(self):
        self.source.write_text("""struct Pair { int first; int second; };
int global;
extern int external;
thread_local int tls_global = 1;
int forms(short value = 1) {
  int copy = value, direct(value), list{value}, copy_list = {value}, zero{}, uninitialized;
  const int constant = 1;
  constexpr int fixed = 2;
  volatile int observed = value;
  auto inferred = value;
  static int persistent = value;
  thread_local int per_thread = value;
  extern int imported;
  int &reference = copy;
  int array[2] = {value};
  Pair aggregate(1, 2);
  [[maybe_unused]] int attributed = 1;
  { int copy = 3; }
  return copy;
}
""", encoding="utf-8")
        probe = self.probe()
        metadata = probe["metadata"]
        self.assertEqual(metadata["variable_evidence_api"],
                         "Clang::VarDecl storage and initializer projection v1")
        declarations = {row["id"]: row for row in metadata["declarations"]}
        rows = {}
        for row in metadata["variable_evidence"]:
            rows.setdefault(declarations[row["occurrence"]].get("name", ""), []).append(row)
            self.assertEqual(row["canonical"], declarations[row["occurrence"]]["canonical"])
            self.assertEqual(row["kind"], declarations[row["occurrence"]]["kind"])
        return probe, rows

    def test_variable_storage_duration_tls_and_parameter_roles(self):
        _, rows = self.variable_probe()
        for name, local, parameter, storage, duration, tls in (
            ("global", False, False, "none", "static", "none"),
            ("external", False, False, "extern", "static", "none"),
            ("tls_global", False, False, "none", "thread", "dynamic"),
            ("value", False, True, "none", "automatic", "none"),
            ("direct", True, True, "none", "automatic", "none"),
            ("persistent", True, True, "static", "static", "none"),
            ("per_thread", True, True, "none", "thread", "dynamic"),
            ("imported", True, True, "extern", "static", "none"),
        ):
            with self.subTest(name=name):
                row = rows[name][0]
                self.assertEqual((row["local"], row["local_or_parameter"],
                                  row["storage_class"], row["storage_duration"], row["tls"]),
                                 (local, parameter, storage, duration, tls))

    def test_variable_initializer_styles_and_source_converted_types(self):
        probe, rows = self.variable_probe()
        nodes = {}
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if isinstance(node, dict):
                if "id" in node:
                    nodes[node["id"]] = node
                pending.extend(node.get("inner", []))
        for name, style, kind in (
            ("copy", "c", "ImplicitCastExpr"), ("direct", "call", "ImplicitCastExpr"),
            ("list", "list", "InitListExpr"), ("copy_list", "c", "InitListExpr"),
            ("zero", "list", "InitListExpr"),
            ("aggregate", "paren-list", "CXXParenListInitExpr"),
        ):
            row = rows[name][0]
            self.assertTrue(row["has_initializer"])
            self.assertEqual(row["init_style"], style)
            self.assertEqual(row["initializer"]["kind"], kind)
            node = nodes[row["occurrence"]]
            self.assertEqual(node["init"], style)
            self.assertEqual(node["inner"][0]["id"], row["initializer"]["occurrence"])
        for name in ("global", "external", "uninitialized", "imported"):
            self.assertFalse(rows[name][0]["has_initializer"])
            self.assertIsNone(rows[name][0]["initializer"])
        converted = rows["direct"][0]["initializer"]
        self.assertEqual(converted["source"], {"kind": "builtin", "name": "short"})
        self.assertEqual(converted["type"], {"kind": "builtin", "name": "int"})
        self.assertTrue(rows["value"][0]["has_initializer"])

    def test_variable_qualifiers_attributes_and_shadowing_are_retained(self):
        probe, rows = self.variable_probe()
        types = {row["occurrence"]: row["type"] for row in probe["metadata"]["type_evidence"]}
        self.assertEqual(types[rows["constant"][0]["occurrence"]]["const"], True)
        self.assertEqual(types[rows["observed"][0]["occurrence"]]["volatile"], True)
        self.assertEqual(types[rows["reference"][0]["occurrence"]]["kind"], "lvalue-reference")
        self.assertEqual(types[rows["inferred"][0]["occurrence"]], {"kind": "builtin", "name": "short"})
        self.assertTrue(rows["fixed"][0]["constexpr"])
        self.assertEqual(rows["attributed"][0]["attribute_count"], 1)
        self.assertEqual(len(rows["copy"]), 2)
        self.assertEqual(len({row["occurrence"] for row in rows["copy"]}), 2)

    def test_initializer_subexpression_types_preserve_unary_operand_conversions(self):
        self.source.write_text("""int logical() { int local = !2; return local; }
int promoted() { short small = -32768; int local = -small; return local; }
""", encoding="utf-8")
        probe = self.probe()
        nodes = {}
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            nodes[node["id"]] = node
            pending.extend(child for child in node.get("inner", []) if "id" in child)
        observed = []
        for row in probe["metadata"]["variable_evidence"]:
            initializer = row["initializer"]
            self.assertEqual(initializer["expression_types_api"],
                             "Clang::Expr initializer type projection v1")
            types = {item["occurrence"]: item for item in initializer["expression_types"]}
            self.assertEqual(types[initializer["occurrence"]]["type"], initializer["type"])
            for occurrence, item in types.items():
                node = nodes[occurrence]
                self.assertEqual(item["kind"], node["kind"])
                if node["kind"] == "UnaryOperator":
                    operand = node["inner"][0]
                    observed.append((node["opcode"], item["type"]["name"],
                                     types[operand["id"]]["type"]["name"]))
        self.assertIn(("!", "bool", "bool"), observed)
        self.assertIn(("-", "int", "int"), observed)
        self.assertTrue(any(node.get("castKind") == "IntegralCast" and
                            node["type"]["qualType"] == "int" for node in nodes.values()))

    def test_expression_types_preserve_callable_promotions_and_refusals(self):
        self.source.write_text("""bool negated(short value) { return -value; }
bool complemented(unsigned char value) { return ~value; }
int promoted(bool value) { return +value; }
long wide() { return 4294967296L; }
bool flag() { return true; }
float floating(float value) { return -value; }
""", encoding="utf-8")
        probe = self.probe()
        self.assertEqual(probe["metadata"]["expression_types_api"],
                         "Clang::Expr type projection v1")
        nodes = {}
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "id" in node:
                nodes[node["id"]] = node
            pending.extend(node.get("inner", []))
        rows = probe["metadata"]["expression_types"]
        types = {row["occurrence"]: row for row in rows}
        self.assertTrue(rows)
        for row in rows:
            self.assertEqual(nodes[row["occurrence"]]["kind"], row["kind"])
        unary = [row for row in rows if row["kind"] == "UnaryOperator"]
        self.assertEqual(len(unary), 3)
        for row in unary:
            self.assertEqual(row["type"], {"kind": "builtin", "name": "int"})
            operand = nodes[row["occurrence"]]["inner"][0]
            self.assertEqual(operand["castKind"], "IntegralCast")
            self.assertEqual(types[operand["id"]]["type"], row["type"])
        self.assertTrue(any(row["kind"] == "CXXBoolLiteralExpr" and
                            row["type"] == {"kind": "builtin", "name": "bool"}
                            for row in rows))
        self.assertTrue(any(row["kind"] == "IntegerLiteral" and
                            row["type"] == {"kind": "builtin", "name": "long"}
                            for row in rows))
        refused = probe["metadata"]["expression_type_refusals"]
        self.assertTrue(any(row["kind"] == "UnaryOperator" and
                            not row["projection_supported"] for row in refused))

    def test_variable_unsupported_types_and_pending_defaults_are_explicit_refusals(self):
        probe, rows = self.variable_probe()
        self.assertNotIn("array", rows)
        declarations = {row["id"]: row for row in probe["metadata"]["declarations"]}
        refused = probe["metadata"]["variable_refusals"]
        array = next(row for row in refused
                     if declarations[row["occurrence"]].get("name") == "array")
        self.assertTrue(array["dump_visible"])
        self.assertFalse(array["projection_supported"])
        self.source.write_text("""template<class T> struct Defaults {
  void method(int value = T::value);
};
Defaults<int> object;
template<class T> int dependent(T value) { T local = value; return 1; }
""", encoding="utf-8")
        probe = self.probe()
        refused = probe["metadata"]["variable_refusals"]
        self.assertTrue(refused)
        self.assertTrue(any("uninstantiated" in row["reason"] for row in refused))
        self.assertTrue(any("type/shape" in row["reason"] for row in refused))

    def test_schema_and_frontend_versions_are_explicit(self):
        probe = self.probe()
        metadata = probe["metadata"]
        self.assertEqual(metadata["schema_version"], "cpp-canonical-probe-0.3")
        self.assertTrue(metadata["compiled_frontend"])
        self.assertIn(metadata["compiled_frontend"], metadata["runtime_frontend"])
        self.assertTrue(metadata["llvm_headers"])
        self.assertEqual(probe["ast"]["kind"], "TranslationUnitDecl")

    def test_structured_type_rows_are_clang_witnessed_and_recursive(self):
        self.source.write_text(TYPE_EVIDENCE_SOURCE, encoding="utf-8")
        probe = self.probe()
        metadata = probe["metadata"]
        self.assertEqual(metadata["type_evidence_api"],
                         "Clang::QualType structured type projection v1")
        rows = metadata["type_evidence"]
        self.assertTrue(rows)
        declarations = metadata["declarations"]
        by_name = {}
        for declaration in declarations:
            if declaration.get("name"):
                by_name.setdefault(declaration["name"], set()).add(declaration["id"])
        rows_by_occurrence = {row["occurrence"]: row for row in rows}

        def declaration_id(name, kind):
            return next(record["id"] for record in declarations
                        if record.get("name") == name and record["kind"] == kind)

        def row_for(name, kind="VarDecl"):
            return rows_by_occurrence[declaration_id(name, kind)]

        self.assertEqual(row_for("scalar")["type"],
                         {"kind": "builtin", "name": "int"})
        self.assertEqual(row_for("qualified")["type"], {
            "kind": "qualified", "const": True, "volatile": False,
            "base": {"kind": "builtin", "name": "int"},
        })
        self.assertEqual(row_for("volatile_qualified")["type"], {
            "kind": "qualified", "const": False, "volatile": True,
            "base": {"kind": "builtin", "name": "int"},
        })
        self.assertEqual(row_for("pointer")["type"], {
            "kind": "pointer", "pointee": {"kind": "builtin", "name": "int"},
        })
        self.assertEqual(row_for("reference")["type"], {
            "kind": "lvalue-reference", "referent": {"kind": "builtin", "name": "int"},
        })
        self.assertEqual(row_for("rreference")["type"], {
            "kind": "rvalue-reference", "referent": {"kind": "builtin", "name": "int"},
        })
        box_ids = by_name["Box"]
        self.assertIn(row_for("box")["type"]["declaration"], box_ids)
        self.assertEqual(row_for("box")["type"]["kind"], "record")
        self.assertEqual(row_for("color")["type"]["kind"], "enumeration")
        self.assertIn(row_for("color")["type"]["declaration"], by_name["Color"])
        function = row_for("callable", "FunctionDecl")["type"]
        self.assertEqual(function["kind"], "function")
        self.assertEqual(function["result"], {"kind": "builtin", "name": "int"})
        self.assertEqual(function["parameters"][0], {"kind": "builtin", "name": "int"})
        self.assertEqual(function["parameters"][1]["kind"], "pointer")
        self.assertEqual(function["parameters"][1]["pointee"]["kind"], "record")
        self.assertIn(function["parameters"][1]["pointee"]["declaration"], box_ids)
        variadic = row_for("variadic", "FunctionDecl")["type"]
        self.assertTrue(variadic["variadic"])
        self.assertEqual(variadic["parameters"], [{"kind": "builtin", "name": "int"}])
        for row in rows:
            self.assertIn(row["occurrence"], {record["id"] for record in declarations})
            self.assertNotIn("qualType", json.dumps(row))

    def test_binary_expression_rows_bind_ordered_operands_to_ast(self):
        self.source.write_text(EXPRESSION_EVIDENCE_SOURCE, encoding="utf-8")
        probe = self.probe()
        metadata = probe["metadata"]
        self.assertEqual(metadata["expression_evidence_api"],
                         "Clang::BinaryOperator typed operand projection v2")
        rows = metadata["expression_evidence"]
        self.assertEqual([row["operator"] for row in rows], ["+", "+", "*"])
        ast_nodes = {}

        def walk(node):
            if isinstance(node, dict):
                if isinstance(node.get("id"), str):
                    ast_nodes[node["id"]] = node
                for child in node.values():
                    walk(child)
            elif isinstance(node, list):
                for child in node:
                    walk(child)

        walk(probe["ast"])
        for row in rows:
            node = ast_nodes[row["occurrence"]]
            self.assertEqual(node["kind"], "BinaryOperator")
            self.assertEqual(node["opcode"], row["operator"])
            self.assertEqual(len(row["operands"]), 2)
            self.assertEqual([child["id"] for child in node["inner"]],
                             [operand["occurrence"] for operand in row["operands"]])
            source_name = row["operands"][0]["source"]["name"]
            for operand in row["operands"]:
                self.assertEqual(operand["source"], {"kind": "builtin", "name": source_name})
                self.assertEqual(operand["type"], {"kind": "builtin", "name": "int"})
            self.assertEqual(row["result"], {"kind": "builtin", "name": "int"})
            self.assertNotIn("qualType", json.dumps(row))
        self.assertEqual(metadata["expression_refusals"], [])

        narrow = next(row for row in rows if row["operator"] == "+" and
                      row["operands"][0]["source"]["name"] == "short")
        self.assertEqual([operand["source"] for operand in narrow["operands"]],
                         [{"kind": "builtin", "name": "short"}] * 2)
        self.assertEqual([operand["type"] for operand in narrow["operands"]],
                         [{"kind": "builtin", "name": "int"}] * 2)

    def test_compound_assignments_keep_binary_family_evidence_and_exact_ast_kind(self):
        self.source.write_text(
            "int compound(int value) { value += 1; return value; }\n"
            "short narrow(short value) { value += 1; return value; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        rows = probe["metadata"]["expression_evidence"]
        self.assertEqual(len(rows), 2)
        nodes = {}
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "id" in node:
                nodes[node["id"]] = node
            pending.extend(node.get("inner", []))
        for row, type_name in zip(rows, ("int", "short")):
            node = nodes[row["occurrence"]]
            self.assertEqual(row["kind"], "BinaryOperator")
            self.assertEqual(node["kind"], "CompoundAssignOperator")
            self.assertEqual(row["operator"], "+=")
            self.assertEqual(node["opcode"], row["operator"])
            self.assertEqual(row["result"], {"kind": "builtin", "name": type_name})
            self.assertEqual(row["operands"][0]["source"], row["result"])
            self.assertEqual(row["operands"][0]["type"], row["result"])
            self.assertEqual([child["id"] for child in node["inner"]],
                             [operand["occurrence"] for operand in row["operands"]])
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_increment_unary_nodes_preserve_prefix_and_postfix_flags(self):
        self.source.write_text(
            "int pre(int value) { return ++value; }\n"
            "int post(int value) { return value++; }\n"
            "int dec(int value) { value--; return value; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        nodes = {}
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "id" in node:
                nodes[node["id"]] = node
            pending.extend(node.get("inner", []))
        increments = [node for node in nodes.values()
                      if node.get("kind") == "UnaryOperator"]
        self.assertEqual({(node["opcode"], node["isPostfix"]) for node in increments},
                         {("++", False), ("++", True), ("--", True)})
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_conditional_expression_retains_three_ordered_children(self):
        self.source.write_text(
            "int select(int value) { return value ? 7 : 3; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        nodes = {}
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "id" in node:
                nodes[node["id"]] = node
            pending.extend(node.get("inner", []))
        conditionals = [node for node in nodes.values()
                        if node.get("kind") == "ConditionalOperator"]
        self.assertEqual(len(conditionals), 1)
        self.assertEqual(len(conditionals[0].get("inner", [])), 3)
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_comma_expression_is_a_binary_node_with_ordered_children(self):
        self.source.write_text(
            "int comma(int value) { return value++, value; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        nodes = {}
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "id" in node:
                nodes[node["id"]] = node
            pending.extend(node.get("inner", []))
        commas = [node for node in nodes.values()
                  if node.get("kind") == "BinaryOperator" and node.get("opcode") == ","]
        self.assertEqual(len(commas), 1)
        self.assertEqual(len(commas[0].get("inner", [])), 2)
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_for_statement_retains_initializer_condition_step_and_body(self):
        self.source.write_text(
            "int for_loop(int value) { for (value = 0; value < 3; ++value) { value += 1; } return value; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        nodes = {}
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "id" in node:
                nodes[node["id"]] = node
            pending.extend(node.get("inner", []))
        loops = [node for node in nodes.values() if node.get("kind") == "ForStmt"]
        self.assertEqual(len(loops), 1)
        self.assertEqual(len(loops[0].get("inner", [])), 5)
        self.assertEqual(loops[0]["inner"][1], {})
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_for_loop_transfers_retain_body_nodes(self):
        self.source.write_text(
            "int for_break_loop(int value) { for (value = 0; value < 3; ++value) { ++value; break; } return value; }\n"
            "int for_continue_loop(int value) { for (value = 0; value < 3; ++value) { continue; } return value; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        loops = []
        nodes = []
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "kind" in node:
                nodes.append(node)
            if node.get("kind") == "ForStmt":
                loops.append(node)
            pending.extend(node.get("inner", []))
        self.assertEqual(len(loops), 2)
        for loop in loops:
            self.assertEqual(len(loop.get("inner", [])), 5)
            self.assertEqual(loop["inner"][1], {})
            self.assertEqual(loop["inner"][4].get("kind"), "CompoundStmt")
        self.assertEqual(sum(node.get("kind") == "BreakStmt" for node in nodes), 1)
        self.assertEqual(sum(node.get("kind") == "ContinueStmt" for node in nodes), 1)
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_switch_case_default_nodes_retain_order(self):
        self.source.write_text(
            "int switch_select(int value) { switch (value) { case 0: return 4; case 1: return 5; default: return 6; } return 7; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        switches = []
        nodes = []
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "kind" in node:
                nodes.append(node)
            if node.get("kind") == "SwitchStmt":
                switches.append(node)
            pending.extend(node.get("inner", []))
        self.assertEqual(len(switches), 1)
        self.assertEqual([child.get("kind") for child in switches[0]["inner"]],
                         ["ImplicitCastExpr", "CompoundStmt"])
        switch_body = switches[0]["inner"][1]
        self.assertEqual([child.get("kind") for child in switch_body["inner"]],
                         ["CaseStmt", "CaseStmt", "DefaultStmt"])
        self.assertEqual(sum(node.get("kind") == "CaseStmt" for node in nodes), 2)
        self.assertEqual(sum(node.get("kind") == "DefaultStmt" for node in nodes), 1)
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_loop_transfers_are_retained_as_distinct_statement_nodes(self):
        self.source.write_text(
            "int break_loop(int value) { while (value < 3) { ++value; break; } return value; }\n"
            "int continue_loop(int value) { while (value < 3) { ++value; continue; } return value; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        nodes = []
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "kind" in node:
                nodes.append(node["kind"])
            pending.extend(node.get("inner", []))
        self.assertEqual(nodes.count("BreakStmt"), 1)
        self.assertEqual(nodes.count("ContinueStmt"), 1)
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_do_loop_transfers_keep_body_then_condition_order(self):
        self.source.write_text(
            "int do_break_loop(int value) { do { ++value; break; } while (value < 3); return value; }\n"
            "int do_continue_loop(int value) { do { ++value; continue; } while (value < 3); return value; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        loops = []
        nodes = []
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if "kind" in node:
                nodes.append(node)
            if node.get("kind") == "DoStmt":
                loops.append(node)
            pending.extend(node.get("inner", []))
        self.assertEqual(len(loops), 2)
        for loop in loops:
            self.assertEqual([child.get("kind") for child in loop.get("inner", [])],
                             ["CompoundStmt", "BinaryOperator"])
            self.assertEqual(loop["inner"][1].get("opcode"), "<")
        self.assertEqual(sum(node.get("kind") == "BreakStmt" for node in nodes), 1)
        self.assertEqual(sum(node.get("kind") == "ContinueStmt" for node in nodes), 1)
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_logical_effectful_right_operands_keep_boolean_casts(self):
        self.source.write_text(
            "bool both_increment(int value) { return value && ++value; }\n"
            "bool either_increment(int value) { return value || ++value; }\n",
            encoding="utf-8",
        )
        probe = self.probe()
        logicals = []
        pending = [probe["ast"]]
        while pending:
            node = pending.pop()
            if node.get("kind") == "BinaryOperator" and node.get("opcode") in {"&&", "||"}:
                logicals.append(node)
            pending.extend(node.get("inner", []))
        self.assertEqual(len(logicals), 2)
        self.assertTrue(all(
            [child.get("kind") for child in node.get("inner", [])] ==
            ["ImplicitCastExpr", "ImplicitCastExpr"]
            for node in logicals
        ))
        self.assertEqual(probe["metadata"]["expression_refusals"], [])

    def test_binary_expression_unsupported_types_are_refused(self):
        self.source.write_text(
            "double arithmetic(double left, double right) { return left + right; }\n",
            encoding="utf-8",
        )
        metadata = self.probe()["metadata"]
        self.assertEqual(metadata["expression_evidence"], [])
        self.assertEqual(len(metadata["expression_refusals"]), 1)
        self.assertEqual(metadata["expression_refusals"][0]["operator"], "+")
        self.assertIn("unrepresented", metadata["expression_refusals"][0]["reason"])

    def test_binary_expression_outside_dump_is_refused_explicitly(self):
        self.source.write_text(OUT_OF_DUMP_EXPRESSION_SOURCE, encoding="utf-8")
        metadata = self.probe()["metadata"]
        self.assertEqual(metadata["expression_evidence"], [])
        self.assertEqual(len(metadata["expression_refusals"]), 1)
        refusal = metadata["expression_refusals"][0]
        self.assertEqual(refusal["operator"], "+")
        self.assertFalse(refusal["dump_visible"])
        self.assertTrue(refusal["projection_supported"])
        self.assertEqual(refusal["reason"],
                         "expression occurrence is outside JSON AST dump")

    def test_same_process_joins_preserve_nonempty_coverage_and_raw_gaps(self):
        probe = self.probe()
        occurrences = declaration_occurrences(probe["ast"])
        records = probe["metadata"]["declarations"]
        supplemented = {record["id"] for record in records}
        joined = set(occurrences) & supplemented
        unsupplemented = set(occurrences) - supplemented
        supplement_only = supplemented - set(occurrences)
        self.assertGreater(len(joined), 0)
        self.assertEqual(len(occurrences), len(joined) + len(unsupplemented))
        self.assertEqual(len(supplemented), len(joined) + len(supplement_only))
        for record in records:
            if record.get("name") not in {"model", "Box", "read", "pick"}:
                continue
            self.assertIn(record["id"], occurrences)
            for path, node in occurrences[record["id"]]:
                self.assertIsInstance(path, tuple)
                self.assertEqual(node["kind"], record["kind"])
        print(
            "canonical probe coverage: {} joined IDs; {} raw gaps; {} supplement-only".format(
                len(joined), len(unsupplemented), len(supplement_only),
            ),
        )

    def test_raw_ast_matches_independent_stock_dump_up_to_pointer_renaming(self):
        probe = self.probe()
        stock = self.run_frontend(plugin=False)
        self.assertEqual(stock.returncode, 0, stock.stderr)
        self.assertEqual(normalize_pointers(probe["ast"]), normalize_pointers(json.loads(stock.stdout)))

    def test_skeletal_builtin_references_remain_visible_as_raw_gaps(self):
        probe = self.probe()
        occurrences = declaration_occurrences(probe["ast"])
        supplemented = {record["id"] for record in probe["metadata"]["declarations"]}
        gaps = set(occurrences) - supplemented
        skeletal = [
            (path, node) for identifier in gaps for path, node in occurrences[identifier]
            if node["kind"].endswith("RecordDecl") and "decl" in path and "inner" not in node
        ]
        self.assertTrue(skeletal, "nested skeletal builtin records must not disappear from telemetry")
        for path, node in skeletal:
            self.assertNotIn(node["id"], supplemented)
            self.assertNotIn("inner", node)
            self.assertTrue(any(isinstance(component, str) for component in path))
            self.assertTrue(any(isinstance(component, int) for component in path))

    def test_namespace_reopening_reports_one_canonical_namespace(self):
        namespaces = self.records(self.probe(), "NamespaceDecl", "model")
        self.assertEqual(len(namespaces), 2)
        self.assertNotEqual(namespaces[0]["id"], namespaces[1]["id"])
        self.assertEqual(namespaces[0]["canonical"], namespaces[1]["canonical"])
        for record in namespaces:
            self.assertEqual(record["original_namespace"], record["canonical"])
            self.assertFalse(record["anonymous_namespace"])
            self.assertFalse(record["inline_namespace"])

    def test_out_of_class_method_keeps_lexical_and_semantic_contexts_distinct(self):
        methods = self.records(self.probe(), "CXXMethodDecl", "read")
        self.assertEqual(len(methods), 2)
        declaration = next(record for record in methods if not record["definition"])
        definition = next(record for record in methods if record["definition"])
        self.assertEqual(declaration["canonical"], definition["canonical"])
        self.assertEqual(declaration["semantic_context"], definition["semantic_context"])
        self.assertEqual(declaration["semantic_context"], declaration["lexical_context"])
        self.assertNotEqual(definition["semantic_context"], definition["lexical_context"])
        self.assertEqual(definition["previous"], declaration["id"])

    def test_overload_redeclarations_do_not_merge_by_name(self):
        functions = self.records(self.probe(), "FunctionDecl", "pick")
        self.assertEqual(len(functions), 4)
        groups = {}
        for record in functions:
            groups.setdefault(record["canonical"], []).append(record)
        self.assertEqual(len(groups), 2)
        for canonical, records in groups.items():
            self.assertEqual(len(records), 2)
            self.assertEqual(sum(record["definition"] for record in records), 1)
            self.assertIn(canonical, {record["id"] for record in records})

    def test_injected_name_preserves_self_canonical_and_represented_class(self):
        classes = self.records(self.probe(), "CXXRecordDecl", "Box")
        injected = [record for record in classes if record["injected_class_name"]]
        ordinary = [record for record in classes if not record["injected_class_name"]]
        self.assertEqual(len(injected), 1)
        self.assertEqual(len(ordinary), 2)
        self.assertEqual(len({record["canonical"] for record in ordinary}), 1)
        name = injected[0]
        self.assertTrue(name["implicit"])
        self.assertEqual(name["canonical"], name["id"])
        self.assertIsNone(name["previous"])
        self.assertIn(name["represented_class"], {record["id"] for record in ordinary})
        self.assertNotEqual(name["represented_class"], name["canonical"])
        self.assertFalse(name["definition"])
        self.assertEqual(sum(record["definition"] for record in ordinary), 1)

    def test_defaulted_and_deleted_definitions_are_not_body_presence(self):
        constructors = self.records(self.probe(), "CXXConstructorDecl", "Box")
        defaulted = [record for record in constructors if record["defaulted"]]
        deleted = [record for record in constructors if record["deleted_as_written"]]
        self.assertEqual(len(defaulted), 1)
        self.assertEqual(len(deleted), 1)
        for record in defaulted + deleted:
            self.assertTrue(record["definition"])
            self.assertFalse(record["body_present"])
            self.assertEqual(record["definition_api"], "FunctionDecl.isThisDeclarationADefinition")
            self.assert_function_shape_api(record)
            self.assertIsNone(record["own_body_kind"])
            self.assertIsNone(record["own_body_owner"])
        self.assertTrue(defaulted[0]["function_explicitly_defaulted"])
        self.assertFalse(deleted[0]["function_explicitly_defaulted"])

    def test_function_shape_fields_are_versioned_and_function_local(self):
        probe = self.probe()
        functions = self.records(probe, "FunctionDecl", "pick")
        for record in functions:
            self.assert_function_shape_api(record)
            self.assertFalse(record["function_has_skipped_body"])
            self.assertFalse(record["function_will_have_body"])
            self.assertFalse(record["function_has_defining_attr"])
            self.assertFalse(record["function_late_template_parsed"])
            self.assertFalse(record["function_explicitly_defaulted"])
            self.assertEqual(record["function_attribute_count"], 0)
        for record in self.records(probe, "VarDecl", "defined"):
            self.assertNotIn("function_has_skipped_body", record)
            self.assertNotIn("function_attribute_count", record)
            self.assertNotIn("own_body_kind", record)

    def test_prototype_does_not_inherit_later_body_evidence(self):
        self.source.write_text(FUNCTION_SHAPE_SOURCE, encoding="utf-8")
        functions = self.records(self.probe(), "FunctionDecl", "later_body")
        self.assertEqual(len(functions), 2)
        declaration = next(record for record in functions if not record["definition"])
        definition = next(record for record in functions if record["definition"])
        self.assertEqual(declaration["canonical"], definition["canonical"])
        self.assertFalse(declaration["body_present"])
        self.assertIsNone(declaration["own_body_kind"])
        self.assertIsNone(declaration["own_body_owner"])
        self.assertTrue(definition["body_present"])
        self.assertEqual(definition["own_body_kind"], "CompoundStmt")
        self.assertEqual(definition["own_body_owner"], definition["id"])
        for record in functions:
            self.assert_function_shape_api(record)

    def test_function_try_block_reports_own_non_compound_body(self):
        self.source.write_text(FUNCTION_SHAPE_SOURCE, encoding="utf-8")
        probe = self.probe()
        record = self.records(probe, "FunctionDecl", "try_body")[0]
        self.assert_function_shape_api(record)
        self.assertTrue(record["definition"])
        self.assertTrue(record["body_present"])
        self.assertEqual(record["own_body_kind"], "CXXTryStmt")
        self.assertEqual(record["own_body_owner"], record["id"])
        index = pricing.build_index(probe["ast"], probe["metadata"]["declarations"])
        priced = pricing.price_query(index, record["id"], "definition")
        self.assertEqual(priced["status"], "eligible-tooling-evidence")
        self.assertIn("semantic-validator-not-implemented", priced["semantic_barriers"])

    def test_deleted_function_has_definition_without_own_body(self):
        self.source.write_text(FUNCTION_SHAPE_SOURCE, encoding="utf-8")
        record = self.records(self.probe(), "FunctionDecl", "deleted_function")[0]
        self.assert_function_shape_api(record)
        self.assertTrue(record["definition"])
        self.assertTrue(record["deleted_as_written"])
        self.assertFalse(record["body_present"])
        self.assertIsNone(record["own_body_kind"])
        self.assertIsNone(record["own_body_owner"])
        self.assertFalse(record["function_explicitly_defaulted"])

    def test_late_parsed_template_preserves_unmaterialized_own_body(self):
        self.source.write_text(
            "template<class Element> Element deferred(Element value) { return value; }\n",
            encoding="utf-8",
        )
        result = self.run_frontend(frontend_arguments=("-fdelayed-template-parsing",))
        self.assertEqual(result.returncode, 0, result.stderr)
        probe = json.loads(result.stdout)
        record = self.records(probe, "FunctionDecl", "deferred")[0]
        self.assert_function_shape_api(record)
        self.assertTrue(record["function_late_template_parsed"])
        self.assertTrue(record["definition"])
        self.assertTrue(record["body_present"])
        self.assertIsNone(record["own_body_kind"])
        self.assertIsNone(record["own_body_owner"])

    def test_attributed_functions_keep_evidence_without_definition_admission(self):
        self.source.write_text(FUNCTION_SHAPE_SOURCE, encoding="utf-8")
        probe = self.probe()
        index = pricing.build_index(probe["ast"], probe["metadata"]["declarations"])
        for name in ("attributed_declaration", "attributed_body", "defining_attribute"):
            record = self.records(probe, "FunctionDecl", name)[0]
            self.assert_function_shape_api(record)
            self.assertEqual(record["function_attribute_count"], 1)
            priced = pricing.price_query(index, record["id"], "definition")
            self.assertEqual(priced["status"], "refused")
            self.assertIn("function-attributes-not-supported", priced["reasons"])
        alias = self.records(probe, "FunctionDecl", "defining_attribute")[0]
        self.assertTrue(alias["function_has_defining_attr"])
        self.assertTrue(alias["definition"])
        self.assertFalse(alias["body_present"])
        self.assertIsNone(alias["own_body_kind"])
        self.assertIsNone(alias["own_body_owner"])

    def test_variable_definition_kind_is_an_enum_not_a_boolean(self):
        probe = self.probe()
        declaration = self.records(probe, "VarDecl", "declaration_only")[0]
        definition = self.records(probe, "VarDecl", "defined")[0]
        for record in (declaration, definition):
            self.assertIs(type(record["variable_definition_kind"]), int)
            self.assertIn(record["variable_definition_kind"], (0, 1, 2))
            self.assertIsNone(record["definition"])
            self.assertEqual(record["definition_api"], "VarDecl.isThisDeclarationADefinition")
        self.assertEqual(declaration["variable_definition_kind"], 0)
        self.assertEqual(definition["variable_definition_kind"], 2)

    def test_c_language_linkage_survives_redeclaration(self):
        probe = self.probe()
        functions = self.records(probe, "FunctionDecl", "c_function")
        self.assertEqual(len(functions), 2)
        self.assertEqual(len({record["canonical"] for record in functions}), 1)
        for record in functions + self.records(probe, "VarDecl", "c_variable"):
            self.assertEqual(record["language_linkage"], "C")
            self.assertEqual(record["linkage_formal"], "External")
        for record in self.records(probe, "FunctionDecl", "pick"):
            self.assertEqual(record["language_linkage"], "C++")

    def test_ordinary_forward_and_body_functions_report_non_template_api(self):
        functions = self.records(self.template_probe(), "FunctionDecl", "plain")
        self.assertEqual(len(functions), 2)
        self.assertEqual({record["definition"] for record in functions}, {False, True})
        for record in functions:
            self.assertIs(type(record["function_templated_kind"]), int)
            self.assertEqual(record["function_templated_kind"], 0)
            self.assertEqual(record["function_templated_kind_api"], "FunctionDecl.getTemplatedKind")
            self.assert_specialization_api(record, "FunctionDecl")
            self.assertEqual(record["template_specialization_kind"], 0)

    def test_ordinary_variable_and_record_forward_definitions_report_explicit_null(self):
        probe = self.template_probe()
        variables = self.records(probe, "VarDecl", "global_value")
        classes = [record for record in self.records(probe, "CXXRecordDecl", "Ordinary")
                   if not record["injected_class_name"]]
        self.assertEqual({record["variable_definition_kind"] for record in variables}, {0, 2})
        self.assertEqual({record["definition"] for record in classes}, {False, True})
        for family, records, described_api in (
            ("VarDecl", variables, "VarDecl.getDescribedVarTemplate"),
            ("CXXRecordDecl", classes, "CXXRecordDecl.getDescribedClassTemplate"),
        ):
            for record in records:
                self.assertIsNone(record["described_template"])
                self.assertEqual(record["described_template_api"], described_api)
                self.assert_specialization_api(record, family)
                self.assertEqual(record["template_specialization_kind"], 0)

    def test_primary_function_specializations_distinguish_template_from_parent_dependence(self):
        functions = self.records(self.template_probe(), "FunctionDecl", "templated")
        states = {(record["function_templated_kind"], record["template_specialization_kind"])
                  for record in functions}
        self.assertTrue({(1, 0), (3, 1), (3, 2)} <= states)
        for record in functions:
            self.assertIs(type(record["function_templated_kind"]), int)
            self.assertEqual(record["function_templated_kind_api"], "FunctionDecl.getTemplatedKind")
            self.assert_specialization_api(record, "FunctionDecl")
            self.assertFalse(record["dependent_context"])

    def test_primary_variable_and_class_templates_report_described_template_handles(self):
        probe = self.template_probe()
        variables = self.records(probe, "VarDecl", "variable")
        classes = [record for record in self.records(probe, "CXXRecordDecl", "Record")
                   if not record["injected_class_name"]]
        template_ids = {record["id"] for record in probe["metadata"]["declarations"]
                        if record["kind"] in ("VarTemplateDecl", "ClassTemplateDecl")}
        for family, records, described_api in (
            ("VarDecl", variables, "VarDecl.getDescribedVarTemplate"),
            ("CXXRecordDecl", classes, "CXXRecordDecl.getDescribedClassTemplate"),
        ):
            for record in records:
                self.assertRegex(record["described_template"], POINTER_ID)
                self.assertIn(record["described_template"], template_ids)
                self.assertEqual(record["described_template_api"], described_api)
                self.assert_specialization_api(record, family)
                self.assertEqual(record["template_specialization_kind"], 0)
                self.assertFalse(record["dependent_context"])

    def test_variable_and_class_specialization_subclasses_keep_base_api_provenance(self):
        probe = self.template_probe()
        variables = self.records(probe, "VarTemplateSpecializationDecl", "variable")
        classes = self.records(probe, "ClassTemplateSpecializationDecl", "Record")
        for family, records, described_api in (
            ("VarDecl", variables, "VarDecl.getDescribedVarTemplate"),
            ("CXXRecordDecl", classes, "CXXRecordDecl.getDescribedClassTemplate"),
        ):
            self.assertTrue({1, 2} <= {record["template_specialization_kind"] for record in records})
            for record in records:
                self.assertIsNone(record["described_template"])
                self.assertEqual(record["described_template_api"], described_api)
                self.assert_specialization_api(record, family)

    def test_member_specializations_are_not_ordinary_despite_absent_described_templates(self):
        probe = self.template_probe()
        variables = self.records(probe, "VarDecl", "member")
        classes = [record for record in self.records(probe, "CXXRecordDecl", "Nested")
                   if not record["injected_class_name"]]
        for family, records in (("VarDecl", variables), ("CXXRecordDecl", classes)):
            specialized = [record for record in records if record["template_specialization_kind"] != 0]
            self.assertTrue(specialized)
            for record in specialized:
                self.assertIsNone(record["described_template"])
                self.assert_specialization_api(record, family)
                self.assertFalse(record["dependent_context"])

    def test_member_function_templates_and_dependent_members_keep_distinct_classifier(self):
        probe = self.template_probe()
        templates = self.records(probe, "CXXMethodDecl", "member_template")
        ordinary_members = self.records(probe, "CXXMethodDecl", "plain_member")
        self.assertTrue({1, 3} <= {record["function_templated_kind"] for record in templates})
        self.assertTrue({0, 2} <= {record["function_templated_kind"] for record in ordinary_members})
        self.assertTrue(any(record["function_templated_kind"] == 0 and
                            record["dependent_context"] for record in ordinary_members))
        for record in templates + ordinary_members:
            self.assertEqual(record["function_templated_kind_api"], "FunctionDecl.getTemplatedKind")
            self.assert_specialization_api(record, "FunctionDecl")

    def test_member_enum_instantiation_is_not_hidden_by_ordinary_parent_context(self):
        probe = self.template_probe()
        ordinary = self.records(probe, "EnumDecl", "Tag")
        member = self.records(probe, "EnumDecl", "MemberEnum")
        self.assertEqual({record["template_specialization_kind"] for record in ordinary}, {0})
        self.assertTrue({0, 1} <= {record["template_specialization_kind"] for record in member})
        for record in ordinary + member:
            self.assert_specialization_api(record, "EnumDecl")
        self.assertTrue(any(record["template_specialization_kind"] == 1 and
                            not record["dependent_context"] for record in member))

    def test_explicit_member_enum_specialization_at_translation_unit_refuses_local_queries(self):
        self.source.write_text(MEMBER_ENUM_SOURCE, encoding="utf-8")
        probe = self.probe()
        specialized = [record for record in self.records(probe, "EnumDecl", "Specialized")
                       if record["template_specialization_kind"] == 2 and record["definition"]]
        self.assertEqual(len(specialized), 1)
        record = specialized[0]
        self.assertFalse(record["implicit"])
        self.assertFalse(record["dependent_context"])
        self.assertIsNone(record["owning_module"])
        self.assert_specialization_api(record, "EnumDecl")
        direct_ids = {node.get("id") for node in probe["ast"]["inner"]
                      if node.get("kind") == "EnumDecl"}
        self.assertIn(record["id"], direct_ids)
        index = pricing.build_index(probe["ast"], probe["metadata"]["declarations"])
        for query in ("definition", "linkage"):
            result = pricing.price_query(index, record["id"], query)
            self.assertEqual(result["status"], "refused")
            self.assertIn("specialization-or-unestablished", result["reasons"])
            self.assertNotIn("template-associated-occurrence", result["reasons"])
            self.assertNotIn("dependent-or-unestablished", result["reasons"])

    def test_template_alias_context_preserves_raw_template_nodes_and_stock_dump(self):
        probe = self.template_probe()
        aliases = self.records(probe, "TypeAliasTemplateDecl", "Alias")
        self.assertEqual(len(aliases), 1)
        occurrences = declaration_occurrences(probe["ast"])
        self.assertIn(aliases[0]["id"], occurrences)
        for record in self.records(probe, "NamespaceDecl", "evidence"):
            self.assertNotIn("template_specialization_kind", record)
            self.assertNotIn("function_templated_kind", record)
            self.assertNotIn("described_template", record)
        stock = self.run_frontend(plugin=False)
        self.assertEqual(stock.returncode, 0, stock.stderr)
        self.assertEqual(normalize_pointers(probe["ast"]), normalize_pointers(json.loads(stock.stdout)))

    def test_syntax_error_does_not_publish_a_json_artifact(self):
        self.source.write_text("int broken( {\n", encoding="utf-8")
        result = self.run_frontend()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("error:", result.stderr)

    def test_nonempty_plugin_arguments_do_not_publish_a_json_artifact(self):
        result = self.run_frontend(plugin_arguments=("unexpected",))
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("canonical probe accepts no plugin arguments", result.stderr)

    def test_header_runtime_version_mismatch_does_not_publish_json(self):
        headers = pathlib.Path(os.environ.get(
            "LEANCPP_PROBE_INCLUDE", str(self.library.parent / "toolchain" / "include"),
        ))
        library_directory = pathlib.Path(self.clang).parent.parent / "lib"
        clang_library = library_directory / "libclang-cpp.so.21.1"
        llvm_library = library_directory / "libLLVM.so.21.1"
        if not (headers / "clang" / "Basic" / "Version.h").is_file():
            self.skipTest("matching probe development headers are unavailable")
        if not clang_library.is_file() or not llvm_library.is_file():
            self.skipTest("matching probe development libraries are unavailable")
        original = pathlib.Path(__file__).with_name("canonical_probe.cpp").read_text(encoding="utf-8")
        marker = "\nnamespace {"
        self.assertEqual(original.count(marker), 1)
        altered = original.replace(
            marker,
            '\n#undef CLANG_VERSION_STRING\n#define CLANG_VERSION_STRING "0.0.unsupported"\n' + marker,
            1,
        )
        source = self.root / "unsupported_version.cpp"
        source.write_text(altered, encoding="utf-8")
        library = self.root / "unsupported_version.so"
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        built = subprocess.run(
            [
                self.clang, "--no-default-config", "-std=c++17", "-shared", "-fPIC",
                "-I", str(headers), "-I", str(pathlib.Path(__file__).resolve().parent),
                str(source), str(clang_library), str(llvm_library),
                "-Wl,-rpath," + str(library_directory), "-o", str(library),
            ],
            cwd=self.root, env=environment, capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(built.returncode, 0, built.stderr)
        result = self.run_frontend(library=library)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("canonical probe header/runtime version mismatch", result.stderr)

    def test_fresh_runs_agree_by_occurrence_witness_not_pointer_equality(self):
        first = self.probe()
        second = self.probe()
        relationships = witnessed_relationships(first)
        self.assertTrue(relationships)
        self.assertEqual(relationships, witnessed_relationships(second))
        self.assertEqual(
            normalize_pointers(first["metadata"]["type_evidence"]),
            normalize_pointers(second["metadata"]["type_evidence"]),
        )
        self.assertEqual(
            normalize_pointers(first["metadata"]["type_refusals"]),
            normalize_pointers(second["metadata"]["type_refusals"]),
        )
        self.assertEqual(normalize_pointers(first["ast"]), normalize_pointers(second["ast"]))


if __name__ == "__main__":
    unittest.main()
