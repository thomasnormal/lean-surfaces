#!/usr/bin/env python3.12
"""regress_envelopes.py BASE_EXTRACTORS NEW_EXTRACTORS REPO [--jobs N] [--out FILE]

(WP-PROC, 2026-11-01; recipe in docs/sv-proc-lowering.md. BASE_EXTRACTORS is a directory that holds `sv/extract.py`, for
instance `git archive <rev> extractors | tar -x -C /tmp/base` and then `/tmp/base/extractors`.)

Monotonicity check of an extractor change: for every committed sv-0.2 envelope of REPO (Examples/system-verilog/**.json with
mode == symbolic, sources present) re-extract with the BASE and the NEW extractor (same sources, same --top, default point)
and compare the bytes. An envelope with no Unsupported node in the BASE output (an ADMITTED row) must be byte-identical; a
difference elsewhere is listed (it is a refusal that moved, expected for the construct being lowered) but does not fail.
Exit 1 if an admitted envelope changed."""
import sys, os, json, glob, subprocess, argparse, concurrent.futures as cf
ap = argparse.ArgumentParser(); ap.add_argument('base'); ap.add_argument('new'); ap.add_argument('repo')
ap.add_argument('--jobs', type=int, default=4); ap.add_argument('--out')
ap.add_argument('--cache', help='directory caching the BASE outputs (reuse it while the base extractor is the same)'); a = ap.parse_args()
repo = os.path.abspath(a.repo)
def has_unsup(j):
    """REFUSED before: an `Unsupported` node, a `LocalDecl` statement (the loader has no arm for it) or a declaration whose
    packed dimensions were not recovered (`packed: null`, which the Lean loader refuses): none is an admitted row."""
    st = [j]
    while st:
        n = st.pop()
        if isinstance(n, dict):
            if n.get('kind') in ('Unsupported', 'LocalDecl'): return True
            w = n.get('width')
            if (n.get('kind') in ('Var', 'Net', 'Port') and isinstance(w, dict) and w.get('kind') == 'PackedType'
                    and w.get('packed') is None): return True
            st.extend(n.values())
        elif isinstance(n, list): st.extend(n)
    return False
items = []
for f in sorted(glob.glob(repo + '/Examples/system-verilog/**/*.json', recursive=True)):
    if f.endswith('.probes.json'): continue
    try: j = json.load(open(f))
    except Exception: continue
    if not isinstance(j, dict) or j.get('mode') != 'symbolic': continue
    srcs = [s if isinstance(s, str) else s['path'] for s in j['source_files']]
    if not all(os.path.exists(os.path.join(repo, s)) for s in srcs): continue
    items.append((os.path.relpath(f, repo), j['top'], srcs))
# svGolf designs: tasks' references and tests (top from the task directory)
for tj in glob.glob(repo + '/svgolf/tasks/*/task.json'):
    t = json.load(open(tj)); d = os.path.dirname(tj)
    for sv in glob.glob(d + '/reference/*.sv') + glob.glob(repo + '/svgolf/tests/%s/**/*.sv' % t['name'], recursive=True):
        if '/validate/' in sv: continue          # testbenches, not designs
        items.append((os.path.relpath(sv, repo), t['top'], [os.path.relpath(sv, repo)]))
def run(it):
    name, top, srcs = it
    outs = []
    for tag, ex in (('base', a.base), ('new', a.new)):
        cached = os.path.join(a.cache, name.replace('/', '__') + '.base') if (a.cache and tag == 'base') else None
        if cached and os.path.exists(cached):
            raw = open(cached, 'rb').read()
            outs.append(('ERR', 'cached') if raw == b'ERR' else ('ok', raw)); continue
        out = '/tmp/regress_%s_%d.json' % (tag, abs(hash(name)))
        r = subprocess.run([sys.executable, os.path.join(ex, 'sv', 'extract.py'), '--top', top, *srcs, '-o', out], cwd=repo,
                           capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'), timeout=600)
        if r.returncode:
            outs.append(('ERR', r.stderr[-120:]))
            if cached: os.makedirs(a.cache, exist_ok=True); open(cached, 'wb').write(b'ERR')
            continue
        b = open(out, 'rb').read(); os.remove(out); outs.append(('ok', b))
        if cached: os.makedirs(a.cache, exist_ok=True); open(cached, 'wb').write(b)
    return name, outs
res = []
with cf.ThreadPoolExecutor(a.jobs) as ex:
    for name, (b, n) in ex.map(run, items):
        res.append((name, b, n))
bad = []; moved = []; same = 0; err = 0
for name, b, n in res:
    if b[0] == 'ERR' or n[0] == 'ERR':
        if b[0] == 'ERR' and n[0] != 'ERR': moved.append((name, 'extractable now (the base extractor stopped)'))   # `--top` of an instantiated module (N3)
        elif b[0] != n[0]: bad.append((name, 'extractor outcome differs: base=%s new=%s' % (b[0], n[0])))
        err += 1; continue
    if b[1] == n[1]: same += 1; continue
    admitted = not has_unsup(json.loads(b[1]))
    (bad if admitted else moved).append((name, 'ADMITTED envelope changed' if admitted else 'refusal moved'))
print('envelopes %d: identical %d, extractor errors (same both) %d, refusal moved %d, ADMITTED CHANGED %d' % (len(res), same, err, len(moved), len(bad)))
for n_, why in moved: print('  moved:', n_)
for n_, why in bad: print('  BAD  :', n_, why)
if a.out: json.dump({'moved': moved, 'bad': bad, 'same': same}, open(a.out, 'w'))
sys.exit(1 if bad else 0)
