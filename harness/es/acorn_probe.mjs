// harness/es/acorn_probe.mjs — the frontend half of `es_census.py --frontend`.
//
// Reads one absolute path per line on stdin; writes one JSON object per line
// to stdout, IN INPUT ORDER, exactly one line per input line:
//
//   {"path": …, "ok": true,  "types": {"Identifier": 12, …}, "sourceType": …}
//   {"path": …, "ok": false, "error": "…", "pos": 123}
//
// A file that cannot be read, or that acorn cannot be loaded for, produces a
// {"runner_error": …} line rather than no line — the batch protocol's rule:
// a missing row would silently shrink the denominator.
//
// The parse is attempted as `script` first and, only if that fails, as
// `module`: test262's `flags: [module]` is metadata the frontend does not
// see, and a source that parses either way is in the vocabulary either way.
// Which one succeeded is reported, never assumed.

import { createInterface } from 'node:readline';
import { readFileSync } from 'node:fs';

// acorn is FETCHED, never vendored: argv[2] is where the caller put it
// (`npm install acorn` in a scratch directory).  Bare `import 'acorn'` is the
// fallback for a host that has it globally.  Absent either way, this REFUSES
// loudly with exit 3 rather than reporting an empty vocabulary.
let acorn;
const where = process.argv[2];
try {
  acorn = await import(where ? new URL(where, 'file://').href : 'acorn');
} catch (e) {
  process.stdout.write(JSON.stringify({ runner_error: `acorn not available: ${e.message}` }) + '\n');
  process.exit(3);
}

const ECMA = 'latest';

function walk(node, counts) {
  if (node === null || typeof node !== 'object') return;
  if (Array.isArray(node)) {
    for (const x of node) walk(x, counts);
    return;
  }
  if (typeof node.type === 'string') counts[node.type] = (counts[node.type] || 0) + 1;
  for (const k of Object.keys(node)) {
    if (k === 'type' || k === 'start' || k === 'end' || k === 'loc' || k === 'range') continue;
    walk(node[k], counts);
  }
}

const rl = createInterface({ input: process.stdin, crlfDelay: Infinity });
for await (const line of rl) {
  const path = line.trim();
  if (!path) continue;
  let src;
  try {
    src = readFileSync(path, 'utf8');
  } catch (e) {
    process.stdout.write(JSON.stringify({ path, runner_error: `unreadable: ${e.message}` }) + '\n');
    continue;
  }
  let out = null;
  for (const sourceType of ['script', 'module']) {
    try {
      const ast = acorn.parse(src, { ecmaVersion: ECMA, sourceType, allowHashBang: true });
      const counts = {};
      walk(ast, counts);
      out = { path, ok: true, sourceType, types: counts };
      break;
    } catch (e) {
      if (out === null) out = { path, ok: false, error: String(e.message), pos: e.pos ?? -1 };
    }
  }
  process.stdout.write(JSON.stringify(out) + '\n');
}
