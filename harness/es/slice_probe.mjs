// slice_probe.mjs — per-test node kinds and FREE identifiers, for the
// scoreboard's population rule. Reads a file of paths, writes JSONL.
//
// "Free" is approximated by: every Identifier in reference position minus
// every name the script itself declares. It is deliberately CONSERVATIVE in
// the direction that matters — a name wrongly called free EXCLUDES a test
// from the population, so the error shrinks the corpus rather than admitting
// a test the tier cannot run.
// acorn's path is passed in, not resolved as a bare specifier: node resolves
// those relative to THIS FILE, and the fetched acorn lives beside the corpus
// (fetch-don't-vendor), not in the repo. `es_census.py` passes it the same way.
import { readFileSync, writeFileSync } from "fs";
import { pathToFileURL } from "url";
const { parse } = await import(pathToFileURL(process.argv[4]).href);

const files = readFileSync(process.argv[2], "utf8").trim().split("\n").filter(Boolean);
const out = [];
for (const f of files) {
  let src;
  try { src = readFileSync(f, "utf8"); } catch { continue; }
  const m = /\/\*---([\s\S]*?)---\*\//.exec(src);
  const fm = m ? m[1] : "";
  const flags = /^\s*flags:\s*\[(.*?)\]/m.exec(fm);
  const flagList = flags ? flags[1].split(",").map(s => s.trim()) : [];
  const negative = /negative:/.test(fm);
  let ast;
  try { ast = parse(src, { ecmaVersion: "latest", sourceType: "script" }); }
  catch { out.push({ f, parsed: false, negative, flags: flagList, k: [], free: [] }); continue; }
  const declared = new Set(), referenced = new Set(), kinds = new Set();
  (function walk(n, parent, key) {
    if (!n || typeof n.type !== "string") return;
    kinds.add(n.type);
    if (n.type === "Identifier") {
      const p = parent;
      const isBinder =
        (p && p.type === "VariableDeclarator" && key === "id") ||
        (p && /^(Function|Class)(Declaration|Expression)$/.test(p.type) && key === "id") ||
        (p && key === "params") ||
        (p && p.type === "CatchClause" && key === "param");
      const isNotAReference =
        (p && p.type === "MemberExpression" && key === "property" && !p.computed) ||
        (p && p.type === "Property" && key === "key" && !p.computed);
      if (isBinder) declared.add(n.name);
      else if (!isNotAReference) referenced.add(n.name);
    }
    for (const k of Object.keys(n)) {
      if (k === "type" || k === "start" || k === "end") continue;
      const v = n[k];
      if (Array.isArray(v)) v.forEach(c => c && typeof c.type === "string" && walk(c, n, k));
      else if (v && typeof v.type === "string") walk(v, n, k);
    }
  })(ast, null, null);
  out.push({ f, parsed: true, negative, flags: flagList, k: [...kinds],
             free: [...referenced].filter(x => !declared.has(x)) });
}
writeFileSync(process.argv[3], out.map(o => JSON.stringify(o)).join("\n") + "\n");
console.error(`slice_probe: ${out.length} rows`);
