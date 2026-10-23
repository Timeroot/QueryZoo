/* Does switching Total / Partial / Relations drop every measure that is not
   defined in that setting out of every grid -- and only those?

   Hidden = undefined in the setting (nd) plus defined but off the exponent
   scale (nc: degenerate here, or dimensionless everywhere). */
const { load, done, click } = require("./harness");

const { window, doc, errs } = load("matrix.html", { scripts: ["static/app.js"] });
const meta = JSON.parse(doc.getElementById("matrix-meta").textContent);

const nd = {}, nc = {}, gone = {};
["total", "partial", "relation"].forEach((s) => {
  nd[s] = meta.measures.filter((m) => (m.nd || []).indexOf(s) >= 0).map((m) => m.id);
  nc[s] = meta.measures.filter((m) => (m.nc || []).indexOf(s) >= 0).map((m) => m.id);
  gone[s] = nd[s].concat(nc[s]);
});
console.log("  undefined per setting:",
  Object.keys(nd).map((s) => s + "=" + nd[s].length).join(" "));
console.log("  off-scale per setting:",
  Object.keys(nc).map((s) => s + "=" + nc[s].length + "[" + nc[s].join(" ") + "]").join(" "));

const sheet = () => [...doc.head.querySelectorAll("style")].map((s) => s.textContent).join("");
const count = () => doc.getElementById("matrix-count").textContent;
const bad = [];

function report(tag, view) {
  const css = sheet();
  const has = (s) => new RegExp(s.replace(/[.#*+?^${}()|[\]\\]/g, "\\$&") + "(?=[,{])").test(css);
  const missing = [];
  ["matrix", "matrix-all", "matrix-ladder"].forEach((t) => {
    gone[view].forEach((id) => {
      if (!has("#" + t + " tr.y-" + id)) missing.push(t + "/" + id + " row");
      if (!has("#" + t + " .x-" + id)) missing.push(t + "/" + id + " col");
    });
  });
  /* nothing comparable in this setting may be hidden from the ladder grid */
  const overreach = meta.measures.filter(
    (m) => gone[view].indexOf(m.id) < 0 && has("#matrix-ladder tr.y-" + m.id)
  ).map((m) => m.id);
  console.log("  " + tag.padEnd(24), "| count:", count());
  if (missing.length) bad.push(tag + ": not hidden: " + missing.slice(0, 6).join(", "));
  if (overreach.length) bad.push(tag + ": over-hidden: " + overreach.join(","));
}

report("scope=core view=total", "total");
click(doc, window, '#matrix-view [data-view="relation"]');
report("scope=core view=relation", "relation");
click(doc, window, '#matrix-scope [data-scope="ladder"]');
report("scope=ladder view=relation", "relation");
click(doc, window, '#matrix-scope [data-scope="all"]');
report("scope=all view=relation", "relation");
click(doc, window, '#matrix-view [data-view="partial"]');
report("scope=all view=partial", "partial");
click(doc, window, '#matrix-view [data-view="total"]');
report("scope=all view=total", "total");
click(doc, window, '#matrix-scope [data-scope="core"]');
report("scope=core view=total", "total");

/* the body class the cell CSS keys off must still track the buttons */
click(doc, window, '#matrix-view [data-view="relation"]');
if (!/\bview-relation\b/.test(doc.body.className))
  bad.push("body class did not follow the view button: " + doc.body.className);

done(bad, errs);
