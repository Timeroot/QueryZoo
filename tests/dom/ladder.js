/* The ladder grid: square, ranked, diagonal on the diagonal, and the scope
   control still switching wrappers underneath it. */
const { load, done, click } = require("./harness");

const hash = process.argv[2] || "";
const { window, doc, errs } = load("matrix.html", { hash, scripts: ["static/app.js"] });
const bad = [];

const wraps = ["wrap-core", "wrap-all", "wrap-ladder"];
const state = (tag, want) => {
  const vis = wraps.filter((w) => !doc.getElementById(w).hidden);
  const on = [...doc.querySelectorAll("#matrix-scope button.on")]
    .map((b) => b.getAttribute("data-scope"));
  console.log("  " + tag.padEnd(20), "visible:", vis.join(",") || "none",
    "| on:", on.join(",") || "none",
    "| chips hidden:", doc.getElementById("matrix-cats").hidden,
    "| count:", doc.getElementById("matrix-count").textContent);
  if (want && (vis.length !== 1 || vis[0] !== want))
    bad.push(tag + ": showing " + (vis.join(",") || "nothing") + ", wanted " + want);
  if (want && String(on) !== String([want.replace("wrap-", "")]))
    bad.push(tag + ": button state " + on + " does not match " + want);
};

state("on load" + (hash ? " " + hash : ""));
click(doc, window, '#matrix-scope [data-scope="ladder"]');
state("after Ladder", "wrap-ladder");

const tbl = doc.getElementById("matrix-ladder");
const rows = [...tbl.querySelectorAll("tbody tr")];
const rowIds = rows.map((tr) =>
  tr.querySelector("th.rowhead a").getAttribute("href").replace(/.*\/|\.html/g, ""));
const colIds = [...tbl.querySelectorAll("thead th.colhead")].map((th) => th.getAttribute("data-col"));
console.log("  ladder rows:", rows.length, "cols:", colIds.length);
console.log("  row order  :", rowIds.join(" "));
if (JSON.stringify(rowIds) !== JSON.stringify(colIds))
  bad.push("ladder rows and columns are in different orders");
if (doc.getElementById("wrap-ladder").classList.contains("mj-defer"))
  bad.push("mj-defer never cleared: MathJax would not typeset the ladder");
if (!rows.every((tr, i) => tr.querySelectorAll("td.mcell")[i].classList.contains("diag")))
  bad.push("a diagonal cell is off the diagonal");

/* the tooltip/crosshair binding must still work on the generated table */
const td = rows[3].querySelectorAll("td.mcell")[0];
td.dispatchEvent(new window.MouseEvent("mouseover", { bubbles: true }));
const lit = [...tbl.querySelectorAll("th.hl")].length;
if (lit !== 2) bad.push("crosshair lit " + lit + " headers, wanted 2");

/* the order is by size, so recorded exact upper bounds should sit below it */
let below = 0, above = 0;
rows.forEach((tr, i) => {
  [...tr.querySelectorAll("td.mcell")].forEach((cell, j) => {
    if (!cell.querySelector(".v.vt .tchip.c-exact, .v.vt .tchip.c-attained")) return;
    if (i > j) below++; else above++;
  });
});
console.log("  exact-chip cells below the diagonal:", below, "above:", above);

click(doc, window, '#matrix-scope [data-scope="core"]');
state("after Core", "wrap-core");
click(doc, window, '#matrix-scope [data-scope="all"]');
state("after All", "wrap-all");
click(doc, window, '#matrix-scope [data-scope="ladder"]');
state("back to Ladder", "wrap-ladder");

done(bad, errs);
