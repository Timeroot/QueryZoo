/* Do the scope buttons say how many measures they actually draw?

   Counts the rows and columns the injected stylesheet leaves standing in the
   DOM, not the ones the metadata claims, and compares that with the number on
   the button and with the count line.  This is what caught the "13 x 13
   core grid" label being wrong: the exponent table has 12 recorded rows. */
const { load, done, click } = require("./harness");

const { window, doc, errs } = load("matrix.html", { scripts: ["static/app.js"] });

const css = () => [...doc.head.querySelectorAll("style")].map((s) => s.textContent).join("");

/* rows / columns of a grid that the injected stylesheet leaves standing */
function drawn(tbl) {
  const sheet = css();
  const live = (id, kind) => !new RegExp(
    "#" + tbl + (kind === "row" ? " tr\\.y-" : " \\.x-") +
    id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&") + "(?=[,{])").test(sheet);
  const rows = [...doc.querySelectorAll("#" + tbl + " tr[class*=y-]")]
    .map((tr) => (tr.className.match(/\by-(\S+)/) || [])[1])
    .filter((id) => id && live(id, "row"));
  const cols = [...doc.querySelectorAll("#" + tbl + " th[data-col]")]
    .map((th) => th.getAttribute("data-col"))
    .filter((id) => live(id, "col"));
  return { rows: rows.length, cols: cols.length, both: new Set([...rows, ...cols]).size };
}

const state = () =>
  [...doc.querySelectorAll("#matrix-scope [data-scope]")].map((b) => {
    const v = b.getAttribute("data-scope");
    return v + "=" + b.querySelector(".n").textContent + (b.hidden ? "(hidden)" : "") +
      (b.classList.contains("on") ? "*" : "");
  }).join("  ");

const bad = [];
function report(view, scope) {
  const grid = scope === "core" ? "matrix" : scope === "ladder" ? "matrix-ladder" : "matrix-all";
  const d = drawn(grid);
  const btn = doc.querySelector('#matrix-scope [data-scope="' + scope + '"]');
  const says = Number(btn.querySelector(".n").textContent);
  const line = doc.getElementById("matrix-count").textContent;
  if (says !== d.both)
    bad.push(view + "/" + scope + ": button says " + says + ", grid draws " + d.both);
  const m = line.match(/^(\d+)(?: x (\d+))?/);
  const claim = scope === "ladder" ? [d.both] : [d.rows, d.cols];
  const got = [Number(m[1])].concat(m[2] ? [Number(m[2])] : []);
  if (String(claim) !== String(got))
    bad.push(view + "/" + scope + ": count line says " + got + ", grid draws " + claim);
  console.log("  " + (view + " " + scope).padEnd(20), "| drawn:",
    (d.rows + "x" + d.cols).padEnd(7), "|", line);
  console.log("  " + " ".repeat(20), "|", state());
}

["total", "partial", "relation"].forEach((view) => {
  click(doc, window, '#matrix-view [data-view="' + view + '"]');
  ["core", "all", "ladder"].forEach((scope) => {
    click(doc, window, '#matrix-scope [data-scope="' + scope + '"]');
    report(view, scope);
  });
});

done(bad, errs);
