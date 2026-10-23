/* Does the "Show all" fold on a measure page hold the whole zoo?

   The default rows are the entry's hand-picked `related:` list; everything
   else is server-rendered into a second <tbody> that starts hidden.  So the
   things that can go wrong are: the fold never opens, the two lists overlap
   or do not add up to every other measure, or a row links somewhere other
   than the pair it names.  Checks all three, on a spread of pages. */
const fs = require("fs");
const path = require("path");
const { SITE, load, done, click } = require("./harness");

const PAGES = ["Q", "RS", "D", "lambda", "Stab", "Var", "nsr", "osss"];
const all = fs.readdirSync(path.join(SITE, "measures"))
  .filter((f) => f.endsWith(".html") && f !== "index.html")
  .map((f) => f.slice(0, -5));

const bad = [];
const errs = [];

function rowsOf(tbody) {
  return [...tbody.querySelectorAll("tr")].map((tr) => {
    const a = [...tr.querySelectorAll("a.pairlink")];
    return {
      id: (tr.querySelector("a[href*='measures/']").getAttribute("href")
        .match(/measures\/(.+)\.html/) || [])[1],
      pairs: a.map((x) => {
        const q = new URL(x.getAttribute("href"), "http://localhost/m/").search;
        const p = new URLSearchParams(q);
        return [p.get("a"), p.get("b")];
      }),
    };
  });
}

PAGES.forEach((id) => {
  const page = "measures/" + id + ".html";
  const { window, doc, errs: e } = load(page, { scripts: ["static/app.js"] });
  e.forEach((x) => errs.push(page + ": " + x));
  const say = (m) => bad.push(id + ": " + m);

  const bodies = [...doc.querySelectorAll(".nbrs tbody")];
  if (bodies.length !== 2) return say("expected 2 tbodies, found " + bodies.length);
  const [few, rest] = bodies;
  const btn = doc.querySelector("[data-nbrs-toggle]");
  if (!btn) return say("no toggle button");

  const fr = rowsOf(few), rr = rowsOf(rest);
  if (fr.length < 2 || fr.length > 6)
    say("hand-picked list is " + fr.length + " long, want 2-6");
  const seen = new Set([...fr, ...rr].map((r) => r.id));
  if (seen.size !== fr.length + rr.length) say("a measure appears in both lists");
  if (seen.has(id)) say("the page lists itself");
  const missing = all.filter((x) => x !== id && !seen.has(x));
  if (missing.length) say("not shown at all: " + missing.join(","));

  /* both directions of every row, and they point where they say */
  [...fr, ...rr].forEach((r) => {
    if (r.pairs.length !== 2)
      return say(r.id + ": " + r.pairs.length + " pair links, want 2");
    const want = String([[id, r.id], [r.id, id]]);
    if (String(r.pairs) !== want)
      say(r.id + ": links " + r.pairs + ", want " + want);
  });

  /* the fold itself */
  if (!rest.hidden) say("the rest of the zoo starts unfolded");
  const opened = btn.textContent.trim();
  click(doc, window, "[data-nbrs-toggle]");
  if (rest.hidden) say("clicking the button did not unfold it");
  if (btn.textContent.trim() === opened) say("the button label did not change");
  if (!btn.classList.contains("on")) say("the button does not look pressed");
  click(doc, window, "[data-nbrs-toggle]");
  if (!rest.hidden) say("clicking again did not fold it back");
  if (btn.textContent.trim() !== opened) say("the button label did not come back");

  if (!opened.includes(String(fr.length + rr.length)))
    say("button says " + JSON.stringify(opened) + ", there are " +
      (fr.length + rr.length) + " rows");

  console.log("  " + id.padEnd(9), "| picked:", String(fr.length).padStart(2),
    "| folded:", String(rr.length).padStart(2), "|", opened);
});

done(bad, errs);
