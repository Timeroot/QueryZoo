/* Shared jsdom setup for the drivers in this directory.

   The site is static and the pages fetch their own JSON, so `fetch` is wired
   straight to the filesystem.  Exit 77 means "jsdom is not installed here",
   which the Python runner reads as a skip rather than a failure. */
const fs = require("fs");
const path = require("path");

const SITE = process.env.ZOO_SITE || path.resolve(__dirname, "..", "..", "site");

let JSDOM;
try {
  ({ JSDOM } = require("jsdom"));
} catch (e) {
  console.log("  jsdom not found -- set NODE_PATH to a tree that has it");
  process.exit(77);
}

function load(page, opts) {
  opts = opts || {};
  const html = fs.readFileSync(path.join(SITE, page), "utf8");
  const dom = new JSDOM(html, {
    url: "http://localhost/" + page + (opts.query || "") + (opts.hash || ""),
    runScripts: opts.runScripts || "outside-only",
    pretendToBeVisual: true,
  });
  const { window } = dom;
  const doc = window.document;
  const errs = [];
  window.addEventListener("error", (e) => errs.push(String(e.error || e.message)));
  window.fetch = function (u) {
    const p = path.join(SITE, String(u).replace(/^\.*\//, ""));
    return Promise.resolve({
      ok: fs.existsSync(p),
      json: () => Promise.resolve(JSON.parse(fs.readFileSync(p, "utf8"))),
    });
  };
  (opts.scripts || []).forEach((s) =>
    window.eval(fs.readFileSync(path.join(SITE, s), "utf8")));
  return { dom, window, doc, errs, html };
}

/* Every driver ends here: one line of verdict, and the exit status. */
function done(bad, errs) {
  console.log("  problems:", bad.length ? bad.join(" | ") : "none");
  console.log("  script errors:", errs && errs.length ? errs.join(" | ") : "none");
  process.exit(bad.length || (errs && errs.length) ? 1 : 0);
}

const click = (doc, win, sel) =>
  doc.querySelector(sel).dispatchEvent(new win.MouseEvent("click", { bubbles: true }));

module.exports = { SITE, JSDOM, load, done, click };
