/* The pair pages are one page: pair.html?a=X&b=Y fetches a shard and renders.
   Render a handful and look for anything obviously broken in the output.

   Usage: node pair.js [A B [anchor]]   -- with no arguments it sweeps a list. */
const { load, done } = require("./harness");

const argv = process.argv.slice(2);
const PAIRS = argv.length
  ? [argv]
  : [["D", "R"], ["D", "Q"], ["bs", "s"], ["C", "deg"], ["R0", "R"], ["Var", "MaxInf"]];

const bad = [];
const allErrs = [];
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

(async () => {
  for (const [a, b, anchor] of PAIRS) {
    const { doc, errs } = load("pair.html", {
      query: `?a=${a}&b=${b}`,
      hash: anchor ? "#" + anchor : "",
      scripts: ["static/pair.js"],
    });
    await sleep(400);
    const out = doc.getElementById("pairview").innerHTML;
    const crumb = doc.getElementById("crumb").textContent.replace(/\s+/g, " ").trim();
    console.log(`  ${a} vs ${b}: ${out.length} bytes | ${doc.title} | ${crumb}`);
    if (argv.length) console.log(out.replace(/\n\s*\n/g, "\n"));
    if (out.length < 200) bad.push(`${a}/${b}: rendered almost nothing`);
    if (!doc.title || /undefined/.test(doc.title)) bad.push(`${a}/${b}: title is "${doc.title}"`);
    const junk = out.match(/\[object Object\]|\bNaN\b|>undefined<|="undefined"/g);
    if (junk) bad.push(`${a}/${b}: ${[...new Set(junk)].join(" ")}`);
    allErrs.push(...errs);
  }
  done(bad, allErrs);
})();
