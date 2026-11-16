/* The gap report is one page with a client-side filter over an embedded table:
   drive the filter and check the count line keeps up with the rows drawn. */
const { load, done } = require("./harness");

const { window, doc, errs, html } = load("gaps.html", { runScripts: "dangerously" });
const bad = [];
const data = JSON.parse(doc.getElementById("gapdata").textContent);
const rq = data.find(r => r[2] === "R" && r[3] === "Q" && r[4] === "total");
if (!rq || rq[6] !== "subpoly" || rq[7] !== "R = O(Q^4)" ||
    rq[9] !== "R >= Q^(4-o(1))" || rq[10] !== "table" || rq[11] !== "OpenAIQuarticRQ") {
  bad.push("R versus Q must use the quartic table endpoint with subpolynomial slack");
}
const rows = () => doc.querySelectorAll("#gbody tr").length;
const count = () => doc.getElementById("gcount").textContent;
/* the table draws at most a page of rows, so the count line reads
   "1000 of 10594 matching": the second number is the one that moves */
const shown = () => {
  const m = count().match(/of ([\d,]+) matching/) || count().match(/([\d,]+)/);
  return m ? Number(m[1].replace(/,/g, "")) : NaN;
};
const ev = (el, t) => el.dispatchEvent(new window.Event(t, { bubbles: true }));

console.log("  drawn rows", rows(), "|", count());
if (!rows()) bad.push("no rows drawn at all");
const tr = doc.querySelector("#gbody tr");
if (tr) {
  console.log("  row 1:", tr.textContent.replace(/\s+/g, " ").trim().slice(0, 110));
  if (!tr.querySelector("a")) bad.push("first row has no link out");
}

const before = shown();
const f = doc.getElementById("gf");
f.value = "d r";
ev(f, "input");
console.log('  filter "d r":', count());
if (!(shown() < before)) bad.push("the text filter did not narrow anything");
f.value = "";
ev(f, "input");
if (shown() !== before) bad.push("clearing the filter did not restore the count");

const sets = doc.querySelectorAll("#gset input");
sets[1].checked = false;
sets[2].checked = false;
ev(sets[1], "change");
console.log("  total only:", count());
if (!(shown() < before)) bad.push("unticking two settings did not narrow anything");
sets[1].checked = true;
sets[2].checked = true;
ev(sets[1], "change");

const docs = doc.querySelectorAll("#gdoc input");
docs[2].checked = true;
ev(docs[2], "change");
console.log("  documented only:", count(), "| drawn", rows());
docs[0].checked = true;
ev(docs[0], "change");

const v = doc.getElementById("gv");
v.value = "bare";
ev(v, "input");
console.log("  bare only:", count());
if (shown() >= before) bad.push("the state filter did not narrow anything");

/* an unrendered template tag or a stringified null in the page is a build bug */
const junk = html.match(/\{\{|\{%|>None<|>undefined</g);
if (junk) bad.push("suspicious tokens in the page: " + [...new Set(junk)].join(" "));

done(bad, errs);
