/* pair.html -- the pair browser.
 *
 * Every ordered pair of measures (all 67x67 of them, diagonal included) is a
 * view of this one page. The prose of a recorded relation arrives as HTML,
 * rendered by the same Jinja macro the rest of the site uses; everything the
 * build *derived* -- exponents, tightness chips, derivation chains -- arrives
 * as data and is assembled here. Shards are per row measure, so walking along
 * a row of the matrix costs one fetch.
 */
(function () {
  "use strict";

  var ROOT = document.body.getAttribute("data-root") || "";
  var view = document.getElementById("pairview");
  if (!view) return;

  var pickA = document.getElementById("pick-a");
  var pickB = document.getElementById("pick-b");
  var crumb = document.getElementById("crumb");
  var META = null;
  var shards = {};       /* row id -> promise of {a, cols} */
  var SITE = (document.title.split("·").pop() || "").trim();

  /* ------------------------------------------------------------ helpers */
  function esc(s) {
    return String(s == null ? "" : s).replace(/[&<>"]/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c];
    });
  }
  function tex(s) { return '<span class="tex">\\(' + esc(s) + "\\)</span>"; }
  function murl(id) { return ROOT + "measures/" + id + ".html"; }
  function purl(a, b, anchor) {
    return ROOT + "pair.html?a=" + a + "&b=" + b + (anchor ? "#" + anchor : "");
  }
  function sym(id) { return (META.measures[id] || {}).sym || id; }
  /* symbols carry their argument ("\mathrm{D}(f)"); sometimes we supply it */
  function bare(id) { return sym(id).replace(/\((f|x)\)\s*$/, ""); }
  function mname(id) { return (META.measures[id] || {}).name || id; }
  function cites(refs) {
    if (!refs || !refs.length) return "";
    return '<span class="refs">[' + refs.map(function (k) {
      return '<a class="xref ref" href="' + ROOT + "refs.html#" + esc(k) + '">' + esc(k) + "</a>";
    }).join(", ") + "]</span>";
  }
  function witlink(id) {
    var f = META.functions[id];
    if (!f) return esc(id);
    return '<a class="xref function" href="' + ROOT + "functions/" + esc(id) + '.html">' +
      tex(f.sym) + "</a>";
  }
  function setting(sid) {
    for (var i = 0; i < META.settings.length; i++) {
      if (META.settings[i].id === sid) return META.settings[i];
    }
    return { id: sid, name: sid, short: sid, blurb: "" };
  }
  function pill(sid) {
    var s = setting(sid);
    return '<span class="pill setting s-' + sid + '" title="' + esc(s.blurb) + '">' +
      esc(s.short) + "</span>";
  }
  function chip(kind, lower) {
    var tbl = lower ? META.chips_lo : META.chips;
    var names = lower ? META.chip_lo_names : META.chip_names;
    if (!tbl || !tbl[kind]) return "";
    return '<span class="tchip ' + (lower ? "lo " : "") + "c-" + kind + '" title="' +
      esc(names[kind]) + '">' + esc(tbl[kind]) + "</span>";
  }

  /* --------------------------------------------------------- derivations */
  function derivSummary(d) {
    if (d.vals) {
      /* the separation is two recorded values on one family, compared */
      var parts = d.vals.map(function (x) { return tex(x.m + " = " + x.tex); });
      return "derived: read off the recorded values" +
        (d.fn ? " on " + esc(d.fn) : "") + ", " + parts.join(" against ") +
        (d.how === "setting" ? " (inherited from " + esc(d.from_setting) + ")" : "");
    }
    if (d.how === "setting") {
      return "derived: holds because it holds for " + esc(d.from_setting) + " problems";
    }
    if (d.how === "push") {
      var n = d.steps.length - 1;
      return "derived: a separation pushed through " + n + " recorded bound" + (n === 1 ? "" : "s");
    }
    return "derived: " + tex(d.path.join(" \\to "));
  }

  /* Every line in a cell's detail is either an upper bound or a separation --
     including the non-polynomial ones. The bullet knows which it is. */
  function sidedet(v, label) {
    if (!v) return "";
    if (v.side) label = v.side === "lower" ? "separation" : "upper";
    var h = '<div class="dline"><span class="dlbl">' + esc(label) + "</span>" +
      '<span class="dst">' + tex(v.tex) + "</span>";
    if (v.witness) h += '<span class="wit">witness: ' + witlink(v.witness) + "</span>";
    h += cites(v.refs);
    if (v.deriv && !(v.deriv.steps || []).length) {
      /* nothing to unfold: the summary is the whole derivation */
      h += '<div class="deriv flat">' + derivSummary(v.deriv) + "</div>";
      if (v.note) h += '<div class="note">' + v.note + "</div>";
    } else if (v.deriv) {
      h += '<details class="deriv"><summary>' + derivSummary(v.deriv) + "</summary><ol class=\"dsteps\">";
      v.deriv.steps.forEach(function (st) {
        h += "<li><span class=\"dst\">" + tex(st.tex) + "</span>" +
          (st.witness ? '<span class="wit">witness: ' + witlink(st.witness) + "</span>" : "") +
          cites(st.refs) +
          '<span class="dim small">[' + esc(st.setting) + "]</span>" +
          '<a class="dim small" href="' + purl(st.a, st.b) + '">record</a></li>';
      });
      h += "</ol></details>";
    } else if (v.note) {
      h += '<div class="note">' + v.note + "</div>";
    }
    return h + "</div>";
  }

  /* -------------------------------------------------------------- blocks */
  function header(a, b, p) {
    var ma = META.measures[a] || {}, mb = META.measures[b] || {};
    var h = '<header class="pairhead"><h1>' +
      '<a href="' + murl(a) + '" class="cat-' + esc(ma.cat) + '">' + tex(ma.sym) + "</a>" +
      '<span class="vs">' + (a === b ? "against itself" : "versus") + "</span>" +
      (a === b ? "" : '<a href="' + murl(b) + '" class="cat-' + esc(mb.cat) + '">' + tex(mb.sym) + "</a>") +
      "</h1>";
    h += '<p class="lede">' + (a === b
      ? "A measure paired with itself. The bound is an equality; what is worth knowing here is " +
        "how the measure behaves under <em>composition</em> and how it moves with its " +
        "<em>parameters</em>."
      : "How large can " + tex(ma.sym) + " be as a function of " + tex(mb.sym) + "? " +
        "Upper bounds hold for <em>all</em> problems in the setting; lower bounds are " +
        "<em>separations</em>, exhibited by a named family.") + "</p>";
    h += '<p class="pairnav">';
    if (a !== b) {
      h += '<a class="btn" href="' + purl(b, a) + '">&#8646; the other direction: ' +
        tex(mb.sym) + " vs " + tex(ma.sym) + "</a>";
    }
    h += '<a class="btn ghost" href="' + murl(a) + '">' + esc(mname(a)) + "</a>";
    if (a !== b) h += '<a class="btn ghost" href="' + murl(b) + '">' + esc(mname(b)) + "</a>";
    return h + "</p></header>";
  }

  function cellCard(a, b, c) {
    var sa = sym(a), sb = sym(b);
    var h = '<section class="card cellcard"><h2>Matrix cell ' +
      '<span class="dim">(total functions, exponents only)</span></h2>' +
      '<div class="cellbig ' + (c.tight ? "tight" : "gapc") + '">' +
      '<span class="a">' + esc(c.a) + '</span><span class="comma">,</span>' +
      '<span class="b">' + esc(c.b) + "</span></div>" +
      '<div class="cellexp"><p>There is a total \\(g\\) with ' +
      tex(sa + " \\ge " + sb + "^{" + c.a + " - o(1)}") + ", ";
    h += (String(c.b) === "?"
      ? "and <b>no polynomial upper bound is known</b> in the other direction."
      : "and every total \\(f\\) satisfies " + tex(sa + " \\le " + sb + "^{" + c.b + " + o(1)}") + ".");
    if (c.tight) h += " <b>These match &mdash; the exponent is settled.</b>";
    h += "</p>";
    if (c.w) h += "<p>Separation witness: " + witlink(c.w) + ".</p>";
    if (c.refs) h += "<p>" + cites(c.refs) + "</p>";
    if (c.note) h += '<div class="note">' + c.note + "</div>";
    if (c.own) {
      h += '<div class="banner star">&#9733; This exponent is the zoo\'s own: ' +
        (c.own_note || "") + "</div>";
    }
    h += '<p class="dim">Exponents suppress \\(o(1)\\) in the exponent, hence all log factors. ' +
      "The statements below are the fine-grained versions.</p></div></section>";
    return h;
  }

  /* Only a number can have come from the exponent table; "exp", "log" and the
     glyphs belong to the derived layer. */
  function numeric(v) { return /^[0-9]/.test(String(v)); }

  /* An exponential upper bound met by an exponential separation is as settled
     as `2, 2` is -- say so rather than "exponential only". */
  function verdictWord(d) {
    var w = META.verdicts[d.verdict];
    if ((d.verdict === "exp" || d.verdict === "log") &&
        d.a !== "?" && d.b !== "?" && !numeric(d.b)) {
      return "settled, " + (d.verdict === "exp" ? "exponentially" : "logarithmically");
    }
    return w;
  }

  function derivedCard(tok) {
    var h = '<section class="card derivedcard"><h2>Best bounds the zoo can justify ' +
      '<span class="dim">&mdash; computed from the records, per setting</span></h2>' +
      '<table class="dtab"><thead><tr><th>setting</th><th>separation \\(\\ge\\)</th>' +
      "<th>upper bound \\(\\le\\)</th><th></th></tr></thead><tbody>";
    META.settings.forEach(function (s) {
      var d = tok[s.id];
      if (!d) return;
      h += '<tr class="v-' + d.verdict + '"><th>' + pill(s.id) + "</th>" +
        '<td class="ex">' + esc(d.a) + chip(d.chip_lo_kind, true) + "</td>" +
        '<td class="ex">' + esc(d.b) + chip(d.chip_kind) + "</td>" +
        '<td class="vw">' + esc(verdictWord(d)) +
        (d.tight_exact ? " &mdash; with equality" : "") +
        (d.derived ? ' <span class="tag drv">derived</span>' : "") + "</td></tr>";
      h += '<tr class="det v-' + d.verdict + '"><td colspan="4">' +
        sidedet(d.fails, "upper") + sidedet(d.other_up, "upper") +
        sidedet(d.other_lo, "separation") +
        sidedet(d.up, "upper") + sidedet(d.lo, "separation");
      if (!d.up && numeric(d.b)) {
        h += '<div class="dline"><span class="dlbl">upper</span>exponent ' +
          tex(d.b) + " from the matrix table</div>";
      }
      if (!d.lo && numeric(d.a)) {
        h += '<div class="dline"><span class="dlbl">separation</span>exponent ' +
          tex(d.a) + " from the matrix table</div>";
      }
      h += "</td></tr>";
    });
    h += '</tbody></table><p class="dim small">Exponents only tell you so much: the chip says ' +
      'whether the bound is exact (<span class="tchip c-exact">&le;</span>), tight to a constant ' +
      '(<span class="tchip c-theta">&Theta;</span>), tight up to logs ' +
      '(<span class="tchip c-tilde">&Otilde;</span>) or a plain \\(O\\) ' +
      '(<span class="tchip c-const">O</span>). Anything marked ' +
      '<span class="tag drv">derived</span> was computed by the build &mdash; from the ' +
      "transitive closure, from a separation pushed through a chain of bounds, or from " +
      'setting inheritance &mdash; and is not in the data. See ' +
      '<a href="' + ROOT + 'editing.html#derived">how that works</a>.</p></section>';
    return h;
  }

  function settingCards(a, b, rels) {
    var h = "";
    META.settings.forEach(function (s) {
      var blocks = rels[s.id];
      h += '<section class="card settingcard s-' + s.id + '"><h2>' + pill(s.id) + " " +
        esc(s.name) + "</h2>";
      if (blocks && blocks.length) {
        h += blocks.join("");
      } else {
        var da = (META.measures[a] || {}).def || {}, db = (META.measures[b] || {}).def || {};
        if (da[s.id] === "no" || db[s.id] === "no") {
          h += '<p class="dim empty">Not applicable: ' +
            (da[s.id] === "no" ? tex(sym(a)) : tex(sym(b))) +
            " is not defined for " + esc(s.short) + " problems.</p>";
        } else {
          h += '<p class="dim empty">No entry yet for this pair in the ' + esc(s.short) +
            " setting. That is a gap in the zoo, not necessarily in the literature &mdash; " +
            'see <a href="' + ROOT + 'editing.html">Editing</a> if you want to add one.</p>';
        }
      }
      h += "</section>";
    });
    return h;
  }

  function diagonalCard(a, self) {
    var s = bare(a);
    var h = '<section class="card"><h2>The trivial cell</h2><p>' +
      tex(s + "(f) \\le " + s + "(f)") + ", with nothing hidden: the diagonal of the matrix is " +
      "\\(1,1\\) by definition. The interesting questions about a measure and itself are " +
      "composition and parameters.</p>";
    if (self.facts && self.facts.length) {
      h += "<ul class=\"tick\">" + self.facts.map(function (f) {
        return "<li>" + f + "</li>";
      }).join("") + "</ul>";
    }
    h += "</section>";
    if (self.params && self.params.length) {
      h += '<section class="card"><h2>Parameters</h2>';
      self.params.forEach(function (p) {
        h += '<div class="paramblock"><h3>' + tex(p.symbol) +
          (p["default"] ? ' <span class="dim">default ' + tex(p["default"]) + "</span>" : "") +
          (p.range ? ' <span class="dim">range ' + tex(p.range) + "</span>" : "") + "</h3>";
        if (p.description) h += '<div class="note">' + p.description + "</div>";
        if (p.dependence) h += '<div class="prose">' + p.dependence + "</div>";
        h += "</div>";
      });
      h += "</section>";
    }
    if (self.comp && self.comp.length) {
      h += '<section class="card"><h2>Composition records elsewhere involving ' + tex(s) +
        "</h2>" + self.comp.join("") + "</section>";
    }
    return h;
  }

  function emptyCard(a, b) {
    return '<section class="card"><h2>Nothing on record</h2><p>The zoo holds no statement ' +
      "relating " + tex(sym(a)) + " to " + tex(sym(b)) + ", and cannot derive one from what " +
      "it does hold. That is a gap in the zoo, not a theorem &mdash; see " +
      '<a href="' + ROOT + 'editing.html">Editing</a>.</p></section>';
  }

  /* -------------------------------------------------------------- render */
  function shard(a) {
    if (!shards[a]) {
      shards[a] = fetch(ROOT + "api/pair/" + a + ".json")
        .then(function (r) { return r.ok ? r.json() : { a: a, cols: {} }; })
        .catch(function () { return { a: a, cols: {} }; });
    }
    return shards[a];
  }

  function draw(a, b, anchor) {
    return Promise.all([metaP, shard(a)]).then(function (res) {
      var data = res[1];
      var p = (data.cols || {})[b] || null;
      var h = header(a, b, p);
      if (p && p.cell) h += cellCard(a, b, p.cell);
      if (p && p.tok && Object.keys(p.tok).length) h += derivedCard(p.tok);
      if (a === b && p && p.self) h += diagonalCard(a, p.self);
      if (!p) h += emptyCard(a, b);
      h += settingCards(a, b, (p && p.rels) || {});
      view.innerHTML = h;
      document.title = a + " vs " + b + " \u00b7 " + SITE;
      if (crumb) {
        crumb.innerHTML = '<a href="' + murl(a) + '">' + esc(a) + "</a> vs " +
          '<a href="' + murl(b) + '">' + esc(b) + "</a>";
      }
      if (pickA) pickA.value = a;
      if (pickB) pickB.value = b;
      if (window.MathJax && window.MathJax.typesetPromise) {
        return window.MathJax.typesetPromise([view]).catch(function () {}).then(function () {
          scrollTo(anchor);
        });
      }
      scrollTo(anchor);
    });
  }

  function scrollTo(anchor) {
    if (!anchor) { window.scrollTo(0, 0); return; }
    var el = document.getElementById(anchor);
    if (el) {
      el.scrollIntoView();
      el.classList.add("targeted");
    }
  }

  function current() {
    var q = new URLSearchParams(location.search);
    var a = q.get("a"), b = q.get("b");
    var hash = (location.hash || "").replace(/^#/, "");
    /* pair.html#D__R still works: that is what the old pair pages were called.
       With ?a=&b= present the hash is a record anchor instead (D__R__total). */
    if (!a && hash.indexOf("__") > 0) {
      var parts = hash.split("__");
      return [parts[0], parts[1], ""];
    }
    return [a, b, hash];
  }

  function go(a, b, anchor, push) {
    if (!META.measures[a]) a = "D";
    if (!META.measures[b]) b = a === "R" ? "D" : "R";
    if (push) {
      history.pushState(null, "", purl(a, b, anchor));
    }
    draw(a, b, anchor || null);
  }

  var metaP = fetch(ROOT + "api/meta.json")
    .then(function (r) { return r.json(); })
    .then(function (j) { META = j; return j; });

  metaP.then(function () {
    var c = current();
    go(c[0], c[1], c[2], false);
  }).catch(function (e) {
    view.innerHTML = '<div class="banner">Could not load the pair data: ' + esc(e) + "</div>";
  });

  window.addEventListener("popstate", function () {
    var c = current();
    go(c[0], c[1], c[2], false);
  });

  /* pair links anywhere on this page navigate without a reload */
  var RE = /(^|\/)pair\.html\?a=([A-Za-z0-9_]+)&b=([A-Za-z0-9_]+)(?:#(.*))?$/;
  document.addEventListener("click", function (e) {
    var link = e.target.closest ? e.target.closest("a") : null;
    if (!link || e.metaKey || e.ctrlKey || e.shiftKey || e.button !== 0) return;
    var m = RE.exec(link.getAttribute("href") || "");
    if (!m) return;
    e.preventDefault();
    go(m[2], m[3], m[4] || "", true);
  });

  if (pickA && pickB) {
    var jump = function () { go(pickA.value, pickB.value, "", true); };
    pickA.addEventListener("change", jump);
    pickB.addEventListener("change", jump);
    var swap = document.getElementById("swap");
    if (swap) swap.addEventListener("click", function () {
      go(pickB.value, pickA.value, "", true);
    });
  }
})();
