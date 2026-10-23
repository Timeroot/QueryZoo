/* The Query Complexity Zoo -- client-side search and table controls. */
(function () {
  "use strict";

  var ROOT = document.body.getAttribute("data-root") || "";

  /* ------------------------------------------------------------- search */
  var input = document.getElementById("q");
  var panel = document.getElementById("results");
  var index = null;
  var sel = -1;

  function load() {
    if (index) return Promise.resolve(index);
    return fetch(ROOT + "search-index.json")
      .then(function (r) { return r.json(); })
      .then(function (j) { index = j; return j; });
  }

  var KIND_LABEL = {
    measure: "measure", "function": "function", pair: "pair",
    concept: "concept", open: "open problem", ref: "reference", page: "page"
  };
  var KIND_RANK = { measure: 0, pair: 1, "function": 2, concept: 3, open: 4, page: 5, ref: 6 };

  function score(item, terms) {
    var t = item.t.toLowerCase(), s = (item.s || "").toLowerCase(), x = (item.x || "").toLowerCase();
    var total = 0;
    for (var i = 0; i < terms.length; i++) {
      var q = terms[i], hit = 0;
      if (t === q) hit = 120;
      else if (t.indexOf("(" + q + ")") >= 0) hit = 100;      /* exact id match */
      else if (t.indexOf(q) === 0) hit = 60;
      else if (t.indexOf(q) > 0) hit = 40;
      else if (s.indexOf(q) >= 0) hit = 18;
      else if (x.indexOf(q) >= 0) hit = 7;
      if (!hit) return -1;
      total += hit;
    }
    return total - (KIND_RANK[item.k] || 5);
  }

  function render(list, q) {
    if (!list.length) {
      panel.innerHTML = '<div class="none">No match for &ldquo;' + esc(q) + '&rdquo;</div>';
      panel.hidden = false;
      return;
    }
    var html = "";
    for (var i = 0; i < list.length; i++) {
      var it = list[i];
      html += '<a href="' + ROOT + it.u + '"' + (i === sel ? ' class="sel"' : "") + ">" +
        '<div class="rk">' + (KIND_LABEL[it.k] || it.k) + "</div>" +
        '<div class="rt">' + esc(it.t) + "</div>" +
        (it.s ? '<div class="rs">' + esc(it.s.slice(0, 120)) + "</div>" : "") +
        "</a>";
    }
    panel.innerHTML = html;
    panel.hidden = false;
  }

  function esc(s) {
    return String(s).replace(/[&<>"]/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c];
    });
  }

  function run() {
    var q = input.value.trim();
    if (q.length < 1) { panel.hidden = true; return; }
    load().then(function (idx) {
      var terms = q.toLowerCase().split(/\s+/);
      var out = [];
      for (var i = 0; i < idx.length; i++) {
        var sc = score(idx[i], terms);
        if (sc >= 0) out.push([sc, idx[i]]);
      }
      out.sort(function (a, b) { return b[0] - a[0]; });
      sel = -1;
      render(out.slice(0, 25).map(function (p) { return p[1]; }), q);
    });
  }

  if (input) {
    input.addEventListener("input", run);
    input.addEventListener("focus", function () { if (input.value) run(); });
    input.addEventListener("keydown", function (e) {
      var links = panel.querySelectorAll("a");
      if (e.key === "ArrowDown" || e.key === "ArrowUp") {
        e.preventDefault();
        if (!links.length) return;
        sel += e.key === "ArrowDown" ? 1 : -1;
        if (sel < 0) sel = links.length - 1;
        if (sel >= links.length) sel = 0;
        for (var i = 0; i < links.length; i++) links[i].className = i === sel ? "sel" : "";
        links[sel].scrollIntoView({ block: "nearest" });
      } else if (e.key === "Enter") {
        if (sel >= 0 && links[sel]) { e.preventDefault(); window.location = links[sel].href; }
      } else if (e.key === "Escape") {
        panel.hidden = true; input.blur();
      }
    });
    document.addEventListener("click", function (e) {
      if (!panel.contains(e.target) && e.target !== input) panel.hidden = true;
    });
    document.addEventListener("keydown", function (e) {
      if (e.key === "/" && document.activeElement !== input &&
          !/^(INPUT|TEXTAREA)$/.test(document.activeElement.tagName)) {
        e.preventDefault(); input.focus();
      }
    });
    load();
  }

  /* ------------------------------------------------------- matrix views */
  /* Which of total/partial/relation the grids are showing.  The scope filter
     below reads it too: a measure with no definition in the current setting
     has nothing to say, so its row and column come out of the table. */
  var matrixView = "total";
  var onMatrixView = null;

  var mc = document.getElementById("matrix-controls");
  if (mc) {
    var btns = mc.querySelectorAll("[data-view]");
    btns.forEach(function (b) {
      b.addEventListener("click", function () {
        btns.forEach(function (o) { o.classList.remove("on"); });
        b.classList.add("on");
        matrixView = b.getAttribute("data-view");
        document.body.classList.remove("view-total", "view-partial", "view-relation");
        document.body.classList.add("view-" + matrixView);
        if (onMatrixView) onMatrixView();
      });
    });
    var ht = document.getElementById("hide-tight");
    if (ht) ht.addEventListener("change", function () {
      document.body.classList.toggle("dim-tight", ht.checked);
    });
    /* Blanks out the cells nobody wrote down: what is left is the data. */
    var hd = document.getElementById("hide-derived");
    if (hd) hd.addEventListener("change", function () {
      document.body.classList.toggle("hide-derived", hd.checked);
    });
  }

  /* ------------------------------------------- matrix scope / categories */
  /* The full grid holds every measure; showing a subset is done by injecting
     one stylesheet of `display:none` rules rather than touching 4000 cells. */
  var metaEl = document.getElementById("matrix-meta");
  if (metaEl) {
    var meta = JSON.parse(metaEl.textContent);
    var SCOPE_RANK = { core: 0, recorded: 1, all: 2 };
    var scope = "core";
    var offCats = {};
    var sheet = document.createElement("style");
    document.head.appendChild(sheet);

    var wrapCore = document.getElementById("wrap-core");
    var wrapAll = document.getElementById("wrap-all");
    /* The ladder is a table of its own -- its rows and columns are in the
       hand-written order from site.yaml, which no stylesheet could produce
       out of the full grid. */
    var wrapLadder = document.getElementById("wrap-ladder");
    var catbox = document.getElementById("matrix-cats");
    var countEl = document.getElementById("matrix-count");
    var scopeBtns = mc ? mc.querySelectorAll("[data-scope]") : [];
    var catInputs = catbox ? catbox.querySelectorAll("input[type=checkbox]") : [];

    function visible(m) {
      return SCOPE_RANK[m.scope] <= SCOPE_RANK[scope] && !offCats[m.cat];
    }

    /* Defined -- in any conventional sense -- in the setting on screen? */
    function defined(m) {
      return !m.nd || m.nd.indexOf(matrixView) < 0;
    }

    /* Defined, but nothing for a grid of exponents to say: it degenerates into
       another measure in this setting, or it is dimensionless and no exponent
       can relate it to a query count.  Its pair pages are still built -- the
       relations are computed and are a useful check on the closure. */
    function comparable(m) {
      return !m.nc || m.nc.indexOf(matrixView) < 0;
    }

    function hideRules(tbl, id) {
      return "#" + tbl + " tr.y-" + id + ",#" + tbl + " .x-" + id;
    }

    /* A grid is skipped at load (class mj-defer) because MathJax mismeasures
       inside display:none; typeset it once, on first reveal. */
    function reveal(wrap) {
      if (!wrap || !wrap.classList.contains("mj-defer")) return;
      wrap.classList.remove("mj-defer");
      if (window.MathJax && window.MathJax.typesetPromise) {
        window.MathJax.typesetPromise([wrap]).catch(function () {});
      }
    }

    function applyScope() {
      var core = scope === "core";
      var ladder = scope === "ladder";
      var big = !core && !ladder;
      /* How many measures each button would show, in the setting on screen and
         under the current chips -- what goes on the buttons, so that no button
         promises a measure the grid will not draw. */
      var tier = { core: 0, recorded: 0, all: 0, ladder: 0 };
      /* ...and why the rest are out, for the scope showing: no definition in
         this setting, dimensionless everywhere, or degenerate in this one. */
      var out = { undef: 0, dimless: 0, degen: 0 };
      var inLadder = {};
      (meta.ladder || []).forEach(function (id) { inLadder[id] = true; });
      /* the core grid is not square: rdeg has a column but no recorded row */
      var isRow = {}, isCol = {}, coreRows = 0, coreCols = 0;
      ((meta.core || {}).rows || []).forEach(function (id) { isRow[id] = true; });
      ((meta.core || {}).cols || []).forEach(function (id) { isCol[id] = true; });
      var hidden = [];
      meta.measures.forEach(function (m) {
        var rank = SCOPE_RANK[m.scope];
        var inScope = core ? m.scope === "core"
          : ladder ? inLadder[m.id]
          : rank <= SCOPE_RANK[scope] && !offCats[m.cat];
        if (!defined(m) || !comparable(m)) {
          /* out of every grid, whatever the scope */
          if (inScope) {
            if (!defined(m)) out.undef++;
            else if (m.dl) out.dimless++;
            else out.degen++;
          }
          hidden.push(hideRules("matrix", m.id), hideRules("matrix-all", m.id),
                      hideRules("matrix-ladder", m.id));
          return;
        }
        if (m.scope === "core") tier.core++;
        if (isRow[m.id]) coreRows++;
        if (isCol[m.id]) coreCols++;
        if (inLadder[m.id]) tier.ladder++;
        if (!offCats[m.cat]) {
          tier.all++;
          if (rank <= SCOPE_RANK.recorded) tier.recorded++;
        }
        if (!visible(m)) hidden.push(hideRules("matrix-all", m.id));
      });
      sheet.textContent = hidden.length ? hidden.join(",") + "{display:none}" : "";
      wrapCore.hidden = !core;
      wrapAll.hidden = !big;
      if (wrapLadder) wrapLadder.hidden = !ladder;
      /* The chips filter the full grid only: the ladder is a hand-picked list,
         so there is nothing sensible for them to do while it is showing. */
      if (catbox) catbox.hidden = !big;
      document.body.classList.toggle("scope-all", big);
      labelScopes(tier);
      if (countEl) {
        var what = matrixView === "relation" ? "relations"
          : matrixView === "partial" ? "partial functions" : "total functions";
        var why = [];
        if (out.undef) why.push(out.undef + " undefined for " + what);
        if (out.dimless) why.push(out.dimless + " dimensionless");
        if (out.degen) why.push(out.degen + " degenerate here");
        var n = ladder ? tier.ladder : tier[scope];
        countEl.textContent = (ladder
          ? n + " measures, roughly ordered by size"
          : core ? coreRows + " x " + coreCols + " core table"
                 : n + " x " + n + " grid")
          + (why.length ? " · " + why.join(", ") + ", hidden" : "");
      }
      reveal(big ? wrapAll : ladder ? wrapLadder : null);
    }

    /* Put the live counts on the buttons, and drop a button whose grid would be
       a duplicate: the scopes nest, so equal counts mean the same measures, and
       an "All" that draws exactly what "With records" drew reads as a bug. */
    function labelScopes(tier) {
      var dup = null;
      scopeBtns.forEach(function (b) {
        var v = b.getAttribute("data-scope");
        var n = b.querySelector(".n");
        if (n) n.textContent = tier[v];
        if (v === "recorded" && tier.recorded === tier.all) dup = b;
      });
      scopeBtns.forEach(function (b) {
        b.hidden = b === dup && scope !== "recorded";
      });
    }

    onMatrixView = applyScope;

    bindSeg("matrix-scope", "data-scope", function (v) {
      scope = v;
      applyScope();
      try { history.replaceState(null, "", v === "core" ? "#" : "#" + v); } catch (e) {}
    });

    catInputs.forEach(function (cb) {
      cb.addEventListener("change", function () {
        offCats[cb.value] = !cb.checked;
        applyScope();
      });
    });
    function setAllCats(on) {
      catInputs.forEach(function (cb) { cb.checked = on; offCats[cb.value] = !on; });
      applyScope();
    }
    var ca = document.getElementById("cats-all"), cn = document.getElementById("cats-none");
    if (ca) ca.addEventListener("click", function () { setAllCats(true); });
    if (cn) cn.addEventListener("click", function () { setAllCats(false); });

    /* #recorded, #all, #ladder select a scope on load; the buttons are the
       list of what is legal, so a new one needs no second registration. */
    var want = (location.hash || "").replace(/^#/, "");
    var b = /^[a-z]+$/.test(want) && want !== "core"
      ? mc.querySelector('[data-scope="' + want + '"]') : null;
    if (b) {
      scope = want;
      mc.querySelectorAll("[data-scope]").forEach(function (o) { o.classList.remove("on"); });
      b.classList.add("on");
    }
    applyScope();
  }

  /* ------------------------------------------ matrix crosshair + tooltip */
  var mtables = document.querySelectorAll("table.matrix");
  if (mtables.length) {
    var tip = null;

    function hide() { if (tip) { tip.remove(); tip = null; } }

    function show(td) {
      var src = td.querySelector(".celltip");
      if (!src) return;
      hide();
      tip = document.createElement("div");
      tip.id = "floattip";
      tip.innerHTML = src.innerHTML;
      document.body.appendChild(tip);

      var r = td.getBoundingClientRect();
      var h = tip.offsetHeight, w = tip.offsetWidth;
      var top = r.bottom + 8;
      if (top + h > window.innerHeight - 8) top = Math.max(8, r.top - h - 8);
      var left = r.left + r.width / 2 - w / 2;
      left = Math.min(Math.max(8, left), window.innerWidth - w - 8);
      tip.style.top = top + "px";
      tip.style.left = left + "px";
      // .celltip is in MathJax's ignore list, so the clone still holds raw TeX.
      if (window.MathJax && window.MathJax.typesetPromise) {
        window.MathJax.typesetPromise([tip]).then(reposition).catch(function () {});
      }

      function reposition() {
        if (!tip) return;
        var hh = tip.offsetHeight;
        var t = r.bottom + 8;
        if (t + hh > window.innerHeight - 8) t = Math.max(8, r.top - hh - 8);
        tip.style.top = t + "px";
      }
    }

    /* Crosshair: with 67 columns, knowing which pair you are on matters.
       Keep references to the lit headers -- re-scanning a 4500-cell table on
       every mouseover is not free. */
    var lit = [];
    function crosshair(tbl, td) {
      var col = td && td.getAttribute("data-col");
      var th = col ? tbl.querySelector('th.colhead[data-col="' + col + '"]') : null;
      var rh = td ? td.parentNode.querySelector("th.rowhead") : null;
      if (lit[0] === th && lit[1] === rh) return;
      lit.forEach(function (el) { if (el) el.classList.remove("hl"); });
      lit = [th, rh];
      lit.forEach(function (el) { if (el) el.classList.add("hl"); });
    }

    mtables.forEach(function (mtable) {
      mtable.addEventListener("mouseover", function (e) {
        var td = e.target.closest ? e.target.closest("td[data-col]") : null;
        crosshair(mtable, td);
        if (td && td.querySelector(".celltip")) show(td);
      });
      mtable.addEventListener("mouseout", function (e) {
        var td = e.target.closest ? e.target.closest("td.mcell") : null;
        if (td && !td.contains(e.relatedTarget)) hide();
      });
      mtable.addEventListener("mouseleave", function () { crosshair(mtable, null); hide(); });
      mtable.addEventListener("focusin", function (e) {
        var td = e.target.closest ? e.target.closest("td.mcell") : null;
        crosshair(mtable, td);
        if (td) show(td);
      });
      mtable.addEventListener("focusout", hide);
    });
    window.addEventListener("scroll", hide, true);
  }

  /* ------------------------------------------------------ relation table */
  var rf = document.getElementById("relfilter");
  var rtable = document.getElementById("reltable");
  if (rtable) {
    var rows = Array.prototype.slice.call(rtable.querySelectorAll("tbody tr"));
    var setFilter = "all", stFilter = "all";
    var count = document.getElementById("relcount");

    function apply() {
      var q = (rf && rf.value || "").trim().toLowerCase();
      var shown = 0;
      rows.forEach(function (tr) {
        var ok = true;
        if (q) ok = (tr.getAttribute("data-search") || "").indexOf(q) >= 0;
        if (ok && setFilter !== "all") {
          ok = (" " + (tr.getAttribute("data-sets") || "") + " ").indexOf(" " + setFilter + " ") >= 0;
        }
        if (ok && stFilter !== "all") {
          ok = (" " + (tr.getAttribute("data-statuses") || "") + " ").indexOf(" " + stFilter + " ") >= 0;
        }
        tr.style.display = ok ? "" : "none";
        if (ok) shown++;
      });
      if (count) count.textContent = shown + " of " + rows.length + " pairs";
    }

    if (rf) rf.addEventListener("input", apply);
    bindSeg("relsetting", "data-set", function (v) { setFilter = v; apply(); });
    bindSeg("relstatus", "data-st", function (v) { stFilter = v; apply(); });
    apply();
  }

  function bindSeg(id, attr, cb) {
    var el = document.getElementById(id);
    if (!el) return;
    var bs = el.querySelectorAll("[" + attr + "]");
    bs.forEach(function (b) {
      b.addEventListener("click", function () {
        bs.forEach(function (o) { o.classList.remove("on"); });
        b.classList.add("on");
        cb(b.getAttribute(attr));
      });
    });
  }

  /* ------------------------------------------- measure page: all neighbours
     The default rows are the entry's hand-picked `related:` list. The rest of
     the zoo is already in the page, in a second <tbody>; this just unhides it.
     Server-rendered rather than fetched, so the fold works with no network and
     the full table is in the page source for anyone reading it that way. */
  document.querySelectorAll("[data-nbrs-toggle]").forEach(function (btn) {
    var rest = document.querySelector(".nbrs-rest");
    if (!rest) return;
    btn.addEventListener("click", function () {
      var showing = !rest.hidden;
      rest.hidden = showing;
      btn.textContent = btn.getAttribute(showing ? "data-all" : "data-few");
      btn.classList.toggle("on", !showing);
    });
  });

  /* --------------------------------------------------------- ref filter */
  var reff = document.getElementById("reffilter");
  if (reff) {
    var entries = Array.prototype.slice.call(document.querySelectorAll(".bibentry"));
    reff.addEventListener("input", function () {
      var q = reff.value.trim().toLowerCase();
      entries.forEach(function (li) {
        li.style.display = !q || (li.getAttribute("data-search") || "").indexOf(q) >= 0 ? "" : "none";
      });
    });
  }
})();
