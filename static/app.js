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
  var mc = document.getElementById("matrix-controls");
  if (mc) {
    var btns = mc.querySelectorAll("[data-view]");
    btns.forEach(function (b) {
      b.addEventListener("click", function () {
        btns.forEach(function (o) { o.classList.remove("on"); });
        b.classList.add("on");
        document.body.classList.remove("view-total", "view-partial", "view-relation");
        document.body.classList.add("view-" + b.getAttribute("data-view"));
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
    var catbox = document.getElementById("matrix-cats");
    var countEl = document.getElementById("matrix-count");
    var catInputs = catbox ? catbox.querySelectorAll("input[type=checkbox]") : [];

    function visible(m) {
      return SCOPE_RANK[m.scope] <= SCOPE_RANK[scope] && !offCats[m.cat];
    }

    function applyScope() {
      var hidden = [], shown = 0;
      meta.measures.forEach(function (m) {
        if (visible(m)) shown++;
        else hidden.push("#matrix-all tr.y-" + m.id + ",#matrix-all .x-" + m.id);
      });
      sheet.textContent = hidden.length ? hidden.join(",") + "{display:none}" : "";
      var core = scope === "core";
      wrapCore.hidden = !core;
      wrapAll.hidden = core;
      if (catbox) catbox.hidden = core;
      document.body.classList.toggle("scope-all", !core);
      if (countEl) {
        countEl.textContent = core
          ? meta.counts.core + " x " + meta.counts.core + " published table"
          : shown + " x " + shown + " of " + meta.counts.all + " measures";
      }
      /* The full grid is skipped at load (class mj-defer) because MathJax
         mismeasures inside display:none; typeset it once, on first reveal. */
      if (!core && wrapAll.classList.contains("mj-defer")) {
        wrapAll.classList.remove("mj-defer");
        if (window.MathJax && window.MathJax.typesetPromise) {
          window.MathJax.typesetPromise([wrapAll]).catch(function () {});
        }
      }
    }

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

    var want = (location.hash || "").replace(/^#/, "");
    if (SCOPE_RANK[want] !== undefined && want !== "core") {
      scope = want;
      var b = mc.querySelector('[data-scope="' + want + '"]');
      if (b) {
        mc.querySelectorAll("[data-scope]").forEach(function (o) { o.classList.remove("on"); });
        b.classList.add("on");
      }
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
