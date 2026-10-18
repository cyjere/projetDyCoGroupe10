# -*- coding: utf-8 -*-
"""
ABA / ABA+ Generator - Flask web app

Run locally:      python app.py   then open http://127.0.0.1:5000
Render (deploy):  gunicorn app:app
"""
import os
import sys
import json
import threading

from flask import Flask, request, render_template_string

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from aba_core import (
    parse_aba_text, analyze, render_attacks_graph, convert,
    is_atomic, is_circular, describe_framework, fmt_argument,
)

app = Flask(__name__)
# matplotlib is not thread-safe, so graphs are drawn one at a time
_draw_lock = threading.Lock()

EXAMPLE = """## Literals
L: [a,b,c,q,p,r,s,t]

## Assumptions
A: [a,b,c]

## Contraries
C(a): r
C(b): s
C(c): t

## Rules
[r1]: p <- q,a
[r2]: q <-
[r3]: r <- b,c
[r4]: t <- p,c
[r5]: s <- t

## Preferences
PREF: a > b
"""

HTML = """
<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>ABA / ABA+ Generator</title>
<style>
  :root { --ink:#0f172a; --soft:#475569; --muted:#94a3b8; --border:#e2e8f0;
          --primary:#4f46e5; --primary-dark:#4338ca; --primary-soft:#eef2ff; }
  * { box-sizing: border-box; }
  body { font-family: system-ui, -apple-system, sans-serif; color: var(--ink); background:#f8fafc; margin:0; line-height:1.5; }
  .page { max-width: 1000px; margin: 0 auto; padding: 2rem 1rem 3rem; }
  header { text-align:center; margin-bottom:1.5rem; }
  header h1 { font-size:2rem; margin:0 0 .4rem; }
  header p { color:var(--soft); margin:0; }
  .card { background:#fff; border:1px solid var(--border); border-radius:12px; margin-bottom:1.25rem; box-shadow:0 1px 3px rgba(15,23,42,.06); overflow:hidden; }
  .card-header { padding:.85rem 1.25rem; border-bottom:1px solid var(--border); font-weight:600; }
  .card-header .dot { display:inline-block; width:8px; height:8px; border-radius:50%; margin-right:.45rem; vertical-align:middle; background:var(--primary); }
  .card-body { padding:1.1rem 1.25rem; }
  textarea { width:100%; min-height:360px; border:0; outline:0; resize:vertical; padding:1rem; background:#0f172a; color:#e2e8f0; font-family:ui-monospace, monospace; font-size:13.5px; line-height:1.6; border-radius:8px; }
  .actions { display:flex; flex-wrap:wrap; gap:.6rem; margin-top:1rem; align-items:center; }
  .btn { padding:.6rem 1.1rem; border-radius:8px; font-size:.9rem; font-weight:600; border:1px solid var(--border); cursor:pointer; background:#fff; color:var(--soft); }
  .btn-primary { background:var(--primary); color:#fff; border-color:var(--primary-dark); }
  .check { display:flex; align-items:center; gap:.45rem; margin-left:auto; font-size:.9rem; cursor:pointer; }
  .alert { padding:.9rem 1.1rem; border-radius:8px; margin-bottom:1.25rem; font-size:.92rem; }
  .alert-error { background:#fef2f2; color:#7f1d1d; border:1px solid #fecaca; }
  .alert-warn { background:#fffbeb; color:#78350f; border:1px solid #fde68a; }
  .alert ul { margin:.3rem 0 0; padding-left:1.2rem; }
  ul.res { margin:0; padding-left:1.2rem; font-family:ui-monospace, monospace; font-size:13px; }
  ul.res li { margin-bottom:.2rem; }
  pre { margin:0; font-size:13px; background:#f1f5f9; padding:.8rem; border-radius:8px; overflow-x:auto; }
  .empty { color:var(--muted); font-style:italic; }
  .tags span { display:inline-block; margin:0 .5rem .4rem 0; padding:.25rem .6rem; border-radius:999px; font-size:.82rem; font-weight:600; }
  .yes { background:#dcfce7; color:#166534; } .no { background:#fee2e2; color:#991b1b; }
  .grid2 { display:grid; grid-template-columns:1fr 1fr; gap:1rem; }
  @media (max-width: 700px) { .grid2 { grid-template-columns:1fr; } .check { margin-left:0; } }
  .graph img { width:100%; height:auto; display:block; }
  .count { color:var(--muted); font-weight:400; }
</style>
</head>
<body>
<div class="page">
  <header>
    <h1>ABA / ABA+ Generator</h1>
    <p>Arguments, ABA attacks, non-circular/atomic conversion and ABA+ attacks (normal and reverse).</p>
  </header>

  <form method="post" class="card">
    <div class="card-header"><span class="dot"></span>Framework input</div>
    <div class="card-body">
      <textarea name="input" spellcheck="false" autocomplete="off">{{ input_text }}</textarea>
      <div class="actions">
        <button type="button" class="btn" id="btn-example">Example</button>
        <button type="submit" class="btn btn-primary">Run</button>
        <button type="button" class="btn" id="btn-clear">Clear</button>
        <label class="check">
          <input type="checkbox" name="auto_convert" {{ 'checked' if auto_convert else '' }}>
          Analyse the converted framework (non-circular + atomic)
        </label>
      </div>
    </div>
  </form>

  {% if error %}<div class="alert alert-error"><strong>Error:</strong> {{ error }}</div>{% endif %}
  {% if warnings %}
  <div class="alert alert-warn"><strong>Warnings</strong>
    <ul>{% for w in warnings %}<li>{{ w }}</li>{% endfor %}</ul>
  </div>
  {% endif %}

  {% if res %}
  <div class="card">
    <div class="card-header"><span class="dot"></span>0. Properties and conversion</div>
    <div class="card-body">
      <div class="tags">
        <span class="{{ 'no' if res.orig_circular else 'yes' }}">Original framework: {{ 'circular' if res.orig_circular else 'non-circular' }}</span>
        <span class="{{ 'yes' if res.orig_atomic else 'no' }}">{{ 'atomic' if res.orig_atomic else 'not atomic' }}</span>
      </div>
      <p style="margin:.3rem 0 .8rem">{{ res.conversion_msg }}</p>
      <div class="grid2">
        <div><strong>Original framework</strong><pre>{{ res.orig_desc }}</pre></div>
        <div><strong>Converted framework</strong><pre>{{ res.conv_desc }}</pre></div>
      </div>
      <p style="margin:.8rem 0 0;color:var(--soft)">The results below are computed on the <strong>{{ 'converted' if auto_convert else 'original' }}</strong> framework.</p>
    </div>
  </div>

  <div class="card">
    <div class="card-header"><span class="dot" style="background:#16a34a"></span>1. Arguments <span class="count">({{ res.args|length }})</span></div>
    <div class="card-body">
      {% if res.args %}<ul class="res">{% for x in res.args %}<li>{{ x }}</li>{% endfor %}</ul>
      {% else %}<p class="empty">No arguments.</p>{% endif %}
    </div>
  </div>

  <div class="card">
    <div class="card-header"><span class="dot" style="background:#d97706"></span>2. ABA attacks <span class="count">({{ res.aba|length }})</span></div>
    <div class="card-body">
      {% if res.aba %}<ul class="res">{% for x in res.aba %}<li>{{ x }}</li>{% endfor %}</ul>
      {% else %}<p class="empty">No ABA attacks.</p>{% endif %}
    </div>
  </div>

  <div class="card">
    <div class="card-header"><span class="dot" style="background:#2563eb"></span>3. ABA+ normal attacks <span class="count">({{ res.normal|length }})</span></div>
    <div class="card-body">
      {% if res.normal %}<ul class="res">{% for x in res.normal %}<li>{{ x }}</li>{% endfor %}</ul>
      {% else %}<p class="empty">No normal attacks.</p>{% endif %}
    </div>
  </div>

  <div class="card">
    <div class="card-header"><span class="dot" style="background:#dc2626"></span>4. ABA+ reverse attacks <span class="count">({{ res.reverse|length }})</span></div>
    <div class="card-body">
      {% if res.reverse %}<ul class="res">{% for x in res.reverse %}<li>{{ x }}</li>{% endfor %}</ul>
      {% else %}<p class="empty">No reverse attacks.</p>{% endif %}
    </div>
  </div>

  {% if graph_uri %}
  <div class="card">
    <div class="card-header"><span class="dot"></span>5. Attack graph</div>
    <div class="card-body graph"><img src="{{ graph_uri }}" alt="ABA and ABA+ attack graph"></div>
  </div>
  {% endif %}
  {% endif %}
</div>

<script>
  const EXAMPLE = {{ example_json | safe }};
  const ta = document.querySelector('textarea');
  document.getElementById('btn-example').onclick = () => { ta.value = EXAMPLE; ta.focus(); };
  document.getElementById('btn-clear').onclick = () => { ta.value = ''; ta.focus(); };
</script>
</body>
</html>
"""


def _arg_line(arg, ids):
    return f"[{ids[arg]}] {fmt_argument(arg)}"


def _attack_line(X, Y, ids):
    return f"{ids[X]} → {ids[Y]}    ({fmt_argument(X)}  attacks  {fmt_argument(Y)})"


def build_data(analysis):
    ids = analysis.arguments

    def order(a):
        return int(ids[a][1:])

    def att_order(e):
        return (order(e[0]), order(e[1]))

    return {
        "args": [_arg_line(a, ids) for a in sorted(ids, key=order)],
        "aba": [_attack_line(X, Y, ids) for X, Y in sorted(analysis.attacks, key=att_order)],
        "normal": [_attack_line(X, Y, ids) for X, Y in sorted(analysis.aba_plus["normal"], key=att_order)],
        "reverse": [_attack_line(X, Y, ids) for X, Y in sorted(analysis.aba_plus["reverse"], key=att_order)],
    }


@app.route("/", methods=["GET", "POST"])
def index():
    input_text = EXAMPLE
    auto_convert = False
    error, warnings, res, graph_uri = "", [], None, None

    if request.method == "POST":
        input_text = request.form.get("input", "")
        auto_convert = "auto_convert" in request.form
        try:
            fw = parse_aba_text(input_text)
            warnings = fw.warnings
            if not fw.assumptions:
                raise ValueError("No assumptions found ('A: [...]' line).")

            conv_fw, steps = convert(fw)
            if steps:
                msg = "Automatic conversion done: the framework was made " + " then ".join(steps) + "."
            else:
                msg = "The framework is already non-circular and atomic: no conversion needed."

            target = conv_fw if auto_convert else fw
            analysis = analyze(target)
            res = build_data(analysis)
            res.update(
                orig_circular=is_circular(fw), orig_atomic=is_atomic(fw),
                conversion_msg=msg,
                orig_desc="\n".join(describe_framework(fw)),
                conv_desc="\n".join(describe_framework(conv_fw)),
            )
            try:
                with _draw_lock:
                    graph_uri = render_attacks_graph(analysis, title="ABA vs ABA+ attacks")
            except Exception as e:
                # if the graph fails we still show the text results
                warnings = warnings + ["Graph could not be generated: " + str(e)]
        except Exception as e:
            error = str(e)

    return render_template_string(
        HTML, input_text=input_text, auto_convert=auto_convert, error=error,
        warnings=warnings, res=res, graph_uri=graph_uri,
        example_json=json.dumps(EXAMPLE),
    )


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=True)
