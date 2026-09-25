#!/usr/bin/env python3
"""Generate a lightweight replacement for the doc-gen4 "find" page.

leanblueprint links every \\lean{Name} to  <dochome>/find/#doc/Name .
Instead of full API docs (too slow to build on GitHub's free runners because
all of Mathlib gets documented), this writes docs/find/index.html, which
redirects to the declaration's source line on GitHub.

Usage (from the repository root):
    python3 blueprint/scripts/make_source_links.py OWNER/REPO [BRANCH]
e.g.
    python3 blueprint/scripts/make_source_links.py ouboub/DeGiorgi-ub main
Re-run it after changing the Lean code so that the line numbers stay right.
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leanparse

repo = sys.argv[1]
branch = sys.argv[2] if len(sys.argv) > 2 else 'main'
root = os.getcwd()
decls = leanparse.parse_repo(root)

table = {}
for d in decls:
    if d['private'] or d['name'] in table:
        continue
    table[d['name']] = '%s#L%d' % (os.path.relpath(d['file'], root), d['line'])

os.makedirs('docs/find', exist_ok=True)
page = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Lean declaration lookup</title>
<style>body{font-family:system-ui,sans-serif;max-width:40rem;margin:3rem auto;padding:0 1rem;line-height:1.5}
code{background:#eee;padding:.1em .3em;border-radius:3px}</style>
</head><body>
<p id="msg">Looking up the Lean declaration&hellip;</p>
<script>
const REPO = %s, BRANCH = %s;
const TABLE = %s;
function go() {
  const h = decodeURIComponent(location.hash || '');
  const name = h.startsWith('#doc/') ? h.slice(5) : h.replace(/^#/, '');
  const msg = document.getElementById('msg');
  if (!name) { msg.textContent = 'No declaration name given.'; return; }
  const loc = TABLE[name];
  if (loc) {
    location.replace('https://github.com/' + REPO + '/blob/' + BRANCH + '/' + loc);
  } else {
    const q = encodeURIComponent('repo:' + REPO + ' ' + name.split('.').pop());
    msg.innerHTML = 'Declaration <code></code> not found in the index; ' +
      '<a href="https://github.com/search?type=code&q=' + q + '">search the code on GitHub</a>.';
    msg.querySelector('code').textContent = name;
  }
}
window.addEventListener('hashchange', go);
go();
</script>
</body></html>
""" % (json.dumps(repo), json.dumps(branch), json.dumps(table, ensure_ascii=False, separators=(',', ':')))
open('docs/find/index.html', 'w', encoding='utf-8').write(page)

owner, name = repo.split('/')
index = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta http-equiv="refresh" content="0; url=blueprint/">
<title>%s</title></head>
<body><p><a href="blueprint/">Blueprint (web)</a> &middot; <a href="blueprint.pdf">Blueprint (PDF)</a></p></body></html>
""" % name
open('docs/index.html', 'w', encoding='utf-8').write(index)
print('wrote docs/find/index.html (%d declarations) and docs/index.html' % len(table))
