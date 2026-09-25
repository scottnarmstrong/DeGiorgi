#!/usr/bin/env python3
"""Convert DeGiorgi_Lean_to_Tex.tex into a leanblueprint source tree.

Usage: python3 convert.py <repo-root> <out-blueprint-src-dir>

Steps:
 1. parse Lean sources textually (leanparse.py) to get fully-qualified names,
    privacy flags, signature/body text;
 2. parse theorem-like environments of the companion .tex (texparse.py) and
    resolve the Lean names in their headers;
 3. compute \\uses{} edges from Lean references (through untagged helpers)
    plus existing \\ref{}s in proofs, keeping the graph acyclic;
 4. write chapter files with \\label, \\lean, \\leanok, \\uses inserted.
"""
import re, os, sys, json, unicodedata
from collections import defaultdict, OrderedDict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leanparse, texparse

ROOT, OUT = sys.argv[1], sys.argv[2]
tex = open(os.path.join(ROOT, 'DeGiorgi_Lean_to_Tex.tex'), encoding='utf-8').read()
decls = leanparse.parse_repo(ROOT)

# ---------------------------------------------------------------- name tables
GREEK = {'Λ':'Lambda','λ':'lambda','Ω':'Omega','ω':'omega','α':'alpha','β':'beta','γ':'gamma','δ':'delta',
         'ε':'eps','θ':'theta','μ':'mu','ν':'nu','ρ':'rho','σ':'sigma','τ':'tau','φ':'phi','χ':'chi','ψ':'psi',
         'κ':'kappa','η':'eta','ξ':'xi','ζ':'zeta','π':'pi','Γ':'Gamma','Δ':'Delta','Φ':'Phi','Ψ':'Psi'}
SUB = {chr(0x2080+i):'_%d'%i for i in range(10)}
def norm(n):
    out=''.join(GREEK.get(c, SUB.get(c, c)) for c in n)
    return out.replace("'", "_prime").lower()

by_full = defaultdict(list)          # full name -> decls (private dupes possible)
for d in decls: by_full[d['name']].append(d)
by_norm = defaultdict(set)
for f in by_full: by_norm[norm(f)].add(f)
by_last = defaultdict(set)
for f in by_full: by_last[f.split('.')[-1]].add(f)

def resolve_header(n, prev):
    cands = []
    tries = [n, 'DeGiorgi.'+n]
    if prev:
        pns = prev.rsplit('.',1)[0] if '.' in prev else ''
        if n.startswith('_'):                       # "\leanname{\_add}" shorthand
            stem = prev.rsplit('_',1)[0]
            tries = [stem+n] + tries
        elif pns and pns!='DeGiorgi':
            tries = [pns+'.'+n] + tries
    for t in tries:
        if t in by_full: return t
        if norm(t) in by_norm and len(by_norm[norm(t)])==1: return next(iter(by_norm[norm(t)]))
    suf = [f for f in by_full if f.endswith('.'+n) or norm(f).endswith('.'+norm(n))]
    if len(suf)==1: return suf[0]
    return None

# ---------------------------------------------------------------- tex nodes
envs = texparse.find_envs(tex)
used_labels = set(re.findall(r'\\label\{([^}]*)\}', tex))
PREFIX = {'theorem':'thm','lemma':'lem','corollary':'cor','proposition':'prop','definition':'def'}
def slug(s): return re.sub(r'[^A-Za-z0-9]+','_',s).strip('_')[:60]

unresolved = []
decl2node = {}
for k,e in enumerate(envs):
    full=[]; prev=None
    if not e['names']:            # names given in the statement body instead of the header
        e['names'] = texparse.leannames(e['body'])
    for n,priv in e['names']:
        r = resolve_header(n, prev)
        if r: full.append(r); prev=r
        else: unresolved.append((e['label'], n))
    e['full'] = list(OrderedDict.fromkeys(full))
    if not e['label']:
        base = PREFIX[e['env']]+':'+(slug(e['full'][0].split('.',1)[-1]) if e['full'] else 'node%d'%k)
        lab=base; i=2
        while lab in used_labels: lab='%s_%d'%(base,i); i+=1
        e['label']=lab; e['new_label']=True
        used_labels.add(lab)
    else: e['new_label']=False
    for f in e['full']: decl2node.setdefault(f, e['label'])

lab2env = {e['label']:e for e in envs}
order = {e['label']:i for i,e in enumerate(envs)}

# ---------------------------------------------------------------- Lean references
IDENT = re.compile(r"[A-Za-z_\u0370-\u03ff\u1f00-\u1fff\u2080-\u209f\u2100-\u214f][A-Za-z0-9_'!?.\u0370-\u03ff\u1f00-\u1fff\u2080-\u209f\u2100-\u214f]*|\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*")
def visible(target, d):
    t = by_full[target]
    return any((not x['private']) or x['module']==d['module'] for x in t)

def refs(d, text):
    out=set()
    nsl = d['ns']
    prefixes = ['.'.join(nsl[:i]) for i in range(len(nsl),-1,-1)] + ['DeGiorgi']
    for tok in IDENT.findall(text):
        tok = tok.rstrip('.')
        cands=[]
        if tok.startswith('.'):
            last = tok[1:]
            if len(by_last.get(last,()))==1 and (len(last)>=6 or '_' in last): cands=list(by_last[last])
        else:
            for p in prefixes:
                t = (p+'.'+tok) if p else tok
                if t in by_full: cands=[t]; break
            if not cands and '.' in tok:                       # h.foo generalized field notation
                last = tok.split('.')[-1]
                if len(by_last.get(last,()))==1 and (len(last)>=6 or '_' in last): cands=list(by_last[last])
        for c in cands:
            if c!=d['name'] and visible(c,d): out.add(c)
    return out

sig_refs, body_refs = {}, {}
for d in decls:
    key=(d['name'],d['module'])
    sig_refs[key] = refs(d, d['sig']); body_refs[key] = refs(d, d['body'])
def keys_of(name): return [(name,x['module']) for x in by_full[name]]

# frontier of tagged nodes reachable through untagged declarations
memo={}
def frontier(name, stack):
    if name in memo: return memo[name]
    if name in stack: return set()
    stack.add(name); acc=set()
    for k in keys_of(name):
        for r in sig_refs[k] | body_refs[k]:
            if r in decl2node: acc.add(decl2node[r])
            else: acc |= frontier(r, stack)
    stack.discard(name); memo[name]=acc
    return acc

def direct_nodes(rs, stack=None):
    acc=set()
    for r in rs:
        if r in decl2node: acc.add(decl2node[r])
        else: acc |= frontier(r, set())
    return acc

for e in envs:
    st, pf = set(), set()
    for f in e['full']:
        for k in keys_of(f):
            if e['env']=='definition':
                st |= direct_nodes(sig_refs[k] | body_refs[k])
            else:
                st |= direct_nodes(sig_refs[k]); pf |= direct_nodes(body_refs[k])
    # author cross-references inside the proof
    if e['proof']:
        ptxt = tex[e['proof'][0]:e['proof'][1]]
        pf |= {l for l in re.findall(r'\\ref\{([^}]*)\}', ptxt) if l in lab2env}
    st.discard(e['label']); pf.discard(e['label'])
    pf -= st
    e['st_uses']=st; e['pf_uses']=pf
    e['lean_only_edges']=set()

# ---------------------------------------------------------------- break cycles
def edges():
    for e in envs:
        for u in e['st_uses']|e['pf_uses']: yield e['label'],u
removed=[]
while True:
    G=defaultdict(set)
    for a,b in edges(): G[a].add(b)
    color={}; cyc=None
    def dfs(v,path):
        global cyc
        color[v]=1; path.append(v)
        for w in G[v]:
            if cyc: return
            if color.get(w)==1: cyc=path[path.index(w):]+[w]; return
            if not color.get(w): dfs(w,path)
        path.pop(); color[v]=2
    sys.setrecursionlimit(10000)
    for v in list(G):
        if not color.get(v): dfs(v,[])
        if cyc: break
    if not cyc: break
    # drop the edge in the cycle pointing "forward" in the document the most
    pairs=list(zip(cyc,cyc[1:]))
    a,b=max(pairs,key=lambda p: order[p[1]]-order[p[0]])
    for key in ('pf_uses','st_uses'): lab2env[a][key].discard(b)
    removed.append((a,b))

# ---------------------------------------------------------------- rewrite tex
def clean_title(opt):
    if opt is None: return None
    k = opt.find('\\leanname')
    if k<0: return opt
    head = opt[:k].rstrip()
    head = re.sub(r'[;,:(]\s*$','',head).rstrip()
    head = re.sub(r'\s*\($','',head).rstrip()
    return head or None

inserts=[]   # (pos, replace_until, text)
stats=defaultdict(int)
for e in envs:
    pub = [f for f in e['full'] if not all(x['private'] for x in by_full[f])]
    priv = [f for f in e['full'] if f not in pub]
    title = clean_title(e['opt'])
    hdr = '\\begin{%s}%s\n' % (e['env'], ('['+title+']') if title else '')
    hdr += '\\label{%s}\n' % e['label']
    if pub: hdr += '\\lean{%s}\n' % ', '.join(pub); stats['lean']+=1
    if e['full']: hdr += '\\leanok\n'; stats['leanok']+=1
    if e['st_uses']: hdr += '\\uses{%s}\n' % ', '.join(sorted(e['st_uses'], key=order.get))
    if priv:
        hdr += '\\noindent\\textit{(Formalized as private declaration%s %s.)}\\par\n' % (
            's' if len(priv)>1 else '', ', '.join('\\leanname{%s}'%texparse_escape for texparse_escape in
                                                   [p.replace('_','\\_') for p in priv]))
        stats['private_nodes']+=1
    if not e['full']: stats['no_lean']+=1
    inserts.append((e['start'], e['hdr_end'], hdr))
    if e['proof']:
        p = '\n' + ('\\leanok\n' if e['full'] else '')
        if e['pf_uses']: p += '\\uses{%s}\n' % ', '.join(sorted(e['pf_uses'], key=order.get))
        inserts.append((e['proof'][0], e['proof'][0], p))
    elif e['env']!='definition':
        # no proof block in the companion: add a stub so the graph shows the proof as formalized
        endtag='\\end{%s}' % e['env']
        p = '\n\n\\begin{proof}\n\\leanok\n'
        if e['pf_uses']: p += '\\uses{%s}\n' % ', '.join(sorted(e['pf_uses'], key=order.get))
        p += 'See the Lean formalization.\n\\end{proof}'
        inserts.append((e['end']+len(endtag), e['end']+len(endtag), p))
        stats['proof_stubs'] += 1
new = tex
for pos,until,txt in sorted(inserts, key=lambda x:-x[0]):
    new = new[:pos] + txt + new[until:].lstrip('\n') if until>pos else new[:pos]+txt+new[until:]

# display math: use equation* consistently instead of \\[ \\]
new = re.sub(r'(?<!\\)\\\[(.*?)(?<!\\)\\\]', lambda m: '\\begin{equation*}'+m.group(1)+'\\end{equation*}', new, flags=re.S)

# ---------------------------------------------------------------- split output
pre, rest = new.split('\\begin{document}',1)
body = rest.rsplit('\\end{document}',1)[0]
body = re.sub(r'\\maketitle|\\tableofcontents','',body)
body = body.replace('\\subsubsection','\\SUBSUB').replace('\\subsection','\\SUB').replace('\\section','\\chapter')
body = body.replace('\\SUBSUB','\\subsection').replace('\\SUB','\\section')
parts = re.split(r'(?=\\chapter\{)', body)
os.makedirs(os.path.join(OUT,'chapters'), exist_ok=True)
content = ['% Generated by convert.py from DeGiorgi_Lean_to_Tex.tex\n']
for i,p in enumerate(parts):
    if not p.strip() or not p.lstrip().startswith('\\chapter'):
        if p.strip().strip('%= \n'): content.append(p)
        continue
    m = re.search(r'\\label\{sec:([^}]*)\}', p)
    name = '%02d_%s' % (i, m.group(1) if m else 'ch%d'%i)
    open(os.path.join(OUT,'chapters',name+'.tex'),'w',encoding='utf-8').write(p.rstrip()+'\n')
    content.append('\\input{chapters/%s}\n' % name)
open(os.path.join(OUT,'content.tex'),'w',encoding='utf-8').write(''.join(content))

# preamble macros (everything except documentclass/usepackage/theorem/title bits)
macro_lines=[]
skip = re.compile(r'\\(documentclass|usepackage|title|author|date|newtheorem|theoremstyle|setlength|emergencystretch)')
buf=pre.split('\n'); i=0
leanname_def=[]
while i<len(buf):
    l=buf[i]
    if l.startswith('\\newcommand{\\leanname}'):
        while True:
            leanname_def.append(buf[i]);
            if buf[i].strip().endswith('\\endgroup}'): break
            i+=1
        i+=1; continue
    if l.startswith('\\newcommand{\\fint}'):
        j=i
        while not buf[j].rstrip().endswith('\\nolimits}'): j+=1
        fint='\n'.join(buf[i:j+1]); i=j+1; continue
    if not skip.match(l.strip()) and l.strip() and not l.lstrip().startswith('%'):
        macro_lines.append(l)
    i+=1
json.dump(dict(macros=macro_lines, fint=fint, leanname='\n'.join(leanname_def)),
          open(os.path.join(OUT,'_macros.json'),'w'))

report = dict(nodes=len(envs), with_lean_decl=sum(1 for e in envs if e['full']),
              lean_tagged=stats['lean'], private_only_or_partly=stats['private_nodes'],
              without_lean_decl=[(e['env'], e['label'], (e['opt'] or '')[:70]) for e in envs if not e['full']],
              labels_added=sum(e['new_label'] for e in envs), proof_stubs_added=stats['proof_stubs'],
              unresolved_header_names=unresolved,
              edges=sum(len(e['st_uses'])+len(e['pf_uses']) for e in envs),
              cycle_edges_removed=removed)
json.dump(report, open(os.path.join(OUT,'_report.json'),'w'), indent=1, ensure_ascii=False)
print(json.dumps({k:(v if not isinstance(v,list) else len(v)) for k,v in report.items()}, indent=1))
