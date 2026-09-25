"""Textual parser for the DeGiorgi Lean sources.
Extracts declarations with fully-qualified names, privacy, signature text and body text."""
import re, os, json, sys

DECL_RE = re.compile(r'^(?P<mods>(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)'
                     r'(?P<kind>theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+(?P<name>[^\s:({\[]+)?')
TOPLEVEL_RE = re.compile(r'^(namespace|end|section|open|variable|noncomputable section|universe|set_option|attribute|@\[|#|mutual|/-|--|import|theorem|lemma|def|abbrev|structure|instance|class|inductive|private|protected|noncomputable|example|omit|include|local|scoped|notation|macro|syntax)\b')

def strip_comments(src):
    # remove block comments (nested) and line comments, preserving newlines
    out=[];i=0;depth=0;n=len(src)
    while i<n:
        if src.startswith('/-',i):
            depth+=1;i+=2;continue
        if depth and src.startswith('-/',i):
            depth-=1;i+=2;continue
        if depth:
            out.append('\n' if src[i]=='\n' else ' ');i+=1;continue
        if src.startswith('--',i):
            j=src.find('\n',i); j=n if j<0 else j
            out.append(' '*(j-i)); i=j; continue
        out.append(src[i]);i+=1
    return ''.join(out)

def parse_file(path, modname):
    raw=open(path,encoding='utf-8').read()
    src=strip_comments(raw)
    lines=src.split('\n')
    ns=[]  # stack of (kind, name)
    decls=[]; cur=None
    def cur_ns():
        parts=[]
        for k,nm in ns:
            if k=='namespace': parts+=nm.split('.')
        return parts
    for ln_no,line in enumerate(lines,1):
        is_top = bool(line) and (not line[0].isspace() or
                  (line.startswith('  ') and not line.startswith('   ') and ln_no>1 and not lines[ln_no-2].strip()
                   and re.match(r'\s*(private |protected )?(noncomputable )?(def|theorem|lemma) ', line)))
        if is_top:
            s=line.strip()
            m=DECL_RE.match(s)
            if m and m.group('kind') in ('theorem','lemma','def','abbrev','structure','instance','class','inductive'):
                if cur: decls.append(cur)
                name=m.group('name') or ''
                if m.group('kind')=='instance' and (not name or name.startswith('[') ):
                    name=''
                if name.startswith('_root_.'): full=name[len('_root_.'):]
                elif name: full='.'.join(cur_ns()+[name])
                else: full=None
                cur=dict(name=full, short=name, kind=m.group('kind'), private='private' in m.group('mods'),
                         file=path, module=modname, line=ln_no, text=[line], ns=cur_ns())
                continue
            if TOPLEVEL_RE.match(s):
                if cur: decls.append(cur); cur=None
                tok=s.split()
                if tok[0]=='namespace': ns.append(('namespace',tok[1]))
                elif tok[0]=='section' or s.startswith('noncomputable section'):
                    ns.append(('section', tok[-1] if tok[-1]!='section' else ''))
                elif tok[0]=='end':
                    if ns: ns.pop()
                continue
        if cur: cur['text'].append(line)
    if cur: decls.append(cur)
    for d in decls:
        t='\n'.join(d.pop('text'))
        # split signature / body at first top-level ':=' or ' where' or '|'
        m=re.search(r':=|\bwhere\b',t)
        if m: d['sig']=t[:m.start()]; d['body']=t[m.end():]
        else: d['sig']=t; d['body']=''
    return decls

def parse_repo(root):
    out=[]
    for dp,_,fs in os.walk(os.path.join(root,'DeGiorgi')):
        for f in sorted(fs):
            if f.endswith('.lean'):
                p=os.path.join(dp,f)
                mod=os.path.relpath(p,root)[:-5].replace('/','.')
                out+=parse_file(p,mod)
    return [d for d in out if d['name']]

if __name__=='__main__':
    ds=parse_repo(sys.argv[1])
    print(len(ds)); 
    from collections import Counter
    print(Counter(d['kind'] for d in ds), sum(d['private'] for d in ds))
    print(Counter(d['name'].split('.')[0] for d in ds).most_common(8))
    names=[d['name'] for d in ds]; print([n for n,c in Counter(names).items() if c>1][:20])
