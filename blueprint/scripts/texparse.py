import re
ENVS=('theorem','lemma','corollary','proposition','definition')
BEGIN_RE=re.compile(r'\\begin\{('+'|'.join(ENVS)+r')\}')

def read_balanced(s,i,open_c,close_c):
    """s[i]==open_c; return index after matching close."""
    depth=0;j=i
    while j<len(s):
        c=s[j]
        if c=='\\': j+=2; continue
        if c==open_c: depth+=1
        elif c==close_c:
            depth-=1
            if depth==0: return j+1
        j+=1
    raise ValueError('unbalanced at %d'%i)

def leannames(s):
    out=[];i=0
    while True:
        k=s.find('\\leanname{',i)
        if k<0: return out
        e=read_balanced(s,k+9,'{','}')
        nm=s[k+10:e-1].replace('\\_','_').replace('\\allowbreak','').replace(' ','').strip()
        tail=s[e:e+15]
        out.append((nm,'(private)' in tail))
        i=e

def find_envs(tex):
    envs=[]
    for m in BEGIN_RE.finditer(tex):
        env=m.group(1); i=m.end()
        opt=None; opt_span=None
        j=i
        while j<len(tex) and tex[j] in ' \t': j+=1
        if j<len(tex) and tex[j]=='[':
            e=read_balanced(tex,j,'[',']')
            opt=tex[j+1:e-1]; opt_span=(j,e); i=e
        # label directly after?
        lm=re.match(r'\s*\\label\{([^}]*)\}',tex[i:])
        label=lm.group(1) if lm else None
        hdr_end=i+(lm.end() if lm else 0)
        end=tex.find('\\end{%s}'%env,i)
        body=tex[hdr_end:end]
        # proof immediately after?
        pm=re.match(r'\s*\\begin\{proof\}',tex[end+len('\\end{%s}'%env):])
        proof=None
        if pm:
            ps=end+len('\\end{%s}'%env)+pm.end()
            pe=tex.find('\\end{proof}',ps)
            proof=(ps,pe)
        envs.append(dict(env=env,start=m.start(),begin_end=m.end(),opt=opt,opt_span=opt_span,label=label,
                         hdr_end=hdr_end,end=end,body=body,proof=proof,
                         names=leannames(opt or '')))
    return envs
