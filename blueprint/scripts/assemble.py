#!/usr/bin/env python3
"""Write the leanblueprint scaffolding around the converted content. Usage: assemble.py <blueprint-dir>"""
import json, os, sys, shutil
BP = sys.argv[1]; SRC = os.path.join(BP, 'src')
m = json.load(open(os.path.join(SRC, '_macros.json')))
os.makedirs(os.path.join(SRC, 'macros'), exist_ok=True)
W = lambda p, s: open(os.path.join(SRC, p), 'w', encoding='utf-8').write(s)

W('macros/common.tex', r"""% Macros shared by the print and web versions.
% Theorem-like environments (these are the ones shown in the dependency graph).
\newtheorem{theorem}{Theorem}[chapter]
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\newtheorem{notation}[theorem]{Notation}

% Notation (taken from DeGiorgi_Lean_to_Tex.tex)
""" + '\n'.join(m['macros']) + '\n')

W('macros/print.tex', r"""% Print-only macros.
\newcommand{\lean}[1]{}
\newcommand{\discussion}[1]{}
\newcommand{\leanok}{}
\newcommand{\mathlibok}{}
\newcommand{\notready}{}
\ExplSyntaxOn
\NewDocumentCommand{\uses}{m}
 {\clist_map_inline:nn{#1}{\vphantom{\ref{##1}}}%
  \ignorespaces}
\NewDocumentCommand{\proves}{m}
 {\clist_map_inline:nn{#1}{\vphantom{\ref{##1}}}%
  \ignorespaces}
\ExplSyntaxOff

""" + m['fint'] + '\n\n% Lean names in running text, breakable at underscores\n' + m['leanname'] + '\n')

W('macros/web.tex', r"""% Web-only versions of macros that plasTeX / MathJax cannot handle.
\newcommand{\fint}{\mathop{⨍}\nolimits}
\newcommand{\leanname}[1]{\texttt{#1}}
""")

W('print.tex', r"""% Printable version of the blueprint (compile with latexmk, see latexmkrc).
% Uses pdflatex, like the original companion document.
\documentclass[a4paper]{report}
\usepackage{geometry}
\usepackage{expl3}
\usepackage{amssymb, amsthm, mathtools}
\usepackage{enumitem}
\usepackage{nicefrac}
\usepackage{seqsplit}
\usepackage[unicode,colorlinks=true,linkcolor=blue,urlcolor=magenta,citecolor=blue]{hyperref}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\IfFileExists{lmodern.sty}{\usepackage{lmodern}}{}
\usepackage[expansion=false]{microtype}
\setlength{\emergencystretch}{3em}

\input{macros/common}
\input{macros/print}

\title{De Giorgi--Nash--Moser theory in Lean: blueprint}
\author{Scott Armstrong and Julia Kempe\\\small(blueprint generated from the Lean-to-\TeX{} companion)}

\begin{document}
\maketitle
\tableofcontents
\input{content}
\end{document}
""")

W('web.tex', r"""% Web version of the blueprint.
\documentclass{report}
\usepackage{amssymb, amsthm, amsmath}
\usepackage{hyperref}
\usepackage[dep_graph]{blueprint}

\input{macros/common}
\input{macros/web}

\home{https://scottnarmstrong.github.io/DeGiorgi}
\github{https://github.com/scottnarmstrong/DeGiorgi}
\dochome{https://scottnarmstrong.github.io/DeGiorgi/docs}

\title{De Giorgi--Nash--Moser theory in Lean: blueprint}
\author{Scott Armstrong and Julia Kempe}

\begin{document}
\maketitle
\input{content}
\end{document}
""")

W('plastex.cfg', """[general]
renderer=HTML5
copy-theme-extras=yes
plugins=plastexdepgraph leanblueprint

[document]
toc-depth=3
toc-non-files=True

[files]
directory=../web/
split-level=0

[html5]
localtoc-level=0
extra-css=extra_styles.css
mathjax-dollars=False
""")
W('latexmkrc', "$pdf_mode = 1;\n$pdflatex = 'pdflatex -synctex=1';\n@default_files = ('print.tex');\n")
W('extra_styles.css', "/* Extra CSS for the web blueprint */\n")
for f in ('_macros.json',):
    os.remove(os.path.join(SRC, f))
