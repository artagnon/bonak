\LoadClass{article}
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{art}[2022/02/23 Artistic article class]
\RequirePackage{iftex}
\RequireLuaTeX
\RequirePackage[allbordercolors={.192157 .76862 .28627}]{hyperref} % Emerald Green
\RequirePackage{amsmath, amsthm, amssymb, mathrsfs, url, bookmark, fontspec, tikz-cd, mathpazo, fancyhdr, lastpage, titling, titlesec, enumitem, thmtools, soulutf8, color, luacode, colorpal, bibspacing, nestthms, ct, sset, lim, xargs, xkeyval}

% Use lettered footnotes
\renewcommand{\thefootnote}{\alph{footnote}}

% Title styling
\pretitle{
  \begin{center}
    \huge\scshape\strongenv\color{gray80}
}
\posttitle{
    \color{gray65}
  \end{center}
  \noindent\vrule height 2.5pt width \textwidth
  \vskip .75em plus .25em minus .25em
}

% Remove space after author
\renewcommand\maketitlehookd{
  \vspace{-2em}
}
