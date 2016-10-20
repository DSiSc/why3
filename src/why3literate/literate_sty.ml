
open Format

let style_why3lang fname =
  let c = open_out fname in
  let fmt = formatter_of_out_channel c in
  fprintf fmt
"@\n\
\\RequirePackage{listings}@\n\
\\RequirePackage{amssymb}@\n\
\\RequirePackage{xcolor}@\n\
\\RequirePackage{bold-extra}@\n\
@\n\
\\lstdefinelanguage{why3}@\n\
{@\n\
basicstyle=\\ttfamily\\small,@\n\
morekeywords=[1]{predicate,constant,function,goal,type,use,@\n\
import,theory,end,module,in,@\n\
mutable,invariant,model,requires,ensures,raises,returns,reads,writes,diverges,@\n\
variant,let,val,while,for,loop,abstract,private,any,assume,check,assert,@\n\
begin,rec,clone,if,then,else,ghost,true,false,do,done,try,raise,absurd,@\n\
axiom,lemma,export,forall,exists,match,with,and,inductive,coinductive,fun,exception},@\n\
keywordstyle=[1]{\\color{blue}},@\n\
otherkeywords={},@\n\
commentstyle=\\itshape,@\n\
columns=[l]fullflexible,@\n\
sensitive=true,@\n\
morecomment=[s]{(*}{*)},@\n\
escapeinside={*?}{?*},@\n\
keepspaces=true,@\n\
literate=@\n\
{<}{$<$}{1}@\n\
{>}{$>$}{1}@\n\
{<=}{$\\le$}{1}@\n\
{>=}{$\\ge$}{1}@\n\
{<>}{$\\ne$}{1}@\n\
{/\\\\}{$\\land$}{1}@\n\
{\\\\/}{ $\\lor$ }{3}@\n\
{\ or(}{ $\\lor$(}{3}@\n\
{+->}{\\texttt{+->}}{2}@\n\
{-->}{\\texttt{-\\relax->}}{2}@\n\
{->}{$\\rightarrow$}{2}@\n\
{<-}{$\\leftarrow$}{2}@\n\
{<->}{$\\leftrightarrow$}{2}@\n\
}@\n\
\\lstnewenvironment{why3}{\\lstset{language=why3}}{}@\n\
\\newcommand{\\whyf}[1]{\\lstinline[language=why3]{#1}}@\n\
\\let\\of\\whyf@\n\
@.";
  close_out c

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3literate.opt"
End:
*)
