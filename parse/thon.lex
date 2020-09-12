structure A = Ast
structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos = ref 0
fun eof () = Tokens.EOF(!pos,!pos)
fun error (e,l : int,_) = TextIO.output (TextIO.stdOut, String.concat[
        "line ", (Int.toString l), ": ", e, "\n"
      ])

%%
%header (functor ThonLexFn(structure Tokens: Thon_TOKENS));
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t];
%%
\n       => (pos := (!pos) + 1; lex());
{ws}+    => (lex());
"Z"      => (Tokens.ZERO(!pos,!pos));
"S"      => (Tokens.SUCC(!pos,!pos));
"\\"     => (Tokens.LAM(!pos,!pos));
"->"     => (Tokens.SARROW(!pos,!pos));
"nat"    => (Tokens.NAT(!pos,!pos));
"rec"    => (Tokens.REC(!pos,!pos));
"go"     => (Tokens.GO(!pos,!pos));
"poly"   => (Tokens.POLY(!pos,!pos));
"left"   => (Tokens.LEFT(!pos,!pos));
"right"  => (Tokens.RIGHT(!pos,!pos));
"all"    => (Tokens.ALL(!pos,!pos));
"some"   => (Tokens.SOME(!pos,!pos));
":"      => (Tokens.COLON(!pos,!pos));
","      => (Tokens.COMMA(!pos,!pos));
"*"      => (Tokens.STAR(!pos,!pos));
"("      => (Tokens.LPAREN(!pos,!pos));
")"      => (Tokens.RPAREN(!pos,!pos));
"|"      => (Tokens.PIPE(!pos,!pos));
{digit}+ => (Tokens.IDX (valOf (Int.fromString yytext), !pos, !pos));
