structure A = Ast
structure Tokens = Tokens

exception UnbalancedComments

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos = ref 0

local val commentLevel = ref 0 in

  (* Thank you to Kaustuv Chaudhuri, Frank Pfenning, Anand
   * Subramanian, and/or Taegyun Kim for these enterComment,
   * exitComment functions and their usages.
   *)
  fun enterComment yypos =
    (commentLevel := !commentLevel + 1)

  fun exitComment () =
    (commentLevel := !commentLevel - 1;
    !commentLevel = 0)

  fun eof () =
      (if (!commentLevel > 0)
       then raise UnbalancedComments
       else ();
       Tokens.EOF(!pos,!pos))
end

fun error (e,l : int,_) = TextIO.output (TextIO.stdOut, String.concat[
        "line ", (Int.toString l), ": ", e, "\n"
      ])

%%
%header (functor ThonLexFn(structure Tokens: Thon_TOKENS));
%s COMMENT;
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t];
%%
<INITIAL> \n       => (pos := (!pos) + 1; lex());
<INITIAL> {ws}+    => (lex());
<INITIAL> "Z"      => (Tokens.ZERO(!pos,!pos));
<INITIAL> "S"      => (Tokens.SUCC(!pos,!pos));
<INITIAL> "\\"     => (Tokens.LAM(!pos,!pos));
<INITIAL> "->"     => (Tokens.SARROW(!pos,!pos));
<INITIAL> "nat"    => (Tokens.NAT(!pos,!pos));
<INITIAL> "rec"    => (Tokens.REC(!pos,!pos));
<INITIAL> "go"     => (Tokens.GO(!pos,!pos));
<INITIAL> "poly"   => (Tokens.POLY(!pos,!pos));
<INITIAL> "left"   => (Tokens.LEFT(!pos,!pos));
<INITIAL> "right"  => (Tokens.RIGHT(!pos,!pos));
<INITIAL> "fst"    => (Tokens.FST(!pos,!pos));
<INITIAL> "snd"    => (Tokens.SND(!pos,!pos));
<INITIAL> "all"    => (Tokens.ALL(!pos,!pos));
<INITIAL> "some"   => (Tokens.SOME(!pos,!pos));
<INITIAL> "unit"   => (Tokens.UNIT(!pos,!pos));
<INITIAL> "fold"   => (Tokens.FOLD(!pos,!pos));
<INITIAL> "unfold" => (Tokens.UNFOLD(!pos,!pos));
<INITIAL> "with"   => (Tokens.WITH(!pos,!pos));
<INITIAL> "impl"   => (Tokens.IMPL(!pos,!pos));
<INITIAL> "use"    => (Tokens.USE(!pos,!pos));
<INITIAL> "case"   => (Tokens.CASE(!pos,!pos));
<INITIAL> "as"     => (Tokens.AS(!pos,!pos));
<INITIAL> "in"     => (Tokens.IN(!pos,!pos));
<INITIAL> "of"     => (Tokens.OF(!pos,!pos));
<INITIAL> "u"      => (Tokens.TYPEREC(!pos,!pos));
<INITIAL> "."      => (Tokens.DOT(!pos,!pos));
<INITIAL> ":"      => (Tokens.COLON(!pos,!pos));
<INITIAL> ","      => (Tokens.COMMA(!pos,!pos));
<INITIAL> "*"      => (Tokens.STAR(!pos,!pos));
<INITIAL> "("      => (Tokens.LPAREN(!pos,!pos));
<INITIAL> ")"      => (Tokens.RPAREN(!pos,!pos));
<INITIAL> "|"      => (Tokens.PIPE(!pos,!pos));
<INITIAL> {digit}+ => (Tokens.IDX (valOf (Int.fromString yytext), !pos, !pos));

<INITIAL> "(*"        => (YYBEGIN COMMENT; enterComment yypos; lex());
<INITIAL> "*)"        => (raise UnbalancedComments);

<COMMENT> "(*"        => (enterComment yypos; lex());
<COMMENT> "*)"        => (if exitComment () then YYBEGIN INITIAL else ();lex());
<COMMENT> \n          => (lex());
<COMMENT> .           => (lex());
