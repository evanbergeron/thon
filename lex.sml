structure Lex : sig
datatype Token = FUN | FN | NAT | COLON | LPAREN | RPAREN | NAME of string | INDENT | DEDENT | RETURN | ZERO | SUCC | LET | SARROW | EQ | DARROW | IF | THEN | ELSE | DATA | BAR | CASE | COMMA | NEWLINE | UNIT | STAR | IFZ | TRUE | FALSE | BOOL
val lex : string -> Token list
val lexFile : string -> Token list
val lexFileNoPrintErrMsg : string -> Token list
val tokenToString : Token -> string
end  =
struct

datatype Token = FUN | FN | NAT | COLON | LPAREN | RPAREN | NAME of string | INDENT | DEDENT | RETURN | ZERO | SUCC | LET | SARROW | EQ | DARROW | IF | THEN | ELSE | DATA | BAR | CASE | COMMA | NEWLINE | UNIT | STAR | IFZ | TRUE | FALSE | BOOL

exception No
exception UnexpectedIndentLevel
exception UnexpectedToken of string
exception UnimplementTokenToString

fun println s = print (s  ^ "\n")

fun debugPrint s =
    if false then println s
    else ()

fun tokenToString FUN = "FUN"
  | tokenToString FN = "FN"
  | tokenToString NAT = "NAT"
  | tokenToString COLON = "COLON"
  | tokenToString LPAREN = "LPAREN"
  | tokenToString RPAREN = "RPAREN"
  | tokenToString (NAME name) = "NAME " ^ name
  | tokenToString INDENT = "INDENT"
  | tokenToString DEDENT = "DEDENT"
  | tokenToString RETURN = "RETURN"
  | tokenToString ZERO = "ZERO"
  | tokenToString SUCC = "SUCC"
  | tokenToString LET = "LET"
  | tokenToString SARROW = "SARROW"
  | tokenToString EQ = "EQ"
  | tokenToString DARROW = "DARROW"
  | tokenToString IF = "IF"
  | tokenToString IFZ = "IFZ"
  | tokenToString THEN = "THEN"
  | tokenToString ELSE = "ELSE"
  | tokenToString DATA = "DATA"
  | tokenToString BAR = "BAR"
  | tokenToString CASE = "CASE"
  | tokenToString COMMA = "COMMA"
  | tokenToString NEWLINE = "NEWLINE"
  | tokenToString UNIT = "UNIT"
  | tokenToString STAR = "STAR"
  | tokenToString TRUE = "TRUE"
  | tokenToString FALSE = "FALSE"
  | tokenToString BOOL = "BOOL"

fun lookaheadN s n =
    (* Can raise Size *)
    let val st = TextIO.getInstream s
        val (n, tail) = TextIO.StreamIO.inputN (st, n);
    in n
    end

(* Get last char of lookahead *)
fun lookaheadOnlyN s n =
    let val st = TextIO.getInstream s
        val (k, tail) = TextIO.StreamIO.inputN (st, n);
        val () = debugPrint k
        val () = debugPrint (Int.toString n)
        val chars = explode k
        val res = (List.nth (chars, (List.length chars) - 1))
    in if n > (List.length chars) then NONE else SOME
        (debugPrint (Int.toString n); debugPrint (Char.toString res); res) end

fun getName' s n =
    (debugPrint ("getName " ^ (Int.toString n));
     case lookaheadOnlyN s n of
         NONE => lookaheadN s (n-1)
       | SOME c =>
         (if not (Char.isAlphaNum (c)) then
              lookaheadN s (n-1)
          else
              getName' s (n+1)))

fun getName s = getName' s 1

fun eatAndGetNumSpaces' s n =
    (debugPrint ("eatAndGetNumSpaces' " ^ (Int.toString n));
     case TextIO.lookahead s of
         SOME #" " => (
          TextIO.input1 s;
          eatAndGetNumSpaces' s (n+1)
         )
       | _ => n
    )

fun eatAndGetNumSpaces s = eatAndGetNumSpaces' s 0

fun eatWhitespace stream =
    case TextIO.lookahead stream of
        NONE => ()
      (* If I need to spit out NEWLINE tokens, feed `out` down here *)
      | SOME #"\n" => ((*TextIO.input1 stream*)(); ())
      | SOME c => if (Char.isSpace c)then
                  (TextIO.input1 stream; eatWhitespace stream)
                  else ()

fun onKeyword kw s =
    (debugPrint ("onKeyword " ^ kw);
    let val prefixOk = kw = (lookaheadN s (String.size kw))
        val afterChar = lookaheadOnlyN s ((String.size kw)+1)
        val suffixOk = (case afterChar of
                            NONE => true
                          | SOME c => not (Char.isAlphaNum (c)))
    in
        prefixOk andalso suffixOk
    end)

fun eatWord w s = (
    TextIO.inputN (s, (String.size w));
    eatWhitespace s
)

(* TODO lets 0 be a keyword, which is jank *)
fun eatKeywordOrName (w, tok) s indentLevel out =
    (debugPrint ("eatKeywordOrName " ^ w);
    if onKeyword w s then (
        debugPrint "confirmed on keyword";
        eatWord w s;
        lexLines' s (tok::out) indentLevel
    ) else (
        debugPrint "not on keyword";
        let val name = getName s in
            eatWord name s;
            lexLines' s ((NAME name)::out) indentLevel
        end
    ))

and getIndentDedentTokens s out indentLevel =
    let
        (* TODO assert last elt of out is NEWLINE here *)
        val () = debugPrint ("Indent level: " ^ (Int.toString (!indentLevel)))
        val numSpaces = eatAndGetNumSpaces s
        (* UNDONE 2 space indent *)
        val thisLineIndentLevel = numSpaces div 4;
        val () = debugPrint ("thisLineIndentLevel " ^ (Int.toString (thisLineIndentLevel)))
        val tok = if thisLineIndentLevel > (!indentLevel) then INDENT else DEDENT
        val numToks = abs (thisLineIndentLevel - (!indentLevel))
        val toks = List.tabulate (numToks, fn _ => tok);
    in
        toks
    end

and lexLines' s out indentLevel =
    (debugPrint "=======================";
     List.map (fn tok => debugPrint (tokenToString tok)) out;
    case lookaheadN s 1 of
        "" => out
      | " " => raise No
      | "\n" => (
     (case lookaheadOnlyN s 2 of
         SOME #"\n" => (TextIO.input1 s;
                        lexLines' s (NEWLINE::out) indentLevel)
        | _ =>
          (TextIO.input1 s; (* can't eatWord here - keep leading spaces *)
        let val toks = getIndentDedentTokens s out indentLevel
        in
            if List.length toks = 0 then
                (* No indent or dedent here *)
                lexLines' s (NEWLINE::out) indentLevel
            else
                (indentLevel := !indentLevel +
                                ((List.length toks) *
                                 (if DEDENT = List.nth (toks, 0) then ~1 else 1))
                ; lexLines' s (toks @ (NEWLINE::out)) indentLevel)
        end)
        ))
      | "=" =>
        if onKeyword "=>" s then (
            eatWord "=>" s;
            lexLines' s (DARROW::out) indentLevel
        ) else if onKeyword "=" s then (
            eatWord "=" s;
            lexLines' s (EQ::out) indentLevel
        ) else (
            raise UnexpectedToken("saw `=`, expected `=>` or `=`")
        )
      | "*" => (
            eatWord "*" s;
            lexLines' s (STAR::out) indentLevel
          )
      | "u" => eatKeywordOrName ("unit", UNIT) s indentLevel out
      | "i" =>
        if onKeyword "ifz" s then (
            eatWord "ifz" s;
            lexLines' s (IFZ::out) indentLevel
        ) else if onKeyword "if" s then (
            eatWord "if" s;
            lexLines' s (IF::out) indentLevel
        ) else (
            let val name = getName s in
                eatWord name s;
                lexLines' s ((NAME name)::out) indentLevel
            end
        )
      | "t" =>
        if onKeyword "true" s then (
            eatWord "true" s;
            lexLines' s (TRUE::out) indentLevel
        ) else if onKeyword "then" s then (
            eatWord "then" s;
            lexLines' s (THEN::out) indentLevel
        ) else (
            let val name = getName s in
                eatWord name s;
                lexLines' s ((NAME name)::out) indentLevel
            end
        )
      | "e" => eatKeywordOrName ("else", ELSE) s indentLevel out
      | "d" => eatKeywordOrName ("data", DATA) s indentLevel out
      | "c" => eatKeywordOrName ("case", CASE) s indentLevel out
      (* TODO can just directly eat single chars *)
      | "," => eatKeywordOrName (",", COMMA) s indentLevel out
      | "|" => eatKeywordOrName ("|", BAR) s indentLevel out
      | "-" => eatKeywordOrName ("->", SARROW) s indentLevel out
      | "z" => eatKeywordOrName ("z", ZERO) s indentLevel out
      | "s" => eatKeywordOrName ("s", SUCC) s indentLevel out
      | "l" => eatKeywordOrName ("let", LET) s indentLevel out
      | "f" =>
        if onKeyword "false" s then (
            eatWord "false" s;
            lexLines' s (FALSE::out) indentLevel
        ) else if onKeyword "fun" s then (
            eatWord "fun" s;
            lexLines' s (FUN::out) indentLevel
        ) else if onKeyword "fn" s then (
            eatWord "fn" s;
            lexLines' s (FN::out) indentLevel
        ) else (
            let val name = getName s in
                eatWord name s;
                lexLines' s ((NAME name)::out) indentLevel
            end
        )
      | "n" => eatKeywordOrName ("nat", NAT) s indentLevel out
      | "b" => eatKeywordOrName ("bool", BOOL) s indentLevel out
      | "r" => eatKeywordOrName ("return", RETURN) s indentLevel out
      | "(" => (
          eatWord "(" s;
          lexLines' s (LPAREN::out) indentLevel
      )
      | ")" => (
          eatWord ")" s;
          lexLines' s (RPAREN::out) indentLevel
      )
      | ":" => (
          eatWord ":" s;
          lexLines' s (COLON::out) indentLevel
      )
      | other =>
        if not (Char.isAlpha (String.sub (other, 0))) then
            raise UnexpectedToken("See identifier starting with " ^ other ^ ". Indentifiers must start with alphabetic characters.")
        else
            let val name = getName s in
            eatWord name s;
            lexLines' s ((NAME name)::out) indentLevel
            end
      )

fun lexLines s indentLevel =
    let val backwards = lexLines' s [] indentLevel in List.rev backwards end

fun lex' s printErrMsg =
    let
        val indentLevel = ref 0;
        val forewards = lexLines s indentLevel
    in
        forewards
    end
    handle UnexpectedToken msg => (if printErrMsg then print ("Lexing error: " ^ msg ^ "\n") else ();
                                   raise (UnexpectedToken msg) )

fun lex s = lex' (TextIO.openString s) true

fun lexFile filename = lex' (TextIO.openIn filename) true

fun lexFileNoPrintErrMsg filename = lex' (TextIO.openIn filename) false


end
