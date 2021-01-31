structure Lex : sig
datatype Token = FUN | FN | NAT | COLON | LPAREN | RPAREN | NAME of string | INDENT | DEDENT | RETURN | ZERO | SUCC | LET | SARROW | EQUAL | DARROW | IF | THEN | ELSE | DATA | BAR | CASE | COMMA | NEWLINE
val lexFile : string -> Token list
end  =
struct

datatype Token = FUN | FN | NAT | COLON | LPAREN | RPAREN | NAME of string | INDENT | DEDENT | RETURN | ZERO | SUCC | LET | SARROW | EQUAL | DARROW | IF | THEN | ELSE | DATA | BAR | CASE | COMMA | NEWLINE

exception UnexpectedIndentLevel
exception UnexpectedToken

fun lookaheadN s n =
    (* Can raise Size *)
    let val st = TextIO.getInstream s
        val (n, tail) = TextIO.StreamIO.inputN (st, n);
    in n
    end

(* Get last char of lookahead *)
fun lookaheadOnlyN s n =
    (* Can raise Size *)
    let val st = TextIO.getInstream s
        val (n, tail) = TextIO.StreamIO.inputN (st, n);
        val chars = explode n
    in (List.nth (chars, (List.length chars) - 1)) end

fun getName' s n =
    if not (Char.isAlphaNum (lookaheadOnlyN s n)) then
        lookaheadN s (n-1)
    else
        getName' s (n+1)

fun getName s = getName' s 1

fun getNumSpaces' s n =
    if not (#" " = (lookaheadOnlyN s n)) then
        n
    else
        getNumSpaces' s (n+1)

fun getNumSpaces s = getNumSpaces' s 0

fun eatWhitespace stream =
    case TextIO.lookahead stream of
        NONE => ()
      (* If I need to spit out NEWLINE tokens, feed `out` down here *)
      | SOME #"\n" => ((*TextIO.input1 stream*)(); ())
      | SOME c => if (Char.isSpace c)then
                  (TextIO.input1 stream; eatWhitespace stream)
                  else ()

fun onKeyword kw s =
    let val prefixOk = kw = (lookaheadN s (String.size kw))
        val afterChar = lookaheadOnlyN s ((String.size kw)+1)
        val suffixOk = not (Char.isAlphaNum afterChar)
    in
        prefixOk andalso suffixOk
    end

fun eatWord w s = (
    TextIO.inputN (s, (String.size w));
    eatWhitespace s
)

(* TODO lets 0 be a keyword, which is jank *)
fun eatKeywordOrName (w, tok) s indentLevel out =
    if onKeyword w s then (
        eatWord w s;
        lexLines' s (tok::out) indentLevel
    ) else (
        let val name = getName s in
            eatWord name s;
            lexLines' s ((NAME name)::out) indentLevel
        end
    )

and lexLines' s out indentLevel =
    (();
    case lookaheadN s 1 of
        "" => out
      | " " =>
        let val spaces =
                String.concat (List.tabulate (4*(!indentLevel), fn _ => " "))
            val dedentSpaces =
                String.concat (List.tabulate (4*((!indentLevel)-1), fn _ => " "))
        in
            (* TODO can dedent unboundedly - use getNumSpaces *)
            if lookaheadN s (4 * (!indentLevel)) = spaces then
                (eatWord spaces s;
                 lexLines' s out indentLevel)
            else if lookaheadN s (4 * ((!indentLevel)-1)) = dedentSpaces then
                (eatWord dedentSpaces s;
                 indentLevel := !indentLevel - 1;
                 lexLines' s (DEDENT::out) indentLevel)
            else
                raise UnexpectedIndentLevel
        end
      | "\n" => (
          TextIO.input1 s; (* can't eatWord here - keep leading spaces *)
          lexLines' s (NEWLINE::out) indentLevel
        )
      | "=" =>
        if onKeyword "=>" s then (
            eatWord "=>" s;
            lexLines' s (DARROW::out) indentLevel
        ) else if onKeyword "=" s then (
            eatWord "=" s;
            lexLines' s (EQUAL::out) indentLevel
        ) else (
            raise UnexpectedToken
        )
      | "i" => eatKeywordOrName ("if", IF) s indentLevel out
      | "t" => eatKeywordOrName ("then", THEN) s indentLevel out
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
        if onKeyword "fun" s then (
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
          if lookaheadN s 2 = ":\n" then
              (eatWord ":\n" s;
               (* could also incr after checking next line *)
               indentLevel := !indentLevel + 1;
               lexLines' s (INDENT::NEWLINE::out) indentLevel)
          else
              (eatWord ":" s;
               lexLines' s (COLON::out) indentLevel)
      )
      | other => let val name = getName s in
                     eatWord name s;
                     lexLines' s ((NAME name)::out) indentLevel
                 end
                     )

fun lexLines s indentLevel =
    let val backwards = lexLines' s [] indentLevel in List.rev backwards end

fun lex s =
    let
        val indentLevel = ref 0;
        val forewards = lexLines s indentLevel
    in
        forewards
    end

fun lexFile filename = lex (TextIO.openIn filename)


end
