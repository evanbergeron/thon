structure Lex : sig
datatype Token = FUN | NAT | COLON | LPAREN | RPAREN | NAME of string | INDENT | DEDENT
val lexFile : string -> Token list
end  =
struct

datatype Token = FUN | NAT | COLON | LPAREN | RPAREN | NAME of string | INDENT | DEDENT


exception UnexpectedIndentLevel

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
    in List.nth (chars, (List.length chars) - 1) end

fun getName' s n =
    if not (Char.isAlphaNum (lookaheadOnlyN s n)) then
        lookaheadN s (n-1)
    else
        getName' s (n+1)

fun getName s = getName' s 1

fun eatWhitespace stream =
    case TextIO.lookahead stream of
        NONE => ()
      | SOME #"\n" => (TextIO.input1 stream; ())
      | SOME c => if (Char.isSpace c)then
                  (TextIO.input1 stream; eatWhitespace stream)
                  else ()

fun onKeyword kw s =
    let val prefixOk = kw = (lookaheadN s (String.size kw))
        val afterChar = lookaheadOnlyN s ((String.size kw)+1)
        val suffixOk = Char.isSpace afterChar
    in
        prefixOk andalso suffixOk
    end

fun eatWord w s = (
    TextIO.inputN (s, (String.size w));
    eatWhitespace s
)

fun lexLines' s out indentLevel =
    case lookaheadN s 1 of
        "" => out
      | " " =>
        let val spaces =
                String.concat (List.tabulate (4*(!indentLevel), fn _ => " "))
            val dedentSpaces =
                String.concat (List.tabulate (4*((!indentLevel)-1), fn _ => " "))
        in
            if lookaheadN s (4 * (!indentLevel)) = spaces then
                (eatWord spaces s;
                 lexLines' s out indentLevel)
            else if lookaheadN s (4 * ((!indentLevel)-1)) = dedentSpaces then
                (eatWord spaces s;
                 lexLines' s (DEDENT::out) indentLevel)
            else
                raise UnexpectedIndentLevel
        end
      | "f" =>
        if onKeyword "fun" s then (
            eatWord "fun" s;
            lexLines' s (FUN::out) indentLevel
        ) else (
            let val name = getName s in
                eatWord name s;
                lexLines' s ((NAME name)::out) indentLevel
            end
        )
      | "n" =>
        if onKeyword "nat" s then (
            eatWord "nat" s;
            lexLines' s (NAT::out) indentLevel
        ) else (
            let val name = getName s in
                eatWord name s;
                lexLines' s ((NAME name)::out) indentLevel
            end
        )
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
               lexLines' s (INDENT::out) indentLevel)
          else
              (eatWord ":" s;
               lexLines' s (COLON::out) indentLevel)
      )
      | other => let val name = getName s in
                     eatWord name s;
                     lexLines' s ((NAME name)::out) indentLevel
                 end

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
