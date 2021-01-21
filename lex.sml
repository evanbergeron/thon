structure Lex : sig
datatype Token = FUN | NAT | COLON | LPAREN | RPAREN | NAME of string
              val lexFile : string -> Token list
          end  =
struct

datatype Token = FUN | NAT | COLON | LPAREN | RPAREN | NAME of string

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

fun eatWhitespace stream =
    case TextIO.lookahead stream of
        NONE => ()
      | SOME c => if (Char.isSpace c) then
                  (TextIO.input1 stream; eatWhitespace stream)
                  else ()

fun onKeyword kw s =
    let val prefixOk = kw = (lookaheadN s (String.size kw))
        val afterChar = lookaheadOnlyN s ((String.size kw)+1)
        val suffixOk = Char.isSpace afterChar
    in
        prefixOk andalso suffixOk
    end

fun eatKeyword kw s = (
    TextIO.inputN (s, (String.size kw));
    eatWhitespace s
)

fun lex' s out =
    case lookaheadN s 1 of
        "f" =>
            if onKeyword "fun" s then (
                eatKeyword "fun" s;
                lex' s (FUN::out)
            ) else (
                (* TODO eat name *)
                out
            )
      | "n" =>
            if onKeyword "nat" s then (
                eatKeyword "nat" s;
                lex' s (NAT::out)
            ) else (
                (* TODO eat name *)
                out
            )
       | other => (print (other ^"\n"); out)

fun lex s =
    let val backwards = lex' s [] in List.rev backwards end

fun lexFile filename = lex (TextIO.openIn filename)


end
