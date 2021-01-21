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

fun inputWhitespace stream =
    case TextIO.lookahead stream of
        NONE => ()
      | SOME c => if (Char.isSpace c) then
                  (TextIO.input1 stream; inputWhitespace stream)
                  else ()

fun onKeyword kw s = kw = (lookaheadN s (String.size kw))

fun lex' s out =
    case lookaheadN s 3 of
        "" => out
      | "fun" => (
          TextIO.inputN (s, 3);
          inputWhitespace s;
          lex' s (FUN::out)
      )
      | "nat" => (
          TextIO.inputN (s, 3);
          inputWhitespace s;
          lex' s (NAT::out)
      )
      | other => (print (other ^"\n"); out)

fun lex s =
    let val backwards = lex' s [] in List.rev backwards end

fun lexFile filename = lex (TextIO.openIn filename)


end
