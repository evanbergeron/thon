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

(* fun nextNonAlphanumeric s = *)

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

fun lexChars s =
    let val tokens = []
        val i = ref 0
        val j = ref 0 in
    while !i < List.length s do (
        while !i < !j do (i := !i + 1);
        let val c = List.nth (s, !i) in
        []
        end;
        i := !i + 1
    );
    []
    end

(* fun lexFile filename = *)
(*     let val instream = TextIO.openIn filename *)
(*         val s : string = TextIO.inputAll instream *)
(*         val chars = explode s *)
(*         val res = lexChars chars *)
(*         val () = TextIO.closeIn instream *)
(*     in *)
(*         res *)
(*     end *)

fun lexFile filename = lex (TextIO.openIn filename)


end
