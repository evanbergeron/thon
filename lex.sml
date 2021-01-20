structure Lex : sig
              datatype Token = FUN | COLON | LPAREN | RPAREN | NAME of string
              val lexFile : string -> Token list
          end  =
struct 

datatype Token = FUN | COLON | LPAREN | RPAREN | NAME of string

fun nextKeyword stream =
    nextKeywordRec stream ""
and nextKeywordRec stream out =
    case TextIO.input1 stream of
        NONE => out
      | SOME c => if (Char.isSpace c) orelse (Char.isPunct c) then out else nextKeywordRec stream (out ^ (Char.toString c))

fun lex' s out = 
    (* case TextIO.lookahead s of *)
    (* case TextIO.input1 s of *)
    case nextKeyword s of
        "" => out
      | "fun" => lex' s (FUN::out)
      | key => lex' s ((NAME key)::out)
and lex s = let val backwards = lex' s [] in List.rev backwards end

fun lexFile filename = lex (TextIO.openIn filename)
    
end
