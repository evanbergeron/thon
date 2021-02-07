structure NewParse : PARSE =
struct 

exception UnexpectedToken
exception Unimplemented

fun parse s = A.Zero

fun expect tokens (token : Lex.Token) i =
    if List.nth (tokens, !i) <> token then
        raise UnexpectedToken
    else (i := !i + 1)

fun consumeName tokens i =
    let val res  = 
            (case List.nth (tokens, !i) of
                 Lex.NAME n => n
               | _ => raise UnexpectedToken)
    in i := (!i) + 1;
       res end
        
fun parseType tokens i = 
    case List.nth (tokens, !i) of
        Lex.NAT => (i := (!i) + 1; A.Nat)
      | _ => raise Unimplemented

fun parseExpr tokens i = 
    (
     (case List.nth (tokens, !i) of
          Lex.FUN =>
          let 
              val () = expect tokens Lex.FUN i
              val funcName = consumeName tokens i
              val () = expect tokens Lex.LPAREN i
              (* TODO multiple params *)
              val argName = consumeName tokens i
              val t = parseType tokens i
              val () = expect tokens Lex.RPAREN i
              val () = expect tokens Lex.NEWLINE i
              val () = expect tokens Lex.INDENT i
              val body = parseExpr tokens i
          in 
              A.Fn(argName, t, body)
          end
        | Lex.ZERO => A.Zero
        | _ => raise Unimplemented)
    )

fun parseFile filename = 
    let val tokens = Lex.lexFile filename
        val i = ref 0;
    in
        parseExpr tokens i
    end
end
