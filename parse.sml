structure NewParse : PARSE =
struct

exception UnexpectedToken of string
exception Unimplemented

fun parse s = A.Zero

fun incr i = (i := !i + 1)

fun println s = print (s  ^ "\n")

fun debugPrint s =
    if false then println s
    else ()

fun errMsg (expectedToken, actualToken) =
    ("Expected " ^ (Lex.tokenToString expectedToken) ^
     ", got " ^ (Lex.tokenToString actualToken) ^ "\n")

fun expect tokens (token : Lex.Token) i =
    if List.nth (tokens, !i) <> token then
        (print (errMsg(token,  List.nth (tokens, !i)));
         raise UnexpectedToken(errMsg(token,  List.nth (tokens, !i))))
    else (i := !i + 1)

fun lookahead tokens i =
    if ((!i)+1) > ((List.length tokens) - 1)
    then NONE
    else SOME (List.nth (tokens, ((!i)+1)))

fun consumeName tokens i =
    let val res  =
            (case List.nth (tokens, !i) of
                 Lex.NAME n => n
               | tok =>

                 (print(errMsg((Lex.NAME "some name"), tok));
                  raise UnexpectedToken(errMsg((Lex.NAME "some name"), tok))))
    in i := (!i) + 1;
       res end

fun consumeNewlines tokens i =
    if (!i) >= (List.length tokens) then () else
    case List.nth (tokens, !i) of
        Lex.NEWLINE => (incr(i); consumeNewlines tokens i)
      | _ => ()

fun parseType tokens i =
    let val this =
            (case List.nth (tokens, !i) of
                 Lex.NAT => (i := (!i) + 1; A.Nat)
               | _ => raise Unimplemented)
    in
        (case List.nth (tokens, !i) of
             Lex.SARROW => (incr(i); A.Arr(this, (parseType tokens i))) | _ => this)
    end

fun parseExpr tokens i =
    (if (!i) >= (List.length tokens) then A.TmUnit else
     (case List.nth (tokens, !i) of
          Lex.FUN =>
          let
              val () = expect tokens Lex.FUN i
              val funcName = consumeName tokens i
              val () = debugPrint (funcName ^ " begin")
              val () = expect tokens Lex.LPAREN i
              (* TODO multiple params - should implement n-nary products first *)
              val argName = consumeName tokens i
              val argType = parseType tokens i
              val () = expect tokens Lex.RPAREN i
              val retType = parseType tokens i
              val funcType = A.Arr(argType, retType)
              val () = consumeNewlines tokens i
              val () = expect tokens Lex.INDENT i
              val () = debugPrint (funcName ^ " indent")
              val body = parseExpr tokens i
              val () = debugPrint (funcName ^ " end of body")
              val () = consumeNewlines tokens i
              val () = expect tokens Lex.DEDENT i
              val () = debugPrint (funcName ^ " dedent")
              val () = consumeNewlines tokens i
              val () = debugPrint (funcName ^ " afterwards")
          in
              if (!i) < (List.length tokens) andalso
                 List.nth (tokens, (!i))  = Lex.DEDENT then
                  (debugPrint (funcName ^ "see dedent next");
                   (* TODO double check these semantics. If there's a
                      dedent after this funciton definition, then this is
                      the last chunk of the parent block and so the value
                      of the parent block should be this function? If so,
                      will need to replicate this logic across every
                      other construct. *)
                   A.Let(funcName, funcType,
                         A.Fix(funcName, funcType,
                               A.Fn(argName, argType, body)), A.Var(funcName, ~1)))
              else
                  let
                      val rest = parseExpr tokens i
                  in
                      A.Let(funcName, funcType,
                            A.Fix(funcName, funcType,
                                  A.Fn(argName, argType, body)), rest)
                  end
          end
        | Lex.ZERO => (incr(i); A.Zero)
        | Lex.NAME name =>
          (case lookahead tokens i of
               SOME Lex.LPAREN => (
                (* Function application *)
                let val funcName = consumeName tokens i
                    val () = expect tokens Lex.LPAREN i
                    (* TODO multiple params *)
                    val arg = parseExpr tokens i
                    val () = expect tokens Lex.RPAREN i
                in
                    A.App(A.Var(funcName, ~1), arg)
                end
            )
             | _ => let val () = expect tokens (Lex.NAME name) i
                    in
                        A.Var (name, ~1)
                    end
          )

        | tok => (println ("Got unexpected " ^
                           (Lex.tokenToString tok)); raise Unimplemented))
    )

fun parseFile filename =
    let val tokens = Lex.lexFile filename
        val i = ref 0;
    in
        parseExpr tokens i
    end
end
