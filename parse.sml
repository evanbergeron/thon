structure A = Ast

signature PARSE = sig
  val parse : string -> Ast.exp
  val parseFile : string -> Ast.exp
end

structure Parse : PARSE =
struct

exception UnexpectedToken of string
exception Unimplemented of string

(* Good test transform - take prefixes of the program and check EOF everywhere *)

fun incr i = (i := !i + 1)

fun println s = print (s  ^ "\n")

fun debugPrint s =
    if false then println s
    else ()

fun errMsg (expectedToken, actualToken) =
    ("Expected " ^ (Lex.tokenToString expectedToken) ^
     ", got " ^ (Lex.tokenToString actualToken) ^ "\n")

fun expect tokens (token : Lex.Token) i =
    if (List.nth (tokens, !i) <> token) then
        (print (errMsg(token,  List.nth (tokens, !i)));
         raise UnexpectedToken(errMsg(token,  List.nth (tokens, !i))))
    else (i := !i + 1)

fun expectOrEof tokens token i =
    if !i > (List.length tokens - 1) then true else ((expect tokens token i); false)

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

(* TODO don't necassarily need to INDENT - output bool if it did and
 * feed that to consumeEndBlock *)
fun consumeStartBlock tokens i =
    let
        val () = expect tokens Lex.COLON i
        val blockIndents = Lex.NEWLINE = List.nth (tokens, !i)
    in
        if blockIndents then
            (let
                val () = consumeNewlines tokens i
                val () = expect tokens Lex.INDENT i
            in
                blockIndents
            end)
        else
            blockIndents
    end

fun consumeEndBlock tokens i startIndented =
    if not startIndented then consumeNewlines tokens i
    else
    let
        val () = consumeNewlines tokens i
        val eof = expectOrEof tokens Lex.DEDENT i
        val () = if not eof then consumeNewlines tokens i else ()
    in () end

fun parseType tokens i =
    let val this =
            (case List.nth (tokens, !i) of
                 Lex.NAT => (i := (!i) + 1; A.Nat)
               | Lex.NAME name => (i := (!i) + 1; A.TypVar(name, ~1))
               | Lex.BOOL => (i := (!i) + 1; A.Bool)
               | Lex.UNIT => (i := (!i) + 1; A.Unit)
               | a => (raise Unimplemented("See token that is not nat or name in type")))
    in
        (case List.nth (tokens, !i) of
            Lex.SARROW => (incr(i); A.Arr(this, (parseType tokens i)))
          | Lex.STAR => (incr(i); A.Prod(this, (parseType tokens i)))
          | _ => this)
    end


(* Parses between parens - expect LPAREN in caller before calling and RPAREN after *)
fun parseFuncCallParams tokens i =
    let
        val arg = parseExpr tokens i
    in
        (* TODO eventually got clean up all these unguarded array accesses *)
        (* Also UNDONE handle more than two func call params *)
        (case List.nth (tokens, !i) of
            Lex.COMMA =>
            (debugPrint "see comma";
            let
                val () = expect tokens Lex.COMMA i
                val arg2 = parseExpr tokens i
            in
                A.Pair(arg, arg2)
            end)
           | Lex.RPAREN => arg
           | tok => raise UnexpectedToken("expected func param or LPAREN, got " ^
                                          (Lex.tokenToString tok)))
    end


and parseExpr tokens i =
    (if (!i) >= (List.length tokens) then A.TmUnit else
     (case List.nth (tokens, !i) of
          Lex.FUN => (
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

               val indents = consumeStartBlock tokens i
               val body = parseExpr tokens i
               val () = consumeEndBlock tokens i indents
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
       )
        | Lex.DATA => (
            let
                val () = expect tokens Lex.DATA i
                val datatypeName = consumeName tokens i

                val indents = consumeStartBlock tokens i
                val fstTypeCtorName = consumeName tokens i
                val fstTypeCtorType = parseType tokens i
                val () = consumeNewlines tokens i
                val sndTypeCtorName = consumeName tokens i
                val sndTypeCtorType = parseType tokens i
                val () = consumeEndBlock tokens i indents

            in
                (* TODO handle dedent again case *)
                let
                    val rest = parseExpr tokens i
                in
                    A.Data(datatypeName,
                           fstTypeCtorName, fstTypeCtorType,
                           sndTypeCtorName, sndTypeCtorType,
                           rest)
                end
            end
        )
        | Lex.UNIT => (incr(i); A.TmUnit)
        | Lex.ZERO => (incr(i); A.Zero)
        | Lex.LPAREN =>
          let
              val () = expect tokens Lex.LPAREN i
              val expr = parseExpr tokens i
          in
              if (!i) < (List.length tokens) andalso
                 List.nth (tokens, (!i)) = Lex.COMMA then
                  let
                      val () = expect tokens Lex.COMMA i
                      val rightExpr = parseExpr tokens i
                      val () = expect tokens Lex.RPAREN i
                  in
                      A.Pair(expr, rightExpr)
                  end
              else (
                  expect tokens Lex.RPAREN i;
                  if (!i) < (List.length tokens) andalso
                     List.nth (tokens, (!i)) = Lex.LPAREN then
                      (* Function application *)
                      let val () = expect tokens Lex.LPAREN i
                          val arg = parseFuncCallParams tokens i
                          val () = expect tokens Lex.RPAREN i
                      in
                          A.App(expr, arg)
                      end
                  else  expr)
          end
        | Lex.FN => (
            let
                val () = expect tokens Lex.FN i
                val () = expect tokens Lex.LPAREN i
                (* TODO multiple params - should implement n-nary products first *)
                val argName = consumeName tokens i
                val argType = parseType tokens i
                val () = expect tokens Lex.RPAREN i
                val () = expect tokens Lex.DARROW i
                val body = parseExpr tokens i
                val () = consumeNewlines tokens i
            in
                A.Fn(argName, argType, body)
            end)
        | Lex.LET => (
            let
                val () = expect tokens Lex.LET i
                val varName = consumeName tokens i
                val varType = parseType tokens i
                val () = expect tokens Lex.EQ i
                val varExpr = parseExpr tokens i
                val () = consumeNewlines tokens i
                (* TODO last of block *)
                val rest = parseExpr tokens i
            in
                A.Let(varName, varType, varExpr, rest)
            end
        )
        | Lex.CASE => (
           let
               val () = expect tokens Lex.CASE i
               val caseExpr = parseExpr tokens i

               val indents = consumeStartBlock tokens i
               val fstCaseVarName = consumeName tokens i

               val fstCaseIndents = consumeStartBlock tokens i
               val fstCaseExpr = parseExpr tokens i
               val () = consumeEndBlock tokens i fstCaseIndents

               val sndCaseVarName = consumeName tokens i

               val sndCaseIndents = consumeStartBlock tokens i
               val sndCaseExpr = parseExpr tokens i
               val () = consumeEndBlock tokens i sndCaseIndents

               val () = expect tokens Lex.DEDENT i
           in
               A.Case(caseExpr, fstCaseVarName, fstCaseExpr, sndCaseVarName, sndCaseExpr)
            end
        )
        | Lex.IFZ => (
           let
               val () = expect tokens Lex.IFZ i
               val ifzExpr = parseExpr tokens i

               val indents = consumeStartBlock tokens i
               val () = expect tokens Lex.ZERO i

               val zeroIndents = consumeStartBlock tokens i
               val zeroExpr = parseExpr tokens i
               val () = consumeEndBlock tokens i zeroIndents

               val () = expect tokens Lex.SUCC i
               val () = expect tokens Lex.LPAREN i
               val prevName = consumeName tokens i
               val () = expect tokens Lex.RPAREN i

               val succIndents = consumeStartBlock tokens i
               val succExpr = parseExpr tokens i
               val () = consumeEndBlock tokens i succIndents

               val () = expect tokens Lex.DEDENT i
           in
               A.Ifz(ifzExpr, zeroExpr, prevName, succExpr)
            end
        )
        | Lex.NAME name =>
          (case lookahead tokens i of
               SOME Lex.LPAREN => (
                (* Function application *)
                let val funcName = consumeName tokens i
                    val () = expect tokens Lex.LPAREN i
                    val arg = parseFuncCallParams tokens i
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
        | Lex.SUCC =>
          (case lookahead tokens i of
               SOME Lex.LPAREN => (
                (* Succ application *)
                let val () = expect tokens Lex.SUCC i
                    val () = expect tokens Lex.LPAREN i
                    val arg = parseExpr tokens i
                    val () = expect tokens Lex.RPAREN i
                in
                    A.Succ(arg)
                end
            )
            | SOME tok => raise UnexpectedToken("Expected ( after s, got " ^ (Lex.tokenToString tok))
            | NONE => raise UnexpectedToken("Unexpected EOF after s")
          )
        | Lex.TRUE => (
            expect tokens Lex.TRUE i;
            A.True
        )
        | Lex.FALSE => (
            expect tokens Lex.FALSE i;
            A.False
        )
        | tok => (raise UnexpectedToken("Got unexpected " ^ (Lex.tokenToString tok))))
    )


fun parse s =
    let val tokens = Lex.lex s
        val i = ref 0;
    in
        parseExpr tokens i
    end
    handle UnexpectedToken msg => (print ("Parsing error: " ^ msg ^ "\n");
                                   raise (UnexpectedToken msg) )


fun parseFile filename =
    let val tokens = Lex.lexFile filename
        val i = ref 0;
    in
        parseExpr tokens i
    end

end
