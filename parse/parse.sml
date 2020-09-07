structure A = Ast

signature PARSE = sig
  val parse : unit -> Ast.Exp
end

structure Parse :> PARSE =
struct 

  structure ThonLrVals = ThonLrValsFn (structure Token = LrParser.Token)
  structure ThonLex = ThonLexFn (structure Tokens = ThonLrVals.Tokens)
  structure ThonParse = Join
      (structure ParserData = ThonLrVals.ParserData
       structure Lex = ThonLex
       structure LrParser = LrParser)

  fun invoke lexstream =
      let fun print_error (s,i:int,_) =
	      TextIO.output(TextIO.stdOut,
			    "Error, line " ^ (Int.toString i) ^ ", " ^ s ^ "\n")
       in ThonParse.parse(0,lexstream,print_error,())
      end

  fun parse () =
      let val lexer = ThonParse.makeLexer (fn _ =>
                                              (case TextIO.inputLine TextIO.stdIn
                                                of SOME s => s
                                                 | _ => ""))
	  fun loop lexer =
	      let val (result,lexer) = invoke lexer
		  val (nextToken,lexer) = ThonParse.Stream.get lexer
	      in loop lexer end
      in A.Zero
      end

end
