structure A = Ast

signature PARSE = sig
  val parse : string -> Ast.Exp
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

  fun parse filename = let
      val instream = TextIO.openIn filename
      val lexer = ThonParse.makeLexer (fn _ => (case TextIO.inputLine TextIO.stdIn
                                                  of SOME s => s | _ => ""))
      fun parseerror (s, p1, p2) = TextIO.output(TextIO.stdOut, "Parsing error\n")
      val lexer0 = LrParser.Stream.streamify
                       (ThonLex.makeLexer (fn _ => TextIO.input instream))
      val (absyn, _) = ThonParse.parse(0, lexer0, parseerror, ())
      in absyn end

end
