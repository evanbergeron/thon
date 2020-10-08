structure A = Ast

signature PARSE = sig
  val parse : string -> Ast.top
  val parseFile : string -> Ast.top
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
       in ThonParse.parse(15,lexstream,print_error,())
      end

  fun parse' instream readline = let
      val inputFn = if not readline then TextIO.input else
                    (fn _ => case TextIO.inputLine instream of SOME s => s | _ => "")
      fun parseerror (s, i, p2) = TextIO.output(TextIO.stdOut,
                            "Error, line " ^ (Int.toString i) ^ ", " ^ s ^ "\n")
      val lexer = LrParser.Stream.streamify
                       (ThonLex.makeLexer (fn _ => TextIO.input instream))
      val (absyn, _) = ThonParse.parse(100, lexer, parseerror, ())
      in absyn end

  fun parseFile filename = parse' (TextIO.openIn filename) false

  fun parse s = parse' (TextIO.openString s) false

  fun parseIn filename = parse' (TextIO.openIn filename) true

end
