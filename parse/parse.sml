structure A = Ast

signature PARSE = sig
  exception ParseError of string
  val parse : string -> Ast.exp
  val parseFile : string -> Ast.exp
end

structure Parse :> PARSE =
struct

  exception ParseError of string

  structure ThonLrVals = ThonLrValsFn (structure Token = LrParser.Token)
  structure ThonLex = ThonLexFn (structure Tokens = ThonLrVals.Tokens)
  structure ThonParse = Join
      (structure ParserData = ThonLrVals.ParserData
       structure Lex = ThonLex
       structure LrParser = LrParser)

  fun parse' instream = let
      fun parseerror (s, i, p2) =
          raise ParseError ("line " ^ (Int.toString i) ^ ", " ^ s)
      val lexer = LrParser.Stream.streamify
                       (ThonLex.makeLexer (fn _ => TextIO.input instream))
      val (absyn, _) = ThonParse.parse(0, lexer, parseerror, ())
      in absyn end

  fun parseFile filename = parse' (TextIO.openIn filename)

  fun parse s = parse' (TextIO.openString s)

end
