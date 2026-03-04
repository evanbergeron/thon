structure Parse :> sig
  exception ParseError of string
  val parse : string -> Ast.exp
  val parseFile : string -> Ast.exp
  val parseTyp : string -> Ast.typ
end = struct

exception ParseError of string
fun error msg = raise ParseError msg

(* ---- Section 1: Tokens ---- *)
datatype token =
    TkId of string
  | TkZero | TkLParen | TkRParen | TkLBrack | TkRBrack
  | TkComma | TkSemicolon | TkColon | TkDot | TkDArrow | TkArrow
  | TkStar | TkPipe | TkSucc | TkFn | TkDeclare | TkFun | TkReturn
  | TkIs | TkGeneric | TkForall | TkSome | TkRec | TkFold | TkUnfold
  | TkFst | TkSnd | TkLeft | TkRight | TkCase | TkOf | TkWhen | TkThen
  | TkIfz | TkElse | TkIf | TkFix | TkIn | TkPackage | TkOpen
  | TkAs | TkData | TkNat | TkUnit | TkEof

fun tokenToString (TkId s) = "TkId(" ^ s ^ ")"
  | tokenToString TkZero = "ZERO" | tokenToString TkLParen = "("
  | tokenToString TkRParen = ")" | tokenToString TkLBrack = "["
  | tokenToString TkRBrack = "]" | tokenToString TkComma = ","
  | tokenToString TkSemicolon = ";" | tokenToString TkColon = ":"
  | tokenToString TkDot = "." | tokenToString TkDArrow = "=>"
  | tokenToString TkArrow = "->" | tokenToString TkStar = "*"
  | tokenToString TkPipe = "|" | tokenToString TkSucc = "SUCC"
  | tokenToString TkFn = "FN" | tokenToString TkDeclare = "DECLARE"
  | tokenToString TkFun = "FUN" | tokenToString TkReturn = "RETURN"
  | tokenToString TkIs = "IS"
  | tokenToString TkGeneric = "GENERIC" | tokenToString TkForall = "FORALL"
  | tokenToString TkSome = "SOME" | tokenToString TkRec = "REC"
  | tokenToString TkFold = "FOLD" | tokenToString TkUnfold = "UNFOLD"
  | tokenToString TkFst = "FST" | tokenToString TkSnd = "SND"
  | tokenToString TkLeft = "LEFT" | tokenToString TkRight = "RIGHT"
  | tokenToString TkCase = "CASE" | tokenToString TkOf = "OF"
  | tokenToString TkWhen = "WHEN" | tokenToString TkThen = "THEN"
  | tokenToString TkIfz = "IFZ" | tokenToString TkElse = "ELSE"
  | tokenToString TkIf = "IF"
  | tokenToString TkFix = "FIX" | tokenToString TkIn = "IN"
  | tokenToString TkPackage = "PACKAGE" | tokenToString TkOpen = "OPEN"
  | tokenToString TkAs = "AS" | tokenToString TkData = "DATA"
  | tokenToString TkNat = "NAT" | tokenToString TkUnit = "UNIT"
  | tokenToString TkEof = "EOF"

(* ---- Section 2: Lexer ---- *)
val keywords : (string * token) list = [
    ("ZERO", TkZero), ("SUCC", TkSucc), ("FN", TkFn),
    ("DECLARE", TkDeclare), ("FUN", TkFun), ("RETURN", TkReturn),
    ("IS", TkIs), ("GENERIC", TkGeneric), ("FORALL", TkForall),
    ("SOME", TkSome), ("REC", TkRec), ("FOLD", TkFold), ("UNFOLD", TkUnfold),
    ("FST", TkFst), ("SND", TkSnd), ("LEFT", TkLeft), ("RIGHT", TkRight),
    ("CASE", TkCase), ("OF", TkOf), ("WHEN", TkWhen), ("THEN", TkThen),
    ("IFZ", TkIfz), ("ELSE", TkElse), ("IF", TkIf),
    ("FIX", TkFix), ("IN", TkIn), ("PACKAGE", TkPackage), ("OPEN", TkOpen),
    ("AS", TkAs), ("DATA", TkData), ("NAT", TkNat), ("UNIT", TkUnit)
  ]

fun lookupKeyword s =
    case List.find (fn (k, _) => k = s) keywords of
        SOME (_, tk) => tk
      | NONE => TkId s

fun isAlpha c = Char.isAlpha c orelse c = #"_" orelse c = #"'"
fun isAlphaNum c = isAlpha c orelse Char.isDigit c

fun lex (src : string) : (token * int) list =
    let val chars = String.explode src
        fun go [] line acc = rev ((TkEof, line) :: acc)
          | go (#"\n" :: cs) line acc = go cs (line+1) acc
          | go (c :: cs) line acc =
            if Char.isSpace c then go cs line acc
            else if c = #"(" andalso (case cs of #"*"::_ => true | _ => false)
            then let val (_::cs') = cs in skipComment cs' line 1 acc end
            else if c = #"-" andalso (case cs of #">"::_ => true | _ => false)
            then let val (_::cs') = cs in go cs' line ((TkArrow, line)::acc) end
            else if c = #"=" andalso (case cs of #">"::_ => true | _ => false)
            then let val (_::cs') = cs in go cs' line ((TkDArrow, line)::acc) end
            else if c = #"(" then go cs line ((TkLParen, line)::acc)
            else if c = #")" then go cs line ((TkRParen, line)::acc)
            else if c = #"[" then go cs line ((TkLBrack, line)::acc)
            else if c = #"]" then go cs line ((TkRBrack, line)::acc)
            else if c = #"," then go cs line ((TkComma, line)::acc)
            else if c = #";" then go cs line ((TkSemicolon, line)::acc)
            else if c = #":" then go cs line ((TkColon, line)::acc)
            else if c = #"." then go cs line ((TkDot, line)::acc)
            else if c = #"*" then go cs line ((TkStar, line)::acc)
            else if c = #"|" then go cs line ((TkPipe, line)::acc)
            else if isAlpha c then
                let fun grab [] buf = (rev buf, [])
                      | grab (all as c'::cs') buf =
                        if isAlphaNum c' then grab cs' (c'::buf) else (rev buf, all)
                    val (buf, rest) = grab cs [c]
                    val word = String.implode buf
                in go rest line ((lookupKeyword word, line)::acc) end
            else error ("Unexpected character '" ^ String.str c ^ "' on line " ^ Int.toString line)
        and skipComment [] line _ acc = error ("Unterminated comment at line " ^ Int.toString line)
          | skipComment (#"(" :: #"*" :: cs) line depth acc = skipComment cs line (depth+1) acc
          | skipComment (#"*" :: #")" :: cs) line depth acc =
            if depth = 1 then go cs line acc else skipComment cs line (depth-1) acc
          | skipComment (#"\n" :: cs) line depth acc = skipComment cs (line+1) depth acc
          | skipComment (_ :: cs) line depth acc = skipComment cs line depth acc
    in go chars 1 [] end

(* ---- Section 3: Parser state ---- *)
type state = (token * int) list ref

fun mkState toks : state = ref toks

fun peek (st : state) : token =
    case !st of [] => TkEof | (tk, _) :: _ => tk

fun peekLine (st : state) : int =
    case !st of [] => 0 | (_, ln) :: _ => ln

fun advance (st : state) : token =
    case !st of
        [] => TkEof
      | (tk, _) :: rest => (st := rest; tk)

fun expect (st : state) (expected : token) : unit =
    let val tk = advance st
    in if tk = expected then ()
       else error ("Expected " ^ tokenToString expected ^
                   " but got " ^ tokenToString tk ^
                   " on line " ^ Int.toString (peekLine st))
    end

fun expectId (st : state) : string =
    case advance st of
        TkId s => s
      | tk => error ("Expected identifier but got " ^ tokenToString tk ^
                     " on line " ^ Int.toString (peekLine st))

(* ---- Section 4: Type parser ---- *)
(* Grammar:
   typ      = arrTyp
   arrTyp   = prodTyp ( "->" arrTyp )?           (* right-assoc *)
   prodTyp  = sumTyp ( "*" sumTyp )*
   sumTyp   = atomTyp ( "|" atomTyp )*
   atomTyp  = NAT | UNIT | id
            | "(" typ ")"
            | FORALL id "." typ
            | SOME id "." typ
            | REC id "." typ
*)

fun parseTyp st = parseArrTyp st

and parseArrTyp st =
    let val lhs = parseSumTyp st
    in if peek st = TkArrow
       then (advance st; Ast.Arr(lhs, parseArrTyp st))
       else lhs
    end

and parseSumTyp st =
    let val first = parseProdTyp st
        fun loop acc =
            if peek st = TkPipe
            then (advance st; loop (parseProdTyp st :: acc))
            else rev acc
        val all = loop [first]
    in case all of [t] => t | ts => Ast.Plus ts end

and parseProdTyp st =
    let val first = parseAtomTyp st
        fun loop acc =
            if peek st = TkStar
            then (advance st; loop (parseAtomTyp st :: acc))
            else rev acc
        val all = loop [first]
    in case all of [t] => t | ts => Ast.Prod ts end

and parseAtomTyp st =
    case peek st of
        TkNat => (advance st; Ast.Nat)
      | TkUnit => (advance st; Ast.Unit)
      | TkId name => (advance st; Ast.TypVar(name, ~1))
      | TkLParen =>
        (advance st;
         let val t = parseTyp st
         in expect st TkRParen; t end)
      | TkForall =>
        (advance st;
         let val name = expectId st
             val _ = expect st TkDot
             val body = parseTyp st
         in Ast.All(Ast.Scope(name, body)) end)
      | TkSome =>
        (advance st;
         let val name = expectId st
             val _ = expect st TkDot
             val body = parseTyp st
         in Ast.Some(Ast.Scope(name, body)) end)
      | TkRec =>
        (advance st;
         let val name = expectId st
             val _ = expect st TkDot
             val body = parseTyp st
         in Ast.TyRec(Ast.Scope(name, body)) end)
      | tk => error ("Expected type but got " ^ tokenToString tk ^
                     " on line " ^ Int.toString (peekLine st))

(* ---- Section 5: Expression parser ---- *)
(* Grammar overview (ALGOL/Ada style):
   exp       = decl | coreExp
   decl      = DECLARE id ":" typ IS exp IN exp
              | FUN id "(" id ":" typ ")" ":" typ IS exp IN exp
              | DATA id IS summands IN exp
   coreExp   = appExp                               (* handles application chains *)
   appExp    = unaryExp ( "(" exp ")" | "[" typ "]" )*
   unaryExp  = atomExp | SUCC "(" exp ")" | FOLD "[" typ "]" "(" exp ")"
             | UNFOLD "(" exp ")" | FST "(" exp ")" | SND "(" exp ")"
             | LEFT "[" typ "]" "(" exp ")" | RIGHT "[" typ "]" "(" exp ")"
             | FN "(" id ":" typ ")" exp
             | GENERIC id IS exp
             | FIX id ":" typ IS exp
             | IFZ exp OF ZERO THEN exp ELSE id THEN exp
             | CASE exp OF branches
             | PACKAGE typ IS exp AS typ
             | OPEN exp AS "(" id "," id ")" IN exp
             | IF exp THEN exp ELSE exp
   atomExp   = ZERO | UNIT | id | "(" expList ")"
*)

(* Check if token can start an expression *)
fun isExpStart tk =
    case tk of
        TkZero => true | TkUnit => true | TkId _ => true | TkLParen => true
      | TkSucc => true | TkFold => true | TkUnfold => true
      | TkFst => true | TkSnd => true | TkLeft => true | TkRight => true
      | TkFn => true | TkGeneric => true | TkFix => true
      | TkIfz => true | TkCase => true | TkPackage => true | TkOpen => true
      | TkDeclare => true | TkFun => true | TkData => true
      | TkIf => true
      | _ => false

fun parseExp st = parseDecl st

and parseDecl st =
    case peek st of
      (* DECLARE x : T IS e IN body *)
        TkDeclare =>
        (advance st;
         let val name = expectId st
             val _ = expect st TkColon
             val ty = parseTyp st
             val _ = expect st TkIs
             val value = parseExp st
             val _ = expect st TkIn
             val body = parseExp st
         in Ast.Let(ty, value, Ast.Scope(name, body)) end)

      (* FUN f(x : T) : U IS body IN exp *)
      | TkFun =>
        (advance st;
         let val fname = expectId st
             val _ = expect st TkLParen
             val argname = expectId st
             val _ = expect st TkColon
             val argty = parseTyp st
             val _ = expect st TkRParen
             val _ = expect st TkColon
             val retty = parseTyp st
             val _ = expect st TkIs
             val body = parseExp st
             val _ = expect st TkIn
             val rest = parseExp st
             val fn_ = Ast.Fn(argty, Ast.Scope(argname, body))
         in Ast.Let(Ast.Arr(argty, retty), fn_, Ast.Scope(fname, rest)) end)

      (* DATA name IS summands IN exp *)
      | TkData =>
        (advance st;
         let val dname = expectId st
             val _ = expect st TkIs
             (* parse summands: name(typ) | name(typ) | ... *)
             fun parseSummands () =
                 let val sname = expectId st
                     val _ = expect st TkLParen
                     val sty = parseTyp st
                     val _ = expect st TkRParen
                 in if peek st = TkPipe
                    then (advance st;
                          let val (ns, ts) = parseSummands ()
                          in (sname :: ns, sty :: ts) end)
                    else ([sname], [sty])
                 end
             val (names, types) = parseSummands ()
             val _ = expect st TkIn
             val body = parseExp st
         in Ast.Data(dname, names, types, body) end)

      | _ => parseCoreExp st

and parseCoreExp st = parseAppExp st

(* Application: f(arg) for term-app, e[T] for type-app *)
and parseAppExp st =
    let val head = parseUnaryExp st
        fun loop e =
            case peek st of
                TkLParen =>
                (advance st;
                 let val arg = parseExp st
                     val _ = expect st TkRParen
                 in loop (Ast.App(e, arg)) end)
              | TkLBrack =>
                (advance st;
                 let val ty = parseTyp st
                     val _ = expect st TkRBrack
                 in loop (Ast.TypApp(ty, e)) end)
              | _ => e
    in loop head end

and parseUnaryExp st =
    case peek st of
      (* SUCC(e) *)
        TkSucc =>
        (advance st;
         expect st TkLParen;
         let val e = parseExp st in expect st TkRParen; Ast.Succ e end)

      (* FOLD[T](e) *)
      | TkFold =>
        (advance st;
         expect st TkLBrack;
         let val ty = parseTyp st
         in expect st TkRBrack; expect st TkLParen;
            let val e = parseExp st
            in expect st TkRParen; Ast.Fold(ty, e) end
         end)

      (* UNFOLD(e) *)
      | TkUnfold =>
        (advance st;
         expect st TkLParen;
         let val e = parseExp st in expect st TkRParen; Ast.Unfold e end)

      (* FST(e) *)
      | TkFst =>
        (advance st;
         expect st TkLParen;
         let val e = parseExp st in expect st TkRParen; Ast.ProdNth(0, e) end)

      (* SND(e) *)
      | TkSnd =>
        (advance st;
         expect st TkLParen;
         let val e = parseExp st in expect st TkRParen; Ast.ProdNth(1, e) end)

      (* LEFT[T](e) *)
      | TkLeft =>
        (advance st;
         expect st TkLBrack;
         let val ty = parseTyp st
         in expect st TkRBrack; expect st TkLParen;
            let val e = parseExp st
            in expect st TkRParen; Ast.PlusNth(0, ty, e) end
         end)

      (* RIGHT[T](e) *)
      | TkRight =>
        (advance st;
         expect st TkLBrack;
         let val ty = parseTyp st
         in expect st TkRBrack; expect st TkLParen;
            let val e = parseExp st
            in expect st TkRParen; Ast.PlusNth(1, ty, e) end
         end)

      (* FN(x : T) body *)
      | TkFn =>
        (advance st;
         expect st TkLParen;
         let val name = expectId st
             val _ = expect st TkColon
             val ty = parseTyp st
         in expect st TkRParen;
            let val body = parseExp st
            in Ast.Fn(ty, Ast.Scope(name, body))
            end
         end)

      (* GENERIC t IS body *)
      | TkGeneric =>
        (advance st;
         let val name = expectId st
             val _ = expect st TkIs
             val body = parseExp st
         in Ast.TypFn(Ast.Scope(name, body))
         end)

      (* FIX x : T IS body *)
      | TkFix =>
        (advance st;
         let val name = expectId st
             val _ = expect st TkColon
             val ty = parseTyp st
             val _ = expect st TkIs
             val body = parseExp st
         in Ast.Fix(ty, Ast.Scope(name, body))
         end)

      (* IFZ e OF ZERO THEN e1 ELSE x THEN e2 *)
      | TkIfz =>
        (advance st;
         let val scrut = parseAppExp st
             val _ = expect st TkOf
             val _ = expect st TkZero
             val _ = expect st TkThen
             val zeroCase = parseExp st
             val _ = expect st TkElse
             val name = expectId st
             val _ = expect st TkThen
             val succCase = parseExp st
         in Ast.Ifz(scrut, zeroCase, Ast.Scope(name, succCase))
         end)

      (* CASE e OF WHEN x => e { | WHEN x => e } *)
      | TkCase =>
        (advance st;
         let val scrut = parseAppExp st
             val _ = expect st TkOf
             fun parseBranches () =
                 (expect st TkWhen;
                  let val name = expectId st
                      val _ = expect st TkDArrow
                      val body = parseExp st
                      val branch = Ast.Scope(name, body)
                  in if peek st = TkPipe
                     then (advance st; branch :: parseBranches ())
                     else [branch]
                  end)
             val branches = parseBranches ()
         in Ast.Case(scrut, branches)
         end)

      (* PACKAGE T IS e AS pkgT *)
      | TkPackage =>
        (advance st;
         let val reprTy = parseAtomTyp st
             val _ = expect st TkIs
             val impl = parseExp st
             val _ = expect st TkAs
             val pkgTy = parseTyp st
         in Ast.Impl(reprTy, impl, pkgTy)
         end)

      (* OPEN e AS (t, x) IN body *)
      | TkOpen =>
        (advance st;
         let val pkg = parseAppExp st
             val _ = expect st TkAs
             val _ = expect st TkLParen
             val tname = expectId st
             val _ = expect st TkComma
             val xname = expectId st
             val _ = expect st TkRParen
             val _ = expect st TkIn
             val body = parseExp st
         in Ast.Use(pkg, Ast.Scope(tname, Ast.Scope(xname, body)))
         end)

      (* IF cond THEN thn ELSE els - sugar for IFZ *)
      | TkIf =>
        (advance st;
         let val cond = parseAppExp st
             val _ = expect st TkThen
             val thn = parseExp st
             val _ = expect st TkElse
             val els = parseExp st
         in Ast.Ifz(cond, thn, Ast.Scope("_if", els))
         end)

      | _ => parseAtomExp st

and parseAtomExp st =
    case peek st of
        TkZero => (advance st; Ast.Zero)
      | TkUnit => (advance st; Ast.TmUnit)
      | TkId name => (advance st; Ast.Var(name, ~1))
      | TkLParen =>
        (advance st;
         (* Could be unit tuple (), single paren (e), or tuple (e, e, ...) *)
         if peek st = TkRParen
         then (advance st; Ast.TmUnit)
         else
         let val first = parseExp st
         in if peek st = TkComma
            then (* tuple *)
                let fun loop acc =
                        (expect st TkComma;
                         let val e = parseExp st
                         in if peek st = TkComma
                            then loop (e :: acc)
                            else rev (e :: acc)
                         end)
                    val rest = loop []
                in expect st TkRParen; Ast.Tuple(first :: rest) end
            else (expect st TkRParen; first)
         end)
      | tk => error ("Expected expression but got " ^ tokenToString tk ^
                     " on line " ^ Int.toString (peekLine st))

(* ---- Section 6: Entry points ---- *)
fun parse src =
    let val toks = lex src
        val st = mkState toks
        val e = parseExp st
        val _ = expect st TkEof
    in e end

fun parseFile filename =
    let val stream = TextIO.openIn filename
        val src = TextIO.inputAll stream
        val _ = TextIO.closeIn stream
    in parse src end

val parseTyp = fn src =>
    let val toks = lex src
        val st = mkState toks
        val t = parseTyp st
        val _ = expect st TkEof
    in t end

end
