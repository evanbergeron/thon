(* thon - a small functional language *)
structure Thon : sig
              val parse : string -> Ast.exp
              val newParse : string -> Ast.exp
              val parseFile : string -> Ast.exp
              val typeof' : A.typ list -> 'b option list -> A.exp -> A.typ
              val typeof : A.exp -> A.typ
              (* val test : unit -> unit *)
              val eval : A.exp -> A.exp
              val evalCmd : A.cmd -> A.cmd
              val isval : A.exp -> bool
              val step : A.exp -> A.exp
              val stepCmd : A.cmd -> A.cmd
              val subst : A.exp -> A.exp -> A.exp
              val run : string -> A.exp
              val newRun : string -> A.exp
              val eraseNamesInTyp : A.typ -> A.typ
              val runFile : string -> A.exp
              val newRunFile : string -> A.exp
              val newParseFile : string -> A.exp
              val findParseErrors : string -> unit
              val elaborateDatatypes : A.exp -> A.exp
              val shiftDeBruijinIndicesInExp : int -> A.exp -> int -> A.exp
              val get : 'a list -> int -> 'a
              val istype : 'a option list -> A.typ -> bool
              val abstractOutType : string -> A.typ -> A.typ -> A.typ
              val substType : A.typ -> A.typ -> A.typ
              exception IllTyped
              exception IllTypedMsg of string
          end =
struct

exception IllTyped
exception IllTypedMsg of string
exception No
exception VarNotInContext
exception VarWithNegativeDeBruijinIndex of string * int
exception ClientTypeCannotEscapeClientScope
exception Unimplemented


fun get ctx i =
    case (List.findi (fn (j, _) => j = i) ctx) of
        NONE => (print (Int.toString i); raise VarNotInContext)
      | SOME (j,v) => v


fun istype typeCtx A.Nat = true
  | istype typeCtx A.Unit = true
  | istype typeCtx A.Bool = true
  | istype typeCtx (A.TypVar (name, i)) = i < (length typeCtx)
  | istype typeCtx (A.Arr(d, c)) = (istype typeCtx d) andalso (istype typeCtx c)
  | istype typeCtx (A.Prod(l, r)) = (istype typeCtx l) andalso (istype typeCtx r)
  | istype typeCtx (A.Plus(l, r)) = (istype typeCtx l) andalso (istype typeCtx r)
  | istype typeCtx (A.All (name, t')) = istype (NONE::typeCtx) t'
  | istype typeCtx (A.Some (name, t')) = istype (NONE::typeCtx) t'
  | istype typeCtx (A.TyRec (name, t')) = istype (NONE::typeCtx) t'


fun substType' src A.Nat bindingDepth = A.Nat
  | substType' src A.Unit bindingDepth = A.Unit
  | substType' src A.Bool bindingDepth = A.Bool
  | substType' src (A.TypVar (name, n)) bindingDepth =
    if n = bindingDepth then src else
    if n > bindingDepth then A.TypVar (name, n-1) else
    (A.TypVar (name, n))
  | substType' src (A.Arr(t, t')) bindingDepth = A.Arr((substType' src t bindingDepth),
                                                       (substType' src t' bindingDepth))
  | substType' src (A.Prod(l, r)) bindingDepth = A.Prod((substType' src l bindingDepth),
                                                        (substType' src r bindingDepth))
  | substType' src (A.Plus(l, r)) bindingDepth = A.Plus((substType' src l bindingDepth),
                                                        (substType' src r bindingDepth))
  | substType' src (A.All (name, t)) bindingDepth =
    A.All(name, substType' src t (bindingDepth + 1))
  | substType' src (A.Some (name, t)) bindingDepth =
    A.Some(name, substType' src t (bindingDepth + 1))
  | substType' src (A.TyRec (name, t)) bindingDepth =
    A.TyRec(name, substType' src t (bindingDepth + 1))


fun substType src dst = substType' src dst 0


(* Turns search to A.Var bindingDepth
 *
 * DEVNOTE: assumes the caller will place the result underneath a type
 * variable binding site.
 *
 * Remarkably similar to substType - might be able to dedup. This needs
 * to track bindingDepth though and subst in A.TypVar of the appropriate
 * depth.
 *)
fun abstractOutType' name search t bindingDepth =
    if t = search then (A.TypVar (name, bindingDepth)) else
    case t
     of A.Nat => A.Nat
      | A.Unit => A.Unit
      | A.Bool => A.Bool
      | A.TypVar (name, n)  => A.TypVar (name, n)
      | A.Arr(d, c) => A.Arr((abstractOutType' name search d bindingDepth),
                          (abstractOutType' name search c bindingDepth))
      | A.Prod(l, r) => A.Prod((abstractOutType' name search l bindingDepth),
                           (abstractOutType' name search r bindingDepth))
      | A.Plus(l, r) => A.Plus((abstractOutType' name search l bindingDepth),
                           (abstractOutType' name search r bindingDepth))
      | A.All (name, t') => A.All(name, abstractOutType' name search t' (bindingDepth+1))
      | A.Some (name, t') => A.Some(name, abstractOutType' name search t' (bindingDepth+1))
      | A.TyRec (name, t') => A.TyRec(name, abstractOutType' name search t' (bindingDepth+1))


fun abstractOutType name search t = abstractOutType' name search t 0


fun decrDeBruijinIndices t =
    case t of
        A.Nat => A.Nat
      | A.Unit => A.Unit
      | A.Bool => A.Bool
      | A.TypVar (name, i) => if (i-1) < 0 then raise ClientTypeCannotEscapeClientScope
                    else A.TypVar (name, i -1)
      | A.Arr(d, c) => A.Arr(decrDeBruijinIndices d, decrDeBruijinIndices c)
      | A.Prod(l, r) => A.Prod(decrDeBruijinIndices l, decrDeBruijinIndices r)
      | A.Plus(l, r) => A.Plus(decrDeBruijinIndices l, decrDeBruijinIndices r)
      | A.All (name, t') => A.All(name, decrDeBruijinIndices t')
      | A.Some (name, t') => A.Some(name, decrDeBruijinIndices t')
      | A.TyRec (name, t') => A.TyRec(name, decrDeBruijinIndices t')


fun shiftDeBruijinIndicesInExp shift dst bindingDepth =
    case dst
     of  A.Zero => A.Zero
       | A.TmUnit => A.TmUnit
       | A.True => A.True
       | A.False => A.False
       | A.Var (name, n)  => if n >= bindingDepth then A.Var(name, n+shift) else
                             A.Var(name, n)
       | A.Succ e2 => A.Succ (shiftDeBruijinIndicesInExp shift e2 bindingDepth)
       | A.ProdLeft e => A.ProdLeft (shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.ProdRight e => A.ProdRight (shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.PlusLeft (t, e) => A.PlusLeft (t, shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.Case(c, lname, l, rname, r) =>
         A.Case(shiftDeBruijinIndicesInExp shift c bindingDepth,
                lname, shiftDeBruijinIndicesInExp shift l (bindingDepth+1),
                rname, shiftDeBruijinIndicesInExp shift r (bindingDepth+1))
       | A.Fn (argName, t, f) => A.Fn(argName, t, (shiftDeBruijinIndicesInExp shift f (bindingDepth+1)))
       | A.Let (varname, vartype, varval, varscope) =>
         A.Let(varname,
               vartype,
               (shiftDeBruijinIndicesInExp shift varval (bindingDepth)),
               (shiftDeBruijinIndicesInExp shift varscope (bindingDepth+1)))
       | A.App (f, n) => A.App((shiftDeBruijinIndicesInExp shift f bindingDepth), (shiftDeBruijinIndicesInExp shift n bindingDepth))
       | A.Ifz (i, t, prev, e) => A.Ifz(shiftDeBruijinIndicesInExp shift i bindingDepth,
                                        shiftDeBruijinIndicesInExp shift t bindingDepth,
                                        prev,
                                        shiftDeBruijinIndicesInExp shift e (bindingDepth+1)) (* binds *)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
         A.Rec(shiftDeBruijinIndicesInExp shift i bindingDepth,
               shiftDeBruijinIndicesInExp shift baseCase bindingDepth,
               prevCaseName, shiftDeBruijinIndicesInExp shift recCase (bindingDepth+1))
       | A.Fix (name, t, e) =>
         A.Fix(name, t, shiftDeBruijinIndicesInExp shift e (bindingDepth+1)) (* binds *)
       | A.TypFn (name, e) => A.TypFn (name, shiftDeBruijinIndicesInExp shift e bindingDepth) (* abstracts over types, not exps *)
       | A.TypApp (appType, e) => A.TypApp(appType, shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.Impl(reprType, pkgImpl, t) => A.Impl(reprType, shiftDeBruijinIndicesInExp shift pkgImpl bindingDepth, t)
       | A.Use (pkg, clientName, typeName, client) =>
         A.Use(shiftDeBruijinIndicesInExp shift pkg bindingDepth,
               clientName,
               typeName,
               shiftDeBruijinIndicesInExp shift client (bindingDepth+1))
       | A.Pair (l, r) => A.Pair (shiftDeBruijinIndicesInExp shift l bindingDepth, shiftDeBruijinIndicesInExp shift r bindingDepth)
       | A.Fold(t, e') => A.Fold(t, (shiftDeBruijinIndicesInExp shift e' (bindingDepth))) (* binds a typ var *)
       | A.Unfold(e') => A.Unfold(shiftDeBruijinIndicesInExp shift e' (bindingDepth))


(* Just substitute the srcType in everywhere you see a A.TypVar bindingDepth *)
fun substTypeInCmd' srcType dstCmd bindingDepth =
    case dstCmd of
        A.Ret e => A.Ret(substTypeInExp' srcType e bindingDepth)
      | A.Bnd(name, e, c) =>
        A.Bnd(name,
              substTypeInExp' srcType e bindingDepth,
              substTypeInCmd' srcType c (bindingDepth+1)) (* binds immutable var *)


and substTypeInExp' srcType dstExp bindingDepth =
    case dstExp
     of  A.Zero => A.Zero
       | A.Var (name, i) => A.Var (name, i)
       | A.TmUnit => A.TmUnit
       | A.True => A.True
       | A.False => A.False
       | A.Succ e2 => A.Succ (substTypeInExp' srcType e2 bindingDepth)
       | A.ProdLeft e => A.ProdLeft (substTypeInExp' srcType e bindingDepth)
       | A.ProdRight e => A.ProdRight (substTypeInExp' srcType e bindingDepth)
       | A.PlusLeft (t, e) => A.PlusLeft (t, substTypeInExp' srcType e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, substTypeInExp' srcType e bindingDepth)
       | A.Case(c, lname, l, rname, r) =>
            A.Case(substTypeInExp' srcType c bindingDepth,
                   lname,
                   substTypeInExp' srcType l bindingDepth,
                   rname,
                   substTypeInExp' srcType r bindingDepth)
       | A.Fn (argName, argType, funcBody) =>
            A.Fn(argName, (substType' srcType argType bindingDepth),
                substTypeInExp' srcType funcBody bindingDepth)
       | A.Let (varname, vartype, varval, varscope) =>
            A.Let(varname, (substType' srcType vartype bindingDepth),
                  substTypeInExp' srcType varval bindingDepth,
                  substTypeInExp' srcType varscope bindingDepth
                 )
       | A.App (f, n) =>
            A.App (substTypeInExp' srcType f bindingDepth,
                 substTypeInExp' srcType n bindingDepth)
       | A.Ifz (i, t, prev, e) =>
            A.Ifz(substTypeInExp' srcType i bindingDepth,
                  substTypeInExp' srcType t bindingDepth,
                  prev,
                  substTypeInExp' srcType e bindingDepth)
       | A.Pair (l, r) =>
            A.Pair (substTypeInExp' srcType l bindingDepth,
                   substTypeInExp' srcType r bindingDepth)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
            A.Rec(substTypeInExp' srcType i bindingDepth,
                substTypeInExp' srcType baseCase bindingDepth,
                prevCaseName, substTypeInExp' srcType recCase bindingDepth)
       | A.Fix (name, t, e) =>
         A.Fix(name,
               substType' srcType t bindingDepth,
               substTypeInExp' srcType e bindingDepth)
       | A.TypFn (name, e) => A.TypFn(name, substTypeInExp' srcType e (bindingDepth+1)) (* binds type var *)
       | A.TypApp (appType, e) =>
            A.TypApp(substType' srcType appType bindingDepth,
                   substTypeInExp' srcType e bindingDepth)
       | A.Impl(reprType, pkgImpl, pkgType) =>
            A.Impl(substType' srcType reprType bindingDepth,
                 substTypeInExp' srcType pkgImpl bindingDepth,
                 substType' srcType pkgType bindingDepth)
       | A.Use (pkg, clientName, typeName, client) =>
            A.Use(substTypeInExp' srcType pkg bindingDepth,
                  clientName,
                  typeName,
                  substTypeInExp' srcType client (bindingDepth+1)) (*binds type var*)
       | A.Fold(t, e') => A.Fold(substType' srcType t bindingDepth,
                             substTypeInExp' srcType e' (bindingDepth+1)) (* binds typ var *)
       | A.Unfold(e') => A.Unfold(substTypeInExp' srcType e' bindingDepth)


fun setDeBruijnIndexInType t varnames typnames =
    let fun find name names =
        (case List.findi (fn (_, n : string) => n = name) names
         of NONE => NONE
          | SOME (i, _) => SOME i)
    in
    case t
     of  A.Nat => A.Nat
       | A.Unit => A.Unit
       | A.Bool => A.Bool
       | A.TypVar (name, i) =>
         (case find name typnames of
             NONE => (print ("unknown type var: "^ name); raise VarNotInContext)
           | SOME i => A.TypVar (name, i))
       | A.Arr(d, c) =>
            A.Arr(setDeBruijnIndexInType d varnames typnames,
                  setDeBruijnIndexInType c varnames typnames)
       | A.Prod(l, r) =>
            A.Prod(setDeBruijnIndexInType l varnames typnames,
                   setDeBruijnIndexInType r varnames typnames)
       | A.Plus(l, r) =>
            A.Plus(setDeBruijnIndexInType l varnames typnames,
                   setDeBruijnIndexInType r varnames typnames)
       | A.All (name, t') =>
            A.All(name, setDeBruijnIndexInType t' varnames (name::typnames))
       | A.Some (name, t') =>
            A.Some(name, setDeBruijnIndexInType t' varnames (name::typnames))
       | A.TyRec (name, t') =>
            A.TyRec(name, setDeBruijnIndexInType t' varnames (name::typnames))
       end


fun setDeBruijnIndexInCmd c varnames typnames mutnames =
    case c of
        A.Ret e => A.Ret(setDeBruijnIndexInExp e varnames typnames)
      | A.Bnd(name, e, c) =>
        A.Bnd(name,
              setDeBruijnIndexInExp e varnames typnames,
              setDeBruijnIndexInCmd c (name::varnames) typnames mutnames) (* binds immutable var *)


and setDeBruijnIndexInExp e varnames typnames =
    let fun find name names =
        (case List.findi (fn (_, n : string) => n = name) names
         of NONE => NONE
          | SOME (i, _) => SOME i)
    in
    case e
     of  A.Zero => e
       | A.TmUnit => e
       | A.True => e
       | A.False => e
       | A.Var (n, i) =>
         (case find n varnames of
             NONE => (print ("unknown var: "^ n); raise VarNotInContext)
           | SOME i => A.Var (n, i))
       | A.Fn(name, argType, funcBody) =>
         A.Fn(name,
               setDeBruijnIndexInType argType varnames typnames,
               setDeBruijnIndexInExp funcBody (name::varnames) typnames)
       | A.Let (varname, vartype, varval, varscope) =>
         A.Let(varname,
               setDeBruijnIndexInType vartype varnames typnames,
               (setDeBruijnIndexInExp varval (varnames) typnames),
               setDeBruijnIndexInExp varscope (varname::varnames) typnames)
       | A.Succ e2 => A.Succ (setDeBruijnIndexInExp e2 varnames typnames)
       | A.ProdLeft e => A.ProdLeft (setDeBruijnIndexInExp e varnames typnames)
       | A.ProdRight e => A.ProdRight (setDeBruijnIndexInExp e varnames typnames)
       | A.PlusLeft (t, e) =>
            A.PlusLeft(setDeBruijnIndexInType t varnames typnames,
                       setDeBruijnIndexInExp e varnames typnames)
       | A.PlusRight (t, e) =>
            A.PlusRight(setDeBruijnIndexInType t varnames typnames,
                        setDeBruijnIndexInExp e varnames typnames)
       | A.App (f, n) => A.App (setDeBruijnIndexInExp f varnames typnames,
                                setDeBruijnIndexInExp n varnames typnames)
       | A.Ifz (i, t, prev, e) => A.Ifz (setDeBruijnIndexInExp i varnames typnames,
                                   setDeBruijnIndexInExp t varnames typnames,
                                   prev,
                                   setDeBruijnIndexInExp e (prev::varnames) typnames)
       | A.Pair (l, r) => A.Pair (setDeBruijnIndexInExp l varnames typnames,
                                    setDeBruijnIndexInExp r varnames typnames)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
            A.Rec (setDeBruijnIndexInExp i varnames typnames,
                   setDeBruijnIndexInExp baseCase varnames typnames,
                   prevCaseName, (setDeBruijnIndexInExp recCase (prevCaseName::varnames) typnames))
       | A.Fix(name, t, e) =>
         A.Fix(name,
               setDeBruijnIndexInType t varnames typnames,
               setDeBruijnIndexInExp e (name::varnames) typnames)
       | A.Case (c, lname, l, rname, r) => A.Case(
            setDeBruijnIndexInExp c varnames typnames,
            lname,
            setDeBruijnIndexInExp l (lname::varnames) typnames,
            rname,
            setDeBruijnIndexInExp r (rname::varnames) typnames)
       | A.Use (pkg, clientName, typeName, client) => A.Use (
            setDeBruijnIndexInExp pkg varnames typnames,
            clientName,
            typeName,
            setDeBruijnIndexInExp client (clientName::varnames) (typeName::typnames))
       | A.TypApp (appType, e) =>
            A.TypApp (setDeBruijnIndexInType appType varnames typnames,
                      setDeBruijnIndexInExp e varnames typnames)
       | A.TypFn (name, e) => A.TypFn (name, setDeBruijnIndexInExp e varnames (name::typnames))
       | A.Fold(A.TyRec(name, t) (*declared type*), e'(* binds a typ var *)) =>
         A.Fold (A.TyRec(name, setDeBruijnIndexInType t varnames (name::typnames)),
                 setDeBruijnIndexInExp e' varnames typnames)
       | A.Unfold(e') =>
            A.Unfold (setDeBruijnIndexInExp e' varnames typnames)
       | A.Impl (reprType, pkgImpl, pkgType) =>
            A.Impl(setDeBruijnIndexInType reprType varnames typnames,
                   setDeBruijnIndexInExp pkgImpl varnames typnames,
                   setDeBruijnIndexInType pkgType varnames typnames)
       | A.Data(dname, lname, ltyp, rname, rtyp, exp) =>
         A.Data(dname,
                lname,
                (* binds a typ var*)
                setDeBruijnIndexInType ltyp varnames (dname::typnames),
                rname,
                (* binds a typ var*)
                setDeBruijnIndexInType rtyp varnames (dname::typnames),
                (* binds lname and rname and dname *)
                setDeBruijnIndexInExp exp (("expose" ^ dname)::rname::lname::varnames) (dname::typnames)
               )
       | _ => raise Unimplemented (* TODO *)
end

fun elaborateDatatype e =
    case e of
        A.Data(dataname, lname, ltyp, rname, rtyp, exp) =>
        let
            val datanameimpl = dataname ^ "Impl"
            val withType = A.TyRec(dataname, A.Plus(ltyp, rtyp))
            (* dataname is not bound here - the recursive reference is bound to the abstract
             * type bound in the Some *)
            val tInLtyp = substType (A.TypVar("t", 0)) ltyp
            val tInRtyp = substType (A.TypVar("t", 0)) rtyp
            val exposeFnType = A.Arr(A.TypVar("t", 0),
                                     A.Plus(tInLtyp, tInRtyp))
            val exposeFn = A.Fn(dataname ^ "exp", withType, A.Unfold(A.Var(dataname ^ "exp", 0)))
            val pkgType = A.Some("t", (*arbitrary name ok here *)
                                 A.Prod(A.Prod(A.Arr(tInLtyp, A.TypVar("t", 0)),
                                               A.Arr(tInRtyp, A.TypVar("t", 0))),
                                 exposeFnType)
                                )
            val lfn = A.Fn("foo", substType withType ltyp,
                           A.Fold(withType, A.PlusLeft(
                                      A.Plus(substType withType ltyp,
                                             substType withType rtyp),
                                      A.Var("foo", 0)
                                  )))
            val rfn = A.Fn("natAndNatList", substType withType rtyp,
                           A.Fold(withType, A.PlusRight(
                                      A.Plus(substType withType ltyp,
                                             substType withType rtyp),
                                      A.Var("natAndNatList", 0)
                                  )))
            val dtval = A.Impl(withType,
                               A.Pair(A.Pair(lfn, rfn), exposeFn),
                               pkgType)
            val useExp =
                A.Use(A.Var(datanameimpl, 0), "li", dataname,
                A.Let(lname, (A.Arr(ltyp, A.TypVar(dataname, 0))), A.ProdLeft(A.ProdLeft(A.Var("li", 0))),
               (A.Let(rname, (A.Arr(rtyp, A.TypVar(dataname, 0))), A.ProdRight(A.ProdLeft(A.Var("li", 1))),
                A.Let("expose" ^ dataname,
                      (A.Arr(A.TypVar(dataname, 0), A.Plus(ltyp, rtyp))),
                      A.ProdRight(A.Var("li", 2)),
                (* We've already bound term vars lname and rname, and type var dname.
                 *
                 * We have package impl to bind still, the use impl pkg exp to bind,
                 * the use impl pkg typ var is already bound as dname, and lname and
                 * rname are already bound.
                 *
                 * Just bump by two. Just a term rewrite, no new type variables are
                 * created in this rewrite.
                 *
                 * Need to bind impl and use vars. (Which are bound immediately before
                 * the two sides of the datatype declaration).
                 *)
                (shiftDeBruijinIndicesInExp 3 exp 3))))))
        in
            A.Let(datanameimpl, pkgType, dtval, useExp)
        end
      | _ => e


fun elaborateDatatypes e = A.expMap elaborateDatatype e


fun substTypeInExp srcType dstExp = substTypeInExp' srcType dstExp 0


fun eraseNamesInTyp t =
    let fun erase t =
            (case t of
                 A.TypVar(_, i) => A.TypVar("", i)
               | A.All(_, t') => A.All("", t')
               | A.Some(_, t') => A.Some("", t')
               | A.TyRec(_, t') => A.TyRec("", t')
               | _ => t
            )
    in A.typMap erase t end


fun typeEq (t : A.typ) (t' : A.typ) = ((eraseNamesInTyp t) = (eraseNamesInTyp t'))

fun cmdOk ctx typCtx c =
    case c of
        A.Ret e => (case typeof' ctx typCtx e of A.Nat => true | _ => false)
      | A.Bnd(name, e, c) => (
       (* TODO guess this binds, need to bump debrui index?
          can also toss this binding, i think it's a bit weird
          yeah when having typed commands, can do dis. why would this
          binding necassarily be a nat? seems unlikely
          eventually typeof' will feed us a type and then we can feed that into cmdOk
          recursive call
        *)
          case typeof' ctx typCtx e of
              A.TypCmd => (cmdOk (A.Nat::ctx) typCtx c)
            | _ => false
      )


and typeof' ctx typCtx A.Zero = A.Nat
  | typeof' ctx typCtx A.TmUnit = A.Unit
  | typeof' ctx typCtx A.True = A.Bool
  | typeof' ctx typCtx A.False = A.Bool
  | typeof' ctx typCtx (A.Var (name, i)) =
    if i < 0 then raise VarWithNegativeDeBruijinIndex(name, i) else get ctx i
  | typeof' ctx typCtx (A.Succ e2) = (typeof' ctx typCtx e2)
  | typeof' ctx typCtx (A.ProdLeft e) = let val A.Prod(l, r) = (typeof' ctx typCtx e) in l end
  | typeof' ctx typCtx (A.ProdRight e) = let val A.Prod(l, r) = (typeof' ctx typCtx e) in r end
  | typeof' ctx typCtx (A.PlusLeft (t, e)) =
    let val A.Plus(l, r) = t in
        if not (typeEq l (typeof' ctx typCtx e)) then
            raise IllTypedMsg "Sum type annotation does not match deduced type"
        else
            A.Plus(l, r)
    end
  | typeof' ctx typCtx (A.PlusRight (t, e)) =
    let val A.Plus(l, r) = t in
        if not (typeEq r (typeof' ctx typCtx e)) then
            raise IllTypedMsg "Sum type annotation does not match deduced type"
        else
            A.Plus(l, r)
    end
  | typeof' ctx typCtx (A.Case (c, lname, l, rname, r)) =
    let val A.Plus(lt, rt) = typeof' ctx typCtx c
        (* both bind a term var *)
        val typeofLeftBranch = typeof' (lt::ctx) typCtx l
        val typeofRightBranch= typeof' (rt::ctx) typCtx r
    in
        if not (typeEq (typeofLeftBranch) (typeofRightBranch)) then
            raise IllTypedMsg "Case statement branches types do not agree"
        else
            typeofLeftBranch
    end
  | typeof' ctx typCtx (A.Fn (argName, argType, funcBody)) =
    if not (istype typCtx argType) then raise IllTypedMsg "Function arg type is not a type."
    else A.Arr (argType, typeof' (argType::ctx) typCtx funcBody)
  | typeof' ctx typCtx (A.Let (varname, vartype, varval, varscope)) =
    if not (istype typCtx vartype) then
        raise IllTypedMsg "Let var type is not a type"
    else if not (typeEq (typeof' ctx typCtx varval) vartype) then
        raise IllTypedMsg "Let var type is not equal to deduced var value type."
    else
        typeof' (vartype::ctx) typCtx varscope
  | typeof' ctx typCtx (A.App (f, n)) =
    let val A.Arr (d, c) = typeof' ctx typCtx f
        val argType = typeof' ctx typCtx n
    in
        if not (typeEq d argType) then raise IllTyped
        else c
    end
  | typeof' ctx typCtx (A.Ifz (i, t, prev, e)) =
    let val Nat = typeof' ctx typCtx i
        val thenType = typeof' ctx typCtx t
        val elseType = typeof' (Nat::ctx) typCtx e
    in
        if not (typeEq thenType elseType) then raise IllTyped
        else thenType
    end
  | typeof' ctx typCtx (A.Pair (l, r)) = A.Prod(typeof' ctx typCtx l, typeof' ctx typCtx r)
  | typeof' ctx typCtx (A.Rec (i, baseCase, prevCaseName, recCase)) =
    let val A.Nat = typeof' ctx typCtx i
        val t = typeof' ctx typCtx baseCase
        val t2 = typeof' (t::ctx) typCtx recCase
    in
        if not (typeEq t t2) then raise IllTyped else t
    end
  | typeof' ctx typCtx (A.Fix (name, typ, e)) = typeof' (typ::ctx) typCtx e
  | typeof' ctx typCtx (A.TypFn (name, e)) = A.All(name, typeof' ctx (NONE::typCtx) e)
  | typeof' ctx typCtx (A.TypApp (appType, e)) =
    if not (istype typCtx appType) then raise IllTyped else
    let val A.All(name, t) = typeof' ctx typCtx e
    in
        substType appType t
    end
  | typeof' ctx typCtx (A.Impl (reprType, pkgImpl, pkgType)) =
    if not (istype [] reprType) then raise IllTyped else
    (* pkgType : [reprType/A.TypVar 0](t') *)
    let val deducedPkgType = typeof' ctx (NONE::typCtx) pkgImpl
        val A.Some(name, pkgType') = pkgType
    in
        if not (typeEq (abstractOutType name reprType deducedPkgType)
                       (abstractOutType name reprType pkgType')) then
            raise IllTyped
        else
            pkgType
    end
  | typeof' ctx typCtx (A.Use (pkg, clientName, typeName, client)) =
    let val A.Some(name, r) = typeof' ctx typCtx pkg
        (* binds BOTH a A.TypVar and a exp A.Var *)
        val clientType = typeof' (r::ctx) (NONE::typCtx) client
        val resType = decrDeBruijinIndices clientType
    in
        if not (istype typCtx resType) then raise IllTyped else
        resType
    end
  | typeof' ctx typCtx (A.Fold(A.TyRec(name, t) (*declared type*), e'(* binds a typ var *))) =
    let val deduced = typeof' ctx (NONE::typCtx) e'
        val absDeduced = A.TyRec(name, abstractOutType name (A.TyRec(name, t)) (deduced))
        val absT = abstractOutType name (A.TyRec(name, t)) (A.TyRec(name, t))
    in
        if not (typeEq absDeduced (A.TyRec(name, t))) then raise IllTyped
        else A.TyRec(name, t)
    end
  | typeof' ctx typCtx (A.Fold(_ , e'(* binds a typ var *))) =
    raise IllTypedMsg "Fold type argument must be a recursive type"
  | typeof' ctx typCtx (A.Unfold(e')) =
    let val A.TyRec(name, t) = typeof' ctx typCtx e' in
        substType (A.TyRec(name, t)) t
    end
  | typeof' ctx typCtx (A.Cmd c) =
    if not (cmdOk ctx typCtx c) then raise IllTyped else A.TypCmd


fun typeof e = typeof' [] [] e


fun isval e =
    case e of
        A.Zero => true
      | A.TmUnit => true
      | A.True => true
      | A.False => true
      | A.Succ(n) => isval n
      | A.Fn(_, _, _) => true
      | A.Let(_, _, _, _) => false
      | A.Pair(l, r) => (isval l) andalso (isval r)
      | A.TypFn (_, _)  => true
      | A.Impl(_, pkgImpl, _) => isval pkgImpl
      | A.PlusLeft(_, e') => isval e'
      | A.PlusRight(_, e') => isval e'
      | A.Fold(t, e') => isval e'
      | A.Cmd(_) => true
      | _ => false

fun isfinal c =
    case c of
        A.Ret e => isval e
      | _ => false

fun substExpInCmd' src c bindingDepth =
    case c of
        A.Ret e => A.Ret(subst' src e bindingDepth)
      | A.Bnd(name, e, c') =>
        A.Bnd(name,
              subst' src e bindingDepth,
              substExpInCmd' src c' (bindingDepth+1)) (* binds immutable var *)

and subst' src dst bindingDepth =
    case dst
     of  A.Zero => A.Zero
       | A.TmUnit => A.TmUnit
       | A.True => A.True
       | A.False => A.False
       | A.Var (name, n)  => if n = bindingDepth then src else
                   if n > bindingDepth then A.Var(name, n-1) else
                   A.Var(name, n)
       | A.Succ e2 => A.Succ (subst' src e2 bindingDepth)
       | A.ProdLeft e => A.ProdLeft (subst' src e bindingDepth)
       | A.ProdRight e => A.ProdRight (subst' src e bindingDepth)
       | A.PlusLeft (t, e) => A.PlusLeft (t, subst' src e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, subst' src e bindingDepth)
       | A.Case(c, lname, l, rname, r) =>
            A.Case(subst' src c bindingDepth,
                   lname, subst' src l (bindingDepth+1),
                   rname, subst' src r (bindingDepth+1))
       | A.Fn (argName, t, f) => A.Fn(argName, t, (subst' src f (bindingDepth+1)))
       | A.Let (varname, vartype, varval, varscope) =>
            A.Let(varname,
                  vartype,
                  (subst' src varval (bindingDepth)),
                  (subst' src varscope (bindingDepth+1)))
       | A.App (f, n) => A.App((subst' src f bindingDepth), (subst' src n bindingDepth))
       | A.Ifz (i, t, prev, e) => A.Ifz(subst' src i bindingDepth,
                                  subst' src t bindingDepth,
                                  prev,
                                  subst' src e (bindingDepth+1)) (* binds *)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
            A.Rec(subst' src i bindingDepth,
                subst' src baseCase bindingDepth,
                prevCaseName, subst' src recCase (bindingDepth+1))
       | A.Fix (name, t, e) =>
         A.Fix(name, t, subst' src e (bindingDepth+1)) (* binds *)
       | A.TypFn (name, e) => A.TypFn (name, subst' src e bindingDepth) (* abstracts over types, not exps *)
       | A.TypApp (appType, e) => A.TypApp(appType, subst' src e bindingDepth)
       | A.Impl(reprType, pkgImpl, t) => A.Impl(reprType, subst' src pkgImpl bindingDepth, t)
       | A.Use (pkg, clientName, typeName, client) =>
         A.Use(subst' src pkg bindingDepth,
               clientName,
               typeName,
               subst' src client (bindingDepth+1))
       | A.Pair (l, r) => A.Pair (subst' src l bindingDepth, subst' src r bindingDepth)
       | A.Fold(t, e') => A.Fold(t, (subst' src e' (bindingDepth))) (* binds a typ var *)
       | A.Unfold(e') => A.Unfold(subst' src e' (bindingDepth))
       | A.Cmd cmd => A.Cmd (substExpInCmd' src cmd bindingDepth)


fun subst src dst = subst' src dst 0

fun substExpInCmd src c = substExpInCmd' src c 0

fun stepCmd c =
    case c of
        A.Ret e => if not (isval e) then A.Ret (step e) else c
      | A.Bnd(name, e, c') =>
        if not (isval e) then
            A.Bnd(name, step e, c')
        else
            (* ensured by typechecker *)
            let val A.Cmd(c'') = e in
            if not (isfinal c'') then
                A.Bnd(name, A.Cmd(stepCmd c''), c')
            else
            (case c'' of
                A.Ret e => substExpInCmd e c'
              | _ => raise No)
            end

and step e =
    let val _ = typeof' [] [] e in
    if isval e then e else
    case e of
        A.Succ(n) => if not (isval n) then A.Succ(step n) else e
      | A.ProdLeft n  => if not (isval n) then A.ProdLeft(step n) else
                   let val A.Pair(l, r) = n in l end
      | A.ProdRight n  => if not (isval n) then A.ProdRight(step n) else
                    let val A.Pair(l, r) = n in r end
      | A.Pair(l, r) => if not (isval l) then A.Pair(step l, r) else
                       if not (isval r) then A.Pair(l, step r) else
                       e
      | A.App(f, n) => if not (isval f) then A.App(step f, n)
                     else (if not (isval n) then A.App(f, step n)
                           else let val A.Fn(argName, t, f') = f
                           in
                               (* plug `n` into `f'` *)
                               subst n f'
                           end
                          )
      | A.Ifz(i, t, prev, e) =>
            if not (isval i) then A.Ifz(step i, t, prev, e)
            else (case i of
                      A.Zero => t
                    | A.Succ i' => subst i' e
                    | _ => raise IllTypedMsg "ifz conditional must be an integer")
      (* BUG? should this eval varval before subst? should it eval varscope before subst? *)
      | A.Let (varname, vartype, varval, varscope) => subst varval varscope
      | A.Var (name, x) => (if x < 0 then raise VarNotInContext else A.Var (name, x))
      | A.Rec (A.Zero, baseCase, prevCaseName, recCase) => baseCase
      | A.Rec (A.Succ(i), baseCase, prevCaseName, recCase) =>
            (* Doesn't evaluate recursive call if not required. *)
            subst (A.Rec(i, baseCase, prevCaseName, recCase)) recCase
      | A.Rec (i, baseCase, prevCaseName, recCase) =>
            if not (isval i) then
                A.Rec(step i, baseCase, prevCaseName, recCase)
            else raise No
      | A.Fix(name, t, body) => subst e body
      | A.TypFn (name, e') => raise No (* Already isval *)
      | A.TypApp (t, e') =>
            if not (isval e') then (A.TypApp (t, step e'))
            else
                let val A.TypFn(name, e'') = e' in
                    substTypeInExp t e''
                end
      | A.Impl(reprType, pkgImpl, pkgType) =>
            if not (isval pkgImpl) then A.Impl(reprType, step pkgImpl, pkgType) else
            if not (isval e) then raise No else
            e
      | A.Use (pkg, clientName, typeName, client) =>
            if not (isval pkg) then A.Use (step pkg, clientName, typeName, client) else
            (* Note that there's no abstract type at runtime. *)
           (case pkg of
                A.Impl(reprType', pkgImpl', _) =>
                    subst pkgImpl' (substTypeInExp reprType' client)
              | _ => raise No
           )
      | A.PlusLeft (t, e') =>
            if not (isval e) then A.PlusLeft(t, step e')
            else e
      | A.PlusRight (t, e') =>
            if not (isval e) then A.PlusRight(t, step e')
            else e
      | A.Case (c, lname, l, rname, r) =>
        if not (isval c) then A.Case(step c, lname, l, rname, r)
        else (
            case c of
                 A.PlusLeft(_, e) => subst e l
               | A.PlusRight(_, e) => subst e r
               | _ => raise IllTyped
        )
      | A.Fold (t, e') => if not (isval e') then A.Fold(t, step e')
                        else (let val true = isval e in e end)
      | A.Unfold e' => if not (isval e') then A.Unfold (step e')
                     else (let val A.Fold(t, e'') = e' in e'' end)
      | A.Cmd c => A.Cmd (stepCmd c)
      | _ => if (isval e) then e else raise No
    end


fun parse s =
    let val ast : A.exp = Parse.parse s
    in
        setDeBruijnIndexInExp ast [] []
    end

fun newParse s =
    let val ast : A.exp = NewParse.parse s
    in
        setDeBruijnIndexInExp ast [] []
    end

fun parseFile filename =
    let val ast : A.exp = Parse.parseFile filename
    in
        setDeBruijnIndexInExp ast [] []
    end

fun newParseFile filename =
    let val ast : A.exp = NewParse.parseFile filename
    in
        setDeBruijnIndexInExp ast [] []
    end

fun findParseErrors filename =
    let val _ = parseFile filename
    in
        ()
    end

fun eval e = if isval e then e else eval (step e)

fun evalCmd c = if isfinal c then c else evalCmd (stepCmd c)

fun run s =
    let val e' = parse s
        val e = elaborateDatatypes e'
    in
        if isval e then e else eval (step e)
    end

fun newRun s =
    let val e' = newParse s
        val e = elaborateDatatypes e'
    in
        if isval e then e else eval (step e)
    end

fun runFile s =
    let val e' = parseFile s
        val e = elaborateDatatypes e'
    in
        if isval e then e else eval (step e)
    end

fun newRunFile s =
    let val e' = newParseFile s
        val e = elaborateDatatypes e'
    in
        if isval e then e else eval (step e)
    end

end (* structure Thon *)
