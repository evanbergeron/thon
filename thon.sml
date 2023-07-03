(* thon - a small functional language *)
structure Thon : sig
                   val parse : string -> Ast.exp
                   val parseFile : string -> Ast.exp
                   val typeof : A.exp -> A.typ
                   val test : unit -> unit
                   val eval : A.exp -> A.exp
                   val isval : A.exp -> bool
                   val step : A.exp -> A.exp
                   val subst : A.exp -> A.exp -> A.exp
                   val substType : A.typ -> A.typ -> A.typ
                   val run : string -> A.exp
                   val eraseNamesInTyp : A.typ -> A.typ
                   val runFile : string -> A.exp
                   val findParseErrors : string -> unit
                   val elaborateDatatype : A.exp -> A.exp
                   val elaborateDatatypes : A.exp -> A.exp
                   val shiftDeBruijinIndicesInExp : int -> A.exp -> int -> A.exp
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


fun printlnType t = (print (A.Print.typToString t); print "\n")
fun printlnExp t = (print (A.Print.expToString t); print "\n")
fun println s = (print s; print "\n")

fun istype typeCtx A.Nat = true
  | istype typeCtx A.Unit = true
  | istype typeCtx (A.TypVar (name, i)) = i < (length typeCtx)
  | istype typeCtx (A.Arr(d, c)) = (istype typeCtx d) andalso (istype typeCtx c)
  | istype typeCtx (A.Prod types) = List.all (istype typeCtx) types
  | istype typeCtx (A.Plus types) = List.all (istype typeCtx) types
  | istype typeCtx (A.All (name, t')) = istype (NONE::typeCtx) t'
  | istype typeCtx (A.Some (name, t')) = istype (NONE::typeCtx) t'
  | istype typeCtx (A.TyRec (name, t')) = istype (NONE::typeCtx) t'


fun substType' src A.Nat bindingDepth = A.Nat
  | substType' src A.Unit bindingDepth = A.Unit
  | substType' src (A.TypVar (name, n)) bindingDepth =
    if n = bindingDepth then src else
    if n > bindingDepth then A.TypVar(name, n-1) else A.TypVar(name, n)
  | substType' src (A.Arr(t, t')) bindingDepth = A.Arr((substType' src t bindingDepth),
                                                       (substType' src t' bindingDepth))
  | substType' src (A.Prod types) bindingDepth = A.Prod(List.map (fn t => substType' src t bindingDepth) types)
  | substType' src (A.Plus types) bindingDepth = A.Plus (List.map (fn t => substType' src t bindingDepth) types)
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
      | A.TypVar (name, n)  => A.TypVar (name, n)
      | A.Arr(d, c) => A.Arr((abstractOutType' name search d bindingDepth),
                          (abstractOutType' name search c bindingDepth))
      | A.Prod types => A.Prod(List.map (fn t => abstractOutType' name search t bindingDepth) types)
      | A.Plus types => A.Plus (List.map (fn t => abstractOutType' name search t bindingDepth) types)
      | A.All (name, t') => A.All(name, abstractOutType' name search t' (bindingDepth+1))
      | A.Some (name, t') => A.Some(name, abstractOutType' name search t' (bindingDepth+1))
      | A.TyRec (name, t') => A.TyRec(name, abstractOutType' name search t' (bindingDepth+1))


fun abstractOutType name search t = abstractOutType' name search t 0


fun decrDeBruijinIndices t =
    case t of
        A.Nat => A.Nat
      | A.Unit => A.Unit
      | A.TypVar (name, i) => if (i-1) < 0 then raise ClientTypeCannotEscapeClientScope
                    else A.TypVar (name, i -1)
      | A.Arr(d, c) => A.Arr(decrDeBruijinIndices d, decrDeBruijinIndices c)
      | A.Prod types => A.Prod(List.map decrDeBruijinIndices types)
      | A.Plus types => A.Plus(List.map decrDeBruijinIndices types)
      | A.All (name, t') => A.All(name, decrDeBruijinIndices t')
      | A.Some (name, t') => A.Some(name, decrDeBruijinIndices t')
      | A.TyRec (name, t') => A.TyRec(name, decrDeBruijinIndices t')


fun shiftDeBruijinIndicesInExp shift dst bindingDepth =
    case dst
     of  A.Zero => A.Zero
       | A.TmUnit => A.TmUnit
       | A.Var (name, n)  => if n >= bindingDepth then A.Var(name, n+shift) else
                             A.Var(name, n)
       | A.Succ e2 => A.Succ (shiftDeBruijinIndicesInExp shift e2 bindingDepth)
       | A.ProdLeft e => A.ProdLeft (shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.ProdRight e => A.ProdRight (shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.ProdNth (i, e) => A.ProdNth (i, shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.PlusLeft (t, e) => A.PlusLeft (t, shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.PlusNth (i, t, e) => A.PlusNth (i, t, shiftDeBruijinIndicesInExp shift e bindingDepth)
       | A.Case(c, names, exps) =>
         A.Case(shiftDeBruijinIndicesInExp shift c bindingDepth,
                names,
                List.map (fn e => shiftDeBruijinIndicesInExp shift e (bindingDepth+1)) exps)
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
       | A.Pair (l, r) => A.Pair (shiftDeBruijinIndicesInExp shift l bindingDepth,
                                  shiftDeBruijinIndicesInExp shift r bindingDepth)
       | A.Tuple exps => A.Tuple (List.map (fn e => shiftDeBruijinIndicesInExp shift e bindingDepth) exps)
       | A.Fold(t, e') => A.Fold(t, (shiftDeBruijinIndicesInExp shift e' (bindingDepth))) (* binds a typ var *)
       | A.Unfold(e') => A.Unfold(shiftDeBruijinIndicesInExp shift e' (bindingDepth))
       | A.Data(dname, names, types, e') => A.Data(dname, names, types, shiftDeBruijinIndicesInExp shift e' (bindingDepth+1+(List.length names)))


(* Just substitute the srcType in everywhere you see a A.TypVar bindingDepth *)
fun substTypeInExp' srcType dstExp bindingDepth =
    case dstExp
     of  A.Zero => A.Zero
       | A.Var (name, i) => A.Var (name, i)
       | A.TmUnit => A.TmUnit
       | A.Succ e2 => A.Succ (substTypeInExp' srcType e2 bindingDepth)
       | A.ProdLeft e => A.ProdLeft (substTypeInExp' srcType e bindingDepth)
       | A.ProdRight e => A.ProdRight (substTypeInExp' srcType e bindingDepth)
       | A.ProdNth (i, e) => A.ProdNth (i, substTypeInExp' srcType e bindingDepth)
       | A.PlusLeft (t, e) => A.PlusLeft (t, substTypeInExp' srcType e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, substTypeInExp' srcType e bindingDepth)
       | A.PlusNth (i, t, e) => A.PlusNth (i, t, substTypeInExp' srcType e bindingDepth)
       | A.Case(c, names, exps) =>
            A.Case(substTypeInExp' srcType c bindingDepth,
                   names,
                   List.map (fn e => substTypeInExp' srcType e bindingDepth) exps)
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
       | A.Tuple exps => A.Tuple (List.map (fn e => substTypeInExp' srcType e bindingDepth) exps)
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
       | A.TypVar (name, i) =>
         (case find name typnames of
             NONE => (print ("unknown type var: "^ name); raise VarNotInContext)
           | SOME i => A.TypVar (name, i))
       | A.Arr(d, c) =>
            A.Arr(setDeBruijnIndexInType d varnames typnames,
                  setDeBruijnIndexInType c varnames typnames)
       | A.Prod types  => A.Prod(List.map (fn t => setDeBruijnIndexInType t varnames typnames) types)
       | A.Plus types  => A.Plus(List.map (fn t => setDeBruijnIndexInType t varnames typnames) types)
       | A.All (name, t') =>
            A.All(name, setDeBruijnIndexInType t' varnames (name::typnames))
       | A.Some (name, t') =>
            A.Some(name, setDeBruijnIndexInType t' varnames (name::typnames))
       | A.TyRec (name, t') =>
            A.TyRec(name, setDeBruijnIndexInType t' varnames (name::typnames))
       end


fun setDeBruijnIndex e varnames typnames =
    let fun find name names =
        (case List.findi (fn (_, n : string) => n = name) names
         of NONE => NONE
          | SOME (i, _) => SOME i)
    in
    case e
     of  A.Zero => e
       | A.TmUnit => e
       | A.Var (n, i) =>
         (case find n varnames of
             NONE => (print ("unknown var: "^ n); raise VarNotInContext)
           | SOME i => A.Var (n, i))
       | A.Fn(name, argType, funcBody) =>
         A.Fn(name,
               setDeBruijnIndexInType argType varnames typnames,
               setDeBruijnIndex funcBody (name::varnames) typnames)
       | A.Let (varname, vartype, varval, varscope) =>
         A.Let(varname,
               setDeBruijnIndexInType vartype varnames typnames,
               (setDeBruijnIndex varval (varnames) typnames),
               setDeBruijnIndex varscope (varname::varnames) typnames)
       | A.Succ e2 => A.Succ (setDeBruijnIndex e2 varnames typnames)
       | A.ProdLeft e => A.ProdLeft (setDeBruijnIndex e varnames typnames)
       | A.ProdRight e => A.ProdRight (setDeBruijnIndex e varnames typnames)
       | A.ProdNth (i, e) => A.ProdNth (i, setDeBruijnIndex e varnames typnames)
       | A.PlusLeft (t, e) =>
            A.PlusLeft(setDeBruijnIndexInType t varnames typnames,
                       setDeBruijnIndex e varnames typnames)
       | A.PlusRight (t, e) =>
            A.PlusRight(setDeBruijnIndexInType t varnames typnames,
                        setDeBruijnIndex e varnames typnames)
       | A.PlusNth (i, t, e) =>
            A.PlusNth(i, setDeBruijnIndexInType t varnames typnames,
                        setDeBruijnIndex e varnames typnames)
       | A.App (f, n) => A.App (setDeBruijnIndex f varnames typnames,
                                setDeBruijnIndex n varnames typnames)
       | A.Ifz (i, t, prev, e) => A.Ifz (setDeBruijnIndex i varnames typnames,
                                   setDeBruijnIndex t varnames typnames,
                                   prev,
                                   setDeBruijnIndex e (prev::varnames) typnames)
       | A.Pair (l, r) => A.Pair (setDeBruijnIndex l varnames typnames,
                                  setDeBruijnIndex r varnames typnames)
       | A.Tuple exps => A.Tuple (List.map (fn e => setDeBruijnIndex e varnames typnames) exps)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
            A.Rec (setDeBruijnIndex i varnames typnames,
                   setDeBruijnIndex baseCase varnames typnames,
                   prevCaseName, (setDeBruijnIndex recCase (prevCaseName::varnames) typnames))
       | A.Fix(name, t, e) =>
         A.Fix(name,
               setDeBruijnIndexInType t varnames typnames,
               setDeBruijnIndex e (name::varnames) typnames)
       | A.Case (c, names, exps) => A.Case(
            setDeBruijnIndex c varnames typnames,
            names,
            List.mapi (fn (i, e) => setDeBruijnIndex e ((List.nth (names, i))::varnames) typnames) exps)
       | A.Use (pkg, clientName, typeName, client) => A.Use (
            setDeBruijnIndex pkg varnames typnames,
            clientName,
            typeName,
            setDeBruijnIndex client (clientName::varnames) (typeName::typnames))
       | A.TypApp (appType, e) =>
            A.TypApp (setDeBruijnIndexInType appType varnames typnames,
                      setDeBruijnIndex e varnames typnames)
       | A.TypFn (name, e) => A.TypFn (name, setDeBruijnIndex e varnames (name::typnames))
       | A.Fold(A.TyRec(name, t) (*declared type*), e'(* binds a typ var *)) =>
         A.Fold (A.TyRec(name, setDeBruijnIndexInType t varnames (name::typnames)),
                 setDeBruijnIndex e' varnames typnames)
       | A.Unfold(e') =>
            A.Unfold (setDeBruijnIndex e' varnames typnames)
       | A.Impl (reprType, pkgImpl, pkgType) =>
            A.Impl(setDeBruijnIndexInType reprType varnames typnames,
                   setDeBruijnIndex pkgImpl varnames typnames,
                   setDeBruijnIndexInType pkgType varnames typnames)
       | A.Data(dname, names, types, exp) =>
         A.Data(dname,
                names,
                (* binds a typ var for each name in names *)
                List.map (fn t => setDeBruijnIndexInType t varnames (dname::typnames)) types,
                (* binds *)
                setDeBruijnIndex exp (("expose" ^ dname)::((List.rev names)@varnames)) (dname::typnames)
               )
       | _ => raise Unimplemented (* TODO *)
end

fun elaborateDatatype e =
    case e of
        A.Data(dataname, names, types, exp) =>
        let
            val datanameimpl = dataname ^ "Impl"
            val withType = A.TyRec(dataname, A.Plus types)
            (* dataname is not bound here - the recursive reference is bound to the abstract
             * type bound in the Some *)
            val tInTypes = List.map (substType (A.TypVar("t", 0))) types
            val exposeFnType = A.Arr(A.TypVar("t", 0), A.Plus tInTypes)
            val exposeFn = A.Fn(dataname ^ "exp", withType, A.Unfold(A.Var(dataname ^ "exp", 0)))
            val pkgType = A.Some("t", (*arbitrary name ok here *)
                                 A.Prod([A.Prod(
                                              List.map (fn t => A.Arr(t, A.TypVar("t", 0))) tInTypes),
                                         exposeFnType])
                                )
            val sumTypeForInjection = List.map (substType withType) types;
            fun makeInjectionExprFromSummandType (i, t) =
                let val name = "summand" ^ Int.toString i
                in
                A.Fn(name,
                     substType withType t, (* getting typ, 0 instead of typ,1 here *)
                     A.Fold(withType,
                            (* UNDONE is DeBruijin index 0 ok here?
                             * Do we need to be incrementing a bindingDepth somewhere else?
                             *)
                            A.PlusNth(i, A.Plus sumTypeForInjection, A.Var(name, 0))))
                end

            val fns = List.mapi makeInjectionExprFromSummandType types;
            val dtval = A.Impl(withType,
                               A.Tuple[A.Tuple fns, exposeFn],
                               pkgType)

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
             *
             * UNDONE need to bump by something parametrized on the length of the list
             *)
            val shift = (List.length types) + 1;
            val innerExp = A.Let("expose" ^ dataname,
                                 A.Arr(A.TypVar(dataname, 0), A.Plus types),
                                 A.ProdNth(1, A.Var("li", (List.length types))),
                                 shiftDeBruijinIndicesInExp shift exp shift);
            fun makeDecls i =
                if i = (List.length types) then innerExp
                else
                    A.Let(List.nth (names, i),
                          A.Arr(List.nth (types, i), A.TypVar(dataname, 0)),
                          A.ProdNth(i, A.ProdNth(0, A.Var("li", i))),
                          makeDecls (i+1))
        in
            A.Let(datanameimpl, pkgType, dtval, A.Use(A.Var(datanameimpl, 0), "li", dataname, makeDecls 0))
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


fun typeof' ctx typCtx A.Zero = A.Nat
  | typeof' ctx typCtx A.TmUnit = A.Unit
  | typeof' ctx typCtx (A.Var (name, i)) =
    if i < 0 then raise VarWithNegativeDeBruijinIndex(name, i) else get ctx i
  | typeof' ctx typCtx (A.Succ e2) = (typeof' ctx typCtx e2)
  | typeof' ctx typCtx (A.ProdLeft e) = let val A.Prod [l, r] = (typeof' ctx typCtx e) in l end
  | typeof' ctx typCtx (A.ProdRight e) = let val A.Prod [l, r] = (typeof' ctx typCtx e) in r end
  | typeof' ctx typCtx (A.ProdNth (i,e)) = let val A.Prod types = (typeof' ctx typCtx e) in List.nth (types, i) end
  | typeof' ctx typCtx (A.PlusLeft (t, e)) =
    let val A.Plus[l, r] = t in
        if not (typeEq l (typeof' ctx typCtx e)) then
            raise IllTypedMsg "Sum type annotation does not match deduced type"
        else
            A.Plus[l, r]
    end
  | typeof' ctx typCtx (A.PlusRight (t, e)) =
    let val A.Plus[l, r] = t in
        if not (typeEq r (typeof' ctx typCtx e)) then
            raise IllTypedMsg "Sum type annotation does not match deduced type"
        else
            A.Plus[l, r]
    end
  | typeof' ctx typCtx (A.PlusNth (i, t, e)) =
    let val A.Plus types = t in
        if not (typeEq (List.nth (types, i)) (typeof' ctx typCtx e)) then (
            print "Sum type annotation:\n";
            printlnType (List.nth (types, i));
            print "does not match deduced type:\n";
            printlnType ((typeof' ctx typCtx e));
            raise IllTyped
        ) else
            A.Plus types
    end
  | typeof' ctx typCtx (A.Case (c, names, exps)) =
    let
        val A.Plus types = typeof' ctx typCtx c
        val typeofFirstBranch = typeof' ((* binds exp var *) List.nth(types, 0)::ctx) typCtx (List.nth (exps, 0))
        val typesExps = List.mapi (fn (i, _) => (List.nth (types, i), List.nth(exps, i))) types;
    in
        if not (List.all (fn (t, e) => (typeEq typeofFirstBranch (typeof' (t::ctx) typCtx e))) typesExps) then
            raise IllTypedMsg "Case statement branches types do not agree"
        else
            typeofFirstBranch
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
  | typeof' ctx typCtx (A.Pair (l, r)) = A.Prod [typeof' ctx typCtx l, typeof' ctx typCtx r]
  | typeof' ctx typCtx (A.Tuple exps) = A.Prod (List.map (typeof' ctx typCtx) exps)
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
    if not (istype typCtx reprType) then (
        print ("Package implementation representation type:\n" ^ A.Print.typToString(reprType) ^ "\nis not a type.\n");
        raise IllTyped
    ) else
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
        val finalType = A.TyRec(name, t)
        val absDeduced = A.TyRec(name, abstractOutType name finalType deduced)
    in
        if not (typeEq absDeduced finalType) then (
            print "Recursive type deduced type:\n";
            print (A.Print.typToString absDeduced);
            print "\nis not type-equal to declared type:\n";
            printlnType (A.TyRec(name, t));
            raise IllTyped
         ) else
            finalType
    end
  | typeof' ctx typCtx (A.Fold(_ , e'(* binds a typ var *))) =
    raise IllTypedMsg "Fold type argument must be a recursive type"
  | typeof' ctx typCtx (A.Unfold(e')) =
    let val A.TyRec(name, t) = typeof' ctx typCtx e' in
        substType (A.TyRec(name, t)) t
    end


fun typeof e = typeof' [] [] e


fun isval e =
    case e of
        A.Zero => true
      | A.TmUnit => true
      | A.Succ(n) => isval n
      | A.Fn(_, _, _) => true
      | A.Let(_, _, _, _) => false
      | A.Pair(l, r) => (isval l) andalso (isval r)
      | A.Tuple exps => List.all isval exps
      | A.TypFn (_, _)  => true
      | A.Impl(_, pkgImpl, _) => isval pkgImpl
      | A.PlusLeft(_, e') => isval e'
      | A.PlusRight(_, e') => isval e'
      | A.PlusNth(_, _, e') => isval e'
      | A.Fold(t, e') => isval e'
      | _ => false


fun subst' src dst bindingDepth =
    case dst
     of  A.Zero => A.Zero
       | A.TmUnit => A.TmUnit
       | A.Var (name, n)  => if n = bindingDepth then src else
                   if n > bindingDepth then A.Var(name, n-1) else
                   A.Var(name, n)
       | A.Succ e2 => A.Succ (subst' src e2 bindingDepth)
       | A.ProdLeft e => A.ProdLeft (subst' src e bindingDepth)
       | A.ProdRight e => A.ProdRight (subst' src e bindingDepth)
       | A.ProdNth (i, e) => A.ProdNth (i, subst' src e bindingDepth)
       | A.PlusLeft (t, e) => A.PlusLeft (t, subst' src e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, subst' src e bindingDepth)
       | A.PlusNth (i, t, e) => A.PlusNth (i, t, subst' src e bindingDepth)
       | A.Case(c, names, exps) =>
            A.Case(subst' src c bindingDepth,
                   names, List.map (fn e => subst' src e (bindingDepth+1)) exps)
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
       | A.Tuple exps => A.Tuple (List.map (fn e => subst' src e bindingDepth) exps)
       | A.Fold(t, e') => A.Fold(t, (subst' src e' (bindingDepth))) (* binds a typ var *)
       | A.Unfold(e') => A.Unfold(subst' src e' (bindingDepth))


fun subst src dst = subst' src dst 0


fun step e =
    let val _ = typeof' [] [] e in
    if isval e then e else
    case e of
        A.Succ(n) => if not (isval n) then A.Succ(step n) else e
      | A.ProdLeft n  => if not (isval n) then A.ProdLeft(step n) else
                   let val A.Pair(l, r) = n in l end
      | A.ProdRight n  => if not (isval n) then A.ProdRight(step n) else
                    let val A.Pair(l, r) = n in r end
      | A.ProdNth (i, n)  => if not (isval n) then A.ProdNth(i, step n) else
                    let val A.Tuple exps = n in List.nth (exps, i) end
      | A.Pair(l, r) => if not (isval l) then A.Pair(step l, r) else
                       if not (isval r) then A.Pair(l, step r) else
                       e
      | A.Tuple exps =>
        let fun recr [] = []
              | recr (e::es) = if isval e then e::(recr es) else (step e)::es
        in
            A.Tuple (recr exps)
        end
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
            if not (isval e') then A.PlusLeft(t, step e')
            else e
      | A.PlusRight (t, e') =>
            if not (isval e') then A.PlusRight(t, step e')
            else e
      | A.PlusNth (i, t, e') =>
        (print "plusnth";
            if not (isval e') then A.PlusNth(i, t, step e')
            else e)
      | A.Case (c, names, exps) =>
        if not (isval c) then A.Case(step c, names, exps)
        else (
            case c of
                 A.PlusLeft(_, e) => subst e (List.nth (exps, 0))
               | A.PlusRight(_, e) => subst e (List.nth (exps, 1))
               | A.PlusNth(i, _, e) => subst e (List.nth (exps, i))
               | _ => raise IllTyped
        )
      | A.Fold (t, e') => if not (isval e') then A.Fold(t, step e')
                        else (let val true = isval e in e end)
      | A.Unfold e' => if not (isval e') then A.Unfold (step e')
                     else (let val A.Fold(t, e'') = e' in e'' end)
      | _ => if (isval e) then e else raise No
    end


fun parse s =
    let val ast : A.exp = Parse.parse s
    in
        setDeBruijnIndex ast [] []
    end

fun parseFile filename =
    let val ast : A.exp = Parse.parseFile filename
    in
        setDeBruijnIndex ast [] []
    end

fun findParseErrors filename =
    let val _ = parseFile filename
    in
        ()
    end

fun eval e = if isval e then e else eval (step e)

fun run s =
    let val e' = parse s
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


(******* Tests *******)

fun test() = let
open A;
(* Data Natlist = None | Some(Nat, Natlist) *)
val natlist : typ = TyRec("natlist",Plus[Unit, Prod [Nat, TypVar ("natlist", 0)]]);
val Fn ("natlist", TyRec ("l",Plus [Unit,Prod [Nat,TypVar ("l", 0)]]),Var ("natlist",0)) =
    parse "\\ natlist : (u l. (unit ||  (nat * l))) -> natlist";

(* id function on natlists *)
val TypApp
    (TyRec ("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist",0)])]),
     TypFn ("s",Fn ("x",TypVar ("s",0),Var ("x",0)))) : Ast.exp =
    parse "((poly s -> \\ x : s -> x) (u natlist. (unit || (nat * natlist))))";
val nilNatList =
    Fold(natlist, PlusLeft(Plus[Unit, Prod([Nat, natlist])], TmUnit));

(* TODO don't hardcode dir *)
val parsedConsNatList = parseFile "/home/evan/thon/examples/emptynatlist.thon";

val true = (nilNatList = parsedConsNatList);

val TmUnit : Ast.exp = parse "unit";

val singletonList =
    Fold(natlist, PlusRight(Plus[Unit, Prod([Nat, natlist])], Pair(Zero,
    Fold(natlist, PlusLeft(Plus[Unit, Prod([Nat, natlist])], TmUnit)))));

val TyRec ("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist", 0)])]) = typeof' [] [] singletonList;

val natlistCons =
    Fn("natAndNatlist", Prod([Nat, natlist]),
        Fold(natlist,
             PlusRight(
                 Plus[Unit, Prod([Nat, natlist])],
                 Var ("natAndNatlist", 0)
             )
            )
       );

val Fn("natAndNatlist", Prod [Nat,TyRec ("natlist",Plus [Unit, Prod [Nat,TypVar ("natlist", 0)]])],
     Fold (TyRec ("natlist",Plus [Unit, Prod [Nat,TypVar ("natlist", 0)]]),
        PlusRight
          (Plus ([Unit, Prod [Nat,TyRec ("natlist",Plus [Unit, Prod [Nat,TypVar ("natlist", 0)]])]]),
           Var ("natAndNatlist", 0)))) : Ast.exp =
    parseFile "/home/evan/thon/examples/natlistcons.thon";

val parsedNatlistCons =
    parseFile "/home/evan/thon/examples/natlistcons.thon";
val true = (parsedNatlistCons = natlistCons);

val Arr (Prod ([Nat,TyRec ("natlist",Plus [Unit,Prod [Nat,TypVar ("natlist", 0)]])]),
         TyRec ("natlist",Plus [Unit,Prod [Nat,TypVar ("natlist", 0)]])) : typ =
    typeof' [] [] natlistCons;

val deducedSingleListAppResType = typeof' [] [] (App(natlistCons, Pair(Zero, nilNatList)));
val true = (deducedSingleListAppResType = natlist);

val deducedNatlist = typeof' [] [] nilNatList;
val true = (natlist = deducedNatlist);

val Plus [Unit,Prod ([Nat,TyRec ("natlist",Plus [Unit,Prod [Nat,TypVar ("natlist", 0)]])])] : typ =
    typeof' [] [] (Unfold(nilNatList));

val PlusLeft
    (Plus [Unit,Prod ([Nat,TyRec ("natlist",Plus [Unit,Prod [Nat,TypVar ("natlist", 0)]])])],TmUnit) : exp = eval (Unfold(nilNatList));

val isnil = Fn("x", natlist, Case(Unfold(Var ("x", 0)), ["l", "r"], [Succ Zero, Zero]));
val Nat = typeof' [] [] (App(isnil, nilNatList));
(* isnil nilNatList == 1. *)
val Succ Zero = eval (App(isnil, nilNatList));

(* natlistConsType*)
val natlistConstype = Arr(Prod([Nat, natlist]), natlist);

(* Defines a type of natural number queues. Can wrap in an existential type, also. *)
val natQueueType = Prod [
    (* empty queue *) natlist,
    Prod [
          (* insert *) Arr(Prod[Nat, natlist], natlist),
          (* remove*) Arr(natlist, (Plus[(*None*) Unit, (*Some(Nat, natlist)*)Prod[Nat, natlist]]))
         ]
    ]
;

val Plus[Nat, Nat] = typeof' [] [] (PlusLeft (Plus[Nat, Nat], Zero));
val Plus[Nat, Prod[Nat, Nat]] = typeof' [] [] (PlusLeft (Plus[Nat, Prod([Nat, Nat])], Zero));
val Zero = step (Case(PlusLeft (Plus[Nat, Nat], Zero), ["l", "r"], [Var ("l", 0), Succ(Var ("r", 0))]));
val (Succ Zero) = step (Case(PlusRight (Plus[Nat, Nat], Zero), ["l", "r"], [Var ("l", 0), Succ(Var ("r", 0))]));

(* Seems there are multiple valid typings of this expression. Up *)
(* front, I thought Some(Arr(TypVar ("t", 0), Nat)) is the only correct typing, *)
(* but the chapter on existential types in TAPL suggests otherwise. *)

(* That's why we require an explicit type annotation from the programmer. *)
val Arr(Nat, Nat) = typeof' [] [NONE] (Fn("x", Nat, Zero));
val Arr(TypVar ("t", 0), TypVar ("t", 0)) = abstractOutType "t" Nat (Arr(Nat, Nat));
val All("t", Arr(TypVar ("t", 0), Nat)) = abstractOutType "t" (Arr(Nat, Nat)) (All("t", Arr(TypVar ("t", 0), Nat)));

val e0 = Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof' [] [] e0;

val Impl (Nat,Fn ("x",Nat,Zero),Some ("t",Arr (TypVar ("t",0),TypVar ("t",0)))) =
    parse "impl (some t. t -> t) with nat as \\ x : nat -> Z";

val Impl (Nat,Fn ("x",Nat,Zero),Some ("t",Arr (TypVar ("t",0),TypVar ("t",0)))) =
    run "impl (some t. t -> t) with nat as \\ x : nat -> Z";

val Impl
    (TyRec ("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist",0)])]),
     Fn
       ("l",TyRec ("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist",0)])]),
        Zero),Some ("s",Arr (TypVar ("s",0),TypVar ("s",0)))) : exp =
    parse "impl (some s. s -> s) with (u natlist. (unit || (nat * natlist))) as \\ l : (u natlist. (unit || (nat * natlist))) -> Z";

val Use (Impl (Nat,Fn ("x",Nat,Zero),Some ("t'",Arr (TypVar ("t'",0),TypVar ("t'",0)))),
         "pkg","s", Var ("pkg",0)) : exp =
    parse "use (impl (some t'. t' -> t') with nat as \\ x : nat -> Z) as (pkg, s) in (pkg)";

val Zero = run "use (impl (some t. t -> t) with nat as \\ x : nat -> Z) as (pkg, s) in (pkg)"
           handle ClientTypeCannotEscapeClientScope => Zero;


val e1 = Impl(Nat, Fn("x", Nat, Var ("x", 0)), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof' [] [] e1;
val e2 = Impl(Arr(Nat, Nat), Fn("x", Arr(Nat, Nat), Var ("x", 0)), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof' [] [] e2;
val e4 = Impl(All("t", Nat), Fn("x", All("t", Nat), Zero), Some("t", Arr(TypVar ("t", 0), Nat)));
val Some("t",Arr(TypVar ("t", 0), Nat)) = typeof' [] [] e4

val e5 = Impl(Nat, Fn("x", All("t", Nat), Zero), Some("t", Arr(All ("t", TypVar ("t", 1)), TypVar ("t", 0))));
val Some("t",Arr(All ("t", TypVar ("t", 1)), TypVar ("t", 0))) = typeof' [] [] e5

val t5 = typeof' [] [] (Fn("x", All("t", Nat), Zero));
val (Arr(All ("t", Nat), Nat)) = t5;
val Arr(All ("t", TypVar ("t", 1)), TypVar ("t", 0)) = abstractOutType "t" Nat (Arr(All ("t", Nat), Nat));

val f = Fn("x", Arr(Nat, Nat), Zero);
val g = Fn ("x", Nat,Succ (Var ("x", 0)));
val pkg = Impl(Arr(Nat, Nat), f, Some("t", Arr(TypVar ("t", 0), Nat)));
val Some ("t",Arr(TypVar ("t", 0), Nat)) = typeof' [] [] pkg;

val Some("t",Arr(TypVar ("t", 0), Nat)) = typeof' [] [] (Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), Nat))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof' [] [] (Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))));
val Nat = typeof' [] [] (Impl(Nat, Fn("x", Nat, Zero), Some("t", TypVar ("t", 0)))) handle IllTyped => Nat;

val zeroFnPkg = Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), Nat)));
val zeroFnPkg2 = Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(Nat, TypVar ("t", 0))));

(* Define identity package; can convert Nat to internal repr type and back. *)
val idid = Pair(Fn("x", Nat, Var ("x", 0)), Fn("x", Nat, Var ("x", 0)));
val Prod([Arr(Nat, Nat), Arr(Nat, Nat)]) = typeof' [] [] idid;
val inoutpkg = Impl(Nat, idid, Some("t", Prod([Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat)])));
val Some("t",Prod([Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat)])) = typeof' [] [] inoutpkg;
val Nat = typeof' [] [] (Use(inoutpkg, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));
val true = isval inoutpkg;
(* Dynamics *)
val App
    (ProdRight (Pair (Fn ("x", Nat,Var ("x", 0)),Fn ("x", Nat,Var ("x", 0)))),
     App (ProdLeft (Pair (Fn ("x", Nat,Var ("x", 0)),Fn ("x", Nat,Var ("x", 0)))),Zero))
    = step (Use(inoutpkg, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val Zero = eval (Use(inoutpkg, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val leftandback = Pair(Fn("x", Nat, Pair(Var ("x", 0), Zero)), Fn("x", Prod([Nat, Nat]), ProdLeft (Var ("x", 0))));
val Prod ([Arr (Nat,Prod [Nat, Nat]),Arr (Prod [Nat, Nat],Nat)]) = typeof' [] [] leftandback;
val inoutpkg2 = Impl(Prod([Nat, Nat]), leftandback, Some("t", Prod ([Arr (Nat,TypVar ("t", 0)),Arr (TypVar ("t", 0),Nat)])));
val Some("t",Prod([Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat)])) = typeof' [] [] inoutpkg2;
val Nat = typeof' [] [] (Use(inoutpkg2, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));
val Zero = eval (Use(inoutpkg2, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val double = Fn("x", Nat, Rec(Var ("x", 0), Zero, "prev", Succ (Succ (Var ("x", 0)))));
val Succ (Succ Zero) = eval (App(double, (Succ Zero)));

val All("t", TypVar ("t", 1)) = abstractOutType "t" Nat (All("t", Nat));
val TypVar ("t", 0) = abstractOutType "t" Nat Nat;
val Arr(TypVar ("t", 0), Nat)= abstractOutType "t" (Arr(Nat, Nat)) (Arr(Arr(Nat, Nat), Nat));
val Some("t",Arr(TypVar ("t", 1), Nat)) = abstractOutType "t" (Arr(Nat, Nat)) (Some("t",Arr(Arr(Nat, Nat), Nat)));
val All("t", Arr(TypVar ("t", 1), Nat)) = abstractOutType "t" (Arr(Nat, Nat)) (All("t", Arr(Arr(Nat, Nat), Nat)));
val Some("t",All("t", Arr(TypVar ("t", 2), Nat))) = abstractOutType "t" (Arr(Nat, Nat)) (Some("t",All("t", Arr(Arr(Nat, Nat), Nat))));

val polymorphicIdFn = TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0)));

val Fn("x", Nat, Var ("x", 0)) = step (TypApp(Nat, polymorphicIdFn));
val Fn("x", Arr(Nat, Nat), Var ("x", 0)) = step (TypApp(Arr(Nat, Nat), polymorphicIdFn));
val TypFn ("t", Fn ("x", TypVar ("t", 0), Var ("x", 0))) = step (TypApp(Nat, TypFn("t", polymorphicIdFn)))
val TypApp(Nat, TypFn("t", (Fn ("x", TypVar ("t", 0), Var ("x", 0))))) = step (TypApp(Nat, TypApp(Nat, TypFn("t", polymorphicIdFn))))
val TypFn("t", Fn("x", Arr(Nat, TypVar ("t", 0)), Var ("x", 0))) = step (TypApp(Nat, TypFn("t", TypFn("t", Fn("x", Arr(TypVar ("t", 1), TypVar ("t", 0)), Var ("x", 0))))));
val Fn("x", Nat, Var ("x", 0)) = eval (TypApp(Nat, TypApp(Nat, TypFn("t", polymorphicIdFn))));

val Succ Zero = eval (App(TypApp(Nat, polymorphicIdFn), Succ(Zero)));

val TypFn("t", Zero) = step (TypFn("t", Zero));
val true = isval (Fn("x", Nat, TypFn("t", Zero)));
val (TypFn ("t", Zero)) = step (App(Fn("x", Nat, TypFn("t", Zero)), Zero));

val Nat = substType Nat (TypVar ("t", 0)); (* Tho this isn't actually a well-formed type *)
val Arr(Nat, Nat) = substType (Arr(Nat, Nat)) (TypVar ("t", 0)); (* Tho this isn't actually a well-formed type *)
val false = istype [] (TypVar ("t", 0));
val All("t", Nat) = substType Nat (All("t", TypVar ("t", 1)));
val Some("t",Nat) = substType Nat (Some("t",TypVar ("t", 1)));
val Some("t",Some("t",TypVar ("t", 1))) = substType Nat (Some("t",Some("t",TypVar ("t", 1))));
val true = istype [] (All("t", TypVar ("t", 0)));
val true = istype [] (Some("t",TypVar ("t", 0)));
val All("t", Arr(Nat, (All("t", Nat)))) = substType (All("t", Nat)) (All("t", Arr(Nat, TypVar ("t", 1))));
val All("t", Arr(Nat, (Some("t",Nat)))) = substType (Some("t",Nat)) (All("t", Arr(Nat, TypVar ("t", 1))));

val Nat = typeof' [] [] (TypApp(TypVar ("t", 0), Zero)) handle IllTyped => Nat;
val All("t", Arr(TypVar ("t", 0), Nat)) = typeof' [] [] (TypFn("t", Fn("x", TypVar ("t", 0), Zero)));
val Arr(Arr(Nat, Nat), Nat) = typeof' [] [] (TypApp(Arr(Nat, Nat), (TypFn("t", Fn("x", TypVar ("t", 0), Zero)))));
val Nat = typeof' [] [] (TypApp(Arr(Nat, Nat), (TypFn("t", Fn("x", TypVar ("t", 1), Zero))))) handle IllTypedMsg _ => Nat;


val All("t", Nat) = typeof' [] [] (TypFn("t", Zero)); (* polymorphic zero *)
(* polymorphic id function :) *)
val All("t", Arr(TypVar ("t", 0), TypVar ("t", 0))) =
    typeof' [] [] (TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0))));
val Arr(Nat, All("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))) =
    typeof' [] [] (Fn("x", Nat, TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0)))));
val Arr(Nat, All("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))) =
    typeof' [] [] (Fn("x", Nat, TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0)))));
(* Nested type variables *)
val All("t", All("t", Arr(TypVar ("t", 1),Nat))) =
    typeof' [] [] (TypFn("t", TypFn("t", Fn("x", TypVar ("t", 1), Zero))))
val All("t", All("t", Arr(TypVar ("t", 1), TypVar ("t", 1)))) =
    typeof' [] [] (TypFn("t", TypFn("t", Fn("x", TypVar ("t", 1), Var ("x", 0)))))

val true = istype [] Nat;
val false = istype [] (TypVar ("t", 0)); (* Unbound type variable *)
val false = istype [] (Arr(TypVar ("t", 0), Nat)); (* Unbound type variable *)
val false = istype [] (Arr(Nat, TypVar ("t", 0))); (* Unbound type variable *)
val true = istype [] (All("t", Nat));
val true = istype [] (All("t", TypVar ("t", 0)));
val true = istype [] (All("t", Arr(TypVar ("t", 0), Nat)));
val true = istype [] (All("t", Arr(Nat, TypVar ("t", 0))));
val false = istype [] (All("t", Arr(Nat, TypVar ("t", 1)))); (* Unbound *)
val true = istype [] (All("t", All("t", Arr(Nat, TypVar ("t", 1))))); (* Bound *)

val true = isval Zero;
val true = isval (Succ(Zero));
val true = isval (Fn("x", Nat, Succ(Zero)));
val true = isval (Fn("x", Nat, Zero));
val true = isval (Fn("x", Nat, Succ(Var("x", 0))));
val false = isval (App(Fn("x", Nat, Zero), Zero));

val Zero = subst Zero Zero;
val Succ Zero = subst Zero (Succ Zero);
val (Fn("x", Nat, Var ("x", 0))) = subst (Succ Zero) (Fn("x", Nat, Var ("x", 0)));
val (Var ("y", 0)) = subst (Succ Zero) (Var ("y", 1));
val Fn("x", Nat, Var ("x", 0)) = subst (Succ Zero) (Fn("x", Nat, Var ("x", 0)));
val Fn("x", Nat, (Succ Zero)) = subst (Succ Zero) (Fn("x", Nat, Var("y", 1)));
val App(Fn("x", Nat, Succ Zero), (Succ Zero)) =
    subst (Succ Zero) (App(Fn("x", Nat, Var ("y", 1)), (Var ("x", 0))));

val Fn("y", Nat, Zero) = subst Zero (Fn("y", Nat, Var ("x", 1)));
val Fn("x", Nat, Succ Zero) = subst (Succ Zero) (Fn("x", Nat, Var ("x", 1)));
val Fn("x", Nat, Fn("x", Nat, Succ Zero)) = subst (Succ Zero) (Fn("x", Nat, Fn("x", Nat, Var ("z", 2))));
val Fn("x", Nat, Rec(Zero, Zero, "prev", Succ Zero)) = subst (Succ Zero) (Fn("x", Nat, Rec(Zero, Zero, "prev", Var ("z", 2))));


val Fn("x", Nat, Rec (Zero,
                       Var ("x",0),
                       "prev", Zero)) : exp =
    subst Zero (Fn("x", Nat, Rec(Var ("x", 1),
                                  Var ("x", 0),
                                  "prev", Zero)));
val Fn("x", Nat, Rec(Zero, Var ("x", 1), "prev", Zero)) = subst Zero (Fn("x", Nat, Rec(Var ("x", 1), Var ("x", 2), "prev", Zero)));
val Rec(Zero, Zero, "prev", Zero) = step (App(Fn("x", Nat, Rec(Var ("x", 0), Var ("x", 0), "prev", Zero)), Zero));

val Nat = get [Nat] 0;
val Arr(Nat, Nat) = get [Nat, Arr(Nat, Nat)] 1;
val Nat = get [Nat, Arr(Nat, Nat)] 0;

val Nat = typeof' [] [] Zero;
val Nat = typeof' [] [] (Succ (Zero));

val Nat = typeof' [Nat] [] (Var("x", 0));
val Arr(Nat, Nat) = typeof' [Arr(Nat, Nat)] [] (Var("x", 0));
val Arr(Nat, Nat) = typeof' [Arr(Nat, Nat), Nat] [] (Var("x", 0));
val Nat = typeof' [Arr(Nat, Nat), Nat] [] (Var("x", 1));

val Arr(Nat, Nat) = typeof' [] [] (Fn("x", Nat, Zero));
val Arr(Nat, Nat) = typeof' [] [] (Fn("x", Nat, Succ(Zero)));

val Nat = typeof' [] [] (App(Fn("x", Nat, Zero), Zero));

val Nat = typeof' [] [] (App(Fn("x", Nat, Succ(Zero)), Fn("x", Nat, Zero)))
          handle IllTyped => Nat;

val timesTwo = Rec(Succ(Zero), Zero, "prev", Succ(Succ(Var("prev", 0))));
val Nat = typeof' [] [] timesTwo;

val Arr(Arr(Nat, Nat), Nat) =
    typeof' [] [] (Fn("f", Arr(Nat, Nat), App(Var("f", 0), Zero)));

val Arr(Nat, Nat) = typeof' [] [] (Rec(Zero,
                                       Fn("x", Nat, Succ(Zero)),
                                       "prev", Fn("x", Nat, Succ(Var("x", 0)))));
val Arr(Nat, Nat) = typeof' [] [] (Rec(Succ(Zero),
                                       Fn("x", Nat, Succ(Zero)),
                                       "prev", Fn("x", Nat, Succ(Var("x", 0)))));

val Arr(Nat, Nat) = typeof' [Nat] [] (Rec(Var("dne", 0),
                                       Fn("x", Nat, Succ(Zero)),
                                       "prev", Fn("x", Nat, Succ(Var("x", 0)))));


val Nat = typeof' [] [] (App(Fn("f", Arr(Nat, Nat), App(Var("f", 0), Zero)), Zero)) handle IllTyped => Nat;

(* Ill-formed; first param must be Nat. *)
val Nat = typeof' [] [] (Rec(Fn("x", Nat, Zero),
                               Fn("x", Nat, Succ(Zero)),
                               "prev", Fn("x", Nat, Succ(Var("x", 0))))) handle Bind => Nat;

(* Ill-formed; base case type does not match rec case type. *)
val Nat = (typeof' [] [] (Rec(Zero,
                                Succ(Zero),
                                "prev", Fn("x", Nat, Succ(Zero))))
          handle IllTyped => Nat);

val Arr(Nat, Nat) = typeof' [] [] (Fn("x", (TypVar ("t", 0)), Zero)) handle IllTypedMsg _ => Arr(Nat, Nat);

val Succ(Rec(Zero, Zero, "prev", Succ(Var("prev", 0)))) = step (Rec(Succ(Zero), Zero, "prev", Succ(Var ("prev", 0))));

val Succ(Succ(Rec(Zero, Zero, "prev", Succ(Succ(Var ("prev", 0)))))) =
    step (Rec(Succ(Zero), Zero, "prev", Succ(Succ(Var ("prev", 0)))));

val Zero = step (Rec(Zero, Zero, "prev", Succ(Var ("prev", 0))));
val Succ(Succ(Zero)) = eval (Rec(Succ(Succ(Zero)), Zero, "prev", Succ(Var ("prev", 0))));
val Succ(Succ(Succ(Succ(Zero)))) =
    eval (Rec(Succ(Succ(Zero)), Zero, "prev", Succ(Succ(Var ("prev", 0)))));

val Succ(Succ(Succ(Succ(Zero)))) =
    eval (Rec(App(Fn("x", Nat, Succ(Var ("x", 0))), Succ(Zero)),
              Zero, "prev", Succ(Succ(Var ("prev", 0)))));

val Zero = step Zero;
val Succ(Zero) = step (Succ(Zero));
val Fn("x", Nat, Zero) = step (Fn("x", Nat, Zero));
val Succ Zero = step (App(Fn("x", Nat, Succ(Zero)), Zero));
val Succ Zero = step (App(Fn("x", Nat, Succ(Var("x", 0))), Zero));
val Succ (Succ Zero) = step (App(Fn("x", Nat, Succ(Var("x", 0))), Succ Zero));
val Succ (Succ (Succ Zero)) = step (App(Fn("x", Nat, Succ(Var("x", 0))), Succ (Succ Zero)));
val Succ (Succ (Succ Zero)) = step (App(Fn("x", Nat, Succ(Succ(Var("x", 0)))), Succ Zero));
(* Take in a nat -> nat and apply to zero. Input nat -> nat is Succ *)
val App(Fn("x", Nat, Succ(Var("x", 0))), Zero) = step (App(Fn("x", Arr(Nat, Nat), App(Var("x", 0), Zero)),
                                                  Fn("x", Nat, Succ(Var("x", 0)))));
val Succ Zero = step (App(Fn("x", Nat, Succ(Var("x", 0))), Zero));

val Succ Zero = eval (App(Fn("x", Arr(Nat, Nat), App(Var("x", 0), Zero)),
                          Fn("x", Nat, Succ(Var("x", 0)))));
val Succ (Succ (Succ (Succ Zero))) = eval (Rec(Succ(Succ(Zero)), Zero, "prev", Succ(Succ(Var ("prev", 0)))));

val multByThree = Fn("x", Nat, Rec(Var ("x", 0), Zero, "prev", Succ(Succ(Succ(Var("prev", 0))))));

val Fn ("n",Nat,Rec (Var ("n",0),Var ("n",0),"prev",Succ (Succ Zero))) =
    parse "\\ n : nat -> rec n of Z -> n | prev -> S S Z ";

val App (Fn ("n", Nat,Rec (Var ("n",0),Zero, "prev", Succ (Succ (Var ("prev", 0))))),Succ Zero) : Ast.exp =
    parse "((\\ n : nat -> rec n of Z -> Z | prev -> S S prev ) (S Z))";

val (Succ (Succ Zero)) =
    run "((\\ n : nat -> rec n of Z -> Z | prev -> S S prev ) (S Z))";

val Succ (Succ (Succ (Succ Zero))) : Ast.exp =
    run "((\\ n : nat -> rec n of Z -> Z | prev -> S S prev ) (S S Z))";

val Succ (Succ (Succ Zero)) = eval (App(multByThree, Succ Zero));

val TypFn ("s", Fn("x",TypVar ("s", 0),Var ("x", 0))) : Ast.exp =
    parse "poly s -> \\ x : s -> x";
(* TODO also wrong *)
val TypFn("t", TypFn ("t'",Fn ("x",Arr (TypVar ("t",1),TypVar ("t'",0)),Var ("x",0)))) =
    parse "poly t -> poly t' -> \\ x : (t -> t') -> x";
val TypApp (Nat,TypFn ("s", Fn("x",TypVar ("s", 0),Var ("x",0)))) =
    parse "((poly s -> \\ x : s -> x) (nat))";
val Fn ("x", Nat,Var ("x", 0)) : Ast.exp =
    run "((poly s -> \\ x : s -> x) (nat))";

val TypApp
    (Nat,
     TypFn("t",
       (TypFn ("t'", Fn("f",Arr (TypVar ("t", 1),TypVar ("t'", 0)),Var ("f",0))))))
  : Ast.exp =
    parse "((poly t -> poly t' -> \\ f : (t -> t') -> f) (nat))";
val TypFn ("t'", Fn ("f",Arr (Nat,TypVar ("t'",0)),Var ("f",0))) =
    run "((poly t -> poly t' -> \\ f : (t -> t') -> f) (nat))";

val Pair (Zero,Succ Zero) : Ast.exp =
    parse "(Z, S Z)";

val Pair (Zero,Pair (Succ Zero,Succ (Succ Zero))) : Ast.exp =
    parse "(Z, (S Z, S S Z))";

val Fn ("x", Prod ([Nat,Nat]),Var("x", 0)) : Ast.exp =
    parse "\\ x : (nat * nat) -> x";

val ProdLeft (Pair (Zero,Pair (Succ Zero,Succ (Succ Zero)))) : Ast.exp =
    parse "fst (Z, (S Z, S S Z))";
val ProdRight (Pair (Zero,Pair (Succ Zero,Succ (Succ Zero)))) : Ast.exp =
    parse "snd (Z, (S Z, S S Z))";
val Zero : Ast.exp =
    run "fst (Z, (S Z, S S Z))";
val Succ Zero : Ast.exp =
    run "fst snd (Z, (S Z, S S Z))";

val TypFn ("s",Fn("x",All ("t'", TypVar ("t'",0)),Var ("x",0))) : Ast.exp =
    parse "poly s -> \\ x : (all t'. t') -> x"

val Fn ("pkg", Some ("t'",TypVar ("t'", 0)),Var ("pkg",0)) : Ast.exp =
    parse "\\ pkg : (some t'. t') -> pkg"

val Fn ("natOrFunc", Plus [Nat,Arr (Nat,Nat)],Var ("natOrFunc",0)) : Ast.exp =
    parse "\\ natOrFunc : (nat || nat -> nat) -> natOrFunc"

val Fn ("natOrFunc", Plus [Nat,Arr (Nat,Nat)],Case (Var ("natOrFunc", 0),["l", "r"], [Zero, Succ Zero])) : exp =
    run "\\ natOrFunc : (nat || nat -> nat) -> case natOrFunc of l => Z | r => S Z end"

val App
    (Fn ("natOrFunc", Plus [Nat,Arr (Nat,Nat)], Case (Var ("natOrFunc",0),["l", "r"], [Zero, Succ Zero])),
     PlusLeft (Plus [Nat,Arr (Nat,Nat)],Zero)) : Ast.exp =
    parse "((\\ natOrFunc : (nat || nat -> nat) -> case natOrFunc of l => Z | r => S Z end) (left Z : (nat || nat -> nat)))";

val Zero : exp =
    run "((\\ natOrFunc : (nat || nat -> nat) -> case natOrFunc of l => Z | r => S Z end) (left Z : (nat || nat -> nat)))";

val Succ Zero: exp =
    run "((\\ natOrFunc : (nat || nat -> nat) -> case natOrFunc of l => Z | r => S Z end) (right (\\ x : nat -> Z) : (nat || nat -> nat)))";

val Fn ("natOrFuncOrProd", Plus [Nat,Plus [Arr (Nat,Nat),Prod ([Nat,Nat])]], Var ("natOrFuncOrProd",0)) : Ast.exp =
    parse "\\ natOrFuncOrProd : (nat || ((nat -> nat) || (nat * nat))) -> natOrFuncOrProd"

val Some ("t",Prod ([TypVar ("t", 0),Prod ([Arr (Prod [Nat,TypVar ("t", 0)],TypVar ("t", 0)),Arr (TypVar ("t", 0),Nat)])])) : typ =
    typeof (parseFile "/home/evan/thon/examples/natlist.thon");

val natList = (parseFile "/home/evan/thon/examples/natlist.thon");

val Arr (Plus [Nat,Unit],Arr (Nat,Nat)) : Ast.typ =
    typeof (parseFile "/home/evan/thon/examples/option.thon");

val Fn
    ("x",Plus [Nat,Unit],
     Fn
       ("y",Nat,Case (Var ("x",1),["somex", "none"],[Var ("somex",0),Var ("y",1)])))
  : exp =
    parseFile "/home/evan/thon/examples/option.thon";

val Let ("x",Nat,Zero,Var ("x",0)) : Ast.exp = parse "let x : nat = Z in x";
val Let ("x",Nat,Zero,Let ("y",Nat,Succ Zero,Var ("x",1))) : Ast.exp =
    parse "let x : nat = Z in (let y : nat = S Z in x)";
val Let ("x",Nat,Zero,Let ("y",Nat,Succ Zero,Var ("x",1))) : Ast.exp =
    parse "let x : nat = Z in let y : nat = S Z in x";

val Zero : Ast.exp = run "let x : nat = Z in x";

val Succ Zero : Ast.exp = runFile "/home/evan/thon/examples/nilisempty.thon";

val Succ Zero : Ast.exp = run "ifz Z of Z -> S Z | S prev -> Z";
val Zero : Ast.exp = run "ifz S Z of Z -> S Z | S prev -> prev";

val Succ Zero : Ast.exp = runFile "/home/evan/thon/examples/decr.thon";

val Succ (Succ Zero) : Ast.exp = runFile "/home/evan/thon/examples/add.thon";
val Succ Zero : Ast.exp = runFile "/home/evan/thon/examples/sub.thon";
val Zero : Ast.exp = runFile "/home/evan/thon/examples/eq.thon";

val Succ Zero : Ast.exp = runFile "/home/evan/thon/examples/len.thon";

val Fold
    (TyRec
       ("node",
        Plus [Unit,Prod [Nat,Prod [TypVar ("node",0),TypVar ("node",0)]]]),
     PlusLeft
       (Plus
          [Unit, (*empty base or... *)
           Prod (* a nat and... *)
             [Nat,
              Prod (* a node and... *)
                [TyRec
                   ("node",
                    Plus
                      [Unit,
                       Prod [Nat,Prod [TypVar ("node",0),TypVar ("node",0)]]]),
                 TyRec (* a another node. *)
                   ("node",
                    Plus
                      [Unit,
                       Prod [Nat,Prod [TypVar ("node",0),TypVar ("node",0)]]])]]],
        TmUnit)) : Ast.exp = runFile "/home/evan/thon/examples/emptybst.thon";

val bstType : Ast.typ = typeof (parseFile "/home/evan/thon/examples/singletonbst.thon");

val TyRec
    ("node",Plus [Unit,Prod [Nat,Prod [TypVar ("node",0),TypVar ("node",0)]]])
    : Ast.typ = bstType;

val bstInsertType : Ast.typ = typeof (parseFile "/home/evan/thon/examples/bst.thon");
val Arr(Nat, (Arr(bstType1, bstType2))) = bstInsertType;
val true = (bstType = bstType1);

val true = (bstType = bstType2);

val loop = parse "fix loop : nat in loop";
val true = (loop) = (step loop);
val Nat = typeof loop;
(* 2 is even *)
val Succ Zero = runFile "/home/evan/thon/examples/iseven.thon";;

val bstinsert = parseFile "/home/evan/thon/examples/bst.thon";
val emptybst = parseFile "/home/evan/thon/examples/emptybst.thon";
val zerobst = parseFile "/home/evan/thon/examples/singletonbst.thon";

val appbst = eval (A.App(A.App(bstinsert, A.Zero), emptybst));
val true = (zerobst = appbst);

val Succ (Succ Zero) = runFile "/home/evan/thon/examples/setget.thon";

val TypFn ("t", Zero) = runFile "/home/evan/thon/examples/typnames.thon";

val
  Data
    ("List",["Nil", Cons], [Unit,
     Prod [Nat,Some ("t",Arr (TypVar ("t",0),TypVar ("List",1)))]],Zero)
  : Ast.exp =
    parse "data List = Nil unit | Cons nat * (some t. t -> List) in Z";

val manualDatatype = parseFile "/home/evan/thon/examples/manual-datatype.thon";
val autoDatatype = elaborateDatatypes (parse "data List = Nil unit | Cons nat * List in Z");

val Zero = runFile "/home/evan/thon/examples/auto-natlist.thon";
val Succ (Succ Zero) = runFile "/home/evan/thon/examples/bst-depth.thon";

val Zero = runFile "/home/evan/thon/examples/ternary-tree.thon";
val Zero = runFile "/home/evan/thon/examples/three-summands-to-data.thon";
val Zero = runFile "/home/evan/thon/examples/one-summand-to-data.thon";

val Fn
    ("natOrFuncOrProd",Prod [Nat,Prod [Arr (Nat,Nat),Prod [Nat,Nat]]],
     Var ("natOrFuncOrProd",0)) = runFile "/home/evan/thon/examples/ternary-prod-type.thon";

val Fn
    ("natOrFuncOrProd",Plus [Nat,Plus [Arr (Nat,Nat),Prod [Nat,Nat]]],
     Var ("natOrFuncOrProd",0)) = runFile "/home/evan/thon/examples/ternary-sum-type.thon";

val
  Tuple
      [TypFn ("t",Fn ("x",TypVar ("t",0),Var ("x",0))),
       Fn ("x",Nat,Var ("x",0)),
       TypFn ("t",Fn ("x",TypVar ("t",0),Var ("x",0)))] : exp =
step (A.Tuple [polymorphicIdFn, A.TypApp(Nat, polymorphicIdFn), polymorphicIdFn]);

val
  Data
    ("tree",["nil","two","cons"],
     [Unit,Prod [Nat,Prod [Nat,TypVar ("tree",0)]],
      Prod [Nat,TypVar ("tree",0)]],
     Let
       ("isempty",Arr (TypVar ("tree",0),Nat),
        Fix
          ("isempty",Arr (TypVar ("tree",0),Nat),
           Fn
             ("t",TypVar ("tree",0),
              Case
                (App (Var ("exposetree",2),Var ("t",0)),
                 ["empty","twocase","conscase"],[Succ Zero,Zero,Zero]))),
        App
          (Var ("isempty",0),
           App (Var ("cons",2),Pair (Zero,App (Var ("nil",4),TmUnit))))))
  : exp = parseFile "/home/evan/thon/examples/unary-or-binary-tree.thon";

val Zero = runFile "/home/evan/thon/examples/unary-or-binary-tree.thon";

val simpleNestedDatatypes =
  Data
    ("typ",["Arr"],[TypVar ("typ",0)],
     Data ("exp",["Fn"],[TypVar ("typ",1)],Zero));

val elaborated = elaborateDatatypes simpleNestedDatatypes;

val Nat = substType Nat (TypVar ("typ",0));
val Nat = substType' Nat (TypVar ("typ",1)) 1;
val Zero = subst Zero (Var("x", 0));

(* WRONG WE SHOULD NOT CHANGE THE DBI
 * Only decr dbi if we have actually subst'd something
 *)
val TypVar("typ", 0) = substType Nat (TypVar ("typ",1));
(* WRONG WE SHOULD NOT CHANGE THE DBI
 * We are substituting for depth 1.
 * There is not a depth 1 variable in the dst expression.
 *)
val TypVar("typ", 1) = substType' Nat (TypVar ("typ",2)) 1;
(* WRONG *)
val Var("x", 0) = subst Zero (Var("x", 1));
(* WRONG *)
val Var("x", 1) = subst' Zero (Var("x", 2)) 1;

in
()
end

end (* structure Thon *)
