(* thon - a small functional language *)
structure Thon : sig
                   val parse : string -> Ast.exp
                   val parseFile : string -> Ast.exp
                   val parseFileTop : string -> Ast.top
                   val typeof : A.exp -> A.typ
                   val test : unit -> unit
                   val eval : A.exp -> A.exp
                   val evalTop : A.top -> A.top
                   val isval : A.exp -> bool
                   val step : A.exp -> A.exp
                   val stepCmd : A.cmd -> A.cmd
                   val stepCmd' : A.cmd -> (string, A.exp) HashTable.hash_table-> A.cmd
                   val stepTop : A.top -> A.top
                   val subst : A.exp -> A.exp -> A.exp
                   val run : string -> A.exp
                   val eraseNamesInTyp : A.typ -> A.typ
                   val runFile : string -> A.exp
                   val findParseErrors : string -> unit
                 end =
struct

exception IllTyped
exception IllTypedMsg of string
exception No
exception VarNotInContext
exception UnknownSymbol
exception VarWithNegativeDeBruijinIndex of string * int
exception ClientTypeCannotEscapeClientScope
exception Unimplemented


fun get ctx i =
    case (List.findi (fn (j, _) => j = i) ctx) of
        NONE => (print (Int.toString i); raise VarNotInContext)
      | SOME (j,v) => v


fun istype typeCtx t =
    case t of
        A.Nat => true
      | A.Unit => true
      | A.TypVar (name, i) => i < (length typeCtx)
      | A.Arr(d, c) => (istype typeCtx d) andalso (istype typeCtx c)
      | A.Prod(l, r) => (istype typeCtx l) andalso (istype typeCtx r)
      | A.Plus(l, r) => (istype typeCtx l) andalso (istype typeCtx r)
      | A.All (name, t') => istype (NONE::typeCtx) t'
      | A.Some (name, t') => istype (NONE::typeCtx) t'
      | A.TyRec (name, t') => istype (NONE::typeCtx) t'


fun substType' src dst bindingDepth =
    case dst
     of A.Nat => A.Nat
      | A.Unit => A.Unit
      | A.TypVar (name, n)  => if n = bindingDepth then src else
                     if n > bindingDepth then A.TypVar (name, n-1) else
                     dst
      | A.Arr(t, t') => A.Arr((substType' src t bindingDepth),
                          (substType' src t' bindingDepth))
      | A.Prod(l, r) => A.Prod((substType' src l bindingDepth),
                           (substType' src r bindingDepth))
      | A.Plus(l, r) => A.Plus((substType' src l bindingDepth),
                           (substType' src r bindingDepth))
      | A.All (name, t) => A.All(name, substType' src t (bindingDepth + 1))
      | A.Some (name, t) => A.Some(name, substType' src t (bindingDepth + 1))
      | A.TyRec (name, t) => A.TyRec(name, substType' src t (bindingDepth + 1))


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
      | A.TypVar (name, i) => if (i-1) < 0 then raise ClientTypeCannotEscapeClientScope
                    else A.TypVar (name, i -1)
      | A.Arr(d, c) => A.Arr(decrDeBruijinIndices d, decrDeBruijinIndices c)
      | A.Prod(l, r) => A.Prod(decrDeBruijinIndices l, decrDeBruijinIndices r)
      | A.Plus(l, r) => A.Plus(decrDeBruijinIndices l, decrDeBruijinIndices r)
      | A.All (name, t') => A.All(name, decrDeBruijinIndices t')
      | A.Some (name, t') => A.Some(name, decrDeBruijinIndices t')
      | A.TyRec (name, t') => A.TyRec(name, decrDeBruijinIndices t')


(* Just substitute the srcType in everywhere you see a A.TypVar bindingDepth *)
fun substTypeInExp' srcType dstExp bindingDepth =
    case dstExp
     of  A.Zero => A.Zero
       | A.Var (name, i) => A.Var (name, i)
       | A.TmUnit => A.TmUnit
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
      | A.Dcl(name, e, c) =>
        A.Dcl(name,
              setDeBruijnIndexInExp e varnames typnames,
              (*binds symbol, not a immutable var*)
              setDeBruijnIndexInCmd c varnames typnames (name::mutnames))
      | A.Get name => A.Get name
      | A.Set(name, e) => A.Set(name, setDeBruijnIndexInExp e varnames typnames)

and setDeBruijnIndexInExp e varnames typnames =
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
       | A.Cmd c => A.Cmd (setDeBruijnIndexInCmd c varnames typnames [])
       | _ => raise Unimplemented (* TODO *)
end


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

fun cmdOk ctx typCtx mutCtx c =
    case c of
        A.Ret e => (case typeof' ctx typCtx mutCtx e of A.Nat => true | _ => false)
      | A.Bnd(name, e, c) => (
       (* TODO guess this binds, need to bump debrui index?
          can also toss this binding, i think it's a bit weird *)
          case typeof' ctx typCtx mutCtx e of
              A.TypCmd => (cmdOk (A.Nat::ctx) typCtx mutCtx c)
            | _ => false
      )
      | A.Dcl(name, e, c) => (
          case typeof' ctx typCtx mutCtx e of
              A.Nat => cmdOk ctx typCtx (name::mutCtx) c
            | _ => false
        )
      | A.Get(name) => true
      | A.Set(name, e) => (case typeof' ctx typCtx mutCtx e of A.Nat => true | _ => false)

and typeof' ctx typCtx mutCtx e =
    case e
     of  A.Zero => A.Nat
       | A.TmUnit => A.Unit
       | A.Var (name, i) =>
         if i < 0 then raise VarWithNegativeDeBruijinIndex(name, i) else get ctx i
       | A.Succ e2 => (typeof' ctx typCtx mutCtx e2)
       | A.ProdLeft e => let val A.Prod(l, r) = (typeof' ctx typCtx mutCtx e) in l end
       | A.ProdRight e => let val A.Prod(l, r) = (typeof' ctx typCtx mutCtx e) in r end
       | A.PlusLeft (t, e) =>
         let val A.Plus(l, r) = t in
             if not (typeEq l (typeof' ctx typCtx mutCtx e)) then
                 raise IllTypedMsg "Sum type annotation does not match deduced type"
             else
                 A.Plus(l, r)
         end
       | A.PlusRight (t, e) =>
         let val A.Plus(l, r) = t in
             if not (typeEq r (typeof' ctx typCtx mutCtx e)) then
                 raise IllTypedMsg "Sum type annotation does not match deduced type"
             else
                 A.Plus(l, r)
         end
       | A.Case (c, lname, l, rname, r) =>
         let val A.Plus(lt, rt) = typeof' ctx typCtx mutCtx c
             (* both bind a term var *)
             val typeofLeftBranch = typeof' (lt::ctx) typCtx mutCtx l
             val typeofRightBranch= typeof' (rt::ctx) typCtx mutCtx r
         in
             if not (typeEq (typeofLeftBranch) (typeofRightBranch)) then
                 raise IllTypedMsg "Case statement branches types do not agree"
             else
                 typeofLeftBranch
         end
       | A.Fn (argName, argType, funcBody) =>
         if not (istype typCtx argType) then raise IllTypedMsg "Function arg type is not a type."
         else A.Arr (argType, typeof' (argType::ctx) typCtx mutCtx funcBody)
       | A.Let (varname, vartype, varval, varscope) =>
         if not (istype typCtx vartype) then
             raise IllTypedMsg "Let var type is not a type"
         else if not (typeEq (typeof' ctx typCtx mutCtx varval) vartype) then
             raise IllTypedMsg "Let var type is not equal to deduced var value type."
         else
            typeof' (vartype::ctx) typCtx mutCtx varscope
       | A.App (f, n) =>
         let val A.Arr (d, c) = typeof' ctx typCtx mutCtx f
             val argType = typeof' ctx typCtx mutCtx n
         in
             if not (typeEq d argType) then raise IllTyped
             else c
         end
       | A.Ifz (i, t, prev, e) =>
         let val Nat = typeof' ctx typCtx mutCtx i
             val thenType = typeof' ctx typCtx mutCtx t
             val elseType = typeof' (Nat::ctx) typCtx mutCtx e
         in
             if not (typeEq thenType elseType) then raise IllTyped
             else thenType
         end
       | A.Pair (l, r) => A.Prod(typeof' ctx typCtx mutCtx l, typeof' ctx typCtx mutCtx r)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
         let val A.Nat = typeof' ctx typCtx mutCtx i
             val t = typeof' ctx typCtx mutCtx baseCase
             val t2 = typeof' (t::ctx) typCtx mutCtx recCase
         in
             if not (typeEq t t2) then raise IllTyped else t
         end
       | A.Fix (name, typ, e) => typeof' (typ::ctx) typCtx mutCtx e
       | A.TypFn (name, e) => A.All(name, typeof' ctx (NONE::typCtx) mutCtx e)
       | A.TypApp (appType, e) =>
         if not (istype typCtx appType) then raise IllTyped else
         let val A.All(name, t) = typeof' ctx typCtx mutCtx e
         in
             substType appType t
         end
       | A.Impl (reprType, pkgImpl, pkgType) =>
         if not (istype [] reprType) then raise IllTyped else
         (* pkgType : [reprType/A.TypVar 0](t') *)
         let val deducedPkgType = typeof' ctx (NONE::typCtx) mutCtx pkgImpl
             val A.Some(name, pkgType') = pkgType
         in
             if not (typeEq (abstractOutType name reprType deducedPkgType)
                            (abstractOutType name reprType pkgType')) then
                 raise IllTyped
             else
                 pkgType
         end
       | A.Use (pkg, clientName, typeName, client) =>
         let val A.Some(name, r) = typeof' ctx typCtx mutCtx pkg
             (* binds BOTH a A.TypVar and a exp A.Var *)
             val clientType = typeof' (r::ctx) (NONE::typCtx) mutCtx client
             val resType = decrDeBruijinIndices clientType
         in
             if not (istype typCtx resType) then raise IllTyped else
             resType
         end
       | A.Fold(A.TyRec(name, t) (*declared type*), e'(* binds a typ var *)) =>
         let val deduced = typeof' ctx (NONE::typCtx) mutCtx e'
             val absDeduced = A.TyRec(name, abstractOutType name (A.TyRec(name, t)) (deduced))
             val absT = abstractOutType name (A.TyRec(name, t)) (A.TyRec(name, t))
         in
             if not (typeEq absDeduced (A.TyRec(name, t))) then raise IllTyped
             else A.TyRec(name, t)
         end
       | A.Fold(_ , e'(* binds a typ var *)) =>
         raise IllTypedMsg "Fold type argument must be a recursive type"
       | A.Unfold(e') =>
         let val A.TyRec(name, t) = typeof' ctx typCtx mutCtx e' in
             substType (A.TyRec(name, t)) t
         end
       | A.Cmd c => if not (cmdOk ctx typCtx mutCtx c) then raise IllTyped else A.TypCmd


fun typeof e = typeof' [] [] [] e


fun isval e =
    case e of
        A.Zero => true
      | A.TmUnit => true
      | A.Succ(n) => isval n
      | A.Fn(_, _, _) => true
      | A.Let(_, _, _, _) => false
      | A.Pair(l, r) => (isval l) andalso (isval r)
      | A.TypFn (_, _)  => true
      | A.Impl(_, pkgImpl, _) => isval pkgImpl
      | A.PlusLeft(_, e') => isval e'
      | A.PlusRight(_, e') => isval e'
      | A.Fold(t, e') => isval e'
      | A.Cmd _ => true
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
      | A.Dcl(name, e, c') =>
        A.Dcl(name,
              subst' src e bindingDepth,
              substExpInCmd' src c' bindingDepth)
      | A.Get(name) => c
      | A.Set(name, e) =>
        A.Set(name,
              subst' src e bindingDepth)

and subst' src dst bindingDepth =
    case dst
     of  A.Zero => A.Zero
       | A.TmUnit => A.TmUnit
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

fun substExpInCmd src c = substExpInCmd' src c 0
fun subst src dst = subst' src dst 0

fun stepCmd' c expForSym =
    case c of
        A.Ret e => if not (isval e) then A.Ret (step e) else c
      | A.Bnd(name, e, c') =>
        if not (isval e) then
            A.Bnd(name, step e, c')
        else
            (* ensured by typechecker *)
            let val A.Cmd(c'') = e in
            if not (isfinal c'') then
                A.Bnd(name, A.Cmd(stepCmd' c'' expForSym), c')
            else
            (case c'' of
                A.Ret e => substExpInCmd e c'
              | _ => raise No)
            end
      | A.Dcl(name, e, c') =>
        if not (isval e) then
            A.Dcl(name, step e, c')
        else if not (isfinal c') then
            let val () = HashTable.insert expForSym (name, e)
                val sc' = stepCmd' c' expForSym
                val se = HashTable.remove expForSym name
            in
                A.Dcl(name, se, sc')
            end
        else
            let val () = HashTable.insert expForSym (name, e)
                val A.Ret e' = c'
                (* BUG? the book has MA's isval depending on the expForSym,
                 * but I don't see how/if that's needed. If it's not
                 * needed, believe we can rm the HashTable operations
                 * in this case. *)
                val true = isval e'
                val _ = HashTable.remove expForSym name
            in
                A.Ret e'
            end
      | A.Get name =>
        (case HashTable.find expForSym name of
             SOME e => A.Ret e
           | NONE => raise UnknownSymbol)
      | A.Set(name, e) =>
        if not (isval e) then
            A.Set(name, step e)
        else
            (HashTable.insert expForSym (name, e);
             A.Ret e)


and step e =
    let val _ = typeof e in
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

and stepCmd c =
    let
        val expForSym : (string, A.exp) HashTable.hash_table =
            HashTable.mkTable (HashString.hashString, op=)
                              (42 (*initial size*), Fail "not found");
    in
        stepCmd' c expForSym
    end

fun stepTop p =
    case p of A.E e => A.E (step e) | A.Run c => A.Run (stepCmd c)

fun setDeBruijnIndex ast =
    case ast of
        A.E e => A.E (setDeBruijnIndexInExp e [] [])
      | A.Run c => A.Run (setDeBruijnIndexInCmd c [] [] [])


fun parse s =
    let val A.E ast : A.top = Parse.parse s
    in
        setDeBruijnIndexInExp ast [] []
    end

fun parseFile filename =
    let val ast : A.top = Parse.parseFile filename
    in (case ast of
           A.E e => setDeBruijnIndexInExp e [] []
         | A.Run c => raise Unimplemented)
    end

fun parseFileTop filename =
    let val ast : A.top = Parse.parseFile filename
    in setDeBruijnIndex ast end

fun findParseErrors filename =
    let val _ = parseFile filename
    in
        ()
    end

fun eval e = if isval e then e else eval (step e)

fun evalTop p =
    case p of
        A.E e => if isval e then p else evalTop (A.E (step e))
      | A.Run c => if isfinal c then p else evalTop (A.Run (stepCmd c))

fun run s = let val e = parse s in if isval e then e else eval (step e) end

fun runFile s = let val e = parseFile s in if isval e then e else eval (step e) end



(******* Tests *******)

fun test() = let
open A;
(* Data Natlist = None | Some(Nat, Natlist) *)
val natlist : typ = TyRec("natlist",Plus(Unit, Prod(Nat, TypVar ("natlist", 0))));
val Fn ("natlist", TyRec ("l",Plus (Unit,Prod (Nat,TypVar ("l", 0)))),Var ("natlist",0)) =
    parse "\\ natlist : (u l. (unit |  (nat * l))) -> natlist";

(* id function on natlists *)
val TypApp
    (TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist",0)))),
     TypFn ("s",Fn ("x",TypVar ("s",0),Var ("x",0)))) : Ast.exp =
    parse "((poly s -> \\ x : s -> x) (u natlist. (unit | (nat * natlist))))";
val nilNatList =
    Fold(natlist, PlusLeft(Plus(Unit, Prod(Nat, natlist)), TmUnit));

(* TODO don't hardcode dir *)
val parsedConsNatList = parseFile "/home/evan/thon/examples/emptynatlist.thon";

val true = (nilNatList = parsedConsNatList);

val TmUnit : Ast.exp = parse "unit";

val singletonList =
    Fold(natlist, PlusRight(Plus(Unit, Prod(Nat, natlist)), Pair(Zero,
    Fold(natlist, PlusLeft(Plus(Unit, Prod(Nat, natlist)), TmUnit)))));

val TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0)))) = typeof singletonList;

val natlistCons =
    Fn("natAndNatlist", Prod(Nat, natlist),
        Fold(natlist,
             PlusRight(
                 Plus(Unit, Prod(Nat, natlist)),
                 Var ("natAndNatlist", 0)
             )
            )
       );

val Fn("natAndNatlist",Prod (Nat,TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0))))),
     Fold (TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0)))),
        PlusRight
          (Plus (Unit,Prod (Nat,TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0)))))),
           Var ("natAndNatlist", 0)))) : Ast.exp =
    parseFile "/home/evan/thon/examples/natlistcons.thon";

val parsedNatlistCons =
    parseFile "/home/evan/thon/examples/natlistcons.thon";
val true = (parsedNatlistCons = natlistCons);

val Arr (Prod (Nat,TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0))))),
         TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0))))) : typ =
    typeof natlistCons;

val deducedSingleListAppResType = typeof (App(natlistCons, Pair(Zero, nilNatList)));
val true = (deducedSingleListAppResType = natlist);

val deducedNatlist = typeof nilNatList;
val true = (natlist = deducedNatlist);

val Plus (Unit,Prod (Nat,TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0)))))) : typ =
    typeof (Unfold(nilNatList));

val PlusLeft
    (Plus (Unit,Prod (Nat,TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0)))))),TmUnit) : exp = eval (Unfold(nilNatList));

val isnil = Fn("x", natlist, Case(Unfold(Var ("x", 0)), "l", Succ Zero, "r", Zero));
val Nat = typeof (App(isnil, nilNatList));
(* isnil nilNatList == 1. *)
val Succ Zero = eval (App(isnil, nilNatList));

(* natlistConsType*)
val natlistConstype = Arr(Prod(Nat, natlist), natlist);

(* Defines a type of natural number queues. Can wrap in an existential type, also. *)
val natQueueType = Prod(
    (* empty queue *) natlist,
    Prod((* insert *) (Arr(Prod(Nat, natlist), natlist)),
        (* remove*) Arr(natlist, (Plus((*None*) Unit, (*Some(Nat, natlist)*)Prod(Nat, natlist))))
    )
);

val Plus(Nat, Nat) = typeof (PlusLeft (Plus(Nat, Nat), Zero));
val Plus(Nat, Prod(Nat, Nat)) = typeof (PlusLeft (Plus(Nat, Prod(Nat, Nat)), Zero));
val Zero = step (Case(PlusLeft (Plus(Nat, Nat), Zero), "l", Var ("l", 0), "r", Succ(Var ("r", 0))));
val (Succ Zero) = step (Case(PlusRight (Plus(Nat, Nat), Zero), "l", Var ("l", 0), "r", Succ(Var ("r", 0))));

(* Seems there are multiple valid typings of this expression. Up *)
(* front, I thought Some(Arr(TypVar ("t", 0), Nat)) is the only correct typing, *)
(* but the chapter on existential types in TAPL suggests otherwise. *)

(* That's why we require an explicit type annotation from the programmer. *)
val Arr(Nat, Nat) = typeof' [] [NONE] [] (Fn("x", Nat, Zero));
val Arr(TypVar ("t", 0), TypVar ("t", 0)) = abstractOutType "t" Nat (Arr(Nat, Nat));
val All("t", Arr(TypVar ("t", 0), Nat)) = abstractOutType "t" (Arr(Nat, Nat)) (All("t", Arr(TypVar ("t", 0), Nat)));

val e0 = Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof e0;

val Impl (Nat,Fn ("x",Nat,Zero),Some ("t",Arr (TypVar ("t",0),TypVar ("t",0)))) =
    parse "impl (some t. t -> t) with nat as \\ x : nat -> Z";

val Impl (Nat,Fn ("x",Nat,Zero),Some ("t",Arr (TypVar ("t",0),TypVar ("t",0)))) =
    run "impl (some t. t -> t) with nat as \\ x : nat -> Z";

val Impl
    (TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist",0)))),
     Fn
       ("l",TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist",0)))),
        Zero),Some ("s",Arr (TypVar ("s",0),TypVar ("s",0)))) : exp =
    parse "impl (some s. s -> s) with (u natlist. (unit |  (nat * natlist))) as \\ l : (u natlist. (unit |  (nat * natlist))) -> Z";

val Use (Impl (Nat,Fn ("x",Nat,Zero),Some ("t'",Arr (TypVar ("t'",0),TypVar ("t'",0)))),
         "pkg","s", Var ("pkg",0)) : exp =
    parse "use (impl (some t'. t' -> t') with nat as \\ x : nat -> Z) as (pkg, s) in (pkg)";

val Zero = run "use (impl (some t. t -> t) with nat as \\ x : nat -> Z) as (pkg, s) in (pkg)"
           handle ClientTypeCannotEscapeClientScope => Zero;


val e1 = Impl(Nat, Fn("x", Nat, Var ("x", 0)), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof e1;
val e2 = Impl(Arr(Nat, Nat), Fn("x", Arr(Nat, Nat), Var ("x", 0)), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof e2;
val e4 = Impl(All("t", Nat), Fn("x", All("t", Nat), Zero), Some("t", Arr(TypVar ("t", 0), Nat)));
val Some("t",Arr(TypVar ("t", 0), Nat)) = typeof e4

val e5 = Impl(Nat, Fn("x", All("t", Nat), Zero), Some("t", Arr(All ("t", TypVar ("t", 1)), TypVar ("t", 0))));
val Some("t",Arr(All ("t", TypVar ("t", 1)), TypVar ("t", 0))) = typeof e5

val t5 = typeof (Fn("x", All("t", Nat), Zero));
val (Arr(All ("t", Nat), Nat)) = t5;
val Arr(All ("t", TypVar ("t", 1)), TypVar ("t", 0)) = abstractOutType "t" Nat (Arr(All ("t", Nat), Nat));

val f = Fn("x", Arr(Nat, Nat), Zero);
val g = Fn ("x", Nat,Succ (Var ("x", 0)));
val pkg = Impl(Arr(Nat, Nat), f, Some("t", Arr(TypVar ("t", 0), Nat)));
val Some ("t",Arr(TypVar ("t", 0), Nat)) = typeof pkg;

val Some("t",Arr(TypVar ("t", 0), Nat)) = typeof (Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), Nat))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof (Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))));
val Nat = typeof (Impl(Nat, Fn("x", Nat, Zero), Some("t", TypVar ("t", 0)))) handle IllTyped => Nat;

val zeroFnPkg = Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), Nat)));
val zeroFnPkg2 = Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(Nat, TypVar ("t", 0))));

(* Define identity package; can convert Nat to internal repr type and back. *)
val idid = Pair(Fn("x", Nat, Var ("x", 0)), Fn("x", Nat, Var ("x", 0)));
val Prod(Arr(Nat, Nat), Arr(Nat, Nat)) = typeof idid;
val inoutpkg = Impl(Nat, idid, Some("t", Prod(Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat))));
val Some("t",Prod(Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat))) = typeof inoutpkg;
val Nat = typeof (Use(inoutpkg, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));
val true = isval inoutpkg;
(* Dynamics *)
val App
    (ProdRight (Pair (Fn ("x", Nat,Var ("x", 0)),Fn ("x", Nat,Var ("x", 0)))),
     App (ProdLeft (Pair (Fn ("x", Nat,Var ("x", 0)),Fn ("x", Nat,Var ("x", 0)))),Zero))
    = step (Use(inoutpkg, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val Zero = eval (Use(inoutpkg, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val leftandback = Pair(Fn("x", Nat, Pair(Var ("x", 0), Zero)), Fn("x", Prod(Nat, Nat), ProdLeft (Var ("x", 0))));
val Prod (Arr (Nat,Prod (Nat, Nat)),Arr (Prod (Nat, Nat),Nat)) = typeof leftandback;
val inoutpkg2 = Impl(Prod(Nat, Nat), leftandback, Some("t", Prod (Arr (Nat,TypVar ("t", 0)),Arr (TypVar ("t", 0),Nat))));
val Some("t",Prod(Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat))) = typeof inoutpkg2;
val Nat = typeof (Use(inoutpkg2, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));
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

val Nat = typeof (TypApp(TypVar ("t", 0), Zero)) handle IllTyped => Nat;
val All("t", Arr(TypVar ("t", 0), Nat)) = typeof (TypFn("t", Fn("x", TypVar ("t", 0), Zero)));
val Arr(Arr(Nat, Nat), Nat) = typeof (TypApp(Arr(Nat, Nat), (TypFn("t", Fn("x", TypVar ("t", 0), Zero)))));
val Nat = typeof (TypApp(Arr(Nat, Nat), (TypFn("t", Fn("x", TypVar ("t", 1), Zero))))) handle IllTypedMsg _ => Nat;


val All("t", Nat) = typeof (TypFn("t", Zero)); (* polymorphic zero *)
(* polymorphic id function :) *)
val All("t", Arr(TypVar ("t", 0), TypVar ("t", 0))) =
    typeof (TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0))));
val Arr(Nat, All("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))) =
    typeof (Fn("x", Nat, TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0)))));
val Arr(Nat, All("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))) =
    typeof (Fn("x", Nat, TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0)))));
(* Nested type variables *)
val All("t", All("t", Arr(TypVar ("t", 1),Nat))) =
    typeof (TypFn("t", TypFn("t", Fn("x", TypVar ("t", 1), Zero))))
val All("t", All("t", Arr(TypVar ("t", 1), TypVar ("t", 1)))) =
    typeof (TypFn("t", TypFn("t", Fn("x", TypVar ("t", 1), Var ("x", 0)))))

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

val Nat = typeof Zero;
val Nat = typeof (Succ (Zero));

val Nat = typeof' [Nat] [] [] (Var("x", 0));
val Arr(Nat, Nat) = typeof' [Arr(Nat, Nat)] [] [] (Var("x", 0));
val Arr(Nat, Nat) = typeof' [Arr(Nat, Nat), Nat] [] [] (Var("x", 0));
val Nat = typeof' [Arr(Nat, Nat), Nat] [] [] (Var("x", 1));

val Arr(Nat, Nat) = typeof (Fn("x", Nat, Zero));
val Arr(Nat, Nat) = typeof (Fn("x", Nat, Succ(Zero)));

val Nat = typeof (App(Fn("x", Nat, Zero), Zero));

val Nat = typeof (App(Fn("x", Nat, Succ(Zero)), Fn("x", Nat, Zero)))
          handle IllTyped => Nat;

val timesTwo = Rec(Succ(Zero), Zero, "prev", Succ(Succ(Var("prev", 0))));
val Nat = typeof timesTwo;

val Arr(Arr(Nat, Nat), Nat) =
    typeof (Fn("f", Arr(Nat, Nat), App(Var("f", 0), Zero)));

val Arr(Nat, Nat) = typeof (Rec(Zero,
                                       Fn("x", Nat, Succ(Zero)),
                                       "prev", Fn("x", Nat, Succ(Var("x", 0)))));
val Arr(Nat, Nat) = typeof (Rec(Succ(Zero),
                                       Fn("x", Nat, Succ(Zero)),
                                       "prev", Fn("x", Nat, Succ(Var("x", 0)))));

val Arr(Nat, Nat) = typeof' [Nat] [] [] (Rec(Var("dne", 0),
                                       Fn("x", Nat, Succ(Zero)),
                                       "prev", Fn("x", Nat, Succ(Var("x", 0)))));


val Nat = typeof (App(Fn("f", Arr(Nat, Nat), App(Var("f", 0), Zero)), Zero)) handle IllTyped => Nat;

(* Ill-formed; first param must be Nat. *)
val Nat = typeof (Rec(Fn("x", Nat, Zero),
                               Fn("x", Nat, Succ(Zero)),
                               "prev", Fn("x", Nat, Succ(Var("x", 0))))) handle Bind => Nat;

(* Ill-formed; base case type does not match rec case type. *)
val Nat = (typeof (Rec(Zero,
                                Succ(Zero),
                                "prev", Fn("x", Nat, Succ(Zero))))
          handle IllTyped => Nat);

val Arr(Nat, Nat) = typeof (Fn("x", (TypVar ("t", 0)), Zero)) handle IllTypedMsg _ => Arr(Nat, Nat);

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

val Fn ("x", Prod (Nat,Nat),Var("x", 0)) : Ast.exp =
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

val Fn ("natOrFunc", Plus (Nat,Arr (Nat,Nat)),Var ("natOrFunc",0)) : Ast.exp =
    parse "\\ natOrFunc : (nat | nat -> nat) -> natOrFunc"

val Fn ("natOrFunc", Plus (Nat,Arr (Nat,Nat)),Case (Var ("natOrFunc", 0),"l", Zero,"r", Succ Zero)) : exp =
    run "\\ natOrFunc : (nat | nat -> nat) -> case natOrFunc of l -> Z | r -> S Z"

val App
    (Fn ("natOrFunc", Plus (Nat,Arr (Nat,Nat)), Case (Var ("natOrFunc",0),"l", Zero,"r", Succ Zero)),
     PlusLeft (Plus (Nat,Arr (Nat,Nat)),Zero)) : Ast.exp =
    parse "((\\ natOrFunc : (nat | nat -> nat) -> case natOrFunc of l -> Z | r -> S Z) (left Z : (nat | nat -> nat)))";

val Zero : exp =
    run "((\\ natOrFunc : (nat | nat -> nat) -> case natOrFunc of l -> Z | r -> S Z) (left Z : (nat | nat -> nat)))";

val Succ Zero: exp =
    run "((\\ natOrFunc : (nat | nat -> nat) -> case natOrFunc of l -> Z | r -> S Z) (right (\\ x : nat -> Z) : (nat | nat -> nat)))";

val Fn ("natOrFuncOrProd", Plus (Nat,Plus (Arr (Nat,Nat),Prod (Nat,Nat))), Var ("natOrFuncOrProd",0)) : Ast.exp =
    parse "\\ natOrFuncOrProd : (nat | ((nat -> nat) | (nat * nat))) -> natOrFuncOrProd"

val Some ("t",Prod (TypVar ("t", 0),Prod (Arr (Prod (Nat,TypVar ("t", 0)),TypVar ("t", 0)),Arr (TypVar ("t", 0),Nat)))) : typ =
    typeof (parseFile "/home/evan/thon/examples/natlist.thon");

val natList = (parseFile "/home/evan/thon/examples/natlist.thon");

val Arr (Plus (Nat,Unit),Arr (Nat,Nat)) : Ast.typ =
    typeof (parseFile "/home/evan/thon/examples/option.thon");

val Fn
    ("x",Plus (Nat,Unit),
     Fn
       ("y",Nat,Case (Var ("x",1),"somex",Var ("somex",0),"none",Var ("y",1))))
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
        Plus (Unit,Prod (Nat,Prod (TypVar ("node",0),TypVar ("node",0))))),
     PlusLeft
       (Plus
          (Unit, (*empty base or... *)
           Prod (* a nat and... *)
             (Nat,
              Prod (* a node and... *)
                (TyRec
                   ("node",
                    Plus
                      (Unit,
                       Prod (Nat,Prod (TypVar ("node",0),TypVar ("node",0))))),
                 TyRec (* a another node. *)
                   ("node",
                    Plus
                      (Unit,
                       Prod (Nat,Prod (TypVar ("node",0),TypVar ("node",0)))))))),
        TmUnit)) : Ast.exp = runFile "/home/evan/thon/examples/emptybst.thon";

val bstType : Ast.typ = typeof (parseFile "/home/evan/thon/examples/singletonbst.thon");

val TyRec
    ("node",Plus (Unit,Prod (Nat,Prod (TypVar ("node",0),TypVar ("node",0)))))
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

val cmd0 : cmd = Bnd ("x",Cmd (Ret Zero),Ret (Var ("x",0)));
val Ret Zero = stepCmd cmd0;

val cmd1 : cmd = Bnd ("x",Cmd (Get "sym"),Ret (Var ("x",0)));
val syms : (string, A.exp) HashTable.hash_table =
    HashTable.mkTable (HashString.hashString, op=)
    (42 (*initial size*), Fail "not found");

val () = HashTable.insert syms ("sym", Succ Zero);
val Bnd ("x",Cmd (Ret (Succ Zero)),Ret (Var ("x",0))) : cmd = stepCmd' cmd1 syms;

val cmd2 : cmd = Bnd ("x",Cmd (Get "dne"),Ret (Var ("x",0)));
val Ret Zero = stepCmd' cmd2 syms handle UnknownSymbol => Ret Zero;

(* Set turns into Ret and writes its corresponding symbol *)
val cmd3 : cmd =
    Bnd ("x",Cmd (Set("sym", (Succ (Succ Zero)))),Ret (Var ("x",0)));
val Bnd ("x",Cmd (Ret (Succ (Succ Zero))),Ret (Var ("x",0))) : cmd = stepCmd' cmd3 syms;
val SOME(Succ (Succ Zero)) = HashTable.find syms "sym";

val Dcl ("foo",Succ Zero,Ret (Succ Zero)) : cmd =
    stepCmd (Dcl ("foo", Zero, Set("foo", Succ Zero)))

val Ret (Succ Zero) : cmd =
    stepCmd (Dcl ("foo",Succ Zero,Ret (Succ Zero)))

in
()
end

end (* structure Thon *)
