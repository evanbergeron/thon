(* A system FE interpreter - System F with existential packages *)
structure Thon : sig
                   val parse : string -> Ast.Exp
                   val parseFile : string -> Ast.Exp
                   val typeof : A.Exp -> A.Typ
                   val test : unit -> unit
                   val eval : A.Exp -> A.Exp
                   val run : string -> A.Exp
                   val runFile : string -> A.Exp
                   (* TODO val repl : () -> () *)
                 end =
struct

exception IllTyped
exception IllTypedMsg of string
exception No
exception ClientTypeCannotEscapeClientScope
exception Unimplemented

datatype Idx = int


(* Holds typing assertions we already know. Head of the list
 * represents the type of the variable most recently seen. (The
 * "lowest" scope variable). *)
datatype 'a List = Nil | Cons of 'a * 'a List


fun get ctx i =
    case ctx of
        Nil => raise No
      | Cons (h, t) => if i = 0 then h else get t (i-1)


fun len' acc Nil = acc
  | len' acc (Cons(h, t)) = len' (acc+1) t


fun len ctx = len' 0 ctx


fun istype typeCtx t =
    case t of
        A.Nat => true
      | A.Unit => true
      | A.TypVar i => i < (len typeCtx)
      | A.Arr(d, c) => (istype typeCtx d) andalso (istype typeCtx c)
      | A.Prod(l, r) => (istype typeCtx l) andalso (istype typeCtx r)
      | A.Plus(l, r) => (istype typeCtx l) andalso (istype typeCtx r)
      | A.All t' => istype (Cons(42, typeCtx)) t'
      | A.Some t' => istype (Cons(42, typeCtx)) t'
      | A.TyRec t' => istype (Cons(42, typeCtx)) t'


fun typsubst' src dst bindingDepth =
    case dst
     of A.Nat => A.Nat
      | A.Unit => A.Unit
      | A.TypVar n  => if n = bindingDepth then src else
                     if n > bindingDepth then A.TypVar (n-1) else
                     dst
      | A.Arr(t, t') => A.Arr((typsubst' src t bindingDepth),
                          (typsubst' src t' bindingDepth))
      | A.Prod(l, r) => A.Prod((typsubst' src l bindingDepth),
                           (typsubst' src r bindingDepth))
      | A.Plus(l, r) => A.Plus((typsubst' src l bindingDepth),
                           (typsubst' src r bindingDepth))
      | A.All t => A.All(typsubst' src t (bindingDepth + 1))
      | A.Some t => A.Some(typsubst' src t (bindingDepth + 1))
      | A.TyRec t => A.TyRec(typsubst' src t (bindingDepth + 1))


fun typsubst src dst = typsubst' src dst 0


(* Turns search to A.Var bindingDepth
 *
 * DEVNOTE: assumes the caller will place the result underneath a type
 * variable binding site.
 *
 * Remarkably similar to typSubst - might be able to dedup. This needs
 * to track bindingDepth though and subst in A.TypVar of the appropriate
 * depth.
 *)
fun typAbstractOut' search t bindingDepth =
    if t = search then (A.TypVar bindingDepth) else
    case t
     of A.Nat => A.Nat
      | A.Unit => A.Unit
      | A.TypVar n  => A.TypVar n
      | A.Arr(d, c) => A.Arr((typAbstractOut' search d bindingDepth),
                          (typAbstractOut' search c bindingDepth))
      | A.Prod(l, r) => A.Prod((typAbstractOut' search l bindingDepth),
                           (typAbstractOut' search r bindingDepth))
      | A.Plus(l, r) => A.Plus((typAbstractOut' search l bindingDepth),
                           (typAbstractOut' search r bindingDepth))
      | A.All t' => A.All(typAbstractOut' search t' (bindingDepth+1))
      | A.Some t' => A.Some(typAbstractOut' search t' (bindingDepth+1))
      | A.TyRec t' => A.TyRec(typAbstractOut' search t' (bindingDepth+1))


fun typAbstractOut search t = typAbstractOut' search t 0


(* TODO Figure something better out... *)
fun typtypDecrVarIdxs t =
    case t of
        A.Nat => A.Nat
      | A.Unit => A.Unit
      | A.TypVar i => if (i-1) < 0 then raise ClientTypeCannotEscapeClientScope
                    else A.TypVar (i -1)
      | A.Arr(d, c) => A.Arr(typtypDecrVarIdxs d, typtypDecrVarIdxs c)
      | A.Prod(l, r) => A.Prod(typtypDecrVarIdxs l, typtypDecrVarIdxs r)
      | A.Plus(l, r) => A.Plus(typtypDecrVarIdxs l, typtypDecrVarIdxs r)
      | A.All t' => A.All(typtypDecrVarIdxs t')
      | A.Some t' => A.Some(typtypDecrVarIdxs t')
      | A.TyRec t' => A.TyRec(typtypDecrVarIdxs t')


fun typDecrVarIdxs e =
    case e
     of  A.Zero => A.Zero
       | A.TmUnit => A.TmUnit
       | A.Var (name, i) => if (i-1) < 0 then raise ClientTypeCannotEscapeClientScope
                  else A.Var (name, i - 1)
       | A.Succ e2 => (A.Succ (typDecrVarIdxs e2))
       | A.ProdLeft e => (A.ProdLeft (typDecrVarIdxs e))
       | A.ProdRight e => (A.ProdRight (typDecrVarIdxs e))
       | A.PlusLeft(t, e) => (A.PlusLeft (t, typDecrVarIdxs e))
       | A.PlusRight(t, e) => (A.PlusRight (t, typDecrVarIdxs e))
       | A.Case(c, lname, l, rname, r) =>
         A.Case(typDecrVarIdxs c,
                lname,
                typDecrVarIdxs l,
                rname,
                typDecrVarIdxs r)
       | A.Lam (argName, argType, funcBody) => A.Lam(argName, typtypDecrVarIdxs argType, typDecrVarIdxs funcBody)
       | A.App (f, n) => A.App(typDecrVarIdxs f, typDecrVarIdxs n)
       | A.Tuple (l, r) => A.Tuple(typDecrVarIdxs l, typDecrVarIdxs r)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
         A.Rec(typDecrVarIdxs i,
               typDecrVarIdxs baseCase,
               prevCaseName, typDecrVarIdxs recCase)
       | A.TypAbs e => A.TypAbs (typDecrVarIdxs e)
       | A.TypApp (appType, e) => A.TypApp(typtypDecrVarIdxs appType, typDecrVarIdxs e)
       | A.Impl (reprType, pkgImpl, pkgType) => A.Impl(typtypDecrVarIdxs reprType, typDecrVarIdxs pkgImpl, typtypDecrVarIdxs pkgType)
       | A.Use (pkg, clientName, client) => A.Use(typDecrVarIdxs pkg, clientName, typDecrVarIdxs client)
       | A.Fold(t, e') => A.Fold(typtypDecrVarIdxs t, typDecrVarIdxs e')
       | A.Unfold(e') => A.Unfold(typDecrVarIdxs e')


(* Just substitute the srcType in everywhere you see a A.TypVar bindingDepth *)
fun typSubstInExp' srcType dstExp bindingDepth =
    case dstExp
     of  A.Zero => A.Zero
       | A.Var (name, i) => A.Var (name, i)
       | A.TmUnit => A.TmUnit
       | A.Succ e2 => A.Succ (typSubstInExp' srcType e2 bindingDepth)
       | A.ProdLeft e => A.ProdLeft (typSubstInExp' srcType e bindingDepth)
       | A.ProdRight e => A.ProdRight (typSubstInExp' srcType e bindingDepth)
       | A.PlusLeft (t, e) => A.PlusLeft (t, typSubstInExp' srcType e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, typSubstInExp' srcType e bindingDepth)
       | A.Case(c, lname, l, rname, r) =>
            A.Case(typSubstInExp' srcType c bindingDepth,
                   lname,
                   typSubstInExp' srcType l bindingDepth,
                   rname,
                   typSubstInExp' srcType r bindingDepth)
       | A.Lam (argName, argType, funcBody) =>
            A.Lam(argName, (typsubst' srcType argType bindingDepth),
                typSubstInExp' srcType funcBody bindingDepth)
       | A.App (f, n) =>
            A.App (typSubstInExp' srcType f bindingDepth,
                 typSubstInExp' srcType n bindingDepth)
       | A.Tuple (l, r) =>
            A.Tuple (typSubstInExp' srcType l bindingDepth,
                   typSubstInExp' srcType r bindingDepth)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
            A.Rec(typSubstInExp' srcType i bindingDepth,
                typSubstInExp' srcType baseCase bindingDepth,
                prevCaseName, typSubstInExp' srcType recCase bindingDepth)
       | A.TypAbs e => A.TypAbs(typSubstInExp' srcType e (bindingDepth+1)) (* binds type var *)
       | A.TypApp (appType, e) =>
            A.TypApp(typsubst' srcType appType bindingDepth,
                   typSubstInExp' srcType e bindingDepth)
       | A.Impl(reprType, pkgImpl, pkgType) =>
            A.Impl(typsubst' srcType reprType bindingDepth,
                 typSubstInExp' srcType pkgImpl bindingDepth,
                 typsubst' srcType pkgType bindingDepth)
       | A.Use (pkg, clientName, client) =>
            A.Use(typSubstInExp' srcType pkg bindingDepth,
                  clientName,
                  typSubstInExp' srcType client (bindingDepth+1))
       | A.Fold(t, e') => A.Fold(typsubst' srcType t bindingDepth,
                             typSubstInExp' srcType e' (bindingDepth+1)) (* binds typ var *)
       | A.Unfold(e') => A.Unfold(typSubstInExp' srcType e' bindingDepth)


fun setDeBruijnIndex e varnames typnames =
    let fun find name names =
        (case List.findi (fn (_, n) => n = name) names
         of NONE => NONE
          | SOME (i, _) => SOME i)
    in
    case e
     of  A.Zero => e
       | A.TmUnit => e
       | A.Var (n, i) =>
         (case find n varnames of
             NONE => raise No
           | SOME i => A.Var (n, i))
       | A.Lam(name, argType, funcBody) =>
            A.Lam(name, argType, setDeBruijnIndex funcBody (name::varnames) typnames)
       | A.Succ e2 => A.Succ (setDeBruijnIndex e2 varnames typnames)
       | A.ProdLeft e => A.ProdLeft (setDeBruijnIndex e varnames typnames)
       | A.ProdRight e => A.ProdRight (setDeBruijnIndex e varnames typnames)
       | A.PlusLeft (t, e) => A.PlusLeft (t, setDeBruijnIndex e varnames typnames)
       | A.PlusRight (t, e) => A.PlusRight (t, setDeBruijnIndex e varnames typnames)
       | A.App (f, n) => A.App (setDeBruijnIndex f varnames typnames,
                                setDeBruijnIndex n varnames typnames)
       | A.Tuple (l, r) => A.Tuple (setDeBruijnIndex l varnames typnames,
                                    setDeBruijnIndex r varnames typnames)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
            A.Rec (setDeBruijnIndex i varnames typnames,
                   setDeBruijnIndex baseCase varnames typnames,
                   prevCaseName, (setDeBruijnIndex recCase (prevCaseName::varnames) typnames))
       | A.Case (c, lname, l, rname, r) => A.Case(
            setDeBruijnIndex c varnames typnames,
            lname,
            setDeBruijnIndex l (lname::varnames) typnames,
            rname,
            setDeBruijnIndex r (rname::varnames) typnames)
       | A.Use (pkg, clientName, client) => A.Use (
            setDeBruijnIndex pkg varnames typnames,
            clientName,
            setDeBruijnIndex client (clientName::varnames) typnames) (* TODO need a type name still *)
       (* | A.TypApp (appType, e) => *)
       (* | A.TypAbs e => *)
       | _ => raise Unimplemented (* TODO *)
       (* | A.Fold(A.TyRec(t) (*declared type*), e'(* binds a typ var *)) => *)
       (* | A.Unfold(e') => *)
       (* | A.Impl (reprType, pkgImpl, pkgType) => *)
end




fun typSubstInExp srcType dstExp = typSubstInExp' srcType dstExp 0

fun typeof' ctx typCtx e =
    case e
     of  A.Zero => A.Nat
       | A.TmUnit => A.Unit
       | A.Var (name, i) => get ctx i
       | A.Succ e2 => (typeof' ctx typCtx e2)
       | A.ProdLeft e => let val A.Prod(l, r) = (typeof' ctx typCtx e) in l end
       | A.ProdRight e => let val A.Prod(l, r) = (typeof' ctx typCtx e) in r end
       | A.PlusLeft (t, e) => let val A.Plus(l, r) = t in
                                if l <> typeof' ctx typCtx e then
                                    raise IllTypedMsg "Sum type annotation does not match deduced type"
                                else
                                    A.Plus(l, r)
                            end
       | A.PlusRight (t, e) => let val A.Plus(l, r) = t in
                                if r <> typeof' ctx typCtx e then
                                    raise IllTypedMsg "Sum type annotation does not match deduced type"
                                else
                                    A.Plus(l, r)
                            end
       | A.Case (c, lname, l, rname, r) => let val A.Plus(lt, rt) = typeof' ctx typCtx c
                               (* both bind a term var *)
                               val typeof'LeftBranch = typeof' (Cons(lt, ctx)) typCtx l
                               val typeof'RightBranch= typeof' (Cons(rt, ctx)) typCtx r
                           in
                               if typeof'LeftBranch <> typeof'RightBranch then
                                   raise IllTyped
                               else
                                   typeof'LeftBranch
                               end
       | A.Lam (argName, argType, funcBody) =>
            if not (istype typCtx argType) then raise IllTyped else
            A.Arr (argType, typeof' (Cons(argType, ctx)) typCtx funcBody)
       | A.App (f, n) =>
            let val A.Arr (d, c) = typeof' ctx typCtx f
                val argType = typeof' ctx typCtx n
            in
                if d <> argType then raise IllTyped
                else c
            end
       | A.Tuple (l, r) => A.Prod(typeof' ctx typCtx l, typeof' ctx typCtx r)
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
            let val A.Nat = typeof' ctx typCtx i
                val t = typeof' ctx typCtx baseCase
                val t2 = typeof' (Cons(t, ctx)) typCtx recCase
            in
                if t <> t2 then raise IllTyped else t
            end
       | A.TypAbs e => A.All(typeof' ctx (Cons(42, typCtx)) e)
       | A.TypApp (appType, e) =>
            if not (istype typCtx appType) then raise IllTyped else
            let val A.All(t) = typeof' ctx typCtx e
            in
                typsubst appType t
            end
       | A.Impl (reprType, pkgImpl, pkgType) =>
            if not (istype Nil reprType) then raise IllTyped else
            (* pkgType : [reprType/A.TypVar 0](t') *)
            let val deducedPkgType = typeof' ctx (Cons(42, typCtx)) pkgImpl
            in
                if (typAbstractOut reprType deducedPkgType) <>
                   (typAbstractOut reprType pkgType) then
                    raise IllTyped
                else
                    A.Some(pkgType)
            end
       | A.Use (pkg, clientName, client) =>
            let val A.Some(r) = typeof' ctx typCtx pkg
                (* binds BOTH a A.TypVar and a Exp A.Var *)
                val clientType = typeof' (Cons(r, ctx)) (Cons(42, typCtx)) client
                (* shift indices of free vars and typevars in clientType down by one *)
                val resType = typtypDecrVarIdxs clientType
            in
                if not (istype typCtx resType) then raise IllTyped else
                resType
            end
       | A.Fold(A.TyRec(t) (*declared type*), e'(* binds a typ var *)) =>
            let val deduced = typeof' ctx (Cons(42, typCtx)) e'
                val absDeduced = A.TyRec(typAbstractOut (A.TyRec(t)) (deduced))
                val absT = typAbstractOut (A.TyRec(t)) (A.TyRec(t))
            in
                if absDeduced <> A.TyRec(t) then raise IllTyped
                else A.TyRec(t)
            end
       | A.Unfold(e') =>
            let val A.TyRec(t) = typeof' ctx typCtx e' in
                typsubst (A.TyRec(t)) t
            end

fun typeof e = typeof' Nil Nil e

fun isval e =
    case e of
        A.Zero => true
      | A.TmUnit => true
      | A.Succ(n) => isval n
      | A.Lam(argName, _, _) => true
      | A.Tuple(l, r) => (isval l) andalso (isval r)
      | A.TypAbs _  => true
      | A.Impl(_, pkgImpl, _) => isval pkgImpl
      | A.PlusLeft(_, e') => isval e'
      | A.PlusRight(_, e') => isval e'
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
       | A.PlusLeft (t, e) => A.PlusLeft (t, subst' src e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, subst' src e bindingDepth)
       | A.Case(c, lname, l, rname, r) =>
            A.Case(subst' src c bindingDepth,
                   lname, subst' src l (bindingDepth+1),
                   rname, subst' src r (bindingDepth+1))
       | A.Lam (argName, t, f) => A.Lam(argName, t, (subst' src f (bindingDepth+1)))
       | A.App (f, n) => A.App((subst' src f bindingDepth), (subst' src n bindingDepth))
       | A.Rec (i, baseCase, prevCaseName, recCase) =>
            A.Rec(subst' src i bindingDepth,
                subst' src baseCase bindingDepth,
                prevCaseName, subst' src recCase (bindingDepth+1))
       | A.TypAbs e => A.TypAbs (subst' src e bindingDepth) (* abstracts over types, not exps *)
       | A.TypApp (appType, e) => A.TypApp(appType, subst' src e bindingDepth)
       | A.Impl(reprType, pkgImpl, t) => A.Impl(reprType, subst' src pkgImpl bindingDepth, t)
       | A.Use (pkg, clientName, client) => A.Use(subst' src pkg bindingDepth, clientName, subst' src client (bindingDepth+1))
       | A.Tuple (l, r) => A.Tuple (subst' src l bindingDepth, subst' src r bindingDepth)
       | A.Fold(t, e') => A.Fold(t, (subst' src e' (bindingDepth))) (* binds a typ var *)
       | A.Unfold(e') => A.Unfold(subst' src e' (bindingDepth))


fun subst src dst = subst' src dst 0


fun step e =
    let val _ = typeof' Nil Nil e in
    if isval e then e else
    case e of
        A.Succ(n) => if not (isval n) then A.Succ(step n) else e
      | A.ProdLeft n  => if not (isval n) then A.ProdLeft(step n) else
                   let val A.Tuple(l, r) = n in l end
      | A.ProdRight n  => if not (isval n) then A.ProdRight(step n) else
                    let val A.Tuple(l, r) = n in r end
      | A.Tuple(l, r) => if not (isval l) then A.Tuple(step l, r) else
                       if not (isval r) then A.Tuple(l, step r) else
                       e
      | A.App(f, n) => if not (isval f) then A.App(step f, n)
                     else (if not (isval n) then A.App(f, step n)
                           else let val A.Lam(argName, t, f') = f
                           in
                               (* plug `n` into `f'` *)
                               subst n f'
                           end
                          )
      | A.Var (name, x) => A.Var (name, x)
      | A.Rec (A.Zero, baseCase, prevCaseName, recCase) => baseCase
      | A.Rec (A.Succ(i), baseCase, prevCaseName, recCase) =>
            (* Doesn't evaluate recursive call if not required. *)
            subst (A.Rec(i, baseCase, prevCaseName, recCase)) recCase
      | A.Rec (i, baseCase, prevCaseName, recCase) =>
            if not (isval i) then
                A.Rec(step i, baseCase, prevCaseName, recCase)
            else raise No
      | A.TypAbs e' => raise No (* Already isval *)
      | A.TypApp (t, e') =>
            if not (isval e') then (A.TypApp (t, step e'))
            else
                let val A.TypAbs(e'') = e' in
                    typSubstInExp t e''
                end
      | A.Impl(reprType, pkgImpl, pkgType) =>
            if not (isval pkgImpl) then A.Impl(reprType, step pkgImpl, pkgType) else
            if not (isval e) then raise No else
            e
      | A.Use (pkg, clientName, client) =>
            if not (isval pkg) then A.Use (step pkg, clientName, client) else
            (* Note that there's no abstract type at runtime. *)
           (case pkg of
                A.Impl(reprType', pkgImpl', _) =>
                    subst pkgImpl' (typSubstInExp reprType' client)
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
      | _ => if (isval e) then e else raise No
    end


fun eval e = if isval e then e else eval (step e)

fun run s = let val e = Parse.parse s in if isval e then e else eval (step e) end

fun runFile s = let val e = Parse.parseFile s in if isval e then e else eval (step e) end

fun parse s =
    let val ast : A.Exp = Parse.parse s
    in
        setDeBruijnIndex ast [] []
    end

fun parseFile filename =
    let val ast : A.Exp = Parse.parseFile filename
    in
        setDeBruijnIndex ast [] []
    end


(******* Tests *******)

fun test() = let
open A;
(* Data Natlist = None | Some(Nat, Natlist) *)
val natlist : Typ = TyRec(Plus(Unit, Prod(Nat, TypVar 0)));
val Lam ("natlist", TyRec (Plus (Unit,Prod (Nat,TypVar 0))),Var ("natlist",0)) =
    parse "\\ natlist : (u. (unit |  (nat * 0))) -> natlist";
(* id function on natlists *)
val TypApp
    (TyRec (Plus (Unit,Prod (Nat,TypVar 0))),
     TypAbs (Lam("x",TypVar 0,Var ("x",~1)))) : Ast.Exp =
    parse "((poly \\ x : 0 -> x) (u. (unit | (nat * 0))))";
(* Unfolded Natlist type *)
val nlbody : Typ = TyRec(Plus(Unit, Prod(Nat, natlist)));
val nilNatList =
    Fold(natlist, PlusLeft(Plus(Unit, Prod(Nat, natlist)), TmUnit));

(* TODO don't hardcode dir *)
val parsedNilNatList = parseFile "/home/evan/thon/examples/emptynatlist.thon";

val true = (nilNatList = parsedNilNatList);

val TmUnit : Ast.Exp = parse "unit";

val singletonList =
    Fold(natlist, PlusRight(Plus(Unit, Prod(Nat, natlist)), Tuple(Zero,
    Fold(natlist, PlusLeft(Plus(Unit, Prod(Nat, natlist)), TmUnit)))));

val TyRec (Plus (Unit,Prod (Nat,TypVar 0))) = typeof' Nil Nil singletonList;

val natlistCons =
    Lam("natAndNatlist", Prod(Nat, natlist),
        Fold(natlist,
             PlusRight(
                 Plus(Unit, Prod(Nat, natlist)),
                 Var ("natAndNatlist", 0)
             )
            )
       );

val Lam("natAndNatlist",Prod (Nat,TyRec (Plus (Unit,Prod (Nat,TypVar 0)))),
     Fold (TyRec (Plus (Unit,Prod (Nat,TypVar 0))),
        PlusRight
          (Plus (Unit,Prod (Nat,TyRec (Plus (Unit,Prod (Nat,TypVar 0))))),
           Var ("natAndNatlist", 0)))) : Ast.Exp =
    parseFile "/home/evan/thon/examples/natlistcons.thon";

val parsedNatlistCons =
    parseFile "/home/evan/thon/examples/natlistcons.thon";
val true = (parsedNatlistCons = natlistCons);

val Arr (Prod (Nat,TyRec (Plus (Unit,Prod (Nat,TypVar 0)))),
         TyRec (Plus (Unit,Prod (Nat,TypVar 0)))) : Typ =
    typeof' Nil Nil natlistCons;

val deducedSingleListAppResType = typeof' Nil Nil (App(natlistCons, Tuple(Zero, nilNatList)));
val true = (deducedSingleListAppResType = natlist);

val deducedNatlist = typeof' Nil Nil nilNatList;
val true = (natlist = deducedNatlist);

val Plus (Unit,Prod (Nat,TyRec (Plus (Unit,Prod (Nat,TypVar 0))))) : Typ =
    typeof' Nil Nil (Unfold(nilNatList));

val PlusLeft
    (Plus (Unit,Prod (Nat,TyRec (Plus (Unit,Prod (Nat,TypVar 0))))),TmUnit) : Exp = eval (Unfold(nilNatList));

val isnil = Lam("x", natlist, Case(Unfold(Var ("x", 0)), "l", Succ Zero, "r", Zero));
val Nat = typeof' Nil Nil (App(isnil, nilNatList));
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

val Plus(Nat, Nat) = typeof' Nil Nil (PlusLeft (Plus(Nat, Nat), Zero));
val Plus(Nat, Prod(Nat, Nat)) = typeof' Nil Nil (PlusLeft (Plus(Nat, Prod(Nat, Nat)), Zero));
val Zero = step (Case(PlusLeft (Plus(Nat, Nat), Zero), "l", Var ("l", 0), "r", Succ(Var ("r", 0))));
val (Succ Zero) = step (Case(PlusRight (Plus(Nat, Nat), Zero), "l", Var ("l", 0), "r", Succ(Var ("r", 0))));

(* Seems there are multiple valid typings of this expression. Up *)
(* front, I thought Some(Arr(TypVar 0, Nat)) is the only correct typing, *)
(* but the chapter on existential types in TAPL suggests otherwise. *)

(* That's why we require an explicit type annotation from the programmer. *)
val Arr(Nat, Nat) = typeof' Nil (Cons(42, Nil)) (Lam("x", Nat, Zero));
val Arr(TypVar 0, TypVar 0) = typAbstractOut Nat (Arr(Nat, Nat));
val All(Arr(TypVar 0, Nat)) = typAbstractOut (Arr(Nat, Nat)) (All(Arr(TypVar 0, Nat)));

val e0 = Impl(Nat, Lam("x", Nat, Zero), Arr(TypVar 0, TypVar 0));
val Some(Arr(TypVar 0, TypVar 0)) = typeof' Nil Nil e0;

val Impl (Nat,Lam("x",Nat,Zero),Arr (TypVar 0,TypVar 0)) : Exp =
    parse "impl (0 -> 0) with nat as \\ x : nat -> Z";

val Impl (Nat,Lam ("x", Nat,Zero),Arr (TypVar 0,TypVar 0)) : Exp =
    run "impl (0 -> 0) with nat as \\ x : nat -> Z";

val Impl
    (TyRec (Plus (Unit,Prod (Nat,TypVar 0))),
     Lam("l",TyRec (Plus (Unit,Prod (Nat,TypVar 0))),Zero),
     Arr (TypVar 0,TypVar 0)) : Ast.Exp =
    parse "impl (0 -> 0) with (u. (unit |  (nat * 0))) as \\ l : (u. (unit |  (nat * 0))) -> Z";

val Use (Impl (Nat,Lam("x",Nat,Zero),Arr (TypVar 0,TypVar 0)), "pkg", Var ("x", 0)) =
    parse "use (impl (0 -> 0) with nat as \\ x : nat -> Z) as pkg in (pkg)";

val Zero = run "use (impl (0 -> 0) with nat as \\ nat -> Z) in (0)"
           handle ClientTypeCannotEscapeClientScope => Zero;

val e1 = Impl(Nat, Lam("x", Nat, Var ("x", 0)), Arr(TypVar 0, TypVar 0));
val Some(Arr(TypVar 0, TypVar 0)) = typeof' Nil Nil e1;
val e2 = Impl(Arr(Nat, Nat), Lam("x", Arr(Nat, Nat), Var ("x", 0)), Arr(TypVar 0, TypVar 0));
val Some(Arr(TypVar 0, TypVar 0)) = typeof' Nil Nil e2;
val e4 = Impl(All(Nat), Lam("x", All(Nat), Zero), Arr(TypVar 0, Nat));
val Some(Arr(TypVar 0, Nat)) = typeof' Nil Nil e4

val e5 = Impl(Nat, Lam("x", All(Nat), Zero), Arr(All (TypVar 1), TypVar 0));
val Some(Arr(All (TypVar 1), TypVar 0)) = typeof' Nil Nil e5

val t5 = typeof' Nil Nil (Lam("x", All(Nat), Zero));
val (Arr(All Nat, Nat)) = t5;
val Arr(All (TypVar 1), TypVar 0) = typAbstractOut Nat (Arr(All Nat, Nat));

val f = Lam("x", Arr(Nat, Nat), Zero);
val g = Lam ("x", Nat,Succ (Var ("x", 0)));
val pkg = Impl(Arr(Nat, Nat), f, Arr(TypVar 0, Nat));
val Some (Arr(TypVar 0, Nat)) = typeof' Nil Nil pkg;

val Some(Arr(TypVar 0, Nat)) = typeof' Nil Nil (Impl(Nat, Lam("x", Nat, Zero), Arr(TypVar 0, Nat)));
val Some(Arr(TypVar 0, TypVar 0)) = typeof' Nil Nil (Impl(Nat, Lam("x", Nat, Zero), Arr(TypVar 0, TypVar 0)));
val Nat = typeof' Nil Nil (Impl(Nat, Lam("x", Nat, Zero), TypVar 0)) handle IllTyped => Nat;

val zeroFnPkg = Impl(Nat, Lam("x", Nat, Zero), Arr(TypVar 0, Nat));
val zeroFnPkg2 = Impl(Nat, Lam("x", Nat, Zero), Arr(Nat, TypVar 0));

(* Define identity package; can convert Nat to internal repr type and back. *)
val idid = Tuple(Lam("x", Nat, Var ("x", 0)), Lam("x", Nat, Var ("x", 0)));
val Prod(Arr(Nat, Nat), Arr(Nat, Nat)) = typeof' Nil Nil idid;
val inoutpkg = Impl(Nat, idid, Prod(Arr(Nat, TypVar 0), Arr(TypVar 0, Nat)));
val Some(Prod(Arr(Nat, TypVar 0), Arr(TypVar 0, Nat))) = typeof' Nil Nil inoutpkg;
val Nat = typeof' Nil Nil (Use(inoutpkg, "pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));
val true = isval inoutpkg;
(* Dynamics *)
val App
    (ProdRight (Tuple (Lam ("x", Nat,Var ("x", 0)),Lam ("x", Nat,Var ("x", 0)))),
     App (ProdLeft (Tuple (Lam ("x", Nat,Var ("x", 0)),Lam ("x", Nat,Var ("x", 0)))),Zero))
    = step (Use(inoutpkg, "pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val Zero = eval (Use(inoutpkg, "pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val leftandback = Tuple(Lam("x", Nat, Tuple(Var ("x", 0), Zero)), Lam("x", Prod(Nat, Nat), ProdLeft (Var ("x", 0))));
val Prod (Arr (Nat,Prod (Nat, Nat)),Arr (Prod (Nat, Nat),Nat)) = typeof' Nil Nil leftandback;
val inoutpkg2 = Impl(Prod(Nat, Nat), leftandback, Prod (Arr (Nat,TypVar 0),Arr (TypVar 0,Nat)));
val Some(Prod(Arr(Nat, TypVar 0), Arr(TypVar 0, Nat))) = typeof' Nil Nil inoutpkg2;
val Nat = typeof' Nil Nil (Use(inoutpkg2, "pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));
val Zero = eval (Use(inoutpkg2, "pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val double = Lam("x", Nat, Rec(Var ("x", 0), Zero, "prev", Succ (Succ (Var ("x", 0)))));
val Succ (Succ Zero) = eval (App(double, (Succ Zero)));

val All(TypVar 1) = typAbstractOut Nat (All(Nat));
val TypVar 0 = typAbstractOut Nat Nat;
val Arr(TypVar 0, Nat)= typAbstractOut (Arr(Nat, Nat)) (Arr(Arr(Nat, Nat), Nat));
val Some(Arr(TypVar 1, Nat)) = typAbstractOut (Arr(Nat, Nat)) (Some(Arr(Arr(Nat, Nat), Nat)));
val All(Arr(TypVar 1, Nat)) = typAbstractOut (Arr(Nat, Nat)) (All(Arr(Arr(Nat, Nat), Nat)));
val Some(All(Arr(TypVar 2, Nat))) = typAbstractOut (Arr(Nat, Nat)) (Some(All(Arr(Arr(Nat, Nat), Nat))));

val polymorphicIdFn = TypAbs(Lam("x", TypVar 0, Var ("x", 0)));

val Lam("x", Nat, Var ("x", 0)) = step (TypApp(Nat, polymorphicIdFn));
val Lam("x", Arr(Nat, Nat), Var ("x", 0)) = step (TypApp(Arr(Nat, Nat), polymorphicIdFn));
val TypAbs (Lam ("x", TypVar 0, Var ("x", 0))) = step (TypApp(Nat, TypAbs(polymorphicIdFn)))
val TypApp(Nat, TypAbs((Lam ("x", TypVar 0, Var ("x", 0))))) = step (TypApp(Nat, TypApp(Nat, TypAbs(polymorphicIdFn))))
val TypAbs(Lam("x", Arr(Nat, TypVar 0), Var ("x", 0))) = step (TypApp(Nat, TypAbs(TypAbs(Lam("x", Arr(TypVar 1, TypVar 0), Var ("x", 0))))));
val Lam("x", Nat, Var ("x", 0)) = eval (TypApp(Nat, TypApp(Nat, TypAbs(polymorphicIdFn))));

val Succ Zero = eval (App(TypApp(Nat, polymorphicIdFn), Succ(Zero)));

val TypAbs(Zero) = step (TypAbs(Zero));
val true = isval (Lam("x", Nat, TypAbs(Zero)));
val (TypAbs Zero) = step (App(Lam("x", Nat, TypAbs(Zero)), Zero));

val Nat = typsubst Nat (TypVar 0); (* Tho this isn't actually a well-formed type *)
val Arr(Nat, Nat) = typsubst (Arr(Nat, Nat)) (TypVar 0); (* Tho this isn't actually a well-formed type *)
val false = istype Nil (TypVar 0);
val All(Nat) = typsubst Nat (All(TypVar 1));
val Some(Nat) = typsubst Nat (Some(TypVar 1));
val Some(Some(TypVar 1)) = typsubst Nat (Some(Some(TypVar 1)));
val true = istype Nil (All(TypVar 0));
val true = istype Nil (Some(TypVar 0));
val All(Arr(Nat, (All(Nat)))) = typsubst (All(Nat)) (All(Arr(Nat, TypVar 1)));
val All(Arr(Nat, (Some(Nat)))) = typsubst (Some(Nat)) (All(Arr(Nat, TypVar 1)));

val Nat = typeof' Nil Nil (TypApp(TypVar 0, Zero)) handle IllTyped => Nat;
val All(Arr(TypVar 0, Nat)) = typeof' Nil Nil (TypAbs(Lam("x", TypVar 0, Zero)));
val Arr(Arr(Nat, Nat), Nat) = typeof' Nil Nil (TypApp(Arr(Nat, Nat), (TypAbs(Lam("x", TypVar 0, Zero)))));
val Nat = typeof' Nil Nil (TypApp(Arr(Nat, Nat), (TypAbs(Lam("x", TypVar 1, Zero))))) handle IllTyped => Nat;


val All(Nat) = typeof' Nil Nil (TypAbs(Zero)); (* polymorphic zero *)
(* polymorphic id function :) *)
val All(Arr(TypVar 0, TypVar 0)) =
    typeof' Nil Nil (TypAbs(Lam("x", TypVar 0, Var ("x", 0))));
val Arr(Nat, All(Arr(TypVar 0, TypVar 0))) =
    typeof' Nil Nil (Lam("x", Nat, TypAbs(Lam("x", TypVar 0, Var ("x", 0)))));
val Arr(Nat, All(Arr(TypVar 0, TypVar 0))) =
    typeof' Nil Nil (Lam("x", Nat, TypAbs(Lam("x", TypVar 0, Var ("x", 0)))));
(* Nested type variables *)
val All(All(Arr(TypVar 1,Nat))) =
    typeof' Nil Nil (TypAbs(TypAbs(Lam("x", TypVar 1, Zero))))
val All(All(Arr(TypVar 1, TypVar 1))) =
    typeof' Nil Nil (TypAbs(TypAbs(Lam("x", TypVar 1, Var ("x", 0)))))

val true = istype Nil Nat;
val false = istype Nil (TypVar 0); (* Unbound type variable *)
val false = istype Nil (Arr(TypVar 0, Nat)); (* Unbound type variable *)
val false = istype Nil (Arr(Nat, TypVar 0)); (* Unbound type variable *)
val true = istype Nil (All(Nat));
val true = istype Nil (All(TypVar 0));
val true = istype Nil (All(Arr(TypVar 0, Nat)));
val true = istype Nil (All(Arr(Nat, TypVar 0)));
val false = istype Nil (All(Arr(Nat, TypVar 1))); (* Unbound *)
val true = istype Nil (All(All(Arr(Nat, TypVar 1)))); (* Bound *)

val 0 = len Nil;
val 1 = len (Cons(1, Nil));

val true = isval Zero;
val true = isval (Succ(Zero));
val true = isval (Lam("x", Nat, Succ(Zero)));
val true = isval (Lam("x", Nat, Zero));
val true = isval (Lam("x", Nat, Succ(Var("x", 0))));
val false = isval (App(Lam("x", Nat, Zero), Zero));

val Zero = subst Zero Zero;
val Succ Zero = subst Zero (Succ Zero);
val (Lam("x", Nat, Var ("x", 0))) = subst (Succ Zero) (Lam("x", Nat, Var ("x", 0)));
val (Var ("y", 0)) = subst (Succ Zero) (Var ("y", 1));
val Lam("x", Nat, Var ("x", 0)) = subst (Succ Zero) (Lam("x", Nat, Var ("x", 0)));
val Lam("x", Nat, (Succ Zero)) = subst (Succ Zero) (Lam("x", Nat, Var("y", 1)));
val App(Lam("x", Nat, Succ Zero), (Succ Zero)) =
    subst (Succ Zero) (App(Lam("x", Nat, Var ("y", 1)), (Var ("x", 0))));

val Lam("y", Nat, Zero) = subst Zero (Lam("y", Nat, Var ("x", 1)));
val Lam("x", Nat, Succ Zero) = subst (Succ Zero) (Lam("x", Nat, Var ("x", 1)));
val Lam("x", Nat, Lam("x", Nat, Succ Zero)) = subst (Succ Zero) (Lam("x", Nat, Lam("x", Nat, Var ("z", 2))));
val Lam("x", Nat, Rec(Zero, Zero, "prev", Succ Zero)) = subst (Succ Zero) (Lam("x", Nat, Rec(Zero, Zero, "prev", Var ("z", 2))));

val Lam("x", Nat, Rec(Zero, Var ("y", 0), "prev", Zero)) = subst Zero (Lam("x", Nat, Rec(Var ("x", 1), Var ("x", 0), "prev", Zero)));
val Lam("x", Nat, Rec(Zero, Var ("x", 1), "prev", Zero)) = subst Zero (Lam("x", Nat, Rec(Var ("x", 1), Var ("x", 2), "prev", Zero)));
val Rec(Zero, Zero, "prev", Zero) = step (App(Lam("x", Nat, Rec(Var ("x", 0), Var ("x", 0), "prev", Zero)), Zero));

val Nat = get (Cons(Nat, Nil)) 0;
val Arr(Nat, Nat) = get (Cons(Nat, Cons(Arr(Nat, Nat), Nil))) 1;
val Nat = get (Cons(Nat, Cons(Arr(Nat, Nat), Nil))) 0;

val Nat = typeof' Nil Nil Zero;
val Nat = typeof' Nil Nil (Succ (Zero));

val Nat = typeof' (Cons(Nat, Nil)) Nil (Var("x", 0));
val Arr(Nat, Nat) = typeof' (Cons(Arr(Nat, Nat), Nil)) Nil (Var("x", 0));
val Arr(Nat, Nat) = typeof' (Cons(Arr(Nat, Nat), Cons(Nat, Nil))) Nil (Var("x", 0));
val Nat = typeof' (Cons(Arr(Nat, Nat), Cons(Nat, Nil))) Nil (Var("x", 1));

val Arr(Nat, Nat) = typeof' Nil Nil (Lam("x", Nat, Zero));
val Arr(Nat, Nat) = typeof' Nil Nil (Lam("x", Nat, Succ(Zero)));

val Nat = typeof' Nil Nil (App(Lam("x", Nat, Zero), Zero));

val Nat = typeof' Nil Nil (App(Lam("x", Nat, Succ(Zero)), Lam("x", Nat, Zero)))
          handle IllTyped => Nat;

val timesTwo = Rec(Succ(Zero), Zero, "prev", Succ(Succ(Var("prev", 0))));
val Nat = typeof' Nil Nil timesTwo;

val Arr(Arr(Nat, Nat), Nat) =
    typeof' Nil Nil (Lam("f", Arr(Nat, Nat), App(Var("f", 0), Zero)));

val Arr(Nat, Nat) = typeof' Nil Nil (Rec(Zero,
                                       Lam("x", Nat, Succ(Zero)),
                                       "prev", Lam("x", Nat, Succ(Var("x", 0)))));

val Arr(Nat, Nat) = typeof' Nil Nil (Rec(Succ(Zero),
                                       Lam("x", Nat, Succ(Zero)),
                                       "prev", Lam("x", Nat, Succ(Var("x", 0)))));

val Arr(Nat, Nat) = typeof' (Cons(Nat, Nil)) Nil (Rec(Var("dne", 0),
                                       Lam("x", Nat, Succ(Zero)),
                                       "prev", Lam("x", Nat, Succ(Var("x", 0)))));


val Nat = typeof' Nil Nil (App(Lam("f", Arr(Nat, Nat), App(Var("f", 0), Zero)), Zero)) handle IllTyped => Nat;

(* Ill-formed; first param must be Nat. *)
val Nat = typeof' Nil Nil (Rec(Lam("x", Nat, Zero),
                               Lam("x", Nat, Succ(Zero)),
                               "prev", Lam("x", Nat, Succ(Var("x", 0))))) handle Bind => Nat;

(* Ill-formed; base case type does not match rec case type. *)
val Nat = (typeof' Nil Nil (Rec(Zero,
                                Succ(Zero),
                                "prev", Lam("x", Nat, Succ(Zero))))
          handle IllTyped => Nat);

val Arr(Nat, Nat) = typeof' Nil Nil (Lam("x", (TypVar 0), Zero)) handle IllTyped => Arr(Nat, Nat);

val Succ(Rec(Zero, Zero, "prev", Succ(Var("prev", 0)))) = step (Rec(Succ(Zero), Zero, "prev", Succ(Var ("prev", 0))));

val Succ(Succ(Rec(Zero, Zero, "prev", Succ(Succ(Var ("prev", 0)))))) =
    step (Rec(Succ(Zero), Zero, "prev", Succ(Succ(Var ("prev", 0)))));

val Zero = step (Rec(Zero, Zero, "prev", Succ(Var ("prev", 0))));
val Succ(Succ(Zero)) = eval (Rec(Succ(Succ(Zero)), Zero, "prev", Succ(Var ("prev", 0))));
val Succ(Succ(Succ(Succ(Zero)))) =
    eval (Rec(Succ(Succ(Zero)), Zero, "prev", Succ(Succ(Var ("prev", 0)))));

val Succ(Succ(Succ(Succ(Zero)))) =
    eval (Rec(App(Lam("x", Nat, Succ(Var ("x", 0))), Succ(Zero)),
              Zero, "prev", Succ(Succ(Var ("prev", 0)))));

val Zero = step Zero;
val Succ(Zero) = step (Succ(Zero));
val Lam("x", Nat, Zero) = step (Lam("x", Nat, Zero));
val Succ Zero = step (App(Lam("x", Nat, Succ(Zero)), Zero));
val Succ Zero = step (App(Lam("x", Nat, Succ(Var("x", 0))), Zero));
val Succ (Succ Zero) = step (App(Lam("x", Nat, Succ(Var("x", 0))), Succ Zero));
val Succ (Succ (Succ Zero)) = step (App(Lam("x", Nat, Succ(Var("x", 0))), Succ (Succ Zero)));
val Succ (Succ (Succ Zero)) = step (App(Lam("x", Nat, Succ(Succ(Var("x", 0)))), Succ Zero));

(* Take in a nat -> nat and apply to zero. Input nat -> nat is Succ *)
val App(Lam("x", Nat, Succ(Var("x", 0))), Zero) = step (App(Lam("x", Arr(Nat, Nat), App(Var("x", 0), Zero)),
                                                  Lam("x", Nat, Succ(Var("x", 0)))));
val Succ Zero = step (App(Lam("x", Nat, Succ(Var("x", 0))), Zero));

val Succ Zero = eval (App(Lam("x", Arr(Nat, Nat), App(Var("x", 0), Zero)),
                          Lam("x", Nat, Succ(Var("x", 0)))));
val Succ (Succ (Succ (Succ Zero))) = eval (Rec(Succ(Succ(Zero)), Zero, "prev", Succ(Succ(Var ("prev", 0)))));

val multByThree = Lam("x", Nat, Rec(Var ("x", 0), Zero, "prev", Succ(Succ(Succ(Var("prev", 0))))));

(* TODO this is wrong *)
val Lam ("n", Nat,Rec (Var ("n",~1),Var ("n", 0), "prev", Succ (Succ Zero))) : Ast.Exp =
    parse "\\ n : nat -> rec n ( Z -> 0 | S prev -> S S Z )";

val App (Lam ("n", Nat,Rec (Var ("n",~1),Zero, "prev", Succ (Succ (Var ("n", 0))))),Succ Zero) : Ast.Exp =
    parse "((\\ n : nat -> rec n ( Z -> Z | S prev -> S S 0 )) (S Z))";

val (Succ (Succ Zero)) =
    run "((\\ nat -> rec 0 ( Z -> Z | S -> S S 0 )) (S Z))";

val Succ (Succ (Succ (Succ Zero))) : Ast.Exp =
    run "((\\ nat -> rec 0 ( Z -> Z | S -> S S 0 )) (S S Z))";

val Succ (Succ (Succ Zero)) = eval (App(multByThree, Succ Zero));

val TypAbs (Lam("x",TypVar 0,Var ("x", 0))) : Ast.Exp =
    parse "poly \\ x : 0 -> 0";
(* TODO also wrong *)
val TypAbs (TypAbs (Lam("x",TypVar 1,Var ("x",~1)))) =
    parse "poly poly \\ x : 1 -> x";
val TypApp (Nat,TypAbs (Lam("x",TypVar 0,Var ("x",~1)))) =
    parse "((poly \\ x : 0 -> x) (nat))";
val Lam ("x", Nat,Var ("x", 0)) : Ast.Exp =
    run "((poly \\ x : 0 -> x) (nat))";

val TypApp
    (Nat,
     TypAbs
       (TypAbs (Lam("f",Arr (TypVar 1,TypVar 0),Var ("f",~1)))))
  : Ast.Exp =
    parse "((poly poly \\ f : (1 -> 0) -> f) (nat))";
val TypAbs (Lam ("x", Arr (Nat,TypVar 0),Var ("x", 0))) : Ast.Exp =
    run "((poly poly \\ x : (1 -> 0) -> x) (nat))";

val Tuple (Zero,Succ Zero) : Ast.Exp =
    parse "(Z, S Z)";

val Tuple (Zero,Tuple (Succ Zero,Succ (Succ Zero))) : Ast.Exp =
    parse "(Z, (S Z, S S Z))";

val Lam ("x", Prod (Nat,Nat),Var("x", 0)) : Ast.Exp =
    parse "\\ x : (nat * nat) -> x";

val ProdLeft (Tuple (Zero,Tuple (Succ Zero,Succ (Succ Zero)))) : Ast.Exp =
    parse "fst (Z, (S Z, S S Z))";
val ProdRight (Tuple (Zero,Tuple (Succ Zero,Succ (Succ Zero)))) : Ast.Exp =
    parse "snd (Z, (S Z, S S Z))";
val Zero : Ast.Exp =
    run "fst (Z, (S Z, S S Z))";
val Succ Zero : Ast.Exp =
    run "fst snd (Z, (S Z, S S Z))";

val TypAbs (Lam("x",All (TypVar 0),Var ("x",~1))) : Ast.Exp =
    parse "poly \\ x : (all 0) -> x"

val Lam ("pkg", Some (TypVar 0),Var ("pkg",0)) : Ast.Exp =
    parse "\\ pkg : (some 0) -> pkg"

val Lam ("natOrFunc", Plus (Nat,Arr (Nat,Nat)),Var ("natOrFunc",0)) : Ast.Exp =
    parse "\\ natOrFunc : (nat | nat -> nat) -> natOrFunc"

val Lam ("natOrFunc", Plus (Nat,Arr (Nat,Nat)),Case (Var ("natOrFunc", 0),"l", Zero,"r", Succ Zero)) : Exp =
    run "\\ natOrFunc : (nat | nat -> nat) -> case 0 of l -> Z | r -> S Z"

val App
    (Lam ("natOrFunc", Plus (Nat,Arr (Nat,Nat)), Case (Var ("natOrFunc",~1),"l", Zero,"r", Succ Zero)),
     PlusLeft (Plus (Nat,Arr (Nat,Nat)),Zero)) : Ast.Exp =
    parse "((\\ natOrFunc : (nat | nat -> nat) -> case natOrFunc of l -> Z | r -> S Z) (left Z : (nat | nat -> nat)))";

val Zero : Exp =
    run "((\\ (nat | nat -> nat) -> case 0 of l -> Z | r -> S Z) (left Z : (nat | nat -> nat)))";

val Succ Zero: Exp =
    run "((\\ (nat | nat -> nat) -> case 0 of l -> Z | r -> S Z) (right (\\ nat -> Z) : (nat | nat -> nat)))";

val Lam ("natOrFuncOrProd", Plus (Nat,Plus (Arr (Nat,Nat),Prod (Nat,Nat))), Var ("natOrFuncOrProd",0)) : Ast.Exp =
    parse "\\ natOrFuncOrProd : (nat | ((nat -> nat) | (nat * nat))) -> natOrFuncOrProd"

val Some (Prod (TypVar 0,Arr (Prod (Nat,TypVar 0),TypVar 0))) : Typ =
    typeof (parseFile "/home/evan/thon/examples/natlist.thon");

val natList = (parseFile "/home/evan/thon/examples/natlist.thon");

(* (* TODO *) *)
(* val thisIsABug = *)
val Arr (Plus (Nat,Unit),Arr (Nat,Nat)) : Ast.Typ =
    typeof (parseFile "/home/evan/thon/examples/option.thon");
(*   Lam *)
(*     ("x",Plus (Nat,Unit), *)
(*      Lam *)
(*        ("y",Nat, *)
(*         Case *)
(*           (VarName ("x",~1), *)
(*            App (App (VarName ("some_x",~1),Zero),VarName ("some_x",~1)), *)
(*            VarName ("y",~1)))) : Ast.Exp = *)
(*     parseFile "/home/evan/thon/examples/option.thon"; *)

in
()
end

end (* structure Thon *)
