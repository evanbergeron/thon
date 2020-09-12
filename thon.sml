(* A system FE interpreter - System F with existential packages *)
structure Thon : sig
                   val parse : string -> Ast.Exp
                   val test : unit -> unit
                   val eval : A.Exp -> A.Exp
                   val run : string -> A.Exp
                   val runFile : string -> A.Exp
                 end =
struct

exception IllTyped
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
       | A.Var i => if (i-1) < 0 then raise ClientTypeCannotEscapeClientScope
                  else A.Var (i - 1)
       | A.Succ e2 => (A.Succ (typDecrVarIdxs e2))
       | A.ProdLeft e => (A.ProdLeft (typDecrVarIdxs e))
       | A.ProdRight e => (A.ProdRight (typDecrVarIdxs e))
       | A.PlusLeft(t, e) => (A.PlusLeft (t, typDecrVarIdxs e))
       | A.PlusRight(t, e) => (A.PlusRight (t, typDecrVarIdxs e))
       | A.Case(c, l, r) => (A.Case(typDecrVarIdxs c, typDecrVarIdxs l, typDecrVarIdxs r))
       | A.Lam (argType, funcBody) => A.Lam(typtypDecrVarIdxs argType, typDecrVarIdxs funcBody)
       | A.App (f, n) => A.App(typDecrVarIdxs f, typDecrVarIdxs n)
       | A.Tuple (l, r) => A.Tuple(typDecrVarIdxs l, typDecrVarIdxs r)
       | A.Rec (i, baseCase, recCase) =>
            A.Rec(typDecrVarIdxs i, typDecrVarIdxs baseCase, typDecrVarIdxs recCase)
       | A.TypAbs e => A.TypAbs (typDecrVarIdxs e)
       | A.TypApp (appType, e) => A.TypApp(typtypDecrVarIdxs appType, typDecrVarIdxs e)
       | A.Pack (reprType, pkgImpl, pkgType) => A.Pack(typtypDecrVarIdxs reprType, typDecrVarIdxs pkgImpl, typtypDecrVarIdxs pkgType)
       | A.Open (pkg, client) => A.Open(typDecrVarIdxs pkg, typDecrVarIdxs client)
       | A.Fold(t, e') => A.Fold(typtypDecrVarIdxs t, typDecrVarIdxs e')
       | A.Unfold(e') => A.Unfold(typDecrVarIdxs e')


(* Just substitute the srcType in everywhere you see a A.TypVar bindingDepth *)
fun typSubstInExp' srcType dstExp bindingDepth =
    case dstExp
     of  A.Zero => A.Zero
       | A.Var i => A.Var i
       | A.TmUnit => A.TmUnit
       | A.Succ e2 => A.Succ (typSubstInExp' srcType e2 bindingDepth)
       | A.ProdLeft e => A.ProdLeft (typSubstInExp' srcType e bindingDepth)
       | A.ProdRight e => A.ProdRight (typSubstInExp' srcType e bindingDepth)
       | A.PlusLeft (t, e) => A.PlusLeft (t, typSubstInExp' srcType e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, typSubstInExp' srcType e bindingDepth)
       | A.Case(c, l, r) => A.Case(typSubstInExp' srcType c bindingDepth,
                               typSubstInExp' srcType l bindingDepth,
                               typSubstInExp' srcType r bindingDepth)
       | A.Lam (argType, funcBody) =>
            A.Lam((typsubst' srcType argType bindingDepth),
                typSubstInExp' srcType funcBody bindingDepth)
       | A.App (f, n) =>
            A.App (typSubstInExp' srcType f bindingDepth,
                 typSubstInExp' srcType n bindingDepth)
       | A.Tuple (l, r) =>
            A.Tuple (typSubstInExp' srcType l bindingDepth,
                   typSubstInExp' srcType r bindingDepth)
       | A.Rec (i, baseCase, recCase) =>
            A.Rec(typSubstInExp' srcType i bindingDepth,
                typSubstInExp' srcType baseCase bindingDepth,
                typSubstInExp' srcType recCase bindingDepth)
       | A.TypAbs e => A.TypAbs(typSubstInExp' srcType e (bindingDepth+1)) (* binds type var *)
       | A.TypApp (appType, e) =>
            A.TypApp(typsubst' srcType appType bindingDepth,
                   typSubstInExp' srcType e bindingDepth)
       | A.Pack(reprType, pkgImpl, pkgType) =>
            A.Pack(typsubst' srcType reprType bindingDepth,
                 typSubstInExp' srcType pkgImpl bindingDepth,
                 typsubst' srcType pkgType bindingDepth)
       | A.Open (pkg, client) =>
            A.Open(typSubstInExp' srcType pkg bindingDepth,
                 typSubstInExp' srcType client (bindingDepth+1))
       | A.Fold(t, e') => A.Fold(typsubst' srcType t bindingDepth,
                             typSubstInExp' srcType e' (bindingDepth+1)) (* binds typ var *)
       | A.Unfold(e') => A.Unfold(typSubstInExp' srcType e' bindingDepth)


fun typSubstInExp srcType dstExp = typSubstInExp' srcType dstExp 0


fun typeof ctx typCtx e =
    case e
     of  A.Zero => A.Nat
       | A.TmUnit => A.Unit
       | A.Var i => get ctx i
       | A.Succ e2 => (typeof ctx typCtx e2)
       | A.ProdLeft e => let val A.Prod(l, r) = (typeof ctx typCtx e) in l end
       | A.ProdRight e => let val A.Prod(l, r) = (typeof ctx typCtx e) in r end
       | A.PlusLeft (t, e) => let val A.Plus(l, r) = t in
                                if l <> typeof ctx typCtx e then
                                    raise IllTyped
                                else
                                    A.Plus(l, r)
                            end
       | A.PlusRight (t, e) => let val A.Plus(l, r) = t in
                                if r <> typeof ctx typCtx e then
                                    raise IllTyped
                                else
                                    A.Plus(l, r)
                            end
       | A.Case (c, l, r) => let val A.Plus(lt, rt) = typeof ctx typCtx c
                               (* both bind a term var *)
                               val typeOfLeftBranch = typeof (Cons(lt, ctx)) typCtx l
                               val typeOfRightBranch= typeof (Cons(rt, ctx)) typCtx r
                           in
                               if typeOfLeftBranch <> typeOfRightBranch then
                                   raise IllTyped
                               else
                                   typeOfLeftBranch
                               end
       | A.Lam (argType, funcBody) =>
            if not (istype typCtx argType) then raise IllTyped else
            A.Arr (argType, typeof (Cons(argType, ctx)) typCtx funcBody)
       | A.App (f, n) =>
            let val A.Arr (d, c) = typeof ctx typCtx f
                val argType = typeof ctx typCtx n
            in
                if d <> argType then raise IllTyped
                else c
            end
       | A.Tuple (l, r) => A.Prod(typeof ctx typCtx l, typeof ctx typCtx r)
       | A.Rec (i, baseCase, recCase) =>
            let val A.Nat = typeof ctx typCtx i
                val t = typeof ctx typCtx baseCase
                val t2 = typeof (Cons(t, ctx)) typCtx recCase
            in
                if t <> t2 then raise IllTyped else t
            end
       | A.TypAbs e => A.All(typeof ctx (Cons(42, typCtx)) e)
       | A.TypApp (appType, e) =>
            if not (istype typCtx appType) then raise IllTyped else
            let val A.All(t) = typeof ctx typCtx e
            in
                typsubst appType t
            end
       | A.Pack (reprType, pkgImpl, pkgType) =>
            if not (istype Nil reprType) then raise IllTyped else
            (* pkgType : [reprType/A.TypVar 0](t') *)
            let val deducedPkgType = typeof ctx (Cons(42, typCtx)) pkgImpl
            in
                if (typAbstractOut reprType deducedPkgType) <>
                   (typAbstractOut reprType pkgType) then
                    raise IllTyped
                else
                    A.Some(pkgType)
            end
       | A.Open (pkg, client) =>
            let val A.Some(r) = typeof ctx typCtx pkg
                (* binds BOTH a A.TypVar and a Exp A.Var *)
                val clientType = typeof (Cons(r, ctx)) (Cons(42, typCtx)) client
                (* shift indices of free vars and typevars in clientType down by one *)
                val resType = typtypDecrVarIdxs clientType
            in
                if not (istype typCtx resType) then raise IllTyped else
                resType
            end
       | A.Fold(A.TyRec(t) (*declared type*), e'(* binds a typ var *)) =>
            let val deduced = typeof ctx (Cons(42, typCtx)) e'
                val absDeduced = A.TyRec(typAbstractOut (A.TyRec(t)) (deduced))
                val absT = typAbstractOut (A.TyRec(t)) (A.TyRec(t))
            in
                if absDeduced <> A.TyRec(t) then raise IllTyped
                else A.TyRec(t)
            end
       | A.Unfold(e') =>
            let val A.TyRec(t) = typeof ctx typCtx e' in
                typsubst (A.TyRec(t)) t
            end

fun isval e =
    case e of
        A.Zero => true
      | A.TmUnit => true
      | A.Succ(n) => isval n
      | A.Lam(_, _) => true
      | A.Tuple(l, r) => (isval l) andalso (isval r)
      | A.TypAbs _  => true
      | A.Pack(_, pkgImpl, _) => isval pkgImpl
      | A.PlusLeft(_, e') => isval e'
      | A.PlusRight(_, e') => isval e'
      | A.Fold(t, e') => isval e'
      | _ => false


fun subst' src dst bindingDepth =
    case dst
     of  A.Zero => A.Zero
       | A.TmUnit => A.TmUnit
       | A.Var n  => if n = bindingDepth then src else
                   if n > bindingDepth then A.Var(n-1) else
                   A.Var(n)
       | A.Succ e2 => A.Succ (subst' src e2 bindingDepth)
       | A.ProdLeft e => A.ProdLeft (subst' src e bindingDepth)
       | A.ProdRight e => A.ProdRight (subst' src e bindingDepth)
       | A.PlusLeft (t, e) => A.PlusLeft (t, subst' src e bindingDepth)
       | A.PlusRight (t, e) => A.PlusRight (t, subst' src e bindingDepth)
       | A.Case(c, l, r) => A.Case(subst' src c bindingDepth,
                               subst' src l (bindingDepth+1),
                               subst' src r (bindingDepth+1))
       | A.Lam (t, f) => A.Lam(t, (subst' src f (bindingDepth+1)))
       | A.App (f, n) => A.App((subst' src f bindingDepth), (subst' src n bindingDepth))
       | A.Rec (i, baseCase, recCase) =>
            A.Rec(subst' src i bindingDepth,
                subst' src baseCase bindingDepth,
                subst' src recCase (bindingDepth+1))
       | A.TypAbs e => A.TypAbs (subst' src e bindingDepth) (* abstracts over types, not exps *)
       | A.TypApp (appType, e) => A.TypApp(appType, subst' src e bindingDepth)
       | A.Pack(reprType, pkgImpl, t) => A.Pack(reprType, subst' src pkgImpl bindingDepth, t)
       | A.Open (pkg, client) => A.Open(subst' src pkg bindingDepth, subst' src client (bindingDepth+1))
       | A.Tuple (l, r) => A.Tuple (subst' src l bindingDepth, subst' src r bindingDepth)
       | A.Fold(t, e') => A.Fold(t, (subst' src e' (bindingDepth))) (* binds a typ var *)
       | A.Unfold(e') => A.Unfold(subst' src e' (bindingDepth))


fun subst src dst = subst' src dst 0


fun step e =
    let val _ = typeof Nil Nil e in
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
                           else let val A.Lam(t, f') = f
                           in
                               (* plug `n` into `f'` *)
                               subst n f'
                           end
                          )
      | A.Var x => A.Var x
      | A.Rec (A.Zero, baseCase, recCase) => baseCase
      | A.Rec (A.Succ(i), baseCase, recCase) =>
            (* Doesn't evaluate recursive call if not required. *)
            subst (A.Rec(i, baseCase, recCase)) recCase
      | A.Rec (i, baseCase, recCase) =>
            if not (isval i) then
                A.Rec(step i, baseCase, recCase)
            else raise No
      | A.TypAbs e' => raise No (* Already isval *)
      | A.TypApp (t, e') =>
            if not (isval e') then (A.TypApp (t, step e'))
            else
                let val A.TypAbs(e'') = e' in
                    typSubstInExp t e''
                end
      | A.Pack(reprType, pkgImpl, pkgType) =>
            if not (isval pkgImpl) then A.Pack(reprType, step pkgImpl, pkgType) else
            if not (isval e) then raise No else
            e
      | A.Open (pkg, client) =>
            if not (isval pkg) then A.Open (step pkg, client) else
            (* Note that there's no abstract type at runtime. *)
           (case pkg of
                A.Pack(reprType', pkgImpl', _) =>
                    subst pkgImpl' (typSubstInExp reprType' client)
              | _ => raise No
           )
      | A.PlusLeft (t, e') =>
            if not (isval e) then A.PlusLeft(t, step e')
            else e
      | A.PlusRight (t, e') =>
            if not (isval e) then A.PlusRight(t, step e')
            else e
      | A.Case (c, l, r) =>
        if not (isval c) then A.Case(step c, l, r)
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

fun parse filename =
    let val ast : A.Exp = Parse.parse filename
    in
        ast
    end


(******* Tests *******)

fun test() =
    let
(* Data A.Natlist = None | A.Some(A.Nat, A.Natlist) *)
val natlist : A.Typ = A.TyRec(A.Plus(A.Unit, A.Prod(A.Nat, A.TypVar 0)));
(* A.Unfolded A.Natlist type *)
val nlbody : A.Typ = A.TyRec(A.Plus(A.Unit, A.Prod(A.Nat, natlist)));

(* (* empty : natlist *) *)

(* (* We're projecting.... against a sum type... needs to be a plus. *) *)
(* (* Why does this need to be nlbody, not natlist? *) *)
val nilNatList =
    A.Fold(natlist, A.PlusLeft(A.Plus(A.Unit, A.Prod(A.Nat, natlist)), A.TmUnit));

val singletonList =
    A.Fold(natlist, A.PlusRight(A.Plus(A.Unit, A.Prod(A.Nat, natlist)), A.Tuple(A.Zero,
    A.Fold(natlist, A.PlusLeft(A.Plus(A.Unit, A.Prod(A.Nat, natlist)), A.TmUnit)))));

(* val A.TyRec (A.Plus (A.Unit,A.Prod (A.Nat,A.TypVar 0))) = .Atypeof Nil Nil singletonList; *)

(* val natlistCons = *)
(*     A.Lam(A.Prod(A.Nat, natlist), *)
(*         A.Fold(natlist, *)
(*              A.PlusRight( *)
(*                  A.Plus(A.Unit, A.Prod(A.Nat, natlist)), *)
(*                  A.Var 0 *)
(*              ) *)
(*             ) *)
(*        ); *)

(* val A.Arr (A.Prod (A.Nat,A.TyRec (A.Plus (A.Unit,A.Prod (A.Nat,A.TypVar 0)))), *)
(*          A.TyRec (A.Plus (A.Unit,A.Prod (A.Nat,A.TypVar 0)))) : Typ = *)
(*     typeof Nil Nil natlistCons; *)

(* val deducedSingleListA.AppResType = typeof Nil Nil (A.App(natlistCons, A.Tuple(A.Zero, nilA.NatList))); *)
(* val true = (deducedSingleListA.AppResType = natlist); *)

(* val deducedA.Natlist = typeof Nil Nil nilA.NatList; *)
(* val true = (natlist = deducedA.Natlist); *)

(* val A.Plus (A.Unit,A.Prod (A.Nat,A.TyRec (A.Plus (A.Unit,A.Prod (A.Nat,A.TypVar 0))))) : Typ = *)
(*     typeof Nil Nil (A.Unfold(nilA.NatList)); *)

(* val A.PlusLeft *)
(*     (A.Plus (A.Unit,A.Prod (A.Nat,A.TyRec (A.Plus (A.Unit,A.Prod (A.Nat,A.TypVar 0))))),A.TmUnit) : Exp = eval (A.Unfold(nilA.NatList)); *)

(* (* isnil : nlbody..... ? -> A.Nat (*True or False*) *) *)
(* val isnil = A.Lam(natlist, A.Case(A.Unfold(A.Var 0), A.Succ A.Zero, A.Zero)); *)
(* val A.Nat = typeof Nil Nil (A.App(isnil, nilA.NatList)); *)
(* (* isnil nilA.NatList == 1. *) *)
(* val A.Succ A.Zero = eval (A.App(isnil, nilA.NatList)); *)

(* (* natlistConsType*) *)
(* val natlistConstype = A.Arr(A.Prod(A.Nat, natlist), natlist); *)

(* (* A.PlusRight(natlist, (A.Zero, nilA.NatList)) *) *)

(* (* val natlistCons = A.Lam(A.Prod(A.Nat, natlist), A.Fold(natlist, A.Tuple(A.Var 1, A.Var 0))); *) *)

(* (* Defines a type of natural number queues. Can wrap in an existential type, also. *) *)
(* val natQueueType = A.Prod( *)
(*     (* empty queue *) natlist, *)
(*     A.Prod((* insert *) (A.Arr(A.Prod(A.Nat, natlist), natlist)), *)
(*         (* remove*) A.Arr(natlist, (A.Plus((*None*) A.Unit, (*A.Some(A.Nat, natlist)*)A.Prod(A.Nat, natlist)))) *)
(*     ) *)
(* ); *)

(* val A.Plus(A.Nat, A.Nat) = typeof Nil Nil (A.PlusLeft (A.Plus(A.Nat, A.Nat), A.Zero)); *)
(* val A.Plus(A.Nat, A.Prod(A.Nat, A.Nat)) = typeof Nil Nil (A.PlusLeft (A.Plus(A.Nat, A.Prod(A.Nat, A.Nat)), A.Zero)); *)
(* val A.Zero = step (A.Case(A.PlusLeft (A.Plus(A.Nat, A.Nat), A.Zero), A.Var 0, A.Succ(A.Var 0))); *)
(* val (A.Succ A.Zero) = step (A.Case(A.PlusRight (A.Plus(A.Nat, A.Nat), A.Zero), A.Var 0, A.Succ(A.Var 0))); *)


(* (* Seems there are multiple valid typings of this expression. Up *) *)
(* (* front, I thought A.Some(A.Arr(A.TypVar 0, A.Nat)) is the only correct typing, *) *)
(* (* but the chapter on existential types in TAPL suggests otherwise. *) *)

(* (* That's why we require an explicit type annotation from the programmer. *) *)
(* val A.Arr(A.Nat, A.Nat) = typeof Nil (Cons(42, Nil)) (A.Lam(A.Nat, A.Zero)); *)
(* val A.Arr(A.TypVar 0, A.TypVar 0) = typAbstractOut A.Nat (A.Arr(A.Nat, A.Nat)); *)
(* val A.All(A.Arr(A.TypVar 0, A.Nat)) = typAbstractOut (A.Arr(A.Nat, A.Nat)) (A.All(A.Arr(A.TypVar 0, A.Nat))); *)

(* val e0 = A.Pack(A.Nat, A.Lam(A.Nat, A.Zero), A.Arr(A.TypVar 0, A.TypVar 0)); *)
(* val A.Some(A.Arr(A.TypVar 0, A.TypVar 0)) = typeof Nil Nil e0; *)
(* val e1 = A.Pack(A.Nat, A.Lam(A.Nat, A.Var 0), A.Arr(A.TypVar 0, A.TypVar 0)); *)
(* val A.Some(A.Arr(A.TypVar 0, A.TypVar 0)) = typeof Nil Nil e1; *)
(* val e2 = A.Pack(A.Arr(A.Nat, A.Nat), A.Lam(A.Arr(A.Nat, A.Nat), A.Var 0), A.Arr(A.TypVar 0, A.TypVar 0)); *)
(* val A.Some(A.Arr(A.TypVar 0, A.TypVar 0)) = typeof Nil Nil e2; *)
(* val e4 = A.Pack(A.All(A.Nat), A.Lam(A.All(A.Nat), A.Zero), A.Arr(A.TypVar 0, A.Nat)); *)
(* val A.Some(A.Arr(A.TypVar 0, A.Nat)) = typeof Nil Nil e4 *)

(* val e5 = A.Pack(A.Nat, A.Lam(A.All(A.Nat), A.Zero), A.Arr(A.All (A.TypVar 1), A.TypVar 0)); *)
(* val A.Some(A.Arr(A.All (A.TypVar 1), A.TypVar 0)) = typeof Nil Nil e5 *)

(* val t5 = typeof Nil Nil (A.Lam(A.All(A.Nat), A.Zero)); *)
(* val (A.Arr(A.All A.Nat, A.Nat)) = t5; *)
(* val A.Arr(A.All (A.TypVar 1), A.TypVar 0) = typAbstractOut A.Nat (A.Arr(A.All A.Nat, A.Nat)); *)

(* val f = A.Lam(A.Arr(A.Nat, A.Nat), A.Zero); *)
(* val g = A.Lam (A.Nat,A.Succ (A.Var 0)); *)
(* val pkg = A.Pack(A.Arr(A.Nat, A.Nat), f, A.Arr(A.TypVar 0, A.Nat)); *)
(* val A.Some (A.Arr(A.TypVar 0, A.Nat)) = typeof Nil Nil pkg; *)

(* val A.Some(A.Arr(A.TypVar 0, A.Nat)) = typeof Nil Nil (A.Pack(A.Nat, A.Lam(A.Nat, A.Zero), A.Arr(A.TypVar 0, A.Nat))); *)
(* val A.Some(A.Arr(A.TypVar 0, A.TypVar 0)) = typeof Nil Nil (A.Pack(A.Nat, A.Lam(A.Nat, A.Zero), A.Arr(A.TypVar 0, A.TypVar 0))); *)
(* val A.Nat = typeof Nil Nil (A.Pack(A.Nat, A.Lam(A.Nat, A.Zero), A.TypVar 0)) handle IllTyped => A.Nat; *)

(* val zeroFnPkg = A.Pack(A.Nat, A.Lam(A.Nat, A.Zero), A.Arr(A.TypVar 0, A.Nat)); *)
(* val zeroFnPkg2 = A.Pack(A.Nat, A.Lam(A.Nat, A.Zero), A.Arr(A.Nat, A.TypVar 0)); *)

(* (* Define identity package; can convert A.Nat to internal repr type and back. *) *)
(* val idid = A.Tuple(A.Lam(A.Nat, A.Var 0), A.Lam(A.Nat, A.Var 0)); *)
(* val A.Prod(A.Arr(A.Nat, A.Nat), A.Arr(A.Nat, A.Nat)) = typeof Nil Nil idid; *)
(* val inoutpkg = A.Pack(A.Nat, idid, A.Prod(A.Arr(A.Nat, A.TypVar 0), A.Arr(A.TypVar 0, A.Nat))); *)
(* val A.Some(A.Prod(A.Arr(A.Nat, A.TypVar 0), A.Arr(A.TypVar 0, A.Nat))) = typeof Nil Nil inoutpkg; *)
(* val A.Nat = typeof Nil Nil (A.Open(inoutpkg, A.App(A.ProdRight(A.Var 0), A.App(A.ProdLeft(A.Var 0), A.Zero)))); *)
(* val true = isval inoutpkg; *)
(* (* Dynamics *) *)
(* val A.App *)
(*     (A.ProdRight (A.Tuple (A.Lam (A.Nat,A.Var 0),A.Lam (A.Nat,A.Var 0))), *)
(*      A.App (A.ProdLeft (A.Tuple (A.Lam (A.Nat,A.Var 0),A.Lam (A.Nat,A.Var 0))),A.Zero)) *)
(*     = step (A.Open(inoutpkg, A.App(A.ProdRight(A.Var 0), A.App(A.ProdLeft(A.Var 0), A.Zero)))); *)

(* val A.Zero = eval (A.Open(inoutpkg, A.App(A.ProdRight(A.Var 0), A.App(A.ProdLeft(A.Var 0), A.Zero)))); *)

(* val leftandback = A.Tuple(A.Lam(A.Nat, A.Tuple(A.Var 0, A.Zero)), A.Lam(A.Prod(A.Nat, A.Nat), A.ProdLeft (A.Var 0))); *)
(* val A.Prod (A.Arr (A.Nat,A.Prod (A.Nat, A.Nat)),A.Arr (A.Prod (A.Nat, A.Nat),A.Nat)) = typeof Nil Nil leftandback; *)
(* val inoutpkg2 = A.Pack(A.Prod(A.Nat, A.Nat), leftandback, A.Prod (A.Arr (A.Nat,A.TypVar 0),A.Arr (A.TypVar 0,A.Nat))); *)
(* val A.Some(A.Prod(A.Arr(A.Nat, A.TypVar 0), A.Arr(A.TypVar 0, A.Nat))) = typeof Nil Nil inoutpkg2; *)
(* val A.Nat = typeof Nil Nil (A.Open(inoutpkg2, A.App(A.ProdRight(A.Var 0), A.App(A.ProdLeft(A.Var 0), A.Zero)))); *)
(* val A.Zero = eval (A.Open(inoutpkg2, A.App(A.ProdRight(A.Var 0), A.App(A.ProdLeft(A.Var 0), A.Zero)))); *)

(* val double = A.Lam(A.Nat, A.Rec(A.Var 0, A.Zero, A.Succ (A.Succ (A.Var 0)))); *)
(* val A.Succ (A.Succ A.Zero) = eval (A.App(double, (A.Succ A.Zero))); *)

(* val A.All(A.TypVar 1) = typAbstractOut A.Nat (A.All(A.Nat)); *)
(* val A.TypVar 0 = typAbstractOut A.Nat A.Nat; *)
(* val A.Arr(A.TypVar 0, A.Nat)= typAbstractOut (A.Arr(A.Nat, A.Nat)) (A.Arr(A.Arr(A.Nat, A.Nat), A.Nat)); *)
(* val A.Some(A.Arr(A.TypVar 1, A.Nat)) = typAbstractOut (A.Arr(A.Nat, A.Nat)) (A.Some(A.Arr(A.Arr(A.Nat, A.Nat), A.Nat))); *)
(* val A.All(A.Arr(A.TypVar 1, A.Nat)) = typAbstractOut (A.Arr(A.Nat, A.Nat)) (A.All(A.Arr(A.Arr(A.Nat, A.Nat), A.Nat))); *)
(* val A.Some(A.All(A.Arr(A.TypVar 2, A.Nat))) = typAbstractOut (A.Arr(A.Nat, A.Nat)) (A.Some(A.All(A.Arr(A.Arr(A.Nat, A.Nat), A.Nat)))); *)


(* val polymorphicIdFn = A.TypAbs(A.Lam(A.TypVar 0, A.Var 0)); *)

(* val A.Lam(A.Nat, A.Var 0) = step (A.TypApp(A.Nat, polymorphicIdFn)); *)
(* val A.Lam(A.Arr(A.Nat, A.Nat), A.Var 0) = step (A.TypApp(A.Arr(A.Nat, A.Nat), polymorphicIdFn)); *)
(* val A.TypAbs (A.Lam (A.TypVar 0, A.Var 0)) = step (A.TypApp(A.Nat, A.TypAbs(polymorphicIdFn))) *)
(* val A.TypApp(A.Nat, A.TypAbs((A.Lam (A.TypVar 0, A.Var 0)))) = step (A.TypApp(A.Nat, A.TypApp(A.Nat, A.TypAbs(polymorphicIdFn)))) *)
(* val A.TypAbs(A.Lam(A.Arr(A.Nat, A.TypVar 0), A.Var 0)) = step (A.TypApp(A.Nat, A.TypAbs(A.TypAbs(A.Lam(A.Arr(A.TypVar 1, A.TypVar 0), A.Var 0))))); *)
(* val A.Lam(A.Nat, A.Var 0) = eval (A.TypApp(A.Nat, A.TypApp(A.Nat, A.TypAbs(polymorphicIdFn)))); *)

(* val A.Succ A.Zero = eval (A.App(A.TypApp(A.Nat, polymorphicIdFn), A.Succ(A.Zero))); *)

(* val A.TypAbs(A.Zero) = step (A.TypAbs(A.Zero)); *)
(* val true = isval (A.Lam(A.Nat, A.TypAbs(A.Zero))); *)
(* val (A.TypAbs A.Zero) = step (A.App(A.Lam(A.Nat, A.TypAbs(A.Zero)), A.Zero)); *)

(* val A.Nat = typsubst A.Nat (A.TypVar 0); (* Tho this isn't actually a well-formed type *) *)
(* val A.Arr(A.Nat, A.Nat) = typsubst (A.Arr(A.Nat, A.Nat)) (A.TypVar 0); (* Tho this isn't actually a well-formed type *) *)
(* val false = istype Nil (A.TypVar 0); *)
(* val A.All(A.Nat) = typsubst A.Nat (A.All(A.TypVar 1)); *)
(* val A.Some(A.Nat) = typsubst A.Nat (A.Some(A.TypVar 1)); *)
(* val A.Some(A.Some(A.TypVar 1)) = typsubst A.Nat (A.Some(A.Some(A.TypVar 1))); *)
(* val true = istype Nil (A.All(A.TypVar 0)); *)
(* val true = istype Nil (A.Some(A.TypVar 0)); *)
(* val A.All(A.Arr(A.Nat, (A.All(A.Nat)))) = typsubst (A.All(A.Nat)) (A.All(A.Arr(A.Nat, A.TypVar 1))); *)
(* val A.All(A.Arr(A.Nat, (A.Some(A.Nat)))) = typsubst (A.Some(A.Nat)) (A.All(A.Arr(A.Nat, A.TypVar 1))); *)

(* val A.Nat = typeof Nil Nil (A.TypApp(A.TypVar 0, A.Zero)) handle IllTyped => A.Nat; *)
(* val A.All(A.Arr(A.TypVar 0, A.Nat)) = typeof Nil Nil (A.TypAbs(A.Lam(A.TypVar 0, A.Zero))); *)
(* val A.Arr(A.Arr(A.Nat, A.Nat), A.Nat) = typeof Nil Nil (A.TypApp(A.Arr(A.Nat, A.Nat), (A.TypAbs(A.Lam(A.TypVar 0, A.Zero))))); *)
(* val A.Nat = typeof Nil Nil (A.TypApp(A.Arr(A.Nat, A.Nat), (A.TypAbs(A.Lam(A.TypVar 1, A.Zero))))) handle IllTyped => A.Nat; *)


(* val A.All(A.Nat) = typeof Nil Nil (A.TypAbs(A.Zero)); (* polymorphic zero *) *)
(* (* polymorphic id function :) *) *)
(* val A.All(A.Arr(A.TypVar 0, A.TypVar 0)) = *)
(*     typeof Nil Nil (A.TypAbs(A.Lam(A.TypVar 0, A.Var 0))); *)
(* val A.Arr(A.Nat, A.All(A.Arr(A.TypVar 0, A.TypVar 0))) = *)
(*     typeof Nil Nil (A.Lam(A.Nat, A.TypAbs(A.Lam(A.TypVar 0, A.Var 0)))); *)
(* val A.Arr(A.Nat, A.All(A.Arr(A.TypVar 0, A.TypVar 0))) = *)
(*     typeof Nil Nil (A.Lam(A.Nat, A.TypAbs(A.Lam(A.TypVar 0, A.Var 0)))); *)
(* (* Nested type variables *) *)
(* val A.All(A.All(A.Arr(A.TypVar 1,A.Nat))) = *)
(*     typeof Nil Nil (A.TypAbs(A.TypAbs(A.Lam(A.TypVar 1, A.Zero)))) *)
(* val A.All(A.All(A.Arr(A.TypVar 1, A.TypVar 1))) = *)
(*     typeof Nil Nil (A.TypAbs(A.TypAbs(A.Lam(A.TypVar 1, A.Var 0)))) *)

(* val true = istype Nil A.Nat; *)
(* val false = istype Nil (A.TypVar 0); (* Unbound type variable *) *)
(* val false = istype Nil (A.Arr(A.TypVar 0, A.Nat)); (* Unbound type variable *) *)
(* val false = istype Nil (A.Arr(A.Nat, A.TypVar 0)); (* Unbound type variable *) *)
(* val true = istype Nil (A.All(A.Nat)); *)
(* val true = istype Nil (A.All(A.TypVar 0)); *)
(* val true = istype Nil (A.All(A.Arr(A.TypVar 0, A.Nat))); *)
(* val true = istype Nil (A.All(A.Arr(A.Nat, A.TypVar 0))); *)
(* val false = istype Nil (A.All(A.Arr(A.Nat, A.TypVar 1))); (* Unbound *) *)
(* val true = istype Nil (A.All(A.All(A.Arr(A.Nat, A.TypVar 1)))); (* Bound *) *)

(* val 0 = len Nil; *)
(* val 1 = len (Cons(1, Nil)); *)

(* val true = isval A.Zero; *)
(* val true = isval (A.Succ(A.Zero)); *)
(* val true = isval (A.Lam(A.Nat, A.Succ(A.Zero))); *)
(* val true = isval (A.Lam(A.Nat, A.Zero)); *)
(* val true = isval (A.Lam(A.Nat, A.Succ(A.Var(0)))); *)
(* val false = isval (A.App(A.Lam(A.Nat, A.Zero), A.Zero)); *)

(* val A.Zero = subst A.Zero A.Zero; *)
(* val A.Succ A.Zero = subst A.Zero (A.Succ A.Zero); *)
(* val (A.Lam(A.Nat, A.Var 0)) = subst (A.Succ A.Zero) (A.Lam(A.Nat, A.Var 0)); *)
(* val (A.Var 0) = subst (A.Succ A.Zero) (A.Var 1); *)
(* val A.Lam(A.Nat, A.Var 0) = subst (A.Succ A.Zero) (A.Lam(A.Nat, A.Var 0)); *)
(* val A.Lam(A.Nat, (A.Succ A.Zero)) = subst (A.Succ A.Zero) (A.Lam(A.Nat, A.Var 1)); *)
(* val A.App(A.Lam(A.Nat, A.Succ A.Zero), (A.Succ A.Zero)) = *)
(*     subst (A.Succ A.Zero) (A.App(A.Lam(A.Nat, A.Var 1), (A.Var 0))); *)

(* val A.Lam(A.Nat, A.Zero) = subst A.Zero (A.Lam(A.Nat, A.Var 1)); *)
(* val A.Lam(A.Nat, A.Succ A.Zero) = subst (A.Succ A.Zero) (A.Lam(A.Nat, A.Var 1)); *)
(* val A.Lam(A.Nat, A.Lam(A.Nat, A.Succ A.Zero)) = subst (A.Succ A.Zero) (A.Lam(A.Nat, A.Lam(A.Nat, A.Var 2))); *)
(* val A.Lam(A.Nat, A.Rec(A.Zero, A.Zero, A.Succ A.Zero)) = subst (A.Succ A.Zero) (A.Lam(A.Nat, A.Rec(A.Zero, A.Zero, A.Var 2))); *)

(* val A.Lam(A.Nat, A.Rec(A.Zero, A.Var 0, A.Zero)) = subst A.Zero (A.Lam(A.Nat, A.Rec(A.Var 1, A.Var 0, A.Zero))); *)
(* val A.Lam(A.Nat, A.Rec(A.Zero, A.Var 1, A.Zero)) = subst A.Zero (A.Lam(A.Nat, A.Rec(A.Var 1, A.Var 2, A.Zero))); *)
(* val A.Rec(A.Zero, A.Zero, A.Zero) = step (A.App(A.Lam(A.Nat, A.Rec(A.Var 0, A.Var 0, A.Zero)), A.Zero)); *)

(* val A.Nat = get (Cons(A.Nat, Nil)) 0; *)
(* val A.Arr(A.Nat, A.Nat) = get (Cons(A.Nat, Cons(A.Arr(A.Nat, A.Nat), Nil))) 1; *)
(* val A.Nat = get (Cons(A.Nat, Cons(A.Arr(A.Nat, A.Nat), Nil))) 0; *)

(* val A.Nat = typeof Nil Nil A.Zero; *)
(* val A.Nat = typeof Nil Nil (A.Succ (A.Zero)); *)

(* val A.Nat = typeof (Cons(A.Nat, Nil)) Nil (A.Var(0)); *)
(* val A.Arr(A.Nat, A.Nat) = typeof (Cons(A.Arr(A.Nat, A.Nat), Nil)) Nil (A.Var(0)); *)
(* val A.Arr(A.Nat, A.Nat) = typeof (Cons(A.Arr(A.Nat, A.Nat), Cons(A.Nat, Nil))) Nil (A.Var(0)); *)
(* val A.Nat = typeof (Cons(A.Arr(A.Nat, A.Nat), Cons(A.Nat, Nil))) Nil (A.Var(1)); *)

(* val A.Arr(A.Nat, A.Nat) = typeof Nil Nil (A.Lam(A.Nat, A.Zero)); *)
(* val A.Arr(A.Nat, A.Nat) = typeof Nil Nil (A.Lam(A.Nat, A.Succ(A.Zero))); *)

(* val A.Nat = typeof Nil Nil (A.App(A.Lam(A.Nat, A.Zero), A.Zero)); *)

(* val A.Nat = typeof Nil Nil (A.App(A.Lam(A.Nat, A.Succ(A.Zero)), A.Lam(A.Nat, A.Zero))) *)
(*           handle IllTyped => A.Nat; *)

(* val timesTwo = A.Rec(A.Succ(A.Zero), A.Zero, A.Succ(A.Succ(A.Var(0 (* prev *))))); *)
(* val A.Nat = typeof Nil Nil timesTwo; *)

(* val A.Arr(A.Arr(A.Nat, A.Nat), A.Nat) = *)
(*     typeof Nil Nil (A.Lam(A.Arr(A.Nat, A.Nat), A.App(A.Var(0), A.Zero))); *)

(* val A.Arr(A.Nat, A.Nat) = typeof Nil Nil (A.Rec(A.Zero, *)
(*                                        A.Lam(A.Nat, A.Succ(A.Zero)), *)
(*                                        A.Lam(A.Nat, A.Succ(A.Var(0))))); *)

(* val A.Arr(A.Nat, A.Nat) = typeof Nil Nil (A.Rec(A.Succ(A.Zero), *)
(*                                        A.Lam(A.Nat, A.Succ(A.Zero)), *)
(*                                        A.Lam(A.Nat, A.Succ(A.Var(0))))); *)

(* val A.Arr(A.Nat, A.Nat) = typeof (Cons(A.Nat, Nil)) Nil (A.Rec(A.Var(0), *)
(*                                        A.Lam(A.Nat, A.Succ(A.Zero)), *)
(*                                        A.Lam(A.Nat, A.Succ(A.Var(0))))); *)


(* val A.Nat = typeof Nil Nil (A.App(A.Lam(A.Arr(A.Nat, A.Nat), A.App(A.Var(0), A.Zero)), A.Zero)) handle IllTyped => A.Nat; *)

(* (* Ill-formed; first param must be A.Nat. *) *)
(* val A.Nat = typeof Nil Nil (A.Rec(A.Lam(A.Nat, A.Zero), A.Lam(A.Nat, A.Succ(A.Zero)), A.Lam(A.Nat, A.Succ(A.Var(0))))) handle Bind => A.Nat; *)

(* (* Ill-formed; base case type does not match rec case type. *) *)
(* val A.Nat = (typeof Nil Nil (A.Rec(A.Zero, A.Succ(A.Zero), A.Lam(A.Nat, A.Succ(A.Zero)))) *)
(*           handle IllTyped => A.Nat); *)

(* val A.Arr(A.Nat, A.Nat) = typeof Nil Nil (A.Lam((A.TypVar 0), A.Zero)) handle IllTyped => A.Arr(A.Nat, A.Nat); *)

(* val A.Succ(A.Rec(A.Zero, A.Zero, A.Succ(A.Var 0))) = step (A.Rec(A.Succ(A.Zero), A.Zero, A.Succ(A.Var 0))); *)

(* val A.Succ(A.Succ(A.Rec(A.Zero, A.Zero, A.Succ(A.Succ(A.Var 0))))) = *)
(*     step (A.Rec(A.Succ(A.Zero), A.Zero, A.Succ(A.Succ(A.Var 0)))); *)

(* val A.Zero = step (A.Rec(A.Zero, A.Zero, A.Succ(A.Var 0))); *)
(* val A.Succ(A.Succ(A.Zero)) = eval (A.Rec(A.Succ(A.Succ(A.Zero)), A.Zero, A.Succ(A.Var 0))); *)
(* val A.Succ(A.Succ(A.Succ(A.Succ(A.Zero)))) = *)
(*     eval (A.Rec(A.Succ(A.Succ(A.Zero)), A.Zero, A.Succ(A.Succ(A.Var 0)))); *)

(* val A.Succ(A.Succ(A.Succ(A.Succ(A.Zero)))) = *)
(*     eval (A.Rec(A.App(A.Lam(A.Nat, A.Succ(A.Var 0)), A.Succ(A.Zero)), *)
(*               A.Zero, A.Succ(A.Succ(A.Var 0)))); *)

(* val A.Zero = step A.Zero; *)
(* val A.Succ(A.Zero) = step (A.Succ(A.Zero)); *)
(* val A.Lam(A.Nat, A.Zero) = step (A.Lam(A.Nat, A.Zero)); *)
(* val A.Succ A.Zero = step (A.App(A.Lam(A.Nat, A.Succ(A.Zero)), A.Zero)); *)
(* val A.Succ A.Zero = step (A.App(A.Lam(A.Nat, A.Succ(A.Var(0))), A.Zero)); *)
(* val A.Succ (A.Succ A.Zero) = step (A.App(A.Lam(A.Nat, A.Succ(A.Var(0))), A.Succ A.Zero)); *)
(* val A.Succ (A.Succ (A.Succ A.Zero)) = step (A.App(A.Lam(A.Nat, A.Succ(A.Var(0))), A.Succ (A.Succ A.Zero))); *)
(* val A.Succ (A.Succ (A.Succ A.Zero)) = step (A.App(A.Lam(A.Nat, A.Succ(A.Succ(A.Var(0)))), A.Succ A.Zero)); *)

(* (* Take in a nat -> nat and apply to zero. Input nat -> nat is A.Succ *) *)
(* val A.App(A.Lam(A.Nat, A.Succ(A.Var(0))), A.Zero) = step (A.App(A.Lam(A.Arr(A.Nat, A.Nat), A.App(A.Var(0), A.Zero)), *)
(*                                                   A.Lam(A.Nat, A.Succ(A.Var(0))))); *)
(* val A.Succ A.Zero = step (A.App(A.Lam(A.Nat, A.Succ(A.Var(0))), A.Zero)); *)

(* val A.Succ A.Zero = eval (A.App(A.Lam(A.Arr(A.Nat, A.Nat), A.App(A.Var(0), A.Zero)), *)
(*                           A.Lam(A.Nat, A.Succ(A.Var(0))))); *)
(* val A.Succ (A.Succ (A.Succ (A.Succ A.Zero))) = eval (A.Rec(A.Succ(A.Succ(A.Zero)), A.Zero, A.Succ(A.Succ(A.Var 0)))); *)

(* val multByThree = A.Lam(A.Nat, A.Rec(A.Var 0, A.Zero, A.Succ(A.Succ(A.Succ(A.Var 0))))); *)
(* val A.Succ (A.Succ (A.Succ A.Zero)) = eval (A.App(multByThree, A.Succ A.Zero)) *)
in
()
end

end (* structure Thon *)
