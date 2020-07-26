(* A system FE interpreter - System F with existential packages *)
Control.Print.printDepth := 100;

exception TypeMismatch
exception No
exception ClientTypeCannotEscapeClientScope
exception Unimplemented

datatype Typ = Nat
             | TypVar of int
             | Arr of Typ * Typ
             | Prod of Typ * Typ
             | All of Typ (* binds *)
             | Some of Typ (* binds *)

datatype Idx = int

datatype Exp = Zero
             | Var of int (* idx into ctx *)
             | Succ of Exp
             | Left of Exp
             | Right of Exp
             | Lam of Typ (*argType*) * Exp (*funcBody*)
             | App of Exp * Exp
             | Rec of Exp (*i : Nat*) * Exp (*baseCase: t*) * Exp (*recCase - binds*)
             | TypAbs of Exp (* binds type variable *)
             | TypApp of Typ * Exp
             | Pack of Typ * Exp
             | AnnotatedPack of Typ (*reprType*)* Exp (*pkgImpl*)* Typ (*pkgType - first example of explicit type binding - there's not one cannonical type*)
             | Open of Exp (*package*) * Exp (* client that binds BOTH a TypVar and a Exp Var *)
             | Tuple of Exp * Exp


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
        Nat => true
      | TypVar i => i < (len typeCtx)
      | Arr(d, c) => (istype typeCtx d) andalso (istype typeCtx c)
      | Prod(l, r) => (istype typeCtx l) andalso (istype typeCtx r)
      | All t' => istype (Cons(42, typeCtx)) t'
      | Some t' => istype (Cons(42, typeCtx)) t'


fun typsubst' src dst bindingDepth =
    case dst
     of Nat => Nat
      | TypVar n  => if n = bindingDepth then src else
                     if n > bindingDepth then TypVar (n-1) else
                     dst
      | Arr (t, t') => Arr((typsubst' src t bindingDepth),
                           (typsubst' src t' bindingDepth))
      | Prod (l, r) => Arr((typsubst' src l bindingDepth),
                           (typsubst' src r bindingDepth))
      | All t => All(typsubst' src t (bindingDepth + 1))
      | Some t => Some(typsubst' src t (bindingDepth + 1))


fun typsubst src dst = typsubst' src dst 0


(* Turns search to Var bindingDepth
 *
 * DEVNOTE: assumes the caller will place the result underneath a type
 * variable binding site.
 *
 * Remarkably similar to typSubst - might be able to dedup. This needs
 * to track bindingDepth though and subst in TypVar of the appropriate
 * depth.
 *)
fun typAbstractOut' search t bindingDepth =
    if t = search then (TypVar bindingDepth) else
    case t
     of Nat => Nat
      | TypVar n  => TypVar n
      | Arr (d, c) => Arr((typAbstractOut' search d bindingDepth),
                           (typAbstractOut' search c bindingDepth))
      | Prod (l, r) => Prod((typAbstractOut' search l bindingDepth),
                            (typAbstractOut' search r bindingDepth))
      | All t' => All(typAbstractOut' search t' (bindingDepth+1))
      | Some t' => Some(typAbstractOut' search t' (bindingDepth+1))


fun typAbstractOut search t = typAbstractOut' search t 0


(* TODO Figure something better out... *)
fun typdecrVarIdxs t =
    case t of
        Nat => Nat
      | TypVar i => if (i-1) < 0 then raise ClientTypeCannotEscapeClientScope
                    else TypVar (i -1)
      | Arr(d, c) => Arr(typdecrVarIdxs d, typdecrVarIdxs c)
      | Prod(l, r) => Arr(typdecrVarIdxs l, typdecrVarIdxs r)
      | All t' => All(typdecrVarIdxs t')
      | Some t' => Some(typdecrVarIdxs t')


fun decrVarIdxs e =
    case e
     of  Zero => Zero
       | Var i => if (i-1) < 0 then raise ClientTypeCannotEscapeClientScope
                  else Var (i - 1)
       | Succ e2 => (Succ (decrVarIdxs e2))
       | Left e => (Left (decrVarIdxs e))
       | Right e => (Right (decrVarIdxs e))
       | Lam (argType, funcBody) => Lam(typdecrVarIdxs argType, decrVarIdxs funcBody)
       | App (f, n) => App(decrVarIdxs f, decrVarIdxs n)
       | Tuple (l, r) => Tuple(decrVarIdxs l, decrVarIdxs r)
       | Rec (i, baseCase, recCase) =>
            Rec(decrVarIdxs i, decrVarIdxs baseCase, decrVarIdxs recCase)
       | TypAbs e => TypAbs (decrVarIdxs e)
       | TypApp (appType, e) => TypApp(typdecrVarIdxs appType, decrVarIdxs e)
       | Pack (reprType, pkgImpl) => Pack(typdecrVarIdxs reprType, decrVarIdxs pkgImpl)
       | AnnotatedPack (reprType, pkgImpl, pkgType) => AnnotatedPack(typdecrVarIdxs reprType, decrVarIdxs pkgImpl, typdecrVarIdxs pkgType)
       | Open (pkg, client) => Open(decrVarIdxs pkg, decrVarIdxs client)


(* Just substitute the srcType in everywhere you see a TypVar bindingDepth *)
(* might not need to track bindingdepth ourselves *)
fun typSubstInExp' srcType dstExp bindingDepth =
    case dstExp
     of  Zero => Zero
       | Var i => Var i
       | Succ e2 => Succ (typSubstInExp' srcType e2 bindingDepth)
       | Left e => Left (typSubstInExp' srcType e bindingDepth)
       | Right e => Right (typSubstInExp' srcType e bindingDepth)
       | Lam (argType, funcBody) =>
            Lam((typsubst' srcType argType bindingDepth),
                typSubstInExp' srcType funcBody bindingDepth)
       | App (f, n) =>
            App (typSubstInExp' srcType f bindingDepth,
                 typSubstInExp' srcType n bindingDepth)
       | Tuple (l, r) =>
            Tuple (typSubstInExp' srcType l bindingDepth,
                   typSubstInExp' srcType r bindingDepth)
       | Rec (i, baseCase, recCase) =>
            Rec(typSubstInExp' srcType i bindingDepth,
                typSubstInExp' srcType baseCase bindingDepth,
                typSubstInExp' srcType recCase bindingDepth)
       | TypAbs e => TypAbs(typSubstInExp' srcType e (bindingDepth+1)) (* binds type var *)
       | TypApp (appType, e) =>
            TypApp(typsubst' srcType appType bindingDepth,
                   typSubstInExp' srcType e bindingDepth)
       | Pack (reprType, pkgImpl) =>
            Pack(typsubst' srcType reprType bindingDepth,
                typSubstInExp' srcType pkgImpl bindingDepth)
       | AnnotatedPack(reprType, pkgImpl, pkgType) =>
            AnnotatedPack(typsubst' srcType reprType bindingDepth,
                          typSubstInExp' srcType pkgImpl bindingDepth,
                          typsubst' srcType pkgType bindingDepth)
       | Open (pkg, client) =>
            Open(typSubstInExp' srcType pkg bindingDepth,
                 typSubstInExp' srcType client (bindingDepth+1))


fun typSubstInExp srcType dstExp = typSubstInExp' srcType dstExp 0


fun typecheck ctx typCtx e =
    case e
     of  Zero => Nat
       | Var i => get ctx i
       | Succ e2 => (typecheck ctx typCtx e2)
       | Left e => let val Prod(l, r) = (typecheck ctx typCtx e) in l end
       | Right e => let val Prod(l, r) = (typecheck ctx typCtx e) in r end
       | Lam (argType, funcBody) =>
            if not (istype typCtx argType) then raise No else
            Arr (argType, typecheck (Cons(argType, ctx)) typCtx funcBody)
       | App (f, n) =>
            let val Arr (d, c) = typecheck ctx typCtx f
                val argType = typecheck ctx typCtx n
            in
                if d <> argType then raise TypeMismatch
                else c
            end
       | Tuple (l, r) => Prod(typecheck ctx typCtx l, typecheck ctx typCtx r)
       | Rec (i, baseCase, recCase) =>
            let val Nat = typecheck ctx typCtx i
                val t = typecheck ctx typCtx baseCase
                val t2 = typecheck (Cons(t, ctx)) typCtx recCase
            in
                if t <> t2 then raise TypeMismatch else t
            end
       | TypAbs e => All(typecheck ctx (Cons(42, typCtx)) e)
       | TypApp (appType, e) =>
            if not (istype typCtx appType) then raise No else
            let val All(t) = typecheck ctx typCtx e
            in
                typsubst appType t
            end
       | Pack (reprType, pkgImpl) =>
            if not (istype Nil reprType) then raise TypeMismatch else
            (* pkgType : [reprType/TypVar 0](t') *)
            let val pkgType = typecheck ctx (Cons(42, typCtx)) pkgImpl
            (* Want Some(t') *)
            in Some(typAbstractOut reprType pkgType) end
       | AnnotatedPack (reprType, pkgImpl, pkgType) =>
            if not (istype Nil reprType) then raise TypeMismatch else
            (* pkgType : [reprType/TypVar 0](t') *)
            let val deducedPkgType = typecheck ctx (Cons(42, typCtx)) pkgImpl
            in
                if (typAbstractOut reprType deducedPkgType) <>
                   (typAbstractOut reprType pkgType) then
                raise TypeMismatch else
            Some(pkgType)
            end
       | Open (pkg, client) =>
            let val Some(r) = typecheck ctx typCtx pkg
                (* binds BOTH a TypVar and a Exp Var *)
                val clientType = typecheck (Cons(r, ctx)) (Cons(42, typCtx)) client
                (* shift indices of free vars and typevars in clientType down by one *)
            in
                (* if not (istype typCtx clientType) then raise TypeMismatch else *)
                typdecrVarIdxs clientType
            end

fun isVal e =
    case e of
        Zero => true
      | Succ(n) => isVal n
      | Lam(_, _) => true
      | Tuple(l, r) => (isVal l) andalso (isVal r)
      | TypAbs _  => true
      | Pack (reprType, pkgImpl) => isVal pkgImpl
      | AnnotatedPack(_, pkgImpl, _) => isVal pkgImpl
      | _ => false


fun subst' src dst bindingDepth =
    case dst
     of  Zero => Zero
       | Var n  => if n = bindingDepth then src else
                   if n > bindingDepth then Var(n-1) else
                   Var(n)
       | Succ e2 => Succ (subst' src e2 bindingDepth)
       | Left e => Left (subst' src e bindingDepth)
       | Right e => Right (subst' src e bindingDepth)
       | Lam (t, f) => Lam(t, (subst' src f (bindingDepth+1)))
       | App (f, n) => App((subst' src f bindingDepth), (subst' src n bindingDepth))
       | Rec (i, baseCase, recCase) =>
            Rec(subst' src i bindingDepth,
                subst' src baseCase bindingDepth,
                subst' src recCase (bindingDepth+1))
       | TypAbs e => TypAbs (subst' src e bindingDepth) (* abstracts over types, not exps *)
       | TypApp (appType, e) => TypApp(appType, subst' src e bindingDepth)
       | Pack (reprType, pkgImpl) => Pack(reprType, subst' src pkgImpl bindingDepth)
       | AnnotatedPack(reprType, pkgImpl, t) => AnnotatedPack(reprType,
subst' src pkgImpl bindingDepth, t)
       | Open (pkg, client) => Open(subst' src pkg bindingDepth, subst' src client (bindingDepth+1))
       | Tuple (l, r) => Tuple (subst' src l bindingDepth, subst' src r bindingDepth)


fun subst src dst = subst' src dst 0


fun step e =
    let val _ = typecheck Nil Nil e in
    if isVal e then e else
    case e of
        Succ(n) => if not (isVal n) then Succ(step n) else e
      | Left n  => if not (isVal n) then Left(step n) else
                   let val Tuple(l, r) = n in l end
      | Right n  => if not (isVal n) then Right(step n) else
                    let val Tuple(l, r) = n in r end
      | Tuple(l, r) => if not (isVal l) then Tuple(step l, r) else
                       if not (isVal r) then Tuple(l, step r) else
                       e
      | App(f, n) => if not (isVal f) then App(step f, n)
                     else (if not (isVal n) then App(f, step n)
                           else let val Lam(t, f') = f
                           in
                               (* plug `n` into `f'` *)
                               subst n f'
                           end
                          )
      | Var x => Var x
      | Rec (Zero, baseCase, recCase) => baseCase
      | Rec (Succ(i), baseCase, recCase) =>
            (* Doesn't evaluate recursive call if not required. *)
            subst (Rec(i, baseCase, recCase)) recCase
      | Rec (i, baseCase, recCase) =>
            if not (isVal i) then
                Rec(step i, baseCase, recCase)
            else raise No
      | TypAbs e' => raise No (* Already isVal *)
      | TypApp (t, e') =>
            if not (isVal e') then (TypApp (t, step e'))
            else
                let val TypAbs(e'') = e' in
                    typSubstInExp t e''
                end
      | Pack (reprType, pkgImpl) =>
            if not (isVal pkgImpl) then Pack(reprType, step pkgImpl) else
            if not (isVal e) then raise No else
            e
      | AnnotatedPack(reprType, pkgImpl, pkgType) =>
            if not (isVal pkgImpl) then AnnotatedPack(reprType, step pkgImpl, pkgType) else
            if not (isVal e) then raise No else
            e
      | Open (pkg, client) =>
            if not (isVal pkg) then Open (step pkg, client) else
            (* Note that there's no abstract type at runtime. *)
           (case pkg of
                Pack(reprType', pkgImpl') =>
                    subst pkgImpl' (typSubstInExp reprType' client)
              | AnnotatedPack(reprType', pkgImpl', _) =>
                    subst pkgImpl' (typSubstInExp reprType' client)
              | _ => raise No
           )
      | _ => if (isVal e) then e else raise No
    end


fun eval e = if isVal e then e else eval (step e)


(******* Tests *******)


(* Seems there are multiple valid typings of this expression. Up
front, I thought Some(Arr(TypVar 0, Nat)) is the only correct typing,
but the chapter on existential types in TAPL suggests otherwise. *)
val Arr(Nat, Nat) = typecheck Nil (Cons(42, Nil)) (Lam(Nat, Zero));
val Arr(TypVar 0, TypVar 0) = typAbstractOut Nat (Arr(Nat, Nat));
val All(Arr(TypVar 0, Nat)) = typAbstractOut (Arr(Nat, Nat)) (All(Arr(TypVar 0, Nat)));

val e0 = AnnotatedPack(Nat, Lam(Nat, Zero), Arr(TypVar 0, TypVar 0));
val Some(Arr(TypVar 0, TypVar 0)) = typecheck Nil Nil e0;
val e1 = AnnotatedPack(Nat, Lam(Nat, Var 0), Arr(TypVar 0, TypVar 0));
val Some(Arr(TypVar 0, TypVar 0)) = typecheck Nil Nil e1;
val e2 = AnnotatedPack(Arr(Nat, Nat), Lam(Arr(Nat, Nat), Var 0), Arr(TypVar 0, TypVar 0));
val Some(Arr(TypVar 0, TypVar 0)) = typecheck Nil Nil e2;
val e4 = AnnotatedPack(All(Nat), Lam(All(Nat), Zero), Arr(TypVar 0, Nat));
val Some(Arr(TypVar 0, Nat)) = typecheck Nil Nil e4

val e5 = AnnotatedPack(Nat, Lam(All(Nat), Zero), Arr(All (TypVar 1), TypVar 0));
val Some(Arr(All (TypVar 1), TypVar 0)) = typecheck Nil Nil e5

val t5 = typecheck Nil Nil (Lam(All(Nat), Zero));
val (Arr(All Nat, Nat)) = t5;
val Arr(All (TypVar 1), TypVar 0) = typAbstractOut Nat (Arr(All Nat, Nat));

val f = Lam(Arr(Nat, Nat), Zero);
val g = Lam (Nat,Succ (Var 0));
val pkg = AnnotatedPack(Arr(Nat, Nat), f, Arr(TypVar 0, Nat));
val Some (Arr(TypVar 0, Nat)) = typecheck Nil Nil pkg;

val Some(Arr(TypVar 0, Nat)) = typecheck Nil Nil (AnnotatedPack(Nat, Lam(Nat, Zero), Arr(TypVar 0, Nat)));
val Some(Arr(TypVar 0, TypVar 0)) = typecheck Nil Nil (AnnotatedPack(Nat, Lam(Nat, Zero), Arr(TypVar 0, TypVar 0)));
val Nat = typecheck Nil Nil (AnnotatedPack(Nat, Lam(Nat, Zero), TypVar 0)) handle TypeMismatch => Nat;

val zeroFnPkg = AnnotatedPack(Nat, Lam(Nat, Zero), Arr(TypVar 0, Nat));
val zeroFnPkg2 = AnnotatedPack(Nat, Lam(Nat, Zero), Arr(Nat, TypVar 0));

(* Define identity package; can convert Nat to internal repr type and back. *)
val idid = Tuple(Lam(Nat, Var 0), Lam(Nat, Var 0));
val Prod(Arr(Nat, Nat), Arr(Nat, Nat)) = typecheck Nil Nil idid;
val inoutpkg = AnnotatedPack(Nat, idid, Prod(Arr(Nat, TypVar 0), Arr(TypVar 0, Nat)));
val Some(Prod(Arr(Nat, TypVar 0), Arr(TypVar 0, Nat))) = typecheck Nil Nil inoutpkg;
val Nat = typecheck Nil Nil (Open(inoutpkg, App(Right(Var 0), App(Left(Var 0), Zero))));
val true = isVal inoutpkg;
(* Dynamics *)
val App
    (Right (Tuple (Lam (Nat,Var 0),Lam (Nat,Var 0))),
     App (Left (Tuple (Lam (Nat,Var 0),Lam (Nat,Var 0))),Zero))
    = step (Open(inoutpkg, App(Right(Var 0), App(Left(Var 0), Zero))));

val Zero = eval (Open(inoutpkg, App(Right(Var 0), App(Left(Var 0), Zero))));

val leftandback = Tuple(Lam(Nat, Tuple(Var 0, Zero)), Lam(Prod(Nat, Nat), Left (Var 0)));
val Prod (Arr (Nat,Prod (Nat, Nat)),Arr (Prod (Nat, Nat),Nat)) = typecheck Nil Nil leftandback;
val inoutpkg2 = AnnotatedPack(Prod(Nat, Nat), leftandback, Prod (Arr (Nat,TypVar 0),Arr (TypVar 0,Nat)));
val Some(Prod(Arr(Nat, TypVar 0), Arr(TypVar 0, Nat))) = typecheck Nil Nil inoutpkg2;
val Nat = typecheck Nil Nil (Open(inoutpkg2, App(Right(Var 0), App(Left(Var 0), Zero))));
val Zero = eval (Open(inoutpkg2, App(Right(Var 0), App(Left(Var 0), Zero))));

val double = Lam(Nat, Rec(Var 0, Zero, Succ (Succ (Var 0))));
val Succ (Succ Zero) = eval (App(double, (Succ Zero)));

val All(TypVar 1) = typAbstractOut Nat (All(Nat));
val TypVar 0 = typAbstractOut Nat Nat;
val Arr(TypVar 0, Nat)= typAbstractOut (Arr(Nat, Nat)) (Arr(Arr(Nat, Nat), Nat));
val Some(Arr(TypVar 1, Nat)) = typAbstractOut (Arr(Nat, Nat)) (Some(Arr(Arr(Nat, Nat), Nat)));
val All(Arr(TypVar 1, Nat)) = typAbstractOut (Arr(Nat, Nat)) (All(Arr(Arr(Nat, Nat), Nat)));
val Some(All(Arr(TypVar 2, Nat))) = typAbstractOut (Arr(Nat, Nat)) (Some(All(Arr(Arr(Nat, Nat), Nat))));


val polymorphicIdFn = TypAbs(Lam(TypVar 0, Var 0));

val Lam(Nat, Var 0) = step (TypApp(Nat, polymorphicIdFn));
val Lam(Arr(Nat, Nat), Var 0) = step (TypApp(Arr(Nat, Nat), polymorphicIdFn));
val TypAbs (Lam (TypVar 0, Var 0)) = step (TypApp(Nat, TypAbs(polymorphicIdFn)))
val TypApp(Nat, TypAbs((Lam (TypVar 0, Var 0)))) = step (TypApp(Nat, TypApp(Nat, TypAbs(polymorphicIdFn))))
val TypAbs(Lam(Arr(Nat, TypVar 0), Var 0)) = step (TypApp(Nat, TypAbs(TypAbs(Lam(Arr(TypVar 1, TypVar 0), Var 0)))));
val Lam(Nat, Var 0) = eval (TypApp(Nat, TypApp(Nat, TypAbs(polymorphicIdFn))));

val Succ Zero = eval (App(TypApp(Nat, polymorphicIdFn), Succ(Zero)));

val TypAbs(Zero) = step (TypAbs(Zero));
val true = isVal (Lam(Nat, TypAbs(Zero)));
val (TypAbs Zero) = step (App(Lam(Nat, TypAbs(Zero)), Zero));

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

val Nat = typecheck Nil Nil (TypApp(TypVar 0, Zero)) handle No => Nat;
val All(Arr(TypVar 0, Nat)) = typecheck Nil Nil (TypAbs(Lam(TypVar 0, Zero)));
val Arr(Arr(Nat, Nat), Nat) = typecheck Nil Nil (TypApp(Arr(Nat, Nat), (TypAbs(Lam(TypVar 0, Zero)))));
val Nat = typecheck Nil Nil (TypApp(Arr(Nat, Nat), (TypAbs(Lam(TypVar 1, Zero))))) handle No => Nat;


val All(Nat) = typecheck Nil Nil (TypAbs(Zero)); (* polymorphic zero *)
(* polymorphic id function :) *)
val All(Arr(TypVar 0, TypVar 0)) =
    typecheck Nil Nil (TypAbs(Lam(TypVar 0, Var 0)));
val Arr(Nat, All(Arr(TypVar 0, TypVar 0))) =
    typecheck Nil Nil (Lam(Nat, TypAbs(Lam(TypVar 0, Var 0))));
val Arr(Nat, All(Arr(TypVar 0, TypVar 0))) =
    typecheck Nil Nil (Lam(Nat, TypAbs(Lam(TypVar 0, Var 0))));
(* Nested type variables *)
val All(All(Arr(TypVar 1,Nat))) =
    typecheck Nil Nil (TypAbs(TypAbs(Lam(TypVar 1, Zero))))
val All(All(Arr(TypVar 1, TypVar 1))) =
    typecheck Nil Nil (TypAbs(TypAbs(Lam(TypVar 1, Var 0))))

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

val true = isVal Zero;
val true = isVal (Succ(Zero));
val true = isVal (Lam(Nat, Succ(Zero)));
val true = isVal (Lam(Nat, Zero));
val true = isVal (Lam(Nat, Succ(Var(0))));
val false = isVal (App(Lam(Nat, Zero), Zero));

val Zero = subst Zero Zero;
val Succ Zero = subst Zero (Succ Zero);
val (Lam(Nat, Var 0)) = subst (Succ Zero) (Lam(Nat, Var 0));
val (Var 0) = subst (Succ Zero) (Var 1);
val Lam(Nat, Var 0) = subst (Succ Zero) (Lam(Nat, Var 0));
val Lam(Nat, (Succ Zero)) = subst (Succ Zero) (Lam(Nat, Var 1));
val App(Lam(Nat, Succ Zero), (Succ Zero)) =
    subst (Succ Zero) (App(Lam(Nat, Var 1), (Var 0)));

val Lam(Nat, Zero) = subst Zero (Lam(Nat, Var 1));
val Lam(Nat, Succ Zero) = subst (Succ Zero) (Lam(Nat, Var 1));
val Lam(Nat, Lam(Nat, Succ Zero)) = subst (Succ Zero) (Lam(Nat, Lam(Nat, Var 2)));
val Lam(Nat, Rec(Zero, Zero, Succ Zero)) = subst (Succ Zero) (Lam(Nat, Rec(Zero, Zero, Var 2)));

val Lam(Nat, Rec(Zero, Var 0, Zero)) = subst Zero (Lam(Nat, Rec(Var 1, Var 0, Zero)));
val Lam(Nat, Rec(Zero, Var 1, Zero)) = subst Zero (Lam(Nat, Rec(Var 1, Var 2, Zero)));
val Rec(Zero, Zero, Zero) = step (App(Lam(Nat, Rec(Var 0, Var 0, Zero)), Zero));

val Nat = get (Cons(Nat, Nil)) 0;
val Arr(Nat, Nat) = get (Cons(Nat, Cons(Arr(Nat, Nat), Nil))) 1;
val Nat = get (Cons(Nat, Cons(Arr(Nat, Nat), Nil))) 0;

val Nat = typecheck Nil Nil Zero;
val Nat = typecheck Nil Nil (Succ (Zero));

val Nat = typecheck (Cons(Nat, Nil)) Nil (Var(0));
val Arr(Nat, Nat) = typecheck (Cons(Arr(Nat, Nat), Nil)) Nil (Var(0));
val Arr(Nat, Nat) = typecheck (Cons(Arr(Nat, Nat), Cons(Nat, Nil))) Nil (Var(0));
val Nat = typecheck (Cons(Arr(Nat, Nat), Cons(Nat, Nil))) Nil (Var(1));

val Arr(Nat, Nat) = typecheck Nil Nil (Lam(Nat, Zero));
val Arr(Nat, Nat) = typecheck Nil Nil (Lam(Nat, Succ(Zero)));

val Nat = typecheck Nil Nil (App(Lam(Nat, Zero), Zero));

val Nat = typecheck Nil Nil (App(Lam(Nat, Succ(Zero)), Lam(Nat, Zero)))
          handle TypeMismatch => Nat;

val timesTwo = Rec(Succ(Zero), Zero, Succ(Succ(Var(0 (* prev *)))));
val Nat = typecheck Nil Nil timesTwo;

val Arr(Arr(Nat, Nat), Nat) =
    typecheck Nil Nil (Lam(Arr(Nat, Nat), App(Var(0), Zero)));

val Arr(Nat, Nat) = typecheck Nil Nil (Rec(Zero,
                                       Lam(Nat, Succ(Zero)),
                                       Lam(Nat, Succ(Var(0)))));

val Arr(Nat, Nat) = typecheck Nil Nil (Rec(Succ(Zero),
                                       Lam(Nat, Succ(Zero)),
                                       Lam(Nat, Succ(Var(0)))));

val Arr(Nat, Nat) = typecheck (Cons(Nat, Nil)) Nil (Rec(Var(0),
                                       Lam(Nat, Succ(Zero)),
                                       Lam(Nat, Succ(Var(0)))));


val Nat = typecheck Nil Nil (App(Lam(Arr(Nat, Nat), App(Var(0), Zero)), Zero)) handle TypeMismatch => Nat;

(* Ill-formed; first param must be Nat. *)
val Nat = typecheck Nil Nil (Rec(Lam(Nat, Zero), Lam(Nat, Succ(Zero)), Lam(Nat, Succ(Var(0))))) handle Bind => Nat;

(* Ill-formed; base case type does not match rec case type. *)
val Nat = (typecheck Nil Nil (Rec(Zero, Succ(Zero), Lam(Nat, Succ(Zero))))
          handle TypeMismatch => Nat);

val Arr(Nat, Nat) = typecheck Nil Nil (Lam((TypVar 0), Zero)) handle No => Arr(Nat, Nat);

val Succ(Rec(Zero, Zero, Succ(Var 0))) = step (Rec(Succ(Zero), Zero, Succ(Var 0)));

val Succ(Succ(Rec(Zero, Zero, Succ(Succ(Var 0))))) =
    step (Rec(Succ(Zero), Zero, Succ(Succ(Var 0))));

val Zero = step (Rec(Zero, Zero, Succ(Var 0)));
val Succ(Succ(Zero)) = eval (Rec(Succ(Succ(Zero)), Zero, Succ(Var 0)));
val Succ(Succ(Succ(Succ(Zero)))) =
    eval (Rec(Succ(Succ(Zero)), Zero, Succ(Succ(Var 0))));

val Succ(Succ(Succ(Succ(Zero)))) =
    eval (Rec(App(Lam(Nat, Succ(Var 0)), Succ(Zero)),
              Zero, Succ(Succ(Var 0))));

val Zero = step Zero;
val Succ(Zero) = step (Succ(Zero));
val Lam(Nat, Zero) = step (Lam(Nat, Zero));
val Succ Zero = step (App(Lam(Nat, Succ(Zero)), Zero));
val Succ Zero = step (App(Lam(Nat, Succ(Var(0))), Zero));
val Succ (Succ Zero) = step (App(Lam(Nat, Succ(Var(0))), Succ Zero));
val Succ (Succ (Succ Zero)) = step (App(Lam(Nat, Succ(Var(0))), Succ (Succ Zero)));
val Succ (Succ (Succ Zero)) = step (App(Lam(Nat, Succ(Succ(Var(0)))), Succ Zero));

(* Take in a nat -> nat and apply to zero. Input nat -> nat is Succ *)
val App(Lam(Nat, Succ(Var(0))), Zero) = step (App(Lam(Arr(Nat, Nat), App(Var(0), Zero)),
                                                  Lam(Nat, Succ(Var(0)))));
val Succ Zero = step (App(Lam(Nat, Succ(Var(0))), Zero));

val Succ Zero = eval (App(Lam(Arr(Nat, Nat), App(Var(0), Zero)),
                          Lam(Nat, Succ(Var(0)))));
val Succ (Succ (Succ (Succ Zero))) = eval (Rec(Succ(Succ(Zero)), Zero, Succ(Succ(Var 0))));

val multByThree = Lam(Nat, Rec(Var 0, Zero, Succ(Succ(Succ(Var 0)))));
val Succ (Succ (Succ Zero)) = eval (App(multByThree, Succ Zero))
