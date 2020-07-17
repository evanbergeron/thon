(* A system F interpreter *)
exception TypeMismatch
exception No
exception Unimplemented

datatype Typ = Nat
             | TypVar of int
             | Arr of Typ * Typ
             | All of Typ (* binds *)

datatype Idx = int

datatype Exp = Zero
             | Var of int (* idx into ctx *)
             | Succ of Exp
             | Lam of Typ (*argType*) * Exp (*funcBody*)
             | App of Exp * Exp
             | Rec of Exp (*i : Nat*) * Exp (*baseCase: t*) * Exp (*recCase - binds*)
             | TypAbs of Exp (* binds type variable *)
             | TypApp of Exp


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
      | All t' => istype (Cons(42, typeCtx)) t'


fun typecheck ctx typCtx e =
    case e
     of  Zero => Nat
       | Var i => get ctx i
       | Succ e2 => (typecheck ctx typCtx e2)
       | Lam (argType, funcBody) =>
            Arr (argType, typecheck (Cons(argType, ctx)) typCtx funcBody)
       | App (f, n) =>
            let val Arr (d, c) = typecheck ctx typCtx f
                val argType = typecheck ctx typCtx n
            in
                if d <> argType then raise TypeMismatch
                else c
            end
       | Rec (i, baseCase, recCase) =>
            let val Nat = typecheck ctx typCtx i
                val t = typecheck ctx typCtx baseCase
                val t2 = typecheck (Cons(t, ctx)) typCtx recCase
            in
                if t <> t2 then raise TypeMismatch else t
            end
       | TypAbs e => raise Unimplemented
       | TypApp e => raise Unimplemented


fun isVal e =
    case e of
        Zero => true
      | Succ(n) => isVal n
      | Lam(_, _) => true
      | _ => false


fun subst' src dst bindingDepth =
    case dst
     of  Zero => Zero
       | Var n  => if n = bindingDepth then src else Var(n) (* ? *)
       | Succ e2 => Succ (subst' src e2 bindingDepth)
       | Lam (t, f) => Lam(t, (subst' src f (bindingDepth+1)))
       | App (f, n) => App((subst' src f bindingDepth), (subst' src n bindingDepth))
       | Rec (i, baseCase, recCase) => raise Unimplemented
       | TypAbs e => raise Unimplemented
       | TypApp e => raise Unimplemented


fun subst src dst = subst' src dst 0


fun step e =
    let val _ = typecheck Nil Nil e in
    if isVal e then e else
    case e of
        Succ(n) => if not (isVal n) then Succ(step n) else e
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
      | TypAbs e => raise Unimplemented
      | TypApp e => raise Unimplemented
      | _ => if (isVal e) then e else raise No
    end


fun eval e = if isVal e then e else eval (step e)


(******* Tests *******)

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
val Succ Zero = subst (Succ Zero) (Var 0);
val (Var 1) = subst (Succ Zero) (Var 1);
val Lam(Nat, Var 0) = subst (Succ Zero) (Lam(Nat, Var 0));
val Lam(Nat, (Succ Zero)) = subst (Succ Zero) (Lam(Nat, Var 1));
val App(Lam(Nat, Succ Zero), (Succ Zero)) =
    subst (Succ Zero) (App(Lam(Nat, Var 1), (Var 0)));

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
