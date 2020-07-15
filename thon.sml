exception TypeMismatch
exception No
exception Unimplemented

datatype Typ = Nat | Arr of Typ * Typ

datatype Idx = int

datatype Exp = Zero
             | Var of int (* idx into ctx *)
             | Succ of Exp
             | Lam of Typ (*argType*) * Exp(*funcBody*)
             | App of Exp * Exp
             | Rec of Exp (*i : Nat*) * Exp (*baseCase: t*) * Exp (*recCase*)

(* Holds typing assertions we already know. Head of the list
 * represents the type of the variable most recently seen. (The
 * "lowest" scope variable). *)
datatype Ctx = Nil | Cons of Typ * Ctx

fun get ctx i =
    case ctx of
        Nil => raise No
      | Cons (h, t) => if i = 0 then h else get t (i-1)

fun typecheck ctx e =
    case e
     of  Zero => Nat
       | Var i => get ctx i
       | Succ e2 => (typecheck ctx e2)
       | Lam (argType, funcBody) => Arr (argType, typecheck (Cons(argType, ctx)) funcBody)
       | App (f, n) => let val Arr (d, c) = typecheck ctx f
                           val argType = typecheck ctx n
                       in
                           if d <> argType then raise TypeMismatch
                           else c
                       end
       | Rec (i, baseCase, recCase) =>
            let val Nat = typecheck ctx i
                val t = typecheck ctx baseCase
                val t2 = typecheck (Cons(t, ctx)) recCase
            in
                if t <> t2 then raise TypeMismatch else t
            end


fun isVal e =
    case e of
        Zero => true
      | Succ(n) => isVal n
      | Lam(_, _) => true
      | _ => false

val true = isVal Zero;
val true = isVal (Succ(Zero));
val true = isVal (Lam(Nat, Succ(Zero)));
val true = isVal (Lam(Nat, Zero));
val true = isVal (Lam(Nat, Succ(Var(0))));
val false = isVal (App(Lam(Nat, Zero), Zero));

fun subst' src dst bindingDepth =
    case dst
     of  Zero => Zero
       | Var n  => if n = bindingDepth then src else Var(n) (* ? *)
       | Succ e2 => Succ (subst' src e2 bindingDepth)
       | Lam (t, f) => Lam(t, (subst' src f (bindingDepth+1)))
       | App (f, n) => App((subst' src f bindingDepth), (subst' src n bindingDepth))
       | Rec (i, baseCase, recCase) => raise Unimplemented

fun subst src dst = subst' src dst 0

fun step e =
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
      | _ => e (* TODO *)

val Zero = step Zero;
val Succ(Zero) = step (Succ(Zero));
val Lam(Nat, Zero) = step (Lam(Nat, Zero));
val Succ Zero = step (App(Lam(Nat, Succ(Zero)), Zero));
val Succ Zero = step (App(Lam(Nat, Succ(Var(0))), Zero));
val Succ (Succ Zero) = step (App(Lam(Nat, Succ(Var(0))), Succ Zero));
val Succ (Succ (Succ Zero)) = step (App(Lam(Nat, Succ(Var(0))), Succ (Succ Zero)));
val Succ (Succ (Succ Zero)) = step (App(Lam(Nat, Succ(Succ(Var(0)))), Succ Zero));

val _ = step (App(Lam(Arr(Nat, Nat), App(Var(0), Zero)),
                  Zero));

(******* Tests *******)

val Nat = get (Cons(Nat, Nil)) 0;
val Arr(Nat, Nat) = get (Cons(Nat, Cons(Arr(Nat, Nat), Nil))) 1;
val Nat = get (Cons(Nat, Cons(Arr(Nat, Nat), Nil))) 0;

val Nat = typecheck Nil Zero;
val Nat = typecheck Nil (Succ (Zero));

val Nat = typecheck (Cons(Nat, Nil)) (Var(0));
val Arr(Nat, Nat) = typecheck (Cons(Arr(Nat, Nat), Nil)) (Var(0));
val Arr(Nat, Nat) = typecheck (Cons(Arr(Nat, Nat), Cons(Nat, Nil))) (Var(0));
val Nat = typecheck (Cons(Arr(Nat, Nat), Cons(Nat, Nil))) (Var(1));

val Arr(Nat, Nat) = typecheck Nil (Lam(Nat, Zero));
val Arr(Nat, Nat) = typecheck Nil (Lam(Nat, Succ(Zero)));

val Nat = typecheck Nil (App(Lam(Nat, Zero), Zero));

val Nat = typecheck Nil (App(Lam(Nat, Succ(Zero)), Lam(Nat, Zero)))
          handle TypeMismatch => Nat;

val timesTwo = Rec(Succ(Zero), Zero, Succ(Succ(Var(0 (* prev *)))));
val Nat = typecheck Nil timesTwo;

val Arr(Arr(Nat, Nat), Nat) =
    typecheck Nil (Lam(Arr(Nat, Nat), App(Var(0), Zero)));

val Arr(Nat, Nat) = typecheck Nil (Rec(Zero,
                                       Lam(Nat, Succ(Zero)),
                                       Lam(Nat, Succ(Var(0)))));

val Arr(Nat, Nat) = typecheck Nil (Rec(Succ(Zero),
                                       Lam(Nat, Succ(Zero)),
                                       Lam(Nat, Succ(Var(0)))));

val Arr(Nat, Nat) = typecheck (Cons(Nat, Nil)) (Rec(Var(0),
                                       Lam(Nat, Succ(Zero)),
                                       Lam(Nat, Succ(Var(0)))));


val Nat = typecheck Nil (App(Lam(Arr(Nat, Nat), App(Var(0), Zero)), Zero)) handle TypeMismatch => Nat;

(* Ill-formed; first param must be Nat. *)
val Nat = typecheck Nil (Rec(Lam(Nat, Zero), Lam(Nat, Succ(Zero)), Lam(Nat, Succ(Var(0))))) handle Bind => Nat;

(* Ill-formed; base case type does not match rec case type. *)
val Nat = (typecheck Nil (Rec(Zero, Succ(Zero), Lam(Nat, Succ(Zero))))
          handle TypeMismatch => Nat);
