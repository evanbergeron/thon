exception TypeMismatch
exception No

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

val Nat = get (Cons(Nat, Nil)) 0;
val Arr(Nat, Nat) = get (Cons(Nat, Cons(Arr(Nat, Nat), Nil))) 1;
val Nat = get (Cons(Nat, Cons(Arr(Nat, Nat), Nil))) 0;

fun typecheck ctx e =
    case e
     of  Zero => Nat
       | Var i => get ctx i
       | Succ e2 => (typecheck ctx e2)
       | Lam (argType, funcBody) => Arr (argType, typecheck ctx funcBody)
       | App (f, n) => let val Arr (d, c) = typecheck ctx f
                           val argType = typecheck ctx n
                       in
                           if c <> argType then raise TypeMismatch
                           else c
                       end
       | Rec (i, baseCase, recCase) =>
            let val Nat = typecheck ctx i 
                val t = typecheck ctx baseCase
            in
                typecheck (Cons(t, ctx)) recCase
            end 

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
