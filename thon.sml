exception TypeMismatch

datatype Typ = Nat | Arr of Typ * Typ
               
datatype Exp = Zero
             | Var of int
             | Succ of Exp
             | Lam of (*argType*) Typ * (*funcBody*) Exp
             | App of Exp * Exp
             | Rec of (*prev*) int * (*prevRec*) int * Exp

fun typecheck e =
    case e
     of  Zero => Nat
       | Var x => Nat
       | Succ e2 => (typecheck e2)
       | Lam (argType, funcBody) => Arr (argType, typecheck funcBody)
       | App (f, n) => let val Arr (d, c) = typecheck f
                           val argType = typecheck n
                       in
                           if c <> argType then raise TypeMismatch
                           else c
                       end
       | Rec (prev, precRec, e) => Nat (*TODO*)

val Nat = typecheck Zero;
val Nat = typecheck (Var 5);
val Nat = typecheck (Succ (Var 5));
val Nat = typecheck (Succ (Zero));

val Arr(Nat, Nat) = typecheck (Lam(Nat, Zero));
val Arr(Nat, Nat) = typecheck (Lam(Nat, Var(5)));
val Arr(Nat, Nat) = typecheck (Lam(Nat, Succ(Zero)));
val Arr(Nat, Nat) = typecheck (Lam(Nat, Succ(Var(5))));

val Nat = typecheck (App(Lam(Nat, Zero), Zero));
val Nat = typecheck (App(Lam(Nat, Succ(Var(5))), Zero));

val Nat = typecheck (App(Lam(Nat, Succ(Var(5))), Lam(Nat, Zero)))
          handle TypeMismatch => Nat;
