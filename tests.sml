structure Tests = struct

open Ast

fun test() = let
open Thon
open A
open Parse;
val testDir = OS.FileSys.getDir() ^ "/tests/";
fun runTest f = (println f; runFile (testDir ^ f));
(* Data Natlist = None | Some(Nat, Natlist) *)
val natlist : typ = TyRec(Scope("natlist",Plus[Unit, Prod [Nat, TypVar ("natlist", 0)]]));

val nilNatList =
    Fold(natlist, PlusNth(0, Plus[Unit, Prod([Nat, natlist])], TmUnit));

val singletonList =
    Fold(natlist, PlusNth(1, Plus[Unit, Prod([Nat, natlist])], Tuple[Zero,
    Fold(natlist, PlusNth(0, Plus[Unit, Prod([Nat, natlist])], TmUnit))]));

val TyRec (Scope("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist", 0)])])) = typeof' [] [] singletonList;

val natlistCons =
    Fn(Prod([Nat, natlist]),
      Scope("natAndNatlist",
        Fold(natlist,
             PlusNth(1,
                 Plus[Unit, Prod([Nat, natlist])],
                 Var ("natAndNatlist", 0)
             )
            )
       ));

val Fn(Prod [Nat,TyRec (Scope("natlist",Plus [Unit, Prod [Nat,TypVar ("natlist", 0)]]))],
       Scope("natAndNatlist", _)) = natlistCons;

val Arr(Prod [Nat,TyRec (Scope("natlist",Plus [Unit, Prod [Nat,TypVar ("natlist", 0)]]))],
        TyRec (Scope("natlist",Plus [Unit, Prod [Nat,TypVar ("natlist", 0)]])))
    = typeof' [] [] natlistCons;

val TyRec (Scope("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist", 0)])])) =
    typeof' [] [] (App(natlistCons, Tuple[Zero, nilNatList]));
(* This should be illtyped since we're applying an int to a function expecting an int * natlist *)
val natlistConsAppliedToZero = App(natlistCons, Zero);
val Nat = typeof' [] [] natlistConsAppliedToZero handle IllTyped => Nat;

val Nat = typeof' [] [] (App(natlistCons, Tuple[Zero, Fn(Nat, Scope("x", Var ("x", 0)))])) handle IllTyped => Nat;
val TyRec (Scope("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist", 0)])])) =
    typeof' [] [] (App(natlistCons, Tuple[Zero, nilNatList]));

val TyRec (Scope("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist", 0)])])) =
    typeof' [] [] (App(natlistCons, Tuple[Zero,
        App(natlistCons, Tuple[Zero, nilNatList])]));
val e = App(natlistCons, Tuple[Zero, nilNatList]);
val singletonList2 = eval e;
val true = (singletonList = singletonList2);

val Impl (Nat,Fn (Nat,Scope("x",Zero)),Some (Scope("t",Arr (TypVar ("t",0),TypVar ("t",0))))) =
    eval (Impl(Nat, Fn(Nat, Scope("x", Zero)), Some(Scope("t", Arr(TypVar ("t", 0), TypVar ("t", 0))))));

val e1 = Impl(Nat, Fn(Nat, Scope("x", Var ("x", 0))), Some(Scope("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))));
val Some(Scope("t",Arr(TypVar ("t", 0), TypVar ("t", 0)))) = typeof' [] [] e1;
val e2 = Impl(Arr(Nat, Nat), Fn(Arr(Nat, Nat), Scope("x", Var ("x", 0))), Some(Scope("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))));
val Some(Scope("t",Arr(TypVar ("t", 0), TypVar ("t", 0)))) = typeof' [] [] e2;
val e4 = Impl(All(Scope("t", Nat)), Fn(All(Scope("t", Nat)), Scope("x", Zero)), Some(Scope("t", Arr(TypVar ("t", 0), Nat))));
val Some(Scope("t",Arr(TypVar ("t", 0), Nat))) = typeof' [] [] e4

val e5 = Impl(Nat, Fn(All(Scope("t", Nat)), Scope("x", Zero)), Some(Scope("t", Arr(All (Scope("t", TypVar ("t", 1))), TypVar ("t", 0)))));
val Some(Scope("t",Arr(All (Scope("t", TypVar ("t", 1))), TypVar ("t", 0)))) = typeof' [] [] e5

val t5 = typeof' [] [] (Fn(All(Scope("t", Nat)), Scope("x", Zero)));
val (Arr(All (Scope("t", Nat)), Nat)) = t5;
val Arr(All (Scope("t", TypVar ("t", 1))), TypVar ("t", 0)) = abstractOutType "t" Nat (Arr(All (Scope("t", Nat)), Nat));

val f = Fn(Arr(Nat, Nat), Scope("x", Zero));
val g = Fn (Nat, Scope("x", Succ (Var ("x", 0))));
val pkg = Impl(Arr(Nat, Nat), f, Some(Scope("t", Arr(TypVar ("t", 0), Nat))));
val Some (Scope("t",Arr(TypVar ("t", 0), Nat))) = typeof' [] [] pkg;

val Some(Scope("t",Arr(TypVar ("t", 0), Nat))) = typeof' [] [] (Impl(Nat, Fn(Nat, Scope("x", Zero)), Some(Scope("t", Arr(TypVar ("t", 0), Nat)))));
val Some(Scope("t",Arr(TypVar ("t", 0), TypVar ("t", 0)))) = typeof' [] [] (Impl(Nat, Fn(Nat, Scope("x", Zero)), Some(Scope("t", Arr(TypVar ("t", 0), TypVar ("t", 0))))));
val Nat = typeof' [] [] (Impl(Nat, Fn(Nat, Scope("x", Zero)), Some(Scope("t", TypVar ("t", 0))))) handle IllTyped => Nat;

(* Define identity package; can convert Nat to internal repr type and back. *)
val idid = Tuple[Fn(Nat, Scope("x", Var ("x", 0))), Fn(Nat, Scope("x", Var ("x", 0)))];
val Prod([Arr(Nat, Nat), Arr(Nat, Nat)]) = typeof' [] [] idid;
val inoutpkg = Impl(Nat, idid, Some(Scope("t", Prod([Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat)]))));
val Some(Scope("t",Prod([Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat)]))) = typeof' [] [] inoutpkg;
val Nat = typeof' [] [] (Use(inoutpkg, Scope("s", Scope("pkg", App(ProdNth(1, Var ("x", 0)), App(ProdNth(0, Var ("x", 0)), Zero))))));
val true = isval inoutpkg;
(* Dynamics *)
val App
    (ProdNth (1, Tuple [Fn (Nat,Scope("x",Var ("x", 0))),Fn (Nat,Scope("x",Var ("x", 0)))]),
     App (ProdNth (0, Tuple [Fn (Nat,Scope("x",Var ("x", 0))),Fn (Nat,Scope("x",Var ("x", 0)))]),Zero))
    = step (Use(inoutpkg, Scope("s", Scope("pkg", App(ProdNth(1, Var ("x", 0)), App(ProdNth(0, Var ("x", 0)), Zero))))));

val Zero = eval (Use(inoutpkg, Scope("s", Scope("pkg", App(ProdNth(1, Var ("x", 0)), App(ProdNth(0, Var ("x", 0)), Zero))))));

val leftandback = Tuple[Fn(Nat, Scope("x", Tuple[Var ("x", 0), Zero])), Fn(Prod([Nat, Nat]), Scope("x", ProdNth (0, Var ("x", 0))))];
val Prod ([Arr (Nat,Prod [Nat, Nat]),Arr (Prod [Nat, Nat],Nat)]) = typeof' [] [] leftandback;
val inoutpkg2 = Impl(Prod([Nat, Nat]), leftandback, Some(Scope("t", Prod ([Arr (Nat,TypVar ("t", 0)),Arr (TypVar ("t", 0),Nat)]))));
val Some(Scope("t",Prod([Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat)]))) = typeof' [] [] inoutpkg2;
val Nat = typeof' [] [] (Use(inoutpkg2, Scope("s", Scope("pkg", App(ProdNth(1, Var ("x", 0)), App(ProdNth(0, Var ("x", 0)), Zero))))));
val Zero = eval (Use(inoutpkg2, Scope("s", Scope("pkg", App(ProdNth(1, Var ("x", 0)), App(ProdNth(0, Var ("x", 0)), Zero))))));

val double = Fn(Nat, Scope("x", Rec(Var ("x", 0), Zero, Scope("prev", Succ (Succ (Var ("x", 0)))))));
val Succ (Succ Zero) = eval (App(double, (Succ Zero)));

val All(Scope("t", TypVar ("t", 1))) = abstractOutType "t" Nat (All(Scope("t", Nat)));
val TypVar ("t", 0) = abstractOutType "t" Nat Nat;
val Arr(TypVar ("t", 0), Nat)= abstractOutType "t" (Arr(Nat, Nat)) (Arr(Arr(Nat, Nat), Nat));
val Some(Scope("t",Arr(TypVar ("t", 1), Nat))) = abstractOutType "t" (Arr(Nat, Nat)) (Some(Scope("t",Arr(Arr(Nat, Nat), Nat))));
val All(Scope("t", Arr(TypVar ("t", 1), Nat))) = abstractOutType "t" (Arr(Nat, Nat)) (All(Scope("t", Arr(Arr(Nat, Nat), Nat))));
val Some(Scope("t",All(Scope("t", Arr(TypVar ("t", 2), Nat))))) = abstractOutType "t" (Arr(Nat, Nat)) (Some(Scope("t",All(Scope("t", Arr(Arr(Nat, Nat), Nat))))));

val polymorphicIdFn = TypFn(Scope("t", Fn(TypVar ("t", 0), Scope("x", Var ("x", 0)))));

val Fn(Nat, Scope("x", Var ("x", 0))) = step (TypApp(Nat, polymorphicIdFn));
val Fn(Arr(Nat, Nat), Scope("x", Var ("x", 0))) = step (TypApp(Arr(Nat, Nat), polymorphicIdFn));
val TypFn (Scope("t", Fn (TypVar ("t", 0), Scope("x", Var ("x", 0))))) = step (TypApp(Nat, TypFn(Scope("t", polymorphicIdFn))))
val TypApp(Nat, TypFn(Scope("t", (Fn (TypVar ("t", 0), Scope("x", Var ("x", 0))))))) = step (TypApp(Nat, TypApp(Nat, TypFn(Scope("t", polymorphicIdFn)))))
val TypFn(Scope("t", Fn(Arr(Nat, TypVar ("t", 0)), Scope("x", Var ("x", 0))))) = step (TypApp(Nat, TypFn(Scope("t", TypFn(Scope("t", Fn(Arr(TypVar ("t", 1), TypVar ("t", 0)), Scope("x", Var ("x", 0)))))))));
val Fn(Nat, Scope("x", Var ("x", 0))) = eval (TypApp(Nat, TypApp(Nat, TypFn(Scope("t", polymorphicIdFn)))));

val Succ Zero = eval (App(TypApp(Nat, polymorphicIdFn), Succ(Zero)));

val TypFn(Scope("t", Zero)) = step (TypFn(Scope("t", Zero)));
val true = isval (Fn(Nat, Scope("x", TypFn(Scope("t", Zero)))));
val (TypFn (Scope("t", Zero))) = step (App(Fn(Nat, Scope("x", TypFn(Scope("t", Zero)))), Zero));

val Nat = typSubst 0 Nat (TypVar ("t", 0)); (* Tho this isn't actually a well-formed type *)
val Arr(Nat, Nat) = typSubst 0 (Arr(Nat, Nat)) (TypVar ("t", 0)); (* Tho this isn't actually a well-formed type *)
val false = istype [] (TypVar ("t", 0));
val All(Scope("t", Nat)) = typSubst 0 Nat (All(Scope("t", TypVar ("t", 1))));
val Some(Scope("t",Nat)) = typSubst 0 Nat (Some(Scope("t",TypVar ("t", 1))));
val Some(Scope("t",Some(Scope("t",TypVar ("t", 1))))) = typSubst 0 Nat (Some(Scope("t",Some(Scope("t",TypVar ("t", 1))))));
val true = istype [] (All(Scope("t", TypVar ("t", 0))));
val true = istype [] (Some(Scope("t",TypVar ("t", 0))));
val All(Scope("t", Arr(Nat, (All(Scope("t", Nat)))))) = typSubst 0 (All(Scope("t", Nat))) (All(Scope("t", Arr(Nat, TypVar ("t", 1)))));
val All(Scope("t", Arr(Nat, (Some(Scope("t",Nat)))))) = typSubst 0 (Some(Scope("t",Nat))) (All(Scope("t", Arr(Nat, TypVar ("t", 1)))));

val Nat = typeof' [] [] (TypApp(TypVar ("t", 0), Zero)) handle IllTyped => Nat;
val All(Scope("t", Arr(TypVar ("t", 0), Nat))) = typeof' [] [] (TypFn(Scope("t", Fn(TypVar ("t", 0), Scope("x", Zero)))));
val Arr(Arr(Nat, Nat), Nat) = typeof' [] [] (TypApp(Arr(Nat, Nat), (TypFn(Scope("t", Fn(TypVar ("t", 0), Scope("x", Zero)))))));
val Nat = typeof' [] [] (TypApp(Arr(Nat, Nat), (TypFn(Scope("t", Fn(TypVar ("t", 1), Scope("x", Zero))))))) handle IllTypedMsg _ => Nat;


val All(Scope("t", Nat)) = typeof' [] [] (TypFn(Scope("t", Zero))); (* polymorphic zero *)
(* polymorphic id function :) *)
val All(Scope("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))) =
    typeof' [] [] (TypFn(Scope("t", Fn(TypVar ("t", 0), Scope("x", Var ("x", 0))))));
val Arr(Nat, All(Scope("t", Arr(TypVar ("t", 0), TypVar ("t", 0))))) =
    typeof' [] [] (Fn(Nat, Scope("x", TypFn(Scope("t", Fn(TypVar ("t", 0), Scope("x", Var ("x", 0))))))));
val Arr(Nat, All(Scope("t", Arr(TypVar ("t", 0), TypVar ("t", 0))))) =
    typeof' [] [] (Fn(Nat, Scope("x", TypFn(Scope("t", Fn(TypVar ("t", 0), Scope("x", Var ("x", 0))))))));
(* Nested type variables *)
val All(Scope("t", All(Scope("t", Arr(TypVar ("t", 1),Nat))))) =
    typeof' [] [] (TypFn(Scope("t", TypFn(Scope("t", Fn(TypVar ("t", 1), Scope("x", Zero)))))))
val All(Scope("t", All(Scope("t", Arr(TypVar ("t", 1), TypVar ("t", 1)))))) =
    typeof' [] [] (TypFn(Scope("t", TypFn(Scope("t", Fn(TypVar ("t", 1), Scope("x", Var ("x", 0))))))))

val true = istype [] Nat;
val false = istype [] (TypVar ("t", 0)); (* Unbound type variable *)
val false = istype [] (Arr(TypVar ("t", 0), Nat)); (* Unbound type variable *)
val false = istype [] (Arr(Nat, TypVar ("t", 0))); (* Unbound type variable *)
val true = istype [] (All(Scope("t", Nat)));
val true = istype [] (All(Scope("t", TypVar ("t", 0))));
val true = istype [] (All(Scope("t", Arr(TypVar ("t", 0), Nat))));
val true = istype [] (All(Scope("t", Arr(Nat, TypVar ("t", 0)))));
val false = istype [] (All(Scope("t", Arr(Nat, TypVar ("t", 1))))); (* Unbound *)
val true = istype [] (All(Scope("t", All(Scope("t", Arr(Nat, TypVar ("t", 1))))))); (* Bound *)

val true = isval Zero;
val true = isval (Succ(Zero));
val true = isval (Fn(Nat, Scope("x", Succ(Zero))));
val true = isval (Fn(Nat, Scope("x", Zero)));
val true = isval (Fn(Nat, Scope("x", Succ(Var("x", 0)))));
val false = isval (App(Fn(Nat, Scope("x", Zero)), Zero));

val Zero = expSubst 0 Zero Zero;
val Succ Zero = expSubst 0 Zero (Succ Zero);
val (Fn(Nat, Scope("x", Var ("x", 0)))) = expSubst 0 (Succ Zero) (Fn(Nat, Scope("x", Var ("x", 0))));
val (Var ("y", 1)) = expSubst 0 (Succ Zero) (Var ("y", 1));
val Tuple [Var ("y",1),Succ Zero] = expSubst 0 (Succ Zero) (Tuple([Var ("y", 1), Var("x", 0)]));
val Fn(Nat, Scope("x", Var ("x", 0))) = expSubst 0 (Succ Zero) (Fn(Nat, Scope("x", Var ("x", 0))));
val Fn(Nat, Scope("x", (Succ Zero))) = expSubst 0 (Succ Zero) (Fn(Nat, Scope("x", Var("y", 1))));
val App(Fn(Nat, Scope("x", Succ Zero)), (Succ Zero)) =
    expSubst 0 (Succ Zero) (App(Fn(Nat, Scope("x", Var ("y", 1))), (Var ("x", 0))));

val Fn(Nat, Scope("y", Zero)) = expSubst 0 Zero (Fn(Nat, Scope("y", Var ("x", 1))));
val Fn(Nat, Scope("x", Succ Zero)) = expSubst 0 (Succ Zero) (Fn(Nat, Scope("x", Var ("x", 1))));
val Fn(Nat, Scope("x", Fn(Nat, Scope("x", Succ Zero)))) = expSubst 0 (Succ Zero) (Fn(Nat, Scope("x", Fn(Nat, Scope("x", Var ("z", 2))))));
val Fn(Nat, Scope("x", Rec(Zero, Zero, Scope("prev", Succ Zero)))) = expSubst 0 (Succ Zero) (Fn(Nat, Scope("x", Rec(Zero, Zero, Scope("prev", Var ("z", 2))))));

val Fn(Nat, Scope("x", Rec (Zero,
                       Var ("x",0),
                       Scope("prev", Zero)))) : exp =
    expSubst 0 Zero (Fn(Nat, Scope("x", Rec(Var ("x", 1),
                                  Var ("x", 0),
                                  Scope("prev", Zero)))));

val Fn(Nat, Scope("x", Rec(Zero, Var ("x", 2), Scope("prev", Zero)))) = expSubst 0 Zero (Fn(Nat, Scope("x", Rec(Var ("x", 1), Var ("x", 2), Scope("prev", Zero)))));
val Rec(Zero, Zero, Scope("prev", Zero)) = step (App(Fn(Nat, Scope("x", Rec(Var ("x", 0), Var ("x", 0), Scope("prev", Zero)))), Zero));

val Nat = get [Nat] 0;
val Arr(Nat, Nat) = get [Nat, Arr(Nat, Nat)] 1;
val Nat = get [Nat, Arr(Nat, Nat)] 0;

val Nat = typeof' [] [] Zero;
val Nat = typeof' [] [] (Succ (Zero));

val Nat = typeof' [Nat] [] (Var("x", 0));
val Arr(Nat, Nat) = typeof' [Arr(Nat, Nat)] [] (Var("x", 0));
val Arr(Nat, Nat) = typeof' [Arr(Nat, Nat), Nat] [] (Var("x", 0));
val Nat = typeof' [Arr(Nat, Nat), Nat] [] (Var("x", 1));

val Arr(Nat, Nat) = typeof' [] [] (Fn(Nat, Scope("x", Zero)));
val Arr(Nat, Nat) = typeof' [] [] (Fn(Nat, Scope("x", Succ(Zero))));

val Nat = typeof' [] [] (App(Fn(Nat, Scope("x", Zero)), Zero));

val Nat = typeof' [] [] (App(Fn(Nat, Scope("x", Succ(Zero))), Fn(Nat, Scope("x", Zero))))
          handle IllTyped => Nat;

val timesTwo = Rec(Succ(Zero), Zero, Scope("prev", Succ(Succ(Var("prev", 0)))));
val Nat = typeof' [] [] timesTwo;

val Arr(Arr(Nat, Nat), Nat) =
    typeof' [] [] (Fn(Arr(Nat, Nat), Scope("f", App(Var("f", 0), Zero))));

val Arr(Nat, Nat) = typeof' [] [] (Rec(Zero,
                                       Fn(Nat, Scope("x", Succ(Zero))),
                                       Scope("prev", Fn(Nat, Scope("x", Succ(Var("x", 0)))))));
val Arr(Nat, Nat) = typeof' [] [] (Rec(Succ(Zero),
                                       Fn(Nat, Scope("x", Succ(Zero))),
                                       Scope("prev", Fn(Nat, Scope("x", Succ(Var("x", 0)))))));

val Arr(Nat, Nat) = typeof' [Nat] [] (Rec(Var("dne", 0),
                                       Fn(Nat, Scope("x", Succ(Zero))),
                                       Scope("prev", Fn(Nat, Scope("x", Succ(Var("x", 0)))))));


val Nat = typeof' [] [] (App(Fn(Arr(Nat, Nat), Scope("f", App(Var("f", 0), Zero))), Zero)) handle IllTyped => Nat;

(* Ill-formed; first param must be Nat. *)
val Nat = typeof' [] [] (Rec(Fn(Nat, Scope("x", Zero)),
                               Fn(Nat, Scope("x", Succ(Zero))),
                               Scope("prev", Fn(Nat, Scope("x", Succ(Var("x", 0))))))) handle Bind => Nat;

(* Ill-formed; base case type does not match rec case type. *)
val Nat = (typeof' [] [] (Rec(Zero,
                                Succ(Zero),
                                Scope("prev", Fn(Nat, Scope("x", Succ(Zero))))))
          handle IllTyped => Nat);

val Arr(Nat, Nat) = typeof' [] [] (Fn((TypVar ("t", 0)), Scope("x", Zero))) handle IllTypedMsg _ => Arr(Nat, Nat);

val Succ(Rec(Zero, Zero, Scope("prev", Succ(Var("prev", 0))))) = step (Rec(Succ(Zero), Zero, Scope("prev", Succ(Var ("prev", 0)))));

val Succ(Succ(Rec(Zero, Zero, Scope("prev", Succ(Succ(Var ("prev", 0))))))) =
    step (Rec(Succ(Zero), Zero, Scope("prev", Succ(Succ(Var ("prev", 0))))));

val Zero = step (Rec(Zero, Zero, Scope("prev", Succ(Var ("prev", 0)))));
val Succ(Succ(Zero)) = eval (Rec(Succ(Succ(Zero)), Zero, Scope("prev", Succ(Var ("prev", 0)))));
val Succ(Succ(Succ(Succ(Zero)))) =
    eval (Rec(Succ(Succ(Zero)), Zero, Scope("prev", Succ(Succ(Var ("prev", 0))))));

val Succ(Succ(Succ(Succ(Zero)))) =
    eval (Rec(App(Fn(Nat, Scope("x", Succ(Var ("x", 0)))), Succ(Zero)),
              Zero, Scope("prev", Succ(Succ(Var ("prev", 0))))));

val Zero = step Zero;
val Succ(Zero) = step (Succ(Zero));
val Fn(Nat, Scope("x", Zero)) = step (Fn(Nat, Scope("x", Zero)));
val Succ Zero = step (App(Fn(Nat, Scope("x", Succ(Zero))), Zero));
val Succ Zero = step (App(Fn(Nat, Scope("x", Succ(Var("x", 0)))), Zero));
val Succ (Succ Zero) = step (App(Fn(Nat, Scope("x", Succ(Var("x", 0)))), Succ Zero));
val Succ (Succ (Succ Zero)) = step (App(Fn(Nat, Scope("x", Succ(Var("x", 0)))), Succ (Succ Zero)));
val Succ (Succ (Succ Zero)) = step (App(Fn(Nat, Scope("x", Succ(Succ(Var("x", 0))))), Succ Zero));
(* Take in a nat -> nat and apply to zero. Input nat -> nat is Succ *)
val App(Fn(Nat, Scope("x", Succ(Var("x", 0)))), Zero) = step (App(Fn(Arr(Nat, Nat), Scope("x", App(Var("x", 0), Zero))),
                                                  Fn(Nat, Scope("x", Succ(Var("x", 0))))));
val Succ Zero = step (App(Fn(Nat, Scope("x", Succ(Var("x", 0)))), Zero));

val Succ Zero = eval (App(Fn(Arr(Nat, Nat), Scope("x", App(Var("x", 0), Zero))),
                          Fn(Nat, Scope("x", Succ(Var("x", 0))))));
val Succ (Succ (Succ (Succ Zero))) = eval (Rec(Succ(Succ(Zero)), Zero, Scope("prev", Succ(Succ(Var ("prev", 0))))));

val multByThree = Fn(Nat, Scope("x", Rec(Var ("x", 0), Zero, Scope("prev", Succ(Succ(Succ(Var("prev", 0))))))));
val Succ (Succ (Succ Zero)) = eval (App(multByThree, Succ Zero));

val
  Tuple
      [TypFn (Scope("t",Fn (TypVar ("t",0), Scope("x",Var ("x",0))))),
       Fn (Nat, Scope("x",Var ("x",0))),
       TypFn (Scope("t",Fn (TypVar ("t",0), Scope("x",Var ("x",0)))))] : exp =
step (A.Tuple [polymorphicIdFn, A.TypApp(Nat, polymorphicIdFn), polymorphicIdFn]);

val simpleNestedDatatypes =
  Data
    ("typ",["Arr"],[TypVar ("typ",0)],
     Data ("exp",["Fn"],[TypVar ("typ",1)],Zero));

val elaborated = elaborateDatatypes simpleNestedDatatypes;

val Nat = typSubst 0 Nat (TypVar ("typ",0));
val Nat = typSubst 1 Nat (TypVar ("typ",1));
val Zero = expSubst 0 Zero (Var("x", 0));

val TypVar("typ", 1) = typSubst 0 Nat (TypVar ("typ",1));
val TypVar("typ", 2) = typSubst 1 Nat (TypVar ("typ",2));
val Var("x", 1) = expSubst 0 Zero (Var("x", 1));
val Var("x", 2) = expSubst 1 Zero (Var("x", 2));

(* ---- File-based tests ---- *)
(* Each test file is parsed, typechecked, and evaluated *)

val Zero = runTest "zero.thon";
val Succ Zero = runTest "succ.thon";
val TmUnit = runTest "unit.thon";
val Tuple [Zero, Succ Zero] = runTest "tuple.thon";
val Tuple [Zero, Tuple [Succ Zero, Succ (Succ Zero)]] = runTest "nested_tuple.thon";
val Zero = runTest "fst.thon";
val Tuple [Succ Zero, Succ (Succ Zero)] = runTest "snd.thon";
val Succ Zero = runTest "fst_snd.thon";
val Succ Zero = runTest "app.thon";
val Succ Zero = runTest "higher_order.thon";
val Tuple [Zero, Zero] = runTest "pair_id.thon";
val Zero = runTest "let.thon";
val Zero = runTest "nested_let.thon";
val Succ Zero = runTest "fun.thon";
val Succ Zero = runTest "ifz_zero.thon";
val Zero = runTest "ifz_succ.thon";
val Succ Zero = runTest "decr.thon";
val Succ Zero = runTest "poly_id.thon";
val Zero = runTest "nested_poly.thon";
val Fn (Nat, Scope(_, Var (_, 0))) = runTest "poly_app.thon";
val TypFn (Scope(_, Fn (Arr (Nat, TypVar(_, 0)), Scope(_, Var (_, 0))))) = runTest "poly_app2.thon";
val _ = runTest "poly_forall.thon";
val _ = runTest "package.thon";
val _ = runTest "open.thon";
val _ = runTest "existential_id.thon";
val TypFn (Scope(_, Fn (TypVar (_, 0), Scope(_, Var (_, 0))))) = runTest "use_poly.thon";
val Succ Zero = runTest "iseven.thon";
val Succ Zero = runTest "fold_unfold.thon";
val Zero = runTest "data_list.thon";
val Zero = runTest "data_three_summands.thon";
val Zero = runTest "data_one_summand.thon";
val Zero = runTest "data_ternary_tree.thon";
val Zero = runTest "data_unary_binary_tree.thon";
val Succ (Succ Zero) = runTest "setget.thon";
val TypFn (Scope(_, Zero)) = runTest "aeqv.thon";
(* val Zero = runTest "data_nested.thon"; *) (* TODO: nested data type error *)
(* TODO: these fail with "Function arg type is not a type" - DBI issue with nested data+let *)
(* val Zero = runTest "dbi_management.thon"; *)
(* val Zero = runTest "data_expmap.thon"; *)
val Succ Zero = runTest "option.thon";
val Zero = runTest "option_none.thon";
val Zero = runTest "case_left.thon";
val Succ Zero = runTest "case_right.thon";
val PlusNth (0, _, Zero) = runTest "sum_id.thon";
val Succ Zero = runTest "if.thon";
val Succ Zero = runTest "collatz.thon";
val _ = runTest "natlist_pkg.thon";
val Zero = runTest "manual_datatype.thon";
val Succ (Succ (Succ (Succ Zero))) = runTest "lru_cache.thon";

in
()
end

end
