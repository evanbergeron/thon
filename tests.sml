structure Tests = struct

open Ast

fun test() = let
open Thon
open A;
val exDir = OS.FileSys.getDir() ^ "/examples/";
fun parseEx f = parseFile (exDir ^ f);
fun runEx f = (println f; runFile (exDir ^ f));
(* Data Natlist = None | Some(Nat, Natlist) *)
val natlist : typ = TyRec(Scope("natlist",Plus[Unit, Prod [Nat, TypVar ("natlist", 0)]]));
val Fn (TyRec (Scope("l",Plus [Unit,Prod [Nat,TypVar ("l", 0)]])), Scope("natlist", Var ("natlist",0))) =
    parse "\\ natlist : (u l. (unit ||  (nat * l))) -> natlist";

(* id function on natlists *)
val TypApp
    (TyRec (Scope("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist",0)])])),
     TypFn (Scope("s",Fn (TypVar ("s",0), Scope("x",Var ("x",0)))))) : Ast.exp =
    parse "((poly s -> \\ x : s -> x) (u natlist. (unit || (nat * natlist))))";
val nilNatList =
    Fold(natlist, PlusLeft(Plus[Unit, Prod([Nat, natlist])], TmUnit));

val parsedConsNatList = parseEx "emptynatlist.thon";

val true = (nilNatList = parsedConsNatList);

val TmUnit : Ast.exp = parse "unit";

val singletonList =
    Fold(natlist, PlusRight(Plus[Unit, Prod([Nat, natlist])], Pair(Zero,
    Fold(natlist, PlusLeft(Plus[Unit, Prod([Nat, natlist])], TmUnit)))));

val TyRec (Scope("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist", 0)])])) = typeof' [] [] singletonList;

val natlistCons =
    Fn(Prod([Nat, natlist]),
      Scope("natAndNatlist",
        Fold(natlist,
             PlusRight(
                 Plus[Unit, Prod([Nat, natlist])],
                 Var ("natAndNatlist", 0)
             )
            )
       ));

val Fn(Prod [Nat,TyRec (Scope("natlist",Plus [Unit, Prod [Nat,TypVar ("natlist", 0)]]))],
     Scope("natAndNatlist",
     Fold (TyRec (Scope("natlist",Plus [Unit, Prod [Nat,TypVar ("natlist", 0)]])),
        PlusRight
          (Plus ([Unit, Prod [Nat,TyRec (Scope("natlist",Plus [Unit, Prod [Nat,TypVar ("natlist", 0)]]))]]),
           Var ("natAndNatlist", 0))))) : Ast.exp =
    parseEx "natlistcons.thon";

val parsedNatlistCons =
    parseEx "natlistcons.thon";
val true = (parsedNatlistCons = natlistCons);

val Arr (Prod ([Nat,TyRec (Scope("natlist",Plus [Unit,Prod [Nat,TypVar ("natlist", 0)]]))]),
         TyRec (Scope("natlist",Plus [Unit,Prod [Nat,TypVar ("natlist", 0)]]))) : typ =
    typeof' [] [] natlistCons;

val deducedSingleListAppResType = typeof' [] [] (App(natlistCons, Pair(Zero, nilNatList)));
val true = (deducedSingleListAppResType = natlist);

val deducedNatlist = typeof' [] [] nilNatList;
val true = (natlist = deducedNatlist);

val Plus [Unit,Prod ([Nat,TyRec (Scope("natlist",Plus [Unit,Prod [Nat,TypVar ("natlist", 0)]]))])] : typ =
    typeof' [] [] (Unfold(nilNatList));

val PlusLeft
    (Plus [Unit,Prod ([Nat,TyRec (Scope("natlist",Plus [Unit,Prod [Nat,TypVar ("natlist", 0)]]))])],TmUnit) : exp = eval (Unfold(nilNatList));

val isnil = Fn(natlist, Scope("x", Case(Unfold(Var ("x", 0)), [Scope("l", Succ Zero), Scope("r", Zero)])));
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
val Zero = step (Case(PlusLeft (Plus[Nat, Nat], Zero), [Scope("l", Var ("l", 0)), Scope("r", Succ(Var ("r", 0)))]));
val (Succ Zero) = step (Case(PlusRight (Plus[Nat, Nat], Zero), [Scope("l", Var ("l", 0)), Scope("r", Succ(Var ("r", 0)))]));

(* Seems there are multiple valid typings of this expression. Up *)
(* front, I thought Some(Arr(TypVar ("t", 0), Nat)) is the only correct typing, *)
(* but the chapter on existential types in TAPL suggests otherwise. *)

(* That's why we require an explicit type annotation from the programmer. *)
val Arr(Nat, Nat) = typeof' [] [NONE] (Fn(Nat, Scope("x", Zero)));
val Arr(TypVar ("t", 0), TypVar ("t", 0)) = abstractOutType "t" Nat (Arr(Nat, Nat));
val All(Scope("t", Arr(TypVar ("t", 0), Nat))) = abstractOutType "t" (Arr(Nat, Nat)) (All(Scope("t", Arr(TypVar ("t", 0), Nat))));

val e0 = Impl(Nat, Fn(Nat, Scope("x", Zero)), Some(Scope("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))));
val Some(Scope("t",Arr(TypVar ("t", 0), TypVar ("t", 0)))) = typeof' [] [] e0;

val Impl (Nat,Fn (Nat,Scope("x",Zero)),Some (Scope("t",Arr (TypVar ("t",0),TypVar ("t",0))))) =
    parse "impl (some t. t -> t) with nat as \\ x : nat -> Z";

val Impl (Nat,Fn (Nat,Scope("x",Zero)),Some (Scope("t",Arr (TypVar ("t",0),TypVar ("t",0))))) =
    run "impl (some t. t -> t) with nat as \\ x : nat -> Z";

val Impl
    (TyRec (Scope("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist",0)])])),
     Fn
       (TyRec (Scope("natlist",Plus [Unit,Prod ([Nat,TypVar ("natlist",0)])])),
        Scope("l", Zero)),Some (Scope("s",Arr (TypVar ("s",0),TypVar ("s",0))))) : exp =
    parse "impl (some s. s -> s) with (u natlist. (unit || (nat * natlist))) as \\ l : (u natlist. (unit || (nat * natlist))) -> Z";

val Use (Impl (Nat,Fn (Nat,Scope("x",Zero)),Some (Scope("t'",Arr (TypVar ("t'",0),TypVar ("t'",0))))),
         Scope("s", Scope("pkg", Var ("pkg",0)))) : exp =
    parse "use (impl (some t'. t' -> t') with nat as \\ x : nat -> Z) as (pkg, s) in (pkg)";

val Zero = run "use (impl (some t. t -> t) with nat as \\ x : nat -> Z) as (pkg, s) in (pkg)"
           handle IllTyped => Zero;

val Zero = runEx "doesnt-parse.sml" handle ParseError => Zero;

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

val zeroFnPkg = Impl(Nat, Fn(Nat, Scope("x", Zero)), Some(Scope("t", Arr(TypVar ("t", 0), Nat))));
val zeroFnPkg2 = Impl(Nat, Fn(Nat, Scope("x", Zero)), Some(Scope("t", Arr(Nat, TypVar ("t", 0)))));

(* Define identity package; can convert Nat to internal repr type and back. *)
val idid = Pair(Fn(Nat, Scope("x", Var ("x", 0))), Fn(Nat, Scope("x", Var ("x", 0))));
val Prod([Arr(Nat, Nat), Arr(Nat, Nat)]) = typeof' [] [] idid;
val inoutpkg = Impl(Nat, idid, Some(Scope("t", Prod([Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat)]))));
val Some(Scope("t",Prod([Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat)]))) = typeof' [] [] inoutpkg;
val Nat = typeof' [] [] (Use(inoutpkg, Scope("s", Scope("pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))))));
val true = isval inoutpkg;
(* Dynamics *)
val App
    (ProdRight (Pair (Fn (Nat,Scope("x",Var ("x", 0))),Fn (Nat,Scope("x",Var ("x", 0))))),
     App (ProdLeft (Pair (Fn (Nat,Scope("x",Var ("x", 0))),Fn (Nat,Scope("x",Var ("x", 0))))),Zero))
    = step (Use(inoutpkg, Scope("s", Scope("pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))))));

val Zero = eval (Use(inoutpkg, Scope("s", Scope("pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))))));

val leftandback = Pair(Fn(Nat, Scope("x", Pair(Var ("x", 0), Zero))), Fn(Prod([Nat, Nat]), Scope("x", ProdLeft (Var ("x", 0)))));
val Prod ([Arr (Nat,Prod [Nat, Nat]),Arr (Prod [Nat, Nat],Nat)]) = typeof' [] [] leftandback;
val inoutpkg2 = Impl(Prod([Nat, Nat]), leftandback, Some(Scope("t", Prod ([Arr (Nat,TypVar ("t", 0)),Arr (TypVar ("t", 0),Nat)]))));
val Some(Scope("t",Prod([Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat)]))) = typeof' [] [] inoutpkg2;
val Nat = typeof' [] [] (Use(inoutpkg2, Scope("s", Scope("pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))))));
val Zero = eval (Use(inoutpkg2, Scope("s", Scope("pkg", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))))));

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

val Fn (Nat, Scope("n",Rec (Var ("n",0),Var ("n",0),Scope("prev", Succ (Succ Zero))))) =
    parse "\\ n : nat -> rec n of Z -> n | prev -> S S Z ";

val App (Fn (Nat, Scope("n",Rec (Var ("n",0),Zero, Scope("prev", Succ (Succ (Var ("prev", 0))))))),Succ Zero) : Ast.exp =
    parse "((\\ n : nat -> rec n of Z -> Z | prev -> S S prev ) (S Z))";

val (Succ (Succ Zero)) =
    run "((\\ n : nat -> rec n of Z -> Z | prev -> S S prev ) (S Z))";

val Succ (Succ (Succ (Succ Zero))) : Ast.exp =
    run "((\\ n : nat -> rec n of Z -> Z | prev -> S S prev ) (S S Z))";

val Succ (Succ (Succ Zero)) = eval (App(multByThree, Succ Zero));

val TypFn (Scope("s", Fn(TypVar ("s", 0), Scope("x",Var ("x", 0))))) : Ast.exp =
    parse "poly s -> \\ x : s -> x";
(* TODO also wrong *)
val TypFn(Scope("t", TypFn (Scope("t'",Fn (Arr (TypVar ("t",1),TypVar ("t'",0)), Scope("x",Var ("x",0))))))) =
    parse "poly t -> poly t' -> \\ x : (t -> t') -> x";
val TypApp (Nat,TypFn (Scope("s", Fn(TypVar ("s", 0), Scope("x",Var ("x",0)))))) =
    parse "((poly s -> \\ x : s -> x) (nat))";
val Fn (Nat, Scope("x",Var ("x", 0))) : Ast.exp =
    run "((poly s -> \\ x : s -> x) (nat))";

val TypApp
    (Nat,
     TypFn(Scope("t",
       (TypFn (Scope("t'", Fn(Arr (TypVar ("t", 1),TypVar ("t'", 0)), Scope("f",Var ("f",0)))))))))
  : Ast.exp =
    parse "((poly t -> poly t' -> \\ f : (t -> t') -> f) (nat))";
val TypFn (Scope("t'", Fn (Arr (Nat,TypVar ("t'",0)), Scope("f",Var ("f",0))))) =
    run "((poly t -> poly t' -> \\ f : (t -> t') -> f) (nat))";

val Pair (Zero,Succ Zero) : Ast.exp =
    parse "(Z, S Z)";

val Pair (Zero,Pair (Succ Zero,Succ (Succ Zero))) : Ast.exp =
    parse "(Z, (S Z, S S Z))";

val Fn (Prod ([Nat,Nat]), Scope("x",Var("x", 0))) : Ast.exp =
    parse "\\ x : (nat * nat) -> x";

val ProdLeft (Pair (Zero,Pair (Succ Zero,Succ (Succ Zero)))) : Ast.exp =
    parse "fst (Z, (S Z, S S Z))";
val ProdRight (Pair (Zero,Pair (Succ Zero,Succ (Succ Zero)))) : Ast.exp =
    parse "snd (Z, (S Z, S S Z))";
val Zero : Ast.exp =
    run "fst (Z, (S Z, S S Z))";
val Succ Zero : Ast.exp =
    run "fst snd (Z, (S Z, S S Z))";

val TypFn (Scope("s",Fn(All (Scope("t'", TypVar ("t'",0))), Scope("x",Var ("x",0))))) : Ast.exp =
    parse "poly s -> \\ x : (all t'. t') -> x"

val Fn (Some (Scope("t'",TypVar ("t'", 0))), Scope("pkg",Var ("pkg",0))) : Ast.exp =
    parse "\\ pkg : (some t'. t') -> pkg"

val Fn (Plus [Nat,Arr (Nat,Nat)], Scope("natOrFunc",Var ("natOrFunc",0))) : Ast.exp =
    parse "\\ natOrFunc : (nat || nat -> nat) -> natOrFunc"

val Fn (Plus [Nat,Arr (Nat,Nat)], Scope("natOrFunc",Case (Var ("natOrFunc", 0), [Scope("l", Zero), Scope("r", Succ Zero)]))) : exp =
    run "\\ natOrFunc : (nat || nat -> nat) -> case natOrFunc of l => Z | r => S Z end"

val App
    (Fn (Plus [Nat,Arr (Nat,Nat)], Scope("natOrFunc", Case (Var ("natOrFunc",0), [Scope("l", Zero), Scope("r", Succ Zero)]))),
     PlusLeft (Plus [Nat,Arr (Nat,Nat)],Zero)) : Ast.exp =
    parse "((\\ natOrFunc : (nat || nat -> nat) -> case natOrFunc of l => Z | r => S Z end) (left Z : (nat || nat -> nat)))";

val Zero : exp =
    run "((\\ natOrFunc : (nat || nat -> nat) -> case natOrFunc of l => Z | r => S Z end) (left Z : (nat || nat -> nat)))";

val Succ Zero: exp =
    run "((\\ natOrFunc : (nat || nat -> nat) -> case natOrFunc of l => Z | r => S Z end) (right (\\ x : nat -> Z) : (nat || nat -> nat)))";

val Fn (Plus [Nat,Plus [Arr (Nat,Nat),Prod ([Nat,Nat])]], Scope("natOrFuncOrProd",Var ("natOrFuncOrProd",0))) : Ast.exp =
    parse "\\ natOrFuncOrProd : (nat || ((nat -> nat) || (nat * nat))) -> natOrFuncOrProd"

val Some (Scope("t",Prod ([TypVar ("t", 0),Prod ([Arr (Prod [Nat,TypVar ("t", 0)],TypVar ("t", 0)),Arr (TypVar ("t", 0),Nat)])]))) : typ =
    typeof (parseEx "natlist.thon");

val natList = parseEx "natlist.thon";

val Arr (Plus [Nat,Unit],Arr (Nat,Nat)) : Ast.typ =
    typeof (parseEx "option.thon");

val Fn
    (Plus [Nat,Unit],
     Scope("x",
     Fn
       (Nat,
        Scope("y",Case (Var ("x",1),[Scope("somex", Var ("somex",0)),Scope("none", Var ("y",1))])))))
  : exp =
    parseEx "option.thon";

val Let (Nat,Zero,Scope("x",Var ("x",0))) : Ast.exp = parse "let x : nat = Z in x";
val Let (Nat,Zero,Scope("x",Let (Nat,Succ Zero,Scope("y",Var ("x",1))))) : Ast.exp =
    parse "let x : nat = Z in (let y : nat = S Z in x)";
val Let (Nat,Zero,Scope("x",Let (Nat,Succ Zero,Scope("y",Var ("x",1))))) : Ast.exp =
    parse "let x : nat = Z in let y : nat = S Z in x";

val Zero : Ast.exp = run "let x : nat = Z in x";

val Succ Zero : Ast.exp = runEx "nilisempty.thon";

val Succ Zero : Ast.exp = run "ifz Z of Z -> S Z | S prev -> Z";
val Zero : Ast.exp = run "ifz S Z of Z -> S Z | S prev -> prev";

val Succ Zero : Ast.exp = runEx "decr.thon";

val Succ (Succ Zero) : Ast.exp = runEx "add.thon";
val Succ Zero : Ast.exp = runEx "sub.thon";
val Zero : Ast.exp = runEx "eq.thon";

val Succ Zero : Ast.exp = runEx "len.thon";

val Fold
    (TyRec
       (Scope("node",
        Plus [Unit,Prod [Nat,Prod [TypVar ("node",0),TypVar ("node",0)]]])),
     PlusLeft
       (Plus
          [Unit, (*empty base or... *)
           Prod (* a nat and... *)
             [Nat,
              Prod (* a node and... *)
                [TyRec
                   (Scope("node",
                    Plus
                      [Unit,
                       Prod [Nat,Prod [TypVar ("node",0),TypVar ("node",0)]]])),
                 TyRec (* a another node. *)
                   (Scope("node",
                    Plus
                      [Unit,
                       Prod [Nat,Prod [TypVar ("node",0),TypVar ("node",0)]]]))]]],
        TmUnit)) : Ast.exp = runEx "emptybst.thon";

val bstType : Ast.typ = typeof (parseEx "singletonbst.thon");

val TyRec
    (Scope("node",Plus [Unit,Prod [Nat,Prod [TypVar ("node",0),TypVar ("node",0)]]]))
    : Ast.typ = bstType;

val bstInsertType : Ast.typ = typeof (parseEx "bst.thon");
val Arr(Nat, (Arr(bstType1, bstType2))) = bstInsertType;
val true = (bstType = bstType1);

val true = (bstType = bstType2);

val loop = parse "fix loop : nat in loop";
val true = (loop) = (step loop);
val Nat = typeof loop;
(* 2 is even *)
val Succ Zero = runEx "iseven.thon";;

val bstinsert = parseEx "bst.thon";
val emptybst = parseEx "emptybst.thon";
val zerobst = parseEx "singletonbst.thon";

val appbst = eval (A.App(A.App(bstinsert, A.Zero), emptybst));
val true = (zerobst = appbst);

val Succ (Succ Zero) = runEx "setget.thon";

val TypFn (Scope("a", Fn (TypVar ("a", 0), Scope("x", Var ("x", 0))))) = runEx "use-poly.thon";

val TypFn (Scope("t", Zero)) = runEx "typnames.thon";

val
  Data
    ("List",["Nil", Cons], [Unit,
     Prod [Nat,Some (Scope("t",Arr (TypVar ("t",0),TypVar ("List",1))))]],Zero)
  : Ast.exp =
    parse "data List = Nil unit | Cons nat * (some t. t -> List) in Z";

val manualDatatype = parseEx "manual-datatype.thon";
val autoDatatype = elaborateDatatypes (parse "data List = Nil unit | Cons nat * List in Z");

val Zero = runEx "auto-natlist.thon";
val Succ (Succ Zero) = runEx "bst-depth.thon";

val Zero = runEx "ternary-tree.thon";
val Zero = runEx "three-summands-to-data.thon";
val Zero = runEx "one-summand-to-data.thon";

val Fn
    (Prod [Nat,Prod [Arr (Nat,Nat),Prod [Nat,Nat]]],
     Scope("natOrFuncOrProd",
     Var ("natOrFuncOrProd",0))) = runEx "ternary-prod-type.thon";

val Fn
    (Plus [Nat,Plus [Arr (Nat,Nat),Prod [Nat,Nat]]],
     Scope("natOrFuncOrProd",
     Var ("natOrFuncOrProd",0))) = runEx "ternary-sum-type.thon";

val
  Tuple
      [TypFn (Scope("t",Fn (TypVar ("t",0), Scope("x",Var ("x",0))))),
       Fn (Nat, Scope("x",Var ("x",0))),
       TypFn (Scope("t",Fn (TypVar ("t",0), Scope("x",Var ("x",0)))))] : exp =
step (A.Tuple [polymorphicIdFn, A.TypApp(Nat, polymorphicIdFn), polymorphicIdFn]);

val
  Data
    ("tree",["nil","two","cons"],
     [Unit,Prod [Nat,Prod [Nat,TypVar ("tree",0)]],
      Prod [Nat,TypVar ("tree",0)]],
     Let
       (Arr (TypVar ("tree",0),Nat),
        Fix
          (Arr (TypVar ("tree",0),Nat),
           Scope("isempty",
           Fn
             (TypVar ("tree",0),
              Scope("t",
              Case
                (App (Var ("exposetree",2),Var ("t",0)),
                 [Scope("empty",Succ Zero),Scope("twocase",Zero),Scope("conscase",Zero)]))))),
        Scope("isempty",
        App
          (Var ("isempty",0),
           App (Var ("cons",2),Pair (Zero,App (Var ("nil",4),TmUnit)))))))
  : exp = parseEx "unary-or-binary-tree.thon";

val Zero = runEx "unary-or-binary-tree.thon";
val Zero = runEx "dbi-management-datatype-elaboration.thon";
val Zero = runEx "expmap-data.thon";

val Zero = runEx "zero.thon";
val Succ Zero = runEx "one.thon";
val Succ Zero = runEx "foo.thon";
val Succ Zero = runEx "idid.thon";
val Succ Zero = runEx "abcd.thon";
val TypFn (Scope("t", Zero)) = runEx "aeqv.thon";
val Succ Zero = runEx "collatz.thon";
(* TODO This is wrong. *)
val All (Scope("t",Arr (TypVar ("t",0),All (Scope("s",TypVar ("t",0 (*Should be 1 here*))))))) = typeof (parseEx "nested-poly.thon");
(* val Zero = runEx "two-datatypes.thon"; *)
(* val Zero = runEx "appapp.thon"; *)
(* val Zero = runEx "thon.thon"; *)

val Arr(Arr(Nat, Arr(Nat, Nat)), Nat) = typeof (parseEx "zero-func.thon");
val All(Scope("t", All(Scope("s", _)))) = typeof (parseEx "all.thon");
val bstType2 = typeof (parseEx "emptybinarytree.thon");
val true = (bstType = bstType2);

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


in
()
end

end
