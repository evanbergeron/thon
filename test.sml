structure T = Thon
structure Test : sig
              val test : unit -> unit
          end =
struct

fun test() = let
open Thon;
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

val TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0)))) = typeof' [] [] singletonList;

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
    typeof' [] [] natlistCons;

val deducedSingleListAppResType = typeof' [] [] (App(natlistCons, Pair(Zero, nilNatList)));
val true = (deducedSingleListAppResType = natlist);

val deducedNatlist = typeof' [] [] nilNatList;
val true = (natlist = deducedNatlist);

val Plus (Unit,Prod (Nat,TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0)))))) : typ =
    typeof' [] [] (Unfold(nilNatList));

val PlusLeft
    (Plus (Unit,Prod (Nat,TyRec ("natlist",Plus (Unit,Prod (Nat,TypVar ("natlist", 0)))))),TmUnit) : exp = eval (Unfold(nilNatList));

val isnil = Fn("x", natlist, Case(Unfold(Var ("x", 0)), "l", Succ Zero, "r", Zero));
val Nat = typeof' [] [] (App(isnil, nilNatList));
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

val Plus(Nat, Nat) = typeof' [] [] (PlusLeft (Plus(Nat, Nat), Zero));
val Plus(Nat, Prod(Nat, Nat)) = typeof' [] [] (PlusLeft (Plus(Nat, Prod(Nat, Nat)), Zero));
val Zero = step (Case(PlusLeft (Plus(Nat, Nat), Zero), "l", Var ("l", 0), "r", Succ(Var ("r", 0))));
val (Succ Zero) = step (Case(PlusRight (Plus(Nat, Nat), Zero), "l", Var ("l", 0), "r", Succ(Var ("r", 0))));

(* Seems there are multiple valid typings of this expression. Up *)
(* front, I thought Some(Arr(TypVar ("t", 0), Nat)) is the only correct typing, *)
(* but the chapter on existential types in TAPL suggests otherwise. *)

(* That's why we require an explicit type annotation from the programmer. *)
val Arr(Nat, Nat) = typeof' [] [NONE] (Fn("x", Nat, Zero));
val Arr(TypVar ("t", 0), TypVar ("t", 0)) = abstractOutType "t" Nat (Arr(Nat, Nat));
val All("t", Arr(TypVar ("t", 0), Nat)) = abstractOutType "t" (Arr(Nat, Nat)) (All("t", Arr(TypVar ("t", 0), Nat)));

val e0 = Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof' [] [] e0;

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
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof' [] [] e1;
val e2 = Impl(Arr(Nat, Nat), Fn("x", Arr(Nat, Nat), Var ("x", 0)), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof' [] [] e2;
val e4 = Impl(All("t", Nat), Fn("x", All("t", Nat), Zero), Some("t", Arr(TypVar ("t", 0), Nat)));
val Some("t",Arr(TypVar ("t", 0), Nat)) = typeof' [] [] e4

val e5 = Impl(Nat, Fn("x", All("t", Nat), Zero), Some("t", Arr(All ("t", TypVar ("t", 1)), TypVar ("t", 0))));
val Some("t",Arr(All ("t", TypVar ("t", 1)), TypVar ("t", 0))) = typeof' [] [] e5

val t5 = typeof' [] [] (Fn("x", All("t", Nat), Zero));
val (Arr(All ("t", Nat), Nat)) = t5;
val Arr(All ("t", TypVar ("t", 1)), TypVar ("t", 0)) = abstractOutType "t" Nat (Arr(All ("t", Nat), Nat));

val f = Fn("x", Arr(Nat, Nat), Zero);
val g = Fn ("x", Nat,Succ (Var ("x", 0)));
val pkg = Impl(Arr(Nat, Nat), f, Some("t", Arr(TypVar ("t", 0), Nat)));
val Some ("t",Arr(TypVar ("t", 0), Nat)) = typeof' [] [] pkg;

val Some("t",Arr(TypVar ("t", 0), Nat)) = typeof' [] [] (Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), Nat))));
val Some("t",Arr(TypVar ("t", 0), TypVar ("t", 0))) = typeof' [] [] (Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))));
val Nat = typeof' [] [] (Impl(Nat, Fn("x", Nat, Zero), Some("t", TypVar ("t", 0)))) handle IllTyped => Nat;

val zeroFnPkg = Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(TypVar ("t", 0), Nat)));
val zeroFnPkg2 = Impl(Nat, Fn("x", Nat, Zero), Some("t", Arr(Nat, TypVar ("t", 0))));

(* Define identity package; can convert Nat to internal repr type and back. *)
val idid = Pair(Fn("x", Nat, Var ("x", 0)), Fn("x", Nat, Var ("x", 0)));
val Prod(Arr(Nat, Nat), Arr(Nat, Nat)) = typeof' [] [] idid;
val inoutpkg = Impl(Nat, idid, Some("t", Prod(Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat))));
val Some("t",Prod(Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat))) = typeof' [] [] inoutpkg;
val Nat = typeof' [] [] (Use(inoutpkg, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));
val true = isval inoutpkg;
(* Dynamics *)
val App
    (ProdRight (Pair (Fn ("x", Nat,Var ("x", 0)),Fn ("x", Nat,Var ("x", 0)))),
     App (ProdLeft (Pair (Fn ("x", Nat,Var ("x", 0)),Fn ("x", Nat,Var ("x", 0)))),Zero))
    = step (Use(inoutpkg, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val Zero = eval (Use(inoutpkg, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));

val leftandback = Pair(Fn("x", Nat, Pair(Var ("x", 0), Zero)), Fn("x", Prod(Nat, Nat), ProdLeft (Var ("x", 0))));
val Prod (Arr (Nat,Prod (Nat, Nat)),Arr (Prod (Nat, Nat),Nat)) = typeof' [] [] leftandback;
val inoutpkg2 = Impl(Prod(Nat, Nat), leftandback, Some("t", Prod (Arr (Nat,TypVar ("t", 0)),Arr (TypVar ("t", 0),Nat))));
val Some("t",Prod(Arr(Nat, TypVar ("t", 0)), Arr(TypVar ("t", 0), Nat))) = typeof' [] [] inoutpkg2;
val Nat = typeof' [] [] (Use(inoutpkg2, "pkg", "s", App(ProdRight(Var ("x", 0)), App(ProdLeft(Var ("x", 0)), Zero))));
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

val Nat = typeof' [] [] (TypApp(TypVar ("t", 0), Zero)) handle IllTyped => Nat;
val All("t", Arr(TypVar ("t", 0), Nat)) = typeof' [] [] (TypFn("t", Fn("x", TypVar ("t", 0), Zero)));
val Arr(Arr(Nat, Nat), Nat) = typeof' [] [] (TypApp(Arr(Nat, Nat), (TypFn("t", Fn("x", TypVar ("t", 0), Zero)))));
val Nat = typeof' [] [] (TypApp(Arr(Nat, Nat), (TypFn("t", Fn("x", TypVar ("t", 1), Zero))))) handle IllTypedMsg _ => Nat;


val All("t", Nat) = typeof' [] [] (TypFn("t", Zero)); (* polymorphic zero *)
(* polymorphic id function :) *)
val All("t", Arr(TypVar ("t", 0), TypVar ("t", 0))) =
    typeof' [] [] (TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0))));
val Arr(Nat, All("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))) =
    typeof' [] [] (Fn("x", Nat, TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0)))));
val Arr(Nat, All("t", Arr(TypVar ("t", 0), TypVar ("t", 0)))) =
    typeof' [] [] (Fn("x", Nat, TypFn("t", Fn("x", TypVar ("t", 0), Var ("x", 0)))));
(* Nested type variables *)
val All("t", All("t", Arr(TypVar ("t", 1),Nat))) =
    typeof' [] [] (TypFn("t", TypFn("t", Fn("x", TypVar ("t", 1), Zero))))
val All("t", All("t", Arr(TypVar ("t", 1), TypVar ("t", 1)))) =
    typeof' [] [] (TypFn("t", TypFn("t", Fn("x", TypVar ("t", 1), Var ("x", 0)))))

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

val Nat = typeof' [] [] Zero;
val Nat = typeof' [] [] (Succ (Zero));

val Nat = typeof' [Nat] [] (Var("x", 0));
val Arr(Nat, Nat) = typeof' [Arr(Nat, Nat)] [] (Var("x", 0));
val Arr(Nat, Nat) = typeof' [Arr(Nat, Nat), Nat] [] (Var("x", 0));
val Nat = typeof' [Arr(Nat, Nat), Nat] [] (Var("x", 1));

val Arr(Nat, Nat) = typeof' [] [] (Fn("x", Nat, Zero));
val Arr(Nat, Nat) = typeof' [] [] (Fn("x", Nat, Succ(Zero)));

val Nat = typeof' [] [] (App(Fn("x", Nat, Zero), Zero));

val Nat = typeof' [] [] (App(Fn("x", Nat, Succ(Zero)), Fn("x", Nat, Zero)))
          handle IllTyped => Nat;

val timesTwo = Rec(Succ(Zero), Zero, "prev", Succ(Succ(Var("prev", 0))));
val Nat = typeof' [] [] timesTwo;

val Arr(Arr(Nat, Nat), Nat) =
    typeof' [] [] (Fn("f", Arr(Nat, Nat), App(Var("f", 0), Zero)));

val Arr(Nat, Nat) = typeof' [] [] (Rec(Zero,
                                       Fn("x", Nat, Succ(Zero)),
                                       "prev", Fn("x", Nat, Succ(Var("x", 0)))));
val Arr(Nat, Nat) = typeof' [] [] (Rec(Succ(Zero),
                                       Fn("x", Nat, Succ(Zero)),
                                       "prev", Fn("x", Nat, Succ(Var("x", 0)))));

val Arr(Nat, Nat) = typeof' [Nat] [] (Rec(Var("dne", 0),
                                       Fn("x", Nat, Succ(Zero)),
                                       "prev", Fn("x", Nat, Succ(Var("x", 0)))));


val Nat = typeof' [] [] (App(Fn("f", Arr(Nat, Nat), App(Var("f", 0), Zero)), Zero)) handle IllTyped => Nat;

(* Ill-formed; first param must be Nat. *)
val Nat = typeof' [] [] (Rec(Fn("x", Nat, Zero),
                               Fn("x", Nat, Succ(Zero)),
                               "prev", Fn("x", Nat, Succ(Var("x", 0))))) handle Bind => Nat;

(* Ill-formed; base case type does not match rec case type. *)
val Nat = (typeof' [] [] (Rec(Zero,
                                Succ(Zero),
                                "prev", Fn("x", Nat, Succ(Zero))))
          handle IllTyped => Nat);

val Arr(Nat, Nat) = typeof' [] [] (Fn("x", (TypVar ("t", 0)), Zero)) handle IllTypedMsg _ => Arr(Nat, Nat);

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

val
  Data
    ("List","Nil",Unit,"Cons",
     Prod (Nat,Some ("t",Arr (TypVar ("t",0),TypVar ("List",1)))),Zero)
  : Ast.exp =
    parse "data List = Nil unit | Cons nat * (some t. t -> List) in Z";

val manualDatatype = parseFile "/home/evan/thon/examples/manual-datatype.thon";
val autoDatatype = elaborateDatatypes (parse "data List = Nil unit | Cons nat * List in Z");

val Zero = runFile "/home/evan/thon/examples/auto-natlist.thon";
val Succ (Succ Zero) = runFile "/home/evan/thon/examples/bst-depth.thon";

(* Handwritten lexer tests *)
open Lex;
val [FUN,NAME "foo",LPAREN,NAME "a",NAT,RPAREN,NEWLINE,INDENT,FUN,NAME "bar",LPAREN,
     NAME "n",NAT,RPAREN,NEWLINE,INDENT,RETURN,NAME "n",NEWLINE,DEDENT,RETURN,NAME "a",
     NEWLINE,DEDENT] : Lex.Token list
    = Lex.lexFile "/home/evan/thon/examples/lex00.thon";

val [FUN,NAME "foo",LPAREN,NAME "a",NAT,RPAREN,NAT,NEWLINE,INDENT,LET,NAME "x",
   NAT,SARROW,NAT,EQ,FN,LPAREN,NAME "x",NAT,RPAREN,DARROW,SUCC,LPAREN,
   NAME "x",RPAREN,NEWLINE,FUN,NAME "bar",LPAREN,NAME "n",NAT,RPAREN,NAT,
   NEWLINE,INDENT,NAME "n",NEWLINE,DEDENT,NAME "a",NEWLINE,DEDENT]
  : Lex.Token list =
    Lex.lexFile "/home/evan/thon/examples/lex01.thon";

val
  [FUN,NAME "foo",LPAREN,NAME "a",NAT,RPAREN,NAT,NEWLINE,INDENT,LET,NAME "b",NAT,
   EQ,ZERO,NEWLINE,LET,NAME "f",NAT,SARROW,NAT,EQ,FN,LPAREN,NAME "x",NAT,RPAREN,
   NAT,DARROW,SUCC,NAME "x",NEWLINE,IF,NAME "t",NEWLINE,INDENT,LET,NAME "c",NAT,EQ,
   NAME "f",LPAREN,NAME "b",RPAREN,NEWLINE,DEDENT,ELSE,NEWLINE,INDENT,LET,NAME "c",NAT,EQ,
   NAME "f",LPAREN,NAME "a",RPAREN,NEWLINE,DEDENT,LET,NAME "p",LPAREN,NAT,COMMA,NAT,
   RPAREN,EQ,LPAREN,SUCC,ZERO,COMMA,ZERO,RPAREN,NEWLINE,DATA,NAME "tree",EQ,
   NAME "nil",BAR,NAME "node",NAT,NAME "tree",NAME "tree",NEWLINE,LET,NAME "n",
   NAME "tree",EQ,NAME "nil",NEWLINE,LET,NAME "n2",NAME "tree",EQ,NAME "node",
   LPAREN,ZERO,COMMA,NAME "nil",COMMA,NAME "nil",RPAREN,NEWLINE,CASE,NAME "n2",NEWLINE,INDENT,
   NAME "nil",NEWLINE,INDENT,RETURN,NAME "b",NEWLINE,DEDENT,NAME "node",LPAREN,NAME "val",
   COMMA,NAME "l",COMMA,NAME "r",RPAREN,NEWLINE,INDENT,RETURN,NAME "f",LPAREN,
   NAME "n",RPAREN,NEWLINE,DEDENT,RETURN,NAME "TODOstillNeedToHandleMultiDedent",
   NEWLINE,DEDENT,RETURN,NAME "b",NEWLINE,DEDENT] : Lex.Token list =
    Lex.lexFile "/home/evan/thon/examples/lex02.thon";

val true = (Lex.lexFileNoPrintErrMsg "/home/evan/thon/examples/lex03.thon"; false) handle UnexpectedToken => true;

val Let ("zero",Arr (Nat,Nat),Fix ("zero",Arr (Nat,Nat),Fn ("a",Nat,Zero)),TmUnit)
    : Ast.exp =
    newParseFile "/home/evan/thon/examples/parse00.thon";

val Let
    ("ident",Arr (Nat,Nat),
     Fix ("ident",Arr (Nat,Nat),Fn ("a",Nat,Var ("a",0))),
     App (Var ("ident",0),Zero)) : Ast.exp =
    newParseFile "/home/evan/thon/examples/parse01.thon";



val [FUN,NAME "foo",LPAREN,NAME "a",NAT,RPAREN,NAT,SARROW,NAT,NEWLINE,INDENT,
   FUN,NAME "bar",LPAREN,NAME "b",NAT,RPAREN,NAT,NEWLINE,INDENT,NAME "a",
   NEWLINE,DEDENT,DEDENT] : Lex.Token list =
    Lex.lexFile "/home/evan/thon/examples/parse02.thon";

val Let
    ("foo",Arr (Nat,Arr (Nat,Nat)),
     Fix
       ("foo",Arr (Nat,Arr (Nat,Nat)),
        Fn
          ("a",Nat,
           Let
             ("bar",Arr (Nat,Nat),
              Fix ("bar",Arr (Nat,Nat),Fn ("b",Nat,Var ("a",2))),
              Var ("bar",0)))),
     TmUnit) : Ast.exp =
    newParseFile "/home/evan/thon/examples/parse02.thon";


val [FUN,NAME "foo",LPAREN,NAME "a",NAT,RPAREN,NAT,SARROW,NAT,NEWLINE,INDENT,
   FUN,NAME "bar",LPAREN,NAME "b",NAT,RPAREN,NAT,NEWLINE,INDENT,NAME "a"]
  : Lex.Token list =
    Lex.lexFile "/home/evan/thon/examples/lex04.thon";


val Data ("list","nil",Unit,"cons",Prod (Nat,TypVar ("list",0)),
          App (Var ("cons",1),Pair (Zero,App (Var ("nil",2),TmUnit)))) : Ast.exp
    = newParseFile "/home/evan/thon/examples/isemptynew.thon";

val Zero = newRunFile "/home/evan/thon/examples/isemptyagain.thon";

val Let
    ("foo",Arr (Nat,Nat),
     Fix
       ("foo",Arr (Nat,Nat),
        Fn
          ("a",Nat,
           Let
             ("x",Arr (Nat,Nat),Fn ("x",Nat,Succ (Var ("x",0))),
              Let
                ("bar",Arr (Nat,Nat),
                 Fix ("bar",Arr (Nat,Nat),Fn ("n",Nat,Var ("n",0))),
                 Var ("a",2))))),TmUnit) : Ast.exp =
    newParseFile "/home/evan/thon/examples/lex01.thon";

val Fn ("x",Nat,Var ("x",0)) : Ast.exp = Thon.newParse "fn (x nat) => x";

val Fn ("x",Nat,Fn ("y",Nat,Var ("y",0))) : Ast.exp = Thon.newParse "fn (x nat) => fn (y nat) => y";

val Succ (Succ Zero) : Ast.exp = Thon.newRunFile "/home/evan/thon/examples/divbytwonew.thon";

in
()
end

end (* structure Test *)
