signature AST =
sig

    (* TODO is there a way to dedupe this with the structure defn below? *)
    datatype Typ =
        Nat
      | TypVar of string * int
      | Arr of Typ * Typ
      | All of string * Typ (* binds *)
      | Some of string * Typ (* binds *)
      | Prod of Typ * Typ
      | Plus of Typ * Typ (* sum type *)
      | TyRec of string * Typ (* binds *)
      | Unit (* nullary sum *)

    datatype Idx = int

    datatype Exp =
        Zero
      | Var of string * int (* idx into ctx *)
      | Succ of Exp
      | Lam of string * Typ (*argType*) * Exp (*funcBody*)
      | Let of string * Typ (*vartype*) * Exp (*varval*) * Exp (*varscope*)
      | App of Exp * Exp
      | Rec of Exp (*i : Nat*) * Exp (*baseCase: t*) * string * Exp (*recCase - binds*)
      | TypAbs of string * Exp (* binds type variable *)
      | TypApp of Typ * Exp
      | Impl of Typ (*reprType*)* Exp (*pkgImpl*)* Typ (*pkgType - first example of explicit type binding - there's not one cannonical type*)
      | Use of Exp (*package*) * string (*exp name*) * Exp (* client that binds BOTH a TypVar and a Exp Var *)
      | Tuple of Exp * Exp
      (* Elimination forms for terms of Prod type *)
      | ProdLeft of Exp
      | ProdRight of Exp
      (* Elimination forms for terms of Plus type *)
      | PlusLeft of Typ * Exp
      | PlusRight of Typ * Exp
      | Case of Exp (* thing being cased on*) *
                string * Exp (* Left binds term var *) *
                string * Exp (* Right binds term var *)
      | Fold of Typ (*binds*) * Exp
      | Unfold of Exp
      | TmUnit

  structure Print :
  sig
    val pp : Exp -> string
  end

end


structure Ast :> AST =
struct
    datatype Typ =
        Nat
      | TypVar of string * int
      | Arr of Typ * Typ
      | All of string * Typ (* binds *)
      | Some of string * Typ (* binds *)
      | Prod of Typ * Typ
      | Plus of Typ * Typ (* sum type *)
      | TyRec of string * Typ (* binds *)
      | Unit (* nullary sum *)

    datatype Idx = int

    datatype Exp =
        Zero
      | Var of string * int (* idx into ctx *)
      | Succ of Exp
      | Lam of string * Typ (*argType*) * Exp (*funcBody*)
      | Let of string * Typ (*vartype*) * Exp (*varval*) * Exp (*varscope*)
      | App of Exp * Exp
      | Rec of Exp (*i : Nat*) * Exp (*baseCase: t*) * string * Exp (*recCase - binds*)
      | TypAbs of string * Exp (* binds type variable *)
      | TypApp of Typ * Exp
      | Impl of Typ (*reprType*)* Exp (*pkgImpl*)* Typ (*pkgType - first example of explicit type binding - there's not one cannonical type*)
      | Use of Exp (*package*) * string (*exp name*) * Exp (* client that binds BOTH a TypVar and a Exp Var *)
      | Tuple of Exp * Exp
      (* Elimination forms for terms of Prod type *)
      | ProdLeft of Exp
      | ProdRight of Exp
      (* Elimination forms for terms of Plus type *)
      | PlusLeft of Typ * Exp
      | PlusRight of Typ * Exp
      | Case of Exp (* thing being cased on*) *
                string * Exp (* Left binds term var *) *
                string * Exp (* Right binds term var *)
      | Fold of Typ (*binds*) * Exp
      | Unfold of Exp
      | TmUnit

  structure Print =
  struct
    fun pp e =
        case e of
            Zero => "Z"
          | Succ e => "S (" ^ (pp e) ^ ")"
  end

end
