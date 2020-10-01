signature AST =
sig

    (* TODO is there a way to dedupe this with the structure defn below? *)
    datatype typ =
        Nat
      | TypVar of string * int
      | Arr of typ * typ
      | All of string * typ (* binds *)
      | Some of string * typ (* binds *)
      | Prod of typ * typ
      | Plus of typ * typ (* sum type *)
      | TyRec of string * typ (* binds *)
      | Unit (* nullary sum *)

    datatype Idx = int

    datatype exp =
        Zero
      | Var of string * int (* idx into ctx *)
      | Succ of exp
      | Fn of string * typ (*argType*) * exp (*funcBody*)
      | Let of string * typ (*vartype*) * exp (*varval*) * exp (*varscope*)
      | App of exp * exp
      | Rec of exp (*i : Nat*) * exp (*baseCase: t*) * string * exp (*recCase - binds*)
      | Fix of string (*x*) * typ (*: t*) * exp (*x's scope*)
      | Data of string (*x*) * typ (*= t*) * exp (*x's scope*)
      | TypFn of string * exp (* binds type variable *)
      | Ifz of exp * exp * string * exp
      | TypApp of typ * exp
      | Impl of typ (*reprType*)* exp (*pkgImpl*)* typ (*pkgType - first example of explicit type binding - there's not one cannonical type*)
      | Use of exp (*package*) * string (*exp name*) * string (*type name*) * exp (* client that binds BOTH a TypVar and a exp Var *)
      | Pair of exp * exp
      (* Elimination forms for terms of Prod type *)
      | ProdLeft of exp
      | ProdRight of exp
      (* Elimination forms for terms of Plus type *)
      | PlusLeft of typ * exp
      | PlusRight of typ * exp
      | Case of exp (* thing being cased on*) *
                string * exp (* Left binds term var *) *
                string * exp (* Right binds term var *)
      | Fold of typ (*binds*) * exp
      | Unfold of exp
      | TmUnit

    val expMap : (exp -> exp) -> exp -> exp

  structure Print :
  sig
    val pp : exp -> string
  end

end


structure Ast :> AST =
struct
    datatype typ =
        Nat
      | TypVar of string * int
      | Arr of typ * typ
      | All of string * typ (* binds *)
      | Some of string * typ (* binds *)
      | Prod of typ * typ
      | Plus of typ * typ (* sum type *)
      | TyRec of string * typ (* binds *)
      | Unit (* nullary sum *)

    datatype Idx = int

    datatype exp =
        Zero
      | Var of string * int (* idx into ctx *)
      | Succ of exp
      | Fn of string * typ (*argType*) * exp (*funcBody*)
      | Let of string * typ (*vartype*) * exp (*varval*) * exp (*varscope*)
      | App of exp * exp
      | Rec of exp (*i : Nat*) * exp (*baseCase: t*) * string * exp (*recCase - binds*)
      | Fix of string (*x*) * typ (*: t*) * exp (*x's scope*)
      | Data of string (*x*) * typ (*= t*) * exp (*x's scope*)
      | TypFn of string * exp (* binds type variable *)
      | Ifz of exp * exp * string * exp
      | TypApp of typ * exp
      | Impl of typ (*reprType*)* exp (*pkgImpl*)* typ (*pkgType - first example of explicit type binding - there's not one cannonical type*)
      | Use of exp (*package*) * string (*exp name*) * string (*type name*) * exp (* client that binds BOTH a TypVar and a exp Var *)
      | Pair of exp * exp
      (* Elimination forms for terms of Prod type *)
      | ProdLeft of exp
      | ProdRight of exp
      (* Elimination forms for terms of Plus type *)
      | PlusLeft of typ * exp
      | PlusRight of typ * exp
      | Case of exp (* thing being cased on*) *
                string * exp (* Left binds term var *) *
                string * exp (* Right binds term var *)
      | Fold of typ (*binds*) * exp
      | Unfold of exp
      | TmUnit

    fun expMap f e =
        case e
         of  Zero => f Zero
           | TmUnit => f TmUnit
           | Var (name, n)  => f (Var(name, n))
           | Succ e' => Succ (f e')
           | ProdLeft e' => ProdLeft(f e')
           | ProdRight e' => ProdRight(f e')
           | PlusLeft(t, e') => PlusLeft(t, f e')
           | PlusRight(t, e') => PlusRight(t, e')
           | Case(c, lname, l, rname, r) =>
             Case(f c, lname, f l, rname, f r)
           | Fn(argName, t, f') => Fn(argName, t, (f f'))
           | Let(varname, vartype, varval, varscope) =>
             Let(varname, vartype, (f varval), (f varscope))
           | App(f', n) => App((f f'), f n)
           | Ifz(i, t, prev, e) => Ifz(f i, f t, prev, f e)
           | Rec(i, baseCase, prevCaseName, recCase) =>
             Rec(f i, f baseCase, prevCaseName, f recCase)
           | Fix(name, t, e') => Fix(name, t, f e')
           | TypFn (name, e') => TypFn (name, f e')
           | TypApp (appType, e') => TypApp(appType, f e')
           | Impl(reprType, pkgImpl, t) => Impl(reprType, f pkgImpl, t)
           | Use(pkg, clientName, typeName, client) =>
             Use(f pkg, clientName, typeName, f client)
           | Pair(l, r) => Pair(f l, f r)
           | Fold(t, e') => Fold(t, (f e'))
           | Unfold(e') => Unfold(f e')


  structure Print =
  struct
    fun pp e =
        case e of
            Zero => "Z"
          | Succ e => "S (" ^ (pp e) ^ ")"
  end

end
