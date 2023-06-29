signature AST =
sig

    (* TODO is there a way to dedupe this with the structure defn below? *)
    datatype typ =
        Nat
      | TypVar of string * int
      | Arr of typ * typ
      | All of string * typ (* binds *)
      | Some of string * typ (* binds *)
      | Prod of typ list
      | Plus of typ list (* sum type *)
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
      | TypFn of string * exp (* binds type variable *)
      | Ifz of exp * exp * string * exp
      | TypApp of typ * exp
      | Impl of typ (*reprType*)* exp (*pkgImpl*)* typ (*pkgType - first example of explicit type binding - there's not one cannonical type*)
      | Use of exp (*package*) * string (*exp name*) * string (*type name*) * exp (* client that binds BOTH a TypVar and a exp Var *)
      | Data of string *
                string list *
                typ list *
                exp (*TODO non-binary datatypes*)
      | Pair of exp * exp
      | Tuple of exp list
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
    val typMap : (typ -> typ) -> typ -> typ

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
      | Prod of typ list
      | Plus of typ list (* sum type *)
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
      | TypFn of string * exp (* binds type variable *)
      | Ifz of exp * exp * string * exp
      | TypApp of typ * exp
      | Impl of typ (*reprType*)* exp (*pkgImpl*)* typ (*pkgType - first example of explicit type binding - there's not one cannonical type*)
      | Use of exp (*package*) * string (*exp name*) * string (*type name*) * exp (* client that binds BOTH a TypVar and a exp Var *)
      | Data of string *
                string list *
                typ list *
                exp (*TODO non-binary datatypes*)
      | Pair of exp * exp
      | Tuple of exp list
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

    (* DEVNOTE this only applies f at the leaves *)
    fun expMap f e =
        case e
         of  Zero => f Zero
           | TmUnit => f TmUnit
           | Var (name, n)  => f (Var(name, n))
           | Succ e' => f (Succ (expMap f e'))
           | ProdLeft e' => f (ProdLeft(expMap f e'))
           | ProdRight e' => f (ProdRight(expMap f e'))
           | PlusLeft(t, e') => f (PlusLeft(t, expMap f e'))
           | PlusRight(t, e') => f (PlusRight(t, expMap f e'))
           | Case(c, lname, l, rname, r) =>
             f (Case(expMap f c, lname, expMap f l, rname, expMap f r))
           | Fn(argName, t, f') => f (Fn(argName, t, (expMap f f')))
           | Let(varname, vartype, varval, varscope) =>
             f (Let(varname, vartype, (expMap f varval), (expMap f varscope)))
           | App(f', n) => f (App((expMap f f'), expMap f n))
           | Ifz(i, t, prev, e) => f (Ifz(expMap f i, expMap f t, prev, expMap f e))
           | Rec(i, baseCase, prevCaseName, recCase) =>
             f (Rec(expMap f i, expMap f baseCase, prevCaseName, expMap f recCase))
           | Fix(name, t, e') => f (Fix(name, t, expMap f e'))
           | TypFn (name, e') => f (TypFn (name, expMap f e'))
           | TypApp (appType, e') => f (TypApp(appType, expMap f e'))
           | Impl(reprType, pkgImpl, t) => f (Impl(reprType, expMap f pkgImpl, t))
           | Use(pkg, clientName, typeName, client) =>
             f (Use(expMap f pkg, clientName, typeName, expMap f client))
           | Pair(l, r) => f (Pair(expMap f l, expMap f r))
           | Tuple exps => f (Tuple (List.map (expMap f) exps))
           | Fold(t, e') => f (Fold(t, (expMap f e')))
           | Unfold(e') => f (Unfold(expMap f e'))
           | Data(dataname, names, types, exp) =>
             f (Data(dataname, names, types, f exp))

    (* DEVNOTE this applies f at every node *)
    fun typMap f t =
        case t of
            Nat => f t
          | Unit => f t
          | TypVar (name, i) => f t
          | Arr(d, c) => f (Arr(typMap f d, typMap f c))
          | Prod types  => f (Prod(map (typMap f) types))
          | Plus types  => f (Plus(map (typMap f) types))
          | All (name, t') => f (All(name, typMap f t'))
          | Some (name, t') => f (Some(name, typMap f t'))
          | TyRec (name, t') => f (TyRec(name, typMap f t'))


  structure Print =
  struct
    fun pp e =
        case e of
            Zero => "Z"
          | Succ e => "S (" ^ (pp e) ^ ")"
  end

end
