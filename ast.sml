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
      | Bool
      | TypCmd of typ
      | Ascii

    datatype Idx = int

    datatype exp =
        Zero
      | Str of string
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
                string * typ *
                string * typ *
                exp (*TODO non-binary datatypes*)
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
      | True 
      | False
      | Cmd of cmd

    and cmd =
        Ret of exp
      | Bnd of string * exp * cmd
      | PrintStr of exp

    val expMap : (exp -> exp) -> exp -> exp
    val typMap : (typ -> typ) -> typ -> typ

  structure Print :
  sig
    val pp : exp -> string
    val typToString : typ -> string
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
      | Bool
      | TypCmd of typ
      | Ascii

    datatype Idx = int

    datatype exp =
        Zero
      | Str of string
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
                string * typ *
                string * typ *
                exp (*TODO non-binary datatypes*)
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
      | True 
      | False
      | Cmd of cmd

    and cmd =
        Ret of exp
      | Bnd of string * exp * cmd
      | PrintStr of exp

    (* DEVNOTE this only applies f at the leaves *)
    fun expMap f e =
        case e
         of  Zero => f Zero
           | Str s => f (Str s)
           | TmUnit => f TmUnit
           | True => f True
           | False => f False
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
           | Fold(t, e') => f (Fold(t, (expMap f e')))
           | Unfold(e') => f (Unfold(expMap f e'))
           | Data(dataname, lname, ltyp, rname, rtyp, exp) =>
             f (Data(dataname, lname, ltyp, rname, rtyp, f exp))
           | Cmd c => f (Cmd c) (* TODO should map into c? *)

    (* DEVNOTE this applies f at every node *)
    fun typMap f t =
        case t of
            Nat => f t
          | Unit => f t
          | TypCmd t' => f (TypCmd (typMap f t'))
          | Bool => f t
          | TypVar (name, i) => f t
          | Arr(d, c) => f (Arr(typMap f d, typMap f c))
          | Prod(l, r) => f (Prod(typMap f l, typMap f r))
          | Plus(l, r) => f (Plus(typMap f l, typMap f r))
          | All (name, t') => f (All(name, typMap f t'))
          | Some (name, t') => f (Some(name, typMap f t'))
          | TyRec (name, t') => f (TyRec(name, typMap f t'))


  structure Print =
  struct
    fun pp e =
        case e of
            Zero => "Z"
          | Succ e => "S (" ^ (pp e) ^ ")"

    fun typToString Nat = "Nat"
      | typToString Unit = "Unit"
      | typToString (TypCmd t') = "TypCmd(" ^ (typToString t') ^ ")"
      | typToString Bool = "Bool"
      | typToString (TypVar (name, i)) = "TypVar(" ^ name ^ ", " ^ (Int.toString i) ^ ")"
      | typToString (Arr(d, c)) = "Arr(" ^ (typToString d) ^ (typToString c) ^ ")"
      | typToString (Prod(l, r)) = "Prod(" ^ (typToString l) ^ (typToString r) ^ ")"
      | typToString (Plus(l, r)) = "Plus(" ^ (typToString l) ^ (typToString r) ^ ")"
      | typToString (All (name, t')) = "All(" ^ name ^ (typToString t') ^ ")"
      | typToString (Some (name, t')) = "Some(" ^ name ^ (typToString t')^ ")"
      | typToString (TyRec (name, t')) = "TyRec(" ^ name ^ (typToString t')^ ")"
  end

end