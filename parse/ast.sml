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
      | ProdNth of int * exp
      (* Elimination forms for terms of Plus type *)
      | PlusLeft of typ * exp
      | PlusRight of typ * exp
      | PlusNth of int * typ * exp (* Internal *)
      | Case of exp (* thing being cased on*) *
                string list *
                exp list (* each exp binds *)
      | Fold of typ (*binds*) * exp
      | Unfold of exp
      | TmUnit

    val expMap : (exp -> exp) -> exp -> exp
    val typMap : (typ -> typ) -> typ -> typ

    val typShift : int -> typ -> typ
    val typSubst : int -> typ -> typ -> typ

    val expShift : int -> int -> exp -> exp
    val expSubst : int -> exp -> exp -> exp

  structure Print :
  sig
    val expToString : exp -> string
    val typToString: typ -> string
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
      | Data of string * (* binds type variable *)
                string list *
                typ list *
                exp (*TODO non-binary datatypes*)
      | Pair of exp * exp
      | Tuple of exp list
      (* Elimination forms for terms of Prod type *)
      | ProdLeft of exp
      | ProdRight of exp
      | ProdNth of int * exp
      (* Elimination forms for terms of Plus type *)
      | PlusLeft of typ * exp
      | PlusRight of typ * exp
      | PlusNth of int * typ * exp (* Internal *)
      | Case of exp (* thing being cased on*) *
                string list *
                exp list (* each exp binds *)
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
           | ProdNth(i, e') => f (ProdNth(i, expMap f e'))
           | PlusLeft(t, e') => f (PlusLeft(t, expMap f e'))
           | PlusRight(t, e') => f (PlusRight(t, expMap f e'))
           | PlusNth(i, t, e') => f (PlusNth(i, t, expMap f e'))
           | Case(c, names, exps) =>
             f (Case(expMap f c, names, List.map (expMap f) exps))
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

    (* See page 86 of Types and Programming Languages *)
    fun typShift shift dst =
        let fun walk c t =
        case t of
             Nat => Nat
           | Unit => Unit
           | TypVar (name, n)  => if n >= c then TypVar(name, n+shift) else TypVar(name, n)
           | Arr(d, co) => Arr(walk c d, walk c co)
           | Prod types => Prod(List.map (walk c) types)
           | Plus types => Plus(List.map (walk c) types)
           | All (name, t') => All(name, walk (c+1) t')
           | Some (name, t') => Some(name, walk (c+1) t')
           | TyRec (name, t') => TyRec(name, walk (c+1) t')
        in walk 0 dst end

    (* See page 86 of Types and Programming Languages *)
    fun expShift cutoff shift dst =
        let fun walk c exp =
        case exp of
            Zero => Zero
          | TmUnit => TmUnit
          | Var (name, n)  => if n >= (c+cutoff) then Var(name, n+shift) else Var(name, n)
          | Succ e2 => Succ (walk c e2)
          | ProdLeft e => ProdLeft (walk c e)
          | ProdRight e => ProdRight (walk c e)
          | ProdNth (i, e) => ProdNth (i, walk c e)
          | PlusLeft (t, e) => PlusLeft (t, walk c e)
          | PlusRight (t, e) => PlusRight (t, walk c e)
          | PlusNth (i, t, e) => PlusNth (i, t, walk c e)
          | Case(cas, names, exps) =>
            Case(walk c cas, names, List.map (fn e => walk (c+1) e) exps)
          | Fn (argName, t, f) => Fn(argName, t, (walk (c+1) f))
          | Let (varname, vartype, varval, varscope) =>
            Let(varname, vartype, walk c varval, walk (c+1) varscope)
          | App (f, n) => App((walk c f), (walk c n))
          | Ifz (i, t, prev, e) => Ifz(walk c i, walk c t, prev, walk (c+1) e)
          | Rec (i, baseCase, prevCaseName, recCase) =>
            Rec(walk c i, walk c baseCase, prevCaseName, walk (c+1) recCase)
          | Fix (name, t, e) => Fix(name, t, walk (c+1) e)
          | TypFn (name, e) => TypFn (name, walk c e)
          | TypApp (appType, e) => TypApp(appType, walk c e)
          | Impl(reprType, pkgImpl, t) => Impl(reprType, walk c pkgImpl, t)
          | Use (pkg, clientName, typeName, client) =>
            Use(walk c pkg, clientName, typeName, walk (c+1) client)
          | Pair (l, r) => Pair (walk c l, walk c r)
          | Tuple exps => Tuple (List.map (fn e => walk c e) exps)
          | Fold(t, e') => Fold(t, (walk c e'))
          | Unfold(e') => Unfold(walk c e')
          in walk 0 dst end

    (* See page 86 of Types and Programming Languages *)
    fun typSubst j s dst =
        let fun walk c dst =
        case dst of
             Nat => Nat
           | Unit => Unit
           | TypVar (name, n)  => if n = j+c then typShift c s else TypVar (name, n)
           | Arr(d, co) => Arr(walk c d, walk c co)
           | Prod types => Prod(List.map (walk c) types)
           | Plus types => Plus (List.map (walk c) types)
           | All (name, t') => All(name, walk (c+1) t')
           | Some (name, t') => Some(name, walk (c+1) t')
           | TyRec (name, t') => TyRec(name, walk (c+1) t')
        in walk 0 dst end

    (* See page 86 of Types and Programming Languages *)
    fun expSubst j s dst =
        let fun walk c dst =
        case dst of
            Zero => Zero
          | TmUnit => TmUnit
          | Var (name, n)  => if n = j+c then expShift 0 c s else Var(name, n)
          | Succ e2 => Succ (walk c e2)
          | ProdLeft e => ProdLeft (walk c e)
          | ProdRight e => ProdRight (walk c e)
          | ProdNth (i, e) => ProdNth (i, walk c e)
          | PlusLeft (t, e) => PlusLeft (t, walk c e)
          | PlusRight (t, e) => PlusRight (t, walk c e)
          | PlusNth (i, t, e) => PlusNth (i, t, walk c e)
          | Case(cas, names, exps) =>
            Case(walk c cas, names, List.map (fn e => walk (c+1) e) exps)
          | Fn (argName, t, f) => Fn(argName, t, (walk (c+1) f))
          | Let (varname, vartype, varval, varscope) =>
            Let(varname, vartype, (walk c varval), (walk (c+1) varscope))
          | App (f, n) => App((walk c f), (walk c n))
          | Ifz (i, t, prev, e) => Ifz(walk c i, walk c t, prev, walk (c+1) e)
          | Rec (i, baseCase, prevCaseName, recCase) =>
            Rec(walk c i, walk c baseCase, prevCaseName, walk (c+1) recCase)
          | Fix (name, t, e) => Fix(name, t, walk (c+1) e)
          | TypFn (name, e) => TypFn (name, walk c e)
          | TypApp (appType, e) => TypApp(appType, walk c e)
          | Impl(reprType, pkgImpl, t) => Impl(reprType, walk c pkgImpl, t)
          | Use (pkg, clientName, typeName, client) =>
            Use(walk c pkg, clientName, typeName, walk (c+1) client)
          | Pair (l, r) => Pair (walk c l, walk c r)
          | Tuple exps => Tuple (List.map (fn e => walk c e) exps)
          | Fold(t, e') => Fold(t, (walk c e'))
          | Unfold(e') => Unfold(walk c e')
          in walk 0 dst end

  structure Print =
  struct

    fun typToString Nat = "Nat"
      | typToString (TypVar(s, i)) = "TypVar(" ^ s ^ "," ^ Int.toString(i) ^ ")"

      | typToString (Arr(t, t')) = "Arr(" ^ typToString(t) ^ "," ^ typToString(t') ^ ")"
      | typToString (All(s, t)) = "All(" ^ s ^ "," ^ typToString(t) ^ ")"
      | typToString (Some(s, t)) = "Some(" ^ s ^ "," ^ typToString(t) ^ ")"
      | typToString (Prod types) = "Prod[" ^ (String.concatWith "," (List.map typToString types)) ^ "]"
      | typToString (Plus types) = "Plus[" ^ (String.concatWith "," (List.map typToString types)) ^ "]"
      | typToString (TyRec(s, t)) = "TyRec(" ^ s ^ "," ^ typToString(t) ^ ")"
      | typToString Unit = "Unit"


    fun expToString Zero = "Z"
      | expToString TmUnit = "unit"
      | expToString (Var (name, n))  = "Var(" ^ name ^ "," ^ (Int.toString n) ^ ")"
      | expToString (Succ e') = "Succ(" ^ (expToString e') ^ ")"
      | expToString (ProdLeft e') = "ProdLeft(" ^ (expToString e') ^ ")"
      | expToString (ProdRight e') = "ProdRight(" ^ (expToString e') ^ ")"
      | expToString (ProdNth(i, e')) = "ProdNth(" ^ (Int.toString i) ^ "," ^ (expToString e') ^ ")"
      | expToString (PlusLeft(t, e')) = "PlusLeft(" ^ (typToString t) ^ (expToString e') ^ ")"
      | expToString (PlusRight(t, e')) = "PlusRight(" ^ (typToString t) ^ (expToString e') ^ ")"
      | expToString (PlusNth(i, t, e')) = "PlusNth(" ^ (Int.toString i) ^ "," ^ (typToString t) ^ (expToString e') ^ ")"
      | expToString (Case(c, names, exps)) = "TODO"
      | expToString (Fn(argName, t, f')) = "TODO"
      | expToString (Let(varname, vartype, varval, varscope)) = "TODO"
      | expToString (App(f', n)) =  "TODO"
      | expToString (Ifz(i, t, prev, e)) =  "TODO"
      | expToString (Rec(i, baseCase, prevCaseName, recCase)) = "TODO"
      | expToString (Fix(name, t, e')) =  "TODO"
      | expToString (TypFn (name, e')) = "TODO"
      | expToString (TypApp (appType, e')) = "TODO"
      | expToString (Impl(reprType, pkgImpl, t)) = "TODO"
      | expToString (Use(pkg, clientName, typeName, client)) = "TODO"
      | expToString (Pair(l, r)) = "TODO"
      | expToString (Tuple exps) = "TODO"
      | expToString (Fold(t, e')) = "TODO"
      | expToString (Unfold(e')) = "TODO"
      | expToString (Data(dataname, names, types, exp)) = "TODO"

  end


end
