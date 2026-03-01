signature AST =
sig

    (* TODO is there a way to dedupe this with the structure defn below? *)
    datatype 'a scope = Scope of string * 'a
    datatype typ =
        Nat
      | TypVar of string * int
      | Arr of typ * typ
      | All of typ scope (* binds *)
      | Some of typ scope (* binds *)
      | Prod of typ list
      | Plus of typ list (* sum type *)
      | TyRec of typ scope (* binds *)
      | Unit (* nullary sum *)

    datatype Idx = int

    datatype exp =
        Zero
      | Var of string * int (* idx into ctx *)
      | Succ of exp
      | Fn of typ (*argType*) * exp scope (*funcBody*)
      | Let of typ (*vartype*) * exp (*varval*) * exp scope (*varscope*)
      | App of exp * exp
      | Rec of exp (*i : Nat*) * exp (*baseCase: t*) * exp scope (*recCase - binds*)
      | Fix of typ (*: t*) * exp scope (*x's scope*)
      | TypFn of exp scope (* binds type variable *)
      | Ifz of exp * exp * exp scope
      | TypApp of typ * exp
      | Impl of typ (*reprType*)* exp (*pkgImpl*)* typ (*pkgType - first example of explicit type binding - there's not one cannonical type*)
      | Use of exp (*package*) * (exp scope) scope (* client that binds BOTH a TypVar and a exp Var *)
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
                exp scope list (* each exp binds *)
      | Fold of typ (*binds*) * exp
      | Unfold of exp
      | TmUnit

    val expMap : (exp -> exp) -> exp -> exp
    val typMap : (typ -> typ) -> typ -> typ

    val typWalk : ('a -> typ -> typ) -> (string -> 'a -> 'a) -> 'a -> typ -> typ
    val incrDepth : string -> int -> int
    val typShift : int -> typ -> typ
    val typSubst : int -> typ -> typ -> typ

    val expWalk : {onExp: 'a -> exp -> exp,
                   onTyp: 'b -> typ -> typ,
                   onBindExp: string -> 'a -> 'a,
                   onBindTyp: string -> 'b -> 'b} -> 'a -> 'b -> exp -> exp
    val expShift : int -> int -> exp -> exp
    val expSubst : int -> exp -> exp -> exp
    val substTypeInExp : typ -> exp -> exp

  structure Print :
  sig
    val expToString : exp -> string
    val typToString: typ -> string
  end

end


structure Ast :> AST =
struct
    datatype 'a scope = Scope of string * 'a
    datatype typ =
        Nat
      | TypVar of string * int
      | Arr of typ * typ
      | All of typ scope (* binds *)
      | Some of typ scope (* binds *)
      | Prod of typ list
      | Plus of typ list (* sum type *)
      | TyRec of typ scope (* binds *)
      | Unit (* nullary sum *)

    datatype Idx = int

    datatype exp =
        Zero
      | Var of string * int (* idx into ctx *)
      | Succ of exp
      | Fn of typ (*argType*) * exp scope (*funcBody*)
      | Let of typ (*vartype*) * exp (*varval*) * exp scope (*varscope*)
      | App of exp * exp
      | Rec of exp (*i : Nat*) * exp (*baseCase: t*) * exp scope (*recCase - binds*)
      | Fix of typ (*: t*) * exp scope (*x's scope*)
      | TypFn of exp scope (* binds type variable *)
      | Ifz of exp * exp * exp scope
      | TypApp of typ * exp
      | Impl of typ (*reprType*)* exp (*pkgImpl*)* typ (*pkgType - first example of explicit type binding - there's not one cannonical type*)
      | Use of exp (*package*) * (exp scope) scope (* client that binds BOTH a TypVar and a exp Var *)
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
                exp scope list (* each exp binds *)
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
           | Case(c, scs) =>
             f (Case(expMap f c, List.map (fn Scope(n, e') => Scope(n, expMap f e')) scs))
           | Fn(t, Scope(argName, f')) => f (Fn(t, Scope(argName, expMap f f')))
           | Let(vartype, varval, Scope(varname, varscope)) =>
             f (Let(vartype, (expMap f varval), Scope(varname, expMap f varscope)))
           | App(f', n) => f (App((expMap f f'), expMap f n))
           | Ifz(i, t, Scope(prev, e')) => f (Ifz(expMap f i, expMap f t, Scope(prev, expMap f e')))
           | Rec(i, baseCase, Scope(prevCaseName, recCase)) =>
             f (Rec(expMap f i, expMap f baseCase, Scope(prevCaseName, expMap f recCase)))
           | Fix(t, Scope(name, e')) => f (Fix(t, Scope(name, expMap f e')))
           | TypFn (Scope(name, e')) => f (TypFn (Scope(name, expMap f e')))
           | TypApp (appType, e') => f (TypApp(appType, expMap f e'))
           | Impl(reprType, pkgImpl, t) => f (Impl(reprType, expMap f pkgImpl, t))
           | Use(pkg, Scope(typeName, Scope(clientName, client))) =>
             f (Use(expMap f pkg, Scope(typeName, Scope(clientName, expMap f client))))
           | Pair(l, r) => f (Pair(expMap f l, expMap f r))
           | Tuple exps => f (Tuple (List.map (expMap f) exps))
           | Fold(t, e') => f (Fold(t, (expMap f e')))
           | Unfold(e') => f (Unfold(expMap f e'))
           | Data(dataname, names, types, exp) =>
             f (Data(dataname, names, types, expMap f exp))

    (* DEVNOTE this applies f at every node *)
    fun typMap f t =
        case t of
            Nat => f t
          | Unit => f t
          | TypVar (name, i) => f t
          | Arr(d, c) => f (Arr(typMap f d, typMap f c))
          | Prod types  => f (Prod(map (typMap f) types))
          | Plus types  => f (Plus(map (typMap f) types))
          | All (Scope(name, t')) => f (All(Scope(name, typMap f t')))
          | Some (Scope(name, t')) => f (Some(Scope(name, typMap f t')))
          | TyRec (Scope(name, t')) => f (TyRec(Scope(name, typMap f t')))

    fun typWalk onTyp inc c t =
        let fun walkScope (Scope(name, t')) = Scope(name, typWalk onTyp inc (inc name c) t')
        in
        onTyp c (case t of
             Nat => Nat
           | Unit => Unit
           | TypVar _ => t
           | Arr(d, co) => Arr(typWalk onTyp inc c d, typWalk onTyp inc c co)
           | Prod types => Prod(List.map (typWalk onTyp inc c) types)
           | Plus types => Plus(List.map (typWalk onTyp inc c) types)
           | All sc => All(walkScope sc)
           | Some sc => Some(walkScope sc)
           | TyRec sc => TyRec(walkScope sc))
        end

    val incrDepth : string -> int -> int = fn _ => fn c => c+1

    (* See page 86 of Types and Programming Languages *)
    fun typShift shift =
        typWalk (fn c => fn TypVar(name, n) =>
            if n >= c then TypVar(name, n+shift) else TypVar(name, n)
            | t => t)
            incrDepth 0

    fun expWalk (args as {onExp, onTyp, onBindExp, onBindTyp}) ce ct e =
        let val walk = expWalk args
            fun walkExpScope (Scope(name, e')) = Scope(name, walk (onBindExp name ce) ct e')
            fun walkTypScope (Scope(name, e')) = Scope(name, walk ce (onBindTyp name ct) e')
        in
        onExp ce (case e of
            Zero => e
          | TmUnit => e
          | Var _ => e
          | Succ e' => Succ (walk ce ct e')
          | ProdLeft e' => ProdLeft (walk ce ct e')
          | ProdRight e' => ProdRight (walk ce ct e')
          | ProdNth (i, e') => ProdNth (i, walk ce ct e')
          | PlusLeft (t, e') => PlusLeft (onTyp ct t, walk ce ct e')
          | PlusRight (t, e') => PlusRight (onTyp ct t, walk ce ct e')
          | PlusNth (i, t, e') => PlusNth (i, onTyp ct t, walk ce ct e')
          | Case(cas, scs) =>
            Case(walk ce ct cas, List.map walkExpScope scs)
          | Fn (t, sc) => Fn(onTyp ct t, walkExpScope sc)
          | Let (vartype, varval, sc) =>
            Let(onTyp ct vartype, walk ce ct varval, walkExpScope sc)
          | App (f, n) => App(walk ce ct f, walk ce ct n)
          | Ifz (i, t, sc) => Ifz(walk ce ct i, walk ce ct t, walkExpScope sc)
          | Rec (i, baseCase, sc) =>
            Rec(walk ce ct i, walk ce ct baseCase, walkExpScope sc)
          | Fix (t, sc) => Fix(onTyp ct t, walkExpScope sc)
          | Pair (l, r) => Pair (walk ce ct l, walk ce ct r)
          | Tuple exps => Tuple (List.map (fn e' => walk ce ct e') exps)
          | TypFn sc => TypFn (walkTypScope sc)
          | TypApp (appType, e') => TypApp(onTyp ct appType, walk ce ct e')
          | Impl(reprType, pkgImpl, t) => Impl(onTyp ct reprType, walk ce ct pkgImpl, onTyp ct t)
          | Use (pkg, Scope(tn, Scope(en, body))) =>
            Use(walk ce ct pkg, Scope(tn, Scope(en, walk (onBindExp en ce) (onBindTyp tn ct) body)))
          | Fold(t, e') =>
            let val ct' = case t of TyRec(Scope(name, _)) => onBindTyp name ct | _ => ct
            in Fold(onTyp ct t, walk ce ct' e') end
          | Unfold(e') => Unfold(walk ce ct e')
          | Data(dataname, names, types, e') =>
            let val ct' = onBindTyp dataname ct
                val ce' = foldl (fn (n, c) => onBindExp n c) ce (names @ ["expose" ^ dataname])
            in Data(dataname, names, List.map (onTyp ct') types, walk ce' ct' e') end)
        end

    fun expShift cutoff shift =
        expWalk {onExp = fn c => fn Var(name, n) =>
                    if n >= (c+cutoff) then Var(name, n+shift) else Var(name, n)
                    | e => e,
                 onTyp = fn _ => fn t => t,
                 onBindExp = incrDepth, onBindTyp = incrDepth} 0 0

    (* See page 86 of Types and Programming Languages *)
    fun typSubst j s =
        typWalk (fn c => fn TypVar(name, n) =>
            if n = j+c then typShift c s else TypVar(name, n)
            | t => t)
            incrDepth 0

    (* See page 86 of Types and Programming Languages *)
    fun expSubst j s =
        expWalk {onExp = fn c => fn Var(name, n) =>
                    if n = j+c then expShift 0 c s else Var(name, n)
                    | e => e,
                 onTyp = fn _ => fn t => t,
                 onBindExp = incrDepth, onBindTyp = incrDepth} 0 0

    fun substTypeInExp srcType =
        expWalk {onExp = fn _ => fn e => e,
                 onTyp = fn ct => fn t => typSubst ct srcType t,
                 onBindExp = incrDepth, onBindTyp = incrDepth} 0 0

  structure Print =
  struct

    fun typToString Nat = "Nat"
      | typToString (TypVar(s, i)) = "TypVar(" ^ s ^ "," ^ Int.toString(i) ^ ")"

      | typToString (Arr(t, t')) = "Arr(" ^ typToString(t) ^ "," ^ typToString(t') ^ ")"
      | typToString (All(Scope(s, t))) = "All(" ^ s ^ "," ^ typToString(t) ^ ")"
      | typToString (Some(Scope(s, t))) = "Some(" ^ s ^ "," ^ typToString(t) ^ ")"
      | typToString (Prod types) = "Prod[" ^ (String.concatWith "," (List.map typToString types)) ^ "]"
      | typToString (Plus types) = "Plus[" ^ (String.concatWith "," (List.map typToString types)) ^ "]"
      | typToString (TyRec(Scope(s, t))) = "TyRec(" ^ s ^ "," ^ typToString(t) ^ ")"
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
      | expToString (Case(c, scs)) = "TODO"
      | expToString (Fn(t, Scope(argName, f'))) = "TODO"
      | expToString (Let(vartype, varval, Scope(varname, varscope))) = "TODO"
      | expToString (App(f', n)) =  "TODO"
      | expToString (Ifz(i, t, Scope(prev, e))) =  "TODO"
      | expToString (Rec(i, baseCase, Scope(prevCaseName, recCase))) = "TODO"
      | expToString (Fix(t, Scope(name, e'))) =  "TODO"
      | expToString (TypFn (Scope(name, e'))) = "TODO"
      | expToString (TypApp (appType, e')) = "TODO"
      | expToString (Impl(reprType, pkgImpl, t)) = "TODO"
      | expToString (Use(pkg, Scope(typeName, Scope(clientName, client)))) = "TODO"
      | expToString (Pair(l, r)) = "TODO"
      | expToString (Tuple exps) = "TODO"
      | expToString (Fold(t, e')) = "TODO"
      | expToString (Unfold(e')) = "TODO"
      | expToString (Data(dataname, names, types, exp)) = "TODO"

  end


end
