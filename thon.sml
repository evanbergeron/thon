(* thon - a small functional language *)
structure A = Ast
structure Thon : sig
                   val typeof : A.exp -> A.typ
                   val typeof' : A.typ list -> A.typ option list -> A.exp -> A.typ
                   val eval : A.exp -> A.exp
                   val isval : A.exp -> bool
                   val step : A.exp -> A.exp
                   val eraseNamesInTyp : A.typ -> A.typ
                   val elaborateDatatypes : A.exp -> A.exp
                   val abstractOutType : string -> A.typ -> A.typ -> A.typ
                   val println : string -> unit
                   val get : 'a list -> int -> 'a
                   val istype : 'a option list -> A.typ -> bool
                   val run : string -> A.exp
                   val runFile : string -> A.exp
                   exception IllTyped
                   exception IllTypedMsg of string
                 end =
struct

exception IllTyped
exception IllTypedMsg of string
fun raiseIllTypedMsg msg = (print ("Type error: " ^ msg ^ "\n"); raise IllTypedMsg msg)
exception No
exception VarNotInContext
exception VarWithNegativeDeBruijinIndex of string * int


fun get ctx i =
    case (List.findi (fn (j, _) => j = i) ctx) of
        NONE => (print (Int.toString i); raise VarNotInContext)
      | SOME (j,v) => v


fun printlnType t = (print (A.Print.typToString t); print "\n")
fun println s = (print s; print "\n")

fun istype typeCtx A.Nat = true
  | istype typeCtx A.Unit = true
  | istype typeCtx (A.TypVar (name, i)) = i >= 0 andalso i < (length typeCtx)
  | istype typeCtx (A.Arr(d, c)) = (istype typeCtx d) andalso (istype typeCtx c)
  | istype typeCtx (A.Prod types) = List.all (istype typeCtx) types
  | istype typeCtx (A.Plus types) = List.all (istype typeCtx) types
  | istype typeCtx (A.All (A.Scope(name, t'))) = istype (NONE::typeCtx) t'
  | istype typeCtx (A.Some (A.Scope(name, t'))) = istype (NONE::typeCtx) t'
  | istype typeCtx (A.TyRec (A.Scope(name, t'))) = istype (NONE::typeCtx) t'

fun abstractOutType name search =
    A.typWalk (fn c => fn t => if t = search then A.TypVar(name, c) else t)
        A.incrDepth 0

fun typOpen s t = A.typShift ~1 (A.typSubst 0 (A.typShift 1 s) t)

fun find name names =
    (case List.findi (fn (_, n : string) => n = name) names
     of NONE => NONE
      | SOME (i, _) => SOME i)

fun setDeBruijnIndexInType t typnames =
    A.typWalk (fn typnames => fn A.TypVar(name, _) =>
        (case find name typnames of
            NONE => (print ("unknown type var: "^ name); raise VarNotInContext)
          | SOME i => A.TypVar(name, i))
        | t => t)
    (fn name => fn names => name::names) typnames t

fun setDeBruijnIndex e varnames typnames =
    A.expWalk
        {onExp = fn varnames => fn A.Var(name, _) =>
            (case find name varnames of
                NONE => (print ("unknown var: "^ name); raise VarNotInContext)
              | SOME i => A.Var(name, i))
            | e => e,
         onTyp = fn typnames => fn t => setDeBruijnIndexInType t typnames,
         onBindExp = fn name => fn names => name::names,
         onBindTyp = fn name => fn names => name::names}
        varnames typnames e

fun elaborateDatatype e =
    case e of
        A.Data(dataname, names, types, exp) =>
        let
            val withType = A.TyRec(A.Scope(dataname, A.Plus types))
            (* dataname is not bound here - the recursive reference is bound to the abstract
             * type bound in the Some *)
            val tInTypes = List.map (A.typSubst 0 (A.TypVar("t", 0))) types
            val exposeFnType = A.Arr(A.TypVar("t", 0), A.Plus tInTypes)
            val exposeFn = A.Fn(withType, A.Scope(dataname ^ "exp", A.Unfold(A.Var(dataname ^ "exp", 0))))
            val pkgType = A.Some(A.Scope("t", (*arbitrary name ok here *)
                                 A.Prod([A.Prod(
                                              List.map (fn t => A.Arr(t, A.TypVar("t", 0))) tInTypes),
                                         exposeFnType])
                                ))
            fun typOpenBinder t =
                A.typShift ~1 (A.typSubst 0 (A.typShift 1 withType) t)
            val openedTypes = List.map typOpenBinder types;
            val sumTypeForFold = List.map (A.typShift 1) openedTypes;
            fun makeInjectionExprFromSummandType (i, t) =
                let val name = "summand" ^ Int.toString i
                in
                A.Fn(List.nth(openedTypes, i),
                     A.Scope(name,
                     A.Fold(withType,
                            A.PlusNth(i, A.Plus sumTypeForFold, A.Var(name, 0)))))
                end

            val fns = List.mapi makeInjectionExprFromSummandType types;
            val dtval = A.Impl(withType,
                               A.Tuple[A.Tuple fns, exposeFn],
                               pkgType)

            val openedPackageTermName = "li"
            val cutoff = (List.length types) + 1;
            val innerExp = A.Let(A.Arr(A.TypVar(dataname, 0), A.Plus types),
                                 A.ProdNth(1, A.Var(openedPackageTermName, (List.length types))),
                                 A.Scope("expose" ^ dataname,
                                 A.expShift cutoff 1 (* reach over expose *) exp));
            fun makeDecls i =
                if i = (List.length types) then innerExp
                else
                    A.Let(A.Arr(List.nth (types, i), A.TypVar(dataname, 0)),
                          A.ProdNth(i, A.ProdNth(0, A.Var(openedPackageTermName, i))),
                          A.Scope(List.nth (names, i),
                          makeDecls (i+1)))
        in
            A.Use(dtval, A.Scope(dataname, A.Scope(openedPackageTermName, makeDecls 0)))
        end
      | _ => e

fun elaborateDatatypes e = A.expMap elaborateDatatype e

fun eraseNamesInTyp t =
    let fun erase t =
            (case t of
                 A.TypVar(_, i) => A.TypVar("", i)
               | A.All(A.Scope(_, t')) => A.All(A.Scope("", t'))
               | A.Some(A.Scope(_, t')) => A.Some(A.Scope("", t'))
               | A.TyRec(A.Scope(_, t')) => A.TyRec(A.Scope("", t'))
               | _ => t
            )
    in A.typMap erase t end

fun typeEq (t : A.typ) (t' : A.typ) = ((eraseNamesInTyp t) = (eraseNamesInTyp t'))

fun typeof' ctx typCtx A.Zero = A.Nat
  | typeof' ctx typCtx A.TmUnit = A.Unit
  | typeof' ctx typCtx (A.Var (name, i)) =
    if i < 0 then raise VarWithNegativeDeBruijinIndex(name, i) else get ctx i
  | typeof' ctx typCtx (A.Succ e2) = (typeof' ctx typCtx e2)
  | typeof' ctx typCtx (A.ProdNth (i,e)) = let val A.Prod types = (typeof' ctx typCtx e) in List.nth (types, i) end
  | typeof' ctx typCtx (A.PlusNth (i, t, e)) =
    let val A.Plus types = t in
        if not (typeEq (List.nth (types, i)) (typeof' ctx typCtx e)) then (
            print "Sum type annotation:\n";
            printlnType (List.nth (types, i));
            print "does not match deduced type:\n";
            printlnType ((typeof' ctx typCtx e));
            raise IllTyped
        ) else
            A.Plus types
    end
  | typeof' ctx typCtx (A.Case (c, scs)) =
    let
        val A.Plus types = typeof' ctx typCtx c
        val A.Scope(_, firstBody) = List.hd scs
        val firstType = List.hd types
        val typeofFirstBranch = typeof' (firstType::ctx) typCtx firstBody
    in
        if not (ListPair.all (fn (t, A.Scope(_, e)) => (typeEq typeofFirstBranch (typeof' (t::ctx) typCtx e))) (types, scs)) then
            raiseIllTypedMsg "Case statement branches types do not agree"
        else
            typeofFirstBranch
    end
  | typeof' ctx typCtx (A.Fn (argType, A.Scope(argName, funcBody))) =
    if not (istype typCtx argType) then raiseIllTypedMsg "Function arg type is not a type."
    else A.Arr (argType, typeof' (argType::ctx) typCtx funcBody)
  | typeof' ctx typCtx (A.Let (vartype, varval, A.Scope(varname, varscope))) =
    if not (istype typCtx vartype) then
        raiseIllTypedMsg "Let var type is not a type"
    else if not (typeEq (typeof' ctx typCtx varval) vartype) then
        raiseIllTypedMsg "Let var type is not equal to deduced var value type."
    else
        typeof' (vartype::ctx) typCtx varscope
  | typeof' ctx typCtx (A.App (f, n)) =
    let val A.Arr (d, c) = typeof' ctx typCtx f
        val argType = typeof' ctx typCtx n
    in
        if not (typeEq d argType) then raise IllTyped
        else c
    end
  | typeof' ctx typCtx (A.Ifz (i, t, A.Scope(prev, e))) =
    let val Nat = typeof' ctx typCtx i
        val thenType = typeof' ctx typCtx t
        val elseType = typeof' (Nat::ctx) typCtx e
    in
        if not (typeEq thenType elseType) then raise IllTyped
        else thenType
    end
  | typeof' ctx typCtx (A.Tuple exps) = A.Prod (List.map (typeof' ctx typCtx) exps)
  | typeof' ctx typCtx (A.Rec (i, baseCase, A.Scope(prevCaseName, recCase))) =
    let val A.Nat = typeof' ctx typCtx i
        val t = typeof' ctx typCtx baseCase
        val t2 = typeof' (t::ctx) typCtx recCase
    in
        if not (typeEq t t2) then raise IllTyped else t
    end
  | typeof' ctx typCtx (A.Fix (typ, A.Scope(name, e))) = typeof' (typ::ctx) typCtx e
  | typeof' ctx typCtx (A.TypFn (A.Scope(name, e))) =
    let val ctx' = List.map (A.typShift 1) ctx
    in A.All(A.Scope(name, typeof' ctx' (NONE::typCtx) e)) end
  | typeof' ctx typCtx (A.TypApp (appType, e)) =
    if not (istype typCtx appType) then raise IllTyped else
    let val A.All(A.Scope(name, t)) = typeof' ctx typCtx e
    in
        typOpen appType t
    end
  | typeof' ctx typCtx (A.Impl (reprType, pkgImpl, pkgType)) =
    if not (istype typCtx reprType) then (
        print ("Package implementation representation type:\n" ^ A.Print.typToString(reprType) ^ "\nis not a type.\n");
        raise IllTyped
    ) else
    let val A.Some(A.Scope(name, pkgType')) = pkgType
        val expectedType = typOpen reprType pkgType'
        val deducedType = typeof' ctx typCtx pkgImpl
    in
        if not (typeEq deducedType expectedType) then
            raise IllTyped
        else
            pkgType
    end
  | typeof' ctx typCtx (A.Use (pkg, A.Scope(typeName, A.Scope(clientName, client)))) =
    let val A.Some(A.Scope(name, r)) = typeof' ctx typCtx pkg
        val ctx' = List.map (A.typShift 1) ctx
        val clientType = typeof' (r::ctx') (NONE::typCtx) client
        val resType = A.typShift ~1 clientType
    in
        if not (istype typCtx resType) then raise IllTyped else
        resType
    end
  | typeof' ctx typCtx (A.Fold(A.TyRec(A.Scope(name, t)) (*declared type*), e'(* binds a typ var *))) =
    let val ctx' = List.map (A.typShift 1) ctx
        val deduced = typeof' ctx' (NONE::typCtx) e'
        val finalType = A.TyRec(A.Scope(name, t))
        val unfoldedAtDepth = A.typSubst 0 (A.typShift 1 finalType) t
    in
        if not (typeEq deduced unfoldedAtDepth) then (
            print "Recursive type deduced type:\n";
            printlnType deduced;
            print "does not match unfolded declared type:\n";
            printlnType unfoldedAtDepth;
            raise IllTyped
         ) else
            finalType
    end
  | typeof' ctx typCtx (A.Fold(_ , e'(* binds a typ var *))) =
    raiseIllTypedMsg "Fold type argument must be a recursive type"
  | typeof' ctx typCtx (A.Unfold(e')) =
    let val A.TyRec(A.Scope(name, t)) = typeof' ctx typCtx e' in
        typOpen (A.TyRec(A.Scope(name, t))) t
    end

fun typeof e = typeof' [] [] e

fun isval e =
    case e of
        A.Zero => true
      | A.TmUnit => true
      | A.Succ(n) => isval n
      | A.Fn(_, _) => true
      | A.Let(_, _, _) => false
      | A.Tuple exps => List.all isval exps
      | A.TypFn _  => true
      | A.Impl(_, pkgImpl, _) => isval pkgImpl
      | A.PlusNth(_, _, e') => isval e'
      | A.Fold(t, e') => isval e'
      | _ => false

fun step e =
    let val _ = typeof' [] [] e in
    if isval e then e else
    case e of
        A.Succ(n) => if not (isval n) then A.Succ(step n) else e
      | A.ProdNth (i, n)  => if not (isval n) then A.ProdNth(i, step n) else
                    let val A.Tuple exps = n in List.nth (exps, i) end
      | A.Tuple exps =>
        let fun recr [] = []
              | recr (e::es) = if isval e then e::(recr es) else (step e)::es
        in
            A.Tuple (recr exps)
        end
      | A.App(f, n) => if not (isval f) then A.App(step f, n)
                     else (if not (isval n) then A.App(f, step n)
                           else let val A.Fn(t, A.Scope(argName, f')) = f
                           in
                               (* plug `n` into `f'` *)
                               A.expSubst 0 n f'
                           end
                          )
      | A.Ifz(i, t, A.Scope(prev, e')) =>
            if not (isval i) then A.Ifz(step i, t, A.Scope(prev, e'))
            else (case i of
                      A.Zero => t
                    | A.Succ i' => A.expSubst 0 i' e'
                    | _ => raiseIllTypedMsg "ifz conditional must be an integer")
      (* BUG? should this eval varval before expSubst? should it eval varscope before expSubst? *)
      | A.Let (vartype, varval, A.Scope(varname, varscope)) => A.expSubst 0 varval varscope
      | A.Var (name, x) => (if x < 0 then raise VarNotInContext else A.Var (name, x))
      | A.Rec (A.Zero, baseCase, _) => baseCase
      | A.Rec (A.Succ(i), baseCase, sc as A.Scope(_, recCase)) =>
            (* Doesn't evaluate recursive call if not required. *)
            A.expSubst 0 (A.Rec(i, baseCase, sc)) recCase
      | A.Rec (i, baseCase, sc) =>
            if not (isval i) then
                A.Rec(step i, baseCase, sc)
            else raise No
      | A.Fix(t, A.Scope(name, body)) => A.expSubst 0 e body
      | A.TypFn _ => raise No (* Already isval *)
      | A.TypApp (t, e') =>
            if not (isval e') then (A.TypApp (t, step e'))
            else
                let val A.TypFn(A.Scope(name, e'')) = e' in
                    A.substTypeInExp t e''
                end
      | A.Impl(reprType, pkgImpl, pkgType) =>
            if not (isval pkgImpl) then A.Impl(reprType, step pkgImpl, pkgType) else
            if not (isval e) then raise No else
            e
      | A.Use (pkg, sc as A.Scope(typeName, A.Scope(clientName, client))) =>
            if not (isval pkg) then A.Use (step pkg, sc) else
            (* Note that there's no abstract type at runtime. *)
           (case pkg of
                A.Impl(reprType', pkgImpl', _) =>
                    A.expSubst 0 pkgImpl' (A.substTypeInExp reprType' client)
              | _ => raise No
           )
      | A.PlusNth (i, t, e') =>
            if not (isval e') then A.PlusNth(i, t, step e')
            else e
      | A.Case (c, scs) =>
        if not (isval c) then A.Case(step c, scs)
        else (
            case c of
                 A.PlusNth(i, _, e') => let val A.Scope(_, body) = List.nth (scs, i) in A.expSubst 0 e' body end
               | _ => raise IllTyped
        )
      | A.Fold (t, e') => if not (isval e') then A.Fold(t, step e')
                        else (let val true = isval e in e end)
      | A.Unfold e' => if not (isval e') then A.Unfold (step e')
                     else (let val A.Fold(t, e'') = e' in e'' end)
      | _ => if (isval e) then e else raise No
    end

fun eval e = if isval e then e else eval (step e)

fun run src =
    let val ast = Parse.parse src
        val ast = setDeBruijnIndex ast [] []
        val ast = elaborateDatatypes ast
        val _ = typeof ast
    in eval ast end

fun runFile filename =
    let val ast = Parse.parseFile filename
        val ast = setDeBruijnIndex ast [] []
        val ast = elaborateDatatypes ast
        val _ = typeof ast
    in eval ast end

end (* structure Thon *)
