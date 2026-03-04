# thon

thon is a small programming language. Here's an example program that
checks whether a singleton list is empty.

```
DATA list IS
  nil(UNIT) | cons(NAT * list) IN
DECLARE isempty : list -> NAT IS
  FIX isempty : list -> NAT IS
    FN(natlist : list)
      CASE exposelist(natlist) OF
        WHEN empty => SUCC(ZERO)
      | WHEN not => ZERO IN
isempty(cons((ZERO, nil(UNIT))))
```

thon has natural numbers, functions, recursion, binary product and sum
types, polymorphism, existential packages (a formalization of
interfaces), recursive types, and binary algebraic datatypes.

## natural numbers

`ZERO` is the natural number 0. `SUCC(ZERO)` is 1 (the successor of zero). `SUCC(SUCC(ZERO))` is 2, and so on.

## functions

In thon, functions are expressions just like numbers are. thon
supports anonymous functions and named, recursive functions.

Here are some example anonymous functions.

```
FN(x : NAT) x
FN(x : NAT) FN(y : NAT) y
```

Functions are applied to their arguments with parentheses.

```
(FN(x : NAT) x)(ZERO)
```

Here's a divide-by-two function:

```
DECLARE divbytwo : NAT -> NAT IS
  FIX divbytwo : NAT -> NAT IS
    FN(n : NAT)
      IFZ n OF ZERO THEN ZERO
      ELSE p THEN
        IFZ p OF ZERO THEN ZERO
        ELSE p' THEN SUCC(divbytwo(p')) IN
divbytwo(SUCC(SUCC(SUCC(SUCC(ZERO)))))
```
If the number is zero, we're done. Otherwise, it has some predecessor
number `p`. If `p` is zero, then return zero (taking the
floor). Otherwise, recurse on the predecessor of the predecessor `n-2`
and add one to whatever that gave us.

Under the hood, recursive functions are implemented as a fixed point
expression that substitutes itself in for itself. It's like a
recursive function, but it doesn't have to be a function, it can be
any expression. Here's an amusing way to loop forever:

```
FIX loop : NAT IS loop
```

## variables

```
DECLARE x : NAT IS ZERO IN x
```
binds the name `x` in the expression following the `IN` keyword.

## polymorphism

Polymorphism lets us reuse code you wrote for many different types,
with the guarantee that the code will behave the same for all types.

```
GENERIC t IS FN(x : t) x
```
is the polymorphic identity function. Feed it a type to get the
identity function on that type. e.g.

```
(GENERIC t IS FN(x : t) x)[NAT]
```
evaluates to the identity function on natural numbers.

## existential packages hide types

They let us write a piece of code with a private implementation
type. Clients that use this implementation don't know what type was
used. This property is enforced by the type system.

Ok, so how do we use them in thon? Let's consider a sort-of-silly
example.

The interface is just "set" and "get." We feed in a number, get a
number back. However the implementation stores the number is up to
them.

We have two implementations with two separate implementation
types. The first just holds on to the number.
```
((*set*) FN(x : NAT) x,
 (*get*) FN(x : NAT) x)
```
The second stores in the number in a tuple (for no real good reason -
you didn't write this code, it's not your fault it does it this way).

```
((*set*) FN(x : NAT) (x, ZERO),
 (*get*) FN(tup : NAT * NAT) FST(tup))
```

Now each of these implementations can be packed away with the syntax

```
PACKAGE NAT IS
  ((*set*) FN(x : NAT) x,
   (*get*) FN(x : NAT) x)
AS SOME t. (NAT -> t) * (t -> NAT)
```
and

```
PACKAGE (NAT * NAT) IS
  ((*set*) FN(x : NAT) (x, ZERO),
   (*get*) FN(tup : NAT * NAT) FST(tup))
AS SOME t. (NAT -> t) * (t -> NAT)
```

Both of these expression have type `(NAT -> T) * (T -> NAT)` for
some type `T`. Note this is an existential claim, hence the name
existential packages.

An implementation can be used as follows:

```
DECLARE setget : SOME t. (NAT -> t) * (t -> NAT) IS
  PACKAGE NAT IS
    ((*set*) FN(x : NAT) x,
     (*get*) FN(x : NAT) x)
  AS SOME t. (NAT -> t) * (t -> NAT) IN
OPEN setget AS (t, sg) IN
DECLARE set : NAT -> t IS FST(sg) IN
DECLARE get : t -> NAT IS SND(sg) IN
DECLARE s : t IS set(SUCC(SUCC(ZERO))) IN
DECLARE g : NAT IS get(s) IN
g
```

Note that since the type variable `t` declared in the `OPEN` clause is
abstract, we can equivalently use the other implementation.

## recursive types

`REC nats. UNIT | NAT * nats` is the type of lists of natural numbers.

```
FOLD[REC nats. UNIT | NAT * nats](
  LEFT[UNIT | NAT * (REC nats. UNIT | NAT * nats)](UNIT)
)
```

is the empty list of natural numbers.

```
FN(p : NAT * (REC nats. UNIT | NAT * nats))
  FOLD[REC nats. UNIT | NAT * nats](
    RIGHT[UNIT | NAT * (REC nats. UNIT | NAT * nats)](p)
  )
```

is a function that takes a pair (nat, natlist) and prepends nat to natlist.

## algebraic datatypes

Algebraic datatypes are a combination of three different language
features: sum types, recursive types, and existential types.

Quoting from "A type-theoretic interpretation of standard ML",

> The underlying implementation type is defined to be a recursive sum type, with one summand corresponding to each constructor in the declaration. The constructors are represented by total functions that inject values into the appropriate summand of the recursive type.

Here's an example in thon of calculating the depth of a binary search tree.

```
DATA tree IS
  Nil(UNIT) | Node(NAT * (tree * tree)) IN

DECLARE decr : NAT -> NAT IS
  FN(x : NAT)
    IFZ x OF ZERO THEN ZERO ELSE p THEN p IN

DECLARE sub : NAT -> NAT -> NAT IS
  FN(x : NAT)
    FN(y : NAT)
      (FIX subhelp : NAT -> NAT IS
        FN(y : NAT)
          IFZ y OF ZERO THEN x
          ELSE py THEN decr(subhelp(py)))(y) IN

DECLARE lt : NAT -> NAT -> NAT IS
  FN(x : NAT)
    FN(y : NAT)
      IFZ sub(y)(x) OF ZERO THEN ZERO
      ELSE p THEN SUCC(ZERO) IN

DECLARE insert : tree -> NAT -> tree IS
  FIX insert : tree -> NAT -> tree IS
    FN(bst : tree)
      FN(n : NAT)
        CASE exposetree(bst) OF
          WHEN empty => Node((n, (Nil(UNIT), Nil(UNIT))))
        | WHEN natAndNodeAndNode =>
            DECLARE thisNode : NAT IS FST(natAndNodeAndNode) IN
            DECLARE leftNode : tree IS FST(SND(natAndNodeAndNode)) IN
            DECLARE rightNode : tree IS SND(SND(natAndNodeAndNode)) IN
            IFZ lt(n)(thisNode) OF
              ZERO THEN Node((thisNode, (leftNode, insert(rightNode)(n))))
            ELSE p THEN Node((thisNode, (insert(leftNode)(n), rightNode))) IN

DECLARE depth : tree -> NAT IS
  FIX depth : tree -> NAT IS
    FN(t : tree)
      CASE exposetree(t) OF
        WHEN empty => ZERO
      | WHEN natAndNodeAndNode =>
          DECLARE leftDepth : NAT IS depth(FST(SND(natAndNodeAndNode))) IN
          DECLARE rightDepth : NAT IS depth(SND(SND(natAndNodeAndNode))) IN
          IFZ lt(leftDepth)(rightDepth) OF
            ZERO THEN SUCC(leftDepth)
          ELSE p THEN SUCC(rightDepth) IN

(* This tree has depth 2.
 *
 *     1
 *    / \
 *   0   2
 *)
depth(insert(insert(insert(Nil(UNIT))(SUCC(ZERO)))(ZERO))(SUCC(SUCC(ZERO))))
```

## thanks

I've mostly been working out of Bob Harper's "Practical Foundations for
Programming Languages," though Pierce's "Types and Programming Languages" has
been a useful source of examples and exposition as well. I am also
grateful to Rob Simmons and every other contributor to the SML starter
code for CMU's Fall 2016 compilers course.

## install

If you'd like to program in thon, here's how I use it.

    $ git clone git@github.com:evanbergeron/thon.git
    $ sudo apt install smlnj
    $ sml
    - CM.make "path/to/your/git/clone/thon.cm";
    - Thon.run "some thon program here";
    - Thon.runFile "path/to/foo.thon";

## collatz conjecture

A fun program I wrote after adding recursion. Pretty much all the code
I've written in thon is available through the git repo.

```
DECLARE isone : NAT -> NAT IS
  FN(n : NAT)
    IFZ n OF ZERO THEN ZERO
    ELSE p THEN
      IFZ p OF ZERO THEN SUCC(ZERO)
      ELSE p THEN ZERO IN
DECLARE iseven : NAT -> NAT IS
  FIX iseven : NAT -> NAT IS
    FN(n : NAT)
      IFZ n OF ZERO THEN SUCC(ZERO)
      ELSE p THEN
        IFZ iseven(p) OF ZERO THEN SUCC(ZERO)
        ELSE p THEN ZERO IN
DECLARE divbytwo : NAT -> NAT IS
  FIX divbytwo : NAT -> NAT IS
    FN(n : NAT)
      IFZ n OF ZERO THEN ZERO
      ELSE p THEN
        IFZ p OF ZERO THEN ZERO
        ELSE p' THEN SUCC(divbytwo(p')) IN
DECLARE multbythree : NAT -> NAT IS
  FIX multbythree : NAT -> NAT IS
    FN(n : NAT)
      IFZ n OF ZERO THEN ZERO
      ELSE nminusone THEN SUCC(SUCC(SUCC(multbythree(nminusone)))) IN
DECLARE collatz : NAT -> NAT IS
  FIX collatz : NAT -> NAT IS
    FN(n : NAT)
      IFZ isone(n) OF
        ZERO THEN
          IFZ iseven(n) OF
            ZERO THEN collatz(SUCC(multbythree(n)))
          ELSE p THEN collatz(divbytwo(n))
      ELSE p THEN SUCC(ZERO) IN
collatz(SUCC(SUCC(ZERO)))
```

[relevant xkcd](https://xkcd.com/710/)
