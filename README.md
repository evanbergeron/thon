# thon

thon is a small programming language. Here's an example program that
verifies the singleton list is not empty.

```
data list = nil unit | cons nat * list in
fun isempty : list -> nat =
  \ natlist : list ->
  case exposelist natlist of
      empty -> S Z
    | not -> Z
in (isempty (cons (Z, (nil unit))))
```

thon has natural numbers, functions, recursion, binary product and sum
types, polymorphism, existential packages (a formalization of
interfaces), recursive types, and binary algebraic datatypes.

## natural numbers

`Z` is the natural number 0. `S Z` is 1 (the succesor of one). `S S Z` is 2, and so on.

## functions

In thon, functions are expressions just like numbers are. thon
supports anonymous functions and named, recursive functions.

Here are some example anonymous functions.

```
\ x : nat -> x
\ x : nat -> (\ y : nat -> y)
```

Functions are applied to their arguments by juxtaposition.

```
((\ x : nat -> x) Z)
```

Here's a divide-by-two function:

```
fun divbytwo : nat -> nat =
  \ n : nat ->
    ifz n of
      Z -> Z
    | S p -> ifz p of Z -> Z | S p' -> (S (divbytwo p'))
in divbytwo (S S S S Z)
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
fix loop : nat in loop
```

## variables

```
let x : nat = Z in x
```
binds the name `x` in the expression following the `in` keyword.

## polymorphism

Polymorphism lets us reuse code you wrote for many different types,
with the guarantee that the code will behave the same for all types.

```
poly t -> \ x : t -> x
```
is the polymorphic identity function. Feed it a type to get the
identity function on that type. e.g.

```
(poly t -> \ x : t -> x) nat
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
((*set*) \ x : nat -> x,
 (*get*) \ x : nat -> x)
```
The second stores in the number in a tuple (for no real good reason -
you didn't write this code, it's not your fault it does it this way).

```
((*set*) \ x : nat -> (x, Z),
 (*get*) \ tup : (nat * nat) -> fst tup)
```

Now each of these implementations can be packed away with the syntax

```
impl some t. ((nat -> t) * (t -> nat)) with nat as
(
    ((*set*) \ x : nat -> x,
    (*get*) \ x : nat -> x)
)
```
and

```
impl some t. ((nat -> t) * (t -> nat)) with (nat, nat) as
(
    ((*set*) \ x : nat -> (x, Z),
    (*get*) \ tup : (nat * nat) -> fst tup)
)
```

Both of these expression have type `((nat -> T) * (T -> nat))` for
some type `T`. Note this is an existential claim, hence the name
existential packages.

An implementation can be used as follows:

```
let setget : some t. ((nat -> t) * (t -> nat)) =
    (impl some t. ((nat -> t) * (t -> nat)) with nat as
    (
        ((*set*) \ x : nat -> x,
        (*get*) \ x : nat -> x)
     ))
in use setget as (sg, t) in
let set : (nat -> t) = fst sg in
let get : (t -> nat) = snd sg in
let s : t = set (S S Z) in
let g : nat = get s in
g
```

Note that since the type variable `t` declared in the `use` clause is
abstract, we can equivalently use the other implementation.

## recursive types

`u nats. (unit | (nat * nats))` is the type of lists natural numbers.

```
fold u nats.  (unit | (nat * nats))
with left unit : (unit | (nat * (u nats. (unit | (nat * nats)))))
```

is the empty list of natural numbers.

```
\ (nat * (u nats. (unit | nat * nats))) ->
   fold u nats. (unit | nat * nats) with
   right 0 : (unit | nat * (u nats. (unit | nat * nats)))
```

is a function that takes a pair (nat, natlist) and prepends nat to natlist.

## algebraic datatypes

Algebraic datatypes are a combination of three different language
features: sum types, recursive types, and existential types.

Quoting from "A type-theoretic interpretation of standard ML",

> The underlying implementation type is defined to be a recursive sum type, with one summand corresponding to each constructor in the declaration. The constructors are represented by total functions that inject values into the appropriate summand of the recursive type.

`examples/manual-datatype.thon` provides an example of how a `data List = Nil | Cons of int * List` is elaborated.

Here's an example in thon of calculating the depth of a binary search tree.

```
data tree = Nil unit | Node nat * (tree * tree)

in let decr : nat -> nat =
  \ x : nat ->
    ifz x of
      Z -> Z
    | S p -> p

in let sub : nat -> nat -> nat =
  \ x : nat ->
  \ y : nat ->
    rec y of
      Z -> x
    | prevRec -> (decr prevRec)

in let lt : nat -> nat -> nat =
  \ x : nat ->
  \ y : nat ->
  ifz (sub y x) of
    Z -> Z
  | S p -> S Z

in fun insert : nat -> tree -> tree =
    \ n : nat ->
    \ bst : tree ->
    case exposetree bst of
        empty -> Node(n, ((Nil unit), (Nil unit)))
      | natAndNodeAndNode ->
        let thisNode : nat = fst natAndNodeAndNode in
        let leftNode : tree = fst (snd natAndNodeAndNode) in
        let rightNode : tree = snd (snd natAndNodeAndNode) in
        ifz (lt n thisNode) of
            Z -> Node(n, (leftNode, (insert n rightNode)))
          | S p -> (Node(n, ((insert n leftNode), rightNode)))

in fun depth : tree -> nat =
    \ t : tree ->
    case exposetree t of
        empty -> Z
      | natAndNodeAndNode ->
        let leftDepth : nat = depth (fst (snd natAndNodeAndNode)) in
        let rightDepth : nat = depth (snd (snd natAndNodeAndNode)) in
        ifz (lt leftDepth rightDepth) of
            Z -> S leftDepth
          | S p -> S rightDepth

(* This tree has depth 2.
 *
 *     1
 *    / \
 *   0   2
 *)
in (depth (insert (S S Z) (insert (Z) (insert (S Z) (Nil unit)))))
```

## thanks

I've mostly been working out of Bob Harper's "Practical Foundations for
Programming Languages," though Pierce's "Types and Programming Languages" has
been a useful source of examples and exposition as well. I am also
grateful to Rob Simmons and every other contributor to the SML starter
code for CMU's Fall 2016 compilers course.

## install (ubuntu 20)

Wow, you read this far! (or scrolled this far, at least) If you'd like
to program in thon, the code is publicly available.

    $ git clone https://git.sr.ht/~thon/thon
    $ sudo apt install smlnj ml-yaxx ml-lex ml-lpt
    $ sml
    - CM.make "path/to/your/git/clone/thon.cm";
    - Thon.run "some thon program here";

If you figure out install instructions on mac or windows or have any
other questions or comments, please email me at
bergeronej@gmail.com. I would love to hear from you!

## collatz conjecture

A fun program I wrote after adding recursion. Pretty much all the code
I've written in thon is available through the git repo.

```
let isone : nat -> nat =
  \ n : nat ->
    ifz n of
      Z -> Z (*false*)
    | S p -> ifz p of Z -> S Z | S p -> Z
in fun iseven : nat -> nat =
  \ n : nat ->
    ifz n of
      Z -> S Z (*true*)
    | S p -> ifz (iseven p) of Z -> S Z | S p -> Z
in fun divbytwo : nat -> nat =
  \ n : nat ->
    ifz n of
      Z -> Z
    | S p -> ifz p of Z -> Z | S p' -> (S (divbytwo p'))
in fun multbythree : nat -> nat =
  \ n : nat ->
    ifz n of
      Z -> Z
   | S nminusone -> S S S (multbythree nminusone)
in fun collatz : nat -> nat =
  \ n : nat ->
    ifz (isone n) of
      Z -> (
        ifz (iseven n) of
          Z -> collatz (S (multbythree n))
        | S p -> (collatz (divbytwo n))
      )
    | S p -> (S Z)
in (collatz (S S Z))
```

[relevant xkcd](https://xkcd.com/710/)