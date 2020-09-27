# thon

thon is a small programming language. Here's an example program that
verifies the empty list is empty.

```
fun isempty : (data l = (unit | nat * l)) -> nat =
  \ natlist : (data l = (unit | nat * l)) ->
        (case (unfold natlist) of
           empty -> S Z
         | not -> Z)
in let nil : (data l = (unit | nat * l)) =
    fold data l = (unit | nat * l) with
    left unit : (unit
               | nat * (data l = (unit | nat * l)))
in
(isempty nil)
```

thon has natural numbers, functions, recursion, binary product and sum
types, parametric polymorphism, existential packages (a formalization of
interfaces), and recursive types.

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

## parametric polymorphism

Parametric polymorphism lets us reuse code you wrote for many
different types, with the guarantee that the code will behave the
same for all types.

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

(Disclaimer, the syntax here needs to be fixed a bit still, it was
made before there were variable names and so now I need to thread a
couple more names through...)

Now each of these implementations can be packed away with the syntax

```
impl (nat -> t, t -> nat) with nat as
(
    ((*set*) \ x : nat -> x,
    (*get*) \ x : nat -> x)
)
```
and

```
impl (nat -> t, t -> nat) with (nat * nat) as
(
    ((*set*) \ x : nat -> (x, Z),
    (*get*) \ tup : (nat * nat) -> fst tup)
)
```

Both of these expression have type `((nat -> T) * (T -> nat))` for
some type `T`. Note this is an existential claim, hence the name
existential packages.

These implementations can be used interchangably by saying

```
use (...either implementation...) as (pkg, t) in
(... some use of pkg ...)
```

Still TODO for me - the `impl` expression need to be clear about what
the abstracted-over type name is. This was fine back when we just
specified De Bruijin indices in the typename... but now we need to
define a type variable name, just like we do for functions.

## recursive types

`u.(unit | (nat * 0))` is the type of lists natural numbers. The `u`
is an approximation of the fancy type theory lowercase mu. Eventually
this will be more reasonable.

```
fold u . (unit | (nat * 0))
with left unit : (unit |  (nat * (u . (unit | (nat * 0)))))
```

is the empty list of natural numbers. Haha I will add better syntax for this over time...

```
\ (nat * (u. (unit |  (nat * 0)))) ->
   fold u.(unit |  (nat * 0)) with
   right 0 : (unit | (nat * (u. (unit |  (nat * 0)))))
```

is a function that takes a pair (nat, natlist) and prepends nat to natlist.

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
      Z -> Z (*true*)
    | S p -> ifz p of Z -> S Z | S p -> Z
in let iseven : nat -> nat = fix rc : nat -> nat in
  \ n : nat ->
    ifz n of
      Z -> S Z (*true*)
    | S p -> ifz (rc p) of Z -> S Z | S p -> Z
in let divbytwo : nat -> nat = fix rc : nat -> nat in
  \ n : nat ->
    ifz n of
      Z -> Z
    | S p -> ifz p of Z -> Z | S p' -> (S (rc p'))
in let multbythree : nat -> nat =
  \ n : nat ->
    rec n of
      Z -> Z
   | prevRec -> S S S prevRec
in let collatz : nat -> nat = fix rc : nat -> nat in
  \ n : nat ->
    ifz (isone n) of
      Z -> (
        ifz (iseven n) of
          Z -> rc (S (multbythree n))
        | S p -> (rc (divbytwo n))
      )
    | S p -> (S Z)
in (collatz (S S Z))
```

[relevant xkcd](https://xkcd.com/710/)