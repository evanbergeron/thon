# thon

thon is a small programming language. Here's an example program that
verifies the singleton list is not empty.

```
data list:
    nil unit
    cons nat * list

fun isempty(l list) nat:
    case exposelist(l):
        empty: true
        not: false

isempty(cons(z, nil(unit)))
```

thon has natural numbers, functions, recursion, binary product and sum
types, polymorphism, existential packages (a formalization of
interfaces), recursive types, and binary algebraic datatypes.

Thon is currently under syntactic refactoring, so this README
regrettably mixes examples of the two syntaxes (and likely will
continue to do so for some time).

## natural numbers

`z` is the natural number 0. `s(z)` is 1 (the succesor of
one). `s(s(z))` is 2, and so on.

## functions

In thon, functions are expressions just like numbers are. thon
supports anonymous functions and named, recursive functions.

Here are some example anonymous functions.

```
fn (x nat) => x
fn (x nat) => fn (y nat) => y
```

Functions are applied to their arguments like so:

```
(fn (x nat) => x)(z)
```

Here's a divide-by-two function:

```
fun divbytwo(n nat) nat:
    ifz n:
        z: z
        s(p):
            ifz p:
                z: z
                s(q): s(divbytwo(q))

divbytwo (s(s(s(s(z)))))
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
(* Legacy syntax *)
fix loop : nat in loop
```

## variables

```
let x nat = z
e
```
binds the name `x` in the expression `e`.

## polymorphism

Polymorphism lets us reuse code you wrote for many different types,
with the guarantee that the code will behave the same for all types.


```
poly t -> \ x : t -> x
```
is the polymorphic identity function. Feed it a type to get the
identity function on that type. e.g.

```
(* Legacy syntax *)
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
(fn (x nat) => x,
 fn (x nat) => x)
```
The second stores in the number in a tuple (for no real good reason -
you didn't write this code, it's not your fault it does it this way).

```
(fn (x nat) => (x, z),
 fn (tup nat * nat) => fst tup)
```
(The fst syntax is only implemented in the legacy syntax).

Now each of these implementations can be packed away with the (legacy)
syntax

```
(* Legacy syntax *)
impl some t. ((nat -> t) * (t -> nat)) with nat as
(
    ((*set*) \ x : nat -> x,
    (*get*) \ x : nat -> x)
)
```
and

```
(* Legacy syntax *)
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

## binary data types

```
data list:
    nil unit
    cons nat * list
```

is a datatype for lists of the natural numbers. Thon currently
supports two cases inside datatypes.

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
fun isone(n nat) nat:
    ifz n:
        z: z
        s(p):
            ifz p:
                z: s(z)
                s(p): z

fun iseven(n nat) nat:
    ifz n:
        z: s(z)
        s(p):
            ifz iseven(p):
                z: s(z)
                s(p): z

fun divbytwo(n nat) nat:
    ifz n:
        z: z
        s(p):
            ifz p:
                z: z
                s(q): s(divbytwo(q))

fun multbythree(n nat) nat:
    ifz n:
        z: z
        s(p): s(s(s(multbythree(p))))

fun collatz(n nat) nat:
    ifz isone(n):
        z:
            ifz iseven(n):
                z: collatz(s(multbythree(n)))
                s(p): collatz(divbytwo(n))
        s(p): s(z)

collatz(s(s(z)))
```

[relevant xkcd](https://xkcd.com/710/)