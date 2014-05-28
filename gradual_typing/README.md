Gradual Typing
==============


This is a rather small extension of the Damas-Hindley-Milner unification-based type inference
algorithm, which allows programmers to combine static and dynamic types in a single language.
In addition to standard types and type schemes (polymorphic types), it supports a special
*dynamic* type, which is automatically cast to any other type as necessary.


Overview
--------

Statically and dynamically typed languages both have their undeniable strenghts and weaknesses,
and are both used to construct huge, complex software systems. In the recent years, there has
been a surge of interest in combining their benefits: type `dynamic` was added to C#, an
`invokedynamic` instruction was added to JVM, JavaScript successors TypeScript and Dart
provide optional type annotations, ... The general idea is to give the programmers the benefits
of static typing (earlier detection of errors and faster execution speed) while allowing them
to bypass the static type system when necessary or convenient (e.g. when protoyping new
functionality or handling dynamic data formats such as JSON). 

This implementation explores the union of static and dynamic typing from a type-theoretic
perspective, following the work of Jeremy G. Siek and collaborators. First, the topics of
*gradual type-checking* and *gradual type-inference* are discussed, followed by an explanation
of a gradual type-inference algorithm and a discussion of related research. The notation `?`
will be used to denote the dynamic type.


Gradual type-checking
---------------------

The stated goal of gradual type-checking is very simple: programs which are fully-annotated
(every term has a static type) are completely (statically) type-safe. Fulfilling this goal in
presence of dynamic types has turned out to be quite elusive. To achieve the feeling of
dynamically-typed languages, we want to be able to seamlessly transition between statically
and dynamically typed values. This means that implicit casts from type `?` to static types
(e.g. `int`, `bool` and `int -> int`) must be allowed, as well as implicit casts from static
types back to type `?`. One way to achieve this is to use subtyping; this was attempted by
Satish Thatte in his paper Quasi-static typing [1]. However, subtyping is a transitive
relation, meaning that if `int <: ?` and `? <: bool`, then `int <: bool`, which is
not something we want.

In their paper [Gradual Typing for Functional Languages][gradual], Jeremy G. Siek and
Walid Taha propose a different way of treating `?` based on *type consistency* (`~`), which
is *not* a transitive relation. In short, `?` is consistent with everything, base types are
consistent only with themselves, and function types are consistent if their parameter and
return types are consistent.

```
? ~ int
int -> bool ~ ?
int -> int ~ ? -> int
? -> int ~ bool -> int
? -> int ~ (int -> int) -> int
```

Note that since `~` is not transitive, we do not have `int -> int ~ bool -> int` even though 
`int -> int ~ ? -> int` and `? -> int ~ bool -> int`. Furthermore, type consistency is symmetric,
which makes the type-checking algorithm considerably simpler (compared to subtyping).

Using type compatibility, we can type-check a gradually-typed program by implicitly converting
a type into any consistent type as necessary. This is quite similar to the way unbound type
variables are treated, except that each occurrence of type `?` is treated as a fresh type variable.


Gradual type inference
----------------------

To make this type system practical, we must extend the gradual type-checking algorithm
with a gradual type inference algorithm. The type inference algorithm should do what type
inference algorithms usually do: allow the programmer to omit most, if not all, type annotations
in programs that do not use dynamic types (i.e. that have no variables and parameters with
type `?` and call no functions returning `?`). Meanwhile, the algorithm should not
obstruct the programmer when he or she wants to use dynamic types.

```
let f1(x) = x + 1

let f2(x) = if not x then x + 1 else 0

let f3(x : ?) = if not x then x + 1 else 0
```

The type inference algorithm should correctly infer that the type of parameter `x` of function
`f1` is `int`, based on its use as an argument to the `+` operator. Function `f2` should be
rejected by the algorithm, because no statically-typed value can be used both as a `bool` and
an `int`. In particular, inferring `x : ?` for function `f2` is not a desired outcome of the
type inference algorithm. However, it should infer type `? -> int` for function `f3`, deferring
the type-checks to runtime (at runtime, `f3(true)` will not result in a type error).

In general, we want the inference algorithm to propagate `?`, but we do not want it to introduce
any fresh `?`. This idea was formalized by Jeremy G. Siek and Manish Vachharajani in their paper
[Gradual Typing with Unification-based Inference][inference] using the *less or equally
informative* relation and the requirement that the types assigned to unifiable type variables
are at least as informative as any of the types constraining the type variable.

In the type inference algorithm, this requirement is satisfied by a very simple rule: an
ordinary (non-dynamic) type variable unified with a dynamic type becomes a dynamic type
variable, and an ordinary or dynamic type variable unified with a type other than `?` is
substituted for that type. In essence, the type inference algorithm tracks the lower bound
of a type variable, which can only move from less informative to more informative.


Implementation
--------------

In their paper, Siek and Vachharajani describe a 2-step type inference algorithm, consisting
of a syntax-directed constraint generation step, followed by a constraint solving step. This
implementation, while inspired by their algorithm, is instead more similar to Algorithm W,
interleaving constraint generation and constraint solving steps. It extends their algorithm
in two significant ways: it handles let-polymorphism (in the same manner as Algorithm W) and
supports *freezing* of dynamic types in variables bound by `let` expressions, allowing them to
be reused multiple times in different contexts.

The main changes between `algorithm_w` and this implementation can be seen in file `infer.ml` [here][git-diff].
We extend the expressions of `algorithm_w` by adding type annotations to function parameters
(`fun (x : int) -> x + 1`), let-bound variables (`let x : ? = 1`) and standalone expressions
(`f(x) : int`).  The setting `dynamic_parameters` controls whether function parameters without
type annotations are treated as having dynamic types (as in dynamically-typed languages) or as
statically-typed variables with yet-unknown types. For examples, `fun g -> g(true)` can be
treated as `fun (g : ?) -> g(true)` or as `fun (g : some[a] a) -> g(true)` (syntax sugar allows
the latter to be written as `fun (g : _) -> g(true)`), for which the system infers the type
`forall[a] (bool -> a) -> a`.

We also introduce type constructor `TDynamic`, used to represent `?`. However, `TDynamic`
is only used to represent type `?` for variables in type environment; as soon as the variable
is used, `TDynamic` is instantiated and replaced with a fresh *dynamic type variable*, which
is represented by constructor `Unbound` but distinguished from an *ordinary type variable* with
a boolean flag. This is not unlike the treatment of polymorphic types in Algorithm W; indeed,
when a variable with a polymorphic type is used, its type is instantiated by replacing all
occurrences of generic type variables with fresh ordinary type variables. Conversely, just as
polymorphic types can be recovered at let-bindings by generalizing free ordinary type variables,
so can dynamic type variables be *frozen* at let-bindings by replacing them with `TDynamic`
types (this is controlled by the setting `freeze_dynamic`).

The idea that makes polymorphic types polymorphic and dynamic types dynamic is that fresh type
variables can be unified with any other type. However, each type variable can only be unified
once, with a single type. This can be a problem when using functions such as
`duplicate : forall[a] a -> pair[a, a]`, which duplicate type variables. The following results
in an error:

```
choose(pair([1], [true]), duplicate([]))

# ERROR: cannot unify types bool and int
```

To avoid this issue with dynamic types, we duplicate dynamic type variables after every function
call, which is equivalent to first generalizing and then instantiating the result type, the trick
used in `first_class_polymorphism`.

```
let x : ? = 1

let y = choose(pair(1, true), duplicate(x))

# y : pair[int, bool]
```


Discussion
----------

This implementation focuses on gradual typing in the context of functional languages. Similar
ideas, but in a context of object-oriented languages, was explored by Jeremy Siek and Walid Taha
in the paper [Gradual Typing for Objects][objects]. It was also researched by other authors, for
example in [2], [3] and [4]. More recent research can be found by looking through the papers
citing the above on Google Scholar. 

Although gradual type inference is not complicated, the implementation of a gradually typed
language can be tricky, especially when a statically-typed function is used in dynamic code or
when a dynamically-typed function is cast to a static type. One issue is accurate reporting of
runtime errors; for example, when a function `inc : int -> int` is cast to a dynamic type and
called with the argument `true`, the system should report an error that the function was *called*
with an argument of the wrong type.  However, if a dynamic function `fun (x : ?) -> not x` is
cast to type `bool -> int` and applied to the argument `true`, the error should say that the
function *returned* a value of the wrong type. The research into the topic of correctly
assigning *blame* in gradually-typed programs has culminated in the *blame theorem*, which states
that "well-typed programs cannot be blamed", meaning that blame is always assigned to the
dynamically-typed portion of the program. A nice overview of this topic is provided in [5].

A related issue is that of efficiently translating type casts and reporting errors at the right
moment. The straightforward way of implementing function casts is to cast the argument and the
return value separately: if `f` has type `? -> ?`, then the cast `f : int -> bool` can be
compiled as `fun (x : int) -> (f(x) : bool)`. However, if we have two functions that call each
other recursively (e.g. the [basic example][mutual-recursion] of `is_odd` and `is_even`), one static and the
other dynamic, a naive implementation would just keep adding cast upon cast, which would result
in space-wise and time-wise inefficient execution. A related issue is how to implement casts
such as `((inc : int -> int) : ?) : bool -> bool` - should the type error be reported immediately,
or only when the function is first used? The first issue is touched upon in [5], while the second
is elaborated more deeply in [6] and also explained in a
[series of blog posts][blog-post].

Finally, [7] explains how to implement safe casts from dynamic functions to parametrically
polymorphic types (such as `forall[a] a -> a`) by using *dynamic sealing*. For example, if `f`
has type `? -> ?`, we can implement the cast `f : forall[a] a -> a` by translating it into
`fun x -> unwrap@1 (f (wrap@1 x))`, where the wrapped value `(wrap@1 x)` cannot be inspected in
any way (e.g. using typecase) and can only be unwrapped by the corresponding `unwrap@1`. This way,
we can be sure that the argument `x` is really used parametrically and we can recover the proof
that the only values of type `forall[a] a -> a` are the identity function and functions that either diverge or
raise an error. However, it remains unclear if this idea can be extended to polymorphic
container types, i.e. how to safely implement casts such as `f : forall[a] a -> list[a]`.



References
----------

[1] S Thatte. *Quasi-static typing.* 1989

[2] T Lindahl, K Sagonas. *[Practical Type Inference Based on Success Typings](http://www.it.uu.se/research/group/hipe/papers/succ_types.pdf).* 2006

[3] A Rastogi, A Chaudhuri, B Hosmer. *[The Ins and Outs of Gradual Type Inference](http://www.cs.umd.edu/~avik/papers/iogti.pdf)*. 2012

[4] T Wrigstad, F Z Nardelli, S Lebresne, J Ostlund, J Vitek. *[Integrating Typed and Untyped Code in a Scripting Language](https://www.cs.purdue.edu/homes/jv/pubs/popl10.pdf)*. 2009

[5] J G Siek, P Thiemann, P Wadler. *[Blame, coercions, and threesomes, precisely](http://homepages.inf.ed.ac.uk/wadler/papers/coercions/coercions.pdf)*. 2009

[6] J G Siek, R Garcia. *[Interpretations of the Gradually-Typed Lambda Calculus](http://wphomes.soic.indiana.edu/jsiek/files/2013/06/igtlc.pdf)*. 2012

[7] A Ahmed, R B Findler, J G Siek, P Wadler. *[Blame for All](http://ecee.colorado.edu/~siek/blame-forall-2011.pdf)*. 2011



[gradual]: http://ecee.colorado.edu/~siek/pubs/pubs/2006/siek06:_gradual.pdf
[inference]: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.84.8219&rep=rep1&type=pdf
[git-diff]: https://github.com/tomprimozic/type-systems/compare/7320bae...1ae7906#diff-4
[objects]: http://www.cs.colorado.edu/~siek/gradual-obj.pdf
[mutual-recursion]: http://en.wikipedia.org/wiki/Mutual_recursion#Basic_examples
[blog-post]: http://siek.blogspot.co.uk/2012/09/interpretations-of-gradually-typed.html
