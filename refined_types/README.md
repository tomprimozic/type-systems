Refined types: a better type system for more secure software
============================================================

This is another type systems experiment that combines Hindley–Milner type inference with static type-checking of
a limited version of dependent types called *refined types*. Although the type-checker only allows
refined types on function parameters and return types (i.e. *function contracts*), it can prove the
absence of some of the most common software bugs.

For a simple example, let's consider integer division: we know that the denominator cannot be zero.
Thus, if we define division as `/ : (int, i : int if i != 0) → int`, the refined type-checker can
tell us *during compilation* that `1/0` will result in an error, as would `1/(2 * 3 - 6)` and
`1/(4 % 2)`. The system can also deduce that the program `10 / (random1toN(10) - 5)` is potentially
unsafe, where `random1toN` is a non-deterministic function whose type is
`(N : int if N ≥ 1) → (i : int if 1 ≤ i and i ≤ N)`.

Refined type checking can also be used to verify that arrays are not accessed out of bounds, and
using appropriate contracts on functions `alloc` and `memcpy`, software bugs such as
[Heartbleed][heartbleed] could be prevented.

```typescript
alloc : (i : int) -> (a : array[byte] if length(a) == i)
memcpy : (dst : array[byte], src : array[byte],
          num : int if num <= length(dst) and num <= length(src)) -> unit

function heartbleed_bug(payload : array[byte], payload_length : int) {
  let response = alloc(payload_length)
  memcpy(response, payload, payload_length)    // ERROR!
  return response
}

function heartbleed_fix(payload : array[byte],
                        payload_length : int if length(payload) == payload_length) {
  let response = alloc(payload_length)
  memcpy(response, payload, payload_length)
  return response
}
```

The implementation of a refined type-checker is actually very straightforward and turned out to be
much simpler than I expected. Essentially, program expressions and contracts on function parameters
and return types are converted into a series of mathematical formulas and logical statements, the
validity of which is then assessed using an external automated theorem prover [Z3][z3]. The details
of the implementation, including the tricks that allow functions to be handled as first-class
values, are explained below.


> *Note about syntax:* These examples use a syntax similar to JavaScript or TypeScript that
> should be familiar to most programmers, which is different from the [ML][ml-language]-like syntax that the
> type-checker and its test cases use.


Overview
--------

*Dependent types*, i.e. types that depend on values, are often presented as the holy grail of secure
static type systems, yet despite intensive research they remain complex and impractical and are only
used in research languages and mathematical proof assistants. *Refined types* or *contracts* are a
restricted form of dependent types that combine base datatypes with logical predicates; for example,
the type of natural numbers could be written `x : int if x ≥ 0` (the notation most commonly used in
academic literature is `{ν : int | ν ≥ 0}`).

Refined types have been a topic of a lot of research and experimentation in the past decade. *Hybrid
type checking* [1] combines static and dynamic type-checking by verifying the contracts statically
when possible and deferring the checks until runtime when necessary (implemented in programming
language [Sage][sage] [2]). Limited automatic inference of function contracts was developed which
can reduce the amount of type annotations necessary to prove software safety (e.g. Liquid Types [3]
and [4]). Refined types have also been used in some experimental programming languages and verifying
compilers, such as the [VCC][vcc], a verifier for concurrent C, [F7][f7], which implements refined
types for F# (since superseded by [F*][f-star]), and the [Whiley][whiley] programming language.

This experiment, inspired primarily by Sage and Liquid Types, is an implementation of refined
type-checking for a simple functional language. Refined types are only allowed on function
parameters and return types; nevertheless, a variety of static program properties can be verified.  The type-checker first strips all refined type annotations and uses Hindley–Milner type inference to
infer base types of functions and variables. Then it translates the program into [SMT-LIB][smtlib],
a language understood by automated theorem provers called *SMT solvers*. SMT solvers understand how
integers and booleans work, so simple expressions such as `1 + a` can be translated directly.
Translation of functions is more complicated, as SMT solvers use first-order logic and cannot handle
functions as first-class values, so the contracts on their parameters and return types are
translated instead. The resulting SMT-LIB formulas are run through a SMT solver (this implementation
uses [Z3][z3]) to verify that none of the translated contracts are broken.

This design allows the refined type-checker to handle a variety of programming constructs, such as
multiple variable definitions, nested function calls, and if statements. It can also track abstract
properties such as array length or integer ranges, and handle function subtyping. The following
examples demonstrate these features:

```typescript
function cannot_get_first(arr : array[int]) {
  return get(arr, 0)    // ERROR!
}

function maybe_get_first(arr : array[int]) {
  if not is_empty(arr) {
    return get(arr, 0)
  } else {
    return -1
  }
}

function get_2dimensional(n : int if n >= 0, m : int if m >= 0,
                          i : int if 0 <= i and i < m, j : int if 0 <= j and j < n,
                          arr : array[int] if length(arr) == m * n) {
  return get(arr, i * n + j)
}

function max_typo(x, y) : (z : int if z >= x and z >= y) {
  if x <= y {     // Oops, should be `x >= y`!
    return x      // ERROR: `z` can be less than `y`
  } else {
    return y
  }
}

function test(x : int if abs(x) <= 10) {
  let z =
    if max(square(x), 25) == 25 {
      3 * x + 7 * random1toN(10)
    } else if x == 11 {     // cannot happen
      0
    } else {
      x
    }
  return 100 / z
}

/* function subtyping */
min : (i : int if i > 0, j : int if j < 0) -> (k : int if k < 0)
make_const(1) : int -> (a : int if a == 1)
```

The `get_2dimensional` function is particularly interesting; it uses
[non-linear integer arithmetic][robinson-arithmetic], which is incomplete and undecidable. Although
Z3 can prove simple non-linear statements about integers, such as `x² ≥ 0`, it cannot prove that the
array is accessed within bound in the function `get_2dimensional`. Instead, it has to convert the
formula to real arithmetic and use the NLSat solver [5]. Even though non-linear real arithmetic is
complete and decidable, this approach only works for certain kinds of problems; for example, it
cannot disprove equalities that have real solutions but no integer ones, such as `x³ + y³ == z³`
where `x`, `y` and `z` are positive.


Implementation
--------------

### Type inference

After lexing and parsing, a slightly modified [**algorithm-w**][algorithm-w] is used to perform
standard Hindley-Milner unification-based type inference on the AST. The main difference is that
instead of merely inferring the type of the input expression, the algorithm also transforms the AST
into a typed expression tree that will be used later by the refined type-checker. The predicate
expressions in refined function types have their types inferred as well and unified with `bool`. To
prevent unification from unexpectedly propagating refined types, predicates are stripped from
function types before calling `unify` and before adding the types to the typing context.

For example, the function cast

```typescript
f : (x : int if x + 1 >= 0) -> int
```

is translated by the type inference algorithm roughly into the following representation, where
`{e; τ}` denotes a typed tree node with expression `e` and type `τ`:

```typescript
{
	{f; int -> int} : (x : int if {{{x; int} + {1; int}; int} >= {0; int}; bool}) -> int;
	int -> int
}
```

### Refined type-checking

The goal of refined type-checking is *proving* that none of the function contracts can be broken at
runtime. To do this, expressions of the source program must be translated into SMT-LIB formulas, so
they can be reasoned about in proofs by the SMT solver. Some expressions, such as integer constants
and applications of built-in operators (e.g. `+`, `%`, `>=`, `==` and `or`), have precise values or
interpretations in SMT theories and can be translated literally. Others, such as function parameters
and the return value of a `random1toN(10)` call, don't have specific values and we can only make
certain more-or-less precise assertions about them.

We can use the SMT-LIB representation of an expression to check if a contract is satisfied. For
a simple example, let's examine the SMT-LIB script generated during refined type-checking of the
function `test`:

```typescript
function test(x : int if x > 3) : (z : int if z > 0) {
	return x - 2
}
```

We first declare a new SMT-LIB variable for the parameter `x`. Its value is unknown and the most we
can say about it is that `x > 3`.

```lisp
(declare-const x Int)                   ; declare `x : int`
(assert (>= (- x 1) 3))                 ; equivalent to `x > 3`
(push)                                  ; enter new stack frame
(assert (not (>= (- (- x 2) 1) 0)))     ; equivalent to `not (z > 0)` where `z == x - 2`
(check-sat)                             ; check satisfiability
(pop)                                   ; exit last stack frame
```

To prove that a contract is satisfied, we need to prove the *validity* of the logical implication
where all previous formulas and assertions are premises and the contract is the conclusion. In the
above example, the required implication is `x > 3 ⇒ x - 2 > 0`. However, SMT solvers can only prove
that a formula is *satisfiable* (there exists an assignment of values to the variables that makes
the formula true), not that it is *valid* (it is true for every assignment of values). Fortunately,
we can determine if the implication is valid by negating the condition of the contract and checking
whether the negation of the implication is satisfiable. If the SMT solver produces a model showing
that it is, indeed, satisfiable, we have a counterexample of values that break the contract. If the
SMT solver proves that the negated implication is not satisfiable, we conclude that the implication
itself is valid, and that the contract cannot be broken. If the solver can neither show that the
negated implication is satisfiable nor prove that it is not, its satisfiability is checked again in
the theory of non-linear real arithmetic by the NLSat solver. (Z3 incorrectly translates strict
inequalities when translating between the theories of integer and real arithmetic, which is why
`>=` and `<=` are used instead of `>` and `<`.) 

Some expressions, such as integers, booleans and variables that do not have function types, can be
trivially translated into SMT-LIB representation, but the translation of other kinds of expressions
can be tricky. When translating an `if` expression, the boolean condition has to be added to the
premises when checking contracts in the `then` branch, while its negation has to be added to the
premises when checking the `else` branch. Another non-trivial case is checking function calls,
where each argument expression is translated and the contract on the corresponding parameter must be
checked. As contracts on function parameters can refer to earlier parameters, the representations of
argument expressions corresponding to named parameters are added to the function's *local
environment*. In the example above, the local environment when checking the refined return type is
`{z ↦ "(- x 2)"}`, so that the variable `z` in the contract expression is translated correctly.

The results of some function calls are represented directly, specifically the results of calls of
built-in operators, which have standard interpretations in SMT theories, and *uninterpreted
functions* such as `length`, which are used to represent abstract properties and whose values can be
tracked and reasoned about by SMT solvers. The results of other function calls are represented by
fresh SMT variables, which are constrained by the contract on the functions return type. For
example, the result of the function application `x + 6` is represented by `"(+ x 6)"`, while the
result of the call `random1toN(10)` is translated as

```lisp
(declare-const _i0 Int)
(assert (and (<= 1 _i0) (<= _i0 10)))
```

In contrast to other values, functions are not translated into SMT-LIB representation, but are
instead stored in a *function environment*. If a function is the result of an application of a
higher-order function, its local environment is stored along with its refined type.
Take, for example, the function `make_const : (x : int) → int → (z : int if z == x)`. The result
of the call `make_const(1 + 2)` is the pair `({x ↦ "(+ 1 2)"}, int → (z : int if z == x))`. That
way, when the resulting function is called, its return type contract can be translated correctly.

Function casts must establish a subtype relationship between two refined function types, e.g. that
`a₁ → b₁ <: a₂ → b₂`. Assuming that the base types of `a₁` and `a₂` and of `b₁` and `b₂` are equal,
we must prove that the contract of `a₂` implies the contract of `a₁` (as parameter types are
contravariant), and that the contract of `a₂` and the contract of `b₁` imply the contract of `b₂`
(since return types are covariant).  If there are multiple parameters, the contracts of all earlier
parameters of the supertype must be used as premises when checking the implication of contracts for
each parameter and for the return type. For example, to prove that the type
`(x : int, y : int if y > 0) → (z : int if z == x + y)` is a subtype of
`(x : int if x > 0, y : int if y > x) → (z : int if z > 0)`, we must prove 1)
`x > 0 ⇒ true`, 2) `x > 0 ∧ y > x ⇒ y > 0`, and 3) `x > 0 ∧ y > x ∧ z == x + y ⇒ z > 0`.



Possible extensions
-------------------

This experimental implementation demonstrates a refined type-checking algorithm that can check
many software safety properties. However, it is far from complete, and could be improved in many
different ways.

A simple addition would be implementing HM type inference and refined type checking for recursive
functions, which are equivalent to loops and would make the language Turing complete. Another idea
is to allow type aliases for refined types (e.g. `type nat = i : int if i ≥ 0`), and to perform a
simple form of dead code elimination by proving when `if` branches cannot be taken. Furthermore, we
could use the model generated by the SMT solver the negated implication is
satisfiable to extract a set of values that break the contract.

Handling of first-class functions needs to be improved. We would need to include functions in local
environment as well, and then use the function subtype-checking algorithm to check refined function
types of parameters and return types. We would need to transform some second-order contracts into equivalent refined function types, for example `f : int → int if f(0) == 1` is equivalent to
`f : (x : int) → (y : int if (if x == 0 then y == 1 else true))`, while
`f : array[int] → int if f == length` is equivalent to
`f : (a : array[int]) → (i : int if i == length(a))`. Finally, it would be useful to alert the user
when there can be no functions inhabiting a given function type, such as
`(x : int if x > 0) → (y : int if y > x and y < 0)`.

More substantial extensions would be adding a function effect system, which would prohibit the use
of functions with side-effects (such as non-determinism or I/O) in refined types, and including
built-in operations for additional datatypes, such as arrays, modular integers and bitvectors, which
can also be reasoned about by some SMT solvers. To make the language practical, it would also need
to support imperative features such as loops and mutable local variables and data structures.

A very useful extension would be to allow refined types within algebraic datatypes, for example
`array[i : int if i ≥ 0]`. This would require the ability to instantiate polymorphic types with
refined base types, so that we could use `get : forall[a] (array[a], i : int) → a` to extract a
non-negative value from this array. A related idea is *predicate polymorphism* [6]: we want to
support types such as
`array_max : forall[p : int → bool] array[i : int if p(i)] → (k : int if p(k))`.

Ideally, refined type-checking could be used without having the programmer explicitly annotate all
parameters and return types. However, refined type inference is complicated, as it is hard to say
what is the "best" refined type for a given expression. For example, the exact refined type of
`square(random1toN(5))` is the existential type `exists[i : int if 1 ≤ i ≤ 5] i * i`, but in many
situations `i : int if 1 ≤ i ≤ 25` is precise enough while being much clearer. The Liquid Types [3]
type inference system attempts to solve this by inferring refined types made only of
programmer-specified qualifiers, such as `0 ≤ _` and `_ < length(_)`. The system presented in [4]
instead uses *weakest precondition generation* to propagate the conditions of a contract that might
be broken backwards to the function parameters.




References
----------

[1] K Knowles, C Flanagan. *[Hybrid Type Checking](http://www.kennknowles.com/research/knowles-flanagan.toplas.2010.pdf)*. 2006/2010

[2] K Knowles, A Tomb, J Gronski, S N Freund, C Flanagan. *[Sage: Uniﬁed Hybrid Checking for First-Class Types, General Reﬁnement Types, and Dynamic](http://sage.soe.ucsc.edu/sage-tr.pdf)*. 2006

[3] P M Rondon, M Kawaguchi, R Jhala. *[Liquid Types](http://goto.ucsd.edu/~rjhala/papers/liquid_types.pdf)*. 2008

[4] H Zhu, S Jagannathan. *[Compositional and Lightweight Dependent Type Inference for ML](https://www.cs.purdue.edu/homes/suresh/papers/vmcai13.pdf)*. 2013

[5] D Jovanović, L de Moura. *[Solving Non-Linear Arithmetic](http://research.microsoft.com/en-us/um/people/leonardo/files/IJCAR2012.pdf)*. 2012

[6] N Vazou, P M Rondon, R Jhala. *[Abstract Reﬁnement Types](http://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf)*. 2013


[heartbleed]: http://en.wikipedia.org/wiki/Heartbleed "Heartbleed"
[z3]: http://z3.codeplex.com/ "Z3, a high-performance theorem prover"
[ml-language]: http://en.wikipedia.org/wiki/ML_(programming_language) "ML programming language"
[f7]: http://research.microsoft.com/en-us/projects/f7/ "F7: Refinement Types for F#"
[f-star]: http://research.microsoft.com/en-us/projects/fstar/ "F*"
[vcc]: http://research.microsoft.com/en-us/projects/vcc/ "VCC: A Verifier for Concurrent C"
[whiley]: http://whiley.org/about/overview/ "Whiley - A Programming Language with Extended Static Checking"
[sage]: http://sage.soe.ucsc.edu/ "Sage: A Programming Language with Hybrid Type-Checking"
[smtlib]: http://www.smtlib.org/ "The Satisfiability Modulo Theories Library"
[robinson-arithmetic]: http://en.wikipedia.org/wiki/Robinson_arithmetic "Robinson arithmetic"
[algorithm-w]: https://github.com/tomprimozic/type-systems/tree/master/algorithm_w
