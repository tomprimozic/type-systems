First-class polymorphism
========================


This in an extension of ordinary Damas-Hindley-Milner type inference that supports first-class
(impredicative) and higher-rank polymorphism in a very simple and intuitive manner, requiring
only minimal type annotations.


Overview
--------

Although classical Damas-Hindley-Milner type inference supports polymorphic types, these types
are quite limited: function parameters cannot have polymorphic type and type variables
cannot be instantiated with polymorphic types. On the other hand we have [System F][system_f],
which supports all of the above, but for which type inference is undecidable. In 2003, Didier
Le Botlan and Didier Rémy presented [MLF][mlf], a system capable of inferring polymorphic
types with minimal type annotations (only function parameters used polymorphically need to be
annotated), which however uses complicated, rigidly or flexibly bounded types and even more
complicated type inference algorithm.

This implementation is based on the work of Daan Leijen, published in his paper
[HMF: Simple Type Inference for First-Class Polymorphism][hmf]. In contrast to MLF, it only
uses very intuitive System F types and has a considerably simpler type inference algorithm,
yet it requires more type annotations, since it always infers the least polymorphic type.
In addition to the basic algorithm, the implementation includes some extensions proposed by
Daan in his paper, including rigid annotations and support for n-ary function calls, that
can significantly increase HMF's expressive power and improve its practical usability.

Features supported by HMF:

  - *polymorphic type parameters*

    Parameters used polymorphically require type annotations even in MLF; indeed, without
    the type annotation this would more likely be programmer error.

    ```
    let poly = fun (f : forall[a] a -> a) -> pair(f(one), f(true)) in
    poly : (forall[a] a -> a) -> pair[int, bool]
    ```

    Parameters *not* used polymorphically, but only passed on to other functions as
    polymorphic arguments, need to be annotated in HMF but not in MLF.

    ```
    let f = fun (x : forall[a] a -> a) -> poly(x) in
    f : (forall[a] a -> a) -> pair[int, bool]
    ```

  - *impredicative polymorphism*

    Type variables such as `a` and `b` in `(a -> b, a) -> b` can be instantiated to
    polymorphic type. During type checking of the example below, the type variable `a` is
    instantiated to a polymorphic type `forall[c] c -> c`, and the correct type is inferred.

    ```
    let apply = fun f x -> f(x) in
    apply : forall[a b] (a -> b, a) -> b

    apply(poly, id) : pair[int, bool]
    ```

  - *rigid type annotations*

    In absence of type annotations, HMF will always infer the least polymorphic type.

    ```
    let single = fun x -> cons(x, nil) in
    single : forall[a] a -> list[a]

    let ids = single(id) in
    ids : forall[a] list[a -> a]
    ```

    The programmer can specify a more polymorphic type for `ids` using type annotations.

    ```
    let ids = single(id : forall[a] a -> a) in
    ids : list[forall[a] a -> a]
    ```


Details
-------

Types and expressions of HMF are simple extensions of what we had in `algorithm_w`. We added the `TForall` constructor, which enables us to construct polymorphic types, and now have 3 types of type variables: `Unbound` type variables can be unified with any other type, `Bound` represents those variables bound by `forall` quantifiers or type annotations, and `Generic` type variables help us typecheck polymorphic parameters and can only be unified with themselves. Expressions are extended with *type annotations* `expr : type`. Type annotations can bind additional unspecified type variables, and can also appear on function parameters:

```
let f_one = fun (f : some[a] a -> a) -> f(one) in
f_one : (int -> int) -> int

let f_one2 = fun f -> f(one) in
f_one2 : forall[a] (int -> a) -> a
```

An important part of the type inference is the `replace_ty_constants_with_vars` function in `parser.mly`, which turns type constants `a` and `b` into `Bound` type variables if they are bound by `forall[a]` or `some[b]`. This function also *normalizes* the type, ordering the bound variables in order in which they appear in the structure of the type, and removing unused ones. This turns different versions of the same type `forall[b a] a -> b` and `forall[c a b] a -> b` into a canonical representation `forall[a b] a -> b`, allowing the type inference engine to efficiently unify polymorphic types.

Function `substitute_bound_vars` in `infer.ml` takes a list of `Bound` variable ids, a list of replacement types and a type and returns a new type with `Bound` variables substituted with respective replacement types. Function `escape_check` takes a list of `Generic` type variables and types `ty1` and `ty2` and checks if any of the `Generic` type variables appears in any of the sets of free generic variables of `ty1` or `ty2`, which are determined using the function `free_generic_vars`.

The main difference in function `unify` is the unification of polymorphic types. First, we create a fresh `Generic` type variable for every type variable bound by the two polymorphic types. Here, we rely on the fact that both types are normalized, so equivalent generic type variables should appear in the same locations in both types. Then, we substitute all `Bound` type variables in both types with `Generic` type variables, and try to unify them. If unification succeeds, we check that none of the `Generic` type variables "escapes", otherwise we would successfully unify types `forall[a] a -> a` and `forall[a] a -> b`, where `b` is a unifiable `Unbound` type variable.

Function `instantiate` instantiates a `forall` type by substituting bound type variables by fresh `Unbound` type variables, which can then by unified with any other type. Function `instantiate_ty_ann` does the same for type annotations. The function `generalize` transforms a type into a `forall` type by substituting all `Unbound` type variables with levels higher than the input level with `Bound` type variables. It traverses the structure of the types in a depth-first, left-to-right order, same as the function `replace_ty_constants_with_vars`, making sure that the resulting type is in normal form.

The function `subsume` takes two types `ty1` and `ty2` and determines if `ty1` is an *instance* of `ty2`. For example, `int -> int` is an instance of `forall[a] a -> a` (the type of `id`), which in turn is an instance of `forall[a b] a -> b` (the type of `magic`). This means that we can pass `id` as an argument to a function expecting `int -> int` and we can pass `magic` to a function expecting `forall[a] a -> a`, but not the other way round. To determine if `ty1` is an instance of `ty2`, `subsume` first instantiates `ty2`, the more general type, with `Unbound` type variables. If `ty1` is not polymorphic, is simply unifies the two types. Otherwise, it instantiates `ty1` with `Generic` type variables and unifies both instantiated types. If unification succeeds, we check that no generic variable escapes, same as in `unify`.

Type inference in function `infer` changed significantly. We no longer instantiate the polymorphic types of variables and generalize types at let bindings, but instantiate at function calls and generalize at function calls and definitions instead. To infer the types of functions, we first extend the environment with the types of the parameters, which might be annotated. While we do this, we remember all new type variables, so that we can later make sure that none of them was unified with a polymorphic type. We then infer the type of the function body using the extended environment, and instantiate it unless it's annotated. Finally, we generalize the resulting function type.

To infer the type of function application we first infer the type of the function being called, instantiate it and separate parameter types from function return type. The core of the algorithm is infering argument types in the function `infer_args`. After infering the type of the argument, we use the function `subsume` (or `unify` if the argument is annotated) to determine if the parameter type is an instance of the type of the argument. When calling functions with multiple arguments, we must first subsume the types of arguments for those parameters that are *not* type variables, otherwise we would fail to typecheck applications such as `rev_apply(id, poly)`, where `rev_apply : forall[a b] (a, a -> b) -> b`, `poly : (forall[a] a -> a) -> pair[int, bool]` and `id : forall[a] a -> a`. Infering type annotation `expr : type` is equivalent to inferring the type of a function call `(fun (x : type) -> x)(expr)`, but optimized in this implementation of `infer`.


Extensions
----------

Daan Leijen also published a reference implementation of HMF, written in Haskell. In addition to the type inference algorithm describe in his paper, he implemented an interesting extension to the algorithm that significantly improves the usability of HMF for programmers. In **Overview** we saw that in order to create a list of polymorphic functions `ids : list[forall[a] a -> a]`, the programmer must add a type annotation `let ids = single(id : forall[a] a -> a)`, otherwise HMF infers the least polymorphic type. The type annotation must be provided on the *argument* to the function `single`, in order to prevent the argument type from being instantiated. However, it would be more desirable for the programmer to be able to specify the type of the *result* of function `single`, like so: `let ids = single(id) : list[forall[a] a -> a]`.

We can implement this in the type inference algorithm by adding information about *expected types* and *propagating* the information from function result type to function arguments and to parameter types of anonymous functions. To function `infer` we add two additional arguments `maybe_expected_ty`, for optionally specifying the resulting type, and `generalized`, which indicates whether the resulting type should be generalized or instantiated. To infer the type of function expression, we annotate the unannotated parameters with expected parameter types and use the expected return type to infer the type of the function body. To propagate the expected type through a function application, we first unify function return type with the expected return type. Then we infer the types of the arguments, taking care to first infer the annotated arguments and to infer arguments to parameters which are type variables last.

In addition to a more intuitive type annotation in cases such as `ids` above, this extension sometimes allows programmers to write anonymous functions with polymorphic arguments without annotations. The function `special : ((forall[a] a -> a) -> (forall[a] a -> a)) -> forall[a] a -> a` expects a function with a polymorphic parameter, which we can define without any annotations: `special(fun f -> f(f))`. We cannot propagate the result type through a function call if the return type of the function is a type variable. For example, given that `head : forall[a] list[a] -> a`, propagating the result type in `head(ids) : int -> int` would instantiate the parameter type to `list[int -> int]`, which is not an instance or a supertype of `list[forall[a] a -> a]` (since HMF is invariant).



[system_f]: http://en.wikipedia.org/wiki/System_F
[hmf]: http://research.microsoft.com/apps/pubs/default.aspx?id=132621
[mlf]: http://gallium.inria.fr/~remy/work/mlf/
