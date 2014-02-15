Extensible records with scoped labels
=====================================


This is an implementation of type inference for safe, polymorphic and extensible records.


Overview
--------

In his paper [Extensible records with scoped labels][1], Daan Leijen describes an innovative
type inference system for extensible records which allows duplicate labels in rows. This makes
it considerably simpler than most other record systems, which include predicates on record
types such as the "lacks" predicate *`(r\l)`*, specifying that the record type `r` must not
contain label `l`. This implementation closely follows Daan's presentation in his paper and
is a relatively small extension of the Hindley-Milner type inference algorithm implemented
in **algorithm_w** (the required changes can be seen in commit [5c183a7][2]).

Records consist of labeled fields with values `{a = one, b = false}` and can extend other
records `{x = false | r}`. The basic operations for records are *selection*, *extension*
and *restriction* and are typed as follows:

```
	(_.label) : forall[a r] {label : a | r} -> a
	{label = _ | _} : forall[a r] (a, {r}) -> {label : a | r}
	{_ - label} : forall[a r] {label : a | r} -> {r}
```



Details
-------

The types of expressions `expr` and types `ty` in `expr.ml` are extended with primitive
record operations and types. Records can either be empty `{}` or extensions of other
records `{x = false | r}`. Syntax sugar for `{x = false | {y = zero | {}}}` is
`{x = false, y = zero}`. The type of rows similarly consists of empty rows `<>` and row
extensions `<a : _ | ...>`. A record type is a wrapper for the type of row; other wrappers
could exist (Daan gives example of sum/variant types).

The core of the type inference is implemented in functions `unify` and `rewrite_row`. The function
`unify` unifies record types by unifying their enclosing rows, and unifies an empty row only
with itself. If a row extension `<a : t | r>` is unified with another row, the function
`rewrite_row` rewrites the second row by searching for the first field with label `a` and
unifies its type with `t`. All other types are handled as before.

The only other significant difference is in function `infer`, where the types of the new
expression terms are inferred by treating them as implicit calls to *selection*, *extension*
and *restriction* functions with types as above.


Discussion
----------

One potential problem with this implementation is that record literals and row types are
represented as a list of record/row extensions, whose order depends on programmer's code
and inner workings of the type inference algorithm. The unification procedure can rearrange
fields as necessary, but records and record types can not be easily compared or canonically
represented by strings. A better solution would be to gather all labels into a multi-map
and use a specific sorting order for labels when representing rows as strings.

While this type system is simple to implement and use (for example, it is a part of the language
[Elm][3]), it represents only one possibility for typing extensible records. Other
proposals, summarized on the [GHC wiki][4], include first-class labels, positive and negative
("lacks") predicates for record types and even more general predicates such as "disjoint", and
also include structural subtyping (as used for objects in OCaml and Go).



[1]: http://research.microsoft.com/apps/pubs/default.aspx?id=65409
[2]: https://github.com/tomprimozic/type-systems/commit/5c183a7866aa30f3350a4cab011e376d36dd385e
[3]: http://elm-lang.org/learn/Records.elm
[4]: https://ghc.haskell.org/trac/ghc/wiki/ExtensibleRecords
