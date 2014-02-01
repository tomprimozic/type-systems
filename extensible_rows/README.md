Extensible records with scoped labels
=====================================


This is an implementation of type inference for safe, polymorphic and extensible records.


Overview
--------

This is an implementation of an innovative type system for extensible records described by
Daan Leijen in his paper [Extensible records with scoped labels][1]. The implementation
closely follows Daan's presentation in his paper and is a relatively small extension of
the Hindley-Milner type inference algorithm implemented in **algorithm_w** (the required
changes can be seen in commit 5c183a7866aa30f3350a4cab011e376d36dd385e). This record type
system is simpler than most other systems in that it avoids predicated types (e.g. that
record type `r` must not contain label `l`), which it achieves by allowing duplicate labels.

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

The types of expressions `expr` and types `ty` are extended with primitive record operations
and types. Records can either be empty `{}` or extensions of other records `{x = false | r}`.
Syntax sugar for `{x = false | {y = zero | {}}}` is `{x = false, y = zero}`. The type of rows
similarly features empty rows `<>` and row extensions `<a : _ | ...>`. A record type is a
wrapper for the type of row; other wrappers could exist (Daan gives example of sum/variant
types).

The core of the type system is implemented in methods `infer` and `rewrite_row`. The function
`infer` unifies record types by unifying their enclosing rows, and unifies an empty row only
with itself. If a row extension `<a : t | r>` is unified with another row, the function
`rewrite_row` rewrites the second row by searching for the first field with label `a` and
unifies its type with `t`. The only other significant difference is in function `infer`, where
the types of the new expression terms are inferred by treating them as implicit calls to
functions *selection*, *extension* and *restriction* with types as above..


Possible extensions
-------------------

One problem with this implementation is that record literals and row types are represented as
a sequence of record/row extensions. The unification algorithm can rearrange the fields as
necessary, but the records and types are still converted to strings using an arbitrary
ordering of labels, dependant on programmer's input. A better solution would be to gather
all labels into a multi-map and convert records and rows to string by listing the labels in
a sorted order.

While this type system is simple to implement and use (for example, it is a part of the language
[Elm][2]), it represents only one possibility for typing extensible records. Other
proposals, summarized on [GHC wiki][3], include first-class labels, positive and negative
("lacks") predicates for records and even more general predicates such as "disjoint", and
also include structural subtyping of records (as used for objects in OCaml and Go).

References
----------

[1]: Didier Rémy. Extending ML type system with a sorted equational theory. 1992


[1]: http://research.microsoft.com/apps/pubs/default.aspx?id=65409
[2]: http://elm-lang.org/learn/Records.elm
[3]: https://ghc.haskell.org/trac/ghc/wiki/ExtensibleRecords
