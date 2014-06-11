Extensible records with scoped labels - improved
================================================

This is an improved implementation of type inference for [extensible records][original].

Essentialy, instead of representing records and row types with a list of `RecordExtend`/`TRowExtend`
nodes, each of which contains a single label and an expression or a type, respectively, each node
contains many labels and a list of expressions/types for each of them. During type inference and when
a record is converted to a string, all labels are gathered together and sorted, making the records
easily comparable and canonically representable.

An overview of changes can be seen in this [diff][diff].

[original]: https://github.com/tomprimozic/type-systems/tree/master/extensible_rows
[diff]: https://github.com/tomprimozic/type-systems/compare/f199446...f39ce0b
