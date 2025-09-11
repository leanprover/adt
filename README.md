# ADT
Abstract Datatypes for Lean 4

This library defines uniform APIs for data structures that have common operations:
* Dependently typed maps: `DHashMap`, `DTreeMap`, `ExtDHashMap`, `ExtDTreeMap`
* Maps: `HashMap`, `TreeMap`, `ExtHashMap`, `ExtTreeMap`
* Sets: `HashSet`, `TreeSet`, `ExtHashSet`, `ExtTreeSet`

To increase modularity, this library also have low-level typeclasses for basic operations on data structures
* The `Size` class: `Size.size`
* The `Foldl`, `FoldlM`, `Foldr`, and `FoldrM` classes: `Foldl.foldl`, `FoldlM.foldlM`, `Foldr.foldr`, `FoldrM.foldrM`
* The `ToList` class: `ToList.toList`
* The `DGetElem` and `DGetElem?` classes: `dGetElem, dGetElem?` and `dGetElem!`. We also defined notations for these operations
  * `dGetElem`: `x[m]ᵈ`
  * `dGetElem?`: `x[m]ᵈ?`
  * `dGetElem!`: `x[m]ᵈ!`

The `IndexMap` file is an example use case of the `MapLike` class. We also included a utility that automatically generates equational theorems for functions that return structure instances. This utility is used by `IndexMap`.