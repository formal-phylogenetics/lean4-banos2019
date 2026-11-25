# General mathematics

Lemmas that say nothing about phylogenetics, filed by field as Mathlib files them
(`Combinatorics/`, `Probability/`, … in `Banos2019/Basic/`) and named as Mathlib would name
them, so that they can be contributed to Mathlib. They import only Mathlib.

| File | Contents |
| --- | --- |
| `Algebra/BigOperators/Finprod.lean` | Finite sums over the elements of a subtype |
| `Data/Finset/Card.lean` | Sets of four elements |
| `Data/Finset/Image.lean` | Images of `univ` |
| `Data/Set/Card.lean` | Cardinalities of sets: disjoint families, subtypes, subsets of a type with four elements, classes of an equivalence relation |
| `Logic/EquivOfInjective.lean` | A type with an injective map is equivalent to the subtype of its image |
| `Logic/RelationAvoid.lean` | Paths of a relation that cannot avoid an element |
| `Logic/RelationSymm.lean` | The reflexive transitive closure of a symmetric relation is symmetric |
| `MeasureTheory/SumCoordsNull.lean` | Null sets pulled back along sums of coordinates |
| `Order/FiniteTotal.lean` | Greatest and least elements of a finite set on which the order is total |

Before adding one, search Mathlib and lean4-phylogenetics (`Phylogenetics/ForMathlib/`): a lemma
that a second repository of the collection needs moves up the tree, to the lowest hub above both
(lean4-phylogenetics, docs/CONVENTIONS.md, Section 4).
