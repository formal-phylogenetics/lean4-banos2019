# General mathematics

Lemmas that say nothing about phylogenetics, filed by field as Mathlib files them and named as
Mathlib would name them, in Mathlib's namespaces, so that they can be contributed to Mathlib. They
import only Mathlib.

| Module | Content | Where it could go |
| --- | --- | --- |
| [`Banos2019.Basic.Data.Set.Card`](Data/Set/Card.lean) | [`Finset.sum_ncard_le_of_pairwiseDisjoint`](Data/Set/Card.lean#L21): the cardinalities of pairwise disjoint subsets of a finite type add up to at most its cardinality (the blocks of a cycle, Lemma 5) | `Mathlib/Data/Set/Card.lean` |
| [`Banos2019.Basic.Logic.EquivOfInjective`](Logic/EquivOfInjective.lean) | [`Equiv.ofInjectiveSubtype`](Logic/EquivOfInjective.lean#L17): a type with an injective map is equivalent to the subtype of its image (isomorphisms onto the image of a network, Proposition 1) | `Mathlib/Logic/Equiv/Set.lean` |
| [`Banos2019.Basic.Logic.RelationAvoid`](Logic/RelationAvoid.lean) | [`Relation.ReflTransGen.through_of_not_avoiding`](Logic/RelationAvoid.lean#L24), [`Relation.ReflTransGen.ne_of_avoiding`](Logic/RelationAvoid.lean#L41): paths of a relation that cannot avoid an element pass through it (the correspondence of cycles in the proof of Lemma 12) | `Mathlib/Logic/Relation.lean` |
| [`Banos2019.Basic.Logic.RelationSymm`](Logic/RelationSymm.lean) | [`Relation.ReflTransGen.symm_of_symm`](Logic/RelationSymm.lean#L15): the reflexive transitive closure of a symmetric relation is symmetric (walks of undirected graphs) | `Mathlib/Logic/Relation.lean` |
| [`Banos2019.Basic.MeasureTheory.SumCoordsNull`](MeasureTheory/SumCoordsNull.lean) | [`MeasureTheory.prod_pi_volume_preimage_sum_coords_null`](MeasureTheory/SumCoordsNull.lean#L25): the preimage of a null set under an affine map onto `ℝ³` given by sums of coordinates is null (the map `ν` of Proposition 10) | `Mathlib/MeasureTheory/Measure/Haar/`, as a case of the pushforward of a Haar measure by a surjective linear map |
| [`Banos2019.Basic.Order.FiniteTotal`](Order/FiniteTotal.lean) | [`Set.Finite.exists_greatest_of_total`](Order/FiniteTotal.lean#L16), [`Set.Finite.exists_least_of_total`](Order/FiniteTotal.lean#L25): a finite nonempty set on which the order is total has a greatest and a least element (the common nodes of two paths, Lemma 17) | `Mathlib/Order/Preorder/Finite.lean` |

Before adding one, search Mathlib and lean4-phylogenetics (`Phylogenetics/ForMathlib/`): a lemma
that a second repository of the collection needs moves up the tree, to the lowest hub above both
(lean4-phylogenetics, `docs/CONVENTIONS.md`, Section 4).
