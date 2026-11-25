module

public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Cardinalities of pairwise disjoint families of sets

* `Finset.sum_ncard_le_of_pairwiseDisjoint`: the cardinalities of pairwise disjoint subsets of a
  finite type, indexed by a finset, add up to at most the cardinality of the type.
-/

@[expose] public section

namespace Finset

variable {ι α : Type*} [Finite α]

/-- The cardinalities of pairwise disjoint subsets of a finite type add up to at most its
cardinality. -/
theorem sum_ncard_le_of_pairwiseDisjoint (I : Finset ι) {s : ι → Set α}
    (h : (I : Set ι).PairwiseDisjoint s) : ∑ i ∈ I, (s i).ncard ≤ Nat.card α := by
  rw [← finsum_mem_coe_finset, ← Set.Finite.ncard_biUnion I.finite_toSet
    (fun _ _ => Set.toFinite _) h]
  exact Set.ncard_le_card _

end Finset
