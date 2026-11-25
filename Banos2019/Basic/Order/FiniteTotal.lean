module

public import Mathlib.Order.Preorder.Finite

/-!
# Greatest and least elements of a finite set on which the order is total
-/

@[expose] public section

namespace Set.Finite

variable {α : Type*} [PartialOrder α] {T : Set α}

/-- A nonempty finite set of a partial order on which the order is total has a greatest element. -/
theorem exists_greatest_of_total (hT : T.Finite) (hne : T.Nonempty)
    (htot : ∀ s ∈ T, ∀ t ∈ T, s ≤ t ∨ t ≤ s) : ∃ g ∈ T, ∀ s ∈ T, s ≤ g := by
  obtain ⟨g, hg⟩ := hT.exists_maximal hne
  refine ⟨g, hg.1, fun s hs => ?_⟩
  rcases htot s hs g hg.1 with h | h
  · exact h
  · exact hg.2 hs h

/-- A nonempty finite set of a partial order on which the order is total has a least element. -/
theorem exists_least_of_total (hT : T.Finite) (hne : T.Nonempty)
    (htot : ∀ s ∈ T, ∀ t ∈ T, s ≤ t ∨ t ≤ s) : ∃ g ∈ T, ∀ s ∈ T, g ≤ s := by
  obtain ⟨g, hg⟩ := hT.exists_minimal hne
  refine ⟨g, hg.1, fun s hs => ?_⟩
  rcases htot s hs g hg.1 with h | h
  · exact hg.2 hs h
  · exact h

end Set.Finite
