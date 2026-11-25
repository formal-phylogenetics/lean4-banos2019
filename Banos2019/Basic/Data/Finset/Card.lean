module

public import Mathlib.Data.Finset.Card

/-!
# Sets of four elements

* `Finset.card_four_of_ne`, `Finset.injOn_four`: four distinct elements make a set of four, on which
  a map with four distinct values is injective.
* `Finset.exists_ne_mem_of_card_four_subset_insert`: four elements of `insert a T` include two
  distinct elements of `T`.
-/

@[expose] public section

namespace Finset

variable {α β : Type*} [DecidableEq α]

/-- Four distinct elements make a set of four. -/
theorem card_four_of_ne {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : #({a, b, c, d} : Finset α) = 4 := by
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
    card_pair hcd]

/-- A map taking four elements to four distinct values is injective on them. -/
theorem injOn_four {f : α → β} {a b c d : α} (hab : f a ≠ f b) (hac : f a ≠ f c) (had : f a ≠ f d)
    (hbc : f b ≠ f c) (hbd : f b ≠ f d) (hcd : f c ≠ f d) :
    Set.InjOn f ↑({a, b, c, d} : Finset α) := by
  intro x hx y hy hxy
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first | rfl | exact absurd hxy ‹_› | exact absurd hxy.symm ‹_›

/-- Four elements of `insert a T` include two distinct elements of `T`. -/
theorem exists_ne_mem_of_card_four_subset_insert {s : Finset α}
    (hs : #s = 4) {a : α} {T : Set α} (h : (s : Set α) ⊆ insert a T) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x ∈ T ∧ y ∈ T := by
  have h1 : 1 < #(s.erase a) := by
    have := Finset.pred_card_le_card_erase (s := s) (a := a)
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h1
  obtain ⟨hxa, hx⟩ := Finset.mem_erase.1 hx
  obtain ⟨hya, hy⟩ := Finset.mem_erase.1 hy
  exact ⟨x, hx, y, hy, hxy, (Set.mem_insert_iff.1 (h (mem_coe.2 hx))).resolve_left hxa,
    (Set.mem_insert_iff.1 (h (mem_coe.2 hy))).resolve_left hya⟩

end Finset
