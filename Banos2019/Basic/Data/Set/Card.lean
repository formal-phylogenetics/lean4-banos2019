module

public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Cardinalities of sets

* `Finset.sum_ncard_le_of_pairwiseDisjoint`: the cardinalities of pairwise disjoint subsets of a
  finite type, indexed by a finset, add up to at most the cardinality of the type.
* `Set.ncard_setOf_subtype_ne_add`, `Set.ncard_setOf_subtype_of_imp`: the elements of a subtype
  satisfying a predicate, counted in the type.
* `Set.exists_mem_and_exists_notMem_of_ncard_eq_two`,
  `Set.exists_not_and_forall_ne_of_ncard_eq_three`: subsets of two and three elements of a type
  with four.
* `Set.ncard_setOf_eq_card_filter`: the size of a set of elements of `Fin n` as a finset.
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

namespace Set

variable {α : Type*}

/-- The elements of the subtype `{a // a ≠ h}` satisfying `p`, and `h` if it satisfies `p`, are the
elements satisfying `p`. -/
theorem ncard_setOf_subtype_ne_add [Finite α] (h : α) (p : α → Prop) [DecidablePred p] :
    {a : {a // a ≠ h} | p a.1}.ncard + (if p h then 1 else 0) = {a | p a}.ncard := by
  have himg : Subtype.val '' {a : {a // a ≠ h} | p a.1} = {a | p a} \ {h} := by
    ext e
    constructor
    · rintro ⟨e', he', rfl⟩
      exact ⟨he', e'.2⟩
    · rintro ⟨he, hne⟩
      exact ⟨⟨e, hne⟩, he, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
  split_ifs with hp
  · exact Set.ncard_sdiff_singleton_add_one hp (Set.toFinite _)
  · rw [Set.sdiff_singleton_eq_self hp, add_zero]

/-- The number of elements of a subtype satisfying `q`, when `q` implies the predicate of the
subtype. -/
theorem ncard_setOf_subtype_of_imp {p q : α → Prop} (h : ∀ a, q a → p a) :
    {a : {a // p a} | q a.1}.ncard = {a | q a}.ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext e
  exact ⟨fun ⟨e', he', hee'⟩ => hee' ▸ he', fun he => ⟨⟨e, h e he⟩, he, rfl⟩⟩

/-- A set of two elements of a type with four has an element and misses one. -/
theorem exists_mem_and_exists_notMem_of_ncard_eq_two [Fintype α] (hα : Fintype.card α = 4)
    {A : Set α} (hA : A.ncard = 2) : (∃ x, x ∈ A) ∧ ∃ x, x ∉ A := by
  refine ⟨Set.nonempty_of_ncard_ne_zero (by omega), ?_⟩
  by_contra h
  push Not at h
  have : A = Set.univ := Set.eq_univ_of_forall h
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, hα] at hA
  omega

/-- When three of four elements satisfy `P`, the fourth does not. -/
theorem exists_not_and_forall_ne_of_ncard_eq_three [Fintype α] (hα : Fintype.card α = 4)
    {P : α → Prop} (h : {x | P x}.ncard = 3) : ∃ d, ¬ P d ∧ ∀ x, x ≠ d → P x := by
  have hc : ({x | P x}ᶜ).ncard = 1 := by
    rw [Set.ncard_compl, Nat.card_eq_fintype_card, hα, h]
  obtain ⟨d, hd⟩ := Set.ncard_eq_one.1 hc
  refine ⟨d, ?_, fun x hx => ?_⟩
  · have : d ∈ ({x | P x}ᶜ) := hd ▸ Set.mem_singleton d
    exact this
  · by_contra hPx
    have : x ∈ ({x | P x}ᶜ) := hPx
    rw [hd] at this
    exact hx this

theorem ncard_setOf_eq_card_filter {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    {a | p a}.ncard = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

end Set
