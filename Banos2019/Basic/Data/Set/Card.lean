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
* `Set.ncard_nontrivialClasses_subtype_lt`: restricting an equivalence relation to a set that meets
  one of its classes with at least two elements in a single element leaves fewer such classes.
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

/-- **Classes of an equivalence relation on a subset**: when `Y` holds one element `x` of a class
with at least two elements and all the elements of the other classes, the classes of the relation on
`Y` with at least two elements are the other classes of `R` with at least two elements, so there are
fewer of them than there are of `R`. -/
theorem ncard_nontrivialClasses_subtype_lt [Finite α] (R : α → α → Prop)
    (hrefl : ∀ a, R a a) (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    {Y : Set α} {x : α} (hY : ∀ z, z ∈ Y ↔ z = x ∨ ¬ R x z) (hP : {y | R x y}.Nontrivial) :
    {B : Set Y | (∃ a : Y, B = {b : Y | R a b}) ∧ B.Nontrivial}.ncard <
      {B : Set α | (∃ a, B = {b | R a b}) ∧ B.Nontrivial}.ncard := by
  have hmaps : ∀ B ∈ {B : Set Y | (∃ a : Y, B = {b : Y | R a b}) ∧ B.Nontrivial},
      Subtype.val '' B ∈ {B : Set α | (∃ a, B = {b | R a b}) ∧ B.Nontrivial} \ {{y | R x y}} := by
    rintro B ⟨⟨a, rfl⟩, hB⟩
    -- `a` is not in the class of `x`, which meets `Y` in `x` only
    have hxa : ¬ R x a := by
      intro hxa
      obtain ⟨b₁, hb₁, b₂, hb₂, hne⟩ := hB
      have e : ∀ b : Y, R a b → (b : α) = x := fun b hb =>
        ((hY b).1 b.2).resolve_right (not_not.2 (htrans _ _ _ hxa hb))
      exact hne (Subtype.ext ((e b₁ hb₁).trans (e b₂ hb₂).symm))
    -- so the class of `a` lies in `Y`
    have himg : Subtype.val '' {b : Y | R a b} = {b | R a b} := by
      ext z
      refine ⟨?_, fun hz => ⟨⟨z, (hY z).2 (Or.inr fun hxz =>
        hxa (htrans _ _ _ hxz (hsymm _ _ hz)))⟩, hz, rfl⟩⟩
      rintro ⟨b, hb, rfl⟩
      exact hb
    refine ⟨⟨⟨a, himg⟩, hB.image Subtype.val_injective⟩, fun h => hxa ?_⟩
    have hx : x ∈ ({y | R a y} : Set α) := by
      rw [← himg, Set.mem_singleton_iff.1 h]
      exact hrefl x
    exact hsymm _ _ hx
  calc _ = (Set.image (Set.image Subtype.val)
        {B : Set Y | (∃ a : Y, B = {b : Y | R a b}) ∧ B.Nontrivial}).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective.image_injective).symm
    _ ≤ ({B : Set α | (∃ a, B = {b | R a b}) ∧ B.Nontrivial} \ {{y | R x y}}).ncard :=
        Set.ncard_le_ncard (by rintro _ ⟨B, hB, rfl⟩; exact hmaps B hB)
    _ < _ := Set.ncard_sdiff_singleton_lt_of_mem
        (show {y | R x y} ∈ {B : Set α | (∃ a, B = {b | R a b}) ∧ B.Nontrivial} from ⟨⟨x, rfl⟩, hP⟩)

theorem ncard_setOf_eq_card_filter {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    {a | p a}.ncard = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

end Set
