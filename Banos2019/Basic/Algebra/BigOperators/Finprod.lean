module

public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Finite sums over the elements of a subtype

* `finsum_mem_setOf_subtype_of_imp`, `finsum_mem_setOf_subtype_ne`: a sum over the elements of a
  subtype satisfying a predicate is the sum over the elements of the type satisfying it.
-/

@[expose] public section

open Finset

variable {α M : Type*} [Fintype α] [AddCommMonoid M]

/-- A sum over the elements of a subtype satisfying `p`, when `p` implies the predicate of the
subtype. -/
theorem finsum_mem_setOf_subtype_of_imp {q p : α → Prop} [DecidablePred p]
    (hpq : ∀ a, p a → q a) (F : α → M) :
    ∑ᶠ f ∈ {f : {a // q a} | p f.1}, F f.1 = ∑ a ∈ univ.filter p, F a := by
  have himg : Subtype.val '' {f : {a // q a} | p f.1} = ↑(univ.filter p) := by
    ext e
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro he
      exact ⟨⟨e, hpq e he⟩, he, rfl⟩
  rw [← finsum_mem_image (g := Subtype.val) Subtype.val_injective.injOn, himg,
    finsum_mem_coe_finset]

/-- A sum over the elements other than `a₀` satisfying `p`, which `a₀` does not. -/
theorem finsum_mem_setOf_subtype_ne {a₀ : α} {p : α → Prop} [DecidablePred p] (hp : ¬ p a₀)
    (F : α → M) : ∑ᶠ f ∈ {f : {a // a ≠ a₀} | p f.1}, F f.1 = ∑ a ∈ univ.filter p, F a :=
  finsum_mem_setOf_subtype_of_imp (q := (· ≠ a₀)) (fun _ ha h => hp (h ▸ ha)) F
