module

public import Mathlib.Logic.Equiv.Set

/-!
# A type with an injective map is equivalent to the subtype of its image
-/

@[expose] public noncomputable section

namespace Equiv

variable {α β : Type*}

/-- A type with an injective map to `β` is equivalent to the subtype of `β` of a predicate that holds
exactly on the image. -/
def ofInjectiveSubtype (f : α → β) (hf : Function.Injective f) (Q : β → Prop)
    (hQ : ∀ b, Q b ↔ ∃ a, f a = b) : α ≃ {b // Q b} :=
  (Equiv.ofInjective f hf).trans (Equiv.subtypeEquivRight fun b => (hQ b).symm)

@[simp] theorem ofInjectiveSubtype_apply (f : α → β) (hf : Function.Injective f) (Q : β → Prop)
    (hQ : ∀ b, Q b ↔ ∃ a, f a = b) (a : α) : (ofInjectiveSubtype f hf Q hQ a).1 = f a := rfl

theorem ofInjectiveSubtype_symm_apply (f : α → β) (hf : Function.Injective f) (Q : β → Prop)
    (hQ : ∀ b, Q b ↔ ∃ a, f a = b) (b : {b // Q b}) :
    f ((ofInjectiveSubtype f hf Q hQ).symm b) = b.1 := by
  have := ofInjectiveSubtype_apply f hf Q hQ ((ofInjectiveSubtype f hf Q hQ).symm b)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

end Equiv
