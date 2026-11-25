module

public import Mathlib.Logic.Relation

/-!
# The reflexive transitive closure of a symmetric relation is symmetric
-/

@[expose] public section

namespace Relation.ReflTransGen

variable {α : Type*} {r : α → α → Prop}

theorem symm_of_symm (hr : ∀ a b, r a b → r b a) {a b : α} (h : ReflTransGen r a b) :
    ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.head (hr _ _ hbc)

end Relation.ReflTransGen
