module

public import Mathlib.Logic.Relation

/-!
# Paths of a relation that cannot avoid an element

For a relation `r`, a path from `a` to `b` *avoids* `m` when it is a path of the relation
`fun x y => r x y ∧ x ≠ m ∧ y ≠ m`.

* `Relation.ReflTransGen.through_of_not_avoiding`: if no path from `a` to `b` avoids `m`, every path
  passes through `m`: `a` reaches `m` and `m` reaches `b`.
* `Relation.ReflTransGen.ne_of_avoiding`: a path avoiding `m` from an element other than `m` ends at
  an element other than `m`.
-/

@[expose] public section

namespace Relation.ReflTransGen

variable {α : Type*} {r : α → α → Prop}

/-- A path from `a` to `b` when no path from `a` to `b` avoids `m` passes through `m`. -/
theorem through_of_not_avoiding {a b m : α} (h : ReflTransGen r a b)
    (hn : ¬ ReflTransGen (fun x y => r x y ∧ x ≠ m ∧ y ≠ m) a b) :
    ReflTransGen r a m ∧ ReflTransGen r m b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd .refl hn
  | @head x z hxz hzb ih =>
    by_cases hx : x = m
    · subst hx
      exact ⟨.refl, hzb.head hxz⟩
    by_cases hz : z = m
    · subst hz
      exact ⟨.single hxz, hzb⟩
    have hn' : ¬ ReflTransGen (fun x y => r x y ∧ x ≠ m ∧ y ≠ m) z b := fun h' =>
      hn (h'.head ⟨hxz, hx, hz⟩)
    exact ⟨(ih hn').1.head hxz, (ih hn').2⟩

/-- A path avoiding `m` from an element other than `m` ends at an element other than `m`. -/
theorem ne_of_avoiding {a b m : α} (h : ReflTransGen (fun x y => r x y ∧ x ≠ m ∧ y ≠ m) a b)
    (ha : a ≠ m) : b ≠ m := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, -, -, -, hb⟩
  · exact ha
  · exact hb

end Relation.ReflTransGen
