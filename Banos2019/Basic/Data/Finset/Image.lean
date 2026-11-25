module

public import Mathlib.Data.Fintype.Basic

/-!
# Images of `univ`

* `Finset.range_eq_coe_of_image_univ_eq`: the range of a map from a finite type is its image of
  `univ`.
* `Finset.image_val_univ_coe`: the elements of a finset, as a type, map onto the finset.
-/

@[expose] public section

namespace Finset

variable {α β : Type*}

/-- The range of a map from a finite type is its image of `univ`. -/
theorem range_eq_coe_of_image_univ_eq [Fintype α] [DecidableEq β] {f : α → β} {s : Finset β}
    (h : univ.image f = s) : Set.range f = ↑s := by
  rw [← h, coe_image, coe_univ, Set.image_univ]

theorem image_val_univ_coe [DecidableEq β] (s : Finset β) :
    (univ : Finset (s : Set β)).image Subtype.val = s := by
  ext x
  simp

end Finset
