module

public import Banos2019.Quartet.Generic
public import Banos2019.Basic.MeasureTheory.SumCoordsNull

/-!
# Null sets of parameters pulled back along chains of edges

The map `ν` of the proof of Proposition 10 sends the parameters of a network to the lengths of two
edges of a reduced network, sums of the lengths of disjoint nonempty chains `A`, `B` of edges, and
to the inheritance probability `γ` of a hybrid edge `h`. In the coordinates of `IsGenericNull`, `γ`
is a coordinate, or one minus the sum of the coordinates of the other edges into the child of `h`;
so `ν` is affine and onto, and the preimage of a null set of `ℝ³` is a null set of parameters
(`isGenericNull_preimage_chainSum`, from `prod_pi_volume_preimage_sum_coords_null`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype E] {N : RootedNetwork V E X}

/-- **The preimage of a null set under `ν` is null**: the parameters whose lengths summed over the
disjoint nonempty sets of edges `A` and `B`, and whose inheritance probability of the hybrid edge
`h`, lie in a null set of `ℝ³` form a null set of parameters. -/
theorem isGenericNull_preimage_chainSum {A B : Finset E} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) {h : E} (hh : N.IsHybridArc h) {Z : Set (Fin 3 → ℝ)} (hZ : volume Z = 0) :
    N.IsGenericNull
      {θ | N.IsMetric θ ∧ ![∑ e ∈ A, θ.length e, ∑ e ∈ B, θ.length e, θ.inheritance h] ∈ Z} := by
  intro d hd
  by_cases hdh : h = d (N.graph.target h)
  · -- `γ` is one minus the coordinates of the other edges into the child of `h`
    set H := univ.filter fun f => N.graph.target f = N.graph.target h ∧ f ≠ h with hH_def
    have hH : H.Nonempty := by
      have h2 : 1 < {f | N.graph.target f = N.graph.target h}.ncard := hh
      obtain ⟨f₁, hf₁, f₂, hf₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).1 h2
      by_cases h₁ : f₁ = h
      · exact ⟨f₂, mem_filter.2 ⟨mem_univ _, hf₂, fun h₂ => hne (h₁.trans h₂.symm)⟩⟩
      · exact ⟨f₁, mem_filter.2 ⟨mem_univ _, hf₁, h₁⟩⟩
    refine measure_mono_null ?_
      (prod_pi_volume_preimage_sum_coords_null hA hB hAB hH 1 (-1) (by norm_num) hZ)
    rintro x ⟨θ, ⟨-, hθZ⟩, hθ, hℓ, hg⟩
    rw [eq_coordMetric hθ hℓ hg, coordMetric_inheritance_of_eq hh hdh] at hθZ
    convert hθZ using 2
    simp only [neg_one_mul, ← sub_eq_add_neg]
    rfl
  · -- `γ` is a coordinate
    refine measure_mono_null ?_ (prod_pi_volume_preimage_sum_coords_null hA hB hAB
      (singleton_nonempty h) 0 1 one_ne_zero hZ)
    rintro x ⟨θ, ⟨-, hθZ⟩, hθ, hℓ, hg⟩
    rw [eq_coordMetric hθ hℓ hg, coordMetric_inheritance_of_ne hh hdh] at hθZ
    convert hθZ using 2
    simp

end Banos2019
