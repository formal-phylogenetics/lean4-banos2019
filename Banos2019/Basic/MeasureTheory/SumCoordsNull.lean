module

public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Null sets pulled back along sums of coordinates

On `(ι → ℝ) × (κ → ℝ)`, with the product of Lebesgue measures, the map `x ↦ (∑_{e ∈ A} x₁ e,
∑_{e ∈ B} x₁ e, α + σ ∑_{f ∈ H} x₂ f)` for disjoint nonempty sets `A`, `B` of coordinates, a nonempty
set `H` and `σ ≠ 0` is affine and onto `ℝ³`, so the preimage of a null set is null
(`prod_pi_volume_preimage_sum_coords_null`). The linear part is surjective, and a surjective linear map
pushes a Haar measure to a multiple of a Haar measure (`MeasureTheory.ae_comp_linearMap_mem_iff`).
-/

@[expose] public section

open Set

namespace MeasureTheory

/-- **The preimage of a null set of `ℝ³` under sums of coordinates over disjoint nonempty sets is
null**: the first two coordinates of the image are the sums of `x₁` over `A` and over `B`, the third
an affine function `α + σ ∑_{f ∈ H} x₂ f` of the second factor. -/
theorem prod_pi_volume_preimage_sum_coords_null {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A B : Finset ι} (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B) {H : Finset κ}
    (hH : H.Nonempty) (α σ : ℝ) (hσ : σ ≠ 0) {Z : Set (Fin 3 → ℝ)} (hZ : volume Z = 0) :
    ((Measure.pi fun _ : ι => (volume : Measure ℝ)).prod
        (Measure.pi fun _ : κ => (volume : Measure ℝ)))
      {x | ![∑ e ∈ A, x.1 e, ∑ e ∈ B, x.1 e, α + σ * ∑ f ∈ H, x.2 f] ∈ Z} = 0 := by
  classical
  obtain ⟨Z₀, hZZ₀, hZ₀m, hZ₀⟩ := exists_measurable_superset_of_null hZ
  -- the linear part of the map
  let φA : ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] ℝ := (∑ e ∈ A, LinearMap.proj e) ∘ₗ LinearMap.fst ℝ _ _
  let φB : ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] ℝ := (∑ e ∈ B, LinearMap.proj e) ∘ₗ LinearMap.fst ℝ _ _
  let φH : ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] ℝ := σ • (∑ f ∈ H, LinearMap.proj f) ∘ₗ LinearMap.snd ℝ _ _
  let L : ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] Fin 3 → ℝ := LinearMap.pi ![φA, φB, φH]
  have hL : ∀ x, L x = ![∑ e ∈ A, x.1 e, ∑ e ∈ B, x.1 e, σ * ∑ f ∈ H, x.2 f] := fun x => by
    funext i
    fin_cases i <;> simp [L, φA, φB, φH]
  -- it is onto
  have hLs : Function.Surjective L := by
    intro p
    obtain ⟨a₀, ha₀⟩ := hA
    obtain ⟨b₀, hb₀⟩ := hB
    obtain ⟨h₀, hh₀⟩ := hH
    have ha₀B : a₀ ∉ B := Finset.disjoint_left.1 hAB ha₀
    have hb₀A : b₀ ∉ A := Finset.disjoint_right.1 hAB hb₀
    refine ⟨(Pi.single a₀ (p 0) + Pi.single b₀ (p 1), Pi.single h₀ (p 2 / σ)), ?_⟩
    rw [hL]
    funext i
    fin_cases i
    · simp [Finset.sum_add_distrib, Finset.sum_pi_single', ha₀, hb₀A]
    · simp [Finset.sum_add_distrib, Finset.sum_pi_single', hb₀, ha₀B]
    · simp [Finset.sum_pi_single', hh₀, mul_div_cancel₀ _ hσ]
  -- the translate of `Z₀` by the constant part is a measurable null set
  set Z₁ := (fun y => ![0, 0, α] + y) ⁻¹' Z₀ with hZ₁_def
  have hZ₁m : MeasurableSet Z₁ := hZ₀m.preimage (measurable_const_add _)
  have hZ₁ : volume Z₁ = 0 := by rw [hZ₁_def, measure_preimage_add]; exact hZ₀
  have hae := (ae_comp_linearMap_mem_iff L
    ((Measure.pi fun _ : ι => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : κ => (volume : Measure ℝ))) volume hLs hZ₁m.compl).2
    (ae_iff.2 (by simpa using hZ₁))
  rw [ae_iff] at hae
  refine measure_mono_null (fun x hx => ?_) hae
  show ¬ L x ∈ Z₁ᶜ
  rw [Set.notMem_compl_iff, hZ₁_def, Set.mem_preimage, hL]
  apply hZZ₀
  have e : ![0, 0, α] + ![∑ e ∈ A, x.1 e, ∑ e ∈ B, x.1 e, σ * ∑ f ∈ H, x.2 f] =
      ![∑ e ∈ A, x.1 e, ∑ e ∈ B, x.1 e, α + σ * ∑ f ∈ H, x.2 f] := by
    funext i
    fin_cases i <;> simp
  rw [e]
  exact hx

end MeasureTheory
