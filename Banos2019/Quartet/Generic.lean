module

public import Banos2019.Coalescent
public import Banos2019.Basic.Analysis.AnalyticZeroSet
public import Phylogenetics.NMSC.Analytic

/-!
# Null sets of parameters

"For generic numerical parameters" (`ForGenericParams`): outside a null set of parameters
(`RootedNetwork.IsGenericNull`).

* `isGenericNull_mono`, `isGenericNull_empty`, `isGenericNull_union`, `isGenericNull_iUnion`: null sets
  of parameters are closed under subsets and countable unions.
* `ForGenericParams.mono`, `forGenericParams_of_forall`, `forGenericParams_iInter`.
* `isGenericNull_of_analyticOnNhd`: a function of the parameters that is analytic in the coordinates
  of `IsGenericNull` and nonzero at some parameters vanishes only on a null set of parameters;
  `isGenericNull_nmscCF_eq`: two concordance factors that differ at some parameters differ at generic
  parameters.

The first four lemmas are those of lean4-tob (`TreeOfBlobs/General.lean`, commit `e435ae0`), and the
analytic argument is that of lean4-allman2023 (`AllmanEtAl2023/GenericCF.lean`, commit `f01bb42`,
`isGenericNull_of_analyticOnNhd`, `isGenericNull_nmscCF_eq`, for valid rather than normalized
parameters), https://github.com/vltanh, licensed under the Apache License 2.0; this project cannot
import those repositories. They belong in lean4-phylogenetics.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype E] {N : RootedNetwork V E X}

/-- A subset of a null set of parameters is null. -/
theorem isGenericNull_mono {A B : Set (MetricData E)} (hB : N.IsGenericNull B) (h : A ⊆ B) :
    N.IsGenericNull A := by
  intro d hd
  refine measure_mono_null ?_ (hB d hd)
  rintro x ⟨θ, hθ, rest⟩
  exact ⟨θ, h hθ, rest⟩

/-- The empty set of parameters is null. -/
theorem isGenericNull_empty : N.IsGenericNull ∅ := by
  intro d _
  have : {x : (E → ℝ) × (E → ℝ) | ∃ θ ∈ (∅ : Set (MetricData E)), N.IsMetric θ ∧ θ.length = x.1 ∧
      ∀ e, N.IsHybridArc e → e ≠ d (N.graph.target e) → θ.inheritance e = x.2 e} = ∅ := by
    ext x
    simp
  rw [this, measure_empty]

/-- A countable union of null sets of parameters is null. -/
theorem isGenericNull_iUnion {ι : Type*} [Countable ι] {A : ι → Set (MetricData E)}
    (h : ∀ i, N.IsGenericNull (A i)) : N.IsGenericNull (⋃ i, A i) := by
  intro d hd
  refine measure_mono_null ?_ (measure_iUnion_null fun i => h i d hd)
  rintro x ⟨θ, hθ, rest⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hθ
  exact Set.mem_iUnion.2 ⟨i, θ, hi, rest⟩

/-- The union of two null sets of parameters is null. -/
theorem isGenericNull_union {A B : Set (MetricData E)} (hA : N.IsGenericNull A)
    (hB : N.IsGenericNull B) : N.IsGenericNull (A ∪ B) := by
  rw [Set.union_eq_iUnion]
  exact isGenericNull_iUnion fun b => by cases b <;> assumption

variable [Fintype V] [Fintype X]

/-- A property implied by a generic property is generic. -/
theorem ForGenericParams.mono {P P' : MetricData E → Prop} (h : ForGenericParams N P)
    (hP : ∀ θ, P θ → P' θ) : ForGenericParams N P' :=
  isGenericNull_mono h fun θ hθ h' => hθ (hP θ h')

/-- A property of all parameters is generic. -/
theorem forGenericParams_of_forall {P : MetricData E → Prop} (h : ∀ θ, P θ) :
    ForGenericParams N P :=
  isGenericNull_mono (isGenericNull_empty (N := N)) fun θ hθ => hθ (h θ)

/-- Countably many generic properties hold together generically. -/
theorem forGenericParams_iInter {ι : Type*} [Countable ι] {P : ι → MetricData E → Prop}
    (h : ∀ i, ForGenericParams N (P i)) : ForGenericParams N fun θ => ∀ i, P i θ := by
  refine isGenericNull_mono (isGenericNull_iUnion h) fun θ hθ => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hθ
  obtain ⟨i, hi⟩ := hθ
  exact Set.mem_iUnion.2 ⟨i, hi⟩

/-- Valid parameters are `coordMetric` at their own coordinates. -/
theorem coordMetric_self_of_isMetric {θ : MetricData E} (hθ : N.IsMetric θ) (d : V → E) :
    coordMetric N d θ.length θ.inheritance = θ :=
  (eq_coordMetric hθ rfl fun _ _ _ => rfl).symm

/-- **The analytic argument.** A function of the parameters that is analytic in the coordinates of
`IsGenericNull`, for every choice of the left-out coordinates, and nonzero at some valid parameters,
vanishes only on a null set of valid parameters. -/
theorem isGenericNull_of_analyticOnNhd {F : MetricData E → ℝ}
    (hF : ∀ d : V → E, AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) => F (coordMetric N d x.1 x.2))
      Set.univ) {θ₀ : MetricData E} (hθ₀ : N.IsMetric θ₀) (h : F θ₀ ≠ 0) :
    N.IsGenericNull {θ | N.IsMetric θ ∧ F θ = 0} := by
  intro d _
  have hw : F (coordMetric N d θ₀.length θ₀.inheritance) ≠ 0 := by
    rwa [coordMetric_self_of_isMetric hθ₀ d]
  refine measure_mono_null ?_
    (AnalyticOnNhd.prod_pi_volume_setOf_eq_zero (hF d) ⟨(θ₀.length, θ₀.inheritance), hw⟩)
  rintro x ⟨θ, ⟨-, hzero⟩, hθ, hℓ, hg⟩
  show F (coordMetric N d x.1 x.2) = 0
  rw [← eq_coordMetric hθ hℓ hg]
  exact hzero

/-- Two concordance factors that differ at some valid parameters differ at generic parameters. -/
theorem isGenericNull_nmscCF_eq {r r' : QuartetTree X} {θ₀ : MetricData E} (hθ₀ : N.IsMetric θ₀)
    (h : nmscCF N θ₀ 0 r ≠ nmscCF N θ₀ 0 r') :
    N.IsGenericNull {θ | N.IsMetric θ ∧ nmscCF N θ 0 r = nmscCF N θ 0 r'} :=
  isGenericNull_mono (isGenericNull_of_analyticOnNhd (F := fun θ => nmscCF N θ 0 r - nmscCF N θ 0 r')
    (fun d => (analyticOnNhd_nmscCF_coordMetric N d 0 r).sub
      (analyticOnNhd_nmscCF_coordMetric N d 0 r')) hθ₀ (sub_ne_zero.2 h))
    fun _ hθ => ⟨hθ.1, sub_eq_zero.2 hθ.2⟩

end Banos2019
