module

public import Banos2019.Coalescent
public import Phylogenetics.NMSC.Generic

/-!
# Generic parameters

"For generic numerical parameters" (`ForGenericParams`): outside a null set of parameters
(`RootedNetwork.IsGenericNull`). The null sets of parameters and the analytic argument are those of
lean4-phylogenetics (`Phylogenetics.NMSC.Generic`): `IsGenericNull.mono`, `isGenericNull_empty`,
`IsGenericNull.union`, `IsGenericNull.iUnion`, `isGenericNull_of_analyticOnNhd`,
`isGenericNull_nmscCF_eq`. This module adds the corresponding facts for `ForGenericParams`.

* `ForGenericParams.mono`, `forGenericParams_of_forall`, `forGenericParams_iInter`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype E] {N : RootedNetwork V E X}

/-- A property implied by a generic property is generic. -/
theorem ForGenericParams.mono {P P' : MetricData E → Prop} (h : ForGenericParams N P)
    (hP : ∀ θ, P θ → P' θ) : ForGenericParams N P' :=
  IsGenericNull.mono h fun θ hθ h' => hθ (hP θ h')

/-- A property of all parameters is generic. -/
theorem forGenericParams_of_forall {P : MetricData E → Prop} (h : ∀ θ, P θ) :
    ForGenericParams N P :=
  (isGenericNull_empty (N := N)).mono fun θ hθ => hθ (h θ)

/-- Countably many generic properties hold together generically. -/
theorem forGenericParams_iInter {ι : Type*} [Countable ι] {P : ι → MetricData E → Prop}
    (h : ∀ i, ForGenericParams N (P i)) : ForGenericParams N fun θ => ∀ i, P i θ := by
  refine (IsGenericNull.iUnion h).mono fun θ hθ => ?_
  simp only [Set.mem_ofPred_eq, not_forall] at hθ
  obtain ⟨i, hi⟩ := hθ
  exact Set.mem_iUnion.2 ⟨i, hi⟩

end Banos2019
