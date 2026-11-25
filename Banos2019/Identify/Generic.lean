module

public import Banos2019.Quartet.Generic

/-!
# Two generic properties together

A property holds *for generic parameters* when the parameters violating it form a null set
(`ForGenericParams`, `RootedNetwork.IsGenericNull`); null sets are closed under countable unions
(`forGenericParams_iInter`), so two generic properties hold together for generic parameters
(`ForGenericParams.and`). Sections 8 and 9 combine in this way the generic statements of Section 7.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*} [Fintype E] {N : RootedNetwork V E X}

/-- Two generic properties hold together for generic parameters. -/
theorem ForGenericParams.and {P Q : MetricData E → Prop} (hP : ForGenericParams N P)
    (hQ : ForGenericParams N Q) : ForGenericParams N fun θ => P θ ∧ Q θ :=
  (forGenericParams_iInter (ι := Bool) (P := fun b => if b then P else Q)
    (fun b => by cases b <;> simpa)).mono
    fun θ hθ => ⟨by simpa using hθ true, by simpa using hθ false⟩

end Banos2019
