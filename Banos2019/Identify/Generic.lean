module

public import Banos2019.Coalescent

/-!
# Combining generic properties

A property holds *for generic parameters* when the parameters violating it form a null set
(`ForGenericParams`, `RootedNetwork.IsGenericNull`). Null sets of parameters are closed under subsets
and countable unions, so generic properties are closed under consequence and countable conjunction:
Sections 8 and 9 combine the generic statements of Section 7, one for each set of four taxa.

* `ForGenericParams.imp`, `ForGenericParams.and`, `ForGenericParams.forall`.

The closure of null sets of parameters under subsets and countable unions is that of lean4-tob
(`TreeOfBlobs/General.lean`, commit `e435ae0`, `IsGenericNull.mono`, `IsGenericNull.iUnion`),
https://github.com/vltanh/lean4-tob, licensed under the Apache License 2.0; this project cannot
import that repository. It belongs in lean4-phylogenetics.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork MeasureTheory

namespace Banos2019

variable {V E X : Type*} [Fintype E] {N : RootedNetwork V E X}

/-- A consequence of a generic property is generic. -/
theorem ForGenericParams.imp {P Q : MetricData E → Prop} (h : ForGenericParams N P)
    (hPQ : ∀ θ, P θ → Q θ) : ForGenericParams N Q := by
  intro d hd
  refine measure_mono_null ?_ (h d hd)
  rintro x ⟨θ, hθ, rest⟩
  exact ⟨θ, fun hP => hθ (hPQ θ hP), rest⟩

/-- Countably many generic properties hold together for generic parameters. -/
theorem ForGenericParams.forall {ι : Sort*} [Countable ι] {P : ι → MetricData E → Prop}
    (h : ∀ i, ForGenericParams N (P i)) : ForGenericParams N fun θ => ∀ i, P i θ := by
  intro d hd
  refine measure_mono_null ?_ (measure_iUnion_null fun i => h i d hd)
  rintro x ⟨θ, hθ, rest⟩
  obtain ⟨i, hi⟩ := not_forall.1 hθ
  exact Set.mem_iUnion.2 ⟨i, θ, hi, rest⟩

/-- Two generic properties hold together for generic parameters. -/
theorem ForGenericParams.and {P Q : MetricData E → Prop} (hP : ForGenericParams N P)
    (hQ : ForGenericParams N Q) : ForGenericParams N fun θ => P θ ∧ Q θ := by
  have h := ForGenericParams.forall (ι := Bool) (P := fun b => if b then P else Q)
    (fun b => by cases b <;> simpa)
  exact h.imp fun θ hθ => ⟨by simpa using hθ true, by simpa using hθ false⟩

end Banos2019
