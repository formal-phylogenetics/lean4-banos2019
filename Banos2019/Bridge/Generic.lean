module

public import Banos2019.Bridge.Model

/-!
# "For generic parameters" is not vacuous

The metric parameters of a binary network do not form a null set: choose at each hybrid node one of its
two hybrid edges; the parameters whose edge lengths are in `(0, 1)` and whose other hybrid edges have
inheritance probability in `(0, 1)` are metric (the chosen edge gets the complement), and in the
coordinates of `IsGenericNull` they fill a product of open unit boxes, of measure one. So no binary
network satisfies `ForGenericParams` of a false property (`Model.Network.not_forGenericParams_false`),
and Theorems 3 and 4 are not satisfied vacuously.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork MeasureTheory

namespace Banos2019.Model.Network

variable {V E X : Type*} [Fintype E] (N : Network V E X)

/-- **The metric parameters of a binary network are not a null set**: "for generic parameters" is not
satisfied vacuously. -/
theorem not_forGenericParams_false (hN : N.IsBinaryNetwork) :
    ¬ N.ForGenericParams fun _ => False := by
  classical
  intro h
  have hb := N.isBinaryNetwork_iff.mp hN
  -- the root has two edges, so there are edges
  have hE : Nonempty E := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h2 : N.graph.outdegree N.root = 2 := hb.2.1
    unfold Digraph.outdegree at h2
    rw [Set.eq_empty_of_isEmpty {e | N.graph.source e = N.root}, Set.ncard_empty] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨e₀⟩ := hE
  -- an edge chosen into each node that has one
  let d : V → E := fun v => if hv : ∃ e, N.graph.target e = v then hv.choose else e₀
  have hd : ∀ v, N.graph.indegree v = 2 → N.graph.target (d v) = v := fun v hv => by
    have hex : ∃ e, N.graph.target e = v :=
      (N.toRooted.graph.one_le_indegree_iff v).mp (by change 1 ≤ N.graph.indegree v; omega)
    simp only [d, hex, ↓reduceDIte]
    exact hex.choose_spec
  -- the other edge into the target of an edge
  let other : E → E := fun e =>
    if hf : ∃ f, f ≠ e ∧ N.graph.target f = N.graph.target e then hf.choose else e
  -- the two edges into a node of indegree two
  have htwo : ∀ e f, e ≠ f → N.graph.indegree (N.graph.target e) = 2 →
      N.graph.target e = N.graph.target f → ∀ g, N.graph.target g = N.graph.target e → g = e ∨ g = f :=
    fun e f hef he hf g hg => by
      have hset := eq_or_eq_of_indegree_eq_two (N := N.toRooted) he hef rfl hf.symm
      have : g ∈ ({e, f} : Set E) := by rw [← hset]; exact hg
      exact this
  have hother : ∀ e f, e ≠ f → N.graph.indegree (N.graph.target e) = 2 →
      N.graph.target e = N.graph.target f → other e = f := fun e f hef he hf => by
    have hex : ∃ f', f' ≠ e ∧ N.graph.target f' = N.graph.target e := ⟨f, hef.symm, hf.symm⟩
    simp only [other, hex, ↓reduceDIte]
    rcases htwo e f hef he hf _ hex.choose_spec.2 with h' | h'
    · exact absurd h' hex.choose_spec.1
    · exact h'
  let B : Set ((E → ℝ) × (E → ℝ)) :=
    (Set.univ.pi fun _ => Set.Ioo 0 1) ×ˢ (Set.univ.pi fun _ => Set.Ioo 0 1)
  have hB : B ⊆ {x | ∃ θ ∈ {θ : Params E | N.IsMetric θ ∧ ¬ False}, N.IsMetric θ ∧
      θ.length = x.1 ∧ ∀ e, N.IsHybridEdge e → e ≠ d (N.graph.target e) →
        θ.inheritance e = x.2 e} := by
    rintro ⟨x₁, x₂⟩ ⟨h₁, h₂⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies] at h₁ h₂
    let θ : Params E := ⟨x₁, fun e => if N.IsHybridEdge e then
      (if e = d (N.graph.target e) then 1 - x₂ (other e) else x₂ e) else 1⟩
    have hθ : N.IsMetric θ := by
      refine ⟨fun e => (h₁ e).1, fun e he => by simp [θ, he], fun e he => ?_,
        fun e f hef he hf => ?_⟩
      · simp only [θ, he, ↓reduceIte]
        split_ifs
        · exact ⟨by linarith [(h₂ (other e)).2], by linarith [(h₂ (other e)).1]⟩
        · exact h₂ e
      · have hfh : N.IsHybridEdge f := by unfold IsHybridEdge; rw [← hf]; exact he
        have hdv := hd _ he
        simp only [θ, he, hfh, ↓reduceIte]
        rcases htwo e f hef he hf _ hdv with hde | hdf
        · have hfd : f ≠ d (N.graph.target f) := by rw [← hf, hde]; exact hef.symm
          rw [ite_eq_left_of_eq_true _ _ (eq_true hde.symm), ite_eq_right_of_eq_false _ _ (eq_false hfd),
            hother e f hef he hf]
          ring
        · have hed : e ≠ d (N.graph.target e) := by rw [hdf]; exact hef
          have hfd : f = d (N.graph.target f) := by rw [← hf, hdf]
          rw [ite_eq_right_of_eq_false _ _ (eq_false hed), ite_eq_left_of_eq_true _ _ (eq_true hfd),
            hother f e hef.symm (by rw [← hf]; exact he) hf.symm]
          ring
    exact ⟨θ, ⟨hθ, not_false⟩, hθ, rfl, fun e he hne => by simp [θ, he, hne]⟩
  have hpos : ((Measure.pi fun _ : E => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : E => (volume : Measure ℝ))) B = 1 := by
    rw [Measure.prod_prod, Measure.pi_pi]
    simp [Real.volume_Ioo]
  have hle := measure_mono (μ := (Measure.pi fun _ : E => (volume : Measure ℝ)).prod
    (Measure.pi fun _ : E => (volume : Measure ℝ))) hB
  rw [h d hd, hpos] at hle
  exact absurd hle (by norm_num)

end Banos2019.Model.Network
