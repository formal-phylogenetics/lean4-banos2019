module

public import Banos2019.Quartet.DeleteArcReduce
public import Banos2019.Quartet.ContractSet

/-!
# The reduced networks of Section 5, as binary LSA networks

The networks that Lemmas 7–11 and Corollary 2 produce from an LSA quartet network `Q` (the network
without a hybrid edge, and the network with some cycles inducing 2-cycles contracted) have nodes of
degree two; the paper identifies them with their suppressions. `reduceNet` builds that suppression,
and this module collects what it keeps.

* `exists_reduce_deleteArc`: without a hybrid edge of a cycle `C`: a binary level-1 metric LSA
  network with the concordance factors of `deleteArc Q h`, fewer cycles, the cycles of `Q` other than
  `C` with their types, and, for a `2₂`- or `3₁`-cycle, the cut edges of `Q` between two pairs of
  taxa.
* `exists_reduce_contractSet`: with the cycles satisfying `P` contracted, when they induce 2-cycles:
  the same, with the cycles of `Q` not satisfying `P`, and all the cut edges of `Q`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] {Q : RootedNetwork V E X}
  {θ : MetricData E}

/-- A set of two taxa among four has a taxon and misses one. -/
theorem exists_mem_and_notMem_of_ncard_eq_two (hX : Fintype.card X = 4) {A : Set X}
    (hA : A.ncard = 2) : (∃ x, x ∈ A) ∧ ∃ x, x ∉ A := by
  refine ⟨Set.nonempty_of_ncard_ne_zero (by omega), ?_⟩
  by_contra h
  push Not at h
  have : A = Set.univ := Set.eq_univ_of_forall h
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, hX] at hA
  omega

/-- **The network without a hybrid edge `h` of a cycle `C`, as a binary LSA network.** -/
theorem exists_reduce_deleteArc (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    (hlsa : Q.IsLSANetwork) (hX : Fintype.card X = 4) (hθ : IsMetricNetwork Q θ) {C : Set E}
    {v : V} {n k : ℕ} (hC : InducesCycleType Q C v n k) {h : E} (hh : Q.graph.target h = v) :
    ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (Q' : RootedNetwork V' E' X)
      (θ' : MetricData E'),
      IsBinaryRootedNetwork Q' ∧ IsLevelOne Q'.graph ∧ Q'.IsLSANetwork ∧ IsMetricNetwork Q' θ' ∧
        cf Q' θ' = cf (deleteArc Q h) (deleteArcMetric Q h θ) ∧
        {D | IsCycle Q'.graph D}.ncard < {D | IsCycle Q.graph D}.ncard ∧
        (∀ n' k' (Dx : Set X), (∃ D w, InducesCycleType Q' D w n' k' ∧
            {x | Q'.graph.Reaches w (Q'.leaf x)} = Dx) ↔
          ∃ D w, D ≠ C ∧ InducesCycleType Q D w n' k' ∧ {x | Q.graph.Reaches w (Q.leaf x)} = Dx) ∧
        (((n = 2 ∧ k = 2) ∨ (n = 3 ∧ k = 1)) → ∀ A : Set X, A.ncard = 2 →
          (Q'.HasCutSplit A ↔ Q.HasCutSplit A)) := by
  have htwo : ∃ x y : X, x ≠ y := by
    have : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_pair_ne X
  have hn : 2 ≤ n := (add_le_of_inducesCycleType hQ h1 hlsa hC).2.2
  have hM := isReducible_deleteArc hQ h1 hC hh hθ htwo hn
  have hcyc := fun n' k' Dx =>
    (hM.exists_inducesCycleType_iff n' k' Dx).trans
      (deleteArc_exists_inducesCycleType_iff hQ h1 hC hh n' k' Dx)
  refine ⟨_, _, inferInstance, inferInstance, reduceNet _ hM.phylo, reduceMetric _ hM.phylo _,
    hM.isBinaryRootedNetwork, hM.isLevelOne, hM.isLSANetwork fun D w k' hD => ?_,
    hM.isMetricNetwork, hM.cf_eq, ?_, hcyc, fun hnk A hA => ?_⟩
  · obtain ⟨D', w', -, hD', -⟩ := (deleteArc_exists_inducesCycleType_iff hQ h1 hC hh 1 k' _).1
      ⟨D, w, hD, rfl⟩
    have := (add_le_of_inducesCycleType hQ h1 hlsa hD').2.2
    omega
  · rw [hM.ncard_setOf_isCycle]
    exact ncard_setOf_isCycle_deleteArc_lt hQ h1 hC hh
  · obtain ⟨h₁, h₂⟩ := exists_mem_and_notMem_of_ncard_eq_two hX hA
    exact (hM.hasCutSplit_iff h₁ h₂).trans (deleteArc_hasCutSplit_iff hQ h1 hC hh hX hnk hA)

/-- **The network with the cycles satisfying `P` contracted, as a binary LSA network**, when these
cycles induce 2-cycles. -/
theorem exists_reduce_contractSet (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    (hlsa : Q.IsLSANetwork) (hX : Fintype.card X = 4) (hθ : IsMetricNetwork Q θ)
    {P : Set E → Prop}
    (hn : ∀ C, IsCycle Q.graph C → P C →
      C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0) = 2) :
    ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (Q' : RootedNetwork V' E' X)
      (θ' : MetricData E'),
      IsBinaryRootedNetwork Q' ∧ IsLevelOne Q'.graph ∧ Q'.IsLSANetwork ∧ IsMetricNetwork Q' θ' ∧
        cf Q' θ' = cf (contractRooted Q P) (contractMetric Q P θ) ∧
        {D | IsCycle Q'.graph D}.ncard = {D | IsCycle Q.graph D ∧ ¬ P D}.ncard ∧
        (∀ n' k' (Dx : Set X), (∃ D w, InducesCycleType Q' D w n' k' ∧
            {x | Q'.graph.Reaches w (Q'.leaf x)} = Dx) ↔
          ∃ D w, ¬ P D ∧ InducesCycleType Q D w n' k' ∧ {x | Q.graph.Reaches w (Q.leaf x)} = Dx) ∧
        (∀ A : Set X, A.ncard = 2 → (Q'.HasCutSplit A ↔ Q.HasCutSplit A)) := by
  have htwo : ∃ x y : X, x ≠ y := by
    have : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_pair_ne X
  have hM := isReducible_contractSet hQ h1 hθ htwo hn
  have hcyc := fun n' k' Dx =>
    (hM.exists_inducesCycleType_iff n' k' Dx).trans
      (contractSet_exists_inducesCycleType_iff hQ h1 (P := P) n' k' Dx)
  refine ⟨_, _, inferInstance, inferInstance, reduceNet _ hM.phylo, reduceMetric _ hM.phylo _,
    hM.isBinaryRootedNetwork, hM.isLevelOne, hM.isLSANetwork fun D w k' hD => ?_,
    hM.isMetricNetwork, hM.cf_eq, ?_, hcyc, fun A hA => ?_⟩
  · obtain ⟨D', w', -, hD', -⟩ := (contractSet_exists_inducesCycleType_iff hQ h1 (P := P) 1 k' _).1
      ⟨D, w, hD, rfl⟩
    have := (add_le_of_inducesCycleType hQ h1 hlsa hD').2.2
    omega
  · rw [hM.ncard_setOf_isCycle]
    exact ncard_setOf_isCycle_contractSet hQ h1
  · obtain ⟨h₁, h₂⟩ := exists_mem_and_notMem_of_ncard_eq_two hX hA
    exact (hM.hasCutSplit_iff h₁ h₂).trans (contractSet_hasCutSplit_iff hQ h1 A)

end Banos2019
