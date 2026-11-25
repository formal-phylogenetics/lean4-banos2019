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
  network with the concordance factors of `deleteArc Q h`, fewer cycles, the cycles of `Q` other
  than `C` with their types, and, for a `2₂`- or `3₁`-cycle, the cut edges of `Q` between two pairs
  of taxa.
* `contractNet`, `contractNetMetric`: `Q` with the cycles satisfying `P` contracted and its nodes of
  degree two suppressed, with the parameters from those of `Q`; `contractNetChain`,
  `contractNetLastArc`: the chain of arcs of `Q` of each of its arcs, and the last one.
  `contractNetMetric_length`, `contractNetMetric_inheritance`, `isHybridArc_contractNet_iff`: an arc
  has the total length of its chain, and the inheritance and the type of its last arc.
* `contractNet_spec`, `exists_reduce_contractSet`: when the contracted cycles induce 2-cycles: a
  binary level-1 metric LSA network with the concordance factors of `contractRooted Q P`, the cycles
  of `Q` not satisfying `P` with their types, and all the cut edges of `Q`.
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

/-! ### The network with cycles contracted, explicitly -/

section ContractNet

variable (Q) (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph) (P : Set E → Prop)

/-- **`Q` with the cycles satisfying `P` contracted and the nodes of degree two this leaves
suppressed** (`reduceNet`); it does not depend on the parameters. -/
def contractNet := reduceNet (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)

/-- The parameters of `contractNet` from those `θ` of `Q`: along a chain of arcs of `Q`, lengths add
(`contractNetMetric_length`), and the inheritance is that of the last arc
(`contractNetMetric_inheritance`). -/
def contractNetMetric (θ : MetricData E) :=
  reduceMetric (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)
    (contractMetric Q P θ)

/-- The arcs of `Q` on the chain of an arc of `contractNet`. -/
def contractNetChain (e : ReduceArc (contractRooted Q P)
    (contractSet_isPhylogenetic (P := P) hQ h1)) :
    Finset E :=
  (reduceChain _ _ e).map (Function.Embedding.subtype _)

/-- The last arc of `Q` on the chain of an arc of `contractNet`. -/
def contractNetLastArc
    (e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)) : E :=
  (reduceLastArc _ _ e).1

variable {Q hQ h1 P}

omit [Fintype X] in
/-- **The length of an arc of `contractNet` is the total length of its chain of arcs of `Q`.** -/
theorem contractNetMetric_length (θ : MetricData E)
    (e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)) :
    (contractNetMetric Q hQ h1 P θ).length e = ∑ f ∈ contractNetChain Q hQ h1 P e, θ.length f := by
  unfold contractNetMetric contractNetChain
  rw [reduceMetric_length, sum_map]
  rfl

omit [Fintype X] in
/-- An arc of `contractNet` is the first arc of its chain. -/
theorem contractNetChain_nonempty
    (e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)) :
    (contractNetChain Q hQ h1 P e).Nonempty :=
  ⟨_, mem_map_of_mem _ (mem_reduceChain_self _ e)⟩

omit [Fintype X] in
/-- **The chains of distinct arcs of `contractNet` are disjoint.** -/
theorem disjoint_contractNetChain
    {e e' : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)}
    (hne : e ≠ e') : Disjoint (contractNetChain Q hQ h1 P e) (contractNetChain Q hQ h1 P e') :=
  (disjoint_map _).2 (disjoint_reduceChain _ hne)

omit [Fintype X] in
/-- The last arc of the chain is on the chain. -/
theorem contractNetLastArc_mem
    (e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)) :
    contractNetLastArc Q hQ h1 P e ∈ contractNetChain Q hQ h1 P e :=
  mem_map_of_mem _ (reduceLastArc_mem _ e)

omit [Fintype X] in
/-- **The inheritance of an arc of `contractNet` is that of the last arc of its chain.** -/
theorem contractNetMetric_inheritance {θ : MetricData E} (hθ : Q.IsMetric θ)
    (e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)) :
    (contractNetMetric Q hQ h1 P θ).inheritance e =
      θ.inheritance (contractNetLastArc Q hQ h1 P e) :=
  reduceMetric_inheritance _ (contractSet_isMetric hQ h1 hθ).isNormalized e

omit [Fintype X] in
/-- **An arc of `contractNet` is a hybrid arc exactly when the last arc of its chain is one of
`Q`.** -/
theorem isHybridArc_contractNet_iff (htwo : ∃ x y : X, x ≠ y)
    (e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)) :
    (contractNet Q hQ h1 P).IsHybridArc e ↔ Q.IsHybridArc (contractNetLastArc Q hQ h1 P e) := by
  rw [contractNet, isHybridArc_reduceNet_iff _ htwo]
  unfold IsHybridArc
  rw [contractSet_indegree hQ h1, contractSetRep_target]
  rfl

end ContractNet

/-- **The network with the cycles satisfying `P` contracted, as a binary LSA network**, when these
cycles induce 2-cycles: `contractNet`, with the parameters `contractNetMetric θ`, is a binary
level-1 metric LSA network with the concordance factors of `contractRooted Q P`, the cycles of `Q`
not satisfying `P` with their types, and the cut edges of `Q` between two pairs of taxa. -/
theorem contractNet_spec (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    (hlsa : Q.IsLSANetwork) (hX : Fintype.card X = 4) (hθ : IsMetricNetwork Q θ)
    {P : Set E → Prop}
    (hn : ∀ C, IsCycle Q.graph C → P C →
      C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0) = 2) :
    IsBinaryRootedNetwork (contractNet Q hQ h1 P) ∧ IsLevelOne (contractNet Q hQ h1 P).graph ∧
      (contractNet Q hQ h1 P).IsLSANetwork ∧
      IsMetricNetwork (contractNet Q hQ h1 P) (contractNetMetric Q hQ h1 P θ) ∧
      cf (contractNet Q hQ h1 P) (contractNetMetric Q hQ h1 P θ) =
        cf (contractRooted Q P) (contractMetric Q P θ) ∧
      {D | IsCycle (contractNet Q hQ h1 P).graph D}.ncard = {D | IsCycle Q.graph D ∧ ¬ P D}.ncard ∧
      (∀ n' k' (Dx : Set X), (∃ D w, InducesCycleType (contractNet Q hQ h1 P) D w n' k' ∧
          {x | (contractNet Q hQ h1 P).graph.Reaches w ((contractNet Q hQ h1 P).leaf x)} = Dx) ↔
        ∃ D w, ¬ P D ∧ InducesCycleType Q D w n' k' ∧ {x | Q.graph.Reaches w (Q.leaf x)} = Dx) ∧
      (∀ A : Set X, A.ncard = 2 → ((contractNet Q hQ h1 P).HasCutSplit A ↔ Q.HasCutSplit A)) := by
  have htwo : ∃ x y : X, x ≠ y := by
    have : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_pair_ne X
  have hM := isReducible_contractSet hQ h1 hθ htwo hn
  have hcyc := fun n' k' Dx =>
    (hM.exists_inducesCycleType_iff n' k' Dx).trans
      (contractSet_exists_inducesCycleType_iff hQ h1 (P := P) n' k' Dx)
  refine ⟨hM.isBinaryRootedNetwork, hM.isLevelOne, hM.isLSANetwork fun D w k' hD => ?_,
    hM.isMetricNetwork, hM.cf_eq, ?_, hcyc, fun A hA => ?_⟩
  · obtain ⟨D', w', -, hD', -⟩ := (contractSet_exists_inducesCycleType_iff hQ h1 (P := P) 1 k' _).1
      ⟨D, w, hD, rfl⟩
    have := (add_le_of_inducesCycleType hQ h1 hlsa hD').2.2
    omega
  · exact hM.ncard_setOf_isCycle.trans (ncard_setOf_isCycle_contractSet hQ h1)
  · obtain ⟨h₁, h₂⟩ := exists_mem_and_notMem_of_ncard_eq_two hX hA
    exact (hM.hasCutSplit_iff h₁ h₂).trans (contractSet_hasCutSplit_iff hQ h1 A)

/-- **The network with the cycles satisfying `P` contracted, as a binary LSA network**, when these
cycles induce 2-cycles (`contractNet_spec`). -/
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
        (∀ A : Set X, A.ncard = 2 → (Q'.HasCutSplit A ↔ Q.HasCutSplit A)) :=
  ⟨_, _, inferInstance, inferInstance, contractNet Q hQ h1 P, contractNetMetric Q hQ h1 P θ,
    contractNet_spec hQ h1 hlsa hX hθ hn⟩

end Banos2019
