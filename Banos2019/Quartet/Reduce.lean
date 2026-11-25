module

public import Banos2019.Quartet.SuppressCycles
public import Banos2019.Quartet.LSARoot
public import Banos2019.Coalescent

/-!
# Networks with nodes of degree two, as binary networks

The reductions of Section 5 (deleting a hybrid edge, contracting cycles) leave networks with nodes of
indegree one and outdegree one, and possibly a root of outdegree one. The paper identifies such a
network with the network obtained by suppressing these nodes (Section 5: "networks with degree-two
nodes are identified with their suppressions"). This module builds that network and gives the
properties it keeps.

* `IsReducible M θ`: the hypotheses on `M`: a phylogenetic level-1 network whose nodes other than
  the root and the chain nodes have degree three, whose root has outdegree one or two, whose chain
  nodes are on no cycle, and whose root, when of outdegree one, has a child on no cycle.
* `reduceNet`, `reduceMetric`: `M` with its nodes of indegree one and outdegree one suppressed
  (`RootedNetwork.suppress`, lengths added along each chain), the arc at a root of outdegree one
  contracted, and its nodes and arcs renamed by `Fin`.
* `IsReducible.reduce_spec`: it is a binary level-1 metric network with the concordance factors of
  `M` (`NMSC.nmscCF_suppress`, `IsContraction.nmscCF_eq`), the cycles of `M` with their types, and the
  cut edges of `M` between two nonempty sets of taxa; it is an LSA network when no cycle of `M`
  induces a cycle of size one (`isLSANetwork_of_target_ne`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-- The hypotheses under which suppressing the nodes of indegree one and outdegree one of `M`, and
contracting the arc at a root of outdegree one, gives a binary metric level-1 network with the same
cycles. -/
structure IsReducible [Fintype E] (M : RootedNetwork V E X) (θ : MetricData E) : Prop where
  phylo : M.IsPhylogenetic
  deg : ∀ v, v ≠ M.root → M.graph.outdegree v ≠ 0 → ¬ M.IsChainVertex v →
    M.graph.indegree v + M.graph.outdegree v = 3
  root : M.graph.outdegree M.root = 1 ∨ M.graph.outdegree M.root = 2
  levelOne : IsLevelOne M.graph
  chain : ∀ D, IsCycle M.graph D → ∀ w ∈ cycleNodes M.graph D, ¬ M.IsChainVertex w
  child : M.graph.outdegree M.root = 1 → ∀ e, M.graph.source e = M.root → ∀ D, IsCycle M.graph D →
    chainEnd phylo (M.graph.target e) ∉ cycleNodes M.graph D
  metric : M.IsMetric θ
  length : ∀ e, 0 < θ.length e
  two : ∃ x y : X, x ≠ y

variable [Fintype V] [Fintype E]

/-- **The binary network of `M`**: its nodes of indegree one and outdegree one suppressed, the arc at
a root of outdegree one contracted, and its nodes and arcs renamed by `Fin`. -/
def reduceNet (M : RootedNetwork V E X) (hM : M.IsPhylogenetic) :=
  finContract (M.suppress hM) (suppress_isPhylogenetic hM)

/-- The parameters of `reduceNet M hM`: along a chain, lengths add, and the inheritance is that of
the last arc. -/
def reduceMetric (M : RootedNetwork V E X) (hM : M.IsPhylogenetic) (θ : MetricData E) :=
  finContractMetric (M.suppress hM) (M.suppressMetric θ)

/-- The arcs of `reduceNet M hM`. -/
abbrev ReduceArc (M : RootedNetwork V E X) (hM : M.IsPhylogenetic) :=
  FinContractArc (M.suppress hM)

/-- The arcs of `M` on the chain of an arc of `reduceNet M hM`. -/
def reduceChain (M : RootedNetwork V E X) (hM : M.IsPhylogenetic) (e : ReduceArc M hM) : Finset E :=
  univ.filter fun f => M.IsOnChain (finContractArc (M.suppress hM) e).1 f

/-- The last arc of `M` on the chain of an arc of `reduceNet M hM`. -/
def reduceLastArc (M : RootedNetwork V E X) (hM : M.IsPhylogenetic) (e : ReduceArc M hM) : E :=
  NMSC.lastArc hM (finContractArc (M.suppress hM) e).1

section Chain

variable {M : RootedNetwork V E X} (hM : M.IsPhylogenetic)

omit [Fintype V] in
/-- **The length of an arc of `reduceNet M hM` is the total length of its chain of arcs of `M`.** -/
theorem reduceMetric_length (θ : MetricData E) (e : ReduceArc M hM) :
    (reduceMetric M hM θ).length e = ∑ f ∈ reduceChain M hM e, θ.length f := rfl

omit [Fintype V] in
theorem mem_reduceChain_self (e : ReduceArc M hM) :
    (finContractArc (M.suppress hM) e).1 ∈ reduceChain M hM e :=
  mem_filter.2 ⟨mem_univ _, Or.inl rfl⟩

/-- **The chains of distinct arcs of `reduceNet M hM` are disjoint.** -/
theorem disjoint_reduceChain {e e' : ReduceArc M hM} (hne : e ≠ e') :
    Disjoint (reduceChain M hM e) (reduceChain M hM e') := by
  refine Finset.disjoint_left.2 fun f hf hf' => hne ?_
  have h := IsOnChain.unique (mem_filter.1 hf).2 (mem_filter.1 hf').2
    (finContractArc _ e).2 (finContractArc _ e').2
  exact (isContraction_finContract _ (suppress_isPhylogenetic hM)).inj_e (Subtype.ext h)

omit [Fintype V] in
theorem reduceLastArc_mem (e : ReduceArc M hM) : reduceLastArc M hM e ∈ reduceChain M hM e :=
  mem_filter.2 ⟨mem_univ _, NMSC.isOnChain_lastArc _ _⟩

omit [Fintype V] in
/-- **The inheritance of an arc of `reduceNet M hM` is that of the last arc of its chain.** -/
theorem reduceMetric_inheritance {θ : MetricData E} (hθ : M.IsNormalized θ) (e : ReduceArc M hM) :
    (reduceMetric M hM θ).inheritance e = θ.inheritance (reduceLastArc M hM e) :=
  NMSC.suppressMetric_inheritance_eq_lastArc hM hθ _

/-- **An arc of `reduceNet M hM` is a hybrid arc exactly when the last arc of its chain is one.** -/
theorem isHybridArc_reduceNet_iff (htwo : ∃ x y : X, x ≠ y) (e : ReduceArc M hM) :
    (reduceNet M hM).IsHybridArc e ↔ M.IsHybridArc (reduceLastArc M hM e) := by
  have hS := suppress_isPhylogenetic hM
  have hK := isContraction_finContract (M.suppress hM) hS
  refine (hK.isHybridArc_iff (hK.isPhylogenetic hS htwo) e).trans ?_
  unfold IsHybridArc
  rw [suppress_indegree]
  change 2 ≤ M.graph.indegree (chainEnd hM _) ↔ _
  rw [← NMSC.target_lastArc hM]
  rfl

end Chain

namespace IsReducible

variable {M : RootedNetwork V E X} {θ : MetricData E} (hM : IsReducible M θ)
include hM

theorem isContraction :
    IsContraction (M.suppress hM.phylo) (reduceNet M hM.phylo)
      (finContractVertex (M.suppress hM.phylo)) (finContractArc (M.suppress hM.phylo)) :=
  isContraction_finContract _ _

/-- **The binary network of `M` is a binary rooted network.** -/
theorem isBinaryRootedNetwork : IsBinaryRootedNetwork (reduceNet M hM.phylo) := by
  have hS := suppress_isPhylogenetic hM.phylo
  have hK := hM.isContraction
  have hroot : (M.suppress hM.phylo).graph.outdegree (M.suppress hM.phylo).root =
      M.graph.outdegree M.root := suppress_outdegree hM.phylo _
  refine ⟨hK.isPhylogenetic hS hM.two, hK.isBinary hS hM.two (fun v hv h0 => ?_) (hroot ▸ hM.root)⟩
  rw [suppress_outdegree] at h0
  rw [suppress_indegree, suppress_outdegree]
  exact hM.deg v.1 (fun h => hv (Subtype.ext h)) h0 v.2

/-- **The binary network of `M` is level-1.** -/
theorem isLevelOne : IsLevelOne (reduceNet M hM.phylo).graph :=
  hM.isContraction.isLevelOne (suppress_isLevelOne hM.phylo hM.levelOne)

/-- **Its parameters are a metric.** -/
theorem isMetricNetwork :
    IsMetricNetwork (reduceNet M hM.phylo) (reduceMetric M hM.phylo θ) := by
  have hS := suppress_isPhylogenetic hM.phylo
  refine ⟨hM.isContraction.isMetric hS hM.two (isMetric_suppressMetric hM.phylo hM.metric),
    fun e => ?_⟩
  change 0 < ∑ f with M.IsOnChain (finContractArc (M.suppress hM.phylo) e).1 f, θ.length f
  exact Finset.sum_pos (fun f _ => hM.length f)
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩⟩

variable [Fintype X]

/-- **The binary network of `M` has the concordance factors of `M`.** -/
theorem cf_eq : cf (reduceNet M hM.phylo) (reduceMetric M hM.phylo θ) = cf M θ := by
  have hS := suppress_isPhylogenetic hM.phylo
  have hK := hM.isContraction
  funext q
  have hθ : ∀ a, (M.suppress hM.phylo).graph.source a = (M.suppress hM.phylo).root →
      (M.suppress hM.phylo).graph.outdegree (M.suppress hM.phylo).root = 1 →
      (M.suppress hM.phylo).IsTreeArc a := by
    intro a ha h1
    obtain ⟨b, hb, hb'⟩ := hK.root_one h1
    obtain ⟨e₀, he₀⟩ := ((M.suppress hM.phylo).graph.outdegree_eq_one_iff _).mp h1
    have hab : a = b := ((he₀ a).mp ha).trans ((he₀ b).mp hb).symm
    subst hab
    unfold IsTreeArc
    rw [hb']
    refine ((M.suppress hM.phylo).graph.indegree_eq_one_iff _).2 ⟨a, fun f => ⟨fun hf => ?_,
      fun h => h ▸ hb'⟩⟩
    exact ((he₀ f).mp (hK.eq_of_target_eq_root hS h1 hf)).trans ((he₀ a).mp ha).symm
  exact (hK.nmscCF_eq hS hM.two _ (fun a ha h1 =>
    (isMetric_suppressMetric hM.phylo hM.metric).2.2.1 a (hθ a ha h1)) le_rfl q).trans
    (NMSC.nmscCF_suppress hM.phylo hM.metric.isNormalized le_rfl q)

/-- **The cycles of the binary network of `M` are those of `M`, with their types.** -/
theorem exists_inducesCycleType_iff (n k : ℕ) (D : Set X) :
    (∃ C v, InducesCycleType (reduceNet M hM.phylo) C v n k ∧
        {x | (reduceNet M hM.phylo).graph.Reaches v ((reduceNet M hM.phylo).leaf x)} = D) ↔
      ∃ C v, InducesCycleType M C v n k ∧ {x | M.graph.Reaches v (M.leaf x)} = D := by
  have hS := suppress_isPhylogenetic hM.phylo
  have hK := hM.isContraction
  set S := M.suppress hM.phylo
  -- the child of a root of outdegree one is on no cycle
  have hchild : S.graph.outdegree S.root = 1 → ∀ D, IsCycle S.graph D →
      finContractVertex S (reduceNet M hM.phylo).root ∉ cycleNodes S.graph D := by
    intro h1 D hD hmem
    obtain ⟨b, hb, hb'⟩ := hK.root_one h1
    have h1' : M.graph.outdegree M.root = 1 := (suppress_outdegree hM.phylo _).symm.trans h1
    have hv := (suppress_cycleNodes_image hM.phylo hM.chain hD) ▸
      (Set.mem_image_of_mem Subtype.val hmem)
    rw [← hb'] at hv
    exact hM.child h1' b.1 (congrArg Subtype.val hb) _
      (suppress_isCycle_image hM.phylo hM.chain hD).1 hv
  have hbelowK : ∀ v, {x | (reduceNet M hM.phylo).graph.Reaches v ((reduceNet M hM.phylo).leaf x)} =
      {x | S.graph.Reaches (finContractVertex S v) (S.leaf x)} := fun v => by
    ext x
    simp only [Set.mem_ofPred_eq, hK.reaches_iff, hK.leaf]
    exact Iff.rfl
  have hbelowS : ∀ v : {v // ¬ M.IsChainVertex v},
      {x | S.graph.Reaches v (S.leaf x)} = {x | M.graph.Reaches v.1 (M.leaf x)} := fun v => by
    ext x
    exact suppress_reaches_iff hM.phylo v _
  constructor
  · rintro ⟨C, v, hC, rfl⟩
    have hC' := (hK.inducesCycleType_iff hS hchild).1 hC
    refine ⟨_, _, (suppress_inducesCycleType_iff hM.phylo hM.chain).1 hC', ?_⟩
    rw [hbelowK, hbelowS]
  · rintro ⟨C, v, hC, rfl⟩
    obtain ⟨C', hC', rfl⟩ := exists_suppress_isCycle hM.phylo hM.chain hC.1
    have hvS : v ∈ Subtype.val '' cycleNodes S.graph C' := by
      rw [← suppress_cycleNodes_image hM.phylo hM.chain hC']
      exact hC.2.1
    obtain ⟨w, -, rfl⟩ := hvS
    have hw := (suppress_inducesCycleType_iff hM.phylo hM.chain).2 hC
    obtain ⟨C'', hC'', rfl⟩ := hK.exists_eq_image hS hC'
    have hwK : w ∈ cycleNodes S.graph (finContractArc S '' C'') := hw.2.1
    rw [hK.cycleNodes_image] at hwK
    obtain ⟨c, -, rfl⟩ := hwK
    refine ⟨C'', c, (hK.inducesCycleType_iff hS hchild).2 hw, ?_⟩
    rw [hbelowK, hbelowS]

omit [Fintype X] in
/-- The binary network of `M` has as many cycles as `M`. -/
theorem ncard_setOf_isCycle :
    {C | IsCycle (reduceNet M hM.phylo).graph C}.ncard = {C | IsCycle M.graph C}.ncard :=
  (hM.isContraction.ncard_setOf_isCycle (suppress_isPhylogenetic hM.phylo)).trans
    (ncard_setOf_isCycle_suppress hM.phylo hM.chain)

omit [Fintype X] in
/-- **The binary network of `M` has the cut edges of `M` between two nonempty sets of taxa.** -/
theorem hasCutSplit_iff {A : Set X} (hA : ∃ x, x ∈ A) (hA' : ∃ x, x ∉ A) :
    (reduceNet M hM.phylo).HasCutSplit A ↔ M.HasCutSplit A :=
  (hM.isContraction.hasCutSplit_iff (suppress_isPhylogenetic hM.phylo) hA hA').trans
    (suppress_hasCutSplit_iff hM.phylo A)

/-- **The binary network of `M` is an LSA network** when no cycle of `M` induces a cycle of size one:
two root arcs with the same target would form a cycle of size two through the root. -/
theorem isLSANetwork (hno : ∀ C v k, ¬ InducesCycleType M C v 1 k) :
    (reduceNet M hM.phylo).IsLSANetwork := by
  set Q := reduceNet M hM.phylo
  have hQ := hM.isBinaryRootedNetwork
  refine isLSANetwork_of_target_ne hQ hM.isLevelOne fun a₁ a₂ hne ha₁ ha₂ ht => ?_
  -- the cycle `{a₁, a₂}`
  obtain ⟨D, hD, ha₁D, hDsub⟩ := exists_isCycle_of_walks (G := Q.graph) (e := a₁) (F := {a₂})
    (fun h => hne (Set.mem_singleton_iff.1 h))
    (.single ⟨a₂, rfl, Or.inr ⟨ha₂.trans ha₁.symm, ht.symm⟩⟩)
  have hloop : ∀ f, Q.graph.source f ≠ Q.graph.target f := fun f h =>
    hQ.1.acyclic _ (.single ⟨f, rfl, h.symm⟩)
  have hrD : Q.root ∈ cycleNodes Q.graph D := ha₁ ▸ source_mem_cycleNodes ha₁D
  have ha₂D : a₂ ∈ D := by
    obtain ⟨f₁, hf₁, f₂, hf₂, hf, -, -⟩ := hD.exists_ne_of_mem (fun f _ => hloop f) hrD
    rcases hDsub hf₁ with rfl | h₁ <;> rcases hDsub hf₂ with rfl | h₂
    · exact absurd rfl hf
    · rwa [Set.mem_singleton_iff.1 h₂] at hf₂
    · rwa [Set.mem_singleton_iff.1 h₁] at hf₁
    · rwa [Set.mem_singleton_iff.1 h₁] at hf₁
  have hDeq : D = {a₁, a₂} := by
    refine Set.Subset.antisymm (fun f hf => ?_) (Set.insert_subset ha₁D
      (Set.singleton_subset_iff.2 ha₂D))
    rcases hDsub hf with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h
  have hin : Q.graph.indegree (Q.graph.target a₁) = 2 := by
    refine le_antisymm (hQ.indegree_le_two _) ?_
    have := hQ.1.finite_arcs
    rw [← Set.ncard_pair hne]
    exact Set.ncard_le_ncard (fun f hf => by
      rcases hf with rfl | hf
      · rfl
      · rw [Set.mem_singleton_iff.1 hf]; exact ht.symm) (Set.toFinite _)
  have hC : InducesCycleType Q D (Q.graph.target a₁) 1
      {x | Q.graph.Reaches (Q.graph.target a₁) (Q.leaf x)}.ncard := by
    refine ⟨hD, target_mem_cycleNodes ha₁D, hin, ?_, rfl⟩
    rw [ite_eq_left hrD, hDeq, Set.ncard_pair hne]
  obtain ⟨C, v, hC', -⟩ := (hM.exists_inducesCycleType_iff 1 _ _).1 ⟨D, _, hC, rfl⟩
  exact hno C v _ hC'

end IsReducible

end Banos2019
