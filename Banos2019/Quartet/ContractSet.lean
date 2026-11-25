module

public import Banos2019.Quartet.Reduce
public import Banos2019.Quartet.CutSplits

/-!
# Contracting several cycles (`Q₀⊕`, `Q̃⊕`, and the tree of Proposition 6)

`contractRooted Q P` contracts the cycles of `Q` satisfying `P`. In a binary level-1 network distinct
cycles have no common node (Lemma 3), so each node of the contracted network is a single node of `Q`
off these cycles or the nodes of one of them, represented by its top (`contractSetRep`).

* `contractSet_mk_eq_mk_iff`, `contractSetRep`: the nodes of the contracted network.
* `contractSet_isPhylogenetic`, `contractSet_isMetric`, `contractSet_indegree`,
  `contractSet_outdegree_of_not`, `contractSet_outdegree_of_mem`: it is a metric phylogenetic network;
  the node of a cycle `C` has indegree one (or zero, for the root) and outdegree `|C| - 1`.
* `contractSet_isCycle_image`, `contractSet_exists_isCycle`, `contractSet_exists_inducesCycleType_iff`:
  its cycles are the cycles of `Q` not satisfying `P`, with their types. A cycle of the contracted
  network gives a closed walk of `Q` through the contracted cycles it passes; it closes a cycle of `Q`
  through any of its edges, which meets no contracted cycle (level-1).
* `contractSet_hasCutSplit_iff`: it has the cut edges of `Q`: a cut edge is on no cycle, and every
  cycle is on one side of it.
* `isReducible_contractSet`: when every contracted cycle induces a 2-cycle, it satisfies
  `IsReducible`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} {Q : RootedNetwork V E X}

/-- The top of a cycle `C`: a node of `C` above its other nodes that receives every arc entering
`C` off `C` (`IsContractible`). -/
def cycleTop (Q : RootedNetwork V E X) (C : Set E) : V :=
  @Classical.epsilon V ⟨Q.root⟩ (IsContractible Q C)

theorem isContractible_cycleTop [Fintype V] [Fintype E] (hQ : IsBinaryRootedNetwork Q)
    (h1 : IsLevelOne Q.graph) {C : Set E} (hC : IsCycle Q.graph C) :
    IsContractible Q C (cycleTop Q C) := by
  have := hQ.1.finite_arcs
  obtain ⟨⟨v, ⟨hv, h2⟩, -⟩, -, -⟩ := lemma3 hQ h1 hC
  exact @Classical.epsilon_spec V (IsContractible Q C) (isContractible_of_cycle hQ h1 hC hv h2)

/-- The top of a cycle through the root is the root. -/
theorem cycleTop_eq_root [Fintype V] [Fintype E] (hQ : IsBinaryRootedNetwork Q)
    (h1 : IsLevelOne Q.graph) {C : Set E} (hC : IsCycle Q.graph C)
    (hr : Q.root ∈ cycleNodes Q.graph C) : cycleTop Q C = Q.root := by
  have hK := isContractible_cycleTop hQ h1 hC
  have := hQ.1.finite_arcs
  by_contra hne
  obtain ⟨e, -, he⟩ := exists_arc_enter (p := fun w => w = Q.root) (hK.top_reaches _ hr) hne rfl
  exact (Q.graph.indegree_eq_zero_iff _).1 hQ.1.root_indegree e he

variable {P : Set E → Prop}

/-- A node of `Q` on a cycle satisfying `P`. -/
def InPCycle (Q : RootedNetwork V E X) (P : Set E → Prop) (w : V) : Prop :=
  ∃ C, IsCycle Q.graph C ∧ P C ∧ w ∈ cycleNodes Q.graph C

section Set

variable [Fintype V] [Fintype E] (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
include hQ h1

omit [Fintype V] in
/-- Two cycles with a common node are the same (Lemma 3). -/
theorem eq_of_mem_cycleNodes {C C' : Set E} (hC : IsCycle Q.graph C) (hC' : IsCycle Q.graph C')
    {w : V} (hw : w ∈ cycleNodes Q.graph C) (hw' : w ∈ cycleNodes Q.graph C') : C = C' :=
  (lemma3 hQ h1 hC).2.2 C' hC' ⟨w, hw, hw'⟩

omit [Fintype V] in
/-- **The nodes identified by contracting the cycles satisfying `P`**: equal nodes, or two nodes of
one of these cycles. -/
theorem contractSet_mk_eq_mk_iff {a b : V} :
    (Quot.mk (RootedContractRel Q P) a = Quot.mk _ b) ↔ a = b ∨ RootedContractRel Q P a b := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel x y hxy => exact Or.inr hxy
    | refl => exact Or.inl rfl
    | symm x y _ ih =>
      rcases ih with rfl | ⟨C, hC, hP, hx, hy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨C, hC, hP, hy, hx⟩
    | trans x y z _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨C, hC, hP, hx, hy⟩
      · exact ih₂
      · rcases ih₂ with rfl | ⟨C', hC', hP', hy', hz⟩
        · exact Or.inr ⟨C, hC, hP, hx, hy⟩
        · have := eq_of_mem_cycleNodes hQ h1 hC hC' hy hy'
          subst this
          exact Or.inr ⟨C, hC, hP, hx, hz⟩
  · rintro (rfl | h)
    · rfl
    · exact Quot.sound h

omit [Fintype V] in
theorem contractSet_mk_eq_mk_iff_of_not {a b : V} (ha : ¬ InPCycle Q P a) :
    (Quot.mk (RootedContractRel Q P) a = Quot.mk _ b) ↔ a = b := by
  rw [contractSet_mk_eq_mk_iff hQ h1]
  exact ⟨fun h => h.resolve_right (fun hr => by
    obtain ⟨C, hC, hP, hx, -⟩ := hr
    exact ha ⟨C, hC, hP, hx⟩), Or.inl⟩

/-- The representative of a node of the contracted network: the node itself off the contracted
cycles, the top of its cycle on one. -/
def contractSetRep : Quot (RootedContractRel Q P) → V :=
  Quot.lift (fun w => if h : InPCycle Q P w then cycleTop Q (Classical.choose h) else w)
    fun a b ⟨C, hC, hP, ha, hb⟩ => by
      have hA : InPCycle Q P a := ⟨C, hC, hP, ha⟩
      have hB : InPCycle Q P b := ⟨C, hC, hP, hb⟩
      simp only [hA, hB, ↓reduceDIte]
      obtain ⟨hCa, -, ha'⟩ := Classical.choose_spec hA
      obtain ⟨hCb, -, hb'⟩ := Classical.choose_spec hB
      rw [eq_of_mem_cycleNodes hQ h1 hCa hC ha' ha, eq_of_mem_cycleNodes hQ h1 hCb hC hb' hb]

omit [Fintype V] in
theorem contractSetRep_mk_of_not {w : V} (hw : ¬ InPCycle Q P w) :
    contractSetRep hQ h1 (Quot.mk (RootedContractRel Q P) w) = w := by
  simp [contractSetRep, hw]

omit [Fintype V] in
theorem contractSetRep_mk_of_mem {C : Set E} (hC : IsCycle Q.graph C) (hP : P C) {w : V}
    (hw : w ∈ cycleNodes Q.graph C) :
    contractSetRep hQ h1 (Quot.mk (RootedContractRel Q P) w) = cycleTop Q C := by
  have hW : InPCycle Q P w := ⟨C, hC, hP, hw⟩
  simp only [contractSetRep, hW, ↓reduceDIte]
  obtain ⟨hC', -, hw'⟩ := Classical.choose_spec hW
  rw [eq_of_mem_cycleNodes hQ h1 hC' hC hw' hw]

theorem contractSet_mk_rep (W : Quot (RootedContractRel Q P)) :
    Quot.mk _ (contractSetRep hQ h1 W) = W := by
  induction W using Quot.ind with
  | mk w =>
    by_cases hw : InPCycle Q P w
    · obtain ⟨C, hC, hP, hwC⟩ := hw
      rw [contractSetRep_mk_of_mem hQ h1 hC hP hwC]
      exact Quot.sound ⟨C, hC, hP, (isContractible_cycleTop hQ h1 hC).top_mem, hwC⟩
    · rw [contractSetRep_mk_of_not hQ h1 hw]

theorem contractSetRep_injective : Function.Injective (contractSetRep (P := P) hQ h1) :=
  fun W W' h => by rw [← contractSet_mk_rep hQ h1 W, h, contractSet_mk_rep hQ h1 W']

/-- **The target of an arc of the contracted network is represented by the target of the arc.** -/
theorem contractSetRep_target (e : {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C}) :
    contractSetRep hQ h1 ((contractRooted Q P).graph.target e) = Q.graph.target e.1 := by
  change contractSetRep hQ h1 (Quot.mk _ (Q.graph.target e.1)) = _
  by_cases h : InPCycle Q P (Q.graph.target e.1)
  · obtain ⟨C, hC, hP, hw⟩ := h
    rw [contractSetRep_mk_of_mem hQ h1 hC hP hw,
      (isContractible_cycleTop hQ h1 hC).entry e.1 (e.2 C hC hP) hw]
  · rw [contractSetRep_mk_of_not hQ h1 h]

theorem contractSet_target_eq_iff (e : {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C})
    (W : Quot (RootedContractRel Q P)) :
    (contractRooted Q P).graph.target e = W ↔ Q.graph.target e.1 = contractSetRep hQ h1 W := by
  constructor
  · rintro rfl
    exact (contractSetRep_target hQ h1 e).symm
  · intro h
    rw [← contractSet_mk_rep hQ h1 W, ← h]
    rfl

/-- An arc of `Q` into a representative is off the contracted cycles. -/
theorem notMem_of_target_eq_contractSetRep {e : E} {W : Quot (RootedContractRel Q P)}
    (h : Q.graph.target e = contractSetRep hQ h1 W) :
    ∀ C, IsCycle Q.graph C → P C → e ∉ C := by
  induction W using Quot.ind with
  | mk w =>
    intro C' hC' hP' heC'
    by_cases hw : InPCycle Q P w
    · obtain ⟨C, hC, hP, hwC⟩ := hw
      rw [contractSetRep_mk_of_mem hQ h1 hC hP hwC] at h
      have hK := isContractible_cycleTop hQ h1 hC
      have hCC' := eq_of_mem_cycleNodes hQ h1 hC hC' (h ▸ hK.top_mem) (target_mem_cycleNodes heC')
      subst hCC'
      exact hK.top_entry e h heC'
    · rw [contractSetRep_mk_of_not hQ h1 hw] at h
      exact hw ⟨C', hC', hP', h ▸ target_mem_cycleNodes heC'⟩

/-- **The indegree of a node of the contracted network is that of its representative.** -/
theorem contractSet_indegree (W : Quot (RootedContractRel Q P)) :
    (contractRooted Q P).graph.indegree W = Q.graph.indegree (contractSetRep hQ h1 W) := by
  unfold DirectedMultigraph.indegree
  refine Set.ncard_congr (fun e _ => e.1) (fun e he => (contractSet_target_eq_iff hQ h1 e W).1 he)
    (fun a b _ _ h => Subtype.ext h) fun e he => ?_
  exact ⟨⟨e, notMem_of_target_eq_contractSetRep hQ h1 he⟩,
    (contractSet_target_eq_iff hQ h1 _ W).2 he, rfl⟩

/-- An arc of the contracted network goes down in `Q` between the representatives. -/
theorem contractSet_transGen_rep_of_adj {W W' : Quot (RootedContractRel Q P)}
    (h : (contractRooted Q P).graph.Adj W W') :
    Relation.TransGen Q.graph.Adj (contractSetRep hQ h1 W) (contractSetRep hQ h1 W') := by
  obtain ⟨e, rfl, rfl⟩ := h
  rw [contractSetRep_target]
  change Relation.TransGen Q.graph.Adj (contractSetRep hQ h1 (Quot.mk _ (Q.graph.source e.1))) _
  by_cases hs : InPCycle Q P (Q.graph.source e.1)
  · obtain ⟨C, hC, hP, hsC⟩ := hs
    rw [contractSetRep_mk_of_mem hQ h1 hC hP hsC]
    exact Relation.TransGen.tail' ((isContractible_cycleTop hQ h1 hC).top_reaches _ hsC)
      ⟨e.1, rfl, rfl⟩
  · rw [contractSetRep_mk_of_not hQ h1 hs]
    exact .single ⟨e.1, rfl, rfl⟩

/-- A path of the contracted network gives a path of `Q` between the representatives. -/
theorem contractSet_reaches_rep {W W' : Quot (RootedContractRel Q P)}
    (h : (contractRooted Q P).graph.Reaches W W') :
    Q.graph.Reaches (contractSetRep hQ h1 W) (contractSetRep hQ h1 W') := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact ih.trans (contractSet_transGen_rep_of_adj hQ h1 hab).to_reflTransGen

omit hQ h1 [Fintype V] [Fintype E] in
/-- A path of `Q` is a path of the contracted network. -/
theorem contractSet_reaches_mk {a b : V} (h : Q.graph.Reaches a b) :
    (contractRooted Q P).graph.Reaches (Quot.mk _ a) (Quot.mk _ b) := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨e, rfl, rfl⟩ := hbc
    by_cases he : ∀ C, IsCycle Q.graph C → P C → e ∉ C
    · exact ih.tail ⟨⟨e, he⟩, rfl, rfl⟩
    · push Not at he
      obtain ⟨C, hC, hP, heC⟩ := he
      have : Quot.mk (RootedContractRel Q P) (Q.graph.source e) = Quot.mk _ (Q.graph.target e) :=
        Quot.sound ⟨C, hC, hP, source_mem_cycleNodes heC, target_mem_cycleNodes heC⟩
      rwa [← this]

/-- **A path of the contracted network is a path of `Q` between the representatives.** -/
theorem contractSet_reaches_iff (W W' : Quot (RootedContractRel Q P)) :
    (contractRooted Q P).graph.Reaches W W' ↔
      Q.graph.Reaches (contractSetRep hQ h1 W) (contractSetRep hQ h1 W') := by
  refine ⟨contractSet_reaches_rep hQ h1, fun h => ?_⟩
  rw [← contractSet_mk_rep hQ h1 W, ← contractSet_mk_rep hQ h1 W']
  exact contractSet_reaches_mk h

/-- A taxon is on no cycle. -/
theorem leaf_not_inPCycle (x : X) : ¬ InPCycle Q P (Q.leaf x) := fun ⟨_, hC, _, hx⟩ =>
  (isContractible_cycleTop hQ h1 hC).leaf_notMem x hx

/-- The representative of the root of the contracted network is the root. -/
theorem contractSetRep_root :
    contractSetRep hQ h1 (contractRooted Q P).root = Q.root := by
  change contractSetRep hQ h1 (Quot.mk _ Q.root) = Q.root
  by_cases hr : InPCycle Q P Q.root
  · obtain ⟨C, hC, hP, hrC⟩ := hr
    rw [contractSetRep_mk_of_mem hQ h1 hC hP hrC, cycleTop_eq_root hQ h1 hC hrC]
  · exact contractSetRep_mk_of_not hQ h1 hr

theorem contractSetRep_leaf (x : X) :
    contractSetRep hQ h1 ((contractRooted Q P).leaf x) = Q.leaf x :=
  contractSetRep_mk_of_not hQ h1 (leaf_not_inPCycle hQ h1 x)

/-- **The contracted network is a phylogenetic network.** -/
theorem contractSet_isPhylogenetic : (contractRooted Q P).IsPhylogenetic := by
  have hQ' := hQ.1
  refine
    { finite_vertices := inferInstance
      finite_arcs := inferInstance
      finite_taxa := hQ'.finite_taxa
      acyclic := fun W hW => ?_
      root_reaches := fun W => ?_
      root_indegree := ?_
      nonroot_indegree := fun W hW => ?_
      leaf_injective := fun x y h => ?_
      leaf_indegree := fun x => ?_
      leaves := fun W => ?_ }
  · have hl : ∀ A B, Relation.TransGen (contractRooted Q P).graph.Adj A B →
        Relation.TransGen Q.graph.Adj (contractSetRep hQ h1 A) (contractSetRep hQ h1 B) := by
      intro A B h
      induction h with
      | single h => exact contractSet_transGen_rep_of_adj hQ h1 h
      | tail _ h ih => exact ih.trans (contractSet_transGen_rep_of_adj hQ h1 h)
    exact hQ'.acyclic _ (hl W W hW)
  · rw [contractSet_reaches_iff hQ h1, contractSetRep_root]
    exact hQ'.root_reaches _
  · rw [contractSet_indegree hQ h1, contractSetRep_root]
    exact hQ'.root_indegree
  · rw [contractSet_indegree hQ h1]
    refine hQ'.nonroot_indegree _ fun h => hW ?_
    rw [← contractSet_mk_rep hQ h1 W, h]
    rfl
  · exact hQ'.leaf_injective ((contractSet_mk_eq_mk_iff_of_not hQ h1
      (leaf_not_inPCycle hQ h1 x)).1 h)
  · rw [contractSet_indegree hQ h1, contractSetRep_leaf]
    exact hQ'.leaf_indegree x
  · rw [(contractRooted Q P).graph.outdegree_eq_zero_iff]
    induction W using Quot.ind with
    | mk w =>
      by_cases hw : InPCycle Q P w
      · obtain ⟨C, hC, hP, hwC⟩ := hw
        constructor
        · intro h0
          obtain ⟨e, he, hs⟩ := (isContractible_cycleTop hQ h1 hC).exit
          have he' : ∀ C', IsCycle Q.graph C' → P C' → e ∉ C' := fun C' hC' _ heC' =>
            he (eq_of_mem_cycleNodes hQ h1 hC' hC (source_mem_cycleNodes heC') hs ▸ heC')
          exact absurd (Quot.sound ⟨C, hC, hP, hs, hwC⟩) (h0 ⟨e, he'⟩)
        · rintro ⟨x, hx⟩
          have := (contractSet_mk_eq_mk_iff_of_not hQ h1 (leaf_not_inPCycle hQ h1 x)).1 hx
          exact absurd ⟨C, hC, hP, by rw [this]; exact hwC⟩ (leaf_not_inPCycle hQ h1 x)
      · have hiff : (∃ x, (contractRooted Q P).leaf x = Quot.mk _ w) ↔ ∃ x, Q.leaf x = w :=
          exists_congr fun x => contractSet_mk_eq_mk_iff_of_not hQ h1 (leaf_not_inPCycle hQ h1 x)
        rw [hiff, ← hQ'.leaves, Q.graph.outdegree_eq_zero_iff]
        constructor
        · intro h e he
          refine h ⟨e, fun C' hC' hP' heC' => hw ⟨C', hC', hP', he ▸ source_mem_cycleNodes heC'⟩⟩ ?_
          change Quot.mk _ (Q.graph.source e) = _
          rw [he]
        · intro h e he
          exact h e.1 (((contractSet_mk_eq_mk_iff hQ h1).1 he).resolve_right
            fun ⟨C, hC, hP, _, hwC⟩ => hw ⟨C, hC, hP, hwC⟩)

/-- **The parameters of the remaining edges are a metric.** -/
theorem contractSet_isMetric {θ : MetricData E} (hθ : Q.IsMetric θ) :
    (contractRooted Q P).IsMetric (contractMetric Q P θ) := by
  have htree : ∀ e : {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C},
      (contractRooted Q P).IsTreeArc e ↔ Q.IsTreeArc e.1 := by
    intro e
    unfold RootedNetwork.IsTreeArc
    rw [contractSet_indegree hQ h1, contractSetRep_target]
  have hhyb : ∀ e : {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C},
      (contractRooted Q P).IsHybridArc e ↔ Q.IsHybridArc e.1 := by
    intro e
    unfold RootedNetwork.IsHybridArc
    rw [contractSet_indegree hQ h1, contractSetRep_target]
  refine ⟨fun e he => hθ.1 e.1 ((htree e).1 he), fun e he => hθ.2.1 e.1 ((hhyb e).1 he),
    fun e he => hθ.2.2.1 e.1 ((htree e).1 he), fun e he => hθ.2.2.2.1 e.1 ((hhyb e).1 he),
    fun W hW => ?_⟩
  rw [contractSet_indegree hQ h1] at hW
  rw [← hθ.2.2.2.2 _ hW, ← sum_filter, ← sum_filter]
  refine sum_bij (fun e _ => e.1) (fun e he => ?_) (fun a _ b _ h => Subtype.ext h)
    (fun e he => ?_) fun e _ => rfl
  · exact mem_filter.2 ⟨mem_univ _, (contractSet_target_eq_iff hQ h1 e W).1 (mem_filter.1 he).2⟩
  · exact ⟨⟨e, notMem_of_target_eq_contractSetRep hQ h1 (mem_filter.1 he).2⟩,
      mem_filter.2 ⟨mem_univ _, (contractSet_target_eq_iff hQ h1 _ W).2 (mem_filter.1 he).2⟩, rfl⟩

omit [Fintype V] in
theorem contractSet_mk_eq_mk_iff_of_not' {a b : V} (hb : ¬ InPCycle Q P b) :
    (Quot.mk (RootedContractRel Q P) a = Quot.mk _ b) ↔ a = b := by
  rw [contractSet_mk_eq_mk_iff hQ h1]
  exact ⟨fun h => h.resolve_right (fun hr => by
    obtain ⟨C, hC, hP, -, hx⟩ := hr
    exact hb ⟨C, hC, hP, hx⟩), Or.inl⟩

omit [Fintype V] in
/-- The nodes of a cycle not contracted are on no contracted cycle. -/
theorem not_inPCycle_of_mem {D : Set E} (hD : IsCycle Q.graph D) (hP : ¬ P D) {w : V}
    (hw : w ∈ cycleNodes Q.graph D) : ¬ InPCycle Q P w := fun ⟨_, hC, hPC, hwC⟩ =>
  hP (eq_of_mem_cycleNodes hQ h1 hC hD hwC hw ▸ hPC)

omit [Fintype V] in
/-- The edges of a cycle not contracted are on no contracted cycle. -/
theorem notMem_of_mem_of_not {D : Set E} (hD : IsCycle Q.graph D) (hP : ¬ P D) {e : E}
    (he : e ∈ D) : ∀ C, IsCycle Q.graph C → P C → e ∉ C := fun C hC hPC heC =>
  not_inPCycle_of_mem hQ h1 hD hP (source_mem_cycleNodes he) ⟨C, hC, hPC, source_mem_cycleNodes heC⟩

omit [Fintype V] in
/-- **The outdegree of a node off the contracted cycles is that in `Q`.** -/
theorem contractSet_outdegree_of_not {w : V} (hw : ¬ InPCycle Q P w) :
    (contractRooted Q P).graph.outdegree (Quot.mk _ w) = Q.graph.outdegree w := by
  unfold DirectedMultigraph.outdegree
  refine Set.ncard_congr (fun e _ => e.1) (fun e he =>
    (contractSet_mk_eq_mk_iff_of_not' hQ h1 hw).1 he) (fun a b _ _ h => Subtype.ext h)
    fun e he => ?_
  refine ⟨⟨e, fun C hC hP heC => hw ⟨C, hC, hP, he ▸ source_mem_cycleNodes heC⟩⟩, ?_, rfl⟩
  change Quot.mk _ (Q.graph.source e) = _
  rw [show Q.graph.source e = w from he]

/-- **The node of a contracted cycle `C` has outdegree `|C| - 1`**: one arc leaves `C` from each of
its nodes other than its top. -/
theorem contractSet_outdegree_of_mem {C : Set E} (hC : IsCycle Q.graph C) (hP : P C) {w : V}
    (hw : w ∈ cycleNodes Q.graph C) :
    (contractRooted Q P).graph.outdegree (Quot.mk _ w) = C.ncard - 1 := by
  have := hQ.1.finite_arcs
  have hK := isContractible_cycleTop hQ h1 hC
  set t := cycleTop Q C
  have hloop : ∀ f, Q.graph.source f ≠ Q.graph.target f := fun f h =>
    hQ.1.acyclic _ (.single ⟨f, rfl, h.symm⟩)
  -- the arcs out of the node of `C` are the arcs leaving `C`
  have h₁ : (contractRooted Q P).graph.outdegree (Quot.mk _ w) =
      {e | e ∉ C ∧ Q.graph.source e ∈ cycleNodes Q.graph C}.ncard := by
    unfold DirectedMultigraph.outdegree
    refine Set.ncard_congr (fun e _ => e.1) (fun e he => ?_) (fun a b _ _ h => Subtype.ext h)
      fun e he => ?_
    · have hs : Q.graph.source e.1 ∈ cycleNodes Q.graph C := by
        rcases (contractSet_mk_eq_mk_iff hQ h1).1 he with h | ⟨C', hC', _, hs, hw'⟩
        · exact h ▸ hw
        · exact eq_of_mem_cycleNodes hQ h1 hC' hC hw' hw ▸ hs
      exact ⟨e.2 C hC hP, hs⟩
    · refine ⟨⟨e, fun C' hC' _ heC' => he.1 ?_⟩, Quot.sound ⟨C, hC, hP, he.2, hw⟩, rfl⟩
      exact eq_of_mem_cycleNodes hQ h1 hC' hC (source_mem_cycleNodes heC') he.2 ▸ heC'
  -- no arc leaves `C` from its top
  have htop : ∀ e, Q.graph.source e = t → e ∈ C := by
    intro e he
    have hinc := hC.ncard_incident hloop hK.top_mem
    have hsub : {f | f ∈ C ∧ (Q.graph.source f = t ∨ Q.graph.target f = t)} ⊆
        {f | Q.graph.source f = t} := fun f hf =>
      hf.2.resolve_right fun h => hK.top_entry f h hf.1
    have hle := hQ.outdegree_le_two t
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      change Q.graph.outdegree t ≤ _
      rw [hinc]
      exact hle) (Set.toFinite _)
    have : e ∈ {f | Q.graph.source f = t} := he
    rw [← heq] at this
    exact this.1
  have htr : ∀ u ∈ cycleNodes Q.graph C, u ≠ t → u ≠ Q.root := fun u hu hut hur =>
    hut (hur ▸ (cycleTop_eq_root hQ h1 hC (hur ▸ hu)).symm)
  rw [h₁, ← ncard_cycleNodes hC, ← Set.ncard_sdiff_singleton_of_mem hK.top_mem]
  refine Set.ncard_congr (fun e _ => Q.graph.source e) (fun e he => ⟨he.2, fun h =>
    he.1 (htop e h)⟩) (fun a b ha hb h => ?_) fun u hu => ?_
  · have hu := htr _ ha.2 (fun h' => ha.1 (htop a h'))
    obtain ⟨-, g, -, -, hguniq⟩ := exists_offCycle_edge hQ hC ha.2 hu
    exact (hguniq a ha.1 (Or.inl rfl)).trans (hguniq b hb.1 (Or.inl h.symm)).symm
  · obtain ⟨-, g, hgC, hgu, -⟩ := exists_offCycle_edge hQ hC hu.1 (htr u hu.1 hu.2)
    rcases hgu with hgs | hgt
    · exact ⟨g, ⟨hgC, hgs ▸ hu.1⟩, hgs⟩
    · exact absurd (hgt ▸ hK.entry g hgC (hgt ▸ hu.1)) hu.2

/-- A walk of `Q` along a contracted cycle from the representative of a node. -/
theorem walks_contractSetRep (w : V) :
    Q.graph.Walks {e | ∃ C, IsCycle Q.graph C ∧ P C ∧ e ∈ C}
      (contractSetRep hQ h1 (Quot.mk (RootedContractRel Q P) w)) w := by
  by_cases hw : InPCycle Q P w
  · obtain ⟨C, hC, hP, hwC⟩ := hw
    rw [contractSetRep_mk_of_mem hQ h1 hC hP hwC]
    exact walks_mono (fun e (he : e ∈ C) =>
      (⟨C, hC, hP, he⟩ : ∃ C', IsCycle Q.graph C' ∧ P C' ∧ e ∈ C'))
      (hC.walks_of_mem (isContractible_cycleTop hQ h1 hC).top_mem hwC)
  · rw [contractSetRep_mk_of_not hQ h1 hw]
    exact .refl

/-- **A walk of the contracted network gives a walk of `Q` between the representatives**, on its
arcs and the edges of the contracted cycles. -/
theorem walks_of_contractSet_walks {F : Set {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C}}
    {W W' : Quot (RootedContractRel Q P)} (h : (contractRooted Q P).graph.Walks F W W') :
    Q.graph.Walks (Subtype.val '' F ∪ {e | ∃ C, IsCycle Q.graph C ∧ P C ∧ e ∈ C})
      (contractSetRep hQ h1 W) (contractSetRep hQ h1 W') := by
  have hstep : ∀ f ∈ F, Q.graph.Walks (Subtype.val '' F ∪ {e | ∃ C, IsCycle Q.graph C ∧ P C ∧ e ∈ C})
      (contractSetRep hQ h1 ((contractRooted Q P).graph.source f))
      (contractSetRep hQ h1 ((contractRooted Q P).graph.target f)) := by
    intro f hf
    rw [contractSetRep_target]
    exact (walks_mono Set.subset_union_right (walks_contractSetRep hQ h1 (Q.graph.source f.1))).tail
      ⟨f.1, Or.inl ⟨f, hf, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, hf, hl⟩ := hbc
    rcases hl with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rw [← ht]
      rw [← hs] at ih
      exact ih.trans (hstep f hf)
    · rw [← hs]
      rw [← ht] at ih
      exact ih.trans (Q.graph.walks_symm (hstep f hf))

/-- **A cycle of `Q` not contracted is a cycle of the contracted network.** -/
theorem contractSet_exists_isCycle {D : Set E} (hD : IsCycle Q.graph D) (hP : ¬ P D) :
    ∃ D', IsCycle (contractRooted Q P).graph D' ∧ Subtype.val '' D' = D := by
  have hDψ : D ⊆ Set.range (Subtype.val : {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C} → E) :=
    fun f hf => ⟨⟨f, notMem_of_mem_of_not hQ h1 hD hP hf⟩, rfl⟩
  have hrep : ∀ w ∈ cycleNodes Q.graph D,
      contractSetRep hQ h1 (Quot.mk (RootedContractRel Q P) w) = w := fun w hw =>
    contractSetRep_mk_of_not hQ h1 (not_inPCycle_of_mem hQ h1 hD hP hw)
  refine ⟨_, hD.preimage (G' := (contractRooted Q P).graph) (contractSetRep hQ h1) Subtype.val
    (contractSetRep_injective hQ h1) Subtype.val_injective hDψ (fun w hw => ⟨Quot.mk _ w, hrep w hw⟩)
    (fun e he => (hrep _ (source_mem_cycleNodes he)).symm)
    (fun e he => (hrep _ (target_mem_cycleNodes he)).symm), Set.image_preimage_eq_of_subset hDψ⟩

/-- **A cycle of the contracted network is a cycle of `Q` not contracted**, on the same edges. -/
theorem contractSet_isCycle_image {D' : Set {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C}}
    (hD' : IsCycle (contractRooted Q P).graph D') :
    IsCycle Q.graph (Subtype.val '' D') ∧ ¬ P (Subtype.val '' D') := by
  have hM := contractSet_isPhylogenetic (P := P) hQ h1
  have hloop : ∀ f, (contractRooted Q P).graph.source f ≠ (contractRooted Q P).graph.target f :=
    fun f h => hM.acyclic _ (.single ⟨f, rfl, h.symm⟩)
  obtain ⟨g, hg⟩ : D'.Nonempty := by
    obtain ⟨k, v, e, hc, rfl⟩ := hD'
    exact ⟨e ⟨0, hc.pos⟩, ⟨_, rfl⟩⟩
  -- the walk of `Q` around the cycle without `g`
  have hW := walks_of_contractSet_walks hQ h1 (hD'.walks_sdiff_singleton hg
    (target_mem_cycleNodes hg) (source_mem_cycleNodes hg))
  rw [contractSetRep_target] at hW
  have hW' := hW.trans (walks_mono Set.subset_union_right
    (walks_contractSetRep hQ h1 (Q.graph.source g.1)))
  have hgF : g.1 ∉ Subtype.val '' (D' \ {g}) ∪ {e | ∃ C, IsCycle Q.graph C ∧ P C ∧ e ∈ C} := by
    rintro (⟨f, hf, hfg⟩ | ⟨C, hC, hP, hgC⟩)
    · exact hf.2 (Subtype.ext hfg)
    · exact g.2 C hC hP hgC
  obtain ⟨D, hD, hgD, hDsub⟩ := exists_isCycle_of_walks hgF hW'
  have hPD : ¬ P D := fun hP => g.2 D hD hP hgD
  have hDsub' : D ⊆ Subtype.val '' D' := by
    intro f hf
    rcases hDsub hf with rfl | (⟨f', hf', rfl⟩ | ⟨C, hC, hP, hfC⟩)
    · exact ⟨g, hg, rfl⟩
    · exact ⟨f', hf'.1, rfl⟩
    · exact absurd (h1 D C hD hC ⟨f, hf, hfC⟩ ▸ hP) hPD
  -- the cycle `D` of the contracted network is all of `D'`
  obtain ⟨D'', hD'', hD''D⟩ := contractSet_exists_isCycle hQ h1 hD hPD
  have hsub : D'' ⊆ D' := fun f hf => by
    obtain ⟨f', hf', hff'⟩ := hDsub' (hD''D ▸ ⟨f, hf, rfl⟩ : f.1 ∈ D)
    rwa [← Subtype.ext hff']
  have hx₀ : (contractRooted Q P).graph.source g ∈ cycleNodes (contractRooted Q P).graph D'' := by
    obtain ⟨f, hf, hfg⟩ : g.1 ∈ Subtype.val '' D'' := hD''D ▸ hgD
    rw [← Subtype.ext hfg]
    exact source_mem_cycleNodes hf
  have hsup := hD''.superset_of_ncard_incident_le hloop hsub (fun x => by
    by_cases hx : x ∈ cycleNodes (contractRooted Q P).graph D'
    · exact (hD'.ncard_incident hloop hx).le
    · have : {f | f ∈ D' ∧ ((contractRooted Q P).graph.source f = x ∨
          (contractRooted Q P).graph.target f = x)} = ∅ :=
        Set.eq_empty_of_forall_notMem fun f hf => hx ⟨f, hf.1, hf.2⟩
      rw [this, Set.ncard_empty]
      omega) hx₀ (fun f hf => hD'.walks_of_mem (by
        obtain ⟨f', hf', hfx⟩ := hx₀
        exact ⟨f', hsub hf', hfx⟩) (source_mem_cycleNodes hf))
  rw [show D' = D'' from hsup.antisymm hsub, hD''D]
  exact ⟨hD, hPD⟩

/-- **The contracted network is level-1.** -/
theorem contractSet_isLevelOne : IsLevelOne (contractRooted Q P).graph := by
  intro D₁ D₂ hD₁ hD₂ ⟨f, hf₁, hf₂⟩
  exact Set.image_injective.2 Subtype.val_injective (h1 _ _ (contractSet_isCycle_image hQ h1 hD₁).1
    (contractSet_isCycle_image hQ h1 hD₂).1 ⟨f.1, ⟨f, hf₁, rfl⟩, ⟨f, hf₂, rfl⟩⟩)

/-- The nodes of a cycle of the contracted network are represented by the nodes of the cycle of
`Q`. -/
theorem contractSet_cycleNodes_image {D' : Set {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C}}
    (hD' : IsCycle (contractRooted Q P).graph D') :
    cycleNodes Q.graph (Subtype.val '' D') =
      contractSetRep hQ h1 '' cycleNodes (contractRooted Q P).graph D' := by
  obtain ⟨hD, hPD⟩ := contractSet_isCycle_image hQ h1 hD'
  have hrep : ∀ e ∈ D', ∀ w, (w = Q.graph.source e.1 ∨ w = Q.graph.target e.1) →
      contractSetRep hQ h1 (Quot.mk (RootedContractRel Q P) w) = w := by
    rintro e he w (rfl | rfl)
    · exact contractSetRep_mk_of_not hQ h1 (not_inPCycle_of_mem hQ h1 hD hPD
        (source_mem_cycleNodes ⟨e, he, rfl⟩))
    · exact contractSetRep_mk_of_not hQ h1 (not_inPCycle_of_mem hQ h1 hD hPD
        (target_mem_cycleNodes ⟨e, he, rfl⟩))
  exact cycleNodes_image _ Subtype.val (fun e he => (hrep e he _ (Or.inl rfl)).symm)
    (fun e he => (hrep e he _ (Or.inr rfl)).symm)

/-- **The cycles of the contracted network have the types of the cycles of `Q`.** -/
theorem contractSet_inducesCycleType_iff {D' : Set {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C}}
    (hD' : IsCycle (contractRooted Q P).graph D') {W : Quot (RootedContractRel Q P)} {n k : ℕ} :
    InducesCycleType (contractRooted Q P) D' W n k ↔
      InducesCycleType Q (Subtype.val '' D') (contractSetRep hQ h1 W) n k := by
  have hnodes : ∀ W', W' ∈ cycleNodes (contractRooted Q P).graph D' ↔
      contractSetRep hQ h1 W' ∈ cycleNodes Q.graph (Subtype.val '' D') := fun W' => by
    rw [contractSet_cycleNodes_image hQ h1 hD']
    exact (contractSetRep_injective hQ h1).mem_set_image.symm
  have hbelow : {x | (contractRooted Q P).graph.Reaches W ((contractRooted Q P).leaf x)} =
      {x | Q.graph.Reaches (contractSetRep hQ h1 W) (Q.leaf x)} := by
    ext x
    simp only [Set.mem_ofPred_eq, contractSet_reaches_iff hQ h1, contractSetRep_leaf]
  unfold InducesCycleType
  rw [hbelow, Set.ncard_image_of_injective _ Subtype.val_injective, contractSet_indegree hQ h1,
    hnodes, hnodes (contractRooted Q P).root, contractSetRep_root]
  simp only [hD', (contractSet_isCycle_image hQ h1 hD').1, true_and]

/-- **The cycles of the contracted network are those of `Q` not contracted, with their types.** -/
theorem contractSet_exists_inducesCycleType_iff (n k : ℕ) (Dx : Set X) :
    (∃ D' W, InducesCycleType (contractRooted Q P) D' W n k ∧
        {x | (contractRooted Q P).graph.Reaches W ((contractRooted Q P).leaf x)} = Dx) ↔
      ∃ D w, ¬ P D ∧ InducesCycleType Q D w n k ∧ {x | Q.graph.Reaches w (Q.leaf x)} = Dx := by
  have hbelow : ∀ W, {x | (contractRooted Q P).graph.Reaches W ((contractRooted Q P).leaf x)} =
      {x | Q.graph.Reaches (contractSetRep hQ h1 W) (Q.leaf x)} := fun W => by
    ext x
    simp only [Set.mem_ofPred_eq, contractSet_reaches_iff hQ h1, contractSetRep_leaf]
  constructor
  · rintro ⟨D', W, hD', rfl⟩
    exact ⟨_, _, (contractSet_isCycle_image hQ h1 hD'.1).2,
      (contractSet_inducesCycleType_iff hQ h1 hD'.1).1 hD', (hbelow W).symm⟩
  · rintro ⟨D, w, hP, hD, rfl⟩
    obtain ⟨D', hD', rfl⟩ := contractSet_exists_isCycle hQ h1 hD.1 hP
    have hrep := contractSetRep_mk_of_not hQ h1 (P := P)
      (not_inPCycle_of_mem hQ h1 hD.1 hP hD.2.1)
    refine ⟨D', Quot.mk _ w, (contractSet_inducesCycleType_iff hQ h1 hD').2 (by rw [hrep]; exact hD),
      ?_⟩
    rw [hbelow, hrep]

/-- The cycles of the contracted network are as many as the cycles of `Q` not contracted. -/
theorem ncard_setOf_isCycle_contractSet :
    {D' | IsCycle (contractRooted Q P).graph D'}.ncard =
      {D | IsCycle Q.graph D ∧ ¬ P D}.ncard := by
  rw [← Set.ncard_image_of_injective _ (Set.image_injective.2 Subtype.val_injective)]
  congr 1
  ext D
  constructor
  · rintro ⟨D', hD', rfl⟩
    exact contractSet_isCycle_image hQ h1 hD'
  · rintro ⟨hD, hP⟩
    obtain ⟨D', hD', rfl⟩ := contractSet_exists_isCycle hQ h1 hD hP
    exact ⟨D', hD', rfl⟩

/-- **The contracted network has the cut edges of `Q`**: a cut edge is on no cycle, and every cycle
is on one side of it. -/
theorem contractSet_hasCutSplit_iff (A : Set X) :
    (contractRooted Q P).HasCutSplit A ↔ Q.HasCutSplit A := by
  constructor
  · rintro ⟨e', T', hT', rfl⟩
    refine ⟨e'.1, {w | Quot.mk (RootedContractRel Q P) w ∈ T'}, fun f => ?_, rfl⟩
    by_cases hf : ∀ C, IsCycle Q.graph C → P C → f ∉ C
    · exact (hT' ⟨f, hf⟩).trans ⟨fun h => by subst h; rfl, fun h => Subtype.ext h⟩
    · push Not at hf
      obtain ⟨C, hC, hP, hfC⟩ := hf
      have : Quot.mk (RootedContractRel Q P) (Q.graph.source f) = Quot.mk _ (Q.graph.target f) :=
        Quot.sound ⟨C, hC, hP, source_mem_cycleNodes hfC, target_mem_cycleNodes hfC⟩
      refine ⟨fun hc => ?_, fun h => absurd (h ▸ hfC) (e'.2 C hC hP)⟩
      unfold DirectedMultigraph.Crosses at hc
      simp only [Set.mem_ofPred_eq, this] at hc
      tauto
  · rintro ⟨e, T, hT, rfl⟩
    have he : ∀ C, IsCycle Q.graph C → P C → e ∉ C := fun C hC _ =>
      notMem_of_crosses_iff hT hC
    -- a contracted cycle is on one side of `T`
    have hside : ∀ w, contractSetRep hQ h1 (Quot.mk (RootedContractRel Q P) w) ∈ T ↔ w ∈ T :=
      fun w => Q.graph.mem_iff_mem_of_walks (F := {e | ∃ C, IsCycle Q.graph C ∧ P C ∧ e ∈ C})
        (fun f ⟨C, hC, hP, hfC⟩ hc => he C hC hP (((hT f).1 hc) ▸ hfC))
        (walks_contractSetRep hQ h1 w)
    refine ⟨⟨e, he⟩, {W | contractSetRep hQ h1 W ∈ T}, fun f => ?_, ?_⟩
    · have key : (contractRooted Q P).graph.Crosses f {W | contractSetRep hQ h1 W ∈ T} ↔
          Q.graph.Crosses f.1 T := by
        unfold DirectedMultigraph.Crosses
        change (contractSetRep hQ h1 (Quot.mk _ (Q.graph.source f.1)) ∈ T ∧
            contractSetRep hQ h1 (Quot.mk _ (Q.graph.target f.1)) ∉ T ∨
            contractSetRep hQ h1 (Quot.mk _ (Q.graph.target f.1)) ∈ T ∧
            contractSetRep hQ h1 (Quot.mk _ (Q.graph.source f.1)) ∉ T) ↔ _
        rw [hside, hside]
      rw [key, hT f.1]
      exact ⟨fun h => Subtype.ext h, fun h => by subst h; rfl⟩
    · ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, contractSetRep_leaf]

omit [Fintype V] [Fintype E] h1 in
/-- A binary network has no node of indegree one and outdegree one. -/
theorem not_isChainVertex_of_binary (w : V) : ¬ Q.IsChainVertex w := fun ⟨hin, hout⟩ => by
  have hwr : w ≠ Q.root := fun h => by
    rw [h, hQ.1.root_indegree] at hin
    omega
  have := hQ.2.2 w hwr (by omega)
  omega

/-- **The network obtained by contracting cycles that induce 2-cycles satisfies `IsReducible`**: the
node of a contracted cycle off the root has indegree and outdegree one, and the root keeps
outdegree two. -/
theorem isReducible_contractSet {θ : MetricData E} (hθ : IsMetricNetwork Q θ)
    (htwo : ∃ x y : X, x ≠ y)
    (hn : ∀ C, IsCycle Q.graph C → P C →
      C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0) = 2) :
    IsReducible (contractRooted Q P) (contractMetric Q P θ) := by
  have hM := contractSet_isPhylogenetic (P := P) hQ h1
  have := hQ.1.finite_arcs
  have hroot2 : (contractRooted Q P).graph.outdegree (contractRooted Q P).root = 2 := by
    change (contractRooted Q P).graph.outdegree (Quot.mk _ Q.root) = 2
    by_cases hr : InPCycle Q P Q.root
    · obtain ⟨C, hC, hP, hrC⟩ := hr
      have := hn C hC hP
      rw [ite_eq_left hrC] at this
      rw [contractSet_outdegree_of_mem hQ h1 hC hP hrC, this]
    · rw [contractSet_outdegree_of_not hQ h1 hr]
      exact hQ.2.1
  refine
    { phylo := hM
      deg := fun W hWr h0 hnc => ?_
      root := Or.inr hroot2
      levelOne := contractSet_isLevelOne hQ h1
      chain := fun D' hD' W hW hc => ?_
      child := fun h1' => absurd (h1'.symm.trans hroot2) (by norm_num)
      metric := contractSet_isMetric hQ h1 hθ.1
      length := fun e => hθ.2 e.1
      two := htwo }
  · induction W using Quot.ind with
    | mk w =>
      by_cases hw : InPCycle Q P w
      · exfalso
        obtain ⟨C, hC, hP, hwC⟩ := hw
        have hK := isContractible_cycleTop hQ h1 hC
        have hrC : Q.root ∉ cycleNodes Q.graph C := fun hrC =>
          hWr (Quot.sound ⟨C, hC, hP, hwC, hrC⟩)
        have hc2 := hn C hC hP
        rw [ite_eq_right hrC] at hc2
        -- the top of `C` has one parent
        have htr : cycleTop Q C ≠ Q.root := fun h => hrC (h ▸ hK.top_mem)
        have hloop : ∀ f, Q.graph.source f ≠ Q.graph.target f := fun f h =>
          hQ.1.acyclic _ (.single ⟨f, rfl, h.symm⟩)
        have hout : 2 ≤ Q.graph.outdegree (cycleTop Q C) := by
          rw [← hC.ncard_incident hloop hK.top_mem]
          exact Set.ncard_le_ncard (fun f hf => hf.2.resolve_right fun h => hK.top_entry f h hf.1)
            (Set.toFinite _)
        have h3 := hQ.2.2 _ htr (by omega)
        have hin1 := hQ.1.nonroot_indegree _ htr
        refine hnc ⟨?_, ?_⟩
        · rw [contractSet_indegree hQ h1, contractSetRep_mk_of_mem hQ h1 hC hP hwC]
          omega
        · rw [contractSet_outdegree_of_mem hQ h1 hC hP hwC]
          omega
      · have hwr : w ≠ Q.root := fun h => hWr (by rw [h]; rfl)
        rw [contractSet_indegree hQ h1, contractSetRep_mk_of_not hQ h1 hw,
          contractSet_outdegree_of_not hQ h1 hw]
        rw [contractSet_outdegree_of_not hQ h1 hw] at h0
        exact hQ.2.2 w hwr h0
  · induction W using Quot.ind with
    | mk w =>
      by_cases hw : InPCycle Q P w
      · obtain ⟨C, hC, hP, hwC⟩ := hw
        have hW' := (contractSet_cycleNodes_image hQ h1 hD').symm ▸
          Set.mem_image_of_mem (contractSetRep hQ h1) hW
        rw [contractSetRep_mk_of_mem hQ h1 hC hP hwC] at hW'
        obtain ⟨hD, hPD⟩ := contractSet_isCycle_image hQ h1 hD'
        exact hPD (eq_of_mem_cycleNodes hQ h1 hC hD (isContractible_cycleTop hQ h1 hC).top_mem
          hW' ▸ hP)
      · refine not_isChainVertex_of_binary hQ w ⟨?_, ?_⟩
        · rw [← contractSetRep_mk_of_not hQ h1 hw, ← contractSet_indegree hQ h1]
          exact hc.1
        · rw [← contractSet_outdegree_of_not hQ h1 hw]
          exact hc.2

end Set

end Banos2019
