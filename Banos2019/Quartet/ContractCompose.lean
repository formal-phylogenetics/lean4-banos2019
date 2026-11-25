module

public import Banos2019.Quartet.ReduceSpec
public import Banos2019.Quartet.ContractComposeChain

/-!
# Contracting one cycle, then the others

Let `Q` be a binary level-1 network whose cycles satisfying `P` induce 2-cycles, `C` one of them,
and `P₀` a predicate that holds of `C` only among the cycles of `Q` (`SelectsCycle Q P₀ C`; for
instance `(· = C)`). Contracting `C` and suppressing the node of degree two this leaves gives
`Q₁ = contractNet Q hQ h1 P₀`. Contracting in `Q₁` the cycles `P₁` that correspond to the cycles of
`Q` satisfying `P` gives `contractRooted Q P` with the node of `C` suppressed when `C` is off the
root, and `contractRooted Q P` itself, renamed, when `C` passes through the root. The two contracted
networks have the same concordance factors.

* `contractSet_isChainVertex_mk_iff`: the chain nodes of `contractRooted Q P` are the nodes of the
  contracted cycles off the root.
* `contractNetVertex`, `contractNetArc`: the node and the arc of `Q` of a node and an arc of `Q₁`;
  `contractNetArc_image_isCycle`, `exists_contractNetArc_image_eq`, `contractNet_cycleNodes`,
  `contractNet_inducesCycleType_iff`: the cycles of `Q₁` are those of `Q` other than `C`, with their
  types; `mem_contractNetChain_iff`: the arcs of `Q` on the chain of an arc of `Q₁`.
* `contractComposeVertex`, `contractComposeArc`, `isPartialSuppression_contractCompose`: the
  contracted `Q₁` is the contracted `Q` with the node of `C` suppressed (`IsPartialSuppression`).
* `cf_contractRooted_contractNet_eq`: the two contracted networks have the same concordance factors.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] {Q : RootedNetwork V E X}

/-! ### The chain nodes of a network with cycles contracted -/

section ChainNodes

variable (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph) {P : Set E → Prop}
  (hn : ∀ D, IsCycle Q.graph D → P D →
    D.ncard - (if Q.root ∈ cycleNodes Q.graph D then 1 else 0) = 2)
include hQ h1 hn

/-- **The chain nodes of the contracted network** are the nodes of the contracted cycles off the
root, when these induce 2-cycles. -/
theorem contractSet_isChainVertex_mk_iff (w : V) :
    (contractRooted Q P).IsChainVertex (Quot.mk _ w) ↔
      ∃ D, IsCycle Q.graph D ∧ P D ∧ w ∈ cycleNodes Q.graph D ∧ Q.root ∉ cycleNodes Q.graph D := by
  constructor
  · intro hc
    by_cases hw : InPCycle Q P w
    · obtain ⟨D, hD, hP, hwD⟩ := hw
      refine ⟨D, hD, hP, hwD, fun hr => ?_⟩
      have h2 := hn D hD hP
      rw [ite_eq_left hr] at h2
      have h3 := hc.2
      rw [contractSet_outdegree_of_mem hQ h1 hD hP hwD] at h3
      omega
    · refine absurd ⟨?_, ?_⟩ (not_isChainVertex_of_binary hQ w)
      · rw [← contractSetRep_mk_of_not hQ h1 hw, ← contractSet_indegree hQ h1]
        exact hc.1
      · rw [← contractSet_outdegree_of_not hQ h1 hw]
        exact hc.2
  · rintro ⟨D, hD, hP, hwD, hr⟩
    have hK := isContractible_cycleTop hQ h1 hD
    have hc2 := hn D hD hP
    rw [ite_eq_right hr] at hc2
    have htr : cycleTop Q D ≠ Q.root := fun h => hr (h ▸ hK.top_mem)
    have hloop : ∀ f, Q.graph.source f ≠ Q.graph.target f := fun f h =>
      hQ.1.acyclic _ (.single ⟨f, rfl, h.symm⟩)
    have hout : 2 ≤ Q.graph.outdegree (cycleTop Q D) := by
      rw [← hD.ncard_incident hloop hK.top_mem]
      exact Set.ncard_le_ncard (fun f hf => hf.2.resolve_right fun h => hK.top_entry f h hf.1)
        (Set.toFinite _)
    have h3 := hQ.2.2 _ htr (by omega)
    have hin1 := hQ.1.nonroot_indegree _ htr
    refine ⟨?_, ?_⟩
    · rw [contractSet_indegree hQ h1, contractSetRep_mk_of_mem hQ h1 hD hP hwD]
      omega
    · rw [contractSet_outdegree_of_mem hQ h1 hD hP hwD]
      omega

/-- The root of the contracted network has outdegree two. -/
theorem contractSet_outdegree_root :
    (contractRooted Q P).graph.outdegree (contractRooted Q P).root = 2 := by
  change (contractRooted Q P).graph.outdegree (Quot.mk _ Q.root) = 2
  by_cases hr : InPCycle Q P Q.root
  · obtain ⟨D, hD, hP, hrD⟩ := hr
    have h2 := hn D hD hP
    rw [ite_eq_left hrD] at h2
    rw [contractSet_outdegree_of_mem hQ h1 hD hP hrD]
    omega
  · rw [contractSet_outdegree_of_not hQ h1 hr]
    exact hQ.2.1

/-- The nodes of a cycle of the contracted network are not chain nodes. -/
theorem contractSet_not_isChainVertex_of_mem_cycleNodes
    {D' : Set {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C}}
    (hD' : IsCycle (contractRooted Q P).graph D') {W : Quot (RootedContractRel Q P)}
    (hW : W ∈ cycleNodes (contractRooted Q P).graph D') :
    ¬ (contractRooted Q P).IsChainVertex W := by
  obtain ⟨hD, hPD⟩ := contractSet_isCycle_image hQ h1 hD'
  have hW' : contractSetRep hQ h1 W ∈ cycleNodes Q.graph (Subtype.val '' D') := by
    rw [contractSet_cycleNodes_image hQ h1 hD']
    exact Set.mem_image_of_mem _ hW
  intro hc
  rw [← contractSet_mk_rep hQ h1 W, contractSet_isChainVertex_mk_iff hQ h1 hn] at hc
  obtain ⟨D, hD₀, hP, hwD, -⟩ := hc
  exact hPD (eq_of_mem_cycleNodes hQ h1 hD₀ hD hwD hW' ▸ hP)

end ChainNodes

/-- A representative on a contracted cycle is its top. -/
theorem contractSetRep_eq_cycleTop {P : Set E → Prop} (hQ : IsBinaryRootedNetwork Q)
    (h1 : IsLevelOne Q.graph) {C : Set E} (hC : IsCycle Q.graph C) (hP : P C)
    {W : Quot (RootedContractRel Q P)} (h : contractSetRep hQ h1 W ∈ cycleNodes Q.graph C) :
    contractSetRep hQ h1 W = cycleTop Q C := by
  have := contractSetRep_mk_of_mem hQ h1 hC hP h
  rwa [contractSet_mk_rep] at this

/-- The inheritance of an arc of `contractNet` is the product of the inheritances of its chain. -/
theorem contractNetMetric_inheritance_eq_prod (hQ : IsBinaryRootedNetwork Q)
    (h1 : IsLevelOne Q.graph) {P : Set E → Prop} (θ : MetricData E)
    (e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)) :
    (contractNetMetric Q hQ h1 P θ).inheritance e =
      ∏ f ∈ contractNetChain Q hQ h1 P e, θ.inheritance f := by
  unfold contractNetChain reduceChain
  rw [prod_map]
  rfl

/-! ### Contracting one cycle -/

/-- `P₀` holds of the cycle `C` of `Q` only, and `C` induces a 2-cycle. -/
structure SelectsCycle (Q : RootedNetwork V E X) (P₀ : Set E → Prop) (C : Set E) : Prop where
  isCycle : IsCycle Q.graph C
  mem : P₀ C
  eq : ∀ D, IsCycle Q.graph D → P₀ D → D = C
  ncard : C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0) = 2

section OneCycle

variable (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph) (P₀ : Set E → Prop)

/-- `Q` with the cycles satisfying `P₀` contracted and its chain nodes suppressed, before the
renaming of its nodes and arcs that gives `contractNet Q hQ h1 P₀`. -/
abbrev contractSuppress :=
  (contractRooted Q P₀).suppress (contractSet_isPhylogenetic hQ h1)

/-- The node of `Q` of a node of `contractNet Q hQ h1 P₀`: the representative of its node in `Q`
with the cycles satisfying `P₀` contracted, the top of the cycle for a contracted cycle. -/
def contractNetVertex (y : FinContractVertex (contractSuppress hQ h1 P₀)) : V :=
  contractSetRep hQ h1 (finContractVertex _ y).1

/-- The arc of `Q` of an arc of `contractNet Q hQ h1 P₀`: the first arc of its chain. -/
def contractNetArc (a : FinContractArc (contractSuppress hQ h1 P₀)) : E :=
  (finContractArc _ a).1.1

/-- `contractNet` is the suppressed contracted network with the arc at a root of outdegree one
contracted. -/
theorem isContraction_contractNet :
    IsContraction (contractSuppress hQ h1 P₀) (contractNet Q hQ h1 P₀)
      (finContractVertex _) (finContractArc _) :=
  isContraction_finContract _ _

theorem contractNetVertex_injective : Function.Injective (contractNetVertex hQ h1 P₀) :=
  (contractSetRep_injective hQ h1).comp
    (Subtype.val_injective.comp (isContraction_contractNet hQ h1 P₀).inj_v)

theorem contractNetArc_injective : Function.Injective (contractNetArc hQ h1 P₀) :=
  Subtype.val_injective.comp (Subtype.val_injective.comp (isContraction_contractNet hQ h1 P₀).inj_e)

variable {P₀}

theorem contractNetVertex_source (a : FinContractArc (contractSuppress hQ h1 P₀)) :
    contractNetVertex hQ h1 P₀ ((contractNet Q hQ h1 P₀).graph.source a) =
      contractSetRep hQ h1
        (Quot.mk (RootedContractRel Q P₀) (Q.graph.source (contractNetArc hQ h1 P₀ a))) := by
  unfold contractNetVertex
  rw [(isContraction_contractNet hQ h1 P₀).source a]
  rfl

theorem contractNetVertex_target (a : FinContractArc (contractSuppress hQ h1 P₀)) :
    contractNetVertex hQ h1 P₀ ((contractNet Q hQ h1 P₀).graph.target a) =
      contractSetRep hQ h1 (chainEnd (contractSet_isPhylogenetic hQ h1)
        (Quot.mk (RootedContractRel Q P₀) (Q.graph.target (contractNetArc hQ h1 P₀ a)))) := by
  unfold contractNetVertex
  rw [(isContraction_contractNet hQ h1 P₀).target a]
  rfl

theorem contractNetVertex_leaf (x : X) :
    contractNetVertex hQ h1 P₀ ((contractNet Q hQ h1 P₀).leaf x) = Q.leaf x := by
  unfold contractNetVertex
  rw [(isContraction_contractNet hQ h1 P₀).leaf x]
  exact contractSetRep_leaf hQ h1 x

theorem contractNetArc_image (D : Set (FinContractArc (contractSuppress hQ h1 P₀))) :
    contractNetArc hQ h1 P₀ '' D =
      Subtype.val '' (Subtype.val '' (finContractArc (contractSuppress hQ h1 P₀) '' D)) := by
  simp only [Set.image_image]
  rfl

variable {C : Set E} (hO : SelectsCycle Q P₀ C)
include hQ h1 hO

omit [Fintype V] [Fintype E] hQ h1 in
theorem SelectsCycle.inPCycle_iff {w : V} : InPCycle Q P₀ w ↔ w ∈ cycleNodes Q.graph C :=
  ⟨fun ⟨D, hD, hP, hw⟩ => hO.eq D hD hP ▸ hw, fun hw => ⟨C, hO.isCycle, hO.mem, hw⟩⟩

omit [Fintype V] [Fintype E] hQ h1 in
theorem SelectsCycle.hn : ∀ D, IsCycle Q.graph D → P₀ D →
    D.ncard - (if Q.root ∈ cycleNodes Q.graph D then 1 else 0) = 2 :=
  fun D hD hP => hO.eq D hD hP ▸ hO.ncard

omit [Fintype V] [Fintype E] hQ h1 in
theorem SelectsCycle.notMem {g : E} (hg : g ∉ C) : ∀ D, IsCycle Q.graph D → P₀ D → g ∉ D :=
  fun D hD hP => hO.eq D hD hP ▸ hg

theorem contractNetArc_notMem (a : FinContractArc (contractSuppress hQ h1 P₀)) :
    contractNetArc hQ h1 P₀ a ∉ C :=
  (finContractArc _ a).1.2 C hO.isCycle hO.mem

omit [Fintype V] in
/-- The representative of a node of `Q` off `C`, with `C` contracted, is the node. -/
theorem contractSetRep_one_of_notMem {w : V} (hw : w ∉ cycleNodes Q.graph C) :
    contractSetRep hQ h1 (Quot.mk (RootedContractRel Q P₀) w) = w :=
  contractSetRep_mk_of_not hQ h1 fun h => hw (hO.inPCycle_iff.1 h)

/-- **The chain node of `Q` with `C` contracted** is the node of `C`, when `C` is off the root. -/
theorem contractOne_isChainVertex_mk_iff (w : V) :
    (contractRooted Q P₀).IsChainVertex (Quot.mk _ w) ↔
      w ∈ cycleNodes Q.graph C ∧ Q.root ∉ cycleNodes Q.graph C := by
  rw [contractSet_isChainVertex_mk_iff hQ h1 hO.hn]
  constructor
  · rintro ⟨D, hD, hP, hw, hr⟩
    obtain rfl := hO.eq D hD hP
    exact ⟨hw, hr⟩
  · rintro ⟨hw, hr⟩
    exact ⟨C, hO.isCycle, hO.mem, hw, hr⟩

theorem contractSuppress_outdegree_root :
    (contractSuppress hQ h1 P₀).graph.outdegree (contractSuppress hQ h1 P₀).root = 2 :=
  (suppress_outdegree _ _).trans (contractSet_outdegree_root hQ h1 hO.hn)

theorem contractNetVertex_root :
    contractNetVertex hQ h1 P₀ (contractNet Q hQ h1 P₀).root = Q.root := by
  unfold contractNetVertex
  rw [(isContraction_contractNet hQ h1 P₀).root_ne (by
    rw [contractSuppress_outdegree_root hQ h1 hO]; norm_num)]
  exact contractSetRep_root hQ h1

/-- A node of `contractNet Q hQ h1 P₀` is on `C` only when `C` passes through the root, as the node
of `C`. -/
theorem contractNetVertex_mem_cycleNodes {y : FinContractVertex (contractSuppress hQ h1 P₀)}
    (hy : contractNetVertex hQ h1 P₀ y ∈ cycleNodes Q.graph C) :
    Q.root ∈ cycleNodes Q.graph C ∧ contractNetVertex hQ h1 P₀ y = cycleTop Q C := by
  refine ⟨?_, contractSetRep_eq_cycleTop hQ h1 hO.isCycle hO.mem
    (W := (finContractVertex (contractSuppress hQ h1 P₀) y).1) hy⟩
  by_contra hr
  apply (finContractVertex (contractSuppress hQ h1 P₀) y).2
  rw [← contractSet_mk_rep hQ h1 (finContractVertex (contractSuppress hQ h1 P₀) y).1,
    contractOne_isChainVertex_mk_iff hQ h1 hO]
  exact ⟨hy, hr⟩

/-- **Every node of `Q` off `C`, or on `C` through the root, is a node of
`contractNet Q hQ h1 P₀`.** -/
theorem exists_contractNetVertex_eq {w : V}
    (hw : ¬ (w ∈ cycleNodes Q.graph C ∧ Q.root ∉ cycleNodes Q.graph C)) :
    ∃ y, (finContractVertex (contractSuppress hQ h1 P₀) y).1 =
      Quot.mk (RootedContractRel Q P₀) w := by
  have hnc : ¬ (contractRooted Q P₀).IsChainVertex (Quot.mk _ w) := by
    rwa [contractOne_isChainVertex_mk_iff hQ h1 hO]
  obtain ⟨y, hy⟩ := ((isContraction_contractNet hQ h1 P₀).range_v ⟨_, hnc⟩).2 (fun h => by
    have := h.2
    rw [contractSuppress_outdegree_root hQ h1 hO] at this
    omega)
  exact ⟨y, congrArg Subtype.val hy⟩

/-- **Every arc of `Q` off `C` whose source is not the node of `C` off the root is an arc of
`contractNet Q hQ h1 P₀`.** -/
theorem exists_contractNetArc_eq {g : E} (hg : g ∉ C)
    (hs : ¬ (Q.graph.source g ∈ cycleNodes Q.graph C ∧ Q.root ∉ cycleNodes Q.graph C)) :
    ∃ a, contractNetArc hQ h1 P₀ a = g := by
  have hnc : ¬ (contractRooted Q P₀).IsChainVertex
      ((contractRooted Q P₀).graph.source ⟨g, hO.notMem hg⟩) := by
    change ¬ (contractRooted Q P₀).IsChainVertex (Quot.mk _ (Q.graph.source g))
    rwa [contractOne_isChainVertex_mk_iff hQ h1 hO]
  obtain ⟨a, ha⟩ := ((isContraction_contractNet hQ h1 P₀).range_e ⟨_, hnc⟩).2 (fun h => by
    have := h.2
    rw [contractSuppress_outdegree_root hQ h1 hO] at this
    omega)
  exact ⟨a, congrArg (fun s => s.1.1) ha⟩

/-- The nodes of a cycle of `Q` with `C` contracted are not chain nodes. -/
theorem contractOne_chain : ∀ D, IsCycle (contractRooted Q P₀).graph D →
    ∀ w ∈ cycleNodes (contractRooted Q P₀).graph D, ¬ (contractRooted Q P₀).IsChainVertex w :=
  fun _ hD _ hw => contractSet_not_isChainVertex_of_mem_cycleNodes hQ h1 hO.hn hD hw

/-- **A cycle of `contractNet Q hQ h1 P₀` is a cycle of `Q` other than `C`**, on the arcs of its
arcs. -/
theorem contractNetArc_image_isCycle {D : Set (FinContractArc (contractSuppress hQ h1 P₀))}
    (hD : IsCycle (contractNet Q hQ h1 P₀).graph D) :
    IsCycle Q.graph (contractNetArc hQ h1 P₀ '' D) ∧ contractNetArc hQ h1 P₀ '' D ≠ C := by
  have h₁ := (isContraction_contractNet hQ h1 P₀).isCycle_image hD
  have h₂ := (suppress_isCycle_image _ (contractOne_chain hQ h1 hO) h₁).1
  rw [contractNetArc_image]
  obtain ⟨h₃, h₄⟩ := contractSet_isCycle_image hQ h1 h₂
  exact ⟨h₃, fun h => h₄ (h ▸ hO.mem)⟩

/-- **Every cycle of `Q` other than `C` is a cycle of `contractNet Q hQ h1 P₀`.** -/
theorem exists_contractNetArc_image_eq {D : Set E} (hD : IsCycle Q.graph D) (hDC : D ≠ C) :
    ∃ D₁, IsCycle (contractNet Q hQ h1 P₀).graph D₁ ∧ contractNetArc hQ h1 P₀ '' D₁ = D := by
  obtain ⟨D', hD', rfl⟩ :=
    contractSet_exists_isCycle hQ h1 (P := P₀) hD fun hP => hDC (hO.eq D hD hP)
  obtain ⟨D'', hD'', rfl⟩ := exists_suppress_isCycle _ (contractOne_chain hQ h1 hO) hD'
  obtain ⟨D₁, hD₁, rfl⟩ :=
    (isContraction_contractNet hQ h1 P₀).exists_eq_image (suppress_isPhylogenetic _) hD''
  exact ⟨D₁, hD₁, contractNetArc_image hQ h1 D₁⟩

/-- The nodes of a cycle of `contractNet Q hQ h1 P₀` are the nodes of its cycle of `Q`. -/
theorem contractNet_cycleNodes {D : Set (FinContractArc (contractSuppress hQ h1 P₀))}
    (hD : IsCycle (contractNet Q hQ h1 P₀).graph D) :
    cycleNodes Q.graph (contractNetArc hQ h1 P₀ '' D) =
      contractNetVertex hQ h1 P₀ '' cycleNodes (contractNet Q hQ h1 P₀).graph D := by
  have hK := isContraction_contractNet hQ h1 P₀
  have h₁ := hK.isCycle_image hD
  have h₂ := (suppress_isCycle_image _ (contractOne_chain hQ h1 hO) h₁).1
  rw [contractNetArc_image, contractSet_cycleNodes_image hQ h1 h₂,
    suppress_cycleNodes_image _ (contractOne_chain hQ h1 hO) h₁, hK.cycleNodes_image,
    Set.image_image, Set.image_image]
  rfl

theorem root_mem_contractNet_cycleNodes_iff
    {D : Set (FinContractArc (contractSuppress hQ h1 P₀))}
    (hD : IsCycle (contractNet Q hQ h1 P₀).graph D) :
    Q.root ∈ cycleNodes Q.graph (contractNetArc hQ h1 P₀ '' D) ↔
      (contractNet Q hQ h1 P₀).root ∈ cycleNodes (contractNet Q hQ h1 P₀).graph D := by
  rw [contractNet_cycleNodes hQ h1 hO hD, ← contractNetVertex_root hQ h1 hO]
  exact (contractNetVertex_injective hQ h1 P₀).mem_set_image

/-- A node of `contractNet Q hQ h1 P₀` on a cycle `D ≠ C` of `Q` is on the cycle of `D`. -/
theorem exists_contractNet_cycle_of_mem {D : Set E} (hD : IsCycle Q.graph D) (hDC : D ≠ C)
    {y : FinContractVertex (contractSuppress hQ h1 P₀)}
    (hy : contractNetVertex hQ h1 P₀ y ∈ cycleNodes Q.graph D) :
    ∃ D₁, IsCycle (contractNet Q hQ h1 P₀).graph D₁ ∧ contractNetArc hQ h1 P₀ '' D₁ = D ∧
      y ∈ cycleNodes (contractNet Q hQ h1 P₀).graph D₁ := by
  obtain ⟨D₁, hD₁, rfl⟩ := exists_contractNetArc_image_eq hQ h1 hO hD hDC
  rw [contractNet_cycleNodes hQ h1 hO hD₁] at hy
  exact ⟨D₁, hD₁, rfl, (contractNetVertex_injective hQ h1 P₀).mem_set_image.1 hy⟩

/-- **The cycles of `contractNet Q hQ h1 P₀` have the types of their cycles of `Q`.** -/
theorem contractNet_inducesCycleType_iff [Fintype X]
    {D : Set (FinContractArc (contractSuppress hQ h1 P₀))}
    (hD : IsCycle (contractNet Q hQ h1 P₀).graph D)
    {y : FinContractVertex (contractSuppress hQ h1 P₀)} {n k : ℕ} :
    InducesCycleType (contractNet Q hQ h1 P₀) D y n k ↔
      InducesCycleType Q (contractNetArc hQ h1 P₀ '' D) (contractNetVertex hQ h1 P₀ y) n k := by
  have hK := isContraction_contractNet hQ h1 P₀
  have h₁ := hK.isCycle_image hD
  have h₂ := (suppress_isCycle_image _ (contractOne_chain hQ h1 hO) h₁).1
  rw [hK.inducesCycleType_iff (suppress_isPhylogenetic _) (fun h => absurd h (by
      rw [contractSuppress_outdegree_root hQ h1 hO]; norm_num)),
    suppress_inducesCycleType_iff _ (contractOne_chain hQ h1 hO),
    contractSet_inducesCycleType_iff hQ h1 h₂, contractNetArc_image]
  rfl

/-- A cycle of `contractNet Q hQ h1 P₀` induces a cycle of one of two types exactly when its cycle
of `Q` does. -/
theorem contractNet_exists_inducesCycleType_or_iff [Fintype X]
    {D : Set (FinContractArc (contractSuppress hQ h1 P₀))}
    (hD : IsCycle (contractNet Q hQ h1 P₀).graph D) (n k n' k' : ℕ) :
    (∃ y, InducesCycleType (contractNet Q hQ h1 P₀) D y n k ∨
        InducesCycleType (contractNet Q hQ h1 P₀) D y n' k') ↔
      ∃ v, InducesCycleType Q (contractNetArc hQ h1 P₀ '' D) v n k ∨
        InducesCycleType Q (contractNetArc hQ h1 P₀ '' D) v n' k' := by
  simp only [contractNet_inducesCycleType_iff hQ h1 hO hD]
  constructor
  · rintro ⟨y, h⟩
    exact ⟨_, h⟩
  · rintro ⟨v, h⟩
    have hv : v ∈ cycleNodes Q.graph (contractNetArc hQ h1 P₀ '' D) := by
      rcases h with h | h <;> exact h.2.1
    rw [contractNet_cycleNodes hQ h1 hO hD] at hv
    obtain ⟨y, -, rfl⟩ := hv
    exact ⟨y, h⟩

/-- **The arcs of `Q` on the chain of an arc of `contractNet Q hQ h1 P₀`**: its arc, and, when it
enters `C` off the root, the arc leaving `C`. -/
theorem mem_contractNetChain_iff (a : FinContractArc (contractSuppress hQ h1 P₀)) (f : E) :
    f ∈ contractNetChain Q hQ h1 P₀ a ↔ f = contractNetArc hQ h1 P₀ a ∨
      (f ∉ C ∧ Q.graph.source f ∈ cycleNodes Q.graph C ∧ Q.root ∉ cycleNodes Q.graph C ∧
        Q.graph.target (contractNetArc hQ h1 P₀ a) ∈ cycleNodes Q.graph C) := by
  simp only [contractNetChain, reduceChain, mem_map, mem_filter, mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨h, hon, rfl⟩
    rcases hon with rfl | ⟨hc, hr⟩
    · exact Or.inl rfl
    · right
      change (contractRooted Q P₀).IsChainVertex (Quot.mk _ (Q.graph.source h.1)) at hc
      rw [contractOne_isChainVertex_mk_iff hQ h1 hO] at hc
      refine ⟨h.2 C hO.isCycle hO.mem, hc.1, hc.2, ?_⟩
      rcases Relation.ReflTransGen.cases_head hr with heq | ⟨b, hb, -⟩
      · rcases (contractSet_mk_eq_mk_iff hQ h1).1 heq with h' | ⟨D, hD, hPD, ht, -⟩
        · exact h' ▸ hc.1
        · exact hO.eq D hD hPD ▸ ht
      · have hb' := hb.1
        change (contractRooted Q P₀).IsChainVertex (Quot.mk _ (Q.graph.target _)) at hb'
        exact ((contractOne_isChainVertex_mk_iff hQ h1 hO _).1 hb').1
  · rintro (rfl | ⟨hfC, hs, hr, ht⟩)
    · exact ⟨(finContractArc _ a).1, Or.inl rfl, rfl⟩
    · refine ⟨⟨f, hO.notMem hfC⟩, Or.inr ⟨?_, ?_⟩, rfl⟩
      · change (contractRooted Q P₀).IsChainVertex (Quot.mk _ (Q.graph.source f))
        exact (contractOne_isChainVertex_mk_iff hQ h1 hO _).2 ⟨hs, hr⟩
      · change (contractRooted Q P₀).ChainReach (Quot.mk _ (Q.graph.target _))
          (Quot.mk _ (Q.graph.source f))
        rw [Quot.sound (⟨C, hO.isCycle, hO.mem, ht, hs⟩ : RootedContractRel Q P₀ _ _)]
        exact .refl

end OneCycle

/-! ### Contracting the other cycles -/

section Compose

variable (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph) {P : Set E → Prop}
  (hn : ∀ D, IsCycle Q.graph D → P D →
    D.ncard - (if Q.root ∈ cycleNodes Q.graph D then 1 else 0) = 2)
  {P₀ : Set E → Prop} {C : Set E} (hO : SelectsCycle Q P₀ C) (hPC : P C)
  (hQ₁ : IsBinaryRootedNetwork (contractNet Q hQ h1 P₀))
  (h1₁ : IsLevelOne (contractNet Q hQ h1 P₀).graph)
  {P₁ : Set (FinContractArc (contractSuppress hQ h1 P₀)) → Prop}
  (hP₁ : ∀ D, IsCycle (contractNet Q hQ h1 P₀).graph D →
    (P₁ D ↔ P (contractNetArc hQ h1 P₀ '' D)))

variable (P P₁) in
/-- The node of `contractRooted Q P` of a node of `contractRooted (contractNet Q hQ h1 P₀) P₁`. -/
def contractComposeVertex (W : Quot (RootedContractRel (contractNet Q hQ h1 P₀) P₁)) :
    Quot (RootedContractRel Q P) :=
  Quot.mk _ (contractNetVertex hQ h1 P₀ (contractSetRep hQ₁ h1₁ W))

include hO hP₁ in
/-- An arc of `contractNet Q hQ h1 P₀` off the cycles `P₁` is an arc of `Q` off the cycles `P`. -/
theorem contractNetArc_notMem_of_notMem
    (e : {e // ∀ D, IsCycle (contractNet Q hQ h1 P₀).graph D → P₁ D → e ∉ D}) :
    ∀ D, IsCycle Q.graph D → P D → contractNetArc hQ h1 P₀ e.1 ∉ D := by
  intro D hD hP he
  have hDC : D ≠ C := fun h => contractNetArc_notMem hQ h1 hO e.1 (h ▸ he)
  obtain ⟨D₁, hD₁, rfl⟩ := exists_contractNetArc_image_eq hQ h1 hO hD hDC
  exact e.2 D₁ hD₁ ((hP₁ D₁ hD₁).2 hP) ((contractNetArc_injective hQ h1 P₀).mem_set_image.1 he)

include hO hP₁ in
/-- The arc of `contractRooted Q P` of an arc of `contractRooted (contractNet Q hQ h1 P₀) P₁`. -/
def contractComposeArc
    (e : {e // ∀ D, IsCycle (contractNet Q hQ h1 P₀).graph D → P₁ D → e ∉ D}) :
    {e // ∀ D, IsCycle Q.graph D → P D → e ∉ D} :=
  ⟨contractNetArc hQ h1 P₀ e.1, contractNetArc_notMem_of_notMem hQ h1 hO hP₁ e⟩

include hO hPC in
/-- A node of `Q` and its representative with `C` contracted are one node of
`contractRooted Q P`. -/
theorem mk_contractSetRep_one (w : V) :
    Quot.mk (RootedContractRel Q P) (contractSetRep hQ h1 (Quot.mk (RootedContractRel Q P₀) w)) =
      Quot.mk _ w := by
  by_cases hw : w ∈ cycleNodes Q.graph C
  · rw [contractSetRep_mk_of_mem hQ h1 hO.isCycle hO.mem hw]
    exact Quot.sound ⟨C, hO.isCycle, hPC, (isContractible_cycleTop hQ h1 hO.isCycle).top_mem, hw⟩
  · rw [contractSetRep_one_of_notMem hQ h1 hO hw]

include hO hP₁ in
theorem contractComposeVertex_mk (y : FinContractVertex (contractSuppress hQ h1 P₀)) :
    contractComposeVertex hQ h1 P hQ₁ h1₁ P₁ (Quot.mk _ y) =
      Quot.mk _ (contractNetVertex hQ h1 P₀ y) := by
  unfold contractComposeVertex
  by_cases hy : InPCycle (contractNet Q hQ h1 P₀) P₁ y
  · obtain ⟨D₁, hD₁, hP, hyD⟩ := hy
    rw [contractSetRep_mk_of_mem hQ₁ h1₁ hD₁ hP hyD]
    refine Quot.sound ⟨_, (contractNetArc_image_isCycle hQ h1 hO hD₁).1, (hP₁ D₁ hD₁).1 hP, ?_, ?_⟩
    · rw [contractNet_cycleNodes hQ h1 hO hD₁]
      exact Set.mem_image_of_mem _ (isContractible_cycleTop hQ₁ h1₁ hD₁).top_mem
    · rw [contractNet_cycleNodes hQ h1 hO hD₁]
      exact Set.mem_image_of_mem _ hyD
  · rw [contractSetRep_mk_of_not hQ₁ h1₁ hy]

include hO hP₁ in
theorem contractComposeVertex_root :
    contractComposeVertex hQ h1 P hQ₁ h1₁ P₁ (contractRooted (contractNet Q hQ h1 P₀) P₁).root =
      (contractRooted Q P).root := by
  change contractComposeVertex hQ h1 P hQ₁ h1₁ P₁ (Quot.mk _ (contractNet Q hQ h1 P₀).root) =
    Quot.mk _ Q.root
  rw [contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁, contractNetVertex_root hQ h1 hO]

include hO hPC hP₁ in
/-- **The nodes of `contractRooted Q P` that are not nodes of the contracted `Q₁`**: the node of
`C`, when `C` is off the root. -/
theorem mk_mem_range_contractComposeVertex_iff (w : V) :
    Quot.mk (RootedContractRel Q P) w ∈ Set.range (contractComposeVertex hQ h1 P hQ₁ h1₁ P₁) ↔
      ¬ (w ∈ cycleNodes Q.graph C ∧ Q.root ∉ cycleNodes Q.graph C) := by
  constructor
  · rintro ⟨W, hW⟩ ⟨hwC, hr⟩
    induction W using Quot.ind with
    | mk y =>
    rw [contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁] at hW
    have hyC : contractNetVertex hQ h1 P₀ y ∈ cycleNodes Q.graph C := by
      rcases (contractSet_mk_eq_mk_iff hQ h1).1 hW with h | ⟨D, hD, -, hy, hw⟩
      · exact h ▸ hwC
      · exact eq_of_mem_cycleNodes hQ h1 hD hO.isCycle hw hwC ▸ hy
    exact hr (contractNetVertex_mem_cycleNodes hQ h1 hO hyC).1
  · intro hw
    by_cases hP : InPCycle Q P w
    · obtain ⟨D, hD, hPD, hwD⟩ := hP
      by_cases hDC : D = C
      · have hr : Q.root ∈ cycleNodes Q.graph C := not_not.1 fun hr => hw ⟨hDC ▸ hwD, hr⟩
        refine ⟨(contractRooted (contractNet Q hQ h1 P₀) P₁).root, ?_⟩
        rw [contractComposeVertex_root hQ h1 hO hQ₁ h1₁ hP₁]
        exact Quot.sound ⟨C, hO.isCycle, hPC, hr, hDC ▸ hwD⟩
      · obtain ⟨D₁, hD₁, rfl⟩ := exists_contractNetArc_image_eq hQ h1 hO hD hDC
        rw [contractNet_cycleNodes hQ h1 hO hD₁] at hwD
        obtain ⟨y, -, rfl⟩ := hwD
        exact ⟨Quot.mk _ y, contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁ y⟩
    · have hwC : w ∉ cycleNodes Q.graph C := fun h => hP ⟨C, hO.isCycle, hPC, h⟩
      obtain ⟨y, hy⟩ := exists_contractNetVertex_eq hQ h1 hO (fun h => hwC h.1)
      refine ⟨Quot.mk _ y, ?_⟩
      rw [contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁]
      unfold contractNetVertex
      rw [hy, contractSetRep_one_of_notMem hQ h1 hO hwC]

include hn hO hP₁ in
/-- The cycles `P₁` of `contractNet Q hQ h1 P₀` induce 2-cycles. -/
theorem contractCompose_hn (D : Set (FinContractArc (contractSuppress hQ h1 P₀)))
    (hD : IsCycle (contractNet Q hQ h1 P₀).graph D) (hP : P₁ D) :
    D.ncard - (if (contractNet Q hQ h1 P₀).root ∈ cycleNodes (contractNet Q hQ h1 P₀).graph D
      then 1 else 0) = 2 := by
  have h := hn _ (contractNetArc_image_isCycle hQ h1 hO hD).1 ((hP₁ D hD).1 hP)
  rw [Set.ncard_image_of_injective _ (contractNetArc_injective hQ h1 P₀)] at h
  have hr := root_mem_contractNet_cycleNodes_iff hQ h1 hO hD
  by_cases h' : (contractNet Q hQ h1 P₀).root ∈ cycleNodes (contractNet Q hQ h1 P₀).graph D
  · rw [ite_eq_left h']
    rwa [ite_eq_left (hr.2 h')] at h
  · rw [ite_eq_right h']
    rwa [ite_eq_right (mt hr.1 h')] at h

include hn hO hP₁ in
/-- **A node of the contracted `Q₁` is a chain node exactly when its node of `contractRooted Q P`
is one.** -/
theorem contractCompose_isChainVertex_iff
    (W : Quot (RootedContractRel (contractNet Q hQ h1 P₀) P₁)) :
    (contractRooted Q P).IsChainVertex (contractComposeVertex hQ h1 P hQ₁ h1₁ P₁ W) ↔
      (contractRooted (contractNet Q hQ h1 P₀) P₁).IsChainVertex W := by
  induction W using Quot.ind with
  | mk y =>
  rw [contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁, contractSet_isChainVertex_mk_iff hQ h1 hn,
    contractSet_isChainVertex_mk_iff hQ₁ h1₁ (contractCompose_hn hQ h1 hn hO hP₁)]
  constructor
  · rintro ⟨D, hD, hP, hyD, hr⟩
    have hDC : D ≠ C := by
      rintro rfl
      exact hr (contractNetVertex_mem_cycleNodes hQ h1 hO hyD).1
    obtain ⟨D₁, hD₁, rfl, hy⟩ := exists_contractNet_cycle_of_mem hQ h1 hO hD hDC hyD
    exact ⟨D₁, hD₁, (hP₁ D₁ hD₁).2 hP, hy,
      fun h => hr ((root_mem_contractNet_cycleNodes_iff hQ h1 hO hD₁).2 h)⟩
  · rintro ⟨D₁, hD₁, hP, hy, hr⟩
    refine ⟨_, (contractNetArc_image_isCycle hQ h1 hO hD₁).1, (hP₁ D₁ hD₁).1 hP, ?_,
      fun h => hr ((root_mem_contractNet_cycleNodes_iff hQ h1 hO hD₁).1 h)⟩
    rw [contractNet_cycleNodes hQ h1 hO hD₁]
    exact Set.mem_image_of_mem _ hy

include hn hO hPC hP₁ in
/-- **From the node of `contractRooted Q P` of a node `t` of `Q`, the chain through the node of `C`
reaches the node of the end of the chain from `t` in `Q` with `C` contracted.** -/
theorem chainReachOff_contractCompose (t : V) :
    ChainReachOff (contractRooted Q P) (Set.range (contractComposeVertex hQ h1 P hQ₁ h1₁ P₁))
      (Quot.mk _ t)
      (Quot.mk _ (contractSetRep hQ h1 (chainEnd (contractSet_isPhylogenetic hQ h1)
        (Quot.mk (RootedContractRel Q P₀) t)))) := by
  have hM := contractSet_isPhylogenetic (P := P₀) hQ h1
  by_cases hc : (contractRooted Q P₀).IsChainVertex (Quot.mk _ t)
  · have ht := (contractOne_isChainVertex_mk_iff hQ h1 hO t).1 hc
    obtain ⟨g, hg⟩ := ((contractRooted Q P₀).graph.outdegree_eq_one_iff _).1 hc.2
    have hgs : (contractRooted Q P₀).graph.source g = Quot.mk _ t := (hg g).2 rfl
    have hsC : Q.graph.source g.1 ∈ cycleNodes Q.graph C := by
      rcases (contractSet_mk_eq_mk_iff hQ h1).1 hgs with h | ⟨D, hD, hPD, hs, -⟩
      · exact h ▸ ht.1
      · exact hO.eq D hD hPD ▸ hs
    have htg : ¬ (contractRooted Q P₀).IsChainVertex ((contractRooted Q P₀).graph.target g) := by
      intro hc'
      have hgt := ((contractOne_isChainVertex_mk_iff hQ h1 hO _).1 hc').1
      have hloop : (contractRooted Q P₀).graph.target g = (contractRooted Q P₀).graph.source g :=
        Quot.sound ⟨C, hO.isCycle, hO.mem, hgt, hsC⟩
      exact hM.acyclic _ (.single ⟨g, rfl, hloop⟩)
    rw [chainEnd_eq_of_adj hM hc ⟨g, hgs, rfl⟩, chainEnd_eq_self hM htg]
    change ChainReachOff _ _ _ (Quot.mk _ (contractSetRep hQ h1 (Quot.mk _ (Q.graph.target g.1))))
    rw [mk_contractSetRep_one hQ h1 hO hPC]
    have hgK : ∀ D, IsCycle Q.graph D → P D → g.1 ∉ D := fun D hD _ hgD =>
      g.2 C hO.isCycle hO.mem
        (eq_of_mem_cycleNodes hQ h1 hD hO.isCycle (source_mem_cycleNodes hgD) hsC ▸ hgD)
    refine Relation.ReflTransGen.single ⟨?_, ?_, ⟨g.1, hgK⟩, ?_, rfl⟩
    · exact (contractSet_isChainVertex_mk_iff hQ h1 hn t).2 ⟨C, hO.isCycle, hPC, ht.1, ht.2⟩
    · rw [mk_mem_range_contractComposeVertex_iff hQ h1 hO hPC hQ₁ h1₁ hP₁]
      exact not_not.2 ht
    · exact Quot.sound ⟨C, hO.isCycle, hPC, hsC, ht.1⟩
  · rw [chainEnd_eq_self hM hc, mk_contractSetRep_one hQ h1 hO hPC]
    exact .refl

include hn hO hPC hP₁ in
/-- **Contracting the cycles `P₁` of `contractNet Q hQ h1 P₀` is contracting the cycles `P` of `Q`
and suppressing the node of `C`.** -/
theorem isPartialSuppression_contractCompose :
    IsPartialSuppression (contractRooted Q P) (contractRooted (contractNet Q hQ h1 P₀) P₁)
      (contractComposeVertex hQ h1 P hQ₁ h1₁ P₁) (contractComposeArc hQ h1 hO hP₁) where
  inj_v W W' h := by
    induction W using Quot.ind with
    | mk y =>
    induction W' using Quot.ind with
    | mk y' =>
    rw [contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁,
      contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁] at h
    rcases (contractSet_mk_eq_mk_iff hQ h1).1 h with h | ⟨D, hD, hP, hy, hy'⟩
    · rw [contractNetVertex_injective hQ h1 P₀ h]
    · by_cases hDC : D = C
      · subst hDC
        have hyy := contractNetVertex_injective hQ h1 P₀
          ((contractNetVertex_mem_cycleNodes hQ h1 hO hy).2.trans
            (contractNetVertex_mem_cycleNodes hQ h1 hO hy').2.symm)
        rw [hyy]
      · obtain ⟨D₁, hD₁, rfl, hy₁⟩ := exists_contractNet_cycle_of_mem hQ h1 hO hD hDC hy
        rw [contractNet_cycleNodes hQ h1 hO hD₁] at hy'
        exact Quot.sound ⟨D₁, hD₁, (hP₁ D₁ hD₁).2 hP, hy₁,
          (contractNetVertex_injective hQ h1 P₀).mem_set_image.1 hy'⟩
  inj_e a b h := Subtype.ext (contractNetArc_injective hQ h1 P₀ (congrArg Subtype.val h :))
  source e := by
    change Quot.mk _ (Q.graph.source (contractNetArc hQ h1 P₀ e.1)) =
      contractComposeVertex hQ h1 P hQ₁ h1₁ P₁
        (Quot.mk _ ((contractNet Q hQ h1 P₀).graph.source e.1))
    rw [contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁, contractNetVertex_source,
      mk_contractSetRep_one hQ h1 hO hPC]
  target e := by
    change ChainReachOff _ _ (Quot.mk _ (Q.graph.target (contractNetArc hQ h1 P₀ e.1)))
      (contractComposeVertex hQ h1 P hQ₁ h1₁ P₁
        (Quot.mk _ ((contractNet Q hQ h1 P₀).graph.target e.1)))
    rw [contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁, contractNetVertex_target]
    exact chainReachOff_contractCompose hQ h1 hn hO hPC hQ₁ h1₁ hP₁ _
  chain_iff W := contractCompose_isChainVertex_iff hQ h1 hn hO hQ₁ h1₁ hP₁ W
  range_v v hv := by
    induction v using Quot.ind with
    | mk w =>
    rw [mk_mem_range_contractComposeVertex_iff hQ h1 hO hPC hQ₁ h1₁ hP₁]
    rintro ⟨hw, hr⟩
    exact hv ((contractSet_isChainVertex_mk_iff hQ h1 hn w).2 ⟨C, hO.isCycle, hPC, hw, hr⟩)
  range_e e v he := by
    have hR : Quot.mk (RootedContractRel Q P) (Q.graph.source e.1) ∈
        Set.range (contractComposeVertex hQ h1 P hQ₁ h1₁ P₁) := ⟨v, he.symm⟩
    rw [mk_mem_range_contractComposeVertex_iff hQ h1 hO hPC hQ₁ h1₁ hP₁] at hR
    obtain ⟨a, ha⟩ := exists_contractNetArc_eq hQ h1 hO (e.2 C hO.isCycle hPC) hR
    exact ⟨⟨a, fun D hD hP haD => e.2 _ (contractNetArc_image_isCycle hQ h1 hO hD).1
      ((hP₁ D hD).1 hP) (ha ▸ Set.mem_image_of_mem _ haD)⟩, Subtype.ext ha⟩
  root := contractComposeVertex_root hQ h1 hO hQ₁ h1₁ hP₁
  leaf x := by
    change contractComposeVertex hQ h1 P hQ₁ h1₁ P₁ (Quot.mk _ ((contractNet Q hQ h1 P₀).leaf x)) =
      Quot.mk _ (Q.leaf x)
    rw [contractComposeVertex_mk hQ h1 hO hQ₁ h1₁ hP₁, contractNetVertex_leaf]

include hO hPC hP₁ in
/-- An arc of the contracted `Q₁` stands for the arcs of `Q` on its chain. -/
theorem mem_segArcs_contractCompose_iff
    (e : {e // ∀ D, IsCycle (contractNet Q hQ h1 P₀).graph D → P₁ D → e ∉ D})
    (g : {e // ∀ D, IsCycle Q.graph D → P D → e ∉ D}) :
    g ∈ segArcs (contractRooted Q P) (contractComposeVertex hQ h1 P hQ₁ h1₁ P₁)
        (contractComposeArc hQ h1 hO hP₁) e ↔
      g.1 = contractNetArc hQ h1 P₀ e.1 ∨ (Q.graph.source g.1 ∈ cycleNodes Q.graph C ∧
        Q.root ∉ cycleNodes Q.graph C ∧
          Q.graph.target (contractNetArc hQ h1 P₀ e.1) ∈ cycleNodes Q.graph C) := by
  simp only [segArcs, mem_filter, mem_univ, true_and]
  change g = _ ∨ (Quot.mk _ (Q.graph.source g.1) ∉ _ ∧ ChainReachOff _ _
    (Quot.mk _ (Q.graph.target (contractNetArc hQ h1 P₀ e.1))) (Quot.mk _ (Q.graph.source g.1))) ↔ _
  rw [mk_mem_range_contractComposeVertex_iff hQ h1 hO hPC hQ₁ h1₁ hP₁, not_not]
  refine or_congr Subtype.ext_iff ⟨fun ⟨hs, hr⟩ => ⟨hs.1, hs.2, ?_⟩,
    fun ⟨hs, hr, ht⟩ => ⟨⟨hs, hr⟩, ?_⟩⟩
  · rcases Relation.ReflTransGen.cases_head hr with h | ⟨b, hb, -⟩
    · rcases (contractSet_mk_eq_mk_iff hQ h1).1 h with h | ⟨D, hD, -, htD, hsD⟩
      · exact h ▸ hs.1
      · exact eq_of_mem_cycleNodes hQ h1 hD hO.isCycle hsD hs.1 ▸ htD
    · have hb' := hb.2.1
      rw [mk_mem_range_contractComposeVertex_iff hQ h1 hO hPC hQ₁ h1₁ hP₁, not_not] at hb'
      exact hb'.1
  · rw [Quot.sound (⟨C, hO.isCycle, hPC, ht, hs⟩ : RootedContractRel Q P _ _)]
    exact .refl

include hO hPC hP₁ in
/-- **The chain of an arc of `contractNet Q hQ h1 P₀` is made of the arcs that its arc in the
contracted `Q₁` stands for.** -/
theorem contractNetChain_eq_map_segArcs
    (e : {e // ∀ D, IsCycle (contractNet Q hQ h1 P₀).graph D → P₁ D → e ∉ D}) :
    contractNetChain Q hQ h1 P₀ e.1 =
      (segArcs (contractRooted Q P) (contractComposeVertex hQ h1 P hQ₁ h1₁ P₁)
        (contractComposeArc hQ h1 hO hP₁) e).map (Function.Embedding.subtype _) := by
  ext f
  rw [mem_contractNetChain_iff hQ h1 hO, mem_map]
  simp only [mem_segArcs_contractCompose_iff hQ h1 hO hPC hQ₁ h1₁ hP₁,
    Function.Embedding.coe_subtype]
  constructor
  · rintro (rfl | ⟨hfC, hs, hr, ht⟩)
    · exact ⟨contractComposeArc hQ h1 hO hP₁ e, Or.inl rfl, rfl⟩
    · refine ⟨⟨f, fun D hD _ hfD => hfC ?_⟩, Or.inr ⟨hs, hr, ht⟩, rfl⟩
      exact eq_of_mem_cycleNodes hQ h1 hD hO.isCycle (source_mem_cycleNodes hfD) hs ▸ hfD
  · rintro ⟨g, hg | ⟨hs, hr, ht⟩, rfl⟩
    · exact Or.inl hg
    · exact Or.inr ⟨g.2 C hO.isCycle hPC, hs, hr, ht⟩

include hn hO hPC hQ₁ h1₁ hP₁ in
/-- **Contracting the cycle `C` and suppressing the node of degree two this leaves, then contracting
the cycles `P₁` that correspond to the other cycles `P` of `Q`, gives the concordance factors of
contracting the cycles `P` of `Q`**: the second network is the first with the node of `C` suppressed
(`isPartialSuppression_contractCompose`), each of its arcs with the total length and the inheritance
of its chain. -/
theorem cf_contractRooted_contractNet_eq [Fintype X] {θ : MetricData E} (hθ : Q.IsMetric θ)
    (hθ₁ : (contractNet Q hQ h1 P₀).IsMetric (contractNetMetric Q hQ h1 P₀ θ)) :
    cf (contractRooted (contractNet Q hQ h1 P₀) P₁)
        (contractMetric _ P₁ (contractNetMetric Q hQ h1 P₀ θ)) =
      cf (contractRooted Q P) (contractMetric Q P θ) := by
  have hS := isPartialSuppression_contractCompose hQ h1 hn hO hPC hQ₁ h1₁ hP₁
  refine hS.cf_eq (contractSet_isPhylogenetic hQ h1) (contractSet_isPhylogenetic hQ₁ h1₁)
    (contractSet_isMetric hQ h1 hθ).isNormalized (contractSet_isMetric hQ₁ h1₁ hθ₁).isNormalized
    (fun e => ?_) (fun e => ?_)
  · change (contractNetMetric Q hQ h1 P₀ θ).length e.1 = _
    rw [contractNetMetric_length, contractNetChain_eq_map_segArcs hQ h1 hO hPC hQ₁ h1₁ hP₁,
      sum_map]
    rfl
  · change (contractNetMetric Q hQ h1 P₀ θ).inheritance e.1 = _
    rw [contractNetMetric_inheritance_eq_prod,
      contractNetChain_eq_map_segArcs hQ h1 hO hPC hQ₁ h1₁ hP₁, prod_map]
    rfl

end Compose

end Banos2019
