module

public import Banos2019.Quartet.SingleFourCycle
public import Banos2019.Quartet.GraphMaps
public import Banos2019.Quartet.Examples

/-!
# The 4-cycle of `Q⁻` and the network of Corollary 2 (proofs of Propositions 10 and 11)

Contracting the cycles of `Q⊕` satisfying `P` and suppressing the nodes of degree two this leaves
(`contractNet`) keeps the cycles of `Q⊕` not satisfying `P`, their arcs and their nodes, and the walks
avoiding them. This module reads the 4-cycle of `Q⁻` and its blocks off the network of Corollary 2,
a rooting of Figure 17 (`exists_rootedIso_fourOne`).

* `contractNetRep`, `contractNetFirstArc`: the node of `Q⊕` of a node of `contractNet`, and the first
  arc of the chain of an arc.
* `walks_of_contractNet_walks`: a walk of `contractNet` gives a walk of `Q⊕` on the chains of its arcs
  and the arcs of the contracted cycles; `walks_compl_of_contractNet_walks`: one avoiding a cycle not
  contracted gives one avoiding that cycle.
* `isCycle_contractNet_preimage`, `contractNetFirstArc_ends`: the arcs of `contractNet` whose first arc
  is on a cycle not contracted form a cycle, with the ends of their first arcs.
* `exists_joins_sdNode`, `mem_nodeBlock_sdNode_of_walks`: the edges of `Q⁻` of the arcs of a cycle of
  `Q⊕`, and the blocks of `Q⁻` of walks of `Q⊕` avoiding the cycle.
* `fig17CycArcs`, `isCycle_fig17Root`: the arcs of the cycle of the rootings of Figure 17.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### The nodes and arcs of `Q⊕` of those of `contractNet` -/

section ContractNetMap

variable [Fintype V] [Fintype E] {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q)
  (h1 : IsLevelOne Q.graph) (P : Set E → Prop)

/-- The node of `Q⊕` of a node of `contractNet Q hQ h1 P`: the representative of its class, the top of
a contracted cycle. -/
def contractNetRep (y : FinContractVertex
    ((contractRooted Q P).suppress (contractSet_isPhylogenetic (P := P) hQ h1))) : V :=
  contractSetRep hQ h1 (finContractVertex _ y).1

/-- The first arc of `Q⊕` on the chain of an arc of `contractNet Q hQ h1 P`. -/
def contractNetFirstArc
    (e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)) : E :=
  (finContractArc _ e).1.1

/-- `contractNet` is the suppressed contracted network with the arc at a root of outdegree one
contracted. -/
theorem isContraction_contractNet_finContract :
    IsContraction ((contractRooted Q P).suppress (contractSet_isPhylogenetic (P := P) hQ h1))
      (contractNet Q hQ h1 P) (finContractVertex _) (finContractArc _) :=
  isContraction_finContract _ (suppress_isPhylogenetic _)

variable {hQ h1 P}

theorem contractNetRep_injective : Function.Injective (contractNetRep hQ h1 P) := fun _ _ h =>
  (isContraction_contractNet_finContract hQ h1 P).inj_v (Subtype.ext (contractSetRep_injective hQ h1 h))

theorem contractNetFirstArc_injective : Function.Injective (contractNetFirstArc hQ h1 P) :=
  fun _ _ h => (isContraction_contractNet_finContract hQ h1 P).inj_e (Subtype.ext (Subtype.ext h))

/-- The node of `Q⊕` of a leaf of `contractNet` is the leaf of the same taxon. -/
theorem contractNetRep_leaf (x : X) :
    contractNetRep hQ h1 P ((contractNet Q hQ h1 P).leaf x) = Q.leaf x := by
  unfold contractNetRep
  rw [(isContraction_contractNet_finContract hQ h1 P).leaf x]
  exact contractSetRep_leaf hQ h1 x

/-- The first arc of the chain of an arc of `contractNet` is on the chain. -/
theorem contractNetFirstArc_mem
    (e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)) :
    contractNetFirstArc hQ h1 P e ∈ contractNetChain Q hQ h1 P e :=
  mem_map_of_mem _ (mem_reduceChain_self _ e)

/-- **A walk of `contractNet` gives a walk of `Q⊕`** between the nodes of `Q⊕` of its ends, on the
chains of its arcs and the arcs of the contracted cycles. -/
theorem walks_of_contractNet_walks
    {F : Set (ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1))} {y z}
    (h : (contractNet Q hQ h1 P).graph.Walks F y z) :
    Q.graph.Walks {f | (∃ e ∈ F, f ∈ contractNetChain Q hQ h1 P e) ∨
        ∃ K, IsCycle Q.graph K ∧ P K ∧ f ∈ K}
      (contractNetRep hQ h1 P y) (contractNetRep hQ h1 P z) := by
  have hK := isContraction_contractNet_finContract hQ h1 P
  have hM := contractSet_isPhylogenetic (P := P) hQ h1
  have h₁ := walks_image_of_hom (fun e => (hK.source e).symm) (fun e => (hK.target e).symm) h
  have h₂ := walks_cycleChainArcs_of_walks hM h₁
  have h₃ := walks_of_contractSet_walks hQ h1 h₂
  refine walks_mono ?_ h₃
  rintro f (⟨fM, ⟨g, ⟨e, he, rfl⟩, hon⟩, rfl⟩ | hf)
  · exact Or.inl ⟨e, he, mem_map_of_mem _ (mem_filter.2 ⟨mem_univ _, hon⟩)⟩
  · exact Or.inr hf

/-- A node of `Q⊕` off the contracted cycles is not a chain node of the contracted network. -/
theorem not_isChainVertex_contractRooted_mk (hB : IsBinaryRootedNetwork Q)
    (h1' : IsLevelOne Q.graph) {w : V} (hw : ¬ InPCycle Q P w) :
    ¬ (contractRooted Q P).IsChainVertex (Quot.mk _ w) := by
  rintro ⟨hin, hout⟩
  rw [contractSet_indegree hB h1', contractSetRep_mk_of_not hB h1' hw] at hin
  rw [contractSet_outdegree_of_not hB h1' hw] at hout
  exact not_isChainVertex_of_binary hB w ⟨hin, hout⟩

/-- Only the root of `contractNet` has the root of `Q⊕` as its node: the root of the contracted
network is the class of the root of `Q⊕`, and is a node of `contractNet` exactly when it is its
root. -/
theorem eq_root_of_contractNetRep_eq_root {y} (hy : contractNetRep hQ h1 P y = Q.root) :
    y = (contractNet Q hQ h1 P).root := by
  have hK := isContraction_contractNet_finContract hQ h1 P
  have hM := contractSet_isPhylogenetic (P := P) hQ h1
  have hyr : finContractVertex _ y = ((contractRooted Q P).suppress hM).root := by
    apply Subtype.ext
    show (finContractVertex _ y).1 = (contractRooted Q P).root
    rw [← contractSet_mk_rep hQ h1 (finContractVertex _ y).1]
    change Quot.mk _ (contractNetRep hQ h1 P y) = _
    rw [hy]
    rfl
  by_cases h1r : ((contractRooted Q P).suppress hM).graph.outdegree
      ((contractRooted Q P).suppress hM).root = 1
  · exact absurd ⟨y, hyr⟩ (fun h => ((hK.range_v _).1 h) ⟨rfl, h1r⟩)
  · exact hK.inj_v (hyr.trans (hK.root_ne h1r).symm)

variable {D : Set E} (hD : IsCycle Q.graph D) (hP : ¬ P D)
include hD hP

/-- **The arcs of `contractNet` whose first arc is on a cycle not contracted form a cycle.** -/
theorem isCycle_contractNet_preimage :
    IsCycle (contractNet Q hQ h1 P).graph {e | contractNetFirstArc hQ h1 P e ∈ D} := by
  have hK := isContraction_contractNet_finContract hQ h1 P
  have hM := contractSet_isPhylogenetic (P := P) hQ h1
  have hS := suppress_isPhylogenetic hM
  obtain ⟨DM, hDM, hDMD⟩ := contractSet_exists_isCycle hQ h1 hD hP
  obtain ⟨hDS, -⟩ := isCycle_suppress_preimage hM (contractSet_isLevelOne hQ h1) hDM
  have hrange : {g : {e // ¬ (contractRooted Q P).IsChainVertex
      ((contractRooted Q P).graph.source e)} | g.1 ∈ DM} ⊆
        Set.range (finContractArc ((contractRooted Q P).suppress hM)) := by
    intro g hg
    refine (hK.range_e g).2 fun ⟨hs, hout⟩ => ?_
    obtain ⟨f₁, hf₁, f₂, hf₂, hne, i₁, i₂⟩ :=
      hDS.exists_ne_of_mem (fun f _ => source_ne_target_of_isPhylogenetic hS f) ⟨g, hg, Or.inl hs⟩
    have s₁ := i₁.resolve_right (hS.target_ne_root f₁)
    have s₂ := i₂.resolve_right (hS.target_ne_root f₂)
    have h2 := Set.ncard_le_ncard (s := {f₁, f₂})
      (t := {e | ((contractRooted Q P).suppress hM).graph.source e =
        ((contractRooted Q P).suppress hM).root})
      (by rintro e (rfl | rfl) <;> assumption) (Set.toFinite _)
    rw [Set.ncard_pair hne] at h2
    unfold DirectedMultigraph.outdegree at hout
    omega
  have hpre := IsCycle.preimage_of_hom hK.inj_v hK.inj_e (fun e => (hK.source e).symm)
    (fun e => (hK.target e).symm) hDS hrange
  convert hpre using 1
  ext e
  change contractNetFirstArc hQ h1 P e ∈ D ↔ (finContractArc _ e).1 ∈ DM
  rw [← hDMD]
  constructor
  · rintro ⟨fM, hfM, hfe⟩
    rwa [← Subtype.ext hfe]
  · intro h
    exact ⟨_, h, rfl⟩

/-- **The first arc of an arc of `contractNet` on a cycle not contracted joins the nodes of `Q⊕` of
its ends.** -/
theorem contractNetFirstArc_ends
    {e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)}
    (he : contractNetFirstArc hQ h1 P e ∈ D) :
    Q.graph.source (contractNetFirstArc hQ h1 P e) =
        contractNetRep hQ h1 P ((contractNet Q hQ h1 P).graph.source e) ∧
      Q.graph.target (contractNetFirstArc hQ h1 P e) =
        contractNetRep hQ h1 P ((contractNet Q hQ h1 P).graph.target e) := by
  have hK := isContraction_contractNet_finContract hQ h1 P
  have hM := contractSet_isPhylogenetic (P := P) hQ h1
  have hs := not_inPCycle_of_mem hQ h1 hD hP (source_mem_cycleNodes he)
  have ht := not_inPCycle_of_mem hQ h1 hD hP (target_mem_cycleNodes he)
  constructor
  · unfold contractNetRep
    rw [hK.source e]
    exact (contractSetRep_mk_of_not hQ h1 hs).symm
  · unfold contractNetRep
    rw [hK.target e]
    show _ = contractSetRep hQ h1
      (chainEnd hM (Quot.mk _ (Q.graph.target (contractNetFirstArc hQ h1 P e))))
    rw [chainEnd_eq_self hM (not_isChainVertex_contractRooted_mk hQ h1 ht),
      contractSetRep_mk_of_not hQ h1 ht]

/-- The chain of an arc of `contractNet` whose first arc is off a cycle not contracted is off the
cycle: its other arcs leave chain nodes. -/
theorem notMem_of_mem_contractNetChain
    {e : ReduceArc (contractRooted Q P) (contractSet_isPhylogenetic (P := P) hQ h1)}
    (he : contractNetFirstArc hQ h1 P e ∉ D) {f : E} (hf : f ∈ contractNetChain Q hQ h1 P e) :
    f ∉ D := by
  obtain ⟨fM, hfM, rfl⟩ := mem_map.1 hf
  intro hfD
  rcases (mem_filter.1 hfM).2 with h | ⟨hch, -⟩
  · exact he (by unfold contractNetFirstArc; rw [← h]; exact hfD)
  · exact not_isChainVertex_contractRooted_mk hQ h1
      (not_inPCycle_of_mem hQ h1 hD hP (source_mem_cycleNodes hfD)) hch

/-- **A walk of `contractNet` avoiding the arcs whose first arc is on a cycle not contracted gives a
walk of `Q⊕` avoiding that cycle.** -/
theorem walks_compl_of_contractNet_walks {y z}
    (h : (contractNet Q hQ h1 P).graph.Walks {e | contractNetFirstArc hQ h1 P e ∉ D} y z) :
    Q.graph.Walks Dᶜ (contractNetRep hQ h1 P y) (contractNetRep hQ h1 P z) := by
  refine walks_mono ?_ (walks_of_contractNet_walks h)
  rintro f (⟨e, he, hfe⟩ | ⟨K, hK, hPK, hfK⟩) hfD
  · exact notMem_of_mem_contractNetChain hD hP he hfe hfD
  · exact hP (h1 K D hK hD ⟨f, hfK, hfD⟩ ▸ hPK)

end ContractNetMap

/-! ### Edges and blocks of `Q⁻` from arcs and walks of `Q⊕` -/

section Unrooted

variable [Fintype V] [Fintype E] [Fintype X] {Q : RootedNetwork V E X} {θ : MetricData E}

omit [Fintype V] in
/-- Two nodes of `Q⊕` other than the root with the same node of `Q⁻` are equal. -/
theorem eq_of_sdNode_eq (hQ : IsLSAQuartet Q θ) {p q : V} (hp : p ≠ Q.root) (hq : q ≠ Q.root)
    (h : sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial p =
      sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial q) : p = q := by
  have := hQ.nontrivial
  have hr := lsa_univ_eq_root hQ.binary.1 hQ.nontrivial hQ.isLSA
  have hreach : ∀ y, Q.graph.Reaches (lsa hQ.binary.1 Set.univ Set.univ_nonempty) y := fun y => by
    rw [hr]; exact hQ.binary.1.root_reaches y
  rw [← sdVert_sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial (hreach p) (hr ▸ hp),
    ← sdVert_sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial (hreach q) (hr ▸ hq), h]

omit [Fintype V] in
/-- **The edge of `Q⁻` of an arc of a cycle of `Q⊕`**: an arc not leaving the root is an edge of
`Q⁻`; the two arcs of the root are merged into one edge. -/
theorem exists_joins_sdNode (hQ : IsLSAQuartet Q θ)
    {C : Set (SemidirectedArc hQ.binary.1 hQ.binary.2 hQ.nontrivial)} {p q : V}
    (h : (∃ e ∈ liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial C, Q.graph.source e ≠ Q.root ∧
        Joins Q.graph e p q) ∨
      ∃ e₁ ∈ liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial C,
        ∃ e₂ ∈ liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial C, e₁ ≠ e₂ ∧
          Q.graph.source e₁ = Q.root ∧ Q.graph.source e₂ = Q.root ∧ Q.graph.target e₁ = p ∧
          Q.graph.target e₂ = q) :
    ∃ g ∈ C, Joins hQ.unrooted.graph g (sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial p)
      (sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial q) := by
  have hM := hQ.binary.1
  have hB := hQ.binary.2
  have hX := hQ.nontrivial
  have hr := lsa_univ_eq_root hM hX hQ.isLSA
  have hreach : ∀ y, Q.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) y := fun y => by
    rw [hr]; exact hM.root_reaches y
  have h0s : Q.graph.source (sdRootArc hM hB hX) = Q.root := by
    rw [(sdRootArc_spec hM hB hX).1, hr]
  rcases h with ⟨e, he, hsr, hj⟩ | ⟨e₁, he₁, e₂, he₂, hne, hs₁, hs₂, ht₁, ht₂⟩
  · obtain ⟨g, rfl⟩ := (mem_range_sdArc hM hB hX e).2
      ⟨hreach _, fun h => hsr (by rw [h, h0s])⟩
    refine ⟨g, (sdArc_mem_liftEdges_iff hM hB hX C g).1 he, ?_⟩
    unfold Joins
    rw [sdNode_source, sdNode_target]
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by rw [h₁], by rw [h₂]⟩
    · exact Or.inr ⟨by rw [h₁], by rw [h₂]⟩
  · -- one of the two arcs of the root is `sdRootArc`, merged into the other
    have hlsa : sdNode hM hB hX (lsa hM Set.univ Set.univ_nonempty) =
        sdNode hM hB hX (Q.graph.target (sdRootArc hM hB hX)) := by
      apply sdVert_injective hM hX
      rw [sdVert_sdNode_lsa, sdVert_sdNode hM hB hX (hreach _)
        (by rw [hr]; exact hM.target_ne_root _)]
    have hr2 : Q.graph.outdegree Q.root = 2 :=
      ((isBinaryRootedNetwork_iff Q).1 hQ.binary).2.2.2.2.2.2.1
    rcases mem_pair_of_source_of_outdegree_eq_two hr2 hne hs₁ hs₂ _ h0s with h0 | h0
    · obtain ⟨g, rfl⟩ := (mem_range_sdArc hM hB hX e₂).2
        ⟨hreach _, fun h => hne (h0.symm.trans h.symm)⟩
      refine ⟨g, (sdArc_mem_liftEdges_iff hM hB hX C g).1 he₂, Or.inl ⟨?_, ?_⟩⟩
      · rw [sdNode_source, hs₂, ← hr, hlsa, h0, ht₁]
      · rw [sdNode_target, ht₂]
    · obtain ⟨g, rfl⟩ := (mem_range_sdArc hM hB hX e₁).2
        ⟨hreach _, fun h => hne (h.trans h0)⟩
      refine ⟨g, (sdArc_mem_liftEdges_iff hM hB hX C g).1 he₁, Or.inr ⟨?_, ?_⟩⟩
      · rw [sdNode_source, hs₁, ← hr, hlsa, h0, ht₂]
      · rw [sdNode_target, ht₁]

omit [Fintype V] in
/-- **A walk of `Q⊕` avoiding the cycle of a cycle `C` of `Q⁻` gives a taxon of a block of `C`.** -/
theorem mem_nodeBlock_sdNode_of_walks (hQ : IsLSAQuartet Q θ)
    {C : Set (SemidirectedArc hQ.binary.1 hQ.binary.2 hQ.nontrivial)} {y : V} {x : X}
    (h : Q.graph.Walks (liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial C)ᶜ y (Q.leaf x)) :
    x ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C
      (sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial y) := by
  have hr := lsa_univ_eq_root hQ.binary.1 hQ.nontrivial hQ.isLSA
  have hw := walks_semidirected_of_walks hQ.binary.1 hQ.binary.2 hQ.nontrivial
    (A := (liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial C)ᶜ) (F := Cᶜ)
    (fun f _ => by rw [hr]; exact hQ.binary.1.root_reaches _)
    (fun g hg hgC => hg ((sdArc_mem_liftEdges_iff _ _ _ C g).2 hgC)) h
  rw [sdNode_leaf] at hw
  exact hw

end Unrooted

/-! ### The cycle of the rootings of Figure 17 -/

/-- The arcs of the cycle of the rootings of Figure 17: the edges `4, …, 7` of the figure, and the
arc `8` of the root when the root is on the cycle (the last three rootings). -/
def fig17CycArcs (s : Fin 7) : Finset (Fin 9) := if 4 ≤ s then {4, 5, 6, 7, 8} else {4, 5, 6, 7}

/-- The nodes `4, 5, 6, 7` of the cycle of Figure 17, of the taxa `a, b, c, d`. -/
def fig17Node : Fin 4 → Fin 9 := ![4, 5, 6, 7]

/-- The leaves `0, 1, 2, 3` of the taxa `a, b, c, d`. -/
def fig17Leaf : Fin 4 → Fin 9 := ![0, 1, 2, 3]

/-- The range of a map from `Fin k` is its image of `univ`. -/
theorem range_eq_coe_of_image_eq {k : ℕ} {e : Fin k → Fin 9} {F : Finset (Fin 9)}
    (h : univ.image e = F) : Set.range e = ↑F := by
  rw [← h, coe_image, coe_univ, Set.image_univ]

/-- **The cycle of the rootings of Figure 17.** -/
theorem isCycle_fig17Root (s : Fin 7) :
    IsCycle (⟨fig17RootSrc s, fig17RootTgt s⟩ : DirectedMultigraph (Fin 9) (Fin 9))
      ↑(fig17CycArcs s) := by
  fin_cases s
  · exact ⟨4, ![4, 5, 6, 7], ![5, 6, 7, 4], ⟨by norm_num, by unfold Joins; decide, by decide,
      by decide⟩, range_eq_coe_of_image_eq (by decide)⟩
  · exact ⟨4, ![4, 5, 6, 7], ![5, 6, 7, 4], ⟨by norm_num, by unfold Joins; decide, by decide,
      by decide⟩, range_eq_coe_of_image_eq (by decide)⟩
  · exact ⟨4, ![4, 5, 6, 7], ![5, 6, 7, 4], ⟨by norm_num, by unfold Joins; decide, by decide,
      by decide⟩, range_eq_coe_of_image_eq (by decide)⟩
  · exact ⟨4, ![4, 5, 6, 7], ![5, 6, 7, 4], ⟨by norm_num, by unfold Joins; decide, by decide,
      by decide⟩, range_eq_coe_of_image_eq (by decide)⟩
  · exact ⟨5, ![4, 8, 5, 6, 7], ![5, 8, 6, 7, 4], ⟨by norm_num, by unfold Joins; decide, by decide,
      by decide⟩, range_eq_coe_of_image_eq (by decide)⟩
  · exact ⟨5, ![4, 8, 5, 6, 7], ![8, 5, 6, 7, 4], ⟨by norm_num, by unfold Joins; decide, by decide,
      by decide⟩, range_eq_coe_of_image_eq (by decide)⟩
  · exact ⟨5, ![4, 5, 8, 6, 7], ![5, 8, 6, 7, 4], ⟨by norm_num, by unfold Joins; decide, by decide,
      by decide⟩, range_eq_coe_of_image_eq (by decide)⟩

/-- Each taxon is joined to its node of the cycle off the cycle: by its arc, or through the root. -/
theorem fig17_witness (s : Fin 7) (i : Fin 4) :
    (∃ j, j ∉ fig17CycArcs s ∧ fig17RootSrc s j = fig17Node i ∧ fig17RootTgt s j = fig17Leaf i) ∨
    ∃ j₁ j₂, j₁ ∉ fig17CycArcs s ∧ j₂ ∉ fig17CycArcs s ∧ fig17RootTgt s j₁ = fig17Node i ∧
      fig17RootSrc s j₁ = fig17RootSrc s j₂ ∧ fig17RootTgt s j₂ = fig17Leaf i := by
  revert s i; decide

/-- Consecutive nodes of the cycle are joined by an arc of the cycle not leaving the root, or by the
two arcs of the root. -/
theorem fig17_edge (s : Fin 7) (i : Fin 4) :
    (∃ j ∈ fig17CycArcs s, fig17RootSrc s j ≠ 8 ∧
      ((fig17RootSrc s j = fig17Node i ∧ fig17RootTgt s j = fig17Node (finRotate 4 i)) ∨
        (fig17RootSrc s j = fig17Node (finRotate 4 i) ∧ fig17RootTgt s j = fig17Node i))) ∨
    ∃ j₁ ∈ fig17CycArcs s, ∃ j₂ ∈ fig17CycArcs s, j₁ ≠ j₂ ∧ fig17RootSrc s j₁ = 8 ∧
      fig17RootSrc s j₂ = 8 ∧ fig17RootTgt s j₁ = fig17Node i ∧
        fig17RootTgt s j₂ = fig17Node (finRotate 4 i) := by
  revert s i; decide

/-- The nodes `4, …, 7` are on the cycle. -/
theorem fig17_mem (s : Fin 7) (i : Fin 4) :
    ∃ j ∈ fig17CycArcs s, fig17RootSrc s j = fig17Node i ∨ fig17RootTgt s j = fig17Node i := by
  revert s i; decide

/-- The edge of Figure 17 that the root of a rooting splits is not `t₁` (the edge `4`): it is the
edge of `a` or of `b`, the edge `t₂`, or the hybrid edge from `5` to `6`. -/
theorem fig17_merged_ne (s : Fin 7) : (![0, 0, 1, 1, 5, 5, 6] : Fin 7 → Fin 8) s ≠ 4 := by
  revert s; decide

/-- The hybrid edges `6` and `7` of the rootings enter the node `6`. -/
theorem fig17_hybrid_tgt (s : Fin 7) : fig17RootTgt s 6 = 6 ∧ fig17RootTgt s 7 = 6 := by
  revert s; decide

end Banos2019
