module

public import Banos2019.Quartet.CycleBlocks
public import Banos2019.Network.Suppress

/-!
# Cut edges of a binary level-1 network

* `notMem_of_crosses_iff`: an edge that alone crosses a set of nodes is on no cycle.
* `hasCutSplit_of_isCut`: the taxa below a cut vertex entered by a single arc are the side of a cut
  edge.
* `hasCutSplit_below_hybrid`: the taxa below a hybrid node are the side of a cut edge.
* `exists_offCycle_edge`: a node of a cycle other than the root is on exactly one edge off the
  cycle.
* `hasCutSplit_nodeBlock`: the block of a node of a cycle other than the root is the side of a cut
  edge, the edge at that node off the cycle.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-- **An edge that alone crosses a set of nodes is on no cycle**: the rest of the cycle would join
its ends without crossing. -/
theorem notMem_of_crosses_iff {G : DirectedMultigraph V E} {T : Set V} {e : E}
    (hT : ∀ f, G.Crosses f T ↔ f = e) {D : Set E} (hD : IsCycle G D) : e ∉ D := by
  intro he
  have hw := hD.walks_sdiff_singleton he (target_mem_cycleNodes he) (source_mem_cycleNodes he)
  have := G.mem_iff_mem_of_walks (F := D \ {e}) (S := T) (fun f hf hc => hf.2 ((hT f).1 hc)) hw
  have hc := (hT e).2 rfl
  unfold DirectedMultigraph.Crosses at hc
  tauto

variable {N : RootedNetwork V E X}

/-- **The taxa below a cut vertex `r` entered by a single arc `c` are the side of the cut edge
`c`.** -/
theorem hasCutSplit_of_isCut (hN : N.IsPhylogenetic) {r : V} (hc : IsCut N r) {c : E}
    (hcr : N.graph.target c = r) (huniq : ∀ g, N.graph.target g = r → g = c) :
    N.HasCutSplit {x | N.graph.Reaches r (N.leaf x)} := by
  refine ⟨c, {w | N.graph.Reaches r w}, fun f => ⟨fun hf => ?_, fun hf => ?_⟩, rfl⟩
  · rcases hf with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact absurd (Relation.ReflTransGen.tail hs ⟨f, rfl, rfl⟩) ht
    · by_contra hfc
      exact hs (hc.entry f ht fun h => hfc (huniq f h))
  · subst hf
    exact Or.inr ⟨hcr ▸ .refl, not_reaches_source_of_target_eq hN hcr⟩

/-- **The taxa below a hybrid node are the side of a cut edge**, the arc out of the hybrid node. -/
theorem hasCutSplit_below_hybrid (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) {v : V}
    (h2 : N.graph.indegree v = 2) : N.HasCutSplit {x | N.graph.Reaches v (N.leaf x)} := by
  obtain ⟨c, hc, hcu⟩ := existsUnique_child_of_hybrid hN h2
  obtain ⟨hcut, huniq⟩ := isCut_child_of_hybrid hN h1 h2 hc hcu
  have hs := hasCutSplit_of_isCut hN.1 hcut rfl huniq
  have heq : {x | N.graph.Reaches v (N.leaf x)} =
      {x | N.graph.Reaches (N.graph.target c) (N.leaf x)} := by
    ext x
    constructor
    · intro hx
      rcases eq_or_reaches_of_unique_child hcu hx with h | h
      · exfalso
        have := hN.1.leaf_indegree x
        rw [h, h2] at this
        omega
      · exact h
    · exact fun hx => Relation.ReflTransGen.head ⟨c, hc, rfl⟩ hx
  rw [heq]
  exact hs

/-- **A node of a cycle other than the root is on exactly one edge off the cycle**: it is on three
edges, two of the cycle. -/
theorem exists_offCycle_edge [Finite E] (hN : IsBinaryRootedNetwork N) {C : Set E}
    (hC : IsCycle N.graph C) {w : V} (hw : w ∈ cycleNodes N.graph C) (hwr : w ≠ N.root) :
    N.graph.outdegree w ≠ 0 ∧ ∃ g, g ∉ C ∧ (N.graph.source g = w ∨ N.graph.target g = w) ∧
      ∀ f, f ∉ C → (N.graph.source f = w ∨ N.graph.target f = w) → f = g := by
  have hloop : ∀ f, N.graph.source f ≠ N.graph.target f := fun f h =>
    hN.1.acyclic _ (.single ⟨f, rfl, h.symm⟩)
  have hinc := hC.ncard_incident hloop hw
  -- `w` is not a taxon, so it is on three edges
  have h0 : N.graph.outdegree w ≠ 0 := fun h0 => by
    obtain ⟨x, rfl⟩ := (hN.1.leaves w).1 h0
    have hsub : {f | f ∈ C ∧ (N.graph.source f = N.leaf x ∨ N.graph.target f = N.leaf x)} ⊆
        {f | N.graph.target f = N.leaf x} := fun f hf =>
      hf.2.resolve_left fun h => (N.graph.outdegree_eq_zero_iff _).1 h0 f h
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hl := hN.1.leaf_indegree x
    unfold DirectedMultigraph.indegree at hl
    omega
  have h3 := hN.2.2 w hwr h0
  have hall : {f | N.graph.source f = w ∨ N.graph.target f = w}.ncard = 3 := by
    rw [show {f | N.graph.source f = w ∨ N.graph.target f = w} =
      {f | N.graph.source f = w} ∪ {f | N.graph.target f = w} from rfl,
      Set.ncard_union_eq (Set.disjoint_left.2 fun f (hs : N.graph.source f = w)
        (ht : N.graph.target f = w) => hloop f (hs.trans ht.symm))
        (Set.toFinite _) (Set.toFinite _)]
    unfold DirectedMultigraph.indegree DirectedMultigraph.outdegree at h3
    omega
  -- the edge `g` at `w` off `C`
  have hoff : {f | f ∉ C ∧ (N.graph.source f = w ∨ N.graph.target f = w)}.ncard = 1 := by
    have hu : {f | N.graph.source f = w ∨ N.graph.target f = w} =
        {f | f ∈ C ∧ (N.graph.source f = w ∨ N.graph.target f = w)} ∪
          {f | f ∉ C ∧ (N.graph.source f = w ∨ N.graph.target f = w)} := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      tauto
    rw [hu, Set.ncard_union_eq (Set.disjoint_left.2 fun f
      (h : f ∈ C ∧ (N.graph.source f = w ∨ N.graph.target f = w))
      (h' : f ∉ C ∧ (N.graph.source f = w ∨ N.graph.target f = w)) => h'.1 h.1) (Set.toFinite _)
      (Set.toFinite _), hinc] at hall
    omega
  obtain ⟨g, hg⟩ := Set.ncard_eq_one.1 hoff
  have hgmem : g ∉ C ∧ (N.graph.source g = w ∨ N.graph.target g = w) := by
    have : g ∈ ({g} : Set E) := rfl
    rw [← hg] at this
    exact this
  refine ⟨h0, g, hgmem.1, hgmem.2, fun f hf hfw => ?_⟩
  have : f ∈ {f | f ∉ C ∧ (N.graph.source f = w ∨ N.graph.target f = w)} := ⟨hf, hfw⟩
  rw [hg] at this
  exact this

/-- **The block of a node `w` of a cycle `C` other than the root is the side of a cut edge**: `w` is
on three edges, two of `C` and one off `C`, `g`; the nodes joined to `w` avoiding `C`, other than
`w`, are entered only by `g`. -/
theorem hasCutSplit_nodeBlock [Finite E] (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    {C : Set E} (hC : IsCycle N.graph C) {w : V} (hw : w ∈ cycleNodes N.graph C)
    (hwr : w ≠ N.root) : N.HasCutSplit (nodeBlock N.graph N.leaf C w) := by
  have hloop : ∀ f, N.graph.source f ≠ N.graph.target f := fun f h =>
    hN.1.acyclic _ (.single ⟨f, rfl, h.symm⟩)
  obtain ⟨h0, g, hgC, hgw, hguniq⟩ := exists_offCycle_edge hN hC hw hwr
  have hgmem : g ∉ C ∧ (N.graph.source g = w ∨ N.graph.target g = w) := ⟨hgC, hgw⟩
  -- the nodes joined to `w` avoiding `C`, other than `w`
  set T : Set V := {u | u ≠ w ∧ N.graph.Walks Cᶜ w u} with hT_def
  have hcn : ∀ u ∈ cycleNodes N.graph C, u ∉ T := fun u hu hT =>
    hT.1 (h1.eq_of_walks_compl hC hw hu hT.2).symm
  refine ⟨g, T, fun f => ⟨fun hf => ?_, fun hf => ?_⟩, ?_⟩
  · by_cases hfC : f ∈ C
    · exfalso
      rcases hf with ⟨hs, -⟩ | ⟨ht, -⟩
      · exact hcn _ (source_mem_cycleNodes hfC) hs
      · exact hcn _ (target_mem_cycleNodes hfC) ht
    by_cases hfw : N.graph.source f = w ∨ N.graph.target f = w
    · exact hguniq f hfC hfw
    · exfalso
      push Not at hfw
      rcases hf with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact ht ⟨hfw.2, hs.2.tail ⟨f, hfC, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact hs ⟨hfw.1, ht.2.tail ⟨f, hfC, Or.inr ⟨rfl, rfl⟩⟩⟩
  · subst hf
    have hwT : w ∉ T := fun h => h.1 rfl
    rcases hgmem.2 with hs | ht
    · refine Or.inr ⟨⟨fun h => hloop f (hs.trans h.symm), .single ⟨f, hgmem.1, Or.inl ⟨hs, rfl⟩⟩⟩,
        hs ▸ hwT⟩
    · refine Or.inl ⟨⟨fun h => hloop f (h.trans ht.symm), .single ⟨f, hgmem.1, Or.inr ⟨rfl, ht⟩⟩⟩,
        ht ▸ hwT⟩
  · ext x
    simp only [Set.mem_preimage, hT_def, Set.mem_ofPred_eq, nodeBlock]
    exact ⟨fun h => h.2, fun h => ⟨fun hx => h0 ((hN.1.leaves w).2 ⟨x, hx⟩), h⟩⟩

end Banos2019
