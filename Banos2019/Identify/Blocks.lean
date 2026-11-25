module

public import Banos2019.Identify.HybridBlock

/-!
# The blocks of a cycle of `N⁻` (Baños 2019, Sections 3, 7 and 8)

Removing the edges of a cycle `C` of `N⁻` leaves one connected component through each node of `C`,
and each component holds at least one taxon: the blocks of `C` are the taxa of these components, one
block for each node of `C`, and the block of the hybrid node is the set of taxa descending from it. The
proofs of Sections 8 and 9 use these facts throughout, without stating them.

* `blockNode G C x`: the node of `C` whose block contains `x`; `sameBlock_iff_blockNode_eq`,
  `exists_blockNode_eq`, `blockNode_eq_iff_descendsFrom`.
* `separatesQuartet_iff`: the cycle `C` separates `s` when `blockNode` is injective on `s` and sends a
  taxon of `s` to the hybrid node; `four_le_ncard_of_separatesQuartet`.
* `exists_separatesQuartet_of_not_sameBlock`: two taxa in different blocks of a cycle of size at least
  four are in a set of four taxa that the cycle separates.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Blocks

variable {N : RootedNetwork V E X} [Finite E] {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}

/-- The node of the cycle `C` whose block contains the taxon `x`. -/
def blockNode {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (x : X') : V' :=
  @Classical.epsilon V' ⟨G.leaf x⟩ fun u => u ∈ cycleNodes G.graph C ∧ x ∈ nodeBlock G.graph G.leaf C u

omit [Finite E] in
theorem blockNode_spec {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) (x : X) :
    blockNode (unrooted N hN hX) C x ∈ cycleNodes (unrooted N hN hX).graph C ∧
      x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C
        (blockNode (unrooted N hN hX) C x) := by
  obtain ⟨u, hu, hux⟩ := exists_walks_compl_cycleNodes (unrooted_isConnected hN hX) hC
    ((unrooted N hN hX).leaf x)
  exact Classical.epsilon_spec (p := fun u => u ∈ cycleNodes (unrooted N hN hX).graph C ∧
    x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u) ⟨u, hu, hux⟩

omit [Finite E] in
theorem blockNode_mem {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) (x : X) :
    blockNode (unrooted N hN hX) C x ∈ cycleNodes (unrooted N hN hX).graph C :=
  (blockNode_spec hC x).1

/-- The block of `x` is that of the node `blockNode C x` only. -/
theorem eq_blockNode (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {u}
    (hu : u ∈ cycleNodes (unrooted N hN hX).graph C) {x : X}
    (hx : x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u) :
    u = blockNode (unrooted N hN hX) C x :=
  (unrooted_isLevelOne hN h1 hX).eq_of_walks_compl hC hu (blockNode_mem hC x)
    (hx.trans (DirectedMultigraph.walks_symm _ (blockNode_spec hC x).2))

/-- **Two taxa are in the same block of `C` exactly when their blocks are those of the same node.** -/
theorem sameBlock_iff_blockNode_eq (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) (x y : X) :
    SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y ↔
      blockNode (unrooted N hN hX) C x = blockNode (unrooted N hN hX) C y := by
  constructor
  · intro h
    exact eq_blockNode h1 hC (blockNode_mem hC x) ((blockNode_spec hC x).2.trans h)
  · intro h
    have hx := (blockNode_spec hC x).2
    have hy := (blockNode_spec hC y).2
    rw [h] at hx
    exact (DirectedMultigraph.walks_symm _ hx).trans hy

/-- **Every node of a cycle is the node of the block of a taxon.** -/
theorem exists_blockNode_eq (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {u}
    (hu : u ∈ cycleNodes (unrooted N hN hX).graph C) : ∃ x, blockNode (unrooted N hN hX) C x = u := by
  obtain ⟨x, hx⟩ := nodeBlock_nonempty_unrooted h1 hC hu
  exact ⟨x, (eq_blockNode h1 hC hu hx).symm⟩

/-- **A taxon is in the block of the hybrid node exactly when it descends from it.** -/
theorem blockNode_eq_iff_descendsFrom (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {v}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (x : X) :
    blockNode (unrooted N hN hX) C x = v ↔ DescendsFrom (unrooted N hN hX) v x := by
  rw [← mem_nodeBlock_iff_descendsFrom h1 hC hv]
  constructor
  · rintro rfl
    exact (blockNode_spec hC x).2
  · intro hx
    exact (eq_blockNode h1 hC hv.mem_cycleNodes hx).symm

/-- **The cycle `C` separates `s`** when the nodes of the blocks of the taxa of `s` are distinct and
one of them is the hybrid node. -/
theorem separatesQuartet_iff (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {v}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (s : Finset X) :
    SeparatesQuartet (unrooted N hN hX) C v s ↔
      Set.InjOn (blockNode (unrooted N hN hX) C) s ∧
        ∃ x ∈ s, blockNode (unrooted N hN hX) C x = v := by
  unfold SeparatesQuartet
  simp only [sameBlock_iff_blockNode_eq h1 hC, blockNode_eq_iff_descendsFrom h1 hC hv]
  constructor
  · rintro ⟨-, -, hinj, hx⟩
    exact ⟨fun x hx y hy hxy => by_contra fun h => hinj x hx y hy h hxy, hx⟩
  · rintro ⟨hinj, hx⟩
    exact ⟨hC, hv, fun x hx y hy hne h => hne (hinj hx hy h), hx⟩

/-- **Two taxa in different blocks of a cycle of size at least four are in a set of four taxa that the
cycle separates**: add taxa from two more blocks, one of them the hybrid block when neither taxon is in
it. -/
theorem exists_separatesQuartet_of_not_sameBlock [DecidableEq X] (h1 : IsLevelOne N.graph)
    {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : 4 ≤ C.ncard) {v}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) {x y : X}
    (hxy : ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) :
    ∃ c d, #({x, y, c, d} : Finset X) = 4 ∧ SeparatesQuartet (unrooted N hN hX) C v {x, y, c, d} := by
  rw [sameBlock_iff_blockNode_eq h1 hC] at hxy
  set β := blockNode (unrooted N hN hX) C
  have hne : ∀ {a b : X}, β a ≠ β b → a ≠ b := fun h h' => h (h' ▸ rfl)
  have h2 : ({β x, β y} : Set _).ncard = 2 := Set.ncard_pair hxy
  -- a third node, the hybrid node if it is not that of `x` or `y`
  obtain ⟨u₃, hu₃, hu₃xy, hvu₃⟩ : ∃ u₃ ∈ cycleNodes (unrooted N hN hX).graph C,
      u₃ ∉ ({β x, β y} : Set _) ∧ (v = β x ∨ v = β y ∨ v = u₃) := by
    by_cases hvxy : v = β x ∨ v = β y
    · obtain ⟨u₃, hu₃, hu₃xy⟩ :=
        hC.exists_mem_cycleNodes_notMem (Set.toFinite {β x, β y}) (by omega)
      exact ⟨u₃, hu₃, hu₃xy, hvxy.elim Or.inl (Or.inr ∘ Or.inl)⟩
    · refine ⟨v, hv.mem_cycleNodes, ?_, Or.inr (Or.inr rfl)⟩
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hvxy
  have h3 : ({u₃, β x, β y} : Set _).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hu₃xy, h2]
  obtain ⟨u₄, hu₄, hu₄xy⟩ :=
    hC.exists_mem_cycleNodes_notMem (Set.toFinite {u₃, β x, β y}) (by omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu₃xy hu₄xy
  obtain ⟨c, rfl⟩ := exists_blockNode_eq h1 hC hu₃
  obtain ⟨d, rfl⟩ := exists_blockNode_eq h1 hC hu₄
  obtain ⟨hcx, hcy⟩ := hu₃xy
  obtain ⟨hdc, hdx, hdy⟩ := hu₄xy
  refine ⟨c, d, card_four_of_ne (hne hxy) (hne (Ne.symm hcx)) (hne (Ne.symm hdx))
    (hne (Ne.symm hcy)) (hne (Ne.symm hdy)) (hne (Ne.symm hdc)),
    (separatesQuartet_iff h1 hC hv _).2 ⟨injOn_four hxy (Ne.symm hcx) (Ne.symm hdx) (Ne.symm hcy)
      (Ne.symm hdy) (Ne.symm hdc), ?_⟩⟩
  rcases hvu₃ with h | h | h
  · exact ⟨x, by simp, h.symm⟩
  · exact ⟨y, by simp, h.symm⟩
  · exact ⟨c, by simp, h.symm⟩

/-- A cycle separating four taxa has at least four nodes, so size at least four. -/
theorem four_le_ncard_of_separatesQuartet (h1 : IsLevelOne N.graph) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v} (hv : IsHybridNodeOf (unrooted N hN hX) C v)
    {s : Finset X} (hs : #s = 4) (hsep : SeparatesQuartet (unrooted N hN hX) C v s) :
    4 ≤ C.ncard := by
  have := hN.1.finite_vertices
  have hinj := ((separatesQuartet_iff h1 hC hv s).1 hsep).1
  rw [← ncard_cycleNodes hC, ← hs, ← Set.ncard_coe_finset, ← hinj.ncard_image]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨x, -, rfl⟩
  exact blockNode_mem hC x

end Blocks

end Banos2019
