module

public import Banos2019.CycleProperty

/-!
# The blocks of a cycle of `N⁻` (Baños 2019, Sections 3, 7 and 8)

Removing the edges of a cycle `C` of `N⁻` leaves one connected component through each node of `C`,
and each component holds at least one taxon: the blocks of `C` are the taxa of these components, one
block for each node of `C`, and the block of the hybrid node is the set of taxa descending from it. The
proofs of Sections 8 and 9 use these facts throughout, without stating them.

* `unrooted_isConnected`, `unrooted_isLevelOne`: `N⁻` is connected and level-1.
* `exists_isHybridNodeOf`, `IsHybridNodeOf.eq`, `IsHybridNodeOf.cycle_eq`: a cycle of `N⁻` has exactly
  one hybrid node, and a hybrid node lies on one cycle (Lemma 3).
* `ncard_cycleNodes`: a cycle of size `k` has `k` nodes.
* `blockNode G C x`: the node of `C` whose block contains `x`; `sameBlock_iff_blockNode_eq`,
  `exists_blockNode_eq`, `blockNode_eq_iff_descendsFrom`.
* `separatesQuartet_iff`: the cycle `C` separates `s` when `blockNode` is injective on `s` and sends a
  taxon of `s` to the hybrid node.
* `blockNodes`, `JoinedAvoiding`: the blocks of `x` and `y` are joined along `C` avoiding the blocks of
  the taxa `T`; `adjacentBlocks_iff_forall_joinedAvoiding`: two blocks are adjacent exactly when they
  are so joined for every set of four taxa separated by `C` that contains them.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Cycles of a directed multigraph -/

section Multigraph

variable {G : DirectedMultigraph V E}

/-- A cycle of size `k` has `k` nodes. -/
theorem ncard_cycleNodes {C : Set E} (hC : IsCycle G C) : (cycleNodes G C).ncard = C.ncard := by
  obtain ⟨k, v, e, hC, rfl⟩ := hC
  have hnodes : cycleNodes G (Set.range e) = Set.range v := by
    ext u
    constructor
    · rintro ⟨f, ⟨i, rfl⟩, hu⟩
      rcases hC.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hu with hu | hu
      · exact ⟨i, h₁.symm.trans hu⟩
      · exact ⟨_, h₂.symm.trans hu⟩
      · exact ⟨_, h₁.symm.trans hu⟩
      · exact ⟨i, h₂.symm.trans hu⟩
    · rintro ⟨i, rfl⟩
      rcases hC.joins i with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact ⟨e i, ⟨i, rfl⟩, Or.inl h₁⟩
      · exact ⟨e i, ⟨i, rfl⟩, Or.inr h₂⟩
  rw [hnodes, Set.ncard_range_of_injective hC.injective_node,
    Set.ncard_range_of_injective hC.injective_edge]

/-- The nodes of a cycle form a nonempty set. -/
theorem IsCycle.cycleNodes_nonempty {C : Set E} (hC : IsCycle G C) : (cycleNodes G C).Nonempty := by
  obtain ⟨k, v, e, hC, rfl⟩ := hC
  exact ⟨G.source (e ⟨0, hC.pos⟩), e ⟨0, hC.pos⟩, ⟨_, rfl⟩, Or.inl rfl⟩

/-- Taxa in the same block of a set of edges are in the same block of a smaller set. -/
theorem SameBlock.mono {ℓ : X → V} {D D' : Set E} (hD : D ⊆ D') {x y : X}
    (h : SameBlock G ℓ D' x y) : SameBlock G ℓ D x y :=
  Relation.ReflTransGen.mono (fun _ _ ⟨f, hf, hl⟩ => ⟨f, fun hfD => hf (hD hfD), hl⟩) _ _ h

/-- A cycle has a node outside a set with fewer elements than the size of the cycle. -/
theorem IsCycle.exists_mem_cycleNodes_notMem {C : Set E} (hC : IsCycle G C) {F : Set V}
    (hF : F.Finite) (h : F.ncard < C.ncard) : ∃ u ∈ cycleNodes G C, u ∉ F :=
  Set.exists_mem_notMem_of_ncard_lt_ncard (by rwa [ncard_cycleNodes hC]) hF

/-- **In a connected graph, every node is joined to a node of a cycle `C` by a walk avoiding the edges
of `C`**: along a walk to a node of `C`, stop at the first node of `C`. -/
theorem exists_walks_compl_of_isConnected (hG : G.IsConnected) {C : Set E} (hC : IsCycle G C)
    (a : V) : ∃ u ∈ cycleNodes G C, G.Walks Cᶜ u a := by
  obtain ⟨u₀, hu₀⟩ := hC.cycleNodes_nonempty
  have hw := hG a u₀
  induction hw using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨u₀, hu₀, .refl⟩
  | @head a b hab _ ih =>
    obtain ⟨u, hu, hub⟩ := ih
    obtain ⟨f, -, hf⟩ := hab
    by_cases hfC : f ∈ C
    · refine ⟨a, ?_, .refl⟩
      rcases hf with ⟨h, -⟩ | ⟨-, h⟩
      · exact ⟨f, hfC, Or.inl h⟩
      · exact ⟨f, hfC, Or.inr h⟩
    · exact ⟨u, hu, hub.tail ⟨f, hfC, hf.symm⟩⟩

/-- **In a level-1 graph, two nodes of a cycle `C` joined by a walk avoiding the edges of `C` are
equal**: otherwise the walk and an arc of `C` would close a second cycle through an edge of `C`. -/
theorem eq_of_walks_compl_of_isLevelOne (h1 : IsLevelOne G) {C : Set E} (hC : IsCycle G C)
    {u w : V} (hu : u ∈ cycleNodes G C) (hw : w ∈ cycleNodes G C) (huw : G.Walks Cᶜ u w) :
    u = w := by
  sorry

end Multigraph

/-! ### Four distinct elements -/

section Four

variable {α β : Type*} [DecidableEq α]

/-- Four distinct elements make a set of four. -/
theorem card_four_of_ne {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : #({a, b, c, d} : Finset α) = 4 := by
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
    card_pair hcd]

/-- A map taking four elements to four distinct values is injective on them. -/
theorem injOn_four {f : α → β} {a b c d : α} (hab : f a ≠ f b) (hac : f a ≠ f c) (had : f a ≠ f d)
    (hbc : f b ≠ f c) (hbd : f b ≠ f d) (hcd : f c ≠ f d) :
    Set.InjOn f ↑({a, b, c, d} : Finset α) := by
  intro x hx y hy hxy
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first | rfl | exact absurd hxy ‹_› | exact absurd hxy.symm ‹_›

/-- Four elements making a set of four are distinct. -/
theorem distinct4_of_card_eq_four {a b c d : α} (h : #({a, b, c, d} : Finset α) = 4) :
    Distinct4 a b c d := by
  have h3 : ∀ p q r : α, #({p, q, r} : Finset α) ≤ 3 := fun p q r => card_le_three
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · have := h3 a c d
    simp_all
  · have := h3 a b d
    rw [show ({a, b, a, d} : Finset α) = {a, b, d} by ext; simp; tauto] at h
    omega
  · have := h3 a b c
    rw [show ({a, b, c, a} : Finset α) = {a, b, c} by ext; simp; tauto] at h
    omega
  · have := h3 a b d
    rw [show ({a, b, b, d} : Finset α) = {a, b, d} by ext; simp] at h
    omega
  · have := h3 a b c
    rw [show ({a, b, c, b} : Finset α) = {a, b, c} by ext; simp; tauto] at h
    omega
  · have := h3 a b c
    rw [show ({a, b, c, c} : Finset α) = {a, b, c} by ext; simp] at h
    omega

/-- Four distinct elements make a set of four. -/
theorem card_eq_four_of_distinct4 {a b c d : α} (h : Distinct4 a b c d) :
    #({a, b, c, d} : Finset α) = 4 :=
  card_four_of_ne h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

end Four

/-! ### `N⁻` is connected and level-1 -/

section Unrooted

variable {N : RootedNetwork V E X}

/-- **`N⁻` is connected.** -/
theorem unrooted_isConnected (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X) :
    (unrooted N hN hX).graph.IsConnected := by
  sorry

variable [Finite E]

/-- **`N⁻` is level-1**: two cycles sharing an edge share its ends, and two cycles with a common node
are the same (Lemma 3). -/
theorem unrooted_isLevelOne (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) : IsLevelOne (unrooted N hN hX).graph := by
  rintro C C' hC hC' ⟨f, hf, hf'⟩
  exact (lemma3_unrooted hN h1 hX hC).2.2 C' hC'
    ⟨_, ⟨f, hf, Or.inl rfl⟩, ⟨f, hf', Or.inl rfl⟩⟩

variable {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}

/-- **A cycle of `N⁻` has a hybrid node** (Lemma 3). -/
theorem exists_isHybridNodeOf (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) :
    ∃ v, IsHybridNodeOf (unrooted N hN hX) C v := by
  obtain ⟨⟨v, ⟨-, h₁, h₂, hne, hd₁, hd₂, ht₁, ht₂⟩, -⟩, h2, -⟩ := lemma3_unrooted hN h1 hX hC
  obtain ⟨v, hv, -⟩ := (lemma3_unrooted hN h1 hX hC).1
  obtain ⟨hvC, g₁, g₂, hne, hd₁, hd₂, ht₁, ht₂⟩ := hv
  exact ⟨v, g₁, h2 v hvC g₁ hd₁ ht₁, g₂, h2 v hvC g₂ hd₂ ht₂, hne, hd₁, hd₂, ht₁, ht₂⟩

/-- The hybrid node of a cycle is a node of the cycle. -/
theorem IsHybridNodeOf.mem_cycleNodes {V' E' X' : Type*} {G : SemidirectedNetwork V' E' X'}
    {C : Set E'} {v : V'} (hv : IsHybridNodeOf G C v) : v ∈ cycleNodes G.graph C := by
  obtain ⟨g, hg, -, -, -, -, -, hgt, -⟩ := hv
  exact ⟨g, hg, Or.inr hgt⟩

/-- **A cycle of `N⁻` has only one hybrid node** (Lemma 3). -/
theorem IsHybridNodeOf.eq (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {v v'}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hv' : IsHybridNodeOf (unrooted N hN hX) C v') :
    v = v' := by
  obtain ⟨v₀, -, huniq⟩ := (lemma3_unrooted hN h1 hX hC).1
  have key : ∀ u, IsHybridNodeOf (unrooted N hN hX) C u → u = v₀ := fun u hu => by
    obtain ⟨g₁, hg₁, g₂, hg₂, hne, hd₁, hd₂, ht₁, ht₂⟩ := hu
    exact huniq u ⟨⟨g₁, hg₁, Or.inr ht₁⟩, g₁, g₂, hne, hd₁, hd₂, ht₁, ht₂⟩
  rw [key v hv, key v' hv']

/-- **A hybrid node of `N⁻` lies on only one cycle** (Lemma 3). -/
theorem IsHybridNodeOf.cycle_eq (h1 : IsLevelOne N.graph) {C C' : Set _} (hC : IsCycle (unrooted N hN hX).graph C)
    (hC' : IsCycle (unrooted N hN hX).graph C') {v} (hv : IsHybridNodeOf (unrooted N hN hX) C v)
    (hv' : IsHybridNodeOf (unrooted N hN hX) C' v) : C = C' :=
  (lemma3_unrooted hN h1 hX hC).2.2 C' hC' ⟨v, hv.mem_cycleNodes, hv'.mem_cycleNodes⟩

end Unrooted

/-! ### The blocks of a cycle of `N⁻` -/

section Blocks

variable {N : RootedNetwork V E X} [Finite E] {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}

/-- **Every node of a cycle of `N⁻` has a taxon in its block**: what hangs from the node, off the
cycle, ends at taxa. -/
theorem nodeBlock_nonempty (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {u}
    (hu : u ∈ cycleNodes (unrooted N hN hX).graph C) :
    (nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u).Nonempty := by
  sorry

/-- **The block of the hybrid node is the set of taxa descending from it**: a semidirected path from
the hybrid node leaves it by its child edge and does not come back to the cycle. -/
theorem mem_nodeBlock_iff_descendsFrom (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {v}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (x : X) :
    x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C v ↔
      DescendsFrom (unrooted N hN hX) v x := by
  sorry

/-- The node of the cycle `C` whose block contains the taxon `x`. -/
def blockNode {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (x : X') : V' :=
  @Classical.epsilon V' ⟨G.leaf x⟩ fun u => u ∈ cycleNodes G.graph C ∧ x ∈ nodeBlock G.graph G.leaf C u

omit [Finite E] in
theorem blockNode_spec {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) (x : X) :
    blockNode (unrooted N hN hX) C x ∈ cycleNodes (unrooted N hN hX).graph C ∧
      x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C
        (blockNode (unrooted N hN hX) C x) := by
  obtain ⟨u, hu, hux⟩ := exists_walks_compl_of_isConnected (unrooted_isConnected hN hX) hC
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
  eq_of_walks_compl_of_isLevelOne (unrooted_isLevelOne hN h1 hX) hC hu (blockNode_mem hC x)
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
  obtain ⟨x, hx⟩ := nodeBlock_nonempty h1 hC hu
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

/-! ### The order of the blocks around a cycle -/

/-- The nodes of the cycle `C` whose blocks contain a taxon of `T`. -/
def blockNodes {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (T : Set X') :
    Set V' :=
  {u | u ∈ cycleNodes G.graph C ∧ ∃ x ∈ T, x ∈ nodeBlock G.graph G.leaf C u}

/-- The blocks of `x` and `y` are *joined along `C` avoiding the blocks of `T`*: in the cycle `C` with
the nodes of the blocks of the taxa of `T` removed, the nodes of the blocks of `x` and `y` are
connected. -/
def JoinedAvoiding {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (T : Set X')
    (x y : X') : Prop :=
  ∃ u w, u ∈ cycleNodes G.graph C ∧ w ∈ cycleNodes G.graph C ∧
    x ∈ nodeBlock G.graph G.leaf C u ∧ y ∈ nodeBlock G.graph G.leaf C w ∧
    Relation.ReflTransGen
      (fun a b => G.graph.AdjOn C a b ∧ a ∉ blockNodes G C T ∧ b ∉ blockNodes G C T) u w

/-- **Two blocks of a cycle of size at least four are adjacent exactly when they are joined avoiding
the other two blocks of every set of four taxa that the cycle separates and that contains them.**
Adjacent blocks are joined by their edge. Two blocks that are not adjacent leave a node on each of the
two arcs of the cycle between them, the hybrid node among them when it is not one of the two; taxa in
the blocks of these nodes separate them. -/
theorem adjacentBlocks_iff_forall_joinedAvoiding [DecidableEq X] (h1 : IsLevelOne N.graph) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : 4 ≤ C.ncard) {v}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (x y : X) :
    AdjacentBlocks (unrooted N hN hX) C x y ↔
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y ∧
        ∀ z z', #({x, y, z, z'} : Finset X) = 4 →
          SeparatesQuartet (unrooted N hN hX) C v {x, y, z, z'} →
          JoinedAvoiding (unrooted N hN hX) C {z, z'} x y := by
  sorry

end Blocks

end Banos2019
