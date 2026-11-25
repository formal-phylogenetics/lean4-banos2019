module

public import Banos2019.Identify.CycleOrder

/-!
# The cycles of `Q⁻_s` and those of `N⁻` (Baños 2019, Sections 7–9)

The cycles of the induced quartet network `Q⁻_s` come from the cycles of `N⁻`: a cycle `C_v` of `N⁻`
whose hybrid block contains a taxon of `s` and whose blocks contain taxa of `s` from at least two
blocks induces a cycle of `Q⁻_s`, with hybrid node `v`; its nodes are the nodes of `C_v` whose blocks
contain taxa of `s`, in the same order around the cycle, and its blocks are the traces of those blocks
on `s`. The paper uses this throughout Sections 7–9 ("since the other taxa are in distinct `v`-blocks
of `Q⁻_abcd`, they must be in distinct `v`-blocks of `N⁻`", proof of Lemma 12; "the 4-cycle in
`Q⁻_abcd` and the 3-cycle in `Q⁻_abce`", proof of Proposition 13).

* `determines_iff_separatesQuartet`: `s` determines the hybrid node `v` of `N⁻` (the 4-cycle of `Q⁻_s`
  has hybrid node `v`) exactly when the cycle `C_v` separates `s`.
* `adjacentBlocks_quartetUnrooted_iff`: in the 4-cycle of `Q⁻_s`, the blocks of `a` and `c` are
  adjacent exactly when, in `C_v`, they are joined avoiding the blocks of the other two taxa of `s`.
* `exists_cycle_of_hasThreeTwoCycle`: a `3₂`-cycle of `Q⁻_s` comes from a cycle of `N⁻` in which the
  two taxa of `s` below its hybrid node are in the hybrid block and the other two in two other
  distinct blocks.

The proofs pass through the cycles of `N`. `Q⊕_s` is the part of `N` below `LSA(s)` ancestral to `s`
(`quartetBelow`) with its vertices of indegree one and outdegree one suppressed, and `Q⁻_s` is
`(Q⊕_s)⁻`.

* `isCycle_suppressChainArcs`, `isLevelOne_suppress`: the chains of the arcs of a cycle of a
  suppressed network form a cycle of the network, and a suppressed level-1 network is level-1; so
  `Q⊕_s` is level-1 (`isLevelOne_quartetLSA_graph`).
* `unrootedCycleArcs`, `isCycle_unrootedCycleArcs`: the cycle of `M` of a cycle of `M⁻`, through
  `LSA(X)` when it has the edge merged there.
* `mem_nodeBlock_of_reaches_offCycle`, `exists_reaches_offCycle_of_mem_nodeBlock`: the block of a
  node of a cycle of `M⁻`, other than the top of its cycle of `M`, is the set of taxa below its arcs
  off the cycle.
* `exists_isHybridNodeOf_of_indegree_eq_two`: a node of `M⁻` entered by two arcs of `M` is the
  hybrid node of a cycle of `M⁻`.
* `unrootedCycleArcs_eq_image_quartet`, `quartetNode_blockNode`: for a cycle of `Q⁻_s` and the cycle
  of `N⁻` with the same hybrid node, the cycle of `N` of the second is made of the chains of the
  first, and each taxon of `s` is in the block of the same node of `N` in both.
* `reflTransGen_unrooted_of_joins_quartet`, `IsCycle.not_joined_three`: an edge of the cycle of
  `Q⁻_s` is a path along the cycle of `N⁻` through nodes that are not nodes of `Q⁻_s`, and of four
  nodes of a cycle, two are opposite, separated by the other two.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-! ### Cycles of a directed multigraph -/

section CycleGraph

variable {V' E' : Type*} {G : DirectedMultigraph V' E'}

/-- **A cycle can be read so that a given edge is its last one.** -/
theorem IsCycle.exists_isCycleOf_last {C : Set E'} (hC : IsCycle G C) {f : E'} (hf : f ∈ C) :
    ∃ (n : ℕ) (v : Fin (n + 1) → V') (e : Fin (n + 1) → E'), IsCycleOf G (n + 1) v e ∧
      Set.range e = C ∧ e (Fin.last n) = f := by
  obtain ⟨k, v, e, hcyc, rfl⟩ := hC
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hcyc.pos; omega⟩
  obtain ⟨j, rfl⟩ := hf
  refine ⟨n, _, _, hcyc.rotate (j + 1), (Equiv.addRight (j + 1)).surjective.range_comp e, ?_⟩
  congr 1
  rw [add_comm j 1, ← add_assoc, Fin.last_add_one, zero_add]

/-- **A cycle contains no other cycle**: a cycle whose edges are edges of the cycle `C` misses no
edge of `C`, since `C` without one of its edges is a path. -/
theorem IsCycle.eq_of_subset {C C' : Set E'} (hC : IsCycle G C) (hC' : IsCycle G C')
    (h : C' ⊆ C) : C' = C := by
  by_contra hne
  obtain ⟨f, hfC, hfC'⟩ := Set.not_subset.1 fun h' => hne (Set.Subset.antisymm h h')
  obtain ⟨n, v, e, hcyc, rfl, hlast⟩ := hC.exists_isCycleOf_last hfC
  refine hcyc.isPathOf.not_subset_of_isCycle hC' fun g hg => ?_
  obtain ⟨i, rfl⟩ := h hg
  induction i using Fin.lastCases with
  | last => exact absurd (hlast ▸ hg) hfC'
  | cast l => exact ⟨l, rfl⟩

/-- **A cycle without one of its edges joins the ends of that edge.** -/
theorem IsCycle.walks_diff_singleton {C : Set E'} (hC : IsCycle G C) {f : E'} (hf : f ∈ C) :
    G.Walks (C \ {f}) (G.target f) (G.source f) := by
  obtain ⟨n, v, e, hcyc, rfl, hlast⟩ := hC.exists_isCycleOf_last hf
  have hW : G.Walks (Set.range e \ {f}) (v 0) (v (Fin.last n)) := by
    refine walks_mono ?_ (hcyc.isPathOf.walks_of_le (Fin.zero_le _))
    rintro g ⟨l, -, -, rfl⟩
    refine ⟨⟨_, rfl⟩, fun h => ?_⟩
    rw [Set.mem_singleton_iff, ← hlast] at h
    exact (Fin.castSucc_lt_last l).ne (hcyc.injective_edge h)
  have hj := hcyc.joins (Fin.last n)
  rw [finRotate_last, hlast] at hj
  rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
    exact hW
  · rw [h₁, h₂]
    exact G.walks_symm hW

/-- A relation's reflexive transitive closure is symmetric when the relation is. -/
theorem reflTransGen_symm_of_symm {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a)
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.head (hr _ _ hbc)

/-- **Of four nodes of a cycle, the three pairs `p₁ p₂`, `p₂ p₃`, `p₁ p₃` are not all joined along
the cycle avoiding the other two nodes**: one of these pairs is a pair of opposite nodes, separated
by the other two. -/
theorem IsCycle.not_joined_three {C : Set E'} (hC : IsCycle G C) {p₁ p₂ p₃ p₄ : V'}
    (hp₁ : p₁ ∈ cycleNodes G C) (hp₂ : p₂ ∈ cycleNodes G C) (hp₃ : p₃ ∈ cycleNodes G C)
    (hp₄ : p₄ ∈ cycleNodes G C) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h14 : p₁ ≠ p₄) (h23 : p₂ ≠ p₃)
    (h24 : p₂ ≠ p₄) (h34 : p₃ ≠ p₄) {F₁ F₂ F₃ : Set V'} (hF₁ : p₃ ∈ F₁ ∧ p₄ ∈ F₁)
    (hF₂ : p₁ ∈ F₂ ∧ p₄ ∈ F₂) (hF₃ : p₂ ∈ F₃ ∧ p₄ ∈ F₃)
    (hj₁₂ : Relation.ReflTransGen (fun a b => G.AdjOn C a b ∧ a ∉ F₁ ∧ b ∉ F₁) p₁ p₂)
    (hj₂₃ : Relation.ReflTransGen (fun a b => G.AdjOn C a b ∧ a ∉ F₂ ∧ b ∉ F₂) p₂ p₃)
    (hj₁₃ : Relation.ReflTransGen (fun a b => G.AdjOn C a b ∧ a ∉ F₃ ∧ b ∉ F₃) p₁ p₃) : False := by
  obtain ⟨n, v, e, hcyc, rfl, h0⟩ := hC.exists_isCycleOf_apply_zero hp₁
  rw [hcyc.cycleNodes_eq] at hp₂ hp₃ hp₄
  obtain ⟨i, rfl⟩ := hp₂
  obtain ⟨j, rfl⟩ := hp₃
  obtain ⟨k, rfl⟩ := hp₄
  subst h0
  have key : ∀ {a b c d : Fin (n + 1)} {F : Set V'}, v c ∈ F → v d ∈ F →
      Relation.ReflTransGen (fun x y => G.AdjOn (Set.range e) x y ∧ x ∉ F ∧ y ∉ F) (v a) (v b) →
      ((c : ℕ) < a ∧ (a : ℕ) < d ↔ (c : ℕ) < b ∧ (b : ℕ) < d) := by
    intro a b c d F hc hd h
    have := hcyc.mem_image_Ioo_iff_of_reflTransGen hc hd h
    rwa [hcyc.injective_node.mem_set_image, hcyc.injective_node.mem_set_image, Set.mem_Ioo,
      Set.mem_Ioo, Fin.lt_def, Fin.lt_def, Fin.lt_def, Fin.lt_def] at this
  have hne : ∀ {a b : Fin (n + 1)}, v a ≠ v b → (a : ℕ) ≠ b := fun h h' =>
    h (congrArg v (Fin.ext h'))
  have hi := hne h12
  have hj := hne h13
  have hk := hne h14
  have hij := hne h23
  have hik := hne h24
  have hjk := hne h34
  simp only [Fin.val_zero] at hi hj hk
  have A₁ := key (a := 0) (b := i) (c := j) (d := k) hF₁.1 hF₁.2 hj₁₂
  have A₂ := key (a := 0) (b := i) (c := k) (d := j) hF₁.2 hF₁.1 hj₁₂
  have B₁ := key (a := i) (b := j) (c := 0) (d := k) hF₂.1 hF₂.2 hj₂₃
  have C₁ := key (a := 0) (b := j) (c := i) (d := k) hF₃.1 hF₃.2 hj₁₃
  have C₂ := key (a := 0) (b := j) (c := k) (d := i) hF₃.2 hF₃.1 hj₁₃
  simp only [Fin.val_zero] at A₁ A₂ B₁ C₁ C₂
  omega

end CycleGraph

/-! ### Arcs off a cycle of a rooted network -/

section RootedCycle

variable {V' E' X' : Type*} {M : RootedNetwork V' E' X'}

/-- **A taxon is not a node of a cycle**: a node of a cycle is on two of its edges, and a taxon is
on one arc only. -/
theorem IsCycle.leaf_notMem_cycleNodes (hM : M.IsPhylogenetic) {C : Set E'}
    (hC : IsCycle M.graph C) (x : X') : M.leaf x ∉ cycleNodes M.graph C := by
  have := hM.finite_arcs
  intro hx
  obtain ⟨f₁, hf₁, f₂, hf₂, h12, hu₁, hu₂⟩ := hC.exists_ne_of_mem
    (fun f _ h => hM.acyclic _ (.single ⟨f, rfl, h.symm⟩)) hx
  have hout := (M.graph.outdegree_eq_zero_iff _).1 ((hM.leaves _).2 ⟨x, rfl⟩)
  have h2 : 2 ≤ M.graph.indegree (M.leaf x) := by
    unfold DirectedMultigraph.indegree
    rw [← Set.ncard_pair h12]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro g (rfl | rfl)
    exacts [hu₁.resolve_left (hout _), hu₂.resolve_left (hout _)]
  have := hM.leaf_indegree x
  omega

/-- **Two arcs off a cycle leaving the same node of it are equal** in a binary network: the node is
on two edges of the cycle, and has degree at most three. -/
theorem IsCycle.eq_of_source_eq_of_notMem (hM : IsBinaryRootedNetwork M) {C : Set E'}
    (hC : IsCycle M.graph C) {u : V'} (hu : u ∈ cycleNodes M.graph C) {c c' : E'}
    (hc : c ∉ C) (hc' : c' ∉ C) (hcs : M.graph.source c = u) (hcs' : M.graph.source c' = u) :
    c = c' := by
  have := hM.1.finite_arcs
  by_contra hne
  obtain ⟨f₁, hf₁, f₂, hf₂, h12, hu₁, hu₂⟩ := hC.exists_ne_of_mem
    (fun f _ => source_ne_target_of_binary hM f) hu
  have hout : M.graph.outdegree u = 2 := le_antisymm (hM.outdegree_le_two u) (by
    unfold DirectedMultigraph.outdegree
    rw [← Set.ncard_pair hne]
    exact Set.ncard_le_ncard (by rintro g (rfl | rfl) <;> assumption) (Set.toFinite _))
  have hset := eq_or_eq_of_outdegree_eq_two hout hne hcs hcs'
  -- the two edges of `C` at `u` enter it
  have hin : ∀ f ∈ C, (M.graph.source f = u ∨ M.graph.target f = u) → M.graph.target f = u := by
    intro f hf hfu
    refine hfu.resolve_left fun hs => ?_
    have : f ∈ ({c, c'} : Set E') := by rw [← hset]; exact hs
    rcases this with rfl | rfl
    exacts [hc hf, hc' hf]
  have h2 := two_le_indegree_of_two_targets hM h12 (hin f₁ hf₁ hu₁) (hin f₂ hf₂ hu₂)
  have := hM.indegree_add_outdegree_le u
  omega

/-- **Below an arc off a cycle**: for an arc `c` off the cycle `C` of a level-1 network leaving a
node `u` of `C`, every vertex below `c` is joined to `u` by a walk avoiding `C`, and is not `u`. -/
theorem IsCycle.walks_compl_of_reaches_target (hM : M.IsPhylogenetic) (h1 : IsLevelOne M.graph)
    {C : Set E'} (hC : IsCycle M.graph C) {u : V'} (hu : u ∈ cycleNodes M.graph C) {c : E'}
    (hc : c ∉ C) (hcs : M.graph.source c = u) {b : V'}
    (hb : M.graph.Reaches (M.graph.target c) b) : M.graph.Walks Cᶜ u b ∧ b ≠ u := by
  have hne : ∀ b, M.graph.Reaches (M.graph.target c) b → b ≠ u := fun b hb h =>
    hM.acyclic _ (Relation.TransGen.head' ⟨c, hcs, rfl⟩ (h ▸ hb))
  refine ⟨?_, hne b hb⟩
  induction hb with
  | refl => exact .single ⟨c, hc, Or.inl ⟨hcs, rfl⟩⟩
  | @tail a b hca hab ih =>
    obtain ⟨f, hfs, hft⟩ := hab
    have := (h1.walks_compl_ends hC hu ih (hne a hca) (Or.inl hfs)).2
    rwa [hft] at this

/-- Below an arc off a cycle leaving a node of the cycle, no vertex is a node of the cycle. -/
theorem IsCycle.notMem_cycleNodes_of_reaches_target (hM : M.IsPhylogenetic)
    (h1 : IsLevelOne M.graph) {C : Set E'} (hC : IsCycle M.graph C) {u : V'}
    (hu : u ∈ cycleNodes M.graph C) {c : E'} (hc : c ∉ C) (hcs : M.graph.source c = u) {b : V'}
    (hb : M.graph.Reaches (M.graph.target c) b) : b ∉ cycleNodes M.graph C := fun hbC => by
  obtain ⟨hw, hne⟩ := hC.walks_compl_of_reaches_target hM h1 hu hc hcs hb
  exact hne (h1.eq_of_walks_compl hC hbC hu (M.graph.walks_symm hw))

/-- **Below an arc off a cycle, vertices are entered only from below it**: for a node `u` of a
cycle `C` of a binary level-1 network other than its top `a` (`IsLevelOne.exists_top`), and an arc
`c` off `C` leaving `u`, an arc `g ≠ c` entering a vertex below `c` leaves a vertex below `c`.
Otherwise a path from the root to the source of `g`, after its last node of `C`, would join that
node to `u` avoiding `C`; that node would be `u`, and `u` would have two arcs off `C`, or the root
would reach `u` avoiding `C`, through an arc entering `u` off `C`. -/
theorem IsCycle.reaches_source_of_reaches_target (hM : IsBinaryRootedNetwork M)
    (h1 : IsLevelOne M.graph) {C : Set E'} (hC : IsCycle M.graph C) {a : V'}
    (hE : ∀ w ∈ cycleNodes M.graph C, w ≠ a → ∀ g, M.graph.target g = w → g ∈ C)
    (hroot : M.root ∈ cycleNodes M.graph C → M.root = a) {u : V'}
    (hu : u ∈ cycleNodes M.graph C) (hua : u ≠ a) {c : E'} (hc : c ∉ C)
    (hcs : M.graph.source c = u) {g : E'} (hgc : g ≠ c)
    (hg : M.graph.Reaches (M.graph.target c) (M.graph.target g)) :
    M.graph.Reaches (M.graph.target c) (M.graph.source g) := by
  obtain ⟨hw, hne⟩ := hC.walks_compl_of_reaches_target hM.1 h1 hu hc hcs hg
  have hgC : g ∉ C := h1.notMem_of_walks_compl hC hu hw hne (Or.inr rfl)
  have hws : M.graph.Walks Cᶜ u (M.graph.source g) := hw.tail ⟨g, hgC, Or.inr ⟨rfl, rfl⟩⟩
  rcases last_hit (C := C) (hM.1.root_reaches (M.graph.source g)) with h | ⟨c₂, hc₂, h⟩
  · -- the root reaches the source of `g` avoiding `C`, and a node of `C` avoiding `C`
    exfalso
    obtain ⟨c₃, hc₃, h₃⟩ : ∃ c₃ ∈ cycleNodes M.graph C,
        Relation.ReflTransGen (AdjOff M.graph C) M.root c₃ := by
      rcases first_hit (C := C) (hM.1.root_reaches u) with h' | h'
      · exact ⟨u, hu, h'⟩
      · exact h'
    have hu₃ := h1.eq_of_walks_compl hC hu hc₃
      (hws.trans ((M.graph.walks_symm (walks_of_adjOff h)).trans (walks_of_adjOff h₃)))
    rw [← hu₃] at h₃
    rcases Relation.ReflTransGen.cases_tail h₃ with h' | ⟨b, -, f, hf, -, hft⟩
    · exact hua (h'.trans (hroot (h' ▸ hu)))
    · exact hf (hE _ hu hua f hft)
  · have hu₂ := h1.eq_of_walks_compl hC hu hc₂ (hws.trans (M.graph.walks_symm (walks_of_adjOff h)))
    rw [← hu₂] at h
    rcases Relation.ReflTransGen.cases_head h with h' | ⟨b, ⟨f, hf, hfs, hft⟩, hb⟩
    · exact absurd (hC.eq_of_source_eq_of_notMem hM hu hgC hc h'.symm hcs) hgc
    · rw [hC.eq_of_source_eq_of_notMem hM hu hf hc hfs hcs] at hft
      rw [hft]
      exact reaches_of_adjOff hb

/-- **The top of a cycle is its only node entered by no edge of the cycle.** -/
theorem eq_top_of_forall_target_ne (hM : M.IsPhylogenetic) {C : Set E'} {a : V'}
    (hE : ∀ w ∈ cycleNodes M.graph C, w ≠ a → ∀ g, M.graph.target g = w → g ∈ C)
    (hroot : M.root ∈ cycleNodes M.graph C → M.root = a) {w : V'}
    (hw : w ∈ cycleNodes M.graph C) (hno : ∀ g ∈ C, M.graph.target g ≠ w) : w = a := by
  have := hM.finite_arcs
  by_contra hwa
  have hwr : w ≠ M.root := fun h => hwa (h.trans (hroot (h ▸ hw)))
  obtain ⟨g, hg⟩ := (M.graph.one_le_indegree_iff w).mp (hM.nonroot_indegree w hwr)
  exact hno g (hE w hw hwa g hg) hg

end RootedCycle

/-! ### Cycles of a suppressed network -/

section Suppress

variable {V' E' X' : Type*} {M : RootedNetwork V' E' X'}

/-- The arcs of `M` on the chains of a set `D` of arcs of the suppressed network `M.suppress`. -/
def suppressChainArcs (M : RootedNetwork V' E' X')
    (D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}) : Set E' :=
  {g | ∃ f ∈ D, M.IsOnChain f.1 g}

/-- An arc of the suppressed network is on the chains of `D` exactly when it is in `D`. -/
theorem mem_suppressChainArcs_iff (D : Set {e // ¬ M.IsChainVertex (M.graph.source e)})
    (f : {e // ¬ M.IsChainVertex (M.graph.source e)}) : f.1 ∈ suppressChainArcs M D ↔ f ∈ D := by
  constructor
  · rintro ⟨f', hf', h⟩
    rwa [Subtype.ext (IsOnChain.unique (Or.inl rfl) h f.2 f'.2)]
  · exact fun hf => ⟨f, hf, Or.inl rfl⟩

/-- **The chain of an arc of the suppressed network**: from the target of its first arc to any of
its vertices, along arcs of the chain, every step leaving a chain vertex. -/
theorem reflTransGen_chain_of_chainReach (f : {e // ¬ M.IsChainVertex (M.graph.source e)})
    {z : V'} (hz : M.ChainReach (M.graph.target f.1) z) :
    Relation.ReflTransGen (fun a b => ∃ g, M.IsOnChain f.1 g ∧ M.IsChainVertex a ∧
      M.graph.source g = a ∧ M.graph.target g = b) (M.graph.target f.1) z := by
  induction hz with
  | refl => exact .refl
  | @tail a b hfa hab ih =>
    obtain ⟨ha, g, hgs, hgt⟩ := hab
    exact ih.tail ⟨g, Or.inr ⟨by rw [hgs]; exact ha, by rw [hgs]; exact hfa⟩, ha, hgs, hgt⟩

/-- The chain of an arc of the suppressed network, with a property `P` of its vertices that holds
at every chain vertex and at the last vertex considered. -/
theorem reflTransGen_chain_targets (f : {e // ¬ M.IsChainVertex (M.graph.source e)})
    {P : V' → Prop} (hP : ∀ z, M.IsChainVertex z → P z) {z : V'}
    (hz : M.ChainReach (M.graph.target f.1) z) (hPz : P z) :
    Relation.ReflTransGen (fun a b => ∃ g, M.IsOnChain f.1 g ∧ M.graph.source g = a ∧
      M.graph.target g = b ∧ P b) (M.graph.target f.1) z := by
  induction hz with
  | refl => exact .refl
  | @tail a b hfa hab ih =>
    obtain ⟨ha, g, hgs, hgt⟩ := hab
    exact (ih (hP a ha)).tail ⟨g, Or.inr ⟨by rw [hgs]; exact ha, by rw [hgs]; exact hfa⟩, hgs,
      hgt, hPz⟩

/-- A path of the suppressed network gives a path of the network. -/
theorem reaches_val_of_suppress_reaches (hM : M.IsPhylogenetic) {a b : {v // ¬ M.IsChainVertex v}}
    (h : (M.suppress hM).graph.Reaches a b) : M.graph.Reaches a.1 b.1 := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, hfs, hft⟩ := hbc
    subst hfs hft
    exact ih.trans (Relation.ReflTransGen.head ⟨f.1, rfl, rfl⟩ (chainReach_chainEnd hM _).reaches)

/-- The end of a chain is the target of its last arc. -/
theorem chainEnd_eq_of_isOnChain (hM : M.IsPhylogenetic) {f g : E'} (h : M.IsOnChain f g)
    (hg : ¬ M.IsChainVertex (M.graph.target g)) :
    chainEnd hM (M.graph.target f) = M.graph.target g :=
  (h.chainEnd_eq hM).trans (chainEnd_eq_self hM hg)

/-- A path to a vertex that is not a chain vertex passes through the end of the chain of its
start. -/
theorem reaches_of_chainEnd_of_reaches (hM : M.IsPhylogenetic) {a b : V'}
    (h : M.graph.Reaches a b) (hb : ¬ M.IsChainVertex b) :
    M.graph.Reaches (chainEnd hM a) b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rw [chainEnd_eq_self hM hb]
    exact .refl
  | @head a a' haa' ha'b ih =>
    by_cases ha : M.IsChainVertex a
    · rw [chainEnd_eq_of_adj hM ha haa']
      exact ih
    · rw [chainEnd_eq_self hM ha]
      exact Relation.ReflTransGen.head haa' ha'b

/-- **A walk of the network gives a walk of the suppressed network** between the ends of the chains
of its ends, along the arcs of the walk that leave vertices that are not chain vertices. -/
theorem suppress_walks_chainEnd (hM : M.IsPhylogenetic) {F : Set E'} {a b : V'}
    (h : M.graph.Walks F a b) :
    (M.suppress hM).graph.Walks {f | f.1 ∈ F} ⟨chainEnd hM a, not_isChainVertex_chainEnd hM a⟩
      ⟨chainEnd hM b, not_isChainVertex_chainEnd hM b⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨g, hg, hj⟩ := hbc
    have key : (M.suppress hM).graph.Walks {f | f.1 ∈ F}
        ⟨chainEnd hM (M.graph.source g), not_isChainVertex_chainEnd hM _⟩
        ⟨chainEnd hM (M.graph.target g), not_isChainVertex_chainEnd hM _⟩ := by
      by_cases hgs : M.IsChainVertex (M.graph.source g)
      · have : (⟨chainEnd hM (M.graph.source g), not_isChainVertex_chainEnd hM _⟩ :
            {v // ¬ M.IsChainVertex v}) =
            ⟨chainEnd hM (M.graph.target g), not_isChainVertex_chainEnd hM _⟩ :=
          Subtype.ext (chainEnd_eq_of_adj hM hgs ⟨g, rfl, rfl⟩)
        rw [this]
        exact .refl
      · exact .single ⟨⟨g, hgs⟩, hg, Or.inl ⟨Subtype.ext (chainEnd_eq_self hM hgs).symm, rfl⟩⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₁ h₂
      exact ih.trans key
    · subst h₁ h₂
      exact ih.trans ((M.suppress hM).graph.walks_symm key)

/-- **A walk of the suppressed network gives a walk of the network**, along the chains of its
arcs. -/
theorem walks_of_suppress_walks (hM : M.IsPhylogenetic)
    {F : Set {e // ¬ M.IsChainVertex (M.graph.source e)}} {a b : {v // ¬ M.IsChainVertex v}}
    (h : (M.suppress hM).graph.Walks F a b) : M.graph.Walks (suppressChainArcs M F) a.1 b.1 := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, hf, hj⟩ := hbc
    have key : M.graph.Walks (suppressChainArcs M F) (M.graph.source f.1)
        (chainEnd hM (M.graph.target f.1)) := by
      refine Relation.ReflTransGen.head ⟨f.1, ⟨f, hf, Or.inl rfl⟩, Or.inl ⟨rfl, rfl⟩⟩ ?_
      refine Relation.ReflTransGen.mono ?_ _ _
        (reflTransGen_chain_of_chainReach f (chainReach_chainEnd hM _))
      rintro x y ⟨g, hg, -, hgs, hgt⟩
      exact ⟨g, ⟨f, hf, hg⟩, Or.inl ⟨hgs, hgt⟩⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₁ h₂
      exact ih.trans key
    · subst h₁ h₂
      exact ih.trans (M.graph.walks_symm key)

/-- **A cycle of the suppressed network contains, on its chains, a cycle of the network** through
any of its arcs. -/
theorem exists_isCycle_subset_suppressChainArcs (hM : M.IsPhylogenetic)
    {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}} (hD : IsCycle (M.suppress hM).graph D)
    {f₀ : {e // ¬ M.IsChainVertex (M.graph.source e)}} (hf₀ : f₀ ∈ D) :
    ∃ C, IsCycle M.graph C ∧ f₀.1 ∈ C ∧ C ⊆ suppressChainArcs M D := by
  have h₁ : M.graph.Walks (suppressChainArcs M D \ {f₀.1}) (M.graph.target f₀.1)
      (chainEnd hM (M.graph.target f₀.1)) := by
    refine Relation.ReflTransGen.mono ?_ _ _
      (reflTransGen_chain_of_chainReach f₀ (chainReach_chainEnd hM _))
    rintro x y ⟨g, hg, hx, hgs, hgt⟩
    refine ⟨g, ⟨⟨f₀, hf₀, hg⟩, fun h => ?_⟩, Or.inl ⟨hgs, hgt⟩⟩
    rw [Set.mem_singleton_iff] at h
    subst h
    exact f₀.2 (hgs ▸ hx)
  have h₂ := walks_of_suppress_walks hM (hD.walks_diff_singleton hf₀)
  have hW : M.graph.Walks (suppressChainArcs M D \ {f₀.1}) (M.graph.target f₀.1)
      (M.graph.source f₀.1) := by
    refine h₁.trans (walks_mono ?_ h₂)
    rintro g ⟨f, ⟨hf, hff₀⟩, hg⟩
    refine ⟨⟨f, hf, hg⟩, fun h => hff₀ ?_⟩
    rw [Set.mem_singleton_iff] at h ⊢
    subst h
    exact Subtype.ext (IsOnChain.unique hg (Or.inl rfl) f.2 f₀.2)
  obtain ⟨C, hC, hf₀C, hsub⟩ := exists_isCycle_of_walks (e := f₀.1)
    (F := suppressChainArcs M D \ {f₀.1}) (fun h => h.2 rfl) hW
  refine ⟨C, hC, hf₀C, fun g hg => ?_⟩
  rcases hsub hg with rfl | h
  · exact ⟨f₀, hf₀, Or.inl rfl⟩
  · exact h.1

/-- **A cycle of the network contains, on its arcs, a cycle of the suppressed network** through
any of its arcs leaving a vertex that is not a chain vertex. -/
theorem exists_isCycle_suppress_of_isCycle (hM : M.IsPhylogenetic) {C : Set E'}
    (hC : IsCycle M.graph C) {g₀ : E'} (hg₀C : g₀ ∈ C)
    (hg₀ : ¬ M.IsChainVertex (M.graph.source g₀)) :
    ∃ D, IsCycle (M.suppress hM).graph D ∧ ⟨g₀, hg₀⟩ ∈ D ∧ ∀ f ∈ D, f.1 ∈ C := by
  have hW := suppress_walks_chainEnd hM (hC.walks_diff_singleton hg₀C)
  have hend : (⟨chainEnd hM (M.graph.source g₀), not_isChainVertex_chainEnd hM _⟩ :
      {v // ¬ M.IsChainVertex v}) = (M.suppress hM).graph.source ⟨g₀, hg₀⟩ :=
    Subtype.ext (chainEnd_eq_self hM hg₀)
  rw [hend] at hW
  obtain ⟨D, hD, hg₀D, hsub⟩ := exists_isCycle_of_walks (G := (M.suppress hM).graph)
    (e := ⟨g₀, hg₀⟩) (F := {f | f.1 ∈ C \ {g₀}}) (fun h => h.2 rfl) hW
  refine ⟨D, hD, hg₀D, fun f hf => ?_⟩
  rcases hsub hf with rfl | h
  · exact hg₀C
  · exact h.1

/-- **A cycle through an arc leaving a chain vertex continues along the chain**: the chain vertex
has one arc in and one arc out, both on the cycle. -/
theorem isOnChain_mem_of_mem_isCycle (hM : M.IsPhylogenetic) {C : Set E'}
    (hC : IsCycle M.graph C) {f g : E'} (hf : f ∈ C) (hg : M.IsOnChain f g) : g ∈ C := by
  have step : ∀ {z : V'} {g' g : E'}, M.IsChainVertex z → g' ∈ C → M.graph.target g' = z →
      M.graph.source g = z → g ∈ C := by
    intro z g' g hz hg' hg't hgs
    obtain ⟨f₁, hf₁, f₂, hf₂, h12, hu₁, hu₂⟩ := hC.exists_ne_of_mem
      (fun e _ h => hM.acyclic _ (.single ⟨e, rfl, h.symm⟩)) ⟨g', hg', Or.inr hg't⟩
    obtain ⟨i, hi⟩ := (M.graph.indegree_eq_one_iff z).mp hz.1
    obtain ⟨o, ho⟩ := (M.graph.outdegree_eq_one_iff z).mp hz.2
    have key : ∀ e, (M.graph.source e = z ∨ M.graph.target e = z) → e = g' ∨ e = g := by
      rintro e (h | h)
      · exact Or.inr (((ho e).mp h).trans ((ho g).mp hgs).symm)
      · exact Or.inl (((hi e).mp h).trans ((hi g').mp hg't).symm)
    rcases key f₁ hu₁ with h₁ | h₁
    · rcases key f₂ hu₂ with h₂ | h₂
      · exact absurd (h₁.trans h₂.symm) h12
      · exact h₂ ▸ hf₂
    · exact h₁ ▸ hf₁
  rcases hg with rfl | ⟨hgc, hr⟩
  · exact hf
  · have hin : ∀ z, M.ChainReach (M.graph.target f) z → ∃ g' ∈ C, M.graph.target g' = z := by
      intro z hz
      induction hz with
      | refl => exact ⟨f, hf, rfl⟩
      | @tail a b _ hab ih =>
        obtain ⟨ha, e, hes, het⟩ := hab
        obtain ⟨g', hg', hg't⟩ := ih
        exact ⟨e, step ha hg' hg't hes, het⟩
    obtain ⟨g', hg', hg't⟩ := hin _ hr
    exact step hgc hg' hg't rfl

/-- **The chains of a cycle of the suppressed network form a cycle of the network.** -/
theorem isCycle_suppressChainArcs (hM : M.IsPhylogenetic)
    {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}} (hD : IsCycle (M.suppress hM).graph D) :
    IsCycle M.graph (suppressChainArcs M D) := by
  obtain ⟨k, v, e, hcyc, hrange⟩ := id hD
  have hf₀ : e ⟨0, hcyc.pos⟩ ∈ D := hrange ▸ ⟨_, rfl⟩
  obtain ⟨C, hC, hf₀C, hCsub⟩ := exists_isCycle_subset_suppressChainArcs hM hD hf₀
  obtain ⟨D₂, hD₂, -, hD₂C⟩ := exists_isCycle_suppress_of_isCycle hM hC hf₀C (e ⟨0, hcyc.pos⟩).2
  have hD₂D : D₂ ⊆ D := fun f hf => (mem_suppressChainArcs_iff D f).1 (hCsub (hD₂C f hf))
  have hDD₂ := hD.eq_of_subset hD₂ hD₂D
  have hsub : suppressChainArcs M D ⊆ C := by
    rintro g ⟨f, hf, hg⟩
    exact isOnChain_mem_of_mem_isCycle hM hC (hD₂C f (by rw [hDD₂]; exact hf)) hg
  rwa [Set.Subset.antisymm hsub hCsub]

/-- **The suppressed network of a level-1 network is level-1**: two cycles sharing an arc have
chains forming cycles of the network that share that arc. -/
theorem isLevelOne_suppress (hM : M.IsPhylogenetic) (h1 : IsLevelOne M.graph) :
    IsLevelOne (M.suppress hM).graph := by
  rintro D₁ D₂ hD₁ hD₂ ⟨f, hf₁, hf₂⟩
  have heq := h1 _ _ (isCycle_suppressChainArcs hM hD₁) (isCycle_suppressChainArcs hM hD₂)
    ⟨f.1, (mem_suppressChainArcs_iff D₁ f).2 hf₁, (mem_suppressChainArcs_iff D₂ f).2 hf₂⟩
  ext g
  rw [← mem_suppressChainArcs_iff D₁ g, ← mem_suppressChainArcs_iff D₂ g, heq]

/-- The nodes of a cycle of the suppressed network are nodes of the cycle of its chains. -/
theorem mem_cycleNodes_suppressChainArcs (hM : M.IsPhylogenetic)
    {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}} {z : {v // ¬ M.IsChainVertex v}}
    (hz : z ∈ cycleNodes (M.suppress hM).graph D) :
    z.1 ∈ cycleNodes M.graph (suppressChainArcs M D) := by
  obtain ⟨f, hf, h | h⟩ := hz
  · exact ⟨f.1, ⟨f, hf, Or.inl rfl⟩, Or.inl (congrArg Subtype.val h)⟩
  · obtain ⟨g, hg, hgt⟩ := exists_isOnChain_target_eq_chainEnd hM f.1
    exact ⟨g, ⟨f, hf, hg⟩, Or.inr (hgt.trans (congrArg Subtype.val h))⟩

/-- The nodes of the cycle of the chains of `D` that are not chain vertices are nodes of `D`. -/
theorem mem_cycleNodes_suppress_of_mem (hM : M.IsPhylogenetic)
    {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}} {z : {v // ¬ M.IsChainVertex v}}
    (hz : z.1 ∈ cycleNodes M.graph (suppressChainArcs M D)) :
    z ∈ cycleNodes (M.suppress hM).graph D := by
  obtain ⟨g, ⟨f, hf, hg⟩, h | h⟩ := hz
  · rcases hg with rfl | ⟨hc, -⟩
    · exact ⟨f, hf, Or.inl (Subtype.ext h)⟩
    · exact absurd (h ▸ hc) z.2
  · refine ⟨f, hf, Or.inr (Subtype.ext ?_)⟩
    change chainEnd hM (M.graph.target f.1) = z.1
    rw [← h]
    exact chainEnd_eq_of_isOnChain hM hg (h ▸ z.2)

end Suppress

/-! ### Cycles below a vertex -/

section Below

variable {V' E' X' : Type*} {N : RootedNetwork V' E' X'} {l : V'} {Y : Set X'}
  {hl : l ∈ N.ancestralVertices Y} {hleaf : ∀ x ∈ Y, N.graph.Reaches l (N.leaf x)}

/-- A cycle of the part of `N` below `l` is a cycle of `N`. -/
theorem isCycle_image_val_belowNetwork {C : Set (N.belowArcs l Y)}
    (hC : IsCycle (N.belowNetwork l Y hl hleaf).graph C) : IsCycle N.graph (Subtype.val '' C) := by
  obtain ⟨k, v, e, hcyc, rfl⟩ := hC
  refine ⟨k, fun i => (v i).1, fun i => (e i).1, ⟨hcyc.pos, fun i => ?_,
    fun i j h => hcyc.injective_node (Subtype.ext h),
    fun i j h => hcyc.injective_edge (Subtype.ext h)⟩, Set.range_comp _ _⟩
  rcases hcyc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
  · exact Or.inr ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩

/-- The part of a level-1 network below a vertex is level-1. -/
theorem isLevelOne_belowNetwork (h1 : IsLevelOne N.graph) :
    IsLevelOne (N.belowNetwork l Y hl hleaf).graph := by
  rintro C C' hC hC' ⟨f, hf, hf'⟩
  exact Set.image_injective.2 Subtype.val_injective (h1 _ _ (isCycle_image_val_belowNetwork hC)
    (isCycle_image_val_belowNetwork hC') ⟨f.1, ⟨f, hf, rfl⟩, ⟨f, hf', rfl⟩⟩)

/-- The nodes of the image of a cycle below `l` are the images of its nodes. -/
theorem mem_cycleNodes_image_val_iff {C : Set (N.belowArcs l Y)} {w : V'} :
    w ∈ cycleNodes N.graph (Subtype.val '' C) ↔
      ∃ z ∈ cycleNodes (N.belowNetwork l Y hl hleaf).graph C, z.1 = w := by
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, h | h⟩
    · exact ⟨_, ⟨f, hf, Or.inl rfl⟩, h⟩
    · exact ⟨_, ⟨f, hf, Or.inr rfl⟩, h⟩
  · rintro ⟨z, ⟨f, hf, h | h⟩, rfl⟩
    · exact ⟨f.1, ⟨f, hf, rfl⟩, Or.inl (congrArg Subtype.val h)⟩
    · exact ⟨f.1, ⟨f, hf, rfl⟩, Or.inr (congrArg Subtype.val h)⟩

end Below

/-! ### The cycles of `M⁻` as cycles of `M` -/

section Unrooted

variable {V' E' X' : Type*} {M : RootedNetwork V' E' X'} (hM : IsBinaryRootedNetwork M)
  {hX : Nontrivial X'}

/-- The arcs of `M` of a set `D` of edges of `M⁻`: the edge merged at `LSA(X)` stands for itself
and for `rootTreeArc`. -/
def unrootedCycleArcs (D : Set (SemidirectedArc hM.1 hM.2 hX)) : Set E' :=
  {f | ∃ c ∈ D, f = c.1.1 ∨
    (M.graph.source c.1.1 = lsa hM.1 Set.univ Set.univ_nonempty ∧ f = (rootTreeArc hM.1 hM.2 hX).1)}

/-- An edge of `M⁻` is in `D` exactly when its arc is an arc of `D`. -/
theorem mem_unrootedCycleArcs_iff (D : Set (SemidirectedArc hM.1 hM.2 hX))
    (c : SemidirectedArc hM.1 hM.2 hX) : c.1.1 ∈ unrootedCycleArcs hM D ↔ c ∈ D := by
  constructor
  · rintro ⟨c', hc', h | ⟨-, h⟩⟩
    · rwa [unrooted_edge_ext h]
    · exact absurd (Subtype.ext h) c.2
  · exact fun hc => ⟨c, hc, Or.inl rfl⟩

/-- The source of `rootTreeArc` is `LSA(X)`. -/
theorem source_rootTreeArc_val :
    M.graph.source (rootTreeArc hM.1 hM.2 hX).1 = lsa hM.1 Set.univ Set.univ_nonempty :=
  congrArg Subtype.val (rootTreeArc_spec hM.1 hM.2 hX).1

/-- **At most one edge of `M⁻` leaves `LSA(X)` in `M`**: the LSA has outdegree two, and
`rootTreeArc` is one of its arcs. -/
theorem unrooted_edge_eq_of_source_eq_lsa {c c' : SemidirectedArc hM.1 hM.2 hX}
    (hc : M.graph.source c.1.1 = lsa hM.1 Set.univ Set.univ_nonempty)
    (hc' : M.graph.source c'.1.1 = lsa hM.1 Set.univ Set.univ_nonempty) : c = c' := by
  have := hM.1.finite_arcs
  by_contra hne
  have hne' : c.1.1 ≠ c'.1.1 := fun h => hne (unrooted_edge_ext h)
  have hκ : ∀ d : SemidirectedArc hM.1 hM.2 hX, (rootTreeArc hM.1 hM.2 hX).1 ≠ d.1.1 :=
    fun d h => d.2 (Subtype.ext h.symm)
  have hsub : ({(rootTreeArc hM.1 hM.2 hX).1, c.1.1, c'.1.1} : Set E') ⊆
      {f | M.graph.source f = lsa hM.1 Set.univ Set.univ_nonempty} := by
    rintro f (rfl | rfl | rfl)
    · exact source_rootTreeArc_val hM
    · exact hc
    · exact hc'
  have h3 : ({(rootTreeArc hM.1 hM.2 hX).1, c.1.1, c'.1.1} : Set E').ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hne']
    rintro (h | h)
    · exact hκ c h
    · exact hκ c' h
  have := h3 ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
  have := hM.outdegree_le_two (lsa hM.1 Set.univ Set.univ_nonempty)
  unfold DirectedMultigraph.outdegree at *
  omega

/-- **A cycle of `M⁻` is a cycle of `M`**, through `LSA(X)` when it has the merged edge (the proof
of `lemma3_unrooted`). -/
theorem isCycle_unrootedCycleArcs {D : Set (SemidirectedArc hM.1 hM.2 hX)}
    (hD : IsCycle (unrooted M hM hX).graph D) : IsCycle M.graph (unrootedCycleArcs hM D) := by
  classical
  set G := unrooted M hM hX with hG_def
  set m := lsa hM.1 Set.univ Set.univ_nonempty with hm_def
  set e₀ := rootTreeArc hM.1 hM.2 hX with he₀_def
  have he₀s : M.graph.source e₀.1 = m := source_rootTreeArc_val hM
  let ι : SemidirectedVertex hM.1 hX → V' := fun u => u.1.1
  let κ : SemidirectedArc hM.1 hM.2 hX → E' := fun c => c.1.1
  have hι : Function.Injective ι := fun u u' h => Subtype.ext (Subtype.ext h)
  have hκ : Function.Injective κ := fun c c' h => Subtype.ext (Subtype.ext h)
  have hιm : ∀ u, ι u ≠ m := fun u h => u.2 (Subtype.ext h)
  have hκe₀ : ∀ c, κ c ≠ e₀.1 := fun c h => c.2 (Subtype.ext h)
  have hsrc : ∀ c, (M.graph.source (κ c) ≠ m ∧ ι (G.graph.source c) = M.graph.source (κ c)) ∨
      (M.graph.source (κ c) = m ∧ ι (G.graph.source c) = M.graph.target e₀.1) := by
    intro c
    by_cases h : M.graph.source (κ c) = m
    · exact Or.inr ⟨h, unrooted_source_val_of_eq hM c h⟩
    · exact Or.inl ⟨h, unrooted_source_val_of_ne hM c h⟩
  have hjoin : ∀ c u w, M.graph.source (κ c) ≠ m → Joins G.graph c u w →
      Joins M.graph (κ c) (ι u) (ι w) := by
    intro c u w hcm h
    have hs : ι (G.graph.source c) = M.graph.source (κ c) :=
      ((hsrc c).resolve_right fun h => hcm h.1).2
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨hs.symm.trans (congrArg ι h₁), (congrArg ι h₂)⟩
    · exact Or.inr ⟨hs.symm.trans (congrArg ι h₁), (congrArg ι h₂)⟩
  obtain ⟨k, v, e, hD, rfl⟩ := hD
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hD.pos; omega⟩
  by_cases hj : ∃ j, M.graph.source (κ (e j)) = m
  · obtain ⟨j, hj⟩ := hj
    -- read the cycle so that the merged edge is last
    have hR := hD.rotate (j + 1)
    have hlast : e (Fin.last n + (j + 1)) = e j := by
      congr 1
      rw [add_comm j 1, ← add_assoc, Fin.last_add_one, zero_add]
    have hrange : Set.range (fun i => e (i + (j + 1))) = Set.range e :=
      (Equiv.addRight (j + 1)).surjective.range_comp e
    have hP := hR.isPathOf
    have hother : ∀ l : Fin n, M.graph.source (κ (e (l.castSucc + (j + 1)))) ≠ m := fun l h => by
      have h' := hR.injective_edge
        ((unrooted_edge_eq_of_source_eq_lsa hM h hj).trans hlast.symm)
      exact (Fin.castSucc_lt_last l).ne h'
    have hPN : IsPathOf M.graph Set.univ n (fun i => ι (v (i + (j + 1))))
        (fun l => κ (e (l.castSucc + (j + 1)))) :=
      ⟨fun _ => trivial, fun l => hjoin _ _ _ (hother l) (hP.link l), hι.comp hP.injective⟩
    have hjl := hR.joins (Fin.last n)
    simp only [finRotate_last, hlast] at hjl
    have hs := ((hsrc (e j)).resolve_left fun h => h.1 hj).2
    have hz : m ∉ Set.range (fun i => ι (v (i + (j + 1)))) := fun ⟨i, hi⟩ => hιm _ hi
    have hnot₀ : e₀.1 ∉ Set.range (fun l : Fin n => κ (e (l.castSucc + (j + 1)))) :=
      fun ⟨l, hl⟩ => hκe₀ _ hl
    have hnotj : κ (e j) ∉ Set.range (fun l : Fin n => κ (e (l.castSucc + (j + 1)))) :=
      fun ⟨l, hl⟩ => hother l (by simp only at hl; rw [hl]; exact hj)
    have hne₀j : e₀.1 ≠ κ (e j) := fun h => hκe₀ _ h.symm
    have hcalc : unrootedCycleArcs hM (Set.range e) = insert e₀.1 (insert (κ (e j))
        (Set.range fun l : Fin n => κ (e (l.castSucc + (j + 1))))) := by
      ext f
      constructor
      · rintro ⟨c, hc, rfl | ⟨-, rfl⟩⟩
        · rw [← hrange] at hc
          obtain ⟨i, rfl⟩ := hc
          induction i using Fin.lastCases with
          | last => exact Or.inr (Or.inl (by simp only; rw [hlast]))
          | cast l => exact Or.inr (Or.inr ⟨l, rfl⟩)
        · exact Or.inl rfl
      · rintro (rfl | rfl | ⟨l, rfl⟩)
        · exact ⟨e j, ⟨j, rfl⟩, Or.inr ⟨hj, rfl⟩⟩
        · exact ⟨e j, ⟨j, rfl⟩, Or.inl rfl⟩
        · exact ⟨_, ⟨_, rfl⟩, Or.inl rfl⟩
    rw [hcalc]
    rcases hjl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · -- the path ends at the child of `e₀`: close it by `e₀` and the merged edge
      have hend : ι (v (Fin.last n + (j + 1))) = M.graph.target e₀.1 := by rw [← h₁]; exact hs
      have h0 : ι (v (0 + (j + 1))) = M.graph.target (κ (e j)) := by rw [← h₂]; rfl
      exact hPN.isCycle_insert_insert hz hnotj hne₀j (Or.inr ⟨he₀s, hend.symm⟩)
        (Or.inl ⟨hj, h0.symm⟩)
    · -- the path starts at the child of `e₀`: close it by the merged edge and `e₀`
      have h0 : ι (v (0 + (j + 1))) = M.graph.target e₀.1 := by rw [← h₁]; exact hs
      have hend : ι (v (Fin.last n + (j + 1))) = M.graph.target (κ (e j)) := by rw [← h₂]; rfl
      rw [Set.insert_comm]
      exact hPN.isCycle_insert_insert hz hnot₀ hne₀j.symm (Or.inr ⟨hj, hend.symm⟩)
        (Or.inl ⟨he₀s, h0.symm⟩)
  · push Not at hj
    refine ⟨n + 1, fun i => ι (v i), fun i => κ (e i), ⟨hD.pos, fun i => hjoin _ _ _ (hj i)
      (hD.joins i), hι.comp hD.injective_node, hκ.comp hD.injective_edge⟩, ?_⟩
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, ⟨i, rfl⟩, Or.inl rfl⟩
    · rintro ⟨c, ⟨i, rfl⟩, rfl | ⟨h, -⟩⟩
      · exact ⟨i, rfl⟩
      · exact absurd h (hj i)

/-- The nodes of a cycle of `M⁻` are nodes of the cycle of `M`. -/
theorem mem_cycleNodes_unrootedCycleArcs {D : Set (SemidirectedArc hM.1 hM.2 hX)}
    {u : SemidirectedVertex hM.1 hX} (hu : u ∈ cycleNodes (unrooted M hM hX).graph D) :
    u.1.1 ∈ cycleNodes M.graph (unrootedCycleArcs hM D) := by
  obtain ⟨c, hc, hu | hu⟩ := hu
  · by_cases hm : M.graph.source c.1.1 = lsa hM.1 Set.univ Set.univ_nonempty
    · refine ⟨(rootTreeArc hM.1 hM.2 hX).1, ⟨c, hc, Or.inr ⟨hm, rfl⟩⟩, Or.inr ?_⟩
      rw [← hu, unrooted_source_val_of_eq hM c hm]
    · refine ⟨c.1.1, ⟨c, hc, Or.inl rfl⟩, Or.inl ?_⟩
      rw [← hu, unrooted_source_val_of_ne hM c hm]
  · exact ⟨c.1.1, ⟨c, hc, Or.inl rfl⟩, Or.inr (by rw [← hu]; rfl)⟩

/-- The nodes of the cycle of `M` of a cycle of `M⁻` other than `LSA(X)` are nodes of the cycle of
`M⁻`. -/
theorem exists_mem_cycleNodes_of_unrootedCycleArcs {D : Set (SemidirectedArc hM.1 hM.2 hX)}
    {z : V'} (hz : z ∈ cycleNodes M.graph (unrootedCycleArcs hM D))
    (hzm : z ≠ lsa hM.1 Set.univ Set.univ_nonempty) :
    ∃ u ∈ cycleNodes (unrooted M hM hX).graph D, u.1.1 = z := by
  obtain ⟨f, ⟨c, hc, rfl | ⟨hm, rfl⟩⟩, h | h⟩ := hz
  · refine ⟨_, ⟨c, hc, Or.inl rfl⟩, ?_⟩
    rw [unrooted_source_val_of_ne hM c (h ▸ hzm)]
    exact h
  · exact ⟨_, ⟨c, hc, Or.inr rfl⟩, h⟩
  · exact absurd (h.symm.trans (source_rootTreeArc_val hM)) hzm
  · refine ⟨_, ⟨c, hc, Or.inl rfl⟩, ?_⟩
    rw [unrooted_source_val_of_eq hM c hm]
    exact h

/-- **A taxon below an arc off the cycle leaving a node `u` is in the block of `u`.** The arc and a
path below it are edges of `M⁻` off the cycle (`nodeBlock_nonempty_of_child`). -/
theorem mem_nodeBlock_of_reaches_offCycle (h1 : IsLevelOne M.graph)
    {C : Set (SemidirectedArc hM.1 hM.2 hX)} (hC : IsCycle (unrooted M hM hX).graph C)
    {u : SemidirectedVertex hM.1 hX} (hu : u ∈ cycleNodes (unrooted M hM hX).graph C) {c : E'}
    (hc : c ∉ unrootedCycleArcs hM C) (hcs : M.graph.source c = u.1.1) {x : X'}
    (hx : M.graph.Reaches (M.graph.target c) (M.leaf x)) :
    x ∈ nodeBlock (unrooted M hM hX).graph (unrooted M hM hX).leaf C u := by
  have := hM.1.finite_arcs
  have h1G := unrooted_isLevelOne hM h1 hX
  obtain ⟨d, rfl, hds, hdt⟩ := exists_unrooted_edge hM u hcs
  have hd : d ∉ C := fun h => hc ⟨d, h, Or.inl rfl⟩
  have key : ∀ b, M.graph.Reaches (M.graph.target d.1.1) b →
      ∃ w, (unrooted M hM hX).graph.Walks Cᶜ u w ∧ w.1.1 = b := by
    intro b hb
    induction hb with
    | refl => exact ⟨_, Relation.ReflTransGen.single ⟨d, hd, Or.inl ⟨hds, rfl⟩⟩, hdt⟩
    | @tail a b hca hab ih =>
      obtain ⟨w, hw, rfl⟩ := ih
      obtain ⟨f, hfs, hft⟩ := hab
      obtain ⟨d', rfl, hds', hdt'⟩ := exists_unrooted_edge hM w hfs
      have hwu : w ≠ u := by
        rintro rfl
        exact hM.1.acyclic _ (Relation.TransGen.head' ⟨d.1.1, hcs, rfl⟩ hca)
      exact ⟨_, (h1G.walks_compl_ends hC hu hw hwu (Or.inl hds')).2, hdt'.trans hft⟩
  obtain ⟨w, hw, hwx⟩ := key _ hx
  obtain rfl : w = (unrooted M hM hX).leaf x := unrooted_node_ext hwx
  exact hw

/-- **A taxon in the block of a node `u` of a cycle of `M⁻` other than the top of its cycle of `M`
is below an arc off the cycle leaving `u`.** The vertices below such arcs, with `u`, are entered
from outside only through edges of the cycle (`IsCycle.reaches_source_of_reaches_target`), and no
edge of `M⁻` off the cycle crosses that cut. -/
theorem exists_reaches_offCycle_of_mem_nodeBlock (h1 : IsLevelOne M.graph)
    {C : Set (SemidirectedArc hM.1 hM.2 hX)} (hC : IsCycle (unrooted M hM hX).graph C) {a : V'}
    (hE : ∀ w ∈ cycleNodes M.graph (unrootedCycleArcs hM C), w ≠ a → ∀ g, M.graph.target g = w →
      g ∈ unrootedCycleArcs hM C)
    (hroot : M.root ∈ cycleNodes M.graph (unrootedCycleArcs hM C) → M.root = a)
    {u : SemidirectedVertex hM.1 hX} (hu : u ∈ cycleNodes (unrooted M hM hX).graph C)
    (hua : u.1.1 ≠ a) {x : X'}
    (hx : x ∈ nodeBlock (unrooted M hM hX).graph (unrooted M hM hX).leaf C u) :
    ∃ c ∉ unrootedCycleArcs hM C, M.graph.source c = u.1.1 ∧
      M.graph.Reaches (M.graph.target c) (M.leaf x) := by
  have hĈ := isCycle_unrootedCycleArcs hM hC
  have huĈ := mem_cycleNodes_unrootedCycleArcs hM hu
  have hum : u.1.1 ≠ lsa hM.1 Set.univ Set.univ_nonempty := unrooted_node_ne_lsa u
  -- the vertices below an arc off the cycle leaving `u`
  let B : V' → Prop := fun w => ∃ c ∉ unrootedCycleArcs hM C, M.graph.source c = u.1.1 ∧
    M.graph.Reaches (M.graph.target c) w
  have hBm : ¬ B (lsa hM.1 Set.univ Set.univ_nonempty) := by
    rintro ⟨c, -, hcs, hc⟩
    exact hum (eq_of_reaches_of_reaches hM.1.acyclic
      (Relation.ReflTransGen.head ⟨c, hcs, rfl⟩ hc) u.1.2.1)
  have hEB : ∀ g, B (M.graph.target g) → M.graph.source g = u.1.1 ∨ B (M.graph.source g) := by
    rintro g ⟨c, hc, hcs, hg⟩
    by_cases hgc : g = c
    · exact Or.inl (hgc ▸ hcs)
    · exact Or.inr ⟨c, hc, hcs,
        hĈ.reaches_source_of_reaches_target hM h1 hE hroot huĈ hua hc hcs hgc hg⟩
  let S : Set (SemidirectedVertex hM.1 hX) := {w | w = u ∨ B w.1.1}
  have hcut : ∀ d ∈ Cᶜ, ¬ (unrooted M hM hX).graph.Crosses d S := by
    intro d hd hcross
    have hdĈ : d.1.1 ∉ unrootedCycleArcs hM C := fun h =>
      hd ((mem_unrootedCycleArcs_iff hM C d).1 h)
    by_cases hdm : M.graph.source d.1.1 = lsa hM.1 Set.univ Set.univ_nonempty
    · -- the merged edge: neither of its ends is in `S`
      have hnot : ∀ w : SemidirectedVertex hM.1 hX, w ∈ S →
          w.1.1 = M.graph.target (rootTreeArc hM.1 hM.2 hX).1 ∨ w.1.1 = M.graph.target d.1.1 →
            False := by
        rintro w (rfl | hB) hw
        · rcases hw with hw | hw
          · obtain ⟨c, hc, h | ⟨hcm, -⟩⟩ := hE _ huĈ hua _ hw.symm
            · exact c.2 (Subtype.ext h.symm)
            · exact hd (unrooted_edge_eq_of_source_eq_lsa hM hcm hdm ▸ hc)
          · exact hdĈ (hE _ huĈ hua _ hw.symm)
        · rcases hw with hw | hw
          · rcases hEB _ (hw ▸ hB) with h | h
            · exact hum (h.symm.trans (source_rootTreeArc_val hM))
            · exact hBm (source_rootTreeArc_val hM ▸ h)
          · rcases hEB _ (hw ▸ hB) with h | h
            · exact hum (h.symm.trans hdm)
            · exact hBm (hdm ▸ h)
      rcases hcross with ⟨h₁, -⟩ | ⟨h₁, -⟩
      · exact hnot _ h₁ (Or.inl (unrooted_source_val_of_eq hM d hdm))
      · exact hnot _ h₁ (Or.inr rfl)
    · have hs := unrooted_source_val_of_ne hM d hdm
      rcases hcross with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · refine h₂ (Or.inr ?_)
        rcases h₁ with h | ⟨c, hc, hcs, hr⟩
        · exact ⟨d.1.1, hdĈ, hs.symm.trans (congrArg (fun w => w.1.1) h), .refl⟩
        · exact ⟨c, hc, hcs, hr.tail ⟨d.1.1, hs.symm, rfl⟩⟩
      · refine h₂ ?_
        rcases h₁ with h | hB
        · exact absurd (hE _ huĈ hua d.1.1 (congrArg (fun w => w.1.1) h)) hdĈ
        · rcases hEB d.1.1 hB with h | h
          · exact Or.inl (unrooted_node_ext (hs.trans h))
          · exact Or.inr (hs ▸ h)
  rcases ((unrooted M hM hX).graph.mem_iff_mem_of_walks hcut hx).1 (Or.inl rfl) with h | hB
  · rw [← h] at huĈ
    exact absurd huĈ (hĈ.leaf_notMem_cycleNodes hM.1 x)
  · exact hB

/-- **A node of `M⁻` entered by two arcs of `M` is the hybrid node of a cycle of `M⁻`**: a walk from
the second parent up to the child of `rootTreeArc` and down to the first parent avoids the first
arc. -/
theorem exists_isHybridNodeOf_of_indegree_eq_two (h1 : IsLevelOne M.graph)
    (v : SemidirectedVertex hM.1 hX) (h2 : M.graph.indegree v.1.1 = 2) :
    ∃ C, IsCycle (unrooted M hM hX).graph C ∧ IsHybridNodeOf (unrooted M hM hX) C v := by
  have := hM.1.finite_arcs
  set P := lsaPlus hM.1 hX
  have hP : P.IsPhylogenetic := lsaPlus_isPhylogenetic hM.1 hX
  set e₀ := rootTreeArc hM.1 hM.2 hX
  set t₀ : SemidirectedVertex hM.1 hX := ⟨P.graph.target e₀, hP.target_ne_root e₀⟩
  -- the two arcs entering `v` are edges of `M⁻`
  obtain ⟨p₁, p₂, hne, hs⟩ := Set.ncard_eq_two.mp h2
  have hp₁ : M.graph.target p₁ = v.1.1 := by
    have : p₁ ∈ {f | M.graph.target f = v.1.1} := by rw [hs]; exact Or.inl rfl
    exact this
  have hp₂ : M.graph.target p₂ = v.1.1 := by
    have : p₂ ∈ {f | M.graph.target f = v.1.1} := by rw [hs]; exact Or.inr rfl
    exact this
  have hst := (lsa_spec hM.1 Set.univ Set.univ_nonempty).1
  have hmem₁ := mem_belowArcs_of_target hM.1 hst v.1 (unrooted_node_ne_lsa v) hp₁
  have hmem₂ := mem_belowArcs_of_target hM.1 hst v.1 (unrooted_node_ne_lsa v) hp₂
  have hM2 : 2 ≤ P.graph.indegree v.1 :=
    two_le_indegree_of_ne_targets (G := P.graph) (e := ⟨p₁, hmem₁⟩)
      (e' := ⟨p₂, hmem₂⟩) (fun h => hne (congrArg Subtype.val h)) (Subtype.ext hp₁)
      (Subtype.ext hp₂)
  have htree : P.graph.indegree (P.graph.target e₀) = 1 := (rootTreeArc_spec hM.1 hM.2 hX).2
  have hq : ∀ (p : E') (hp : p ∈ M.belowArcs (lsa hM.1 Set.univ Set.univ_nonempty) Set.univ),
      M.graph.target p = v.1.1 → (⟨p, hp⟩ : M.belowArcs _ _) ≠ e₀ := by
    intro p hp hpt h
    have : P.graph.target e₀ = v.1 := by
      rw [← h]
      exact Subtype.ext hpt
    rw [this] at htree
    omega
  let q₁ : SemidirectedArc hM.1 hM.2 hX := ⟨⟨p₁, hmem₁⟩, hq p₁ hmem₁ hp₁⟩
  let q₂ : SemidirectedArc hM.1 hM.2 hX := ⟨⟨p₂, hmem₂⟩, hq p₂ hmem₂ hp₂⟩
  have hqt₁ : (unrooted M hM hX).graph.target q₁ = v := unrooted_node_ext hp₁
  have hqt₂ : (unrooted M hM hX).graph.target q₂ = v := unrooted_node_ext hp₂
  have hq21 : q₂ ≠ q₁ := fun h => hne (congrArg (fun c => c.1.1) h).symm
  -- walks from `t₀` along paths from the LSA that avoid `v`
  have key : ∀ w (hw : w ≠ P.root), ¬ P.graph.Reaches v.1 w →
      (unrooted M hM hX).graph.Walks {d | d ≠ q₁} t₀ ⟨w, hw⟩ := by
    intro w hw hv
    induction hP.root_reaches w with
    | refl => exact absurd rfl hw
    | @tail a b _ hab ih =>
      obtain ⟨f, hfs, hft⟩ := hab
      -- the edge of `f` is not `q₁`, which enters `v`
      have hfq : ∀ hf : f ≠ e₀, (⟨f, hf⟩ : SemidirectedArc hM.1 hM.2 hX) ≠ q₁ := by
        intro hf h
        apply hv
        have h' : f = ⟨p₁, hmem₁⟩ := congrArg Subtype.val h
        have : b = v.1 := by
          rw [← hft, h']
          exact Subtype.ext hp₁
        rw [this]
        exact .refl
      by_cases ha : a = P.root
      · by_cases hf : f = e₀
        · have : (⟨b, hw⟩ : SemidirectedVertex hM.1 hX) = t₀ :=
            Subtype.ext (show b = P.graph.target e₀ by rw [← hft, hf])
          rw [this]
          exact .refl
        · refine .single ⟨⟨f, hf⟩, hfq hf, Or.inl ⟨?_, Subtype.ext hft⟩⟩
          show (unrootAt P hP e₀).graph.source ⟨f, hf⟩ = t₀
          simp only [unrootAt]
          rw [dite_eq_left (hfs.trans ha)]
      · have hf : f ≠ e₀ := by
          rintro rfl
          exact ha (hfs.symm.trans (rootTreeArc_spec hM.1 hM.2 hX).1)
        refine (ih ha fun h => hv (h.tail ⟨f, hfs, hft⟩)).tail
          ⟨⟨f, hf⟩, hfq hf, Or.inl ⟨?_, Subtype.ext hft⟩⟩
        show (unrootAt P hP e₀).graph.source ⟨f, hf⟩ = ⟨a, ha⟩
        simp only [unrootAt]
        rw [dite_eq_right (by rw [hfs]; exact ha)]
        exact Subtype.ext hfs
  have hsrc : ∀ q : SemidirectedArc hM.1 hM.2 hX, (unrooted M hM hX).graph.target q = v →
      (unrooted M hM hX).graph.Walks {d | d ≠ q₁} t₀ ((unrooted M hM hX).graph.source q) := by
    intro q hqv
    by_cases hr : P.graph.source q.1 = P.root
    · have : (unrooted M hM hX).graph.source q = t₀ := by
        show (unrootAt P hP e₀).graph.source q = t₀
        simp only [unrootAt]
        rw [dite_eq_left hr]
      rw [this]
      exact .refl
    · have : (unrooted M hM hX).graph.source q = ⟨P.graph.source q.1, hr⟩ := by
        show (unrootAt P hP e₀).graph.source q = _
        simp only [unrootAt]
        rw [dite_eq_right hr]
      rw [this]
      exact key _ hr fun h => hP.acyclic _
        (Relation.TransGen.tail' h ⟨q.1, rfl, congrArg Subtype.val hqv⟩)
  have hW : (unrooted M hM hX).graph.Walks {d | d ≠ q₁} ((unrooted M hM hX).graph.target q₁)
      ((unrooted M hM hX).graph.source q₁) := by
    rw [hqt₁]
    exact (Relation.ReflTransGen.single ⟨q₂, hq21, Or.inr ⟨rfl, hqt₂⟩⟩).trans
      (((unrooted M hM hX).graph.walks_symm (hsrc q₂ hqt₂)).trans (hsrc q₁ hqt₁))
  obtain ⟨C, hC, hq₁C, -⟩ := exists_isCycle_of_walks (e := q₁) (F := {d | d ≠ q₁})
    (fun h => h rfl) hW
  exact ⟨C, hC, isHybridNodeOf_of_indegree h1 hC ⟨q₁, hq₁C, Or.inr hqt₁⟩ h2⟩

/-- **A directed path of `M` along the arcs of a cycle of `M⁻`, from a node of `M⁻`, is a walk of
`M⁻` along the cycle**, through the same vertices. -/
theorem exists_unrooted_reflTransGen (C : Set (SemidirectedArc hM.1 hM.2 hX)) {P : V' → Prop}
    (w : SemidirectedVertex hM.1 hX) (hw : P w.1.1) {b : V'}
    (h : Relation.ReflTransGen (fun x y => ∃ g ∈ unrootedCycleArcs hM C, M.graph.source g = x ∧
      M.graph.target g = y ∧ P y) w.1.1 b) :
    ∃ b' : SemidirectedVertex hM.1 hX, b'.1.1 = b ∧ Relation.ReflTransGen
      (fun x y => (unrooted M hM hX).graph.AdjOn C x y ∧ P x.1.1 ∧ P y.1.1) w b' := by
  suffices key : ∃ b' : SemidirectedVertex hM.1 hX, b'.1.1 = b ∧ P b ∧ Relation.ReflTransGen
      (fun x y => (unrooted M hM hX).graph.AdjOn C x y ∧ P x.1.1 ∧ P y.1.1) w b' by
    obtain ⟨b', h₁, -, h₂⟩ := key
    exact ⟨b', h₁, h₂⟩
  induction h with
  | refl => exact ⟨w, rfl, hw, .refl⟩
  | @tail x y _ hxy ih =>
    obtain ⟨b', rfl, hPb, hb'⟩ := ih
    obtain ⟨g, hg, hgs, hgt, hPy⟩ := hxy
    obtain ⟨c, rfl, hcs, hct⟩ := exists_unrooted_edge hM b' hgs
    refine ⟨_, hct.trans hgt, hPy, hb'.tail ⟨⟨c, (mem_unrootedCycleArcs_iff hM C c).1 hg,
      Or.inl ⟨hcs, rfl⟩⟩, hPb, ?_⟩⟩
    rw [hct, hgt]
    exact hPy

end Unrooted

/-! ### Hybrid nodes of a suppressed network -/

section SuppressHybrid

variable {V' E' X' : Type*} {M : RootedNetwork V' E' X'}

/-- A vertex entered by two arcs of the suppressed network is entered by two arcs of the network:
the last arcs of their chains. -/
theorem two_le_indegree_of_suppress_indegree_eq_two (hM : M.IsPhylogenetic)
    {y : {v // ¬ M.IsChainVertex v}} (h2 : (M.suppress hM).graph.indegree y = 2) :
    2 ≤ M.graph.indegree y.1 := by
  have := hM.finite_arcs
  obtain ⟨f₁, f₂, hne, hs⟩ := Set.ncard_eq_two.mp h2
  have hf₁ : (M.suppress hM).graph.target f₁ = y := by
    have : f₁ ∈ {f | (M.suppress hM).graph.target f = y} := by rw [hs]; exact Or.inl rfl
    exact this
  have hf₂ : (M.suppress hM).graph.target f₂ = y := by
    have : f₂ ∈ {f | (M.suppress hM).graph.target f = y} := by rw [hs]; exact Or.inr rfl
    exact this
  obtain ⟨g₁, hg₁, hg₁t⟩ := exists_isOnChain_target_eq_chainEnd hM f₁.1
  obtain ⟨g₂, hg₂, hg₂t⟩ := exists_isOnChain_target_eq_chainEnd hM f₂.1
  have hgne : g₁ ≠ g₂ := fun h => hne (Subtype.ext (IsOnChain.unique hg₁ (h ▸ hg₂) f₁.2 f₂.2))
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_pair hgne]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro g (rfl | rfl)
  · exact hg₁t.trans (congrArg Subtype.val hf₁)
  · exact hg₂t.trans (congrArg Subtype.val hf₂)

/-- A vertex that is not a chain vertex, entered by two arcs of the network, is entered by two arcs
of the suppressed network: the first arcs of their chains. -/
theorem two_le_suppress_indegree (hM : M.IsPhylogenetic) {y : {v // ¬ M.IsChainVertex v}}
    {p₁ p₂ : E'} (hne : p₁ ≠ p₂) (hp₁ : M.graph.target p₁ = y.1) (hp₂ : M.graph.target p₂ = y.1) :
    2 ≤ (M.suppress hM).graph.indegree y := by
  have := hM.finite_arcs
  obtain ⟨f₁, hf₁, hon₁⟩ := exists_isOnChain hM p₁
  obtain ⟨f₂, hf₂, hon₂⟩ := exists_isOnChain hM p₂
  have ht : ∀ {f p : E'} (hf : ¬ M.IsChainVertex (M.graph.source f)), M.IsOnChain f p →
      M.graph.target p = y.1 → (M.suppress hM).graph.target ⟨f, hf⟩ = y := fun hf hon hp =>
    Subtype.ext ((chainEnd_eq_of_isOnChain hM hon (by rw [hp]; exact y.2)).trans hp)
  have hne' : (⟨f₁, hf₁⟩ : {e // ¬ M.IsChainVertex (M.graph.source e)}) ≠ ⟨f₂, hf₂⟩ := by
    intro h
    have h' : f₁ = f₂ := congrArg Subtype.val h
    subst h'
    exact hne (IsOnChain.eq_of_target hon₁ hon₂ (hp₁.trans hp₂.symm) (by rw [hp₁]; exact y.2))
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_pair hne']
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro f (rfl | rfl)
  · exact ht hf₁ hon₁ hp₁
  · exact ht hf₂ hon₂ hp₂

end SuppressHybrid

/-! ### The cycles of `M⁻` for an LSA network `M` -/

section LSAUnrooted

variable {V' E' X' : Type*} {M : RootedNetwork V' E' X'} (hM : IsBinaryRootedNetwork M)
  {hX : Nontrivial X'}

/-- The nodes of a cycle of `M⁻` are the nodes of the blocks of the taxa. -/
theorem cycleNodes_eq_range_blockNode (h1 : IsLevelOne M.graph)
    {C : Set (SemidirectedArc hM.1 hM.2 hX)} (hC : IsCycle (unrooted M hM hX).graph C) :
    cycleNodes (unrooted M hM hX).graph C = Set.range (blockNode (unrooted M hM hX) C) := by
  have := hM.1.finite_arcs
  ext u
  constructor
  · intro hu
    exact exists_blockNode_eq h1 hC hu
  · rintro ⟨x, rfl⟩
    exact blockNode_mem hC x

/-- A taxon descends from the hybrid node of a cycle of `M⁻` exactly when it is below it in `M`. -/
theorem descendsFrom_iff_reaches (h1 : IsLevelOne M.graph)
    {C : Set (SemidirectedArc hM.1 hM.2 hX)} (hC : IsCycle (unrooted M hM hX).graph C)
    {w : SemidirectedVertex hM.1 hX} (hw : IsHybridNodeOf (unrooted M hM hX) C w) (x : X') :
    DescendsFrom (unrooted M hM hX) w x ↔ M.graph.Reaches w.1.1 (M.leaf x) := by
  have := hM.1.finite_arcs
  exact ⟨fun h => reaches_of_mem_nodeBlock_hybrid h1 hw (mem_nodeBlock_of_descendsFrom h1 hC hw h),
    descendsFrom_of_reaches hM w⟩

/-- **The cycle of `M⁻` of a cycle of an LSA network `M`** through a hybrid node `y` of `M`: its
hybrid node is `y`. -/
theorem exists_unrooted_of_isCycle (h1 : IsLevelOne M.graph)
    (hr : ∀ hne, lsa hM.1 Set.univ hne = M.root) {D : Set E'} (hD : IsCycle M.graph D) {y : V'}
    (hyD : y ∈ cycleNodes M.graph D) (hy2 : M.graph.indegree y = 2) :
    ∃ C w, IsCycle (unrooted M hM hX).graph C ∧ IsHybridNodeOf (unrooted M hM hX) C w ∧
      w.1.1 = y ∧ unrootedCycleArcs hM C = D := by
  have := hM.1.finite_arcs
  have hyr : y ≠ M.root := fun h => by
    rw [h, hM.1.root_indegree] at hy2
    exact absurd hy2 (by norm_num)
  obtain ⟨w, hwy⟩ := exists_unrooted_node (hX := hX) hM.1
    (by rw [hr]; exact hM.1.root_reaches y) (by rw [hr]; exact hyr)
  obtain ⟨C, hC, hw⟩ := exists_isHybridNodeOf_of_indegree_eq_two hM h1 w (hwy ▸ hy2)
  refine ⟨C, w, hC, hw, hwy, (lemma3 hM h1 (isCycle_unrootedCycleArcs hM hC)).2.2 D hD
    ⟨y, ?_, hyD⟩⟩
  rw [← hwy]
  exact mem_cycleNodes_unrootedCycleArcs hM hw.mem_cycleNodes

/-- **The size of a cycle of `M⁻`** for an LSA network `M`: the number of nodes of its cycle of `M`
other than the root. -/
theorem ncard_cycleNodes_unrooted (hr : ∀ hne, lsa hM.1 Set.univ hne = M.root)
    {C : Set (SemidirectedArc hM.1 hM.2 hX)} (hC : IsCycle (unrooted M hM hX).graph C) :
    (cycleNodes (unrooted M hM hX).graph C).ncard = (unrootedCycleArcs hM C).ncard -
      (if M.root ∈ cycleNodes M.graph (unrootedCycleArcs hM C) then 1 else 0) := by
  have := hM.1.finite_vertices
  have hι : Function.Injective (fun u : SemidirectedVertex hM.1 hX => u.1.1) :=
    fun u u' h => unrooted_node_ext h
  have himg : (fun u : SemidirectedVertex hM.1 hX => u.1.1) ''
      cycleNodes (unrooted M hM hX).graph C =
        cycleNodes M.graph (unrootedCycleArcs hM C) \ {M.root} := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨mem_cycleNodes_unrootedCycleArcs hM hu, fun h => unrooted_node_ne_lsa u (h.trans
        (hr _).symm)⟩
    · rintro ⟨hz, hzr⟩
      obtain ⟨u, hu, rfl⟩ := exists_mem_cycleNodes_of_unrootedCycleArcs hM hz
        (by rw [hr]; exact hzr)
      exact ⟨u, hu, rfl⟩
  rw [← Set.ncard_image_of_injective _ hι, himg,
    ← ncard_cycleNodes (isCycle_unrootedCycleArcs hM hC)]
  split_ifs with h
  · rw [← Set.ncard_sdiff_singleton_add_one h]
    omega
  · rw [Set.sdiff_singleton_eq_self h, Nat.sub_zero]

/-- The nodes of the blocks of the taxa of `T` are the nodes `blockNode C x` for `x ∈ T`. -/
theorem mem_blockNodes_iff_blockNode (h1 : IsLevelOne M.graph)
    {C : Set (SemidirectedArc hM.1 hM.2 hX)} (hC : IsCycle (unrooted M hM hX).graph C)
    {T : Set X'} {u : SemidirectedVertex hM.1 hX} :
    u ∈ blockNodes (unrooted M hM hX) C T ↔ ∃ x ∈ T, blockNode (unrooted M hM hX) C x = u := by
  have := hM.1.finite_arcs
  constructor
  · rintro ⟨hu, x, hx, hxu⟩
    exact ⟨x, hx, (eq_blockNode h1 hC hu hxu).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨blockNode_mem hC x, x, hx, (blockNode_spec hC x).2⟩

/-- The blocks of `x` and `y` are joined along `C` avoiding the blocks of `T` exactly when the
nodes of their blocks are. -/
theorem joinedAvoiding_iff_reflTransGen (h1 : IsLevelOne M.graph)
    {C : Set (SemidirectedArc hM.1 hM.2 hX)} (hC : IsCycle (unrooted M hM hX).graph C)
    (T : Set X') (x y : X') :
    JoinedAvoiding (unrooted M hM hX) C T x y ↔ Relation.ReflTransGen (fun a b =>
      (unrooted M hM hX).graph.AdjOn C a b ∧ a ∉ blockNodes (unrooted M hM hX) C T ∧
        b ∉ blockNodes (unrooted M hM hX) C T)
      (blockNode (unrooted M hM hX) C x) (blockNode (unrooted M hM hX) C y) := by
  have := hM.1.finite_arcs
  constructor
  · rintro ⟨u, w, hu, hw, hxu, hyw, h⟩
    rwa [← eq_blockNode h1 hC hu hxu, ← eq_blockNode h1 hC hw hyw]
  · intro h
    exact ⟨_, _, blockNode_mem hC x, blockNode_mem hC y, (blockNode_spec hC x).2,
      (blockNode_spec hC y).2, h⟩

/-- **Around a 4-cycle of `M⁻`**, with nodes `u 0, …, u 3` in order, the blocks of `u i` and `u j`
are adjacent exactly when `u i` and `u j` are consecutive. -/
theorem adjacentBlocks_iff_finRotate (h1 : IsLevelOne M.graph)
    {C : Set (SemidirectedArc hM.1 hM.2 hX)} (hC : IsCycle (unrooted M hM hX).graph C)
    {u : Fin 4 → SemidirectedVertex hM.1 hX} {f : Fin 4 → SemidirectedArc hM.1 hM.2 hX}
    (hcyc : IsCycleOf (unrooted M hM hX).graph 4 u f) (hf : Set.range f = C) {i j : Fin 4}
    {x y : X'} (hx : x ∈ nodeBlock (unrooted M hM hX).graph (unrooted M hM hX).leaf C (u i))
    (hy : y ∈ nodeBlock (unrooted M hM hX).graph (unrooted M hM hX).leaf C (u j)) :
    AdjacentBlocks (unrooted M hM hX) C x y ↔ j = finRotate 4 i ∨ i = finRotate 4 j := by
  have := hM.1.finite_arcs
  have hmem : ∀ k, u k ∈ cycleNodes (unrooted M hM hX).graph C := fun k => by
    rw [← hf, hcyc.cycleNodes_eq]
    exact ⟨k, rfl⟩
  have hxi := eq_blockNode h1 hC (hmem i) hx
  have hyj := eq_blockNode h1 hC (hmem j) hy
  constructor
  · rintro ⟨e, he, p, q, hj, hxp, hyq⟩
    have hpn : p ∈ cycleNodes (unrooted M hM hX).graph C := by
      rcases hj with ⟨h, -⟩ | ⟨-, h⟩
      exacts [⟨e, he, Or.inl h⟩, ⟨e, he, Or.inr h⟩]
    have hqn : q ∈ cycleNodes (unrooted M hM hX).graph C := by
      rcases hj with ⟨-, h⟩ | ⟨h, -⟩
      exacts [⟨e, he, Or.inr h⟩, ⟨e, he, Or.inl h⟩]
    have hp : p = u i := (eq_blockNode h1 hC hpn hxp).trans hxi.symm
    have hq : q = u j := (eq_blockNode h1 hC hqn hyq).trans hyj.symm
    subst hp hq
    rw [← hf] at he
    obtain ⟨k, rfl⟩ := he
    have hk := hcyc.joins k
    have hinj := hcyc.injective_node
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hk with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
    · left; rw [hinj (h₁.symm.trans h₃)]; exact hinj (h₂.symm.trans h₄)
    · right; rw [hinj (h₂.symm.trans h₄)]; exact hinj (h₁.symm.trans h₃)
    · right; rw [hinj (h₁.symm.trans h₃)]; exact hinj (h₂.symm.trans h₄)
    · left; rw [hinj (h₂.symm.trans h₄)]; exact hinj (h₁.symm.trans h₃)
  · rintro (rfl | rfl)
    · exact ⟨f i, hf ▸ ⟨i, rfl⟩, u i, u (finRotate 4 i), hcyc.joins i, hx, hy⟩
    · exact ⟨f j, hf ▸ ⟨j, rfl⟩, u (finRotate 4 j), u j, (hcyc.joins j).symm, hx, hy⟩

end LSAUnrooted

/-! ### `Q⊕_s` and the part of `N` below `LSA(s)` -/

section Quartet

variable {V E X : Type*} {N : RootedNetwork V E X}

/-- The part of `N` below `LSA(s)` ancestral to `s`, rooted at `LSA(s)`: `Q⊕_s` before the vertices
of indegree one and outdegree one are suppressed. -/
abbrev quartetBelow (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (s : Finset X)
    (hs : #s = 4) :=
  lsaNetwork hN (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty

/-- The part of `N` below `LSA(s)` is a phylogenetic network. -/
theorem quartetBelow_isPhylogenetic (hN : N.IsPhylogenetic) {s : Finset X} (hs : #s = 4) :
    (quartetBelow N hN s hs).IsPhylogenetic :=
  lsaNetwork_isPhylogenetic hN (Finset.one_lt_card_iff_nontrivial.mp (by omega))

/-- **`Q⊕_s` of a level-1 network is level-1**: its cycles are made of chains forming cycles of
`N`. -/
theorem isLevelOne_quartetLSA_graph (hN : N.IsPhylogenetic) (h1 : IsLevelOne N.graph)
    {s : Finset X} (hs : #s = 4) : IsLevelOne (quartetLSA N hN s hs).graph :=
  isLevelOne_suppress (quartetBelow_isPhylogenetic hN hs) (isLevelOne_belowNetwork h1)

/-- **The chains of a cycle of `Q⊕_s` form a cycle of `N`.** -/
theorem isCycle_quartetChainArcs (hN : N.IsPhylogenetic) {s : Finset X} (hs : #s = 4)
    {D : Set _} (hD : IsCycle (quartetLSA N hN s hs).graph D) :
    IsCycle N.graph (Subtype.val '' suppressChainArcs (quartetBelow N hN s hs) D) :=
  isCycle_image_val_belowNetwork (isCycle_suppressChainArcs (quartetBelow_isPhylogenetic hN hs) hD)

/-- The LSA of the taxa of `Q⊕_s` is its root. -/
theorem lsa_univ_quartetLSA (hN : IsBinaryRootedNetwork N) {s : Finset X} (hs : #s = 4)
    (hne : (Set.univ : Set (s : Set X)).Nonempty) :
    lsa (quartetLSA_isBinaryRootedNetwork hN hs).1 Set.univ hne = (quartetLSA N hN.1 s hs).root :=
  IsLeastStableAncestor.unique (quartetLSA_isBinaryRootedNetwork hN hs).1 (lsa_spec _ _ _)
    (quartetLSA_isLSANetwork hN hs)

/-- `LSA(X)` is above `LSA(s)` (Lemma 1 (iii)). -/
theorem reaches_lsa_quartet (hN : IsBinaryRootedNetwork N) {s : Finset X} (hs : #s = 4)
    (hne : (Set.univ : Set X).Nonempty) :
    N.graph.Reaches (lsa hN.1 Set.univ hne)
      (lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty) :=
  (lemma1 hN _ (Set.subset_univ _)).2.2

/-- **A vertex of `Q⊕_s` other than its root is a vertex of `N⁻`**: it is strictly below `LSA(s)`,
which is below `LSA(X)`. -/
theorem exists_unrooted_node_of_quartet (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X)
    {s : Finset X} (hs : #s = 4) {z : {v // ¬ (quartetBelow N hN.1 s hs).IsChainVertex v}}
    (hz : z ≠ (quartetLSA N hN.1 s hs).root) :
    z.1.1 ≠ lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty ∧
      ∃ u : SemidirectedVertex hN.1 hX, u.1.1 = z.1.1 := by
  have hzl : z.1.1 ≠
      lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty :=
    fun h => hz (Subtype.ext (Subtype.ext h))
  have hr := (reaches_lsa_quartet hN hs Set.univ_nonempty).trans z.1.2.1
  refine ⟨hzl, exists_unrooted_node hN.1 hr fun h => hzl ?_⟩
  have h₁ : N.graph.Reaches
      (lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty)
      (lsa hN.1 Set.univ Set.univ_nonempty) := h ▸ z.1.2.1
  exact h.trans (eq_of_reaches_of_reaches hN.1.acyclic (reaches_lsa_quartet hN hs _) h₁)

/-- A hybrid node of `Q⊕_s` is a hybrid node of `N`. -/
theorem indegree_eq_two_of_quartetLSA (hN : IsBinaryRootedNetwork N) {s : Finset X} (hs : #s = 4)
    {y : {v // ¬ (quartetBelow N hN.1 s hs).IsChainVertex v}}
    (h2 : (quartetLSA N hN.1 s hs).graph.indegree y = 2) : N.graph.indegree y.1.1 = 2 := by
  have hyr : y ≠ (quartetLSA N hN.1 s hs).root := fun h => by
    rw [h, (quartetLSA_isBinaryRootedNetwork hN hs).1.root_indegree] at h2
    exact absurd h2 (by norm_num)
  have hl : y.1.1 ≠
      lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty :=
    fun h => hyr (Subtype.ext (Subtype.ext h))
  exact le_antisymm (hN.indegree_le_two _)
    ((two_le_indegree_of_suppress_indegree_eq_two (quartetBelow_isPhylogenetic hN.1 hs) h2).trans_eq
      (belowNetwork_indegree hN.1 (lsa_spec hN.1 _ _).1 y.1 hl))

end Quartet

/-! ### The cycles and blocks of `Q⁻_s` and those of `N⁻` -/

section Correspondence

variable {V E X : Type*} {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
  (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {s : Finset X} (hs : #s = 4)

include h1 in
/-- **The cycle of `N` of a cycle of `N⁻` is made of the chains of the cycle of `Q⊕_s` of a cycle of
`Q⁻_s` with the same hybrid node**: both are cycles of `N` through that node (Lemma 3). -/
theorem unrootedCycleArcs_eq_image_quartet {C' : Set _}
    (hC' : IsCycle (quartetUnrooted N hN s hs).graph C') {w}
    (hw : IsHybridNodeOf (quartetUnrooted N hN s hs) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : quartetNode hN hs w = v.1.1) :
    unrootedCycleArcs hN C = Subtype.val '' suppressChainArcs (quartetBelow N hN.1 s hs)
      (unrootedCycleArcs (quartetLSA_isBinaryRootedNetwork hN hs) C') := by
  have := hN.1.finite_arcs
  have hQb := quartetLSA_isBinaryRootedNetwork hN hs
  refine (lemma3 hN h1 (isCycle_unrootedCycleArcs hN hC)).2.2 _
    (isCycle_quartetChainArcs hN.1 hs (isCycle_unrootedCycleArcs hQb hC'))
    ⟨v.1.1, mem_cycleNodes_unrootedCycleArcs hN hv.mem_cycleNodes, ?_⟩
  rw [← hwv]
  exact mem_cycleNodes_image_val_iff.2 ⟨_, mem_cycleNodes_suppressChainArcs
    (quartetBelow_isPhylogenetic hN.1 hs) (mem_cycleNodes_unrootedCycleArcs hQb hw.mem_cycleNodes),
    rfl⟩

include h1 in
/-- **The blocks of `Q⁻_s` are the traces on `s` of the blocks of `N⁻`**: for a cycle of `Q⁻_s` and
the cycle of `N⁻` with the same hybrid node, the block of a taxon of `s` is that of the same node of
`N` in both. A node other than the top of its cycle has the taxa below its arc off the cycle as
block (`exists_reaches_offCycle_of_mem_nodeBlock`, `mem_nodeBlock_of_reaches_offCycle`); these
arcs are those of `Q⊕_s` and their first arcs in `N`, and the tops of the two cycles are the same
node. -/
theorem quartetNode_blockNode {C' : Set _} (hC' : IsCycle (quartetUnrooted N hN s hs).graph C')
    {w} (hw : IsHybridNodeOf (quartetUnrooted N hN s hs) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : quartetNode hN hs w = v.1.1)
    (x : X) (hx : x ∈ s) :
    quartetNode hN hs (blockNode (quartetUnrooted N hN s hs) C' ⟨x, hx⟩) =
      (blockNode (unrooted N hN hX) C x).1.1 := by
  have := hN.1.finite_arcs
  have hQb := quartetLSA_isBinaryRootedNetwork hN hs
  have := hQb.1.finite_arcs
  have h1Q := isLevelOne_quartetLSA_graph hN.1 h1 hs
  have hL := quartetBelow_isPhylogenetic hN.1 hs
  set Q := quartetLSA N hN.1 s hs with hQ_def
  set L := quartetBelow N hN.1 s hs with hL_def
  set D := unrootedCycleArcs hQb C' with hD_def
  have hD : IsCycle Q.graph D := isCycle_unrootedCycleArcs hQb hC'
  set Ĉ := unrootedCycleArcs hN C with hĈ_def
  have hĈ : IsCycle N.graph Ĉ := isCycle_unrootedCycleArcs hN hC
  have hcorr : Ĉ = Subtype.val '' suppressChainArcs L D :=
    unrootedCycleArcs_eq_image_quartet hN h1 hX hs hC' hw hC hv hwv
  have hLD : IsCycle L.graph (suppressChainArcs L D) := isCycle_suppressChainArcs hL hD
  -- the nodes of `D` are nodes of `Ĉ`
  have hnodes : ∀ z ∈ cycleNodes Q.graph D, z.1.1 ∈ cycleNodes N.graph Ĉ := fun z hz => by
    rw [hcorr]
    exact mem_cycleNodes_image_val_iff.2 ⟨_, mem_cycleNodes_suppressChainArcs hL hz, rfl⟩
  -- the arcs of `Q⊕_s` off `D` are off `Ĉ`
  have hoff : ∀ c, c ∉ D → c.1.1 ∉ Ĉ := by
    intro c hc h
    rw [hcorr] at h
    obtain ⟨g, hg, hgc⟩ := h
    obtain rfl : g = c.1 := Subtype.ext hgc
    exact hc ((mem_suppressChainArcs_iff D c).1 hg)
  -- the tops of `D` and `Ĉ`
  obtain ⟨aQ, haQ, -, hGQ, hEQ, hrQ⟩ := h1Q.exists_top hQb.1 hD
  obtain ⟨aN, haN, hFN, -, hEN, hrN⟩ := h1.exists_top hN.1 hĈ
  have htop : aQ.1.1 = aN := by
    refine eq_top_of_forall_target_ne hN.1 hEN hrN (hnodes aQ haQ) fun g hg hgt => ?_
    rw [hcorr] at hg
    obtain ⟨g', ⟨f, hf, hfg⟩, rfl⟩ := hg
    refine hGQ f hf (Subtype.ext ?_)
    have h' : L.graph.target g' = aQ.1 := Subtype.ext hgt
    exact (chainEnd_eq_of_isOnChain hL hfg (by rw [h']; exact aQ.2)).trans h'
  obtain ⟨hq, hxq⟩ := blockNode_spec hC' (⟨x, hx⟩ : (s : Set X))
  obtain ⟨hn, hxn⟩ := blockNode_spec hC x
  set q := blockNode (quartetUnrooted N hN s hs) C' ⟨x, hx⟩ with hq_def
  set n := blockNode (unrooted N hN hX) C x with hn_def
  have hqr : q.1.1 ≠ Q.root := fun h =>
    unrooted_node_ne_lsa q (h.trans (lsa_univ_quartetLSA hN hs _).symm)
  show q.1.1.1.1 = n.1.1
  by_cases hqa : q.1.1 = aQ
  · -- the node of the block of `x` in `Q⁻_s` is the top: so is that in `N⁻`
    rw [hqa, htop]
    by_contra hna
    have hna' : n.1.1 ≠ aN := fun h => hna h.symm
    obtain ⟨c, hc, hcs, hcx⟩ :=
      exists_reaches_offCycle_of_mem_nodeBlock hN h1 hC hEN hrN hn hna' hxn
    have hnĈ : n.1.1 ∈ cycleNodes N.graph Ĉ := mem_cycleNodes_unrootedCycleArcs hN hn
    rw [hcorr] at hnĈ
    obtain ⟨yL, hyL, hyLn⟩ := mem_cycleNodes_image_val_iff.1 hnĈ
    -- the arc `c` is below `LSA(s)`
    have hcB : c ∈ N.belowArcs
        (lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty)
        (s : Set X) := ⟨by rw [hcs, ← hyLn]; exact yL.2.1, ⟨x, hx, hcx⟩⟩
    set cL : N.belowArcs _ (s : Set X) := ⟨c, hcB⟩ with hcL_def
    have hcLs : L.graph.source cL = yL := Subtype.ext (hcs.trans hyLn.symm)
    have hcL : cL ∉ suppressChainArcs L D := fun h =>
      hc (show c ∈ Ĉ by rw [hcorr]; exact ⟨cL, h, rfl⟩)
    -- the vertex `yL` is not a chain vertex: it has an arc of the cycle leaving it, and `c`
    have hyc : ¬ L.IsChainVertex yL := by
      intro hyc
      obtain ⟨f₁, hf₁, f₂, hf₂, h12, hu₁, hu₂⟩ := hLD.exists_ne_of_mem
        (fun e _ h => hL.acyclic _ (.single ⟨e, rfl, h.symm⟩)) hyL
      obtain ⟨i, hi⟩ := (L.graph.indegree_eq_one_iff yL).mp hyc.1
      obtain ⟨o, ho⟩ := (L.graph.outdegree_eq_one_iff yL).mp hyc.2
      have hco := (ho cL).mp hcLs
      have key : ∀ e ∈ suppressChainArcs L D, (L.graph.source e = yL ∨ L.graph.target e = yL) →
          L.graph.target e = yL := by
        rintro e he (h | h)
        · exact absurd (((ho e).mp h).trans hco.symm ▸ he) hcL
        · exact h
      exact h12 (((hi f₁).mp (key f₁ hf₁ hu₁)).trans ((hi f₂).mp (key f₂ hf₂ hu₂)).symm)
    have hyD : (⟨yL, hyc⟩ : {v // ¬ L.IsChainVertex v}) ∈ cycleNodes Q.graph D :=
      mem_cycleNodes_suppress_of_mem hL hyL
    have hcQ : (⟨cL, by rw [hcLs]; exact hyc⟩ : {e // ¬ L.IsChainVertex (L.graph.source e)}) ∉ D :=
      fun h => hcL ((mem_suppressChainArcs_iff D _).2 h)
    have hcQx : Q.graph.Reaches (Q.graph.target ⟨cL, by rw [hcLs]; exact hyc⟩)
        (Q.leaf ⟨x, hx⟩) := by
      have h₁ : L.graph.Reaches (L.graph.target cL) (L.leaf ⟨x, hx⟩) :=
        belowNetwork_reaches_iff.2 hcx
      exact suppress_reaches_of_reaches hL _ _
        (reaches_of_chainEnd_of_reaches hL h₁ (not_isChainVertex_leaf hL _))
    -- the vertex `yL` is not the root of `Q⊕_s`, which is `LSA(s)`
    have hyr : (⟨yL, hyc⟩ : {v // ¬ L.IsChainVertex v}) ≠ Q.root := by
      intro h
      apply hna'
      have hy : n.1.1 = lsa hN.1 (s : Set X)
          (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty :=
        hyLn.symm.trans (congrArg (fun z => z.1.1) h)
      have haNĈ := haN
      rw [hcorr] at haNĈ
      obtain ⟨aL, -, haL⟩ : ∃ z ∈ cycleNodes L.graph (suppressChainArcs L D), z.1 = aN :=
        mem_cycleNodes_image_val_iff.1 haNĈ
      have h₂ : N.graph.Reaches aN n.1.1 := hFN _ (mem_cycleNodes_unrootedCycleArcs hN hn)
      rw [hy] at h₂ ⊢
      exact eq_of_reaches_of_reaches hN.1.acyclic (haL ▸ aL.2.1) h₂
    obtain ⟨u, hu, huy⟩ := exists_mem_cycleNodes_of_unrootedCycleArcs hQb hyD
      (by rw [lsa_univ_quartetLSA hN hs]; exact hyr)
    have hxu := mem_nodeBlock_of_reaches_offCycle hQb h1Q hC' hu hcQ
      (Subtype.ext (show L.graph.source cL = u.1.1.1 by rw [hcLs, huy])) hcQx
    have huq : u = q := eq_blockNode h1Q hC' hu hxu
    apply hna'
    rw [← htop, ← hqa, ← huq, huy]
    exact hyLn.symm
  · obtain ⟨c, hc, hcs, hcx⟩ :=
      exists_reaches_offCycle_of_mem_nodeBlock hQb h1Q hC' hEQ hrQ hq hqa hxq
    have hcNs : N.graph.source c.1.1 = q.1.1.1.1 := congrArg (fun z => z.1.1) hcs
    have hcNx : N.graph.Reaches (N.graph.target c.1.1) (N.leaf x) :=
      (belowNetwork_reaches_iff.1 (chainReach_chainEnd hL (L.graph.target c.1)).reaches).trans
        (belowNetwork_reaches_iff.1 (reaches_val_of_suppress_reaches hL hcx))
    obtain ⟨-, u, huq⟩ := exists_unrooted_node_of_quartet hN hX hs hqr
    obtain ⟨u', hu', hu'q⟩ := exists_mem_cycleNodes_of_unrootedCycleArcs hN
      (hnodes _ (mem_cycleNodes_unrootedCycleArcs hQb hq))
      (by rw [← huq]; exact unrooted_node_ne_lsa u)
    have hxu' := mem_nodeBlock_of_reaches_offCycle hN h1 hC hu' (hoff c hc)
      (hcNs.trans hu'q.symm) hcNx
    exact hu'q.symm.trans (congrArg (fun z => z.1.1) (eq_blockNode h1 hC hu' hxu'))

/-- A node of `Q⁻_s` is determined by its node of `N`. -/
theorem quartetNode_injective : Function.Injective (quartetNode hN hs) :=
  fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext h)))

include h1 in
/-- Two taxa of `s` are in the same block of the cycle of `N⁻` exactly when they are in the same
block of the cycle of `Q⁻_s` with the same hybrid node. -/
theorem blockNode_eq_iff_quartet {C' : Set _} (hC' : IsCycle (quartetUnrooted N hN s hs).graph C')
    {w} (hw : IsHybridNodeOf (quartetUnrooted N hN s hs) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : quartetNode hN hs w = v.1.1) {x y : X}
    (hx : x ∈ s) (hy : y ∈ s) :
    blockNode (unrooted N hN hX) C x = blockNode (unrooted N hN hX) C y ↔
      blockNode (quartetUnrooted N hN s hs) C' ⟨x, hx⟩ =
        blockNode (quartetUnrooted N hN s hs) C' ⟨y, hy⟩ := by
  rw [← (quartetNode_injective hN hs).eq_iff,
    quartetNode_blockNode hN h1 hX hs hC' hw hC hv hwv x hx,
    quartetNode_blockNode hN h1 hX hs hC' hw hC hv hwv y hy]
  exact ⟨fun h => congrArg (fun z => z.1.1) h, fun h => unrooted_node_ext h⟩

include h1 in
/-- A taxon of `s` is in the hybrid block of the cycle of `N⁻` exactly when it is in the hybrid
block of the cycle of `Q⁻_s` with the same hybrid node. -/
theorem blockNode_eq_hybrid_iff_quartet {C' : Set _}
    (hC' : IsCycle (quartetUnrooted N hN s hs).graph C') {w}
    (hw : IsHybridNodeOf (quartetUnrooted N hN s hs) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : quartetNode hN hs w = v.1.1) {x : X}
    (hx : x ∈ s) :
    blockNode (unrooted N hN hX) C x = v ↔
      blockNode (quartetUnrooted N hN s hs) C' ⟨x, hx⟩ = w := by
  rw [← (quartetNode_injective hN hs).eq_iff,
    quartetNode_blockNode hN h1 hX hs hC' hw hC hv hwv x hx, hwv]
  exact ⟨fun h => congrArg (fun z => z.1.1) h, fun h => unrooted_node_ext h⟩

include h1 in
/-- **An edge of a cycle of `Q⁻_s` is a path along the cycle of `N⁻` with the same hybrid node**,
through nodes that are not nodes of `Q⁻_s`: the chain of its arc of `Q⊕_s`, or, for the edge merged
at the root of `Q⊕_s`, the chains of the two arcs leaving `LSA(s)`, joined at `LSA(s)` or, when
`LSA(s) = LSA(X)`, by the edge of `N⁻` merged there. So a set `F` of nodes of `N⁻` that are nodes of
`Q⁻_s` is avoided when the two ends are not in it. -/
theorem reflTransGen_unrooted_of_joins_quartet {C' : Set _}
    (hC' : IsCycle (quartetUnrooted N hN s hs).graph C') {w}
    (hw : IsHybridNodeOf (quartetUnrooted N hN s hs) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : quartetNode hN hs w = v.1.1)
    {F : Set (SemidirectedVertex hN.1 hX)}
    (hF : ∀ n ∈ F, ∃ z : {v // ¬ (quartetBelow N hN.1 s hs).IsChainVertex v},
      z ≠ (quartetLSA N hN.1 s hs).root ∧ z.1.1 = n.1.1)
    {e} (he : e ∈ C') {u₁ u₂} (hj : Joins (quartetUnrooted N hN s hs).graph e u₁ u₂)
    {n₁ n₂ : SemidirectedVertex hN.1 hX} (hn₁ : n₁.1.1 = quartetNode hN hs u₁)
    (hn₂ : n₂.1.1 = quartetNode hN hs u₂) (hn₁F : n₁ ∉ F) (hn₂F : n₂ ∉ F) :
    Relation.ReflTransGen (fun a b => (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F) n₁
      n₂ := by
  have := hN.1.finite_arcs
  have hQb := quartetLSA_isBinaryRootedNetwork hN hs
  have hL := quartetBelow_isPhylogenetic hN.1 hs
  have hXs : Nontrivial (s : Set X) := (Finset.one_lt_card_iff_nontrivial.mp (by omega)).coe_sort
  set Q := quartetLSA N hN.1 s hs with hQ_def
  set L := quartetBelow N hN.1 s hs with hL_def
  set D := unrootedCycleArcs hQb C' with hD_def
  set Ĉ := unrootedCycleArcs hN C with hĈ_def
  have hcorr : Ĉ = Subtype.val '' suppressChainArcs L D :=
    unrootedCycleArcs_eq_image_quartet hN h1 hX hs hC' hw hC hv hwv
  -- the vertices of `N` that are not nodes of `F`
  let P : V → Prop := fun z => ∀ n ∈ F, n.1.1 ≠ z
  have hPF : ∀ n : SemidirectedVertex hN.1 hX, P n.1.1 → n ∉ F := fun n hn hnF => hn n hnF rfl
  have hFP : ∀ n : SemidirectedVertex hN.1 hX, n ∉ F → P n.1.1 := fun n hn n' hn' h =>
    hn (unrooted_node_ext h ▸ hn')
  have hPchain : ∀ z, L.IsChainVertex z → P z.1 := fun z hz n hn h => by
    obtain ⟨y, -, hy⟩ := hF n hn
    exact y.2 (Subtype.ext (hy.trans h) ▸ hz)
  have hProot : P (lsa hN.1 (s : Set X)
      (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty) := fun n hn h => by
    obtain ⟨y, hyr, hy⟩ := hF n hn
    exact hyr (Subtype.ext (Subtype.ext (hy.trans h)))
  have hmemĈ : ∀ f ∈ D, ∀ g, L.IsOnChain f.1 g → g.1 ∈ Ĉ := fun f hf g hg => by
    rw [hcorr]
    exact ⟨g, ⟨f, hf, hg⟩, rfl⟩
  -- directed steps along `Ĉ` to vertices that are not nodes of `F`
  let R : V → V → Prop := fun x y => ∃ g ∈ Ĉ, N.graph.source g = x ∧ N.graph.target g = y ∧ P y
  -- along the chain of an arc of `D`
  have hchain : ∀ f ∈ D, P (Q.graph.target f).1.1 → P (N.graph.target f.1.1) ∧
      Relation.ReflTransGen R (N.graph.target f.1.1) (Q.graph.target f).1.1 := by
    intro f hf hPf
    have h₁ := reflTransGen_chain_targets f (P := fun z => P z.1) (fun z hz => hPchain z hz)
      (chainReach_chainEnd hL _) hPf
    refine ⟨?_, Relation.ReflTransGen.lift Subtype.val ?_ _ _ h₁⟩
    · by_cases hc : L.IsChainVertex (L.graph.target f.1)
      · exact hPchain _ hc
      · have : chainEnd hL (L.graph.target f.1) = L.graph.target f.1 := chainEnd_eq_self hL hc
        change P (L.graph.target f.1).1
        rw [← this]
        exact hPf
    · rintro x y ⟨g, hg, hgs, hgt, hPy⟩
      exact ⟨g.1, hmemĈ f hf g hg, congrArg Subtype.val hgs, congrArg Subtype.val hgt, hPy⟩
  -- directed paths along `Ĉ` are walks of `N⁻` along `C`
  have hlift : ∀ (a : SemidirectedVertex hN.1 hX) {b : V}, P a.1.1 →
      Relation.ReflTransGen R a.1.1 b → ∀ b' : SemidirectedVertex hN.1 hX, b'.1.1 = b →
        Relation.ReflTransGen (fun a b => (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F)
          a b' := by
    intro a b ha hab b' hb'
    obtain ⟨b'', hb'', h⟩ := exists_unrooted_reflTransGen hN C a ha hab
    obtain rfl : b'' = b' := unrooted_node_ext (hb''.trans hb'.symm)
    refine Relation.ReflTransGen.mono ?_ _ _ h
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy, hPF x hx, hPF y hy⟩
  have hsymm : ∀ a b, (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F →
      (unrooted N hN hX).graph.AdjOn C b a ∧ b ∉ F ∧ a ∉ F := fun a b ⟨h, ha, hb⟩ =>
    ⟨(unrooted N hN hX).graph.adjOn_symm h, hb, ha⟩
  -- from the source of `e` to its target
  have core : ∀ n₁ n₂ : SemidirectedVertex hN.1 hX,
      n₁.1.1 = quartetNode hN hs ((quartetUnrooted N hN s hs).graph.source e) →
      n₂.1.1 = quartetNode hN hs ((quartetUnrooted N hN s hs).graph.target e) → n₁ ∉ F → n₂ ∉ F →
      Relation.ReflTransGen (fun a b => (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F)
        n₁ n₂ := by
    intro n₁ n₂ hn₁ hn₂ hn₁F hn₂F
    have heD : e.1.1 ∈ D := ⟨e, he, Or.inl rfl⟩
    have hP₂ : P (Q.graph.target e.1.1).1.1 := by
      have : (Q.graph.target e.1.1).1.1 = n₂.1.1 := hn₂.symm
      rw [this]
      exact hFP n₂ hn₂F
    obtain ⟨hPt, hpath⟩ := hchain _ heD hP₂
    have heĈ : e.1.1.1.1 ∈ Ĉ := hmemĈ _ heD _ (Or.inl rfl)
    by_cases hr : Q.graph.source e.1.1 = Q.root
    · -- the edge merged at the root of `Q⊕_s`: the two arcs leaving `LSA(s)`
      have hr' := hr.trans (lsa_univ_quartetLSA hN hs Set.univ_nonempty).symm
      have hs₁ := unrooted_source_val_of_eq hQb e hr'
      have hrD : (rootTreeArc hQb.1 hQb.2 hXs).1 ∈ D := ⟨e, he, Or.inr ⟨hr', rfl⟩⟩
      have hn₁' : n₁.1.1 = (Q.graph.target (rootTreeArc hQb.1 hQb.2 hXs).1).1.1 :=
        hn₁.trans (congrArg (fun z => z.1.1) hs₁)
      have hP₁ : P (Q.graph.target (rootTreeArc hQb.1 hQb.2 hXs).1).1.1 := by
        rw [← hn₁']
        exact hFP n₁ hn₁F
      obtain ⟨hPr, hpathr⟩ := hchain _ hrD hP₁
      have hrĈ : (rootTreeArc hQb.1 hQb.2 hXs).1.1.1 ∈ Ĉ := hmemĈ _ hrD _ (Or.inl rfl)
      have hrN : N.graph.source (rootTreeArc hQb.1 hQb.2 hXs).1.1.1 =
          lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty :=
        congrArg (fun z => z.1.1) ((source_rootTreeArc_val hQb).trans (lsa_univ_quartetLSA hN hs _))
      have heN : N.graph.source e.1.1.1.1 =
          lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty :=
        congrArg (fun z => z.1.1) hr
      have hne : (rootTreeArc hQb.1 hQb.2 hXs).1.1.1 ≠ e.1.1.1.1 := fun h =>
        e.2 (Subtype.ext (Subtype.ext (Subtype.ext h.symm)))
      by_cases hm :
          lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty =
            lsa hN.1 Set.univ Set.univ_nonempty
      · -- `LSA(s) = LSA(X)`: the edge of `N⁻` merged at `LSA(X)` joins the two children
        have hrm := hrN.trans hm
        have hem := heN.trans hm
        -- the nodes of `N⁻` of the two children
        have hchild : ∀ g : E, N.graph.source g = lsa hN.1 Set.univ Set.univ_nonempty →
            ∃ a : SemidirectedVertex hN.1 hX, a.1.1 = N.graph.target g := fun g hg =>
          exists_unrooted_node hN.1 (Relation.ReflTransGen.single ⟨g, hg, rfl⟩) fun h =>
            hN.1.acyclic _ (.single ⟨g, hg, h ▸ rfl⟩)
        obtain ⟨a₁, ha₁⟩ := hchild _ hrm
        obtain ⟨a₂, ha₂⟩ := hchild _ hem
        have w₁ := hlift a₁ (by rw [ha₁]; exact hPr) (by rw [ha₁]; exact hpathr) n₁ hn₁'
        have w₂ := hlift a₂ (by rw [ha₂]; exact hPt) (by rw [ha₂]; exact hpath) n₂ hn₂
        -- `rootTreeArc` of `N` is one of the two arcs leaving `LSA(X)`
        have hout : N.graph.outdegree (lsa hN.1 Set.univ Set.univ_nonempty) = 2 :=
          le_antisymm (hN.outdegree_le_two _) (by
            unfold DirectedMultigraph.outdegree
            rw [← Set.ncard_pair hne]
            refine Set.ncard_le_ncard ?_ (Set.toFinite _)
            rintro g (rfl | rfl)
            exacts [hrm, hem])
        have he₀ : (rootTreeArc hN.1 hN.2 hX).1 ∈ ({(rootTreeArc hQb.1 hQb.2 hXs).1.1.1,
            e.1.1.1.1} : Set E) := by
          rw [← eq_or_eq_of_outdegree_eq_two hout hne hrm hem]
          exact source_rootTreeArc_val hN
        -- the edge of `N⁻` of the other arc
        have hstep : ∀ o : E, o ∈ Ĉ → N.graph.source o = lsa hN.1 Set.univ Set.univ_nonempty →
            o ≠ (rootTreeArc hN.1 hN.2 hX).1 → ∀ a b : SemidirectedVertex hN.1 hX,
            a.1.1 = N.graph.target (rootTreeArc hN.1 hN.2 hX).1 → b.1.1 = N.graph.target o →
            P a.1.1 → P b.1.1 →
            (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F := by
          intro o hoĈ hos ho a b ha hb hPa hPb
          have hoB : o ∈ N.belowArcs (lsa hN.1 Set.univ Set.univ_nonempty) Set.univ :=
            ⟨by rw [hos]; exact .refl, mem_ancestralVertices_univ hN.1 _⟩
          let c : SemidirectedArc hN.1 hN.2 hX := ⟨⟨o, hoB⟩, fun h => ho (congrArg Subtype.val h)⟩
          have hcC : c ∈ C := (mem_unrootedCycleArcs_iff hN C c).1 hoĈ
          refine ⟨⟨c, hcC, Or.inl ⟨unrooted_node_ext ?_, unrooted_node_ext hb.symm⟩⟩, hPF a hPa,
            hPF b hPb⟩
          rw [unrooted_source_val_of_eq hN c hos, ha]
        rcases he₀ with h₀ | h₀
        · have hst := hstep _ heĈ hem (fun h => hne (h.trans h₀).symm) a₁ a₂
            (by rw [ha₁, ← h₀]) ha₂ (by rw [ha₁]; exact hPr) (by rw [ha₂]; exact hPt)
          exact (reflTransGen_symm_of_symm hsymm w₁).trans (Relation.ReflTransGen.head hst w₂)
        · have hst := hstep _ hrĈ hrm (fun h => hne (h.trans h₀)) a₂ a₁
            (by rw [ha₂, ← h₀]) ha₁ (by rw [ha₂]; exact hPt) (by rw [ha₁]; exact hPr)
          exact (reflTransGen_symm_of_symm hsymm w₁).trans
            (Relation.ReflTransGen.head (hsymm _ _ hst) w₂)
      · -- `LSA(s)` is a node of `N⁻`
        obtain ⟨nl, hnl⟩ := exists_unrooted_node (hX := hX) hN.1 (reaches_lsa_quartet hN hs _) hm
        have hPl : P nl.1.1 := by rw [hnl]; exact hProot
        have w₁ := hlift nl hPl (Relation.ReflTransGen.head ⟨_, hrĈ, hrN.trans hnl.symm, rfl, hPr⟩
          hpathr) n₁ hn₁'
        have w₂ := hlift nl hPl (Relation.ReflTransGen.head ⟨_, heĈ, heN.trans hnl.symm, rfl, hPt⟩
          hpath) n₂ hn₂
        exact (reflTransGen_symm_of_symm hsymm w₁).trans w₂
    · -- an arc of `Q⊕_s`
      have hs₁ := unrooted_source_val_of_ne hQb e
        (fun h => hr (h.trans (lsa_univ_quartetLSA hN hs Set.univ_nonempty)))
      have hn₁' : n₁.1.1 = N.graph.source e.1.1.1.1 := hn₁.trans (congrArg (fun z => z.1.1) hs₁)
      exact hlift n₁ (hFP n₁ hn₁F)
        (Relation.ReflTransGen.head ⟨_, heĈ, hn₁'.symm, rfl, hPt⟩ hpath) n₂ hn₂
  rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact core n₁ n₂ (by rw [h₁]; exact hn₁) (by rw [h₂]; exact hn₂) hn₁F hn₂F
  · exact reflTransGen_symm_of_symm hsymm
      (core n₂ n₁ (by rw [h₁]; exact hn₂) (by rw [h₂]; exact hn₁) hn₂F hn₁F)

end Correspondence

/-! ### The targets -/

section Targets

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] {N : RootedNetwork V E X}

/-- **The hybrid node determined by `s`** (Section 7): `s` determines the hybrid node `v` of `N⁻`
exactly when the cycle `C_v` of `N⁻` separates `s`, its four taxa in four distinct `v`-blocks, one of
them in the hybrid block. The 4-cycle of `Q⁻_s` is the cycle that `C_v` induces on `s`. -/
theorem determines_iff_separatesQuartet (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) (v : SemidirectedVertex hN.1 hX) :
    Determines hN s hs v.1.1 ↔ ∃ C, SeparatesQuartet (unrooted N hN hX) C v s := by
  have := hN.1.finite_arcs
  have hQb := quartetLSA_isBinaryRootedNetwork hN hs
  have := hQb.1.finite_arcs
  have h1Q := isLevelOne_quartetLSA_graph hN.1 h1 hs
  have hXs : Nontrivial (s : Set X) := (Finset.one_lt_card_iff_nontrivial.mp (by omega)).coe_sort
  have hcardQ : Nat.card (s : Set X) = 4 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hs]
  constructor
  · -- the cycle of `N⁻` through the hybrid node of the 4-cycle of `Q⁻_s` separates `s`
    rintro ⟨C', w, hC', hC'4, hw, hwv⟩
    have hN2 : N.graph.indegree v.1.1 = 2 := by
      rw [← hwv]
      exact indegree_eq_two_of_quartetLSA hN hs hw.unrooted_indegree
    obtain ⟨C, hC, hv⟩ := exists_isHybridNodeOf_of_indegree_eq_two hN h1 v hN2
    refine ⟨C, (separatesQuartet_iff h1 hC hv s).2 ⟨?_, ?_⟩⟩
    · -- the four nodes of the 4-cycle are the nodes of the blocks of the four taxa
      have hinj : Function.Injective (blockNode (quartetUnrooted N hN s hs) C') := by
        have h4 : (blockNode (quartetUnrooted N hN s hs) C' '' Set.univ).ncard =
            (Set.univ : Set (s : Set X)).ncard := by
          rw [Set.image_univ, ← cycleNodes_eq_range_blockNode hQb h1Q hC', ncard_cycleNodes hC',
            hC'4, Set.ncard_univ, hcardQ]
        exact Set.injOn_univ.1 (Set.injOn_of_ncard_image_eq h4)
      intro x hx y hy hxy
      exact congrArg Subtype.val
        (hinj ((blockNode_eq_iff_quartet hN h1 hX hs hC' hw hC hv hwv hx hy).1 hxy))
    · obtain ⟨x', hx'⟩ := exists_blockNode_eq h1Q hC' hw.mem_cycleNodes
      exact ⟨x'.1, x'.2, (blockNode_eq_hybrid_iff_quartet hN h1 hX hs hC' hw hC hv hwv x'.2).2 hx'⟩
  · -- the cycle of `Q⁻_s` through `v` is a 4-cycle
    rintro ⟨C, hC, hv, hblk, x₀, hx₀, hd⟩
    have hreach := (descendsFrom_iff_reaches hN h1 hC hv x₀).1 hd
    -- a taxon of `s` not below `v`
    obtain ⟨y₀, hy₀, hyx⟩ := Finset.exists_mem_ne (by omega : 1 < #s) x₀
    have hny : ¬ N.graph.Reaches v.1.1 (N.leaf y₀) := fun h => hblk x₀ hx₀ y₀ hy₀ hyx.symm (by
      rw [sameBlock_iff_blockNode_eq h1 hC, (blockNode_eq_iff_descendsFrom h1 hC hv x₀).2 hd,
        (blockNode_eq_iff_descendsFrom h1 hC hv y₀).2
          ((descendsFrom_iff_reaches hN h1 hC hv y₀).2 h)])
    have hst := (lsa_spec hN.1 (s : Set X)
      (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty).1
    have hvl : ¬ N.graph.Reaches v.1.1
        (lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty) :=
      fun h => hny (h.trans (hst.reaches_leaf hN.1 hy₀))
    -- the two parents of `v` are below `LSA(s)`
    obtain ⟨p₁, p₂, hne, hps⟩ := Set.ncard_eq_two.mp hv.unrooted_indegree
    have hp₁ : N.graph.target p₁ = v.1.1 := by
      have : p₁ ∈ {f | N.graph.target f = v.1.1} := by rw [hps]; exact Or.inl rfl
      exact this
    have hp₂ : N.graph.target p₂ = v.1.1 := by
      have : p₂ ∈ {f | N.graph.target f = v.1.1} := by rw [hps]; exact Or.inr rfl
      exact this
    have hpB : ∀ p, N.graph.target p = v.1.1 → p ∈ N.belowArcs
        (lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty)
        (s : Set X) := fun p hp =>
      ⟨hst.reaches_source hN.1 hx₀ (by rw [hp]; exact hreach) (by rw [hp]; exact hvl),
        ⟨x₀, hx₀, by rw [hp]; exact hreach⟩⟩
    have hvB : v.1.1 ∈ N.belowVertices
        (lsa hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty)
        (s : Set X) :=
      ⟨((hpB p₁ hp₁).1).tail ⟨p₁, rfl, hp₁⟩, ⟨x₀, hx₀, hreach⟩⟩
    have hL := quartetBelow_isPhylogenetic hN.1 hs
    -- `v` is a vertex of `Q⊕_s`, entered by two of its arcs
    have := hL.finite_arcs
    have hchain : ¬ (quartetBelow N hN.1 s hs).IsChainVertex ⟨v.1.1, hvB⟩ := fun h => by
      have h2 := two_le_indegree_of_ne_targets (G := (quartetBelow N hN.1 s hs).graph)
        (w := ⟨v.1.1, hvB⟩) (e := ⟨p₁, hpB p₁ hp₁⟩) (e' := ⟨p₂, hpB p₂ hp₂⟩)
        (fun h => hne (congrArg Subtype.val h)) (Subtype.ext hp₁) (Subtype.ext hp₂)
      have := h.1
      omega
    have hy2 : (quartetLSA N hN.1 s hs).graph.indegree ⟨⟨v.1.1, hvB⟩, hchain⟩ = 2 :=
      le_antisymm (hQb.indegree_le_two _) (two_le_suppress_indegree hL
        (p₁ := ⟨p₁, hpB p₁ hp₁⟩) (p₂ := ⟨p₂, hpB p₂ hp₂⟩) (fun h => hne (congrArg Subtype.val h))
        (Subtype.ext hp₁) (Subtype.ext hp₂))
    have hyr : (⟨⟨v.1.1, hvB⟩, hchain⟩ : {v // ¬ (quartetBelow N hN.1 s hs).IsChainVertex v}) ≠
        (quartetLSA N hN.1 s hs).root := fun h =>
      hvl (by rw [show v.1.1 = _ from congrArg (fun z => z.1.1) h]; exact .refl)
    obtain ⟨w, hwy⟩ := exists_unrooted_node (hX := hXs) (a := ⟨⟨v.1.1, hvB⟩, hchain⟩) hQb.1
      (by rw [lsa_univ_quartetLSA hN hs]; exact hQb.1.root_reaches _)
      (by rw [lsa_univ_quartetLSA hN hs]; exact hyr)
    obtain ⟨C', hC', hw⟩ := exists_isHybridNodeOf_of_indegree_eq_two hQb h1Q w (hwy ▸ hy2)
    have hwv : quartetNode hN hs w = v.1.1 := congrArg (fun z => z.1.1) hwy
    refine ⟨C', w, hC', ?_, hw, hwv⟩
    -- the nodes of the blocks of the four taxa are distinct
    have hinj : Function.Injective (blockNode (quartetUnrooted N hN s hs) C') := by
      intro x' y' h
      have h' := (blockNode_eq_iff_quartet hN h1 hX hs hC' hw hC hv hwv x'.2 y'.2).2 h
      exact Subtype.ext (by_contra fun hne =>
        hblk _ x'.2 _ y'.2 hne ((sameBlock_iff_blockNode_eq h1 hC _ _).2 h'))
    rw [← ncard_cycleNodes hC', cycleNodes_eq_range_blockNode hQb h1Q hC', ← Set.image_univ,
      Set.ncard_image_of_injective _ hinj, Set.ncard_univ, hcardQ]

/-- **The order of the blocks of the 4-cycle of `Q⁻_s`** is that of the blocks of `C_v` that contain
taxa of `s`: the blocks of `a` and `c` are adjacent in the 4-cycle of `Q⁻_s` exactly when they are
joined along `C_v` avoiding the blocks of the other two taxa. -/
theorem adjacentBlocks_quartetUnrooted_iff [DecidableEq X] (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) {C : Set _} {v : SemidirectedVertex hN.1 hX}
    (hsep : SeparatesQuartet (unrooted N hN hX) C v s) {C' : Set _}
    (hC' : IsCycle (quartetUnrooted N hN s hs).graph C') (hC'4 : C'.ncard = 4) {w}
    (hw : IsHybridNodeOf (quartetUnrooted N hN s hs) C' w) (hwv : quartetNode hN hs w = v.1.1)
    {a c : X} (ha : a ∈ s) (hc : c ∈ s) (hac : a ≠ c) :
    AdjacentBlocks (quartetUnrooted N hN s hs) C' ⟨a, ha⟩ ⟨c, hc⟩ ↔
      JoinedAvoiding (unrooted N hN hX) C ↑((s.erase a).erase c) a c := by
  obtain ⟨hC, hv, hblk, -⟩ := hsep
  have := hN.1.finite_arcs
  have hQb := quartetLSA_isBinaryRootedNetwork hN hs
  have := hQb.1.finite_arcs
  have h1Q := isLevelOne_quartetLSA_graph hN.1 h1 hs
  have hXs : Nontrivial (s : Set X) := (Finset.one_lt_card_iff_nontrivial.mp (by omega)).coe_sort
  -- the blocks of distinct taxa of `s` are distinct, in `N⁻` and in `Q⁻_s`
  have hβN : ∀ {x y : X}, x ∈ s → y ∈ s → x ≠ y →
      blockNode (unrooted N hN hX) C x ≠ blockNode (unrooted N hN hX) C y :=
    fun hx hy hxy h => hblk _ hx _ hy hxy ((sameBlock_iff_blockNode_eq h1 hC _ _).2 h)
  have hβQ : ∀ {x y : X} (hx : x ∈ s) (hy : y ∈ s), x ≠ y →
      blockNode (quartetUnrooted N hN s hs) C' ⟨x, hx⟩ ≠
        blockNode (quartetUnrooted N hN s hs) C' ⟨y, hy⟩ :=
    fun hx hy hxy h =>
      hβN hx hy hxy ((blockNode_eq_iff_quartet hN h1 hX hs hC' hw hC hv hwv hx hy).2 h)
  have hTs : ∀ {x y t : X}, t ∈ (↑((s.erase x).erase y) : Set X) ↔ t ∈ s ∧ t ≠ x ∧ t ≠ y := by
    intro x y t
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_erase]
    tauto
  -- adjacent blocks of `Q⁻_s` are joined along `C` avoiding the other two blocks
  have fwd : ∀ {x y : X} (hx : x ∈ s) (hy : y ∈ s),
      AdjacentBlocks (quartetUnrooted N hN s hs) C' ⟨x, hx⟩ ⟨y, hy⟩ →
      JoinedAvoiding (unrooted N hN hX) C ↑((s.erase x).erase y) x y := by
    rintro x y hx hy ⟨e, he, u₁, u₂, hj, hxu, hyu⟩
    have hu₁ : u₁ ∈ cycleNodes (quartetUnrooted N hN s hs).graph C' := by
      rcases hj with ⟨h, -⟩ | ⟨-, h⟩
      exacts [⟨e, he, Or.inl h⟩, ⟨e, he, Or.inr h⟩]
    have hu₂ : u₂ ∈ cycleNodes (quartetUnrooted N hN s hs).graph C' := by
      rcases hj with ⟨-, h⟩ | ⟨h, -⟩
      exacts [⟨e, he, Or.inr h⟩, ⟨e, he, Or.inl h⟩]
    rw [joinedAvoiding_iff_reflTransGen hN h1 hC]
    refine reflTransGen_unrooted_of_joins_quartet hN h1 hX hs hC' hw hC hv hwv ?_ he hj ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨t, ht, rfl⟩ := (mem_blockNodes_iff_blockNode hN h1 hC).1 hn
      obtain ⟨hts, -, -⟩ := hTs.1 ht
      exact ⟨(blockNode (quartetUnrooted N hN s hs) C' ⟨t, hts⟩).1.1,
        fun h => unrooted_node_ne_lsa _ (h.trans (lsa_univ_quartetLSA hN hs _).symm),
        quartetNode_blockNode hN h1 hX hs hC' hw hC hv hwv t hts⟩
    · rw [eq_blockNode h1Q hC' hu₁ hxu]
      exact (quartetNode_blockNode hN h1 hX hs hC' hw hC hv hwv x hx).symm
    · rw [eq_blockNode h1Q hC' hu₂ hyu]
      exact (quartetNode_blockNode hN h1 hX hs hC' hw hC hv hwv y hy).symm
    · intro hn
      obtain ⟨t, ht, h⟩ := (mem_blockNodes_iff_blockNode hN h1 hC).1 hn
      obtain ⟨hts, htx, -⟩ := hTs.1 ht
      exact hβN hts hx htx h
    · intro hn
      obtain ⟨t, ht, h⟩ := (mem_blockNodes_iff_blockNode hN h1 hC).1 hn
      obtain ⟨hts, -, hty⟩ := hTs.1 ht
      exact hβN hts hy hty h
  refine ⟨fwd ha hc, fun hJ => ?_⟩
  by_contra hadj
  -- the other two taxa `b` and `d` of `s`
  have hT2 : #((s.erase a).erase c) = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hac.symm, hc⟩), Finset.card_erase_of_mem ha,
      hs]
  obtain ⟨b, d, hbd, hT⟩ := Finset.card_eq_two.1 hT2
  have hb : b ∈ (s.erase a).erase c := by rw [hT]; exact Finset.mem_insert_self _ _
  have hd : d ∈ (s.erase a).erase c := by
    rw [hT]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [Finset.mem_erase, Finset.mem_erase] at hb hd
  obtain ⟨hbc, hba, hbs⟩ := hb
  obtain ⟨hdc, hda, hds⟩ := hd
  -- the positions of the blocks around the 4-cycle of `Q⁻_s`
  obtain ⟨k, u, f, hcyc, hrange⟩ := id hC'
  have hk : k = 4 := by
    rw [← hC'4, ← hrange, Set.ncard_range_of_injective hcyc.injective_edge,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  subst hk
  have hnodes : cycleNodes (quartetUnrooted N hN s hs).graph C' = Set.range u := by
    rw [← hrange]
    exact hcyc.cycleNodes_eq
  have hpos : ∀ {x : X} (hx : x ∈ s), ∃ i, u i = blockNode (quartetUnrooted N hN s hs) C' ⟨x, hx⟩ :=
    fun hx => by
      have := blockNode_mem hC' ⟨_, hx⟩
      rw [hnodes] at this
      exact this
  obtain ⟨i, hi⟩ := hpos ha
  obtain ⟨j, hj⟩ := hpos hc
  obtain ⟨l, hl⟩ := hpos hbs
  have hadjQ : ∀ {x y : X} (hx : x ∈ s) (hy : y ∈ s) {p q : Fin 4},
      u p = blockNode (quartetUnrooted N hN s hs) C' ⟨x, hx⟩ →
      u q = blockNode (quartetUnrooted N hN s hs) C' ⟨y, hy⟩ →
      (AdjacentBlocks (quartetUnrooted N hN s hs) C' ⟨x, hx⟩ ⟨y, hy⟩ ↔
        q = finRotate 4 p ∨ p = finRotate 4 q) := by
    intro x y hx hy p q hp hq
    exact adjacentBlocks_iff_finRotate hQb h1Q hC' hcyc hrange
      (by rw [hp]; exact (blockNode_spec hC' _).2) (by rw [hq]; exact (blockNode_spec hC' _).2)
  have hij : i ≠ j := fun h => hβQ ha hc hac (hi.symm.trans (h ▸ hj))
  have hil : i ≠ l := fun h => hβQ ha hbs hba.symm (hi.symm.trans (h ▸ hl))
  have hjl : j ≠ l := fun h => hβQ hc hbs hbc.symm (hj.symm.trans (h ▸ hl))
  -- in a 4-cycle, the nodes not adjacent to each other are both adjacent to the other nodes
  have h4 : ∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l → ¬ (j = finRotate 4 i ∨ i = finRotate 4 j) →
      (l = finRotate 4 i ∨ i = finRotate 4 l) ∧ (j = finRotate 4 l ∨ l = finRotate 4 j) := by
    intro i j l
    have := i.isLt
    have := j.isLt
    have := l.isLt
    simp only [finRotate_apply, ne_eq, Fin.ext_iff, Fin.val_add, Fin.val_one]
    omega
  obtain ⟨hab, hbc'⟩ := h4 i j l hij hil hjl fun h => hadj ((hadjQ ha hc hi hj).2 h)
  have J₁ := fwd ha hbs ((hadjQ ha hbs hi hl).2 hab)
  have J₂ := fwd hbs hc ((hadjQ hbs hc hl hj).2 hbc')
  rw [joinedAvoiding_iff_reflTransGen hN h1 hC] at J₁ J₂ hJ
  have hmem : ∀ {t x y : X}, t ∈ s → t ≠ x → t ≠ y →
      blockNode (unrooted N hN hX) C t ∈ blockNodes (unrooted N hN hX) C ↑((s.erase x).erase y) :=
    fun ht htx hty => (mem_blockNodes_iff_blockNode hN h1 hC).2 ⟨_, hTs.2 ⟨ht, htx, hty⟩, rfl⟩
  exact hC.not_joined_three (blockNode_mem hC a) (blockNode_mem hC b) (blockNode_mem hC c)
    (blockNode_mem hC d) (hβN ha hbs hba.symm) (hβN ha hc hac) (hβN ha hds hda.symm)
    (hβN hbs hc hbc) (hβN hbs hds hbd) (hβN hc hds hdc.symm)
    ⟨hmem hc hac.symm hbc.symm, hmem hds hda hbd.symm⟩ ⟨hmem ha hba.symm hac, hmem hds hbd.symm hdc⟩
    ⟨hmem hbs hba hbc, hmem hds hda hdc⟩ J₁ J₂ hJ

/-- **A `3₂`-cycle of `Q⁻_s` comes from a cycle of `N⁻`**, with the same hybrid node: the two taxa
`p`, `q` of `s` below the hybrid node are in the hybrid block of the cycle of `N⁻`, and the other two
taxa `r`, `t` of `s` are in two other blocks, distinct from each other. -/
theorem exists_cycle_of_hasThreeTwoCycle (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) (h32 : HasThreeTwoCycle N hN s hs) :
    ∃ C v, IsCycle (unrooted N hN hX).graph C ∧ IsHybridNodeOf (unrooted N hN hX) C v ∧
      ∃ p ∈ s, ∃ q ∈ s, ∃ r ∈ s, ∃ t ∈ s, p ≠ q ∧ DescendsFrom (unrooted N hN hX) v p ∧
        DescendsFrom (unrooted N hN hX) v q ∧
        ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C p r ∧
        ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C p t ∧
        ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C r t := by
  have := hN.1.finite_arcs
  have hQb := quartetLSA_isBinaryRootedNetwork hN hs
  have := hQb.1.finite_arcs
  have h1Q := isLevelOne_quartetLSA_graph hN.1 h1 hs
  have hXs : Nontrivial (s : Set X) := (Finset.one_lt_card_iff_nontrivial.mp (by omega)).coe_sort
  have hcardQ : Nat.card (s : Set X) = 4 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hs]
  obtain ⟨D, y, hD, hyD, hy2, hcard, hk⟩ := h32
  -- the cycle of `Q⁻_s` of `D`, with three nodes
  obtain ⟨C', w, hC', hw, hwy, hC'D⟩ := exists_unrooted_of_isCycle (hX := hXs) hQb h1Q
    (lsa_univ_quartetLSA hN hs) hD hyD hy2
  have h3 : (cycleNodes (quartetUnrooted N hN s hs).graph C').ncard = 3 := by
    rw [ncard_cycleNodes_unrooted hQb (lsa_univ_quartetLSA hN hs) hC', hC'D]
    exact hcard
  -- the cycle of `N⁻` with the same hybrid node
  have hyr : y ≠ (quartetLSA N hN.1 s hs).root := fun h => by
    rw [h, hQb.1.root_indegree] at hy2
    exact absurd hy2 (by norm_num)
  obtain ⟨-, v, hvy⟩ := exists_unrooted_node_of_quartet hN hX hs hyr
  obtain ⟨C, hC, hv⟩ := exists_isHybridNodeOf_of_indegree_eq_two hN h1 v
    (by rw [hvy]; exact indegree_eq_two_of_quartetLSA hN hs hy2)
  have hwv : quartetNode hN hs w = v.1.1 := by
    rw [hvy]
    exact congrArg (fun z => z.1.1) hwy
  -- the blocks of `C'`: two taxa in the hybrid block, the other two in the other two blocks
  have hrange : (Set.range (blockNode (quartetUnrooted N hN s hs) C')).ncard = 3 := by
    rw [← cycleNodes_eq_range_blockNode hQb h1Q hC']
    exact h3
  set A := {x' | (quartetLSA N hN.1 s hs).graph.Reaches y ((quartetLSA N hN.1 s hs).leaf x')}
    with hA_def
  have hβw : ∀ x', blockNode (quartetUnrooted N hN s hs) C' x' = w ↔ x' ∈ A := fun x' => by
    rw [blockNode_eq_iff_descendsFrom h1Q hC' hw, descendsFrom_iff_reaches hQb h1Q hC' hw, hwy]
    exact Iff.rfl
  obtain ⟨p', q', hpq, hA⟩ := Set.ncard_eq_two.1 hk
  have hAc : Aᶜ.ncard = 2 := by
    rw [Set.ncard_compl, hcardQ, hk]
  obtain ⟨r', t', hrt, hAc'⟩ := Set.ncard_eq_two.1 hAc
  have hp : blockNode (quartetUnrooted N hN s hs) C' p' = w :=
    (hβw p').2 (by rw [hA]; exact Or.inl rfl)
  have hq : blockNode (quartetUnrooted N hN s hs) C' q' = w :=
    (hβw q').2 (by rw [hA]; exact Or.inr rfl)
  have hrA : r' ∈ Aᶜ := by rw [hAc']; exact Or.inl rfl
  have htA : t' ∈ Aᶜ := by rw [hAc']; exact Or.inr rfl
  have hr : blockNode (quartetUnrooted N hN s hs) C' r' ≠ w := fun h => hrA ((hβw r').1 h)
  have ht : blockNode (quartetUnrooted N hN s hs) C' t' ≠ w := fun h => htA ((hβw t').1 h)
  have hrt' : blockNode (quartetUnrooted N hN s hs) C' r' ≠
      blockNode (quartetUnrooted N hN s hs) C' t' := by
    intro h
    have hsub : Set.range (blockNode (quartetUnrooted N hN s hs) C') ⊆
        {w, blockNode (quartetUnrooted N hN s hs) C' r'} := by
      rintro _ ⟨x', rfl⟩
      by_cases hx' : x' ∈ A
      · exact Or.inl ((hβw x').2 hx')
      · have : x' ∈ ({r', t'} : Set _) := by rw [← hAc']; exact hx'
        rcases this with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inr h.symm
    have h₁ := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h₂ := Set.ncard_insert_le w {blockNode (quartetUnrooted N hN s hs) C' r'}
    rw [Set.ncard_singleton] at h₂
    omega
  -- the blocks of `N⁻`
  have hK := fun {x y : X} (hx : x ∈ s) (hy : y ∈ s) =>
    blockNode_eq_iff_quartet hN h1 hX hs hC' hw hC hv hwv hx hy
  have hKv := fun {x : X} (hx : x ∈ s) =>
    blockNode_eq_hybrid_iff_quartet hN h1 hX hs hC' hw hC hv hwv hx
  refine ⟨C, v, hC, hv, p'.1, p'.2, q'.1, q'.2, r'.1, r'.2, t'.1, t'.2,
    fun h => hpq (Subtype.ext h), (blockNode_eq_iff_descendsFrom h1 hC hv _).1 ((hKv p'.2).2 hp),
    (blockNode_eq_iff_descendsFrom h1 hC hv _).1 ((hKv q'.2).2 hq), ?_, ?_, ?_⟩
  · rw [sameBlock_iff_blockNode_eq h1 hC, hK p'.2 r'.2]
    exact fun h => hr (h.symm.trans hp)
  · rw [sameBlock_iff_blockNode_eq h1 hC, hK p'.2 t'.2]
    exact fun h => ht (h.symm.trans hp)
  · rw [sameBlock_iff_blockNode_eq h1 hC, hK r'.2 t'.2]
    exact hrt'

end Targets

end Banos2019
