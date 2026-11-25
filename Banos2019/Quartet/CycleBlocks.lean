module

public import Banos2019.Quartet.Contract
public import Banos2019.Basic.Data.Set.Card

/-!
# The blocks of a cycle of a rooted network (Baños 2019, Section 5, Lemmas 5 and 6)

Removing the edges of a cycle `C` of a binary level-1 rooted network leaves, through each node `u`
of `C`, the taxa joined to `u` by a walk avoiding `C`: the block `nodeBlock N.graph N.leaf C u` of
`u`. On `N⁻`, whose nodes are those of `N` but the root, these are the `v`-blocks of Section 5.

* `disjoint_nodeBlock_of_ne`, `exists_mem_nodeBlock`: the blocks of distinct nodes are disjoint, and
  every taxon is in a block.
* `nodeBlock_hybrid`: the block of the hybrid node `v` is the set of taxa below `v`.
* `nodeBlock_nonempty`: in an LSA network, the block of every node of `C` but the root holds a taxon;
  `nodeBlock_root`: the root, when on `C`, has an empty block.
* `add_le_of_inducesCycleType`: a cycle with `n` nodes other than the root and `k` taxa below its
  hybrid node has `k + n ≤ |X| + 1`, `1 ≤ k` and `2 ≤ n`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Graph

variable {G : DirectedMultigraph V E}

/-- **Two nodes of a cycle are joined by a walk along its edges.** -/
theorem IsCycle.walks_of_mem {C : Set E} (hC : IsCycle G C) {a b : V} (ha : a ∈ cycleNodes G C)
    (hb : b ∈ cycleNodes G C) : G.Walks C a b := by
  obtain ⟨k, v, e, hC', rfl⟩ := hC
  rw [hC'.cycleNodes_eq] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hC'.pos; omega⟩
  have hP := hC'.isPathOf
  have hsub : ∀ i j : Fin (n + 1),
      {f | ∃ l : Fin n, (i : ℕ) ≤ l ∧ (l : ℕ) < j ∧ e l.castSucc = f} ⊆ Set.range e := by
    rintro i j f ⟨l, -, -, rfl⟩
    exact ⟨_, rfl⟩
  rcases le_total i j with h | h
  · exact walks_mono (hsub i j) (hP.walks_of_le h)
  · exact G.walks_symm (walks_mono (hsub j i) (hP.walks_of_le h))

/-- A cycle has a node. -/
theorem IsCycle.nonempty_cycleNodes {C : Set E} (hC : IsCycle G C) : (cycleNodes G C).Nonempty := by
  obtain ⟨k, v, e, hC', rfl⟩ := hC
  exact ⟨G.source (e ⟨0, hC'.pos⟩), e ⟨0, hC'.pos⟩, ⟨_, rfl⟩, Or.inl rfl⟩

/-- **In a connected graph, every node is joined to a node of a cycle `C` by a walk avoiding the
edges of `C`**: along a walk to a node of `C`, stop at the first node of `C`. -/
theorem exists_walks_compl_cycleNodes (hG : G.IsConnected) {C : Set E} (hC : IsCycle G C) (a : V) :
    ∃ u ∈ cycleNodes G C, G.Walks Cᶜ u a := by
  obtain ⟨u₀, hu₀⟩ := hC.nonempty_cycleNodes
  rcases walks_inter_compl_or_exists_cycleNodes (C := C) (hG a u₀) with h | ⟨c, hc, h⟩
  · rw [Set.univ_inter] at h
    exact ⟨u₀, hu₀, G.walks_symm h⟩
  · rw [Set.univ_inter] at h
    exact ⟨c, hc, G.walks_symm h⟩

end Graph

section Blocks

variable {N : RootedNetwork V E X} {C : Set E}

/-- **The blocks of two distinct nodes of a cycle are disjoint** (level-1: two nodes of `C` joined by
a walk avoiding `C` are equal). -/
theorem disjoint_nodeBlock_of_ne (h1 : IsLevelOne N.graph) (hC : IsCycle N.graph C) {u w : V}
    (hu : u ∈ cycleNodes N.graph C) (hw : w ∈ cycleNodes N.graph C) (hne : u ≠ w) :
    Disjoint (nodeBlock N.graph N.leaf C u) (nodeBlock N.graph N.leaf C w) :=
  Set.disjoint_left.2 fun _ hxu hxw =>
    hne (h1.eq_of_walks_compl hC hu hw (Relation.ReflTransGen.trans hxu (N.graph.walks_symm hxw)))

/-- **Every taxon is in a block** of every cycle of a phylogenetic network. -/
theorem exists_mem_nodeBlock (hN : N.IsPhylogenetic) (hC : IsCycle N.graph C) (x : X) :
    ∃ u ∈ cycleNodes N.graph C, x ∈ nodeBlock N.graph N.leaf C u :=
  exists_walks_compl_cycleNodes (N.graph_connected hN) hC (N.leaf x)

variable (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hC : IsCycle N.graph C) {v : V}
  (hv : v ∈ cycleNodes N.graph C) (h2 : N.graph.indegree v = 2)
include hN h1 hC hv h2

/-- A walk avoiding `C` from its hybrid node `v` stays below `v`: an arc into a vertex below `v` is
an edge of `C` (into `v`) or leaves a vertex below `v` (`reaches_source_of_below_hybrid`). -/
theorem reaches_of_walks_compl_hybrid {w : V} (h : N.graph.Walks Cᶜ v w) : N.graph.Reaches v w := by
  have := hN.1.finite_arcs
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨f, hfC, hf | hf⟩ := hab
    · exact hf.2 ▸ ih.tail ⟨f, hf.1, rfl⟩
    · rw [← hf.1]
      by_cases hav : a = v
      · exact absurd ((lemma3 hN h1 hC).2.1 v hv h2 f (hf.2.trans hav)) hfC
      · exact reaches_source_of_below_hybrid hN h1 h2 (hf.2 ▸ ih) (hf.2 ▸ hav)

/-- **The block of the hybrid node is the set of taxa below it.** -/
theorem nodeBlock_hybrid :
    nodeBlock N.graph N.leaf C v = {x | N.graph.Reaches v (N.leaf x)} := by
  ext x
  refine ⟨reaches_of_walks_compl_hybrid hN h1 hC hv h2, fun hx => ?_⟩
  refine walks_of_reaches_of_forall hx fun f hf _ hfC => ?_
  have hs : N.graph.source f = v :=
    eq_of_reaches_of_reaches hN.1.acyclic (reaches_hybrid hN h1 hC hv h2 _ (source_mem_cycleNodes hfC))
      hf
  exact notMem_of_source_eq_hybrid hN h1 hC hv h2 hs hfC

omit hv h2 in
/-- An arc leaving a node `u` of `C` off `C` gives `u` a taxon in its block: a path from its target to
a taxon cannot meet `C`, for its first node on `C` would be joined to `u` avoiding `C`, hence be `u`,
and the network would have a cycle. -/
theorem nodeBlock_nonempty_of_exit {u : V} (hu : u ∈ cycleNodes N.graph C) {g : E}
    (hg : N.graph.source g = u) (hgC : g ∉ C) : (nodeBlock N.graph N.leaf C u).Nonempty := by
  obtain ⟨x, hx⟩ := exists_reaches_leaf hN.1 (N.graph.target g)
  have hstep : N.graph.Walks Cᶜ u (N.graph.target g) :=
    .single ⟨g, hgC, Or.inl ⟨hg, rfl⟩⟩
  rcases first_hit (C := C) hx with h | ⟨c, hc, h⟩
  · exact ⟨x, hstep.trans (walks_of_adjOff h)⟩
  · have hcu : u = c := h1.eq_of_walks_compl hC hu hc (hstep.trans (walks_of_adjOff h))
    rw [← hcu] at h
    exact absurd (Relation.TransGen.head' ⟨g, hg, rfl⟩ (reaches_of_adjOff h)) (hN.1.acyclic u)

/-- **A node of `C` other than its hybrid node and its top leaves an arc off `C`**: it has one parent,
along `C`, and two children, and only two of its arcs are edges of `C`. -/
theorem exists_exit_of_mem {t : V} (hK : IsContractible N C t) {u : V}
    (hu : u ∈ cycleNodes N.graph C) (huv : u ≠ v) (hut : u ≠ t) :
    ∃ g, N.graph.source g = u ∧ g ∉ C := by
  have := hN.1.finite_arcs
  have hloop := source_ne_target_of_binary hN
  have hur : u ≠ N.root := fun h => hut (h.trans (eq_of_reaches_of_reaches hN.1.acyclic
    (hN.1.root_reaches t) (h ▸ hK.top_reaches u hu)))
  obtain ⟨p, hp⟩ := (N.graph.one_le_indegree_iff u).1 (hN.1.nonroot_indegree u hur)
  have hpC : p ∈ C := by
    by_contra hpC
    exact hut ((hp.symm.trans (hK.entry p hpC (hp ▸ hu))))
  have hout0 : N.graph.outdegree u ≠ 0 := fun h0 => by
    obtain ⟨x, hx⟩ := (hN.1.leaves u).1 h0
    exact hK.leaf_notMem x (hx ▸ hu)
  have h3 := hN.2.2 u hur hout0
  have hin1 : N.graph.indegree u = 1 :=
    le_antisymm (indegree_le_one_of_mem hN h1 hC hv h2 hu huv) (hN.1.nonroot_indegree u hur)
  obtain ⟨o₁, o₂, hne, hs⟩ := Set.ncard_eq_two.1 (show N.graph.outdegree u = 2 by omega)
  have ho₁ : N.graph.source o₁ = u := (Set.ext_iff.1 hs o₁).2 (Or.inl rfl)
  have ho₂ : N.graph.source o₂ = u := (Set.ext_iff.1 hs o₂).2 (Or.inr rfl)
  by_contra hno
  push Not at hno
  have hsub : ({p, o₁, o₂} : Set E) ⊆
      {e | e ∈ C ∧ (N.graph.source e = u ∨ N.graph.target e = u)} := by
    rintro f (rfl | rfl | rfl)
    · exact ⟨hpC, Or.inr hp⟩
    · exact ⟨hno _ ho₁, Or.inl ho₁⟩
    · exact ⟨hno _ ho₂, Or.inl ho₂⟩
  have hp₁ : p ≠ o₁ := fun h => hloop p (by rw [hp, h, ho₁])
  have hp₂ : p ≠ o₂ := fun h => hloop p (by rw [hp, h, ho₂])
  have hcard : ({p, o₁, o₂} : Set E).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hp₁, hp₂]) (Set.toFinite _), Set.ncard_pair hne]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hC.ncard_incident hloop hu, hcard] at this
  omega

omit hv h2 in
/-- **In an LSA network, the block of the top `t ≠ root` of `C` holds a taxon.** Below `t` the
vertices are entered only from below `t` (`reaches_source_of_below`: an edge of a cycle through `t`
entering `t` would put that cycle on `C`, against `IsContractible.top_entry`), so if every taxon were
below `t`, `t` would be a stable ancestor of the taxa, below the root. A taxon not below `t` is joined
to `t` by going up from `t` to the root and down to the taxon, avoiding `C`. -/
theorem nodeBlock_top_nonempty {t : V} (hK : IsContractible N C t) (htr : t ≠ N.root)
    (hlsa : N.IsLSANetwork) : (nodeBlock N.graph N.leaf C t).Nonempty := by
  have := hN.1.finite_arcs
  have hcyc : ∀ {a b}, N.graph.Reaches a b → N.graph.Adj b a → False := fun h hab =>
    hN.1.acyclic _ (Relation.TransGen.tail' h hab)
  obtain ⟨p, hp⟩ := (N.graph.one_le_indegree_iff t).1 (hN.1.nonroot_indegree t htr)
  have hpC : p ∉ C := hK.top_entry p hp
  -- below `t`, the vertices are entered only from below `t`
  have hcut : ∀ e, N.graph.Reaches t (N.graph.target e) → N.graph.target e ≠ t →
      N.graph.Reaches t (N.graph.source e) := fun e he hne =>
    reaches_source_of_below hN h1 (fun C' hC' htC' hin _ _ _ => by
      have hCC := (lemma3 hN h1 hC).2.2 C' hC' ⟨t, hK.top_mem, htC'⟩
      exact absurd (hCC ▸ hin p hp) hpC) he hne
  have htroot : ¬ N.graph.Reaches t N.root := fun h =>
    htr (eq_of_reaches_of_reaches hN.1.acyclic h (hN.1.root_reaches t))
  -- a taxon not below `t`
  obtain ⟨x, hx⟩ : ∃ x, ¬ N.graph.Reaches t (N.leaf x) := by
    by_contra hall
    push Not at hall
    have hst : N.IsStableAncestor Set.univ t := by
      rintro x - ⟨-, -, hpath⟩
      have key : ∀ b, Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ t ∧ b ≠ t) N.root b →
          ¬ N.graph.Reaches t b := by
        intro b hb
        induction hb with
        | refl => exact htroot
        | @tail a b _ hab ih =>
          intro htb
          obtain ⟨⟨f, hfs, hft⟩, -, hbt⟩ := hab
          exact ih (hfs ▸ hcut f (hft ▸ htb) (hft ▸ hbt))
      exact key _ hpath (hall x)
    exact htroot (hlsa.2 t hst)
  refine ⟨x, ?_⟩
  have hw₁ : N.graph.Walks Cᶜ N.root (N.graph.source p) :=
    walks_of_reaches_of_forall (hN.1.root_reaches _) fun f _ hf hfC =>
      hcyc ((hK.top_reaches _ (target_mem_cycleNodes hfC)).trans hf) ⟨p, rfl, hp⟩
  have hw₂ : N.graph.Walks Cᶜ N.root (N.leaf x) :=
    walks_of_reaches_of_forall (hN.1.root_reaches _) fun f _ hf hfC =>
      hx (((hK.top_reaches _ (source_mem_cycleNodes hfC)).tail ⟨f, rfl, rfl⟩).trans hf)
  exact (Relation.ReflTransGen.single ⟨p, hpC, Or.inr ⟨rfl, hp⟩⟩).trans
    ((N.graph.walks_symm hw₁).trans hw₂)

/-- **In an LSA network, the block of every node of a cycle but the root holds a taxon.** -/
theorem nodeBlock_nonempty (hlsa : N.IsLSANetwork) {u : V} (hu : u ∈ cycleNodes N.graph C)
    (hur : u ≠ N.root) : (nodeBlock N.graph N.leaf C u).Nonempty := by
  have := hN.1.finite_vertices
  have := hN.1.finite_arcs
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  obtain ⟨t, hK⟩ := isContractible_of_cycle hN h1 hC hv h2
  by_cases huv : u = v
  · rw [huv, nodeBlock_hybrid hN h1 hC hv h2]
    exact exists_reaches_leaf hN.1 v
  by_cases hut : u = t
  · rw [hut] at hur ⊢
    exact nodeBlock_top_nonempty hN h1 hC hK hur hlsa
  obtain ⟨g, hg, hgC⟩ := exists_exit_of_mem hN h1 hC hv h2 hK hu huv hut
  exact nodeBlock_nonempty_of_exit hN h1 hC hu hg hgC

omit h1 hv h2 in
/-- **A cycle through the root contains the arcs out of the root.** -/
theorem mem_of_source_eq_root (hr : N.root ∈ cycleNodes N.graph C) {f : E}
    (hf : N.graph.source f = N.root) : f ∈ C := by
  have := hN.1.finite_arcs
  have hnoin : ∀ e, N.graph.target e ≠ N.root := fun e =>
    (N.graph.indegree_eq_zero_iff _).1 hN.1.root_indegree e
  have hinc := hC.ncard_incident (source_ne_target_of_binary hN) hr
  have hsub : {e | e ∈ C ∧ (N.graph.source e = N.root ∨ N.graph.target e = N.root)} ⊆
      {e | N.graph.source e = N.root} := fun e he => he.2.resolve_right (hnoin e)
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    change N.graph.outdegree N.root ≤ _
    rw [hinc, hN.2.1]) (Set.toFinite _)
  have : f ∈ {e | e ∈ C ∧ (N.graph.source e = N.root ∨ N.graph.target e = N.root)} := heq ▸ hf
  exact this.1

omit h1 hv h2 in
/-- **The root, on a cycle, has an empty block**: its arcs are edges of the cycle. -/
theorem nodeBlock_root (hr : N.root ∈ cycleNodes N.graph C) :
    nodeBlock N.graph N.leaf C N.root = ∅ := by
  have := hN.1.finite_arcs
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  rcases Relation.ReflTransGen.cases_head hx with h | ⟨c, ⟨f, hfC, hf⟩, -⟩
  · exact N.leaf_ne_root hN.1 x h.symm
  · rcases hf with ⟨hs, -⟩ | ⟨-, ht⟩
    · exact hfC (mem_of_source_eq_root hN hC hr hs)
    · exact (N.graph.indegree_eq_zero_iff _).1 hN.1.root_indegree f ht

end Blocks

section Count

variable {N : RootedNetwork V E X}

/-- **In an LSA network, the two arcs out of the root have distinct targets**: a common target would
be a stable ancestor of the taxa below the root. -/
theorem target_ne_of_source_eq_root (hN : IsBinaryRootedNetwork N) (hlsa : N.IsLSANetwork)
    {f₁ f₂ : E} (hne : f₁ ≠ f₂) (hs₁ : N.graph.source f₁ = N.root)
    (hs₂ : N.graph.source f₂ = N.root) : N.graph.target f₁ ≠ N.graph.target f₂ := by
  have := hN.1.finite_arcs
  intro h
  obtain ⟨x₁, x₂, -, hs⟩ := Set.ncard_eq_two.1 hN.2.1
  have hall : ∀ g, N.graph.source g = N.root → N.graph.target g = N.graph.target f₁ := by
    have m : ∀ g, N.graph.source g = N.root → g = x₁ ∨ g = x₂ := fun g hg => by
      have : g ∈ {e | N.graph.source e = N.root} := hg
      rw [hs] at this
      simpa using this
    intro g hg
    rcases m g hg with rfl | rfl <;> rcases m f₁ hs₁ with h₁ | h₁ <;>
      rcases m f₂ hs₂ with h₂ | h₂ <;> subst_vars <;> simp_all
  have hst : N.IsStableAncestor Set.univ (N.graph.target f₁) := by
    rintro x - ⟨-, -, hpath⟩
    rcases Relation.ReflTransGen.cases_head hpath with h' | ⟨b, ⟨⟨g, hgs, hgt⟩, -, hb⟩, -⟩
    · exact N.leaf_ne_root hN.1 x h'.symm
    · exact hb (hgt ▸ hall g hgs)
  exact hN.1.target_ne_root f₁ (eq_of_reaches_of_reaches hN.1.acyclic (hlsa.2 _ hst)
    (hN.1.root_reaches _))

variable [Fintype V] [Fintype X]

/-- The nodes of a cycle other than the root, as a finset. -/
def cycleNodesOffRoot (N : RootedNetwork V E X) (C : Set E) : Finset V :=
  (univ.filter (· ∈ cycleNodes N.graph C)).erase N.root

omit [Fintype X] in
theorem mem_cycleNodesOffRoot {C : Set E} {u : V} :
    u ∈ cycleNodesOffRoot N C ↔ u ∈ cycleNodes N.graph C ∧ u ≠ N.root := by
  simp [cycleNodesOffRoot, and_comm]

omit [Fintype X] in
/-- A cycle of `N⊕` has as many nodes other than the root as the cycle it induces in `N⁻` has
edges. -/
theorem card_cycleNodesOffRoot {C : Set E} (hC : IsCycle N.graph C) :
    #(cycleNodesOffRoot N C) = C.ncard - (if N.root ∈ cycleNodes N.graph C then 1 else 0) := by
  have hT : #(univ.filter (· ∈ cycleNodes N.graph C)) = C.ncard := by
    rw [← ncard_cycleNodes hC, ← Set.ncard_coe_finset]
    congr 1
    ext u
    simp
  unfold cycleNodesOffRoot
  split_ifs with hr
  · rw [card_erase_of_mem (by simpa using hr), hT]
  · rw [erase_eq_of_notMem (by simpa using hr), hT, Nat.sub_zero]

/-- **The blocks of the nodes of a cycle other than the root are pairwise disjoint and nonempty**:
there are at most as many as taxa, and the block of the hybrid node `v` holds the `k` taxa below
`v`. -/
theorem sum_ncard_nodeBlock_le (h1 : IsLevelOne N.graph) {C : Set E} (hC : IsCycle N.graph C) :
    ∑ u ∈ cycleNodesOffRoot N C, (nodeBlock N.graph N.leaf C u).ncard ≤ Fintype.card X := by
  rw [← Nat.card_eq_fintype_card]
  refine sum_ncard_le_of_pairwiseDisjoint _ fun u hu w hw hne => ?_
  exact disjoint_nodeBlock_of_ne h1 hC (mem_cycleNodesOffRoot.1 hu).1
    (mem_cycleNodesOffRoot.1 hw).1 hne

/-- **The size of a cycle and the number of taxa below its hybrid node** (the argument of Lemma 5):
a cycle of an LSA network inducing an `n_k`-cycle has `n` nodes other than the root, whose blocks are
pairwise disjoint and nonempty, and the block of the hybrid node has `k` taxa; so
`k + (n - 1) ≤ |X|`. Moreover `1 ≤ k`, and `2 ≤ n`: the two arcs out of the root have distinct
targets. -/
theorem add_le_of_inducesCycleType (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hlsa : N.IsLSANetwork) {C : Set E} {v : V} {n k : ℕ} (hC : InducesCycleType N C v n k) :
    k + n ≤ Fintype.card X + 1 ∧ 1 ≤ k ∧ 2 ≤ n := by
  obtain ⟨hcyc, hv, h2, hn, hk⟩ := hC
  have := hN.1.finite_arcs
  have hvr : v ≠ N.root := fun h => by
    have := hN.1.root_indegree
    rw [← h, h2] at this
    exact absurd this (by norm_num)
  have hS : #(cycleNodesOffRoot N C) = n := (card_cycleNodesOffRoot hcyc).trans hn
  have hvS : v ∈ cycleNodesOffRoot N C := mem_cycleNodesOffRoot.2 ⟨hv, hvr⟩
  have hsum := sum_ncard_nodeBlock_le h1 hcyc
  rw [← add_sum_erase _ _ hvS, nodeBlock_hybrid hN h1 hcyc hv h2, hk] at hsum
  have hpos : ∀ u ∈ (cycleNodesOffRoot N C).erase v, 1 ≤ (nodeBlock N.graph N.leaf C u).ncard :=
    fun u hu => by
      have hu' := mem_cycleNodesOffRoot.1 (mem_of_mem_erase hu)
      exact (Set.ncard_pos (Set.toFinite _)).2 (nodeBlock_nonempty hN h1 hcyc hv h2 hlsa hu'.1 hu'.2)
  have hrest := card_nsmul_le_sum _ _ 1 hpos
  rw [smul_eq_mul, mul_one, card_erase_of_mem hvS, hS] at hrest
  have hk1 : 1 ≤ k := by
    rw [← hk, ← nodeBlock_hybrid hN h1 hcyc hv h2]
    exact (Set.ncard_pos (Set.toFinite _)).2 (nodeBlock_nonempty hN h1 hcyc hv h2 hlsa hv hvr)
  -- the two hybrid edges of `v` are edges of `C`
  obtain ⟨h₁, h₂, hne, hs⟩ := Set.ncard_eq_two.1 h2
  have hh₁ : N.graph.target h₁ = v := (Set.ext_iff.1 hs h₁).2 (Or.inl rfl)
  have hh₂ : N.graph.target h₂ = v := (Set.ext_iff.1 hs h₂).2 (Or.inr rfl)
  have hsub : ({h₁, h₂} : Set E) ⊆ C := by
    rintro f (rfl | rfl)
    · exact (lemma3 hN h1 hcyc).2.1 v hv h2 _ hh₁
    · exact (lemma3 hN h1 hcyc).2.1 v hv h2 _ (Set.mem_singleton_iff.1 ‹_› ▸ hh₂)
  have hC2 : 2 ≤ C.ncard := by
    rw [← Set.ncard_pair hne]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hn2 : 2 ≤ n := by
    rw [← hn]
    split_ifs with hr
    · -- through the root, `C` has a third edge: otherwise both arcs out of the root enter `v`
      by_contra hlt
      have hC2' : C.ncard ≤ 2 := by omega
      have hCeq : ({h₁, h₂} : Set E) = C :=
        Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_pair hne]; exact hC2') (Set.toFinite _)
      obtain ⟨f₁, f₂, hf, hfs⟩ := Set.ncard_eq_two.1 hN.2.1
      have hf₁ : N.graph.source f₁ = N.root := (Set.ext_iff.1 hfs f₁).2 (Or.inl rfl)
      have hf₂ : N.graph.source f₂ = N.root := (Set.ext_iff.1 hfs f₂).2 (Or.inr rfl)
      have htv : ∀ f, N.graph.source f = N.root → N.graph.target f = v := fun f hf => by
        have hfC := mem_of_source_eq_root hN hcyc hr hf
        rw [← hCeq] at hfC
        rcases hfC with rfl | hfC
        · exact hh₁
        · rw [Set.mem_singleton_iff.1 hfC]; exact hh₂
      exact target_ne_of_source_eq_root hN hlsa hf hf₁ hf₂ ((htv f₁ hf₁).trans (htv f₂ hf₂).symm)
    · omega
  refine ⟨by omega, hk1, hn2⟩

end Count

section Several

variable {N : RootedNetwork V E X} [Fintype V] [Fintype X]

omit [Fintype V] [Fintype X] in
/-- Two distinct cycles of a level-1 network have no common edge. -/
theorem disjoint_of_isCycle_of_ne (h1 : IsLevelOne N.graph) {C₁ C₂ : Set E}
    (hC₁ : IsCycle N.graph C₁) (hC₂ : IsCycle N.graph C₂) (hne : C₁ ≠ C₂) : Disjoint C₁ C₂ :=
  Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 fun h => hne (h1 _ _ hC₁ hC₂ h))

omit [Fintype V] [Fintype X] in
/-- **The node of `C₁` toward another cycle `C₂`** is unique: two nodes of `C₁` joined avoiding `C₁`
to nodes of `C₂` are joined to each other through `C₂`. -/
theorem eq_of_walks_compl_of_cycles (h1 : IsLevelOne N.graph) {C₁ C₂ : Set E}
    (hC₁ : IsCycle N.graph C₁) (hC₂ : IsCycle N.graph C₂) (hne : C₁ ≠ C₂) {u u' c c' : V}
    (hu : u ∈ cycleNodes N.graph C₁) (hu' : u' ∈ cycleNodes N.graph C₁)
    (hc : c ∈ cycleNodes N.graph C₂) (hc' : c' ∈ cycleNodes N.graph C₂)
    (h : N.graph.Walks C₁ᶜ u c) (h' : N.graph.Walks C₁ᶜ u' c') : u = u' := by
  have hsub : C₂ ⊆ C₁ᶜ := fun f hf hf₁ =>
    Set.disjoint_left.1 (disjoint_of_isCycle_of_ne h1 hC₁ hC₂ hne) hf₁ hf
  exact h1.eq_of_walks_compl hC₁ hu hu'
    ((h.trans (walks_mono hsub (hC₂.walks_of_mem hc hc'))).trans (N.graph.walks_symm h'))

omit [Fintype V] [Fintype X] in
/-- A cycle `C₁` has a node toward every other cycle `C₂`. -/
theorem exists_walks_compl_of_cycles (hN : N.IsPhylogenetic) {C₁ C₂ : Set E}
    (hC₁ : IsCycle N.graph C₁) (hC₂ : IsCycle N.graph C₂) :
    ∃ u ∈ cycleNodes N.graph C₁, ∃ c ∈ cycleNodes N.graph C₂, N.graph.Walks C₁ᶜ u c := by
  obtain ⟨c, hc⟩ := hC₂.nonempty_cycleNodes
  obtain ⟨u, hu, h⟩ := exists_walks_compl_cycleNodes (N.graph_connected hN) hC₁ c
  exact ⟨u, hu, c, hc, h⟩

omit [Fintype V] [Fintype X] in
/-- **The blocks of two cycles away from each other are disjoint** (proof of Lemma 5): the block of
a node `a` of `C₁` not toward `C₂` and that of a node `b` of `C₂` not toward `C₁`. A walk from `b`
to a taxon avoiding `C₂` either avoids `C₁`, and then `a` is joined to the node of `C₁` toward `C₂`
avoiding `C₁`, or meets `C₁`, and then `b` is joined to the node of `C₂` toward `C₁` avoiding
`C₂`. -/
theorem disjoint_nodeBlock_of_cycles (h1 : IsLevelOne N.graph) {C₁ C₂ : Set E}
    (hC₁ : IsCycle N.graph C₁) (hC₂ : IsCycle N.graph C₂) (hne : C₁ ≠ C₂) {u₁ a c₂ : V}
    (hu₁ : u₁ ∈ cycleNodes N.graph C₁) (ha : a ∈ cycleNodes N.graph C₁)
    (hc₂ : c₂ ∈ cycleNodes N.graph C₂) (hw₁ : N.graph.Walks C₁ᶜ u₁ c₂) (hau : a ≠ u₁)
    {u₂ b c₁ : V} (hu₂ : u₂ ∈ cycleNodes N.graph C₂) (hb : b ∈ cycleNodes N.graph C₂)
    (hc₁ : c₁ ∈ cycleNodes N.graph C₁) (hw₂ : N.graph.Walks C₂ᶜ u₂ c₁) (hbu : b ≠ u₂) :
    Disjoint (nodeBlock N.graph N.leaf C₁ a) (nodeBlock N.graph N.leaf C₂ b) := by
  have hd := disjoint_of_isCycle_of_ne h1 hC₁ hC₂ hne
  have hsub₂ : C₂ ⊆ C₁ᶜ := fun f hf hf₁ => Set.disjoint_left.1 hd hf₁ hf
  have hsub₁ : C₁ ⊆ C₂ᶜ := fun f hf hf₂ => Set.disjoint_left.1 hd hf hf₂
  refine Set.disjoint_left.2 fun x hxa hxb => ?_
  have hxa' : N.graph.Walks C₁ᶜ a (N.leaf x) := hxa
  have hxb' : N.graph.Walks C₂ᶜ b (N.leaf x) := hxb
  rcases walks_inter_compl_or_exists_cycleNodes (C := C₁) hxb' with h | ⟨c, hc, h⟩
  · refine hau (h1.eq_of_walks_compl hC₁ hu₁ ha ?_).symm
    exact ((hw₁.trans (walks_mono hsub₂ (hC₂.walks_of_mem hc₂ hb))).trans
      (walks_mono Set.inter_subset_right h)).trans (N.graph.walks_symm hxa')
  · refine hbu (h1.eq_of_walks_compl hC₂ hu₂ hb ?_).symm
    exact (hw₂.trans (walks_mono hsub₁ (hC₁.walks_of_mem hc₁ hc))).trans
      (N.graph.walks_symm (walks_mono Set.inter_subset_left h))

/-- **The blocks of a cycle partition the taxa**: they are pairwise disjoint, every taxon is in one,
and the root, when on the cycle, has none. -/
theorem sum_ncard_nodeBlock_eq (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) {C : Set E}
    (hC : IsCycle N.graph C) :
    ∑ u ∈ cycleNodesOffRoot N C, (nodeBlock N.graph N.leaf C u).ncard = Fintype.card X := by
  refine le_antisymm (sum_ncard_nodeBlock_le h1 hC) ?_
  have hdisj : ((cycleNodesOffRoot N C : Finset V) : Set V).PairwiseDisjoint
      (nodeBlock N.graph N.leaf C) := fun u hu w hw hne =>
    disjoint_nodeBlock_of_ne h1 hC (mem_cycleNodesOffRoot.1 hu).1 (mem_cycleNodesOffRoot.1 hw).1 hne
  rw [← finsum_mem_coe_finset, ← Set.Finite.ncard_biUnion (Finset.finite_toSet _)
    (fun _ _ => Set.toFinite _) hdisj, ← Nat.card_eq_fintype_card, ← Set.ncard_univ]
  refine Set.ncard_le_ncard (fun x _ => ?_) (Set.toFinite _)
  obtain ⟨u, hu, hx⟩ := exists_mem_nodeBlock hN.1 hC x
  have hur : u ≠ N.root := fun h => by
    rw [h, nodeBlock_root hN hC (h ▸ hu)] at hx
    exact hx
  exact Set.mem_biUnion (mem_coe.2 (mem_cycleNodesOffRoot.2 ⟨hu, hur⟩)) hx

/-- The block of a node of a cycle other than the root holds a taxon. -/
theorem one_le_ncard_nodeBlock (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hlsa : N.IsLSANetwork) {C : Set E} (hC : IsCycle N.graph C) {u : V}
    (hu : u ∈ cycleNodesOffRoot N C) : 1 ≤ (nodeBlock N.graph N.leaf C u).ncard := by
  have := hN.1.finite_arcs
  obtain ⟨⟨v, ⟨hv, h2⟩, -⟩, -, -⟩ := lemma3 hN h1 hC
  exact (Set.ncard_pos (Set.toFinite _)).2 (nodeBlock_nonempty hN h1 hC hv h2 hlsa
    (mem_cycleNodesOffRoot.1 hu).1 (mem_cycleNodesOffRoot.1 hu).2)

/-- **Several cycles** (proof of Lemma 5): for a family of distinct cycles `C i`, and for each `i` a
set `U i` of nodes of `C i` containing a node toward each other cycle, the blocks of the nodes of the
cycles other than the root and outside the sets `U i` are pairwise disjoint and nonempty, so there are
at most as many as taxa. -/
theorem sum_card_sdiff_le {ι : Type*} [Fintype ι] (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hlsa : N.IsLSANetwork) (C : ι → Set E)
    (hC : ∀ i, IsCycle N.graph (C i)) (hinj : Function.Injective C) (U : ι → Finset V)
    (hU : ∀ i j, i ≠ j → ∃ u ∈ U i, u ∈ cycleNodes N.graph (C i) ∧
      ∃ c ∈ cycleNodes N.graph (C j), N.graph.Walks (C i)ᶜ u c) :
    ∑ i, #(cycleNodesOffRoot N (C i) \ U i) ≤ Fintype.card X := by
  let I : Finset (Σ _ : ι, V) := univ.sigma fun i => cycleNodesOffRoot N (C i) \ U i
  let B : (Σ _ : ι, V) → Set X := fun p => nodeBlock N.graph N.leaf (C p.1) p.2
  have hdisj : (I : Set (Σ _ : ι, V)).PairwiseDisjoint B := by
    rintro ⟨i, a⟩ ha ⟨j, b⟩ hb hne
    simp only [I, mem_coe, mem_sigma, mem_univ, true_and, mem_sdiff, mem_cycleNodesOffRoot] at ha hb
    change Disjoint (nodeBlock N.graph N.leaf (C i) a) (nodeBlock N.graph N.leaf (C j) b)
    by_cases hij : i = j
    · subst hij
      exact disjoint_nodeBlock_of_ne h1 (hC i) ha.1.1 hb.1.1 fun h => hne (by rw [h])
    · obtain ⟨u, huU, hu, c, hc, hw⟩ := hU i j hij
      obtain ⟨u', hu'U, hu', c', hc', hw'⟩ := hU j i (Ne.symm hij)
      exact disjoint_nodeBlock_of_cycles h1 (hC i) (hC j) (fun h => hij (hinj h)) hu ha.1.1 hc hw
        (fun h => ha.2 (h ▸ huU)) hu' hb.1.1 hc' hw' fun h => hb.2 (h ▸ hu'U)
  have hsum := sum_ncard_le_of_pairwiseDisjoint I hdisj
  rw [Nat.card_eq_fintype_card] at hsum
  have hle : #I ≤ ∑ p ∈ I, (B p).ncard := by
    rw [card_eq_sum_ones]
    refine sum_le_sum fun p hp => ?_
    simp only [I, mem_sigma, mem_univ, true_and, mem_sdiff] at hp
    exact one_le_ncard_nodeBlock hN h1 hlsa (hC p.1) hp.1
  rw [card_sigma] at hle
  omega

omit [Fintype V] [Fintype X] in
/-- **Three cycles** (proof of Lemma 5): if the nodes of `C₁` toward `C₂` and toward `C₃` differ, `C₂`
and `C₃` lie on different sides of `C₁`, and the nodes of `C₂` toward `C₁` and toward `C₃` are the
same: a walk from `C₂` to `C₃` avoiding `C₂` meets `C₁`. -/
theorem eq_of_ne_of_cycles (h1 : IsLevelOne N.graph) {C₁ C₂ C₃ : Set E}
    (hC₁ : IsCycle N.graph C₁) (hC₂ : IsCycle N.graph C₂) (hC₃ : IsCycle N.graph C₃)
    (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃) {u₁₂ u₁₃ c₂ c₃ : V} (hu₁₂ : u₁₂ ∈ cycleNodes N.graph C₁)
    (hu₁₃ : u₁₃ ∈ cycleNodes N.graph C₁) (hc₂ : c₂ ∈ cycleNodes N.graph C₂)
    (hc₃ : c₃ ∈ cycleNodes N.graph C₃) (hw₁₂ : N.graph.Walks C₁ᶜ u₁₂ c₂)
    (hw₁₃ : N.graph.Walks C₁ᶜ u₁₃ c₃) (hne : u₁₂ ≠ u₁₃) {u₂₁ u₂₃ c₁ c₃' : V}
    (hu₂₁ : u₂₁ ∈ cycleNodes N.graph C₂) (hu₂₃ : u₂₃ ∈ cycleNodes N.graph C₂)
    (hc₁ : c₁ ∈ cycleNodes N.graph C₁) (hc₃' : c₃' ∈ cycleNodes N.graph C₃)
    (hw₂₁ : N.graph.Walks C₂ᶜ u₂₁ c₁) (hw₂₃ : N.graph.Walks C₂ᶜ u₂₃ c₃') : u₂₁ = u₂₃ := by
  have hsub₂ : C₂ ⊆ C₁ᶜ := fun f hf hf₁ =>
    Set.disjoint_left.1 (disjoint_of_isCycle_of_ne h1 hC₁ hC₂ h12) hf₁ hf
  rcases walks_inter_compl_or_exists_cycleNodes (C := C₁) hw₂₃ with h | ⟨c, hc, h⟩
  · refine absurd (eq_of_walks_compl_of_cycles h1 hC₁ hC₃ h13 hu₁₂ hu₁₃ hc₃' hc₃ ?_ hw₁₃) hne
    exact (hw₁₂.trans (walks_mono hsub₂ (hC₂.walks_of_mem hc₂ hu₂₃))).trans
      (walks_mono Set.inter_subset_right h)
  · exact eq_of_walks_compl_of_cycles h1 hC₂ hC₁ (Ne.symm h12) hu₂₁ hu₂₃ hc₁ hc
      hw₂₁ (walks_mono Set.inter_subset_left h)

/-- **Two distinct cycles of an LSA network** (proof of Lemma 5): each but its node toward the other
keeps its blocks, so `n₁ + n₂ - 2 ≤ |X|` for their numbers `n₁`, `n₂` of nodes other than the
root. -/
theorem card_add_card_le_of_cycles (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hlsa : N.IsLSANetwork) {C₁ C₂ : Set E} (hC₁ : IsCycle N.graph C₁) (hC₂ : IsCycle N.graph C₂)
    (hne : C₁ ≠ C₂) :
    #(cycleNodesOffRoot N C₁) + #(cycleNodesOffRoot N C₂) ≤ Fintype.card X + 2 := by
  obtain ⟨u₁, hu₁, c₂, hc₂, hw₁⟩ := exists_walks_compl_of_cycles hN.1 hC₁ hC₂
  obtain ⟨u₂, hu₂, c₁, hc₁, hw₂⟩ := exists_walks_compl_of_cycles hN.1 hC₂ hC₁
  have h := sum_card_sdiff_le (ι := Bool) hN h1 hlsa (fun b => if b then C₁ else C₂)
    (fun b => by cases b <;> assumption)
    (fun a b hab => by cases a <;> cases b <;> simp_all [eq_comm])
    (fun b : Bool => if b then {u₁} else {u₂}) (fun i j hij => by
      cases i <;> cases j
      · exact absurd rfl hij
      · exact ⟨u₂, by simp, hu₂, c₁, hc₁, hw₂⟩
      · exact ⟨u₁, by simp, hu₁, c₂, hc₂, hw₁⟩
      · exact absurd rfl hij)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at h
  have k₁ := le_card_sdiff {u₁} (cycleNodesOffRoot N C₁)
  have k₂ := le_card_sdiff {u₂} (cycleNodesOffRoot N C₂)
  rw [card_singleton] at k₁ k₂
  omega

/-- **Three distinct cycles of an LSA network** (proof of Lemma 5): `n₁ + n₂ + n₃ - 4 ≤ |X|`. At most
one of the three cycles has different nodes toward the two others (`eq_of_ne_of_cycles`), so at most
four nodes lose their blocks. -/
theorem card_add_card_add_card_le_of_cycles (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hlsa : N.IsLSANetwork) {C₁ C₂ C₃ : Set E}
    (hC₁ : IsCycle N.graph C₁) (hC₂ : IsCycle N.graph C₂) (hC₃ : IsCycle N.graph C₃)
    (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃) (h23 : C₂ ≠ C₃) :
    #(cycleNodesOffRoot N C₁) + #(cycleNodesOffRoot N C₂) + #(cycleNodesOffRoot N C₃) ≤
      Fintype.card X + 4 := by
  obtain ⟨u12, hu12, c12, hc12, hw12⟩ := exists_walks_compl_of_cycles hN.1 hC₁ hC₂
  obtain ⟨u13, hu13, c13, hc13, hw13⟩ := exists_walks_compl_of_cycles hN.1 hC₁ hC₃
  obtain ⟨u21, hu21, c21, hc21, hw21⟩ := exists_walks_compl_of_cycles hN.1 hC₂ hC₁
  obtain ⟨u23, hu23, c23, hc23, hw23⟩ := exists_walks_compl_of_cycles hN.1 hC₂ hC₃
  obtain ⟨u31, hu31, c31, hc31, hw31⟩ := exists_walks_compl_of_cycles hN.1 hC₃ hC₁
  obtain ⟨u32, hu32, c32, hc32, hw32⟩ := exists_walks_compl_of_cycles hN.1 hC₃ hC₂
  have t1 : u12 ≠ u13 → u21 = u23 ∧ u31 = u32 := fun hne =>
    ⟨eq_of_ne_of_cycles h1 hC₁ hC₂ hC₃ h12 h13 hu12 hu13 hc12 hc13 hw12 hw13 hne hu21 hu23 hc21
      hc23 hw21 hw23,
     eq_of_ne_of_cycles h1 hC₁ hC₃ hC₂ h13 h12 hu13 hu12 hc13 hc12 hw13 hw12 (Ne.symm hne) hu31
      hu32 hc31 hc32 hw31 hw32⟩
  have t2 : u21 ≠ u23 → u31 = u32 := fun hne =>
    (eq_of_ne_of_cycles h1 hC₂ hC₃ hC₁ h23 (Ne.symm h12) hu23 hu21 hc23 hc21 hw23 hw21
      (Ne.symm hne) hu32 hu31 hc32 hc31 hw32 hw31).symm
  let C : Fin 3 → Set E := ![C₁, C₂, C₃]
  let U : Fin 3 → Finset V := ![{u12, u13}, {u21, u23}, {u31, u32}]
  have hinj : Function.Injective C := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [C, eq_comm]
  have h := sum_card_sdiff_le hN h1 hlsa C (fun i => by fin_cases i <;> assumption) hinj U
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact ⟨u12, by simp [U], hu12, c12, hc12, hw12⟩
      · exact ⟨u13, by simp [U], hu13, c13, hc13, hw13⟩
      · exact ⟨u21, by simp [U], hu21, c21, hc21, hw21⟩
      · exact absurd rfl hij
      · exact ⟨u23, by simp [U], hu23, c23, hc23, hw23⟩
      · exact ⟨u31, by simp [U], hu31, c31, hc31, hw31⟩
      · exact ⟨u32, by simp [U], hu32, c32, hc32, hw32⟩
      · exact absurd rfl hij)
  rw [Fin.sum_univ_three] at h
  simp only [C, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h
  have k₁ := le_card_sdiff {u12, u13} (cycleNodesOffRoot N C₁)
  have k₂ := le_card_sdiff {u21, u23} (cycleNodesOffRoot N C₂)
  have k₃ := le_card_sdiff {u31, u32} (cycleNodesOffRoot N C₃)
  have p₁ := card_le_two (a := u12) (b := u13)
  have p₂ := card_le_two (a := u21) (b := u23)
  have p₃ := card_le_two (a := u31) (b := u32)
  have hone : ∀ a b : V, a = b → #({a, b} : Finset V) = 1 := by
    rintro a b rfl
    simp
  by_cases e1 : u12 = u13
  · rw [hone _ _ e1] at k₁
    by_cases e2 : u21 = u23
    · rw [hone _ _ e2] at k₂
      omega
    · rw [hone _ _ (t2 e2)] at k₃
      omega
  · obtain ⟨e2, e3⟩ := t1 e1
    rw [hone _ _ e2] at k₂
    rw [hone _ _ e3] at k₃
    omega

omit [Fintype V] [Fintype X] in
/-- **The blocks of the nodes of `C₂` away from `C₁` lie in the block of the node of `C₁` toward
`C₂`**: every taxon is in a block of `C₁`, and the others are disjoint from them. -/
theorem nodeBlock_subset_of_cycles (hN : N.IsPhylogenetic) (h1 : IsLevelOne N.graph)
    {C₁ C₂ : Set E} (hC₁ : IsCycle N.graph C₁) (hC₂ : IsCycle N.graph C₂) (hne : C₁ ≠ C₂)
    {u₁ c₂ : V} (hu₁ : u₁ ∈ cycleNodes N.graph C₁) (hc₂ : c₂ ∈ cycleNodes N.graph C₂)
    (hw₁ : N.graph.Walks C₁ᶜ u₁ c₂) {u₂ b c₁ : V} (hu₂ : u₂ ∈ cycleNodes N.graph C₂)
    (hb : b ∈ cycleNodes N.graph C₂) (hc₁ : c₁ ∈ cycleNodes N.graph C₁)
    (hw₂ : N.graph.Walks C₂ᶜ u₂ c₁) (hbu : b ≠ u₂) :
    nodeBlock N.graph N.leaf C₂ b ⊆ nodeBlock N.graph N.leaf C₁ u₁ := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := exists_mem_nodeBlock hN hC₁ x
  by_cases hau : a = u₁
  · rwa [hau] at hxa
  · exact absurd hx (Set.disjoint_left.1 (disjoint_nodeBlock_of_cycles h1 hC₁ hC₂ hne hu₁ ha hc₂
      hw₁ hau hu₂ hb hc₁ hw₂ hbu) hxa)

/-- For a cycle `C` inducing a `3₂`-cycle and another cycle `C'` with at least three nodes other than
the root, on four taxa, the node of `C` toward `C'` is the hybrid node of `C` (proof of Lemma 6): its
block holds the blocks of two nodes of `C'`, at least two taxa, and the blocks of the other nodes of
`C` hold one taxon each. -/
theorem eq_hybrid_of_walks_compl_of_three_two (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hlsa : N.IsLSANetwork) (hX : Fintype.card X = 4) {C : Set E}
    {v : V} (hC : InducesCycleType N C v 3 2) {C' : Set E} (hC' : IsCycle N.graph C')
    (hn' : 3 ≤ #(cycleNodesOffRoot N C')) (hne : C ≠ C') {u c' : V}
    (hu : u ∈ cycleNodes N.graph C) (hc' : c' ∈ cycleNodes N.graph C')
    (hw : N.graph.Walks Cᶜ u c') : u = v := by
  obtain ⟨hcyc, hv, h2, hn, hk⟩ := hC
  obtain ⟨u', hu', c, hc, hw'⟩ := exists_walks_compl_of_cycles hN.1 hC' hcyc
  -- the block of `u` has at least two taxa
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁₂⟩ := one_lt_card.1 (show 1 < #((cycleNodesOffRoot N C').erase u') by
    have := pred_card_le_card_erase (s := cycleNodesOffRoot N C') (a := u')
    omega)
  have hb₁' := mem_cycleNodesOffRoot.1 (mem_of_mem_erase hb₁)
  have hb₂' := mem_cycleNodesOffRoot.1 (mem_of_mem_erase hb₂)
  have hsub : nodeBlock N.graph N.leaf C' b₁ ∪ nodeBlock N.graph N.leaf C' b₂ ⊆
      nodeBlock N.graph N.leaf C u :=
    Set.union_subset
      (nodeBlock_subset_of_cycles hN.1 h1 hcyc hC' hne hu hc' hw hu' hb₁'.1 hc hw' (ne_of_mem_erase hb₁))
      (nodeBlock_subset_of_cycles hN.1 h1 hcyc hC' hne hu hc' hw hu' hb₂'.1 hc hw' (ne_of_mem_erase hb₂))
  have hu2 : 2 ≤ (nodeBlock N.graph N.leaf C u).ncard := by
    refine le_trans ?_ (Set.ncard_le_ncard hsub (Set.toFinite _))
    rw [Set.ncard_union_eq (disjoint_nodeBlock_of_ne h1 hC' hb₁'.1 hb₂'.1 hb₁₂) (Set.toFinite _)
      (Set.toFinite _)]
    have := one_le_ncard_nodeBlock hN h1 hlsa hC' (mem_of_mem_erase hb₁)
    have := one_le_ncard_nodeBlock hN h1 hlsa hC' (mem_of_mem_erase hb₂)
    omega
  -- `u` is not the root, whose block is empty
  have hur : u ≠ N.root := fun h => by
    rw [h, nodeBlock_root hN hcyc (h ▸ hu), Set.ncard_empty] at hu2
    omega
  have huS : u ∈ cycleNodesOffRoot N C := mem_cycleNodesOffRoot.2 ⟨hu, hur⟩
  have hvr : v ≠ N.root := fun h => by
    have := hN.1.root_indegree
    rw [← h, h2] at this
    exact absurd this (by norm_num)
  have hvS : v ∈ cycleNodesOffRoot N C := mem_cycleNodesOffRoot.2 ⟨hv, hvr⟩
  by_contra huv
  have hsum := sum_ncard_nodeBlock_eq hN h1 hcyc
  have hS : #(cycleNodesOffRoot N C) = 3 := (card_cycleNodesOffRoot hcyc).trans hn
  have huS' : u ∈ (cycleNodesOffRoot N C).erase v := mem_erase.2 ⟨huv, huS⟩
  rw [← add_sum_erase _ _ hvS, ← add_sum_erase _ _ huS', nodeBlock_hybrid hN h1 hcyc hv h2, hk,
    hX] at hsum
  have hrest := card_nsmul_le_sum (((cycleNodesOffRoot N C).erase v).erase u) _ 1 fun w hw =>
    one_le_ncard_nodeBlock hN h1 hlsa hcyc (mem_of_mem_erase (mem_of_mem_erase hw))
  rw [smul_eq_mul, mul_one, card_erase_of_mem huS', card_erase_of_mem hvS, hS] at hrest
  omega

/-- **Two cycles inducing `3₂`-cycles are the same** (Lemma 6, on four taxa): the node of each toward
the other is its hybrid node (`eq_hybrid_of_walks_compl_of_three_two`), and then each hybrid node is
below the other. -/
theorem eq_of_inducesCycleType_three_two_of_card (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hlsa : N.IsLSANetwork) (hX : Fintype.card X = 4) {C C' : Set E}
    {v v' : V} (hC : InducesCycleType N C v 3 2) (hC' : InducesCycleType N C' v' 3 2) : C = C' := by
  have := hN.1.finite_arcs
  by_contra hne
  obtain ⟨u, hu, c', hc', hw⟩ := exists_walks_compl_of_cycles hN.1 hC.1 hC'.1
  obtain ⟨u', hu', c, hc, hw'⟩ := exists_walks_compl_of_cycles hN.1 hC'.1 hC.1
  have huv := eq_hybrid_of_walks_compl_of_three_two hN h1 hlsa hX hC hC'.1
    (by rw [card_cycleNodesOffRoot hC'.1, hC'.2.2.2.1]) hne hu hc' hw
  have hu'v' := eq_hybrid_of_walks_compl_of_three_two hN h1 hlsa hX hC' hC.1
    (by rw [card_cycleNodesOffRoot hC.1, hC.2.2.2.1]) (Ne.symm hne) hu' hc hw'
  subst huv hu'v'
  have r₁ := (reaches_of_walks_compl_hybrid hN h1 hC.1 hC.2.1 hC.2.2.1 hw).trans
    (reaches_hybrid hN h1 hC'.1 hC'.2.1 hC'.2.2.1 c' hc')
  have r₂ := (reaches_of_walks_compl_hybrid hN h1 hC'.1 hC'.2.1 hC'.2.2.1 hw').trans
    (reaches_hybrid hN h1 hC.1 hC.2.1 hC.2.2.1 c hc)
  have heq := eq_of_reaches_of_reaches hN.1.acyclic r₁ r₂
  exact hne ((lemma3 hN h1 hC.1).2.2 C' hC'.1 ⟨u, hC.2.1, heq ▸ hC'.2.1⟩)

/-- **No `2₂`-cycle with a `4`-cycle** (Lemma 6, on four taxa): the four nodes of the `4`-cycle have a
taxon each in their blocks, so the block of its node toward the `2₂`-cycle has at most one, and it
holds the block of a node of the `2₂`-cycle, of two taxa. -/
theorem not_inducesCycleType_two_two_of_four (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hlsa : N.IsLSANetwork) (hX : Fintype.card X = 4) {C C' : Set E}
    {v v' : V} {k' : ℕ} (hC : InducesCycleType N C v 2 2) (hC' : InducesCycleType N C' v' 4 k') :
    False := by
  have hne : C ≠ C' := by
    rintro rfl
    have := hC.2.2.2.1
    have := hC'.2.2.2.1
    omega
  obtain ⟨hcyc, hv, h2, hn, hk⟩ := hC
  obtain ⟨u, hu, c', hc', hw⟩ := exists_walks_compl_of_cycles hN.1 hcyc hC'.1
  obtain ⟨u', hu', c, hc, hw'⟩ := exists_walks_compl_of_cycles hN.1 hC'.1 hcyc
  -- the block of `u'` has at most one taxon
  have hsum' := sum_ncard_nodeBlock_eq hN h1 hC'.1
  have hS' : #(cycleNodesOffRoot N C') = 4 := (card_cycleNodesOffRoot hC'.1).trans hC'.2.2.2.1
  have hu'1 : (nodeBlock N.graph N.leaf C' u').ncard ≤ 1 := by
    by_cases hu'S : u' ∈ cycleNodesOffRoot N C'
    · rw [← add_sum_erase _ _ hu'S, hX] at hsum'
      have hrest := card_nsmul_le_sum ((cycleNodesOffRoot N C').erase u') _ 1 fun w hw =>
        one_le_ncard_nodeBlock hN h1 hlsa hC'.1 (mem_of_mem_erase hw)
      rw [smul_eq_mul, mul_one, card_erase_of_mem hu'S, hS'] at hrest
      omega
    · have hr : u' = N.root := by
        by_contra h
        exact hu'S (mem_cycleNodesOffRoot.2 ⟨hu', h⟩)
      rw [hr, nodeBlock_root hN hC'.1 (hr ▸ hu'), Set.ncard_empty]
      omega
  -- a node `b` of `C` other than its node toward `C'`
  have hS : #(cycleNodesOffRoot N C) = 2 := (card_cycleNodesOffRoot hcyc).trans hn
  obtain ⟨b, hb⟩ : ((cycleNodesOffRoot N C).erase u).Nonempty := by
    rw [← card_pos]
    have := pred_card_le_card_erase (s := cycleNodesOffRoot N C) (a := u)
    omega
  have hb' := mem_cycleNodesOffRoot.1 (mem_of_mem_erase hb)
  have hb1 : (nodeBlock N.graph N.leaf C b).ncard ≤ 1 :=
    (Set.ncard_le_ncard (nodeBlock_subset_of_cycles hN.1 h1 hC'.1 hcyc (Ne.symm hne) hu' hc hw' hu
      hb'.1 hc' hw (ne_of_mem_erase hb)) (Set.toFinite _)).trans hu'1
  have hvr : v ≠ N.root := fun h => by
    have := hN.1.root_indegree
    rw [← h, h2] at this
    exact absurd this (by norm_num)
  have hvS : v ∈ cycleNodesOffRoot N C := mem_cycleNodesOffRoot.2 ⟨hv, hvr⟩
  have hbv : b ≠ v := by
    rintro rfl
    rw [nodeBlock_hybrid hN h1 hcyc hv h2, hk] at hb1
    omega
  -- the blocks of `v` and `b` hold the four taxa
  have hpair : cycleNodesOffRoot N C = {v, b} :=
    (eq_of_subset_of_card_le (insert_subset hvS (singleton_subset_iff.2 (mem_of_mem_erase hb)))
      (by rw [hS, card_pair (Ne.symm hbv)])).symm
  have hsum := sum_ncard_nodeBlock_eq hN h1 hcyc
  rw [hpair, sum_pair (Ne.symm hbv), nodeBlock_hybrid hN h1 hcyc hv h2, hk, hX] at hsum
  omega

/-- **A cycle of an LSA network has at most as many nodes other than the root as taxa** (proof of
Lemma 5): their blocks are pairwise disjoint and nonempty. -/
theorem card_cycleNodesOffRoot_le (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hlsa : N.IsLSANetwork) {C : Set E} (hC : IsCycle N.graph C) :
    #(cycleNodesOffRoot N C) ≤ Fintype.card X := by
  have h := sum_ncard_nodeBlock_le h1 hC
  have hle := card_nsmul_le_sum (cycleNodesOffRoot N C) _ 1 fun u hu =>
    one_le_ncard_nodeBlock hN h1 hlsa hC hu
  rw [smul_eq_mul, mul_one] at hle
  omega

end Several

end Banos2019
