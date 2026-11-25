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

end Banos2019
