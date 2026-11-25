module

public import Banos2019.Coalescent
public import Banos2019.External.AllmanDegnanRhodes2011.Basic
public import Phylogenetics.NMSC.Glue
public import Phylogenetics.NMSC.SpeciesTree

/-!
# Networks without hybrid edges are species trees (Baños 2019, Sections 4 and 5)

The paper applies the results of Allman, Degnan and Rhodes 2011 on species trees to the rooted networks
without hybrid edges that its reductions produce: the quartet trees, and the networks `Q₁⊕`, `Q₂⊕`,
`Q₀⊕` of Section 5 once every cycle is gone, which may have nodes of indegree one and outdegree one and a
root of outdegree one. This file identifies the network multispecies coalescent on such a network with
the multispecies coalescent on a species tree.

For a phylogenetic network `N` with no hybrid arc:

* `treeCluster N v`: the taxa below the vertex `v`; `treeClusters N`, the clusters of all vertices, form
  a hierarchy (`isHierarchy_treeClusters`).
* `treeLength N θ A`: the sum of the lengths of the arcs into the vertices with cluster `A`, the length of
  the edge above `A` once the nodes of indegree one and outdegree one are suppressed.
* `treeSpeciesTree`: the species tree with these clusters and lengths.
* `geneTreeDist_eq_rootedDist`: the network multispecies coalescent on `N`, for any inheritance
  correlation `ρ ≥ 0`, is the multispecies coalescent on `treeSpeciesTree`; `nmscCF_eq_quartetProb`: the
  concordance factors of `N` are the quartet probabilities of `treeSpeciesTree`.

The proof suppresses the nodes of indegree one and outdegree one (`NMSC.geneTreeDist_suppress`), which
leaves a tree in which distinct vertices have distinct clusters, except for a root of outdegree one and
its child. That tree is the network of its hierarchy (`hierarchyNetwork`), up to the names of the
vertices and arcs (`NMSC.rootDist_congr`), or, with a root of outdegree one, the network of its
hierarchy below one arc from the root (`NMSC.IsGlued.rootDist_eq_unit`), and the population on that arc
does not change the gene tree (`kingmanTransition_mul_kingmanAbsorption`). On the network of a hierarchy
the two coalescents agree (`forestDist_univ_eq_geneTreeDist`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

/-! ### Networks without hybrid arcs -/

section Tree

variable {N : RootedNetwork V E X}

/-- The taxa below the vertex `v`. -/
def treeCluster (N : RootedNetwork V E X) (v : V) : Finset X :=
  univ.filter fun x => N.graph.Reaches v (N.leaf x)

theorem mem_treeCluster {v : V} {x : X} : x ∈ treeCluster N v ↔ N.graph.Reaches v (N.leaf x) := by
  simp [treeCluster]

theorem treeCluster_subset_of_reaches {u v : V} (h : N.graph.Reaches u v) :
    treeCluster N v ⊆ treeCluster N u :=
  fun _ hx => mem_treeCluster.2 (h.trans (mem_treeCluster.1 hx))

/-- Without hybrid arcs every vertex has at most one incoming arc. -/
theorem indegree_le_one (ht : ∀ e, ¬ N.IsHybridArc e) (v : V) : N.graph.indegree v ≤ 1 := by
  by_contra h
  obtain ⟨e, he⟩ := (N.graph.one_le_indegree_iff v).1 (by omega)
  exact ht e (by unfold IsHybridArc; rw [he]; omega)

/-- Without hybrid arcs every arc is a tree arc. -/
theorem isTreeArc_of_forall (ht : ∀ e, ¬ N.IsHybridArc e) (e : E) : N.IsTreeArc e :=
  le_antisymm (indegree_le_one ht _) ((N.graph.one_le_indegree_iff _).2 ⟨e, rfl⟩)

/-- Without hybrid arcs an arc is determined by its target. -/
theorem arc_eq_of_target_eq (ht : ∀ e, ¬ N.IsHybridArc e) {e f : E}
    (h : N.graph.target e = N.graph.target f) : e = f := by
  obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).1 (isTreeArc_of_forall ht f)
  rw [(hg e).1 h, (hg f).1 rfl]

/-- Without hybrid arcs, a vertex that reaches the target of an arc and is not that target reaches its
source. -/
theorem reaches_source_of_reaches_target (ht : ∀ e, ¬ N.IsHybridArc e) {e : E} {a : V}
    (h : N.graph.Reaches a (N.graph.target e)) (hne : a ≠ N.graph.target e) :
    N.graph.Reaches a (N.graph.source e) := by
  rcases Relation.ReflTransGen.cases_tail h with h' | ⟨c, hac, g, hgc, hge⟩
  · exact absurd h'.symm hne
  · rw [← arc_eq_of_target_eq ht hge, hgc]
    exact hac

/-- Without hybrid arcs, the ancestors of a vertex are totally ordered. -/
theorem reaches_total (ht : ∀ e, ¬ N.IsHybridArc e) {u v w : V} (hu : N.graph.Reaches u w)
    (hv : N.graph.Reaches v w) : N.graph.Reaches u v ∨ N.graph.Reaches v u := by
  induction hu with
  | refl => exact Or.inr hv
  | @tail a b hua hab ih =>
    rcases Relation.ReflTransGen.cases_tail hv with h | ⟨c, hvc, hcb⟩
    · subst h
      exact Or.inl (hua.tail hab)
    · obtain ⟨e, he1, he2⟩ := hab
      obtain ⟨f, hf1, hf2⟩ := hcb
      have hef : e = f := arc_eq_of_target_eq ht (he2.trans hf2.symm)
      subst hef
      exact ih (he1 ▸ hf1 ▸ hvc)

/-- The target of an arc does not reach its source. -/
theorem not_reaches_source (hN : N.IsPhylogenetic) (e : E) :
    ¬ N.graph.Reaches (N.graph.target e) (N.graph.source e) := fun h =>
  hN.acyclic _ (Relation.TransGen.head' ⟨e, rfl, rfl⟩ h)

/-- Without hybrid arcs, the clusters of two children of a vertex are disjoint. -/
theorem disjoint_treeCluster (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e) {e f : E}
    (hs : N.graph.source e = N.graph.source f) (hef : e ≠ f) :
    Disjoint (treeCluster N (N.graph.target e)) (treeCluster N (N.graph.target f)) := by
  have key : ∀ e f : E, N.graph.source e = N.graph.source f → e ≠ f →
      ¬ N.graph.Reaches (N.graph.target e) (N.graph.target f) := by
    intro e f hs hef h
    have hne : N.graph.target e ≠ N.graph.target f := fun h' => hef (arc_eq_of_target_eq ht h')
    have := reaches_source_of_reaches_target ht h hne
    rw [← hs] at this
    exact not_reaches_source hN e this
  rw [Finset.disjoint_left]
  intro x hxe hxf
  rcases reaches_total ht (mem_treeCluster.1 hxe) (mem_treeCluster.1 hxf) with h | h
  · exact key e f hs hef h
  · exact key f e hs.symm (Ne.symm hef) h

theorem treeCluster_nonempty (hN : N.IsPhylogenetic) (v : V) : (treeCluster N v).Nonempty := by
  obtain ⟨x, hx⟩ := exists_reaches_leaf hN v
  exact ⟨x, mem_treeCluster.2 hx⟩

theorem treeCluster_root (hN : N.IsPhylogenetic) : treeCluster N N.root = univ :=
  eq_univ_of_forall fun _ => mem_treeCluster.2 (hN.root_reaches _)

/-- A leaf reaches only itself. -/
theorem eq_of_leaf_reaches (hN : N.IsPhylogenetic) {x : X} {w : V}
    (h : N.graph.Reaches (N.leaf x) w) : w = N.leaf x := by
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, ⟨e, he, -⟩, -⟩
  · exact h'.symm
  · exact absurd he ((N.graph.outdegree_eq_zero_iff _).1 ((hN.leaves _).2 ⟨x, rfl⟩) e)

theorem treeCluster_leaf (hN : N.IsPhylogenetic) (x : X) : treeCluster N (N.leaf x) = {x} := by
  ext y
  rw [mem_treeCluster, mem_singleton]
  constructor
  · intro h
    exact hN.leaf_injective (eq_of_leaf_reaches hN h)
  · rintro rfl
    exact .refl

/-- Without hybrid arcs, the clusters of two vertices are nested or disjoint. -/
theorem treeCluster_laminar (ht : ∀ e, ¬ N.IsHybridArc e) (u v : V) :
    treeCluster N u ⊆ treeCluster N v ∨ treeCluster N v ⊆ treeCluster N u ∨
      Disjoint (treeCluster N u) (treeCluster N v) := by
  by_cases h : Disjoint (treeCluster N u) (treeCluster N v)
  · exact Or.inr (Or.inr h)
  · obtain ⟨x, hxu, hxv⟩ := Finset.not_disjoint_iff.1 h
    rcases reaches_total ht (mem_treeCluster.1 hxu) (mem_treeCluster.1 hxv) with h' | h'
    · exact Or.inr (Or.inl (treeCluster_subset_of_reaches h'))
    · exact Or.inl (treeCluster_subset_of_reaches h')

/-- The clusters of the vertices. -/
def treeClusters (N : RootedNetwork V E X) : Finset (Finset X) := univ.image (treeCluster N)

theorem mem_treeClusters {A : Finset X} : A ∈ treeClusters N ↔ ∃ v, treeCluster N v = A := by
  simp [treeClusters]

/-- Without hybrid arcs, the clusters of the vertices form a hierarchy. -/
theorem isHierarchy_treeClusters (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e) :
    IsHierarchy (treeClusters N) := by
  refine ⟨mem_treeClusters.2 ⟨N.root, treeCluster_root hN⟩,
    fun x => mem_treeClusters.2 ⟨N.leaf x, treeCluster_leaf hN x⟩, fun A hA => ?_,
    fun A hA B hB => ?_⟩
  · obtain ⟨v, rfl⟩ := mem_treeClusters.1 hA
    exact treeCluster_nonempty hN v
  · obtain ⟨u, rfl⟩ := mem_treeClusters.1 hA
    obtain ⟨v, rfl⟩ := mem_treeClusters.1 hB
    exact treeCluster_laminar ht u v

/-- The length of the edge above the cluster `A`: the sum of the lengths of the arcs into the vertices
with cluster `A`, which form a chain of nodes of indegree one and outdegree one. -/
def treeLength (N : RootedNetwork V E X) (θ : MetricData E) (A : Finset X) : ℝ :=
  ∑ e with treeCluster N (N.graph.target e) = A, θ.length e

theorem treeLength_pos (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e)
    {θ : MetricData E} (hθ : N.IsMetric θ) {A : Finset X} (hA : A ∈ treeClusters N)
    (hAu : A ≠ univ) : 0 < treeLength N θ A := by
  obtain ⟨v, rfl⟩ := mem_treeClusters.1 hA
  have hv : v ≠ N.root := fun h => hAu (h ▸ treeCluster_root hN)
  obtain ⟨e, he⟩ := (N.graph.one_le_indegree_iff v).1 (hN.nonroot_indegree v hv)
  refine Finset.sum_pos' (fun f _ => (hθ.1 f (isTreeArc_of_forall ht f)).le)
    ⟨e, mem_filter.2 ⟨mem_univ _, by rw [he]⟩, hθ.1 e (isTreeArc_of_forall ht e)⟩

/-- **The species tree of a network without hybrid arcs**: its clusters are those of the vertices, and
the edge above a cluster has the length of the chain of arcs into the vertices with that cluster. -/
def treeSpeciesTree (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (ht : ∀ e, ¬ N.IsHybridArc e) {θ : MetricData E} (hθ : N.IsMetric θ) : SpeciesTree X where
  clusters := treeClusters N
  univ_mem := (isHierarchy_treeClusters hN ht).1
  singleton_mem := (isHierarchy_treeClusters hN ht).2.1
  nonempty_of_mem := (isHierarchy_treeClusters hN ht).2.2.1
  laminar := (isHierarchy_treeClusters hN ht).2.2.2
  length := treeLength N θ
  length_pos := fun _ hA hAu => treeLength_pos hN ht hθ hA hAu

@[simp] theorem treeSpeciesTree_clusters (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e)
    {θ : MetricData E} (hθ : N.IsMetric θ) :
    (treeSpeciesTree N hN ht hθ).clusters = treeClusters N := rfl

@[simp] theorem treeSpeciesTree_length (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e)
    {θ : MetricData E} (hθ : N.IsMetric θ) :
    (treeSpeciesTree N hN ht hθ).length = treeLength N θ := rfl

end Tree

/-! ### Suppressing the nodes of indegree one and outdegree one -/

section Suppress

variable {N : RootedNetwork V E X}

/-- A path of the suppressed network is a path of the network. -/
theorem reaches_of_suppress_reaches (hN : N.IsPhylogenetic) {u v : {v // ¬ N.IsChainVertex v}}
    (h : (N.suppress hN).graph.Reaches u v) : N.graph.Reaches u.1 v.1 := by
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨e, rfl, rfl⟩ := hab
    exact (ih.tail ⟨e.1, rfl, rfl⟩).trans (chainReach_chainEnd hN _).reaches

theorem suppress_reaches_iff (hN : N.IsPhylogenetic) (u v : {v // ¬ N.IsChainVertex v}) :
    (N.suppress hN).graph.Reaches u v ↔ N.graph.Reaches u.1 v.1 :=
  ⟨reaches_of_suppress_reaches hN, suppress_reaches_of_reaches hN u v⟩

/-- The cluster of a vertex in the suppressed network is its cluster in the network. -/
theorem treeCluster_suppress (hN : N.IsPhylogenetic) (v : {v // ¬ N.IsChainVertex v}) :
    treeCluster (N.suppress hN) v = treeCluster N v.1 := by
  ext x
  rw [mem_treeCluster, mem_treeCluster, suppress_reaches_iff]
  rfl

/-- Along a chain of nodes of indegree one and outdegree one the cluster does not change. -/
theorem treeCluster_eq_of_chainReach (hN : N.IsPhylogenetic) {v w : V} (h : N.ChainReach v w) :
    treeCluster N v = treeCluster N w := by
  refine Subset.antisymm ?_ (treeCluster_subset_of_reaches h.reaches)
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Subset.refl _
  | @head a b hab _ ih =>
    refine Subset.trans (fun x hx => ?_) ih
    rw [mem_treeCluster] at hx ⊢
    rcases Relation.ReflTransGen.cases_head hx with h' | ⟨c, hac, hc⟩
    · exact absurd (h' ▸ hab.1) (not_isChainVertex_leaf hN x)
    · rwa [hab.1.adj_unique hab.2 hac]

theorem treeCluster_chainEnd (hN : N.IsPhylogenetic) (v : V) :
    treeCluster N (chainEnd hN v) = treeCluster N v :=
  (treeCluster_eq_of_chainReach hN (chainReach_chainEnd hN v)).symm

/-- Suppression keeps the clusters. -/
theorem treeClusters_suppress (hN : N.IsPhylogenetic) :
    treeClusters (N.suppress hN) = treeClusters N := by
  ext A
  rw [mem_treeClusters, mem_treeClusters]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.1, (treeCluster_suppress hN v).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨⟨chainEnd hN v, not_isChainVertex_chainEnd hN v⟩,
      (treeCluster_suppress hN _).trans (treeCluster_chainEnd hN v)⟩

/-- The arcs of a chain lead to vertices with the cluster of the end of the chain. -/
theorem treeCluster_target_of_isOnChain (hN : N.IsPhylogenetic) {e f : E} (h : N.IsOnChain e f) :
    treeCluster N (N.graph.target f) = treeCluster N (N.graph.target e) := by
  rcases h with rfl | ⟨hf, hc⟩
  · rfl
  · exact (treeCluster_eq_of_chainReach hN (hc.tail ⟨hf, f, rfl, rfl⟩)).symm

/-- Suppression keeps the lengths of the edges above the clusters: the length of an arc of the
suppressed network is that of its chain. -/
theorem treeLength_suppress (hN : N.IsPhylogenetic) (θ : MetricData E) (A : Finset X) :
    treeLength (N.suppress hN) (N.suppressMetric θ) A = treeLength N θ A := by
  unfold treeLength
  have hcl : ∀ e : {e // ¬ N.IsChainVertex (N.graph.source e)},
      treeCluster (N.suppress hN) ((N.suppress hN).graph.target e) =
        treeCluster N (N.graph.target e.1) := fun e =>
    (treeCluster_suppress hN _).trans (treeCluster_chainEnd hN _)
  simp only [hcl]
  rw [sum_filter, sum_filter, ← NMSC.biUnion_chainArcs hN, sum_biUnion
    (fun f _ f' _ h => NMSC.disjoint_chainArcs h)]
  refine sum_congr rfl fun e _ => ?_
  have h : ∀ f ∈ NMSC.chainArcs N e.1,
      (if treeCluster N (N.graph.target f) = A then θ.length f else 0) =
        if treeCluster N (N.graph.target e.1) = A then θ.length f else 0 := fun f hf => by
    rw [treeCluster_target_of_isOnChain hN (NMSC.mem_chainArcs.1 hf)]
  rw [sum_congr rfl h]
  split_ifs
  · rfl
  · simp

/-- Without hybrid arcs, the suppressed network has none. -/
theorem suppress_not_isHybridArc (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e)
    (e : {e // ¬ N.IsChainVertex (N.graph.source e)}) : ¬ (N.suppress hN).IsHybridArc e := by
  have : Finite V := hN.finite_vertices
  have huniq : ∀ f g : {e // ¬ N.IsChainVertex (N.graph.source e)},
      (N.suppress hN).graph.target f = (N.suppress hN).graph.target g → f = g := by
    intro f g hfg
    have hw : chainEnd hN (N.graph.target g.1) ≠ N.root := by
      rcases Relation.ReflTransGen.cases_tail (chainReach_chainEnd hN (N.graph.target g.1)).reaches
        with h | ⟨c, -, d, -, hd⟩
      · rw [h]
        exact NMSC.target_ne_root hN _
      · rw [← hd]
        exact NMSC.target_ne_root hN _
    have h1 : N.graph.indegree (chainEnd hN (N.graph.target g.1)) = 1 :=
      le_antisymm (indegree_le_one ht _) (hN.nonroot_indegree _ hw)
    have hfg' : chainEnd hN (N.graph.target f.1) = chainEnd hN (N.graph.target g.1) :=
      congrArg Subtype.val hfg
    exact Subtype.ext (arc_eq_of_chainReach f.2 g.2 (hfg' ▸ chainReach_chainEnd hN _)
      (chainReach_chainEnd hN _) h1)
  unfold IsHybridArc DirectedMultigraph.indegree
  rw [not_le, Nat.lt_succ_iff, Set.ncard_le_one_iff]
  intro a b ha hb
  exact huniq a b (ha.trans hb.symm)

/-- On a network without hybrid arcs, with valid parameters, every arc of the suppressed network has
inheritance probability one. -/
theorem suppressMetric_inheritance (ht : ∀ e, ¬ N.IsHybridArc e) {θ : MetricData E}
    (hθ : N.IsMetric θ) (e : {e // ¬ N.IsChainVertex (N.graph.source e)}) :
    (N.suppressMetric θ).inheritance e = 1 :=
  prod_eq_one fun f _ => hθ.2.2.1 f (isTreeArc_of_forall ht f)

end Suppress

/-! ### Trees without nodes of indegree one and outdegree one -/

section Reduced

variable {K : RootedNetwork V E X}

theorem leaf_ne_root (hK : K.IsPhylogenetic) (x : X) : K.leaf x ≠ K.root := fun h => by
  have := hK.leaf_indegree x
  rw [h, hK.root_indegree] at this
  exact absurd this (by norm_num)

/-- In a tree without nodes of indegree one and outdegree one, the cluster of a vertex strictly
contains the clusters of its children, unless it is a root of outdegree one. -/
theorem treeCluster_target_ssubset (hK : K.IsPhylogenetic) (ht : ∀ e, ¬ K.IsHybridArc e)
    (hc : ∀ v, ¬ K.IsChainVertex v) {e : E}
    (he : K.graph.source e ≠ K.root ∨ 2 ≤ K.graph.outdegree K.root) :
    treeCluster K (K.graph.target e) ⊂ treeCluster K (K.graph.source e) := by
  refine ssubset_of_subset_of_ne (treeCluster_subset_of_reaches (.single ⟨e, rfl, rfl⟩))
    fun heq => ?_
  -- the only arc out of the source of `e` is `e`
  have hout : ∀ f, K.graph.source f = K.graph.source e ↔ f = e := by
    intro f
    refine ⟨fun hf => ?_, fun h => h ▸ rfl⟩
    by_contra hfe
    obtain ⟨x, hx⟩ := treeCluster_nonempty hK (K.graph.target f)
    have hx' := treeCluster_subset_of_reaches (.single ⟨f, hf, rfl⟩) hx
    rw [← heq] at hx'
    exact Finset.disjoint_left.1 (disjoint_treeCluster hK ht hf hfe) hx hx'
  have h1 : K.graph.outdegree (K.graph.source e) = 1 := (K.graph.outdegree_eq_one_iff _).2 ⟨e, hout⟩
  have hr : K.graph.source e = K.root := by
    by_contra hr
    exact hc _ ⟨le_antisymm (indegree_le_one ht _) (hK.nonroot_indegree _ hr), h1⟩
  rcases he with he | he
  · exact he hr
  · rw [← hr, h1] at he
    omega

/-- In a tree without nodes of indegree one and outdegree one, distinct vertices have distinct
clusters, except a root of outdegree one and its child. -/
theorem treeCluster_injOn (hK : K.IsPhylogenetic) (ht : ∀ e, ¬ K.IsHybridArc e)
    (hc : ∀ v, ¬ K.IsChainVertex v) {u v : V}
    (hu : u ≠ K.root ∨ 2 ≤ K.graph.outdegree K.root) (hv : v ≠ K.root ∨ 2 ≤ K.graph.outdegree K.root)
    (h : treeCluster K u = treeCluster K v) : u = v := by
  have key : ∀ u v : V, (u ≠ K.root ∨ 2 ≤ K.graph.outdegree K.root) →
      treeCluster K u = treeCluster K v → K.graph.Reaches u v → u = v := by
    intro u v hu h huv
    rcases Relation.ReflTransGen.cases_head huv with h' | ⟨w, ⟨e, he1, he2⟩, hwv⟩
    · exact h'
    · exfalso
      have hss := treeCluster_target_ssubset hK ht hc (e := e) (by rw [he1]; exact hu)
      rw [he1, he2] at hss
      have hsub := treeCluster_subset_of_reaches hwv
      rw [← h] at hsub
      exact not_subset_of_ssubset hss hsub
  obtain ⟨x, hx⟩ := treeCluster_nonempty hK u
  have hxv : x ∈ treeCluster K v := h ▸ hx
  rcases reaches_total ht (mem_treeCluster.1 hx) (mem_treeCluster.1 hxv) with h' | h'
  · exact key u v hu h h'
  · exact (key v u hv h.symm h').symm

/-- The cluster of the target of an arc is not `univ`, unless the arc leaves a root of outdegree
one. -/
theorem treeCluster_target_ne_univ (hK : K.IsPhylogenetic) (ht : ∀ e, ¬ K.IsHybridArc e)
    (hc : ∀ v, ¬ K.IsChainVertex v) {e : E}
    (he : K.graph.source e ≠ K.root ∨ 2 ≤ K.graph.outdegree K.root) :
    treeCluster K (K.graph.target e) ≠ univ := fun h => by
  have hss := treeCluster_target_ssubset hK ht hc he
  rw [h] at hss
  exact not_subset_of_ssubset hss (subset_univ _)

/-- The parent cluster of the cluster of the target of an arc is the cluster of its source. -/
theorem parentCluster_treeCluster (hK : K.IsPhylogenetic) (ht : ∀ e, ¬ K.IsHybridArc e)
    (hc : ∀ v, ¬ K.IsChainVertex v) {e : E}
    (he : K.graph.source e ≠ K.root ∨ 2 ≤ K.graph.outdegree K.root) :
    parentCluster (treeClusters K) (treeCluster K (K.graph.target e)) =
      treeCluster K (K.graph.source e) := by
  have hH := isHierarchy_treeClusters hK ht
  have hss := treeCluster_target_ssubset hK ht hc he
  have hA : treeCluster K (K.graph.target e) ∈ treeClusters K := mem_treeClusters.2 ⟨_, rfl⟩
  have hAu := treeCluster_target_ne_univ hK ht hc he
  refine Subset.antisymm (parentCluster_subset (mem_treeClusters.2 ⟨_, rfl⟩) hss) ?_
  obtain ⟨w, hw⟩ := mem_treeClusters.1 (hH.parentCluster_mem hA hAu)
  have hlt := hH.ssubset_parentCluster hA hAu
  rw [← hw] at hlt ⊢
  obtain ⟨x, hx⟩ := treeCluster_nonempty hK (K.graph.target e)
  rcases reaches_total ht (mem_treeCluster.1 hx) (mem_treeCluster.1 (hlt.subset hx)) with h | h
  · exact absurd (treeCluster_subset_of_reaches h) (not_subset_of_ssubset hlt)
  · have hne : w ≠ K.graph.target e := fun h' => by
      rw [h'] at hlt
      exact ssubset_irrefl _ hlt
    exact treeCluster_subset_of_reaches (reaches_source_of_reaches_target ht h hne)

/-- The singleton lineages injected at the vertices of a network correspond along a bijection of the
vertices that matches the leaves. -/
theorem taxaInj_congr {V' E' : Type*} [Fintype V'] [Fintype E'] {K' : RootedNetwork V' E' X}
    (fV : V' ≃ V) (hleaf : ∀ x, K.leaf x = fV (K'.leaf x)) (v : V') :
    NMSC.taxaInj K univ (fV v) = NMSC.taxaInj K' univ v := by
  unfold NMSC.taxaInj
  congr 1
  refine filter_congr fun x _ => ?_
  rw [hleaf x, fV.injective.eq_iff]

/-- **A tree without nodes of indegree one and outdegree one, whose root has outdegree at least two,
is the network of its hierarchy** (up to the names of the vertices and arcs), so the two have the same
gene tree distribution. -/
theorem geneTreeDist_eq_hierarchyNetwork_of_two_le (hK : K.IsPhylogenetic)
    (ht : ∀ e, ¬ K.IsHybridArc e) (hc : ∀ v, ¬ K.IsChainVertex v) {θ : MetricData E}
    (hinh : ∀ e, θ.inheritance e = 1) (hX : 2 ≤ Fintype.card X)
    (hroot : 2 ≤ K.graph.outdegree K.root) (ρ : ℝ) (G : Finset (Finset X)) :
    geneTreeDist K θ ρ G =
      geneTreeDist (hierarchyNetwork (treeClusters K) (isHierarchy_treeClusters hK ht))
        (hierarchyMetric (treeClusters K) (treeLength K θ)) ρ G := by
  set H := treeClusters K
  have hH := isHierarchy_treeClusters hK ht
  have hD : ∀ v : V, v ≠ K.root ∨ 2 ≤ K.graph.outdegree K.root := fun _ => Or.inr hroot
  let ψ : V → HierarchyVertex H := fun v => ⟨treeCluster K v, mem_treeClusters.2 ⟨v, rfl⟩⟩
  have hψ : Function.Bijective ψ := by
    refine ⟨fun u v h => treeCluster_injOn hK ht hc (hD u) (hD v) (congrArg Subtype.val h),
      fun A => ?_⟩
    obtain ⟨v, hv⟩ := mem_treeClusters.1 A.2
    exact ⟨v, Subtype.ext hv⟩
  let φ : E → HierarchyArc H := fun e => ⟨ψ (K.graph.target e),
    treeCluster_target_ne_univ hK ht hc (hD _)⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun e f h => arc_eq_of_target_eq ht (treeCluster_injOn hK ht hc (hD _) (hD _)
      (congrArg (fun a : HierarchyArc H => a.val.val) h)), fun a => ?_⟩
    obtain ⟨v, hv⟩ := mem_treeClusters.1 a.val.2
    have hvr : v ≠ K.root := fun h => a.2 (by rw [← hv, h, treeCluster_root hK])
    obtain ⟨e, he⟩ := (K.graph.one_le_indegree_iff v).1 (hK.nonroot_indegree v hvr)
    refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
    show treeCluster K (K.graph.target e) = a.val.val
    rw [he, hv]
  let fV := (Equiv.ofBijective ψ hψ).symm
  let fE := (Equiv.ofBijective φ hφ).symm
  have hψfV : ∀ A, ψ (fV A) = A := (Equiv.ofBijective ψ hψ).apply_symm_apply
  have hfa : ∀ a, treeCluster K (K.graph.target (fE a)) = a.val.val := fun a =>
    congrArg (fun b : HierarchyArc H => b.val.val) ((Equiv.ofBijective φ hφ).apply_symm_apply a)
  have hs : ∀ a, K.graph.source (fE a) = fV ((hierarchyNetwork H hH).graph.source a) := by
    intro a
    apply hψ.1
    rw [hψfV]
    apply Subtype.ext
    show treeCluster K (K.graph.source (fE a)) = parentCluster H a.val.val
    rw [← hfa a, parentCluster_treeCluster hK ht hc (hD _)]
  have ht' : ∀ a, K.graph.target (fE a) = fV ((hierarchyNetwork H hH).graph.target a) := by
    intro a
    apply hψ.1
    rw [hψfV]
    exact Subtype.ext (hfa a)
  have hroot' : K.root = fV (hierarchyNetwork H hH).root := by
    apply hψ.1
    rw [hψfV]
    exact Subtype.ext (treeCluster_root hK)
  have hlen : ∀ a, θ.length (fE a) = (hierarchyMetric H (treeLength K θ)).length a := by
    intro a
    show θ.length (fE a) = treeLength K θ a.val.val
    unfold treeLength
    refine (Finset.sum_eq_single_of_mem (fE a) (mem_filter.2 ⟨mem_univ _, hfa a⟩)
      fun f hf hfne => absurd (arc_eq_of_target_eq ht (treeCluster_injOn hK ht hc (hD _) (hD _)
        ((mem_filter.1 hf).2.trans (hfa a).symm))) hfne).symm
  have hinh' : ∀ a, θ.inheritance (fE a) = (hierarchyMetric H (treeLength K θ)).inheritance a :=
    fun a => hinh _
  have hleaf : ∀ x, K.leaf x = fV ((hierarchyNetwork H hH).leaf x) := by
    intro x
    apply hψ.1
    rw [hψfV]
    exact Subtype.ext (treeCluster_leaf hK x)
  rw [NMSC.geneTreeDist_eq_injDist hK,
    NMSC.geneTreeDist_eq_injDist (hierarchyNetwork_isPhylogenetic H hH hX),
    NMSC.injDist_eq_sum_rootDist, NMSC.injDist_eq_sum_rootDist]
  refine sum_congr rfl fun F _ => ?_
  rw [NMSC.rootDist_congr fV fE hs ht' hroot' hlen hinh' (NMSC.taxaInj K univ) F]
  simp only [taxaInj_congr fV hleaf]
  rfl

end Reduced

end Banos2019
