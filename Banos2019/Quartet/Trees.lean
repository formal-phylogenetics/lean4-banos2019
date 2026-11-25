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

For a phylogenetic network `N` with no hybrid arc, valid parameters `θ` and at least two taxa:

* `treeCluster N v`: the taxa below the vertex `v`; `treeClusters N`, the clusters of all vertices, form
  a hierarchy (`isHierarchy_treeClusters`).
* `treeLength N θ A`: the sum of the lengths of the arcs into the vertices with cluster `A`, the length of
  the edge above `A` once the nodes of indegree one and outdegree one are suppressed.
* `treeSpeciesTree`: the species tree with these clusters and lengths;
  `treeSpeciesTree_unrootedLength`: the length of a split of its unrooted tree is the total length of
  the arcs that induce the split.
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

/-- The length of the split `A | Aᶜ` of the unrooted species tree is the total length of the arcs
into the vertices with cluster `A` or `Aᶜ` (other than `univ`). -/
theorem treeSpeciesTree_unrootedLength (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e)
    {θ : MetricData E} (hθ : N.IsMetric θ) (A : Finset X) :
    (treeSpeciesTree N hN ht hθ).unrootedLength A =
      ∑ e with treeCluster N (N.graph.target e) ≠ univ ∧
        (treeCluster N (N.graph.target e) = A ∨ treeCluster N (N.graph.target e) = Aᶜ),
        θ.length e := by
  unfold SpeciesTree.unrootedLength
  rw [treeSpeciesTree_clusters, treeSpeciesTree_length]
  unfold treeLength
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun e => treeCluster N (N.graph.target e))
    (t := (treeClusters N).filter fun C => C ≠ univ ∧ (C = A ∨ C = Aᶜ))
    fun e he => mem_filter.2 ⟨mem_treeClusters.2 ⟨_, rfl⟩, (mem_filter.1 he).2⟩]
  refine sum_congr rfl fun C hC => sum_congr ?_ fun _ _ => rfl
  ext e
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro rfl
    exact ⟨(mem_filter.1 hC).2, rfl⟩
  · exact fun h => h.2

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
    {f : V' → V} (hf : Function.Injective f) (hleaf : ∀ x, K.leaf x = f (K'.leaf x)) (v : V') :
    NMSC.taxaInj K univ (f v) = NMSC.taxaInj K' univ v := by
  unfold NMSC.taxaInj
  congr 1
  refine filter_congr fun x _ => ?_
  rw [hleaf x, hf.eq_iff]

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
  simp only [taxaInj_congr fV.injective hleaf]
  rfl

/-- The network with one vertex and no arc: the upper part of a network whose root has outdegree
one. -/
def pointNetwork (X : Type*) : RootedNetwork Unit Empty X where
  graph := { source := Empty.elim, target := Empty.elim }
  root := ()
  leaf _ := ()

/-- The parameters of `pointNetwork`. -/
def pointMetric : MetricData Empty := ⟨Empty.elim, Empty.elim⟩

/-- On the network with one vertex, the forest at the root is the injected forest. -/
theorem rootDist_pointNetwork (ρ : ℝ) (inj : Unit → Finset (Finset X)) (F : Finset (Finset X)) :
    NMSC.rootDist (pointNetwork X) pointMetric ρ inj F = if inj () = F then 1 else 0 := by
  unfold NMSC.rootDist NMSC.injWeight NMSC.arriving
  simp [pointNetwork]

/-- The law at the root of a network with valid injected forests is carried by forests. -/
theorem isForest_of_rootDist_ne_zero {V' E' : Type*} [Fintype V'] [Fintype E']
    {K' : RootedNetwork V' E' X} (hK' : K'.IsPhylogenetic) {θ' : MetricData E'} {ρ : ℝ}
    {inj : V' → Finset (Finset X)} (hinj : NMSC.ValidInj inj) {F : Finset (Finset X)}
    (h : NMSC.rootDist K' θ' ρ inj F ≠ 0) : IsForest F := by
  unfold NMSC.rootDist at h
  obtain ⟨bot, -, hb⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨top, -, htop⟩ := exists_ne_zero_of_sum_ne_zero hb
  have hF : NMSC.arriving K' inj top K'.root = F := by
    by_contra hne
    rw [ite_eq_right hne, mul_zero] at htop
    exact htop rfl
  rw [← hF]
  exact (NMSC.good_arriving_root hK' hinj (left_ne_zero_of_mul htop)).1.1

/-- **A tree without nodes of indegree one and outdegree one, whose root has outdegree one, is the
network of its hierarchy below one arc from the root**, and the population on that arc does not change
the gene tree. -/
theorem geneTreeDist_eq_hierarchyNetwork_of_eq_one (hK : K.IsPhylogenetic)
    (ht : ∀ e, ¬ K.IsHybridArc e) (hc : ∀ v, ¬ K.IsChainVertex v) {θ : MetricData E}
    (hinh : ∀ e, θ.inheritance e = 1) (hX : 2 ≤ Fintype.card X)
    (hroot : K.graph.outdegree K.root = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (G : Finset (Finset X)) :
    geneTreeDist K θ ρ G =
      geneTreeDist (hierarchyNetwork (treeClusters K) (isHierarchy_treeClusters hK ht))
        (hierarchyMetric (treeClusters K) (treeLength K θ)) ρ G := by
  set H := treeClusters K
  have hH := isHierarchy_treeClusters hK ht
  have hHN := hierarchyNetwork_isPhylogenetic H hH hX
  obtain ⟨p, hp⟩ := (K.graph.outdegree_eq_one_iff _).1 hroot
  have hp0 : K.graph.source p = K.root := (hp p).2 rfl
  have hsrc : ∀ e, e ≠ p → K.graph.source e ≠ K.root := fun e he h => he ((hp e).1 h)
  -- the child of the root has all the taxa below it
  have hcp : treeCluster K (K.graph.target p) = univ := by
    refine eq_univ_of_forall fun x => mem_treeCluster.2 ?_
    rcases Relation.ReflTransGen.cases_head (hK.root_reaches (K.leaf x)) with h | ⟨c, ⟨f, hf, rfl⟩, hcx⟩
    · exact absurd h.symm (leaf_ne_root hK x)
    · rwa [(hp f).1 hf] at hcx
  have hmem : ∀ v, treeCluster K v ∈ H := fun v => mem_treeClusters.2 ⟨v, rfl⟩
  -- the vertices: the root, and the others as their clusters
  let ψ : V → Unit ⊕ HierarchyVertex H := fun v =>
    if v = K.root then .inl () else .inr ⟨treeCluster K v, hmem v⟩
  have hψr : ψ K.root = .inl () := ite_eq_left rfl
  have hψv : ∀ v, v ≠ K.root → ψ v = .inr ⟨treeCluster K v, hmem v⟩ := fun v hv => ite_eq_right hv
  have hψ : Function.Bijective ψ := by
    refine ⟨fun u v h => ?_, fun y => ?_⟩
    · by_cases hu : u = K.root <;> by_cases hv : v = K.root
      · rw [hu, hv]
      · rw [hu, hψr, hψv v hv] at h
        exact absurd h Sum.inl_ne_inr
      · rw [hv, hψr, hψv u hu] at h
        exact absurd h Sum.inr_ne_inl
      · rw [hψv u hu, hψv v hv] at h
        exact treeCluster_injOn hK ht hc (Or.inl hu) (Or.inl hv)
          (congrArg Subtype.val (Sum.inr_injective h))
    · rcases y with ⟨⟩ | ⟨A, hA⟩
      · exact ⟨K.root, hψr⟩
      · obtain ⟨v, rfl⟩ := mem_treeClusters.1 hA
        by_cases hv : v = K.root
        · refine ⟨K.graph.target p, ?_⟩
          rw [hψv _ (NMSC.target_ne_root hK p)]
          congr 2
          rw [hcp, hv, treeCluster_root hK]
        · exact ⟨v, hψv v hv⟩
  -- the arcs: the arc from the root, and the others as the clusters of their targets
  let φ : E → Empty ⊕ Unit ⊕ HierarchyArc H := fun e =>
    if h : e = p then .inr (.inl ()) else
      .inr (.inr ⟨⟨treeCluster K (K.graph.target e), hmem _⟩,
        treeCluster_target_ne_univ hK ht hc (Or.inl (hsrc e h))⟩)
  have hφp : φ p = .inr (.inl ()) := dite_eq_left rfl
  have hφe : ∀ e (h : e ≠ p), φ e = .inr (.inr ⟨⟨treeCluster K (K.graph.target e), hmem _⟩,
      treeCluster_target_ne_univ hK ht hc (Or.inl (hsrc e h))⟩) := fun e h => dite_eq_right h
  have hinjT : ∀ e f, e ≠ p → f ≠ p →
      treeCluster K (K.graph.target e) = treeCluster K (K.graph.target f) → e = f :=
    fun e f _ _ h => arc_eq_of_target_eq ht (treeCluster_injOn hK ht hc
      (Or.inl (NMSC.target_ne_root hK e)) (Or.inl (NMSC.target_ne_root hK f)) h)
  have hφ : Function.Bijective φ := by
    refine ⟨fun e f h => ?_, fun y => ?_⟩
    · by_cases he : e = p <;> by_cases hf : f = p
      · rw [he, hf]
      · rw [he, hφp, hφe f hf] at h
        exact absurd (Sum.inr_injective h) Sum.inl_ne_inr
      · rw [hf, hφp, hφe e he] at h
        exact absurd (Sum.inr_injective h) Sum.inr_ne_inl
      · rw [hφe e he, hφe f hf] at h
        exact hinjT e f he hf (congrArg (fun a : HierarchyArc H => a.val.val)
          (Sum.inr_injective (Sum.inr_injective h)))
    · rcases y with y | ⟨⟩ | a
      · exact y.elim
      · exact ⟨p, hφp⟩
      · obtain ⟨v, hv⟩ := mem_treeClusters.1 a.val.2
        have hvr : v ≠ K.root := fun h => a.2 (by rw [← hv, h, treeCluster_root hK])
        obtain ⟨e, he⟩ := (K.graph.one_le_indegree_iff v).1 (hK.nonroot_indegree v hvr)
        have hep : e ≠ p := fun h => a.2 (by rw [← hv, ← he, h, hcp])
        refine ⟨e, ?_⟩
        rw [hφe e hep]
        exact congrArg (fun b => Sum.inr (Sum.inr b)) (Subtype.ext (Subtype.ext (by
          show treeCluster K (K.graph.target e) = a.val.val
          rw [he, hv])))
  let fV := (Equiv.ofBijective ψ hψ).symm
  let fE := (Equiv.ofBijective φ hφ).symm
  have hψfV : ∀ y, ψ (fV y) = y := (Equiv.ofBijective ψ hψ).apply_symm_apply
  have hφfE : ∀ y, φ (fE y) = y := (Equiv.ofBijective φ hφ).apply_symm_apply
  have hfV0 : fV (.inl ()) = K.root := by
    apply hψ.1
    rw [hψfV, hψr]
  have hfEp : fE (.inr (.inl ())) = p := by
    apply hφ.1
    rw [hφfE, hφp]
  have hfEa : ∀ a, fE (.inr (.inr a)) ≠ p ∧
      treeCluster K (K.graph.target (fE (.inr (.inr a)))) = a.val.val := by
    intro a
    have h := hφfE (.inr (.inr a))
    by_cases hep : fE (.inr (.inr a)) = p
    · rw [hep, hφp] at h
      exact absurd (Sum.inr_injective h) Sum.inl_ne_inr
    · rw [hφe _ hep] at h
      exact ⟨hep, congrArg (fun b : HierarchyArc H => b.val.val)
        (Sum.inr_injective (Sum.inr_injective h))⟩
  have hfVv : ∀ v, v ≠ K.root → ∀ y, ψ v = y → fV y = v := fun v _ y h => by
    rw [← h]
    exact (Equiv.ofBijective ψ hψ).symm_apply_apply v
  have hg : NMSC.IsGlued K θ (pointNetwork X) pointMetric (hierarchyNetwork H hH)
      (hierarchyMetric H (treeLength K θ)) fV fE (fun _ => ()) (fun _ => θ.length p) :=
    { source₀ := fun e => e.elim
      target₀ := fun e => e.elim
      sourceP := fun u => by
        cases u
        rw [hfEp, hp0]
        exact hfV0.symm
      targetP := fun u => by
        cases u
        rw [hfEp]
        refine (hfVv _ (NMSC.target_ne_root hK p) _ ?_).symm
        rw [hψv _ (NMSC.target_ne_root hK p)]
        congr 2
      source₁ := fun a => by
        obtain ⟨hep, hcl⟩ := hfEa a
        refine (hfVv _ (hsrc _ hep) _ ?_).symm
        rw [hψv _ (hsrc _ hep)]
        congr 2
        show treeCluster K (K.graph.source (fE (.inr (.inr a)))) = parentCluster H a.val.val
        rw [← hcl, parentCluster_treeCluster hK ht hc (Or.inl (hsrc _ hep))]
      target₁ := fun a => by
        obtain ⟨-, hcl⟩ := hfEa a
        refine (hfVv _ (NMSC.target_ne_root hK _) _ ?_).symm
        rw [hψv _ (NMSC.target_ne_root hK _)]
        congr 2
      root := hfV0.symm
      not_target_root := fun a h => a.2 (congrArg Subtype.val h)
      length₀ := fun e => e.elim
      lengthP := fun u => by
        cases u
        rw [hfEp]
      length₁ := fun a => by
        obtain ⟨hep, hcl⟩ := hfEa a
        show θ.length (fE (.inr (.inr a))) = treeLength K θ a.val.val
        unfold treeLength
        have hsingle : ∀ f ∈ univ.filter (fun f => treeCluster K (K.graph.target f) = a.val.val),
            f ≠ fE (.inr (.inr a)) → θ.length f = 0 := by
          intro f hf hfne
          exfalso
          apply hfne
          have hf' := (mem_filter.1 hf).2
          have hfp : f ≠ p := fun h => a.2 (by rw [← hf', h, hcp])
          exact hinjT f _ hfp hep (hf'.trans hcl.symm)
        exact (Finset.sum_eq_single_of_mem (fE (.inr (.inr a))) (mem_filter.2 ⟨mem_univ _, hcl⟩)
          hsingle).symm
      inheritance₀ := fun e => e.elim
      inheritance₁ := fun a => hinh _ }
  have hleaf : ∀ x, K.leaf x = fV (.inr ((hierarchyNetwork H hH).leaf x)) := fun x => by
    refine (hfVv _ (leaf_ne_root hK x) _ ?_).symm
    rw [hψv _ (leaf_ne_root hK x)]
    congr 2
    exact treeCluster_leaf hK x
  have hlow : NMSC.lowerInj fV (NMSC.taxaInj K univ) = NMSC.taxaInj (hierarchyNetwork H hH) univ := by
    funext v
    exact taxaInj_congr (f := fun v => fV (.inr v)) (fV.injective.comp Sum.inr_injective) hleaf v
  have hup : ∀ t : Finset (Finset X),
      NMSC.upperInj fV (fun _ : Unit => ()) (NMSC.taxaInj K univ) (fun _ : Unit => t) () = t := by
    intro t
    unfold NMSC.upperInj NMSC.taxaInj
    rw [hfV0]
    have h0 : (univ.filter fun x => x ∈ (univ : Finset X) ∧ K.leaf x = K.root) = ∅ :=
      filter_eq_empty_iff.2 fun x _ h => leaf_ne_root hK x h.2
    rw [h0, image_empty, empty_union]
    simp
  have h1 : θ.inheritance (fE (.inr (.inl ()))) = 1 := hinh _
  rw [NMSC.geneTreeDist_eq_injDist hK, NMSC.geneTreeDist_eq_injDist hHN,
    NMSC.injDist_eq_sum_rootDist, NMSC.injDist_eq_sum_rootDist]
  simp only [hg.rootDist_eq_unit hρ h1, rootDist_pointNetwork, hup, hlow, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, ite_true]
  simp only [sum_mul, mul_assoc]
  rw [sum_comm]
  refine sum_congr rfl fun F₁ _ => ?_
  rw [← mul_sum]
  by_cases hR : NMSC.rootDist (hierarchyNetwork H hH) (hierarchyMetric H (treeLength K θ)) ρ
      (NMSC.taxaInj (hierarchyNetwork H hH) univ) F₁ = 0
  · rw [hR, zero_mul, zero_mul]
  · rw [kingmanTransition_mul_kingmanAbsorption
      (isForest_of_rootDist_ne_zero hHN (NMSC.validInj_taxaInj univ) hR)]

/-- **A tree without nodes of indegree one and outdegree one carries the multispecies coalescent of
its hierarchy**, with the lengths of its arcs. -/
theorem geneTreeDist_eq_forestDist_of_reduced (hK : K.IsPhylogenetic) (ht : ∀ e, ¬ K.IsHybridArc e)
    (hc : ∀ v, ¬ K.IsChainVertex v) {θ : MetricData E} (hinh : ∀ e, θ.inheritance e = 1)
    (hX : 2 ≤ Fintype.card X) {ρ : ℝ} (hρ : 0 ≤ ρ) (G : Finset (Finset X)) :
    geneTreeDist K θ ρ G = forestDist (treeClusters K) (treeLength K θ) id univ G := by
  rw [forestDist_univ_eq_geneTreeDist (isHierarchy_treeClusters hK ht) id (treeLength K θ) hρ G]
  by_cases hroot : 2 ≤ K.graph.outdegree K.root
  · exact geneTreeDist_eq_hierarchyNetwork_of_two_le hK ht hc hinh hX hroot ρ G
  · have h0 : K.graph.outdegree K.root ≠ 0 := fun h => by
      obtain ⟨x, hx⟩ := (hK.leaves _).1 h
      exact leaf_ne_root hK x hx
    exact geneTreeDist_eq_hierarchyNetwork_of_eq_one hK ht hc hinh hX (by omega) hρ G

end Reduced

/-! ### The species tree of a network without hybrid arcs -/

section Main

variable {N : RootedNetwork V E X}

/-- **The network multispecies coalescent on a network without hybrid arcs is the multispecies
coalescent on its species tree**, for every inheritance correlation `ρ ≥ 0`: nodes of indegree one and
outdegree one (`NMSC.geneTreeDist_suppress`), a root of outdegree one, and the names of the vertices
and arcs do not matter. -/
theorem geneTreeDist_eq_rootedDist (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e)
    {θ : MetricData E} (hθ : N.IsMetric θ) (hX : 2 ≤ Fintype.card X) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (G : Finset (Finset X)) :
    geneTreeDist N θ ρ G = (treeSpeciesTree N hN ht hθ).rootedDist id G := by
  rw [← NMSC.geneTreeDist_suppress hN hθ.isNormalized hρ G,
    geneTreeDist_eq_forestDist_of_reduced (suppress_isPhylogenetic hN)
      (suppress_not_isHybridArc hN ht) (suppress_not_isChainVertex hN)
      (suppressMetric_inheritance ht hθ) hX hρ G,
    treeClusters_suppress hN, show treeLength (N.suppress hN) (N.suppressMetric θ) = treeLength N θ
      from funext (treeLength_suppress hN θ)]
  rfl

/-- **The concordance factors of a network without hybrid arcs are the quartet probabilities of its
species tree** (Allman, Degnan, Rhodes 2011), for every inheritance correlation `ρ ≥ 0`; Baños 2019
uses `ρ = 0`. With the nodes of indegree one and outdegree one allowed, this covers the quartet trees
of Section 4 and the networks `Q₁⊕`, `Q₂⊕`, `Q₀⊕` of Section 5 without cycles. -/
theorem nmscCF_eq_quartetProb (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e)
    {θ : MetricData E} (hθ : N.IsMetric θ) (hX : 2 ≤ Fintype.card X) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (q : QuartetTree X) :
    nmscCF N θ ρ q = External.AllmanDegnanRhodes2011.quartetProb (treeSpeciesTree N hN ht hθ) q := by
  unfold nmscCF External.AllmanDegnanRhodes2011.quartetProb SpeciesTree.unrootedDist
  simp only [geneTreeDist_eq_rootedDist hN ht hθ hX hρ]
  set σ := treeSpeciesTree N hN ht hθ
  have h : ∀ T : Finset (Finset X),
      (if Displays T q then ∑ G, (if unroot G = T then σ.rootedDist id G else 0) else 0) =
        ∑ G, if unroot G = T then (if Displays (unroot G) q then σ.rootedDist id G else 0)
          else 0 := by
    intro T
    by_cases hT : Displays T q
    · rw [ite_eq_left hT]
      refine sum_congr rfl fun G _ => ?_
      by_cases hG : unroot G = T
      · rw [ite_eq_left hG, ite_eq_left hG, ite_eq_left (hG ▸ hT)]
      · rw [ite_eq_right hG, ite_eq_right hG]
    · rw [ite_eq_right hT]
      refine (sum_eq_zero fun G _ => ?_).symm
      by_cases hG : unroot G = T
      · rw [ite_eq_left hG, ite_eq_right (hG ▸ hT)]
      · rw [ite_eq_right hG]
  rw [sum_congr rfl fun T _ => h T, sum_comm]
  refine sum_congr rfl fun G _ => ?_
  rw [sum_ite_eq, ite_eq_left (mem_univ _)]

end Main

end Banos2019
