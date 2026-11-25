module

public import Banos2019.Coalescent
public import Phylogenetics.NMSC.Glue

/-!
# Isomorphisms of rooted networks

An isomorphism of rooted networks renames their nodes and their arcs, keeping the ends of the arcs,
the root and the leaves. It keeps the network laws, and, with the same lengths and inheritance
probabilities, the concordance factors. The examples of Section 5 use it to compute the concordance
factors of networks defined by a construction (`disjointNet`) from an explicit isomorphic network.

* `RootedNetworkIso`: an isomorphism; `RootedNetworkIso.symm`: its inverse.
* `RootedNetworkIso.reaches_iff`, `RootedNetworkIso.indegree_eq`, `RootedNetworkIso.outdegree_eq`.
* `RootedNetworkIso.isPhylogenetic`, `RootedNetworkIso.cf_eq`,
  `RootedNetworkIso.cf_eq_of_isPhylogenetic`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {V E V' E' X : Type*}

/-- An *isomorphism of rooted networks*: bijections of the nodes and of the arcs that keep the ends
of the arcs, the root and the leaves. -/
structure RootedNetworkIso (N : RootedNetwork V E X) (N' : RootedNetwork V' E' X) where
  vert : V ≃ V'
  arc : E ≃ E'
  source : ∀ e, N'.graph.source (arc e) = vert (N.graph.source e)
  target : ∀ e, N'.graph.target (arc e) = vert (N.graph.target e)
  root : N'.root = vert N.root
  leaf : ∀ x, N'.leaf x = vert (N.leaf x)

namespace RootedNetworkIso

variable {N : RootedNetwork V E X} {N' : RootedNetwork V' E' X} (φ : RootedNetworkIso N N')

/-- The inverse isomorphism. -/
def symm : RootedNetworkIso N' N where
  vert := φ.vert.symm
  arc := φ.arc.symm
  source e := by
    rw [Equiv.eq_symm_apply, ← φ.source, Equiv.apply_symm_apply]
  target e := by
    rw [Equiv.eq_symm_apply, ← φ.target, Equiv.apply_symm_apply]
  root := by rw [φ.root, Equiv.symm_apply_apply]
  leaf x := by rw [φ.leaf, Equiv.symm_apply_apply]

theorem adj_iff (u w : V) : N'.graph.Adj (φ.vert u) (φ.vert w) ↔ N.graph.Adj u w := by
  constructor
  · rintro ⟨e', hs, ht⟩
    refine ⟨φ.arc.symm e', φ.vert.injective ?_, φ.vert.injective ?_⟩
    · rw [← φ.source, Equiv.apply_symm_apply, hs]
    · rw [← φ.target, Equiv.apply_symm_apply, ht]
  · rintro ⟨e, rfl, rfl⟩
    exact ⟨φ.arc e, φ.source e, φ.target e⟩

theorem reaches_iff (u w : V) : N'.graph.Reaches (φ.vert u) (φ.vert w) ↔ N.graph.Reaches u w := by
  constructor
  · intro h
    have key : ∀ u' w', N'.graph.Reaches u' w' → N.graph.Reaches (φ.vert.symm u')
      (φ.vert.symm w') :=
      fun u' w' h => by
        induction h with
        | refl => exact .refl
        | @tail b c _ hbc ih =>
          refine ih.tail ((φ.adj_iff _ _).1 ?_)
          rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simpa using key _ _ h
  · intro h
    induction h with
    | refl => exact .refl
    | @tail b c _ hbc ih => exact ih.tail ((φ.adj_iff _ _).2 hbc)

theorem transGen_iff (u w : V) :
    Relation.TransGen N'.graph.Adj (φ.vert u) (φ.vert w) ↔ Relation.TransGen N.graph.Adj u w := by
  constructor
  · intro h
    have key : ∀ u' w', Relation.TransGen N'.graph.Adj u' w' →
        Relation.TransGen N.graph.Adj (φ.vert.symm u') (φ.vert.symm w') := fun u' w' h => by
      induction h with
      | single hab =>
        refine .single ((φ.adj_iff _ _).1 ?_)
        rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      | tail _ hbc ih =>
        refine ih.tail ((φ.adj_iff _ _).1 ?_)
        rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simpa using key _ _ h
  · intro h
    induction h with
    | single hab => exact .single ((φ.adj_iff _ _).2 hab)
    | tail _ hbc ih => exact ih.tail ((φ.adj_iff _ _).2 hbc)

theorem indegree_eq (v : V) : N'.graph.indegree (φ.vert v) = N.graph.indegree v := by
  unfold DirectedMultigraph.indegree
  refine Set.ncard_congr (fun e _ => φ.arc.symm e) (fun e he => ?_) (fun e _ f _ h => ?_)
    (fun e he => ⟨φ.arc e, ?_, ?_⟩)
  · show N.graph.target (φ.arc.symm e) = v
    apply φ.vert.injective
    rw [← φ.target, Equiv.apply_symm_apply]
    exact he
  · exact φ.arc.symm.injective h
  · show N'.graph.target (φ.arc e) = φ.vert v
    rw [φ.target]
    exact congrArg φ.vert he
  · simp

theorem outdegree_eq (v : V) : N'.graph.outdegree (φ.vert v) = N.graph.outdegree v := by
  unfold DirectedMultigraph.outdegree
  refine Set.ncard_congr (fun e _ => φ.arc.symm e) (fun e he => ?_) (fun e _ f _ h => ?_)
    (fun e he => ⟨φ.arc e, ?_, ?_⟩)
  · show N.graph.source (φ.arc.symm e) = v
    apply φ.vert.injective
    rw [← φ.source, Equiv.apply_symm_apply]
    exact he
  · exact φ.arc.symm.injective h
  · show N'.graph.source (φ.arc e) = φ.vert v
    rw [φ.source]
    exact congrArg φ.vert he
  · simp

include φ in
/-- **An isomorphic copy of a phylogenetic network is a phylogenetic network.** -/
theorem isPhylogenetic (hN : N.IsPhylogenetic) : N'.IsPhylogenetic where
  finite_vertices := have := hN.finite_vertices; Finite.of_equiv V φ.vert
  finite_arcs := have := hN.finite_arcs; Finite.of_equiv E φ.arc
  finite_taxa := hN.finite_taxa
  acyclic v' h := by
    obtain ⟨v, rfl⟩ := φ.vert.surjective v'
    exact hN.acyclic v ((φ.transGen_iff v v).1 h)
  root_reaches v' := by
    obtain ⟨v, rfl⟩ := φ.vert.surjective v'
    rw [φ.root, φ.reaches_iff]
    exact hN.root_reaches v
  root_indegree := by rw [φ.root, φ.indegree_eq]; exact hN.root_indegree
  nonroot_indegree v' hv' := by
    obtain ⟨v, rfl⟩ := φ.vert.surjective v'
    rw [φ.indegree_eq]
    exact hN.nonroot_indegree v fun h => hv' (by rw [h, φ.root])
  leaf_injective x y h := hN.leaf_injective (φ.vert.injective (by rw [← φ.leaf, ← φ.leaf, h]))
  leaf_indegree x := by rw [φ.leaf, φ.indegree_eq]; exact hN.leaf_indegree x
  leaves v' := by
    obtain ⟨v, rfl⟩ := φ.vert.surjective v'
    rw [φ.outdegree_eq, hN.leaves]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, φ.leaf x⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, φ.vert.injective (by rw [← φ.leaf, hx])⟩

theorem isHybridArc_iff (e : E) : N'.IsHybridArc (φ.arc e) ↔ N.IsHybridArc e := by
  unfold IsHybridArc
  rw [φ.target, φ.indegree_eq]

variable [Fintype V] [Fintype E] [Fintype V'] [Fintype E'] [Fintype X] [DecidableEq X]

/-- **Isomorphic networks with the same parameters have the same concordance factors**: the law of
the forest arriving at the root does not depend on the names (`NMSC.rootDist_congr`). -/
theorem cf_eq (hN : N.IsPhylogenetic) {θ : MetricData E} {θ' : MetricData E'}
    (hlen : ∀ e, θ'.length (φ.arc e) = θ.length e)
    (hinh : ∀ e, θ'.inheritance (φ.arc e) = θ.inheritance e) : cf N' θ' = cf N θ := by
  have hN' := φ.isPhylogenetic hN
  have hinj : (fun v => taxaInj N' univ (φ.vert v)) = taxaInj N univ := by
    funext v
    ext A
    simp only [taxaInj, mem_image, mem_filter, mem_univ, true_and, φ.leaf, φ.vert.injective.eq_iff]
  funext q
  show nmscCF N' θ' 0 q = nmscCF N θ 0 q
  unfold nmscCF
  refine sum_congr rfl fun G _ => ?_
  rw [geneTreeDist_eq_injDist hN', geneTreeDist_eq_injDist hN, injDist_eq_sum_rootDist,
    injDist_eq_sum_rootDist]
  simp only [rootDist_congr φ.vert φ.arc φ.source φ.target φ.root hlen hinh, hinj]

/-- `cf_eq` from the network laws of the image. -/
theorem cf_eq_of_isPhylogenetic (hN' : N'.IsPhylogenetic) {θ : MetricData E} {θ' : MetricData E'}
    (hlen : ∀ e, θ'.length (φ.arc e) = θ.length e)
    (hinh : ∀ e, θ'.inheritance (φ.arc e) = θ.inheritance e) : cf N θ = cf N' θ' := by
  refine φ.symm.cf_eq hN' (fun e => ?_) (fun e => ?_)
  · obtain ⟨e, rfl⟩ := φ.arc.surjective e
    show θ.length (φ.arc.symm (φ.arc e)) = θ'.length (φ.arc e)
    rw [Equiv.symm_apply_apply, hlen]
  · obtain ⟨e, rfl⟩ := φ.arc.surjective e
    show θ.inheritance (φ.arc.symm (φ.arc e)) = θ'.inheritance (φ.arc e)
    rw [Equiv.symm_apply_apply, hinh]

end RootedNetworkIso

end Banos2019
