module

public import Phylogenetics.Network.Semidirected

/-!
# Rooted networks and the lowest stable ancestor (Baños 2019, Sections 2.1 and 2.2)

The paper's networks are the library's `Phylogenetics.RootedNetwork`: a directed multigraph with named
arcs, a root and a labelling of the taxa. Definition 1 allows up to two edges between two nodes, as the
library does.

* `IsBinaryRootedNetwork` (Definition 1): `IsPhylogenetic` and `IsBinary`; `isBinaryRootedNetwork_iff`
  restates the clauses of Definition 1.
* `IsMetricNetwork` (Definition 2): positive edge lengths and inheritance probabilities in `(0, 1)` that
  sum to one at each hybrid node. The library's `MetricData` gives every arc an inheritance probability,
  and the coalescent reads it on tree arcs too, so a tree arc has inheritance probability `1`
  (`isMetricNetwork_iff`).
* `IsAbove` (Definition 3).
* The lowest stable ancestor (Definition 4) is the library's `RootedNetwork.lsa`, characterized by
  `RootedNetwork.IsLeastStableAncestor`; `isLeastStableAncestor_iff_def4` restates Definition 4.
* `lemma1`, `lemma2`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-- **Definition 1** (`def::network`): a *topological binary rooted phylogenetic network* on the taxa
`X`: a phylogenetic network (a finite directed acyclic graph whose root, of indegree `0`, reaches every
node, and whose sinks are exactly the leaves, labelled bijectively by `X`, each of indegree `1`) that is
binary (the root has outdegree `2`, every other node that is not a leaf has degree `3`). Up to two edges
may join the same two nodes. `isBinaryRootedNetwork_iff` gives the clauses of Definition 1. -/
def IsBinaryRootedNetwork (N : RootedNetwork V E X) : Prop :=
  N.IsPhylogenetic ∧ N.IsBinary

/-- **Definition 1, clause by clause**: a connected directed acyclic graph with root of indegree `0` and
outdegree `2`, leaves of indegree `1` and outdegree `0` labelled injectively by `X`, and every other node
a tree node (indegree `1`, outdegree `2`) or a hybrid node (indegree `2`, outdegree `1`). -/
theorem isBinaryRootedNetwork_iff (N : RootedNetwork V E X) :
    IsBinaryRootedNetwork N ↔
      Finite V ∧ Finite E ∧ Finite X ∧ N.graph.IsConnected ∧ N.graph.IsAcyclic ∧
        N.graph.indegree N.root = 0 ∧ N.graph.outdegree N.root = 2 ∧
        (∀ x, N.graph.indegree (N.leaf x) = 1 ∧ N.graph.outdegree (N.leaf x) = 0) ∧
        Function.Injective N.leaf ∧
        ∀ v, v ≠ N.root → v ∉ Set.range N.leaf →
          (N.graph.indegree v = 1 ∧ N.graph.outdegree v = 2) ∨
            (N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1) := by
  sorry

/-- **Definition 2**: a *metric* `(λ, γ)` for a binary rooted network: every edge has a positive length,
and the inheritance probabilities make the library's valid parameters (`RootedNetwork.IsMetric`: those
of the two hybrid edges of a hybrid node are positive and sum to `1`; a tree edge has `1`). -/
def IsMetricNetwork [Fintype E] (N : RootedNetwork V E X) (θ : MetricData E) : Prop :=
  N.IsMetric θ ∧ ∀ e, 0 < θ.length e

/-- **Definition 2, as printed**: on a binary rooted network, a metric gives every edge a positive
length, every hybrid edge an inheritance probability in `(0, 1)`, with those of the two hybrid edges of
a hybrid node summing to `1`; tree edges carry inheritance probability `1`, which the coalescent reads. -/
theorem isMetricNetwork_iff [Fintype E] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (θ : MetricData E) :
    IsMetricNetwork N θ ↔
      (∀ e, 0 < θ.length e) ∧ (∀ e, N.IsTreeArc e → θ.inheritance e = 1) ∧
        (∀ h, N.IsHybridArc h → 0 < θ.inheritance h ∧ θ.inheritance h < 1) ∧
        ∀ h₁ h₂, h₁ ≠ h₂ → N.IsHybridArc h₁ → N.graph.target h₁ = N.graph.target h₂ →
          θ.inheritance h₁ + θ.inheritance h₂ = 1 := by
  sorry

/-- **Definition 3** (`def::above`): `v` is *above* `u` (and `u` *below* `v`) if a non-empty directed
path leads from `v` to `u`. An edge from `x` to `y` is above `v` if `y` is above or equal to `v`
(`N.graph.Reaches y v`), and below `v` if `x` is below or equal to `v` (`N.graph.Reaches v x`). -/
def IsAbove (N : RootedNetwork V E X) (v u : V) : Prop :=
  Relation.TransGen N.graph.Adj v u

/-- **Definition 4** (`def::MRCA`; LSA in the published version), as printed: for `D` the set of nodes
on every directed path from the root to a taxon of `Z`, the LSA of `Z` is the node of `D` below every
other node of `D`. The library's stable ancestors are the nodes of `D`, and its least stable ancestor
(`RootedNetwork.lsa`) is this node. -/
theorem isLeastStableAncestor_iff_def4 (N : RootedNetwork V E X) (Z : Set X) (v : V) :
    N.IsLeastStableAncestor Z v ↔
      N.IsStableAncestor Z v ∧ ∀ u, N.IsStableAncestor Z u → u ≠ v → IsAbove N u v := by
  sorry

/-- **Lemma 1** (`lem::MRCAproperties`): for nonempty sets of taxa `Z ⊆ Y` of a binary rooted network,
(i) the LSA of `Z` has indegree at most one; (ii) at most one of its out-edges is hybrid; (iii) the LSA
of `Z` is below or equal to the LSA of `Y`. The paper states the lemma for every `Z ⊆ X`; the LSA of
the empty set does not exist (every node lies on every path to a taxon of `∅`). -/
theorem lemma1 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {Z Y : Set X}
    (hZ : Z.Nonempty) (hZY : Z ⊆ Y) :
    N.graph.indegree (lsa hN.1 Z hZ) ≤ 1 ∧
      (∀ e f, N.graph.source e = lsa hN.1 Z hZ → N.graph.source f = lsa hN.1 Z hZ →
        N.IsHybridArc e → N.IsHybridArc f → e = f) ∧
      N.graph.Reaches (lsa hN.1 Y (hZ.mono hZY)) (lsa hN.1 Z hZ) := by
  sorry

/-- **Lemma 2** (`lem::mrcaxy`): for a set `Z` of at least two taxa and `x ∈ Z`, some `y ∈ Z` has
`LSA(x, y) = LSA(Z)`. -/
theorem lemma2 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {Z : Set X}
    (hZ : Z.Nontrivial) {x : X} (hx : x ∈ Z) :
    ∃ y ∈ Z, lsa hN.1 {x, y} (Set.insert_nonempty x {y}) = lsa hN.1 Z hZ.nonempty := by
  sorry

end Banos2019
