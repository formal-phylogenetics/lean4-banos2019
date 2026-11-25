module

public import Banos2019.Quartet.ReduceUnrootedKeep
public import Banos2019.Quartet.DeleteHybridUnrooted
public import Banos2019.Quartet.ContractCyclesUnrooted
public import Banos2019.Quartet.DisjointUnrooted
public import Banos2019.Quartet.ReduceSpec
public import Banos2019.Quartet.ContractCompose

/-!
# The unrooted networks of the reduced networks of Section 5, in the terms of `Q⁻`

For a binary level-1 network `Q` whose root is the LSA of its taxa, the unrooted networks of the
networks that Lemmas 7–11 produce are built from `Q⁻` alone, so isomorphic `Q⁻` and `Q̃⁻` give
isomorphic unrooted networks (proof of Proposition 5).

* `nonempty_sdMetricIso_unrootAt_swap`: merging either of two tree arcs at a root of outdegree two
  gives isomorphic metric networks; `nonempty_sdMetricIso_unrootAt_keepRootSD`: with a root of
  outdegree one, `unrootAt M hP e₀` is `keepRootSD M hP`.
* Without a hybrid edge `h` (`Q₁⊕`, `Q₂⊕`): the unrooted network of `reduceNet (deleteArc Q h)` is
  `deleteHybridEdge Q⁻ h` with its nodes of degree two suppressed
  (`nonempty_sdMetricIso_suppress_deleteHybridEdge`). `deleteHybridEdge Q⁻ h` is `unrootAt` of
  `deleteArc Q h` at the arc of `Q` that `Q⁻` merges
  (`nonempty_sdMetricIso_deleteHybridEdge_unrootAt`).
* Contracting a 2-cycle `D` (`Q₀⊕`): the unrooted network of `contractNet Q (· = liftEdges D)` is
  `contractCycles Q⁻ (· = D)` with its nodes of degree two suppressed
  (`nonempty_sdMetricIso_suppress_contractCycles`). When the cycle of `Q` is off the root,
  `contractCycles Q⁻ (· = D)` is `unrootAt` of the contracted network
  (`nonempty_sdMetricIso_contractCycles_unrootAt`); when it passes through the root, it is the
  contracted network with its root kept (`nonempty_sdMetricIso_contractCycles_keepRootSD`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Swap

variable {M : RootedNetwork V E X} (hP : M.IsPhylogenetic) (θ : MetricData E)

/-- **Merging either tree arc at a root of outdegree two** gives isomorphic metric networks: the
merged edge joins the same two nodes, in the other order. -/
theorem nonempty_sdMetricIso_unrootAt_swap {e₀ e₁ : E} (h₀ : M.graph.source e₀ = M.root)
    (h₁ : M.graph.source e₁ = M.root) (h2 : M.graph.outdegree M.root = 2)
    (ht₀ : ¬ M.IsHybridArc e₀) (ht₁ : ¬ M.IsHybridArc e₁) :
    Nonempty (SDMetricIso (unrootAt M hP e₀) (unrootAtMetric M e₀ θ) (unrootAt M hP e₁)
      (unrootAtMetric M e₁ θ)) := by
  sorry

/-- **With a root of outdegree one, suppressing the root removes it with its arc.** -/
theorem nonempty_sdMetricIso_unrootAt_keepRootSD {e₀ : E} (h₀ : M.graph.source e₀ = M.root)
    (h1 : M.graph.outdegree M.root = 1) :
    Nonempty (SDMetricIso (unrootAt M hP e₀) (unrootAtMetric M e₀ θ) (keepRootSD M hP)
      (restrictMetric θ _)) := by
  sorry

end Swap

section Delete

variable {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q) (hX : Nontrivial X)

/-- **The unrooted network of `Q₁⊕` is `Q⁻` without the hybrid edge `h`, with its nodes of degree
two suppressed.** -/
theorem nonempty_sdMetricIso_suppress_deleteHybridEdge [Fintype V] [Fintype E] [Fintype X]
    (h1 : IsLevelOne Q.graph) (hlsa : Q.IsLSANetwork) {θ : MetricData E} (hθ : IsMetricNetwork Q θ)
    {h : SemidirectedArc hQ.1 hQ.2 hX} (hh : (semidirected hQ.1 hQ.2 hX).IsDirected h)
    (hP : (deleteArc Q (sdArc hQ.1 hQ.2 hX h)).IsPhylogenetic)
    (hb : IsBinaryRootedNetwork (reduceNet _ hP)) :
    Nonempty (SDMetricIso (suppress (deleteHybridEdge (semidirected hQ.1 hQ.2 hX) h))
      (suppressMetric (deleteHybridEdge (semidirected hQ.1 hQ.2 hX) h)
        (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _))
      (unrooted _ hb hX)
      (unrootedMetric _ hb hX (reduceMetric _ hP (deleteArcMetric Q (sdArc hQ.1 hQ.2 hX h) θ)))) := by
  sorry

end Delete

section Contract

variable [Fintype V] [Fintype E] {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q)
  (h1 : IsLevelOne Q.graph) (hX : Nontrivial X)

/-- **The unrooted network of `Q₀⊕` is `Q⁻` with the 2-cycle `D` contracted and its nodes of degree
two suppressed.** -/
theorem nonempty_sdMetricIso_suppress_contractCycles [Fintype X] (hlsa : Q.IsLSANetwork)
    (hX4 : Fintype.card X = 4) {θ : MetricData E} (hθ : IsMetricNetwork Q θ)
    {D : Set (SemidirectedArc hQ.1 hQ.2 hX)} (hD : IsCycle (semidirected hQ.1 hQ.2 hX).graph D)
    (hD2 : D.ncard = 2)
    (hb : IsBinaryRootedNetwork (contractNet Q hQ h1 (· = liftEdges hQ.1 hQ.2 hX D))) :
    Nonempty (SDMetricIso (suppress (contractCycles (semidirected hQ.1 hQ.2 hX) (· = D)))
      (suppressMetric (contractCycles (semidirected hQ.1 hQ.2 hX) (· = D))
        (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _))
      (unrooted _ hb hX)
      (unrootedMetric _ hb hX (contractNetMetric Q hQ h1 (· = liftEdges hQ.1 hQ.2 hX D) θ))) := by
  sorry

end Contract

end Banos2019
