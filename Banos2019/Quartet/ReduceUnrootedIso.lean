module

public import Banos2019.Quartet.ReduceUnrootedKeep
public import Banos2019.Quartet.DisjointUnrooted
public import Banos2019.Quartet.ReduceSpec
public import Banos2019.Quartet.ContractCompose

/-!
# The unrooted networks of the reduced networks of Section 5, in the terms of `Q⁻`

For a binary level-1 network `Q` whose root is the LSA of its taxa, the unrooted networks of the
networks that Lemmas 7–11 produce are built from `Q⁻` alone, so isomorphic `Q⁻` and `Q̃⁻` give
isomorphic unrooted networks (proof of Proposition 5).

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

section Delete

variable {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q) (hX : Nontrivial X)

/-- **`Q⁻` without a hybrid edge `h` is `unrootAt` of `deleteArc Q h`** at the arc of `Q` that `Q⁻`
merges. -/
theorem nonempty_sdMetricIso_deleteHybridEdge_unrootAt
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root) (θ : MetricData E)
    {h : SemidirectedArc hQ.1 hQ.2 hX} (hh : (semidirected hQ.1 hQ.2 hX).IsDirected h)
    (hP : (deleteArc Q (sdArc hQ.1 hQ.2 hX h)).IsPhylogenetic) :
    Nonempty (SDMetricIso (deleteHybridEdge (semidirected hQ.1 hQ.2 hX) h)
      (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _)
      (unrootAt (deleteArc Q (sdArc hQ.1 hQ.2 hX h)) hP
        ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩)
      (unrootAtMetric (deleteArc Q (sdArc hQ.1 hQ.2 hX h))
        ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩
        (deleteArcMetric Q (sdArc hQ.1 hQ.2 hX h) θ))) := by
  sorry

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

omit [Fintype V] [Fintype E] in
/-- The arc of `Q` that `Q⁻` merges is off a cycle of `Q` avoiding the root. -/
theorem sdRootArc_notMem_of_root_notMem {D : Set (SemidirectedArc hQ.1 hQ.2 hX)}
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root)
    (hρ : Q.root ∉ cycleNodes Q.graph (liftEdges hQ.1 hQ.2 hX D)) :
    ∀ C, IsCycle Q.graph C → C = liftEdges hQ.1 hQ.2 hX D → sdRootArc hQ.1 hQ.2 hX ∉ C := by
  rintro C - rfl hC
  exact hρ ⟨_, hC, Or.inl ((sdRootArc_spec hQ.1 hQ.2 hX).1.trans hr)⟩

/-- **Contracting a 2-cycle of `Q⁻` off the root is `unrootAt` of the contracted network** at the arc
of `Q` that `Q⁻` merges. -/
theorem nonempty_sdMetricIso_contractCycles_unrootAt
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root) (θ : MetricData E)
    {D : Set (SemidirectedArc hQ.1 hQ.2 hX)} (hD : IsCycle (semidirected hQ.1 hQ.2 hX).graph D)
    (hρ : Q.root ∉ cycleNodes Q.graph (liftEdges hQ.1 hQ.2 hX D)) :
    Nonempty (SDMetricIso (contractCycles (semidirected hQ.1 hQ.2 hX) (· = D))
      (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _)
      (unrootAt (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D))
        (contractSet_isPhylogenetic hQ h1)
        ⟨sdRootArc hQ.1 hQ.2 hX, sdRootArc_notMem_of_root_notMem hQ hX hr hρ⟩)
      (unrootAtMetric (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D))
        ⟨sdRootArc hQ.1 hQ.2 hX, sdRootArc_notMem_of_root_notMem hQ hX hr hρ⟩
        (contractMetric Q (· = liftEdges hQ.1 hQ.2 hX D) θ))) := by
  sorry

/-- **Contracting a 2-cycle of `Q⁻` through the merged edge is the contracted network with its root
kept**: the node of the contracted cycle of `Q⁻` is the root of the contracted network. -/
theorem nonempty_sdMetricIso_contractCycles_keepRootSD
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root) (θ : MetricData E)
    {D : Set (SemidirectedArc hQ.1 hQ.2 hX)} (hD : IsCycle (semidirected hQ.1 hQ.2 hX).graph D)
    (hD2 : D.ncard = 2) (hρ : Q.root ∈ cycleNodes Q.graph (liftEdges hQ.1 hQ.2 hX D)) :
    Nonempty (SDMetricIso (contractCycles (semidirected hQ.1 hQ.2 hX) (· = D))
      (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _)
      (keepRootSD (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D))
        (contractSet_isPhylogenetic hQ h1))
      (restrictMetric (contractMetric Q (· = liftEdges hQ.1 hQ.2 hX D) θ) _)) := by
  sorry

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
