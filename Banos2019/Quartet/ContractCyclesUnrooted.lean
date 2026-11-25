module

public import Banos2019.Quartet.ReduceUnrootedKeep
public import Banos2019.Quartet.ContractSet

/-!
# `Q⁻` with a 2-cycle contracted

For a binary level-1 network `Q` whose root is the LSA of its taxa and a cycle `D` of `Q⁻`,
`contractCycles Q⁻ (· = D)` is, when the cycle `liftEdges D` of `Q` avoids the root, `unrootAt` of
`contractRooted Q (· = liftEdges D)` at the arc of `Q` that `Q⁻` merges
(`nonempty_sdMetricIso_contractCycles_unrootAt`), and, when it passes through the root, the contracted
network with its root kept (`nonempty_sdMetricIso_contractCycles_keepRootSD`): the node of the
contracted cycle of `Q⁻` is the root of the contracted network.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

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

end Contract

end Banos2019
