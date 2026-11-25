module

public import Banos2019.Quartet.ReduceUnrootedKeep
public import Banos2019.Quartet.DeleteArcReduce

/-!
# `Q⁻` without a hybrid edge

For a binary network `Q` whose root is the LSA of its taxa and a hybrid edge `h` of `Q⁻`,
`deleteHybridEdge Q⁻ h` is `unrootAt` of `deleteArc Q h` at the arc of `Q` that `Q⁻` merges
(`nonempty_sdMetricIso_deleteHybridEdge_unrootAt`): the nodes are those of `Q` other than the root,
the edges the arcs other than `h` and the merged arc, and the other arc into the target of `h` is a
tree arc of `deleteArc Q h`.
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

end Delete

end Banos2019
