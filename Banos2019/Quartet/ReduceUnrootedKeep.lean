module

public import Banos2019.Quartet.ReduceUnrooted
public import Banos2019.Network.SuppressMetric

/-!
# The unrooted network of a reduced network, with the top node kept

`keepRootSD M hP` is `M` with its tree arcs undirected and, when the root has outdegree one, without
the root and its arc. Its *top* node, the root or its child, has degree two. For `M` satisfying
`IsReducible` whose reduced network `reduceNet M` is an LSA network, and whose root, when of outdegree
one, has a child that is not a chain node, the unrooted network of `reduceNet M` is `keepRootSD M hP`
with its nodes of degree two suppressed (`nonempty_sdMetricIso_suppress_keepRootSD`): the top node and
the chain nodes.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-- **`M` with its tree arcs undirected and its top node kept**: when the root has outdegree one,
without the root and its arc. -/
def keepRootSD (M : RootedNetwork V E X) (hP : M.IsPhylogenetic) :
    SemidirectedNetwork {v // ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)}
      {e // ¬ (M.graph.source e = M.root ∧ M.graph.outdegree M.root = 1)} X where
  graph :=
    { source := fun e => ⟨M.graph.source e.1, e.2⟩
      target := fun e => ⟨M.graph.target e.1, fun h => hP.target_ne_root e.1 h.1⟩ }
  IsDirected e := M.IsHybridArc e.1
  leaf x := ⟨M.leaf x, fun h => M.leaf_ne_root hP x h.1⟩

section Keep

variable [Fintype V] [Fintype E] {M : RootedNetwork V E X} {θ : MetricData E}

/-- **The unrooted network of `reduceNet M` is `keepRootSD M` with its nodes of degree two
suppressed**: its nodes are the nodes of `M` other than the root, the top node and the chain nodes;
an edge is the chain of `M` of its arc, and the merged edge at the root the two chains out of the top
node. -/
theorem nonempty_sdMetricIso_suppress_keepRootSD (hM : IsReducible M θ)
    (hb : IsBinaryRootedNetwork (reduceNet M hM.phylo)) (hX : Nontrivial X)
    (hl : (reduceNet M hM.phylo).IsLSANetwork)
    (hc : ∀ e, M.graph.source e = M.root → M.graph.outdegree M.root = 1 →
      ¬ M.IsChainVertex (M.graph.target e)) :
    Nonempty (SDMetricIso (suppress (keepRootSD M hM.phylo))
      (suppressMetric (keepRootSD M hM.phylo) (restrictMetric θ _))
      (unrooted (reduceNet M hM.phylo) hb hX)
      (unrootedMetric (reduceNet M hM.phylo) hb hX (reduceMetric M hM.phylo θ))) := by
  sorry

end Keep

end Banos2019
