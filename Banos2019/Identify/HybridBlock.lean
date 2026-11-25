module

public import Banos2019.Identify.UnrootedCycles

/-!
# The blocks of the nodes of a cycle of `N⁻` (Baños 2019, Sections 3 and 7)

Removing the edges of a cycle `C` of `N⁻` leaves one component through each node of `C`.

* `nodeBlock_nonempty`: the component of every node of `C` holds a taxon.
* `mem_nodeBlock_iff_descendsFrom`: the taxa of the component of the hybrid node are those descending
  from it.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section HybridBlock

variable {N : RootedNetwork V E X} [Finite E] {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}

/-- **Every node of a cycle of `N⁻` has a taxon in its block**: what hangs from the node, off the
cycle, ends at taxa. -/
theorem nodeBlock_nonempty (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {u}
    (hu : u ∈ cycleNodes (unrooted N hN hX).graph C) :
    (nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u).Nonempty := by
  sorry

/-- **The block of the hybrid node is the set of taxa descending from it**: a semidirected path from
the hybrid node leaves it by its child edge and does not come back to the cycle. -/
theorem mem_nodeBlock_iff_descendsFrom (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {v}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (x : X) :
    x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C v ↔
      DescendsFrom (unrooted N hN hX) v x := by
  sorry

end HybridBlock

end Banos2019
