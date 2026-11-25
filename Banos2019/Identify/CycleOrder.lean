module

public import Banos2019.Identify.Blocks

/-!
# The order of the blocks around a cycle of `N⁻` (Baños 2019, Lemma 16)

* `blockNodes`, `JoinedAvoiding`: the blocks of `x` and `y` are joined along `C` avoiding the blocks of
  the taxa `T`.
* `adjacentBlocks_iff_forall_joinedAvoiding`: two blocks of a cycle of size at least four are adjacent
  exactly when they are so joined, avoiding the other two blocks, for every set of four taxa separated
  by the cycle that contains them.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Order

variable {N : RootedNetwork V E X} [Finite E] {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}

/-- The nodes of the cycle `C` whose blocks contain a taxon of `T`. -/
def blockNodes {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (T : Set X') :
    Set V' :=
  {u | u ∈ cycleNodes G.graph C ∧ ∃ x ∈ T, x ∈ nodeBlock G.graph G.leaf C u}

/-- The blocks of `x` and `y` are *joined along `C` avoiding the blocks of `T`*: in the cycle `C` with
the nodes of the blocks of the taxa of `T` removed, the nodes of the blocks of `x` and `y` are
connected. -/
def JoinedAvoiding {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (T : Set X')
    (x y : X') : Prop :=
  ∃ u w, u ∈ cycleNodes G.graph C ∧ w ∈ cycleNodes G.graph C ∧
    x ∈ nodeBlock G.graph G.leaf C u ∧ y ∈ nodeBlock G.graph G.leaf C w ∧
    Relation.ReflTransGen
      (fun a b => G.graph.AdjOn C a b ∧ a ∉ blockNodes G C T ∧ b ∉ blockNodes G C T) u w

/-- **Two blocks of a cycle of size at least four are adjacent exactly when they are joined avoiding
the other two blocks of every set of four taxa that the cycle separates and that contains them.**
Adjacent blocks are joined by their edge. Two blocks that are not adjacent leave a node on each of the
two arcs of the cycle between them, the hybrid node among them when it is not one of the two; taxa in
the blocks of these nodes separate them. -/
theorem adjacentBlocks_iff_forall_joinedAvoiding [DecidableEq X] (h1 : IsLevelOne N.graph) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : 4 ≤ C.ncard) {v}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (x y : X) :
    AdjacentBlocks (unrooted N hN hX) C x y ↔
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y ∧
        ∀ z z', #({x, y, z, z'} : Finset X) = 4 →
          SeparatesQuartet (unrooted N hN hX) C v {x, y, z, z'} →
          JoinedAvoiding (unrooted N hN hX) C {z, z'} x y := by
  sorry

end Order

end Banos2019
