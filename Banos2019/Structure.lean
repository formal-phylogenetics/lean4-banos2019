module

public import Banos2019.Network.Induced

/-!
# The structure of level-1 networks (Baños 2019, Section 3)

* `proposition2`: above `LSA(X)`, a level-1 rooted network is a chain of 2-cycles joined by edges.
* Blocks. Removing the edges of a cycle `C_v` partitions the taxa by the connected components of what
  is left: the *`v`-blocks*. `SameBlock G ℓ D x y`: the taxa `x, y` (at the nodes `ℓ x`, `ℓ y`) are
  joined by a walk avoiding the edges `D`; with `D` the edges of `C_v` these are the `v`-blocks, with
  `D` the edges of a family of cycles the *network blocks* induced by the family. `nodeBlock` is the
  block `B_u` associated with a node `u` of the cycle.
* `lemma4`, `corollary1`: the network partition of a family of cycles is the common refinement of their
  partitions.
* `contractCycles`, `undirectEdges`: contracting cycles (removing their edges and identifying their
  nodes), and forgetting the direction of some hybrid edges, on semidirected networks; they build the
  network `Ñ` of Theorem 4.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-- **Proposition 2** (`prop::structureabove`): in a level-1 binary rooted network, the nodes and edges
above `m = LSA(X)` form a (possibly empty) chain of 2-cycles joined by edges: nodes
`t 0 = r, h 0, t 1, h 1, …, t n = m`, where `t i` has exactly two out-edges, both to `h i`, and `h i` has
exactly one out-edge, to `t (i + 1)`; these are all the edges above `m` (Definition 3: their child is
above or equal to `m`). -/
theorem proposition2 [Nonempty X] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) :
    ∃ (n : ℕ) (t : Fin (n + 1) → V) (h : Fin n → V),
      t 0 = N.root ∧ t (Fin.last n) = lsa hN.1 Set.univ Set.univ_nonempty ∧
      (∀ i : Fin n, ∀ e, N.graph.source e = t i.castSucc ↔ N.graph.target e = h i) ∧
      (∀ i : Fin n, ∀ e, N.graph.source e = h i →
        N.graph.target e = t i.succ ∧ ∀ f, N.graph.source f = h i → f = e) ∧
      ∀ e, N.graph.Reaches (N.graph.target e) (lsa hN.1 Set.univ Set.univ_nonempty) →
        (∃ i : Fin n, N.graph.source e = t i.castSucc) ∨ ∃ i : Fin n, N.graph.source e = h i := by
  sorry

section Blocks

variable (G : DirectedMultigraph V E) (ℓ : X → V)

/-- The taxa `x` and `y` are in the same block of the edge set `D`: a walk avoiding `D` joins them. For
`D` the edges of the cycle `C_v` these are the `v`-blocks; for the edges of a family `𝒟` of cycles, the
network blocks induced by `𝒟`. -/
def SameBlock (D : Set E) (x y : X) : Prop := G.Walks Dᶜ (ℓ x) (ℓ y)

/-- The block `B_u` associated with the node `u` of a cycle with edges `D`: the taxa joined to `u` by a
walk avoiding `D`. -/
def nodeBlock (D : Set E) (u : V) : Set X := {x | G.Walks Dᶜ u (ℓ x)}

/-- The edges of the cycles of the family `𝒟`. -/
def familyEdges (𝒟 : Set (Set E)) : Set E := ⋃₀ 𝒟

/-- The cycles of size at least `k`: their network blocks are the `k`-network blocks. -/
def cyclesOfSizeAtLeast (k : ℕ) : Set (Set E) := {C | IsCycle G C ∧ k ≤ C.ncard}

end Blocks

/-- **Lemma 4** (`2taxnetblo`): in a connected level-1 network, two taxa in different network blocks of
a family `𝒟` of cycles are in different blocks of some cycle of `𝒟` (that is, different `v`-blocks for
its hybrid node `v`). It holds for the graph of a rooted network and of an unrooted one. -/
theorem lemma4 {G : DirectedMultigraph V E} (ℓ : X → V) (hG : G.IsConnected) (h1 : IsLevelOne G)
    {𝒟 : Set (Set E)} (h𝒟 : ∀ C ∈ 𝒟, IsCycle G C) {a b : X}
    (hab : ¬ SameBlock G ℓ (familyEdges 𝒟) a b) : ∃ C ∈ 𝒟, ¬ SameBlock G ℓ C a b := by
  sorry

/-- **Corollary 1** (`cor:partiofparti`): the network partition induced by a family `𝒟` of cycles is the
common refinement of the partitions of its cycles. -/
theorem corollary1 {G : DirectedMultigraph V E} (ℓ : X → V) (hG : G.IsConnected)
    (h1 : IsLevelOne G) {𝒟 : Set (Set E)} (h𝒟 : ∀ C ∈ 𝒟, IsCycle G C) (a b : X) :
    SameBlock G ℓ (familyEdges 𝒟) a b ↔ ∀ C ∈ 𝒟, SameBlock G ℓ C a b := by
  sorry

section Contract

/-- Two nodes are identified by contracting the cycles satisfying `P`: they lie on one such cycle. -/
def ContractRel (G : DirectedMultigraph V E) (P : Set E → Prop) (u w : V) : Prop :=
  ∃ C, IsCycle G C ∧ P C ∧ u ∈ cycleNodes G C ∧ w ∈ cycleNodes G C

/-- **Contracting the cycles satisfying `P`** (Section 2.5): remove their edges and identify the nodes of
each. -/
def contractCycles (G : SemidirectedNetwork V E X) (P : Set E → Prop) :
    SemidirectedNetwork (Quot (ContractRel G.graph P))
      {e // ∀ C, IsCycle G.graph C → P C → e ∉ C} X where
  graph :=
    { source := fun e => Quot.mk _ (G.graph.source e.1)
      target := fun e => Quot.mk _ (G.graph.target e.1) }
  IsDirected e := G.IsDirected e.1
  leaf x := Quot.mk _ (G.leaf x)

/-- Forgetting the direction of the hybrid edges in `D`. -/
def undirectEdges {V' E' : Type*} (G : SemidirectedNetwork V' E' X) (D : Set E') :
    SemidirectedNetwork V' E' X :=
  ⟨G.graph, fun e => G.IsDirected e ∧ e ∉ D, G.leaf⟩

/-- **The network `Ñ` of Theorem 4**: from `N⁻`, contract the 2- and 3-cycles, forget the directions of
the hybrid edges in 4-cycles, and suppress the nodes of degree two that this leaves. The paper's
statement does not mention the last step; contracting a 2-cycle leaves a node of degree two, whose
place on an edge no quartet concordance factor can detect, and the proof of Theorem 4 builds the
network without such nodes. -/
def tildeNetwork (G : SemidirectedNetwork V E X) :=
  suppress (undirectEdges (contractCycles G fun C => C.ncard ≤ 3)
    {e | ∃ C, IsCycle G.graph C ∧ C.ncard = 4 ∧ e.1 ∈ C})

/-- The edges left by removing pendant edges repeatedly until none remains: the largest set of edges in
which every node of an edge has at least two edges of the set. -/
def pendantCore (G : DirectedMultigraph V E) : Set E :=
  ⋃₀ {K | ∀ e ∈ K, ∀ u, (G.source e = u ∨ G.target e = u) →
    2 ≤ {f | f ∈ K ∧ G.source f = u}.ncard + {f | f ∈ K ∧ G.target f = u}.ncard}

/-- **Definition 13** (`treeofcycles`): the *tree of cycles* of `N⁻`: 1) remove pendant edges
repeatedly until none remains; 2) suppress the nodes of degree two that are not on a cycle; 3) contract
each cycle of the result. -/
def treeOfCycles (G : SemidirectedNetwork V E X) :=
  let H := restrict G (pendantCore G.graph) ∅
  contractCycles (suppressExcept H {u | ∃ C, IsCycle G.graph C ∧ u.1 ∈ cycleNodes G.graph C})
    fun _ => True

end Contract

end Banos2019
