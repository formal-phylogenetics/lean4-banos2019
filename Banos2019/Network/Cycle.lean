module

public import Banos2019.Network.Rooted
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cycles and level-1 networks (Baños 2019, Section 2.5 and Definition 12)

A cycle is a closed path of the undirected graph `U(N)`: the directions of the edges are ignored. The
definitions are on `Phylogenetics.DirectedMultigraph`, the graph of a rooted network and of a
semidirected network alike, so they apply to both.

* `Joins`: an edge joins two nodes, in either direction.
* `IsCycleOf` (Definition 11): a cycle `v₀ e₀ v₁ e₁ ⋯ e_{k-1} v₀` of size `k`, given by its nodes and
  edges in order, with distinct nodes and distinct edges. `IsCycle C`: `C` is the edge set of a
  cycle; its size is `C.ncard`.
* `IsLevelOne` (Definition 12): no two cycles share an edge.
* `lemma3`: a cycle of a binary level-1 rooted network has exactly one hybrid node and contains its two
  hybrid edges, and two cycles with a common node are the same (Rosselló, Valiente 2009).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-- The edge `e` joins the nodes `u` and `w`, in one direction or the other. -/
def Joins (G : DirectedMultigraph V E) (e : E) (u w : V) : Prop :=
  (G.source e = u ∧ G.target e = w) ∨ (G.source e = w ∧ G.target e = u)

/-- **Definition 11** (`cycle`): a *cycle* of size `k`: a non-empty path `v₀ e₀ v₁ ⋯ v_{k-1} e_{k-1} v₀`
from a node to itself in the undirected graph, the edge `e i` joining `v i` and `v (i + 1)` (indices
mod `k`), with distinct nodes and distinct edges. -/
structure IsCycleOf (G : DirectedMultigraph V E) (k : ℕ) (v : Fin k → V) (e : Fin k → E) : Prop where
  pos : 0 < k
  joins : ∀ i : Fin k, Joins G (e i) (v i) (v (finRotate k i))
  injective_node : Function.Injective v
  injective_edge : Function.Injective e

/-- `C` is the set of edges of a cycle. A cycle traversed from another node or in the other direction
has the same edges, so cycles are identified with their edge sets; the *size* of the cycle is
`C.ncard`, and its nodes are `cycleNodes G C`. -/
def IsCycle (G : DirectedMultigraph V E) (C : Set E) : Prop :=
  ∃ (k : ℕ) (v : Fin k → V) (e : Fin k → E), IsCycleOf G k v e ∧ Set.range e = C

/-- The nodes of a set of edges: their ends. -/
def cycleNodes (G : DirectedMultigraph V E) (C : Set E) : Set V :=
  {u | ∃ e ∈ C, G.source e = u ∨ G.target e = u}

/-- **Definition 12** (`level1`): a network is *level-1* if no two cycles share an edge. -/
def IsLevelOne (G : DirectedMultigraph V E) : Prop :=
  ∀ C C', IsCycle G C → IsCycle G C' → (C ∩ C').Nonempty → C = C'

/-- **Lemma 3** (`lem:assos`), for rooted networks: in a binary level-1 rooted network, a cycle `C`
contains exactly one hybrid node `v`, and both hybrid edges of `v` are edges of `C`; and two cycles
with a common node are the same, so `v` and its hybrid edges lie on exactly one cycle. The paper takes
the lemma from Rosselló and Valiente (2009). -/
theorem lemma3 [Finite E] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {C : Set E} (hC : IsCycle N.graph C) :
    (∃! v, v ∈ cycleNodes N.graph C ∧ N.graph.indegree v = 2) ∧
      (∀ v ∈ cycleNodes N.graph C, N.graph.indegree v = 2 → ∀ h, N.graph.target h = v → h ∈ C) ∧
      ∀ C', IsCycle N.graph C' → (cycleNodes N.graph C ∩ cycleNodes N.graph C').Nonempty → C = C' := by
  sorry

end Banos2019
