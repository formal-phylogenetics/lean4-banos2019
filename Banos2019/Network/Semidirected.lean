module

public import Banos2019.Network.Cycle
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Semidirected networks: paths, treks, suppression, isomorphism (Baños 2019, Sections 2.3 and 2.4)

The library's `Phylogenetics.SemidirectedNetwork` records each edge with its two ends in some order;
for a hybrid edge (`IsDirected`) the order is the direction, for a tree edge it has no meaning. The
semidirected network `N⁻` of a binary rooted network (Definition 5) and its metric (Definition 6) are
the library's `RootedNetwork.semidirected` and `RootedNetwork.semidirectedMetric`.

* `SDStep`, `IsSDPathOf`, `IsSDPath`: semidirected paths, which follow a hybrid edge only in its
  direction and a tree edge either way, through distinct nodes.
* `DescendsFrom`: a taxon descends from a node (Section 2.3).
* `IsTrek`, `IsSimpleTrek` (Definition 9).
* `trekEdges`, `restrict`: the edges on simple treks between taxa of `Z`, and the network they form.
* `suppress` (Section 2.3, Figure 3): suppressing every node of degree two. The edges of the result
  are the maximal chains through nodes of degree two (other than taxa); a chain is a hybrid edge,
  directed toward one of its ends, when it contains a hybrid edge and all its hybrid edges point toward
  that end. Suppressing the inner nodes one at a time by the rules of Figure 3 gives the same result on
  every chain whose hybrid edges enter its ends, which are the chains of the networks the paper
  suppresses; on a chain with hybrid edges in both directions inside it, the result of one-at-a-time
  suppression depends on the order, and the rule here is one choice.
* `SDIso`, `SDMetricIso`: isomorphisms of leaf-labelled semidirected networks, topological and metric.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

section Paths

variable (G : SemidirectedNetwork V E X)

/-- A step of a semidirected path along the edge `e` from `u` to `w`: in its direction for any edge,
against it only for a tree edge. -/
def SDStep (e : E) (u w : V) : Prop :=
  (G.graph.source e = u ∧ G.graph.target e = w) ∨
    (¬ G.IsDirected e ∧ G.graph.target e = u ∧ G.graph.source e = w)

/-- A *semidirected path* `v 0, e 0, v 1, …, e (k-1), v k` through distinct nodes. -/
structure IsSDPathOf (k : ℕ) (v : Fin (k + 1) → V) (e : Fin k → E) : Prop where
  step : ∀ i : Fin k, SDStep G (e i) (v i.castSucc) (v i.succ)
  injective : Function.Injective v

/-- A semidirected path from `u` to `w` with edges `P` and nodes `S`. -/
def IsSDPath (u w : V) (P : Set E) (S : Set V) : Prop :=
  ∃ (k : ℕ) (v : Fin (k + 1) → V) (e : Fin k → E),
    IsSDPathOf G k v e ∧ v 0 = u ∧ v (Fin.last k) = w ∧ Set.range e = P ∧ Set.range v = S

/-- The taxon `x` *descends from* the node `v`: a semidirected path leads from `v` to `x` (Section
2.3). -/
def DescendsFrom (v : V) (x : X) : Prop :=
  ∃ P S, IsSDPath G v (G.leaf x) P S

/-- **Definition 9**: a *trek* from `x` to `y` with top `t`: a semidirected path from `t` to `x` (edges
`P₁`, nodes `S₁`) and one from `t` to `y` (edges `P₂`, nodes `S₂`). -/
def IsTrek (x y t : V) (P₁ P₂ : Set E) (S₁ S₂ : Set V) : Prop :=
  IsSDPath G t x P₁ S₁ ∧ IsSDPath G t y P₂ S₂

/-- **Definition 9**: a *simple* trek: its two paths have no common node but the top. -/
def IsSimpleTrek (x y t : V) (P₁ P₂ : Set E) : Prop :=
  ∃ S₁ S₂, IsTrek G x y t P₁ P₂ S₁ S₂ ∧ S₁ ∩ S₂ = {t}

/-- The edges on simple treks between two taxa of `Z` (Definition 10). -/
def trekEdges (Z : Set X) : Set E :=
  {e | ∃ x ∈ Z, ∃ y ∈ Z, ∃ t P₁ P₂, IsSimpleTrek G (G.leaf x) (G.leaf y) t P₁ P₂ ∧ e ∈ P₁ ∪ P₂}

end Paths

section Restrict

/-- The nodes of a set of edges and of a set of taxa. -/
def keptNodes (G : SemidirectedNetwork V E X) (K : Set E) (Z : Set X) : Set V :=
  {u | (∃ e ∈ K, G.graph.source e = u ∨ G.graph.target e = u) ∨ ∃ z ∈ Z, G.leaf z = u}

/-- The semidirected network on the taxa `Z` that retains only the edges `K`, with their nodes. -/
def restrict (G : SemidirectedNetwork V E X) (K : Set E) (Z : Set X) :
    SemidirectedNetwork (keptNodes G K Z) K Z where
  graph :=
    { source := fun e => ⟨G.graph.source e.1, Or.inl ⟨e.1, e.2, Or.inl rfl⟩⟩
      target := fun e => ⟨G.graph.target e.1, Or.inl ⟨e.1, e.2, Or.inr rfl⟩⟩ }
  IsDirected e := G.IsDirected e.1
  leaf z := ⟨G.leaf z.1, Or.inr ⟨z.1, z.2, rfl⟩⟩

end Restrict

section Suppress

/-- The degree of a node: the number of edge ends at it, counting parallel edges separately. -/
def degree (G : DirectedMultigraph V E) (u : V) : ℕ := G.indegree u + G.outdegree u

/-- The nodes kept by suppression: those of degree other than two, the taxa, and the nodes of `P`. -/
def IsBranch (G : SemidirectedNetwork V E X) (P : Set V) (u : V) : Prop :=
  degree G.graph u ≠ 2 ∨ (∃ x, G.leaf x = u) ∨ u ∈ P

/-- A *chain*: a path `p 0, e 0, p 1, …, e (k-1), p k` of the undirected graph with `k ≥ 1` distinct
edges, whose inner nodes have degree two and are neither taxa nor in `P`, and whose two ends are not
such nodes. Suppressing the inner nodes merges its edges into one. -/
structure IsChainOf (G : SemidirectedNetwork V E X) (P : Set V) (k : ℕ) (p : Fin (k + 1) → V)
    (e : Fin k → E) : Prop where
  pos : 0 < k
  joins : ∀ i : Fin k, Joins G.graph (e i) (p i.castSucc) (p i.succ)
  inner : ∀ i : Fin (k + 1), i ≠ 0 → i ≠ Fin.last k → ¬ IsBranch G P (p i)
  ends : IsBranch G P (p 0) ∧ IsBranch G P (p (Fin.last k))
  injective_edge : Function.Injective e

/-- `c` is the set of edges of a chain. -/
def IsChain (G : SemidirectedNetwork V E X) (P : Set V) (c : Set E) : Prop :=
  ∃ (k : ℕ) (p : Fin (k + 1) → V) (e : Fin k → E), IsChainOf G P k p e ∧ Set.range e = c

/-- A chain, as nodes and edges in order. -/
structure ChainRep (G : SemidirectedNetwork V E X) (P : Set V) (c : Set E) where
  k : ℕ
  p : Fin (k + 1) → V
  e : Fin k → E
  isChainOf : IsChainOf G P k p e
  range_eq : Set.range e = c

/-- The order chosen on a chain. -/
def chainRep (G : SemidirectedNetwork V E X) (P : Set V) {c : Set E} (hc : IsChain G P c) :
    ChainRep G P c :=
  let h := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hc))
  ⟨_, _, _, h.1, h.2⟩

/-- The chain, in its order, points toward its last node: it has a hybrid edge, and every hybrid edge
of it enters the next node along the order. -/
def ChainRep.PointsForward {G : SemidirectedNetwork V E X} {P : Set V} {c : Set E}
    (r : ChainRep G P c) : Prop :=
  (∃ i, G.IsDirected (r.e i)) ∧ ∀ i, G.IsDirected (r.e i) → G.graph.target (r.e i) = r.p i.succ

/-- The chain, in its order, points toward its first node. -/
def ChainRep.PointsBackward {G : SemidirectedNetwork V E X} {P : Set V} {c : Set E}
    (r : ChainRep G P c) : Prop :=
  (∃ i, G.IsDirected (r.e i)) ∧ ∀ i, G.IsDirected (r.e i) → G.graph.target (r.e i) = r.p i.castSucc

open Classical in
/-- Suppressing the nodes of degree two other than the taxa and the nodes of `P`. The nodes are the
others; the edges are the chains, each from its first node to its last, reversed when it points toward
its first node. A chain is a hybrid edge when it points toward one of its ends. On a chain with one
inner node this is Figure 3 (`x → z — y`, `x — z → y`, `x → z → y` give `x → y`; `x → z ← y`,
`x ← z → y`, `x — z — y` give `x — y`); on longer chains whose hybrid edges enter their ends it is the
result of applying Figure 3 one node at a time, in any order. -/
def suppressExcept (G : SemidirectedNetwork V E X) (P : Set V) :
    SemidirectedNetwork {u // IsBranch G P u} {c : Set E // IsChain G P c} X where
  graph :=
    { source := fun c =>
        let r := chainRep G P c.2
        if r.PointsBackward then ⟨r.p (Fin.last r.k), r.isChainOf.ends.2⟩
        else ⟨r.p 0, r.isChainOf.ends.1⟩
      target := fun c =>
        let r := chainRep G P c.2
        if r.PointsBackward then ⟨r.p 0, r.isChainOf.ends.1⟩
        else ⟨r.p (Fin.last r.k), r.isChainOf.ends.2⟩ }
  IsDirected c := (chainRep G P c.2).PointsForward ∨ (chainRep G P c.2).PointsBackward
  leaf x := ⟨G.leaf x, Or.inr (Or.inl ⟨x, rfl⟩)⟩

/-- **Suppressing all nodes of degree two** (Section 2.3, Figure 3), the taxa excepted. -/
abbrev suppress (G : SemidirectedNetwork V E X) := suppressExcept G ∅

/-- The parameters of the suppressed network: a chain has the sum of the lengths of its edges and the
product of the inheritance probabilities of its hybrid edges. -/
def suppressMetric (G : SemidirectedNetwork V E X) (θ : MetricData E) :
    MetricData {c : Set E // IsChain G ∅ c} where
  length c := ∑ᶠ f ∈ c.1, θ.length f
  inheritance c := ∏ᶠ f ∈ {f | f ∈ c.1 ∧ G.IsDirected f}, θ.inheritance f

end Suppress

section Iso

variable {V' E' : Type*}

/-- An *isomorphism* of leaf-labelled semidirected networks: bijections of the nodes and of the edges
that keep the ends of each edge, which edges are hybrid and the direction of the hybrid edges, and the
labels of the taxa. -/
structure SDIso (G : SemidirectedNetwork V E X) (G' : SemidirectedNetwork V' E' X) where
  vert : V ≃ V'
  edge : E ≃ E'
  isDirected_iff : ∀ e, G'.IsDirected (edge e) ↔ G.IsDirected e
  joins : ∀ e, Joins G'.graph (edge e) (vert (G.graph.source e)) (vert (G.graph.target e))
  directed : ∀ e, G.IsDirected e →
    G'.graph.source (edge e) = vert (G.graph.source e) ∧
      G'.graph.target (edge e) = vert (G.graph.target e)
  leaf : ∀ x, G'.leaf x = vert (G.leaf x)

/-- An isomorphism of metric semidirected networks: it keeps the edge lengths and the inheritance
probabilities of the hybrid edges. -/
structure SDMetricIso (G : SemidirectedNetwork V E X) (θ : MetricData E)
    (G' : SemidirectedNetwork V' E' X) (θ' : MetricData E') extends SDIso G G' where
  length : ∀ e, θ'.length (edge e) = θ.length e
  inheritance : ∀ e, G.IsDirected e → θ'.inheritance (edge e) = θ.inheritance e

end Iso

end Banos2019
