module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Matrix

/-! # Baños 2019: the statements of record

H. Baños, *Identifying species network features from gene tree quartets under the coalescent model*,
Bull. Math. Biol. 81 (2019) 494–534, <https://doi.org/10.1007/s11538-018-0485-4>.

The model. A *binary rooted phylogenetic network* on the taxa `X` (Definition 1) is a finite acyclic
directed multigraph (two edges may join the same two nodes) with a root of outdegree two, leaves
labelled by `X`, and tree nodes (one parent, two children) and hybrid nodes (two parents, one child).
It is *level-1* (Definition 12) when no two cycles of its undirected graph share an edge. A *metric*
(Definition 2) gives each edge a positive length in coalescent units, and the two hybrid edges entering
a hybrid node inheritance probabilities in `(0, 1)` summing to one. Under the *network multispecies
coalescent* (Meng and Kubatko 2009), lineages coalesce along each edge by Kingman's coalescent (each pair
at rate one) and, at a hybrid node, each lineage independently takes a hybrid edge with its inheritance
probability; one lineage is sampled per taxon. The *concordance factor* of a quartet tree `ab|cd` is the
probability that the gene tree displays it (Definition 14). A set of four taxa has the *Big Cycle
property* when its three concordance factors are different (Definition 17). "For generic parameters"
means: except on a set of parameters of Lebesgue measure zero, in the coordinates given by the edge
lengths and one inheritance probability per hybrid node.

The *unrooted network* `N⁻` (Definition 5) keeps what is below the lowest stable ancestor `LSA(X)` of
the taxa (the lowest of the nodes that lie on every path from the root to a taxon), forgets the direction of the tree
edges, and suppresses `LSA(X)`; suppressing a node of degree two merges its two edges (Figure 3). The
*induced unrooted network* `(N⁻)_s` on four taxa `s` (Definition 10) keeps the edges of `N⁻` on simple
treks between taxa of `s` and suppresses the nodes of degree two. `Ñ` (Theorem 4) is `N⁻` with its
2- and 3-cycles contracted, the hybrid edges of its 4-cycles undirected, and the nodes of degree two
left by the contraction suppressed.

* `theorem3` (Theorem 3): for generic parameters, four taxa satisfy the Big Cycle property exactly when
  their induced unrooted network has a 4-cycle.
* `theorem4` (Theorem 4, the main result): for generic parameters, the orderings of the quartet
  concordance factors of a level-1 network identify `Ñ`, up to isomorphism: there is a property of the
  parameters, holding for generic parameters of every binary level-1 network, such that two such
  networks on the same taxa with such parameters and the same orderings have isomorphic `Ñ`. The networks have at least two
  taxa, which Definition 5 needs.
* `proposition5` (Proposition 5): two binary level-1 metric LSA quartet networks (on four taxa, rooted
  at the LSA of the taxa) that induce isomorphic metric unrooted networks have the same concordance
  factors.
-/

-- BEGIN SHARED DEFINITIONS

/-! ## Networks

A rooted network is a finite directed multigraph with named edges (two edges may join the same two
nodes), a root and a labelling of the taxa by leaves. A semidirected network keeps, for every edge,
its two ends in some order; for a hybrid edge the order is its direction, for a tree edge it has no
meaning. -/

@[expose] public noncomputable section

open Finset MeasureTheory
open scoped Classical

namespace Banos2019.Model

/-- A directed multigraph: each edge `e` goes from `source e` to `target e`. -/
structure Digraph (V E : Type*) where
  source : E → V
  target : E → V

namespace Digraph

variable {V E : Type*} (G : Digraph V E)

/-- An edge leads from `u` to `v`. -/
def Adj (u v : V) : Prop := ∃ e, G.source e = u ∧ G.target e = v

/-- A directed path, possibly empty, leads from `u` to `v`. -/
def Reaches : V → V → Prop := Relation.ReflTransGen G.Adj

/-- No non-empty directed path from a node to itself. -/
def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen G.Adj v v

/-- The number of edges entering `v`. -/
def indegree (v : V) : ℕ := {e | G.target e = v}.ncard

/-- The number of edges leaving `v`. -/
def outdegree (v : V) : ℕ := {e | G.source e = v}.ncard

/-- The edge `e` joins `u` and `w`, in one direction or the other. -/
def Joins (e : E) (u w : V) : Prop :=
  (G.source e = u ∧ G.target e = w) ∨ (G.source e = w ∧ G.target e = u)

/-- **Cycles** (Definition 11): a cycle of size `k ≥ 1` is a closed path `v₀ e₀ v₁ ⋯ e_{k-1} v₀` of
the undirected graph, with distinct nodes and distinct edges; `C` is its set of edges. -/
def IsCycle (C : Set E) : Prop :=
  ∃ (k : ℕ) (v : Fin k → V) (e : Fin k → E), 0 < k ∧
    (∀ i : Fin k, G.Joins (e i) (v i) (v (finRotate k i))) ∧
    Function.Injective v ∧ Function.Injective e ∧ Set.range e = C

/-- The nodes of the edges `C`. -/
def nodes (C : Set E) : Set V := {u | ∃ e ∈ C, G.source e = u ∨ G.target e = u}

/-- **Level-1** (Definition 12): no two cycles share an edge. -/
def IsLevelOne : Prop :=
  ∀ C C', G.IsCycle C → G.IsCycle C' → (C ∩ C').Nonempty → C = C'

end Digraph

/-- A rooted network on the taxa `X`. -/
structure Network (V E X : Type*) where
  graph : Digraph V E
  root : V
  leaf : X → V

/-- The numerical parameters: edge lengths, in coalescent units, and inheritance probabilities. -/
structure Params (E : Type*) where
  length : E → ℝ
  inheritance : E → ℝ

namespace Network

variable {V E X : Type*} (N : Network V E X)

/-- A hybrid edge: it enters a node with two entering edges. -/
def IsHybridEdge (e : E) : Prop := N.graph.indegree (N.graph.target e) = 2

/-- **Definition 1**: a *binary rooted phylogenetic network*: finite, acyclic, with a root of indegree
`0` and outdegree `2`, leaves of indegree `1` and outdegree `0` labelled injectively by the taxa, and
every other node a tree node (indegree `1`, outdegree `2`) or a hybrid node (indegree `2`, outdegree
`1`). Definition 1 also asks for a connected graph and a bijective labelling of the leaves; both follow:
every node but the root has a parent, so going up from any node ends at the root, and a node of
outdegree `0` is a labelled leaf. -/
def IsBinaryNetwork : Prop :=
  Finite V ∧ Finite E ∧ Finite X ∧ N.graph.IsAcyclic ∧
    N.graph.indegree N.root = 0 ∧ N.graph.outdegree N.root = 2 ∧
    (∀ x, N.graph.indegree (N.leaf x) = 1 ∧ N.graph.outdegree (N.leaf x) = 0) ∧
    Function.Injective N.leaf ∧
    ∀ v, v ≠ N.root → v ∉ Set.range N.leaf →
      (N.graph.indegree v = 1 ∧ N.graph.outdegree v = 2) ∨
        (N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1)

/-- **Definition 2**: a *metric*: positive edge lengths; the two hybrid edges entering a hybrid node
have inheritance probabilities in `(0, 1)` summing to `1`; a tree edge has inheritance probability `1`,
which every lineage on it follows. -/
def IsMetric (θ : Params E) : Prop :=
  (∀ e, 0 < θ.length e) ∧ (∀ e, ¬ N.IsHybridEdge e → θ.inheritance e = 1) ∧
    (∀ e, N.IsHybridEdge e → 0 < θ.inheritance e ∧ θ.inheritance e < 1) ∧
    ∀ e f, e ≠ f → N.IsHybridEdge e → N.graph.target e = N.graph.target f →
      θ.inheritance e + θ.inheritance f = 1

/-- Every directed path from the root to `u` passes through `w`. -/
def OnEveryRootPath (u w : V) : Prop :=
  ¬ (N.root ≠ w ∧ u ≠ w ∧
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ w ∧ b ≠ w) N.root u)

/-- **Definition 4**: `v` is the *lowest stable ancestor* (LSA) of the taxa `Z`: it lies on every
directed path from the root to a taxon of `Z`, and every other such node is above it. -/
def IsLSA (Z : Set X) (v : V) : Prop :=
  (∀ z ∈ Z, N.OnEveryRootPath (N.leaf z) v) ∧
    ∀ w, (∀ z ∈ Z, N.OnEveryRootPath (N.leaf z) w) → N.graph.Reaches w v

/-- The LSA of all the taxa (when it exists, which it does for a binary rooted network with taxa). -/
def lsa : V := @Classical.epsilon V ⟨N.root⟩ (N.IsLSA Set.univ)

end Network

/-- A semidirected network: each edge `e` has ends `source e` and `target e`; for a hybrid edge
(`IsDirected e`) the edge is directed from `source e` to `target e`. -/
structure SDNetwork (V E X : Type*) where
  graph : Digraph V E
  IsDirected : E → Prop
  leaf : X → V

namespace Network

variable {V E X : Type*} (N : Network V E X)

/-- The part of `N` below the LSA of all the taxa, with its tree edges undirected: the nodes below or
at the LSA (and the leaves), the edges leaving them. -/
def belowLSA : SDNetwork {v // N.graph.Reaches N.lsa v ∨ ∃ x, N.leaf x = v}
    {e // N.graph.Reaches N.lsa (N.graph.source e)} X where
  graph :=
    { source := fun e => ⟨N.graph.source e.1, Or.inl e.2⟩
      target := fun e => ⟨N.graph.target e.1, Or.inl (e.2.tail ⟨e.1, rfl, rfl⟩)⟩ }
  IsDirected e := N.IsHybridEdge e.1
  leaf x := ⟨N.leaf x, Or.inr ⟨x, rfl⟩⟩

end Network

namespace SDNetwork

variable {V E X : Type*} (G : SDNetwork V E X)

/-! ### Suppressing nodes of degree two (Section 2.3, Figure 3) -/

/-- The degree of a node. -/
def degree (u : V) : ℕ := G.graph.indegree u + G.graph.outdegree u

/-- The nodes that suppression keeps: those of degree other than two, the taxa, and the nodes of `P`. -/
def IsBranch (P : Set V) (u : V) : Prop := G.degree u ≠ 2 ∨ (∃ x, G.leaf x = u) ∨ u ∈ P

/-- A chain `p 0, e 0, p 1, …, e (k-1), p k`: a path of the undirected graph with `k ≥ 1` distinct
edges whose inner nodes are not kept and whose ends are kept. -/
structure IsChainOf (P : Set V) (k : ℕ) (p : Fin (k + 1) → V) (e : Fin k → E) : Prop where
  pos : 0 < k
  joins : ∀ i : Fin k, G.graph.Joins (e i) (p i.castSucc) (p i.succ)
  inner : ∀ i : Fin (k + 1), i ≠ 0 → i ≠ Fin.last k → ¬ G.IsBranch P (p i)
  ends : G.IsBranch P (p 0) ∧ G.IsBranch P (p (Fin.last k))
  injective_edge : Function.Injective e

/-- `c` is the set of edges of a chain. -/
def IsChain (P : Set V) (c : Set E) : Prop :=
  ∃ (k : ℕ) (p : Fin (k + 1) → V) (e : Fin k → E), G.IsChainOf P k p e ∧ Set.range e = c

/-- A chain, with its nodes and edges in order. -/
structure ChainRep (P : Set V) (c : Set E) where
  k : ℕ
  p : Fin (k + 1) → V
  e : Fin k → E
  isChainOf : G.IsChainOf P k p e
  range_eq : Set.range e = c

/-- An order chosen on a chain. -/
def chainRep (P : Set V) {c : Set E} (hc : G.IsChain P c) : G.ChainRep P c :=
  let h := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hc))
  ⟨_, _, _, h.1, h.2⟩

/-- The chain points toward its last node: it has a hybrid edge, and each of its hybrid edges enters
the next node along the order. -/
def ChainRep.PointsForward {G : SDNetwork V E X} {P : Set V} {c : Set E} (r : G.ChainRep P c) :
    Prop :=
  (∃ i, G.IsDirected (r.e i)) ∧ ∀ i, G.IsDirected (r.e i) → G.graph.target (r.e i) = r.p i.succ

/-- The chain points toward its first node. -/
def ChainRep.PointsBackward {G : SDNetwork V E X} {P : Set V} {c : Set E} (r : G.ChainRep P c) :
    Prop :=
  (∃ i, G.IsDirected (r.e i)) ∧ ∀ i, G.IsDirected (r.e i) → G.graph.target (r.e i) = r.p i.castSucc

/-- **Suppressing** the nodes of degree two other than the taxa and the nodes of `P`: the edges become
the chains, a chain being a hybrid edge, directed toward one of its ends, when it points toward it
(Figure 3: `x → z — y`, `x — z → y`, `x → z → y` give `x → y`; `x → z ← y`, `x ← z → y`, `x — z — y`
give `x — y`). -/
def suppressExcept (P : Set V) : SDNetwork {u // G.IsBranch P u} {c : Set E // G.IsChain P c} X where
  graph :=
    { source := fun c =>
        let r := G.chainRep P c.2
        if r.PointsBackward then ⟨r.p (Fin.last r.k), r.isChainOf.ends.2⟩
        else ⟨r.p 0, r.isChainOf.ends.1⟩
      target := fun c =>
        let r := G.chainRep P c.2
        if r.PointsBackward then ⟨r.p 0, r.isChainOf.ends.1⟩
        else ⟨r.p (Fin.last r.k), r.isChainOf.ends.2⟩ }
  IsDirected c := (G.chainRep P c.2).PointsForward ∨ (G.chainRep P c.2).PointsBackward
  leaf x := ⟨G.leaf x, Or.inr (Or.inl ⟨x, rfl⟩)⟩

/-- Suppressing all nodes of degree two but the taxa. In the networks that the paper suppresses (`N⁻`,
`(N⁻)_Z`, `Ñ`), every hybrid edge of a chain enters an end of the chain, and then this rule is the result
of applying Figure 3 to the inner nodes one at a time, in any order. -/
abbrev suppress := G.suppressExcept ∅

/-- The parameters after suppression: a chain has the sum of the lengths of its edges and the product
of the inheritance probabilities of its hybrid edges. -/
def suppressParams (θ : Params E) : Params {c : Set E // G.IsChain ∅ c} where
  length c := ∑ᶠ f ∈ c.1, θ.length f
  inheritance c := ∏ᶠ f ∈ {f | f ∈ c.1 ∧ G.IsDirected f}, θ.inheritance f

/-! ### Paths, treks, induced networks (Definitions 9, 10) -/

/-- A step of a semidirected path along `e` from `u` to `w`. -/
def Step (e : E) (u w : V) : Prop :=
  (G.graph.source e = u ∧ G.graph.target e = w) ∨
    (¬ G.IsDirected e ∧ G.graph.target e = u ∧ G.graph.source e = w)

/-- A semidirected path from `u` to `w` through distinct nodes `S`, with edges `P`. -/
def IsPath (u w : V) (P : Set E) (S : Set V) : Prop :=
  ∃ (k : ℕ) (v : Fin (k + 1) → V) (e : Fin k → E),
    (∀ i : Fin k, G.Step (e i) (v i.castSucc) (v i.succ)) ∧ Function.Injective v ∧
      v 0 = u ∧ v (Fin.last k) = w ∧ Set.range e = P ∧ Set.range v = S

/-- **Definition 9**: a *simple trek* from `x` to `y` with top `t`: semidirected paths from `t` to `x`
and to `y` meeting only at `t`; `P₁`, `P₂` are their edges. -/
def IsSimpleTrek (x y t : V) (P₁ P₂ : Set E) : Prop :=
  ∃ S₁ S₂, G.IsPath t x P₁ S₁ ∧ G.IsPath t y P₂ S₂ ∧ S₁ ∩ S₂ = {t}

/-- **Definition 10**: the *induced unrooted network* `(N⁻)_Z`: retain the edges on simple treks
between taxa of `Z`, then suppress the nodes of degree two. -/
def induced (Z : Set X) :=
  let K : Set E :=
    {e | ∃ x ∈ Z, ∃ y ∈ Z, ∃ t P₁ P₂, G.IsSimpleTrek (G.leaf x) (G.leaf y) t P₁ P₂ ∧ e ∈ P₁ ∪ P₂}
  let R : SDNetwork {u // (∃ e ∈ K, G.graph.source e = u ∨ G.graph.target e = u) ∨
      ∃ z ∈ Z, G.leaf z = u} K Z :=
    { graph :=
        { source := fun e => ⟨G.graph.source e.1, Or.inl ⟨e.1, e.2, Or.inl rfl⟩⟩
          target := fun e => ⟨G.graph.target e.1, Or.inl ⟨e.1, e.2, Or.inr rfl⟩⟩ }
      IsDirected := fun e => G.IsDirected e.1
      leaf := fun z => ⟨G.leaf z.1, Or.inr ⟨z.1, z.2, rfl⟩⟩ }
  R.suppress

/-! ### Contracting cycles and the network `Ñ` -/

/-- Two nodes lie on one cycle satisfying `Q`. -/
def ContractRel (Q : Set E → Prop) (u w : V) : Prop :=
  ∃ C, G.graph.IsCycle C ∧ Q C ∧ u ∈ G.graph.nodes C ∧ w ∈ G.graph.nodes C

/-- **Contracting** the cycles satisfying `Q`: removing their edges and identifying the nodes of each. -/
def contract (Q : Set E → Prop) :
    SDNetwork (Quot (G.ContractRel Q)) {e // ∀ C, G.graph.IsCycle C → Q C → e ∉ C} X where
  graph :=
    { source := fun e => Quot.mk _ (G.graph.source e.1)
      target := fun e => Quot.mk _ (G.graph.target e.1) }
  IsDirected e := G.IsDirected e.1
  leaf x := Quot.mk _ (G.leaf x)

/-- **The network `Ñ` of Theorem 4**: contract the 2- and 3-cycles, forget the direction of the hybrid
edges of 4-cycles, and suppress the nodes of degree two this leaves. The paper's statement does not
mention the last step, and its `Ñ` (Figure 23) has no node of degree two. Contracting a 2-cycle leaves
one, and how many there are is not identifiable (`2₁`- and `2₃`-cycles do not change the concordance
factors, Corollary 2); without the suppression Theorem 4 would be false. -/
def tilde :=
  let H := G.contract fun C => C.ncard ≤ 3
  let H' : SDNetwork _ _ X :=
    ⟨H.graph, fun e => H.IsDirected e ∧ ¬ ∃ C, G.graph.IsCycle C ∧ C.ncard = 4 ∧ e.1 ∈ C, H.leaf⟩
  H'.suppress

end SDNetwork

namespace Network

variable {V E X : Type*} (N : Network V E X)

/-- **Definition 5**: the *unrooted semidirected network* `N⁻`: keep what is below `LSA(X)`, undirect
the tree edges and suppress `LSA(X)` (the one node of degree two). -/
abbrev unrooted := N.belowLSA.suppress

/-- **Definition 6**: the parameters of `N⁻`: the edge replacing the two edges at `LSA(X)` has the sum
of their lengths and the inheritance probability of the hybrid one, if any. -/
def unrootedParams (θ : Params E) :=
  N.belowLSA.suppressParams ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩

end Network

/-- An **isomorphism** of leaf-labelled semidirected networks: bijections of nodes and of edges keeping
the ends of the edges, which edges are hybrid and their directions, and the leaves. -/
structure SDIso {V E V' E' X : Type*} (G : SDNetwork V E X) (G' : SDNetwork V' E' X) where
  vert : V ≃ V'
  edge : E ≃ E'
  isDirected_iff : ∀ e, G'.IsDirected (edge e) ↔ G.IsDirected e
  joins : ∀ e, G'.graph.Joins (edge e) (vert (G.graph.source e)) (vert (G.graph.target e))
  directed : ∀ e, G.IsDirected e →
    G'.graph.source (edge e) = vert (G.graph.source e) ∧
      G'.graph.target (edge e) = vert (G.graph.target e)
  leaf : ∀ x, G'.leaf x = vert (G.leaf x)

/-- An isomorphism of metric semidirected networks: it also keeps the edge lengths and the inheritance
probabilities of the hybrid edges. -/
structure SDMetricIso {V E V' E' X : Type*} (G : SDNetwork V E X) (θ : Params E)
    (G' : SDNetwork V' E' X) (θ' : Params E') extends SDIso G G' where
  length : ∀ e, θ'.length (edge e) = θ.length e
  inheritance : ∀ e, G.IsDirected e → θ'.inheritance (edge e) = θ.inheritance e

/-! ## The network multispecies coalescent

A forest of gene lineages `L` is the set of its clusters; its roots are its maximal clusters. Along an
edge of length `t` the lineages coalesce by Kingman's coalescent, each pair of roots merging at rate
`1`; above the root, for an infinite time. At a hybrid node each lineage independently takes each of
the two hybrid edges with its inheritance probability (Meng and Kubatko 2009). -/

section Coalescent

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The roots of a forest: its maximal clusters. -/
def roots (F : Finset (Finset L)) : Finset (Finset L) := F.filter fun A => ∀ B ∈ F, A ⊆ B → B = A

/-- The generator of Kingman's coalescent on forests: each pair of distinct roots `A, B` merges at
rate `1`, adding the cluster `A ∪ B`. -/
def kingmanGenerator : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if G = F then -((#(roots F)).choose 2 : ℝ)
    else if ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F then 1 else 0

/-- Kingman's coalescent over a time `t`: `exp (t • Q)`. -/
def kingmanTransition (t : ℝ) : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  NormedSpace.exp (t • kingmanGenerator)

/-- Kingman's coalescent over an infinite time: the limits as `t → ∞`. -/
def kingmanAbsorption : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G => Filter.limUnder Filter.atTop fun t : ℝ => kingmanTransition t F G

/-- The part of the forest `F` below its roots in `A`. -/
def forestBelow (F A : Finset (Finset L)) : Finset (Finset L) := F.filter fun B => ∃ C ∈ A, B ⊆ C

end Coalescent

/-- The unrooted tree of a rooted tree `G`: the sides of the splits of its non-root clusters. -/
def unroot {L : Type*} [Fintype L] [DecidableEq L] (G : Finset (Finset L)) : Finset (Finset L) :=
  G.erase univ ∪ (G.erase univ).image compl

/-- A resolved quartet tree `ab|cd`: the pair of its two disjoint cherries `{a,b}`, `{c,d}`. -/
def IsQuartetTree {X : Type*} [DecidableEq X] (s : Finset (Finset X)) : Prop :=
  s.card = 2 ∧ (∀ B ∈ s, B.card = 2) ∧ ∀ B ∈ s, ∀ C ∈ s, B ≠ C → Disjoint B C

/-- The resolved quartet trees on `X`. -/
abbrev QuartetTree (X : Type*) [DecidableEq X] := {s : Finset (Finset X) // IsQuartetTree s}

/-- The four taxa of a quartet tree. -/
def QuartetTree.taxa {X : Type*} [DecidableEq X] (s : QuartetTree X) : Finset X := s.val.sup id

/-- The unrooted tree `T` (given by the sides of its splits) displays the quartet tree `s`. -/
def Displays {X : Type*} [DecidableEq X] (T : Finset (Finset X)) (s : QuartetTree X) : Prop :=
  ∃ A ∈ T, A ∩ s.taxa ∈ s.val

/-- The three quartet trees on the four taxa `q`. -/
def treesOn {X : Type*} [Fintype X] [DecidableEq X] (q : Finset X) : Finset (QuartetTree X) :=
  univ.filter fun r => r.taxa = q

namespace Network

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable (N : Network V E X) (θ : Params E)

/-- The forest arriving at `v` from below: its taxon's lineage, if any, and the forests at the top of
the edges leaving `v`. -/
def arrivingForest (top : E → Finset (Finset X)) (v : V) : Finset (Finset X) :=
  ((univ.filter fun x => N.leaf x = v).image fun x => ({x} : Finset X)) ∪
    (univ.filter fun e => N.graph.source e = v).biUnion top

/-- The probability that the roots of the forest `F` arriving at `v` choose the edges entering `v` that
put the forests `bot e` at their bottoms: each root independently takes the edge `e` with probability
the inheritance probability of `e`. -/
def allocationFactor (F : Finset (Finset X)) (v : V) (bot : E → Finset (Finset X)) : ℝ :=
  ∑ a : {A // A ∈ roots F} → {e // N.graph.target e = v},
    if ∀ e : {e // N.graph.target e = v},
        bot e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val) then
      ∏ r, θ.inheritance (a r).val
    else 0

/-- The probability of a history: the forests `bot e` at the bottom and `top e` at the top of each
edge. -/
def historyWeight (bot top : E → Finset (Finset X)) : ℝ :=
  (∏ v ∈ univ.erase N.root, N.allocationFactor θ (N.arrivingForest top v) v bot) *
    ∏ e, kingmanTransition (θ.length e) (bot e) (top e)

/-- **The network multispecies coalescent**: the probability of the rooted gene tree `G` (its clusters),
one lineage per taxon. -/
def geneTreeDist (G : Finset (Finset X)) : ℝ :=
  ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    N.historyWeight θ bot top * kingmanAbsorption (N.arrivingForest top N.root) G

/-- **Definition 14**: the *quartet concordance factor* of the quartet tree `s`: the probability that
the gene tree displays `s`. -/
def cf (s : QuartetTree X) : ℝ := ∑ G : Finset (Finset X), if Displays (unroot G) s then N.geneTreeDist θ G else 0

/-- A set of parameters is *null*: Lebesgue-null in the coordinates given by all edge lengths and, at
each hybrid node, the inheritance probability of one of its two hybrid edges (the other is `1` minus
it). The coordinates of the other edges are dummies. -/
def IsGenericNull (A : Set (Params E)) : Prop :=
  ∀ d : V → E, (∀ v, N.graph.indegree v = 2 → N.graph.target (d v) = v) →
    ((Measure.pi fun _ : E => (volume : Measure ℝ)).prod (Measure.pi fun _ : E => (volume : Measure ℝ)))
      {x | ∃ θ ∈ A, N.IsMetric θ ∧ θ.length = x.1 ∧
        ∀ e, N.IsHybridEdge e → e ≠ d (N.graph.target e) → θ.inheritance e = x.2 e} = 0

/-- `P` holds *for generic parameters*: the metrics violating it form a null set. -/
def ForGenericParams (P : Params E → Prop) : Prop := N.IsGenericNull {θ | N.IsMetric θ ∧ ¬ P θ}

end Network

/-- **Definition 17**: the four taxa `s` satisfy the *Big Cycle property*: their three concordance
factors are different. -/
def BigCycleOn {X : Type*} [Fintype X] [DecidableEq X] (p : QuartetTree X → ℝ) (s : Finset X) :
    Prop :=
  ∀ q ∈ treesOn s, ∀ r ∈ treesOn s, q ≠ r → p q ≠ p r

/-- **Definition 15**: two families of concordance factors order the quartet trees on each set of four
taxa in the same way. -/
def SameOrdering {X : Type*} [DecidableEq X] (p p' : QuartetTree X → ℝ) : Prop :=
  ∀ q r : QuartetTree X, q.taxa = r.taxa → (p q ≤ p r ↔ p' q ≤ p' r)

end Banos2019.Model

end

-- END SHARED DEFINITIONS

namespace Banos2019Challenge

open Finset Banos2019.Model

/-- **Theorem 3**: for generic numerical parameters, a set `s` of four taxa satisfies the Big Cycle
property if and only if the induced unrooted network `(N⁻)_s` has a 4-cycle. -/
theorem theorem3 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : Network V E X) (hN : N.IsBinaryNetwork) (h1 : N.graph.IsLevelOne) (s : Finset X)
    (hs : #s = 4) :
    N.ForGenericParams fun θ =>
      BigCycleOn (N.cf θ) s ↔ ∃ C, (N.unrooted.induced (s : Set X)).graph.IsCycle C ∧ C.ncard = 4 := by
  sorry

/-- **Theorem 4**: for generic numerical parameters, the collection of orderings of the quartet
concordance factors identifies `Ñ`: a property `G` of the parameters of each network holds for generic
parameters, and two binary level-1 networks on the same taxa, with parameters satisfying `G` and the same
orderings of concordance factors, have isomorphic networks `Ñ`. -/
theorem theorem4 {X : Type} [Fintype X] [DecidableEq X] [Nontrivial X] :
    ∃ G : ∀ (V E : Type) [Fintype V] [Fintype E], Network V E X → Params E → Prop,
      (∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E X),
        N.IsBinaryNetwork → N.graph.IsLevelOne → N.ForGenericParams (G V E N)) ∧
      ∀ (V₁ E₁ V₂ E₂ : Type) [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
        (N₁ : Network V₁ E₁ X) (N₂ : Network V₂ E₂ X),
        N₁.IsBinaryNetwork → N₂.IsBinaryNetwork → N₁.graph.IsLevelOne → N₂.graph.IsLevelOne →
        ∀ θ₁ θ₂, N₁.IsMetric θ₁ → N₂.IsMetric θ₂ → G V₁ E₁ N₁ θ₁ → G V₂ E₂ N₂ θ₂ →
          SameOrdering (N₁.cf θ₁) (N₂.cf θ₂) → Nonempty (SDIso N₁.unrooted.tilde N₂.unrooted.tilde) := by
  sorry

/-- **Proposition 5**: two metric binary level-1 networks on four taxa, each rooted at the LSA of its
taxa, whose metric unrooted networks are isomorphic, have the same concordance factors. -/
theorem proposition5 {V E V' E' X : Type*} [Fintype V] [Fintype E] [Fintype V'] [Fintype E']
    [Fintype X] [DecidableEq X] (hX : Fintype.card X = 4) (Q : Network V E X) (θ : Params E)
    (Q' : Network V' E' X) (θ' : Params E') (hQ : Q.IsBinaryNetwork) (hQ' : Q'.IsBinaryNetwork)
    (h1 : Q.graph.IsLevelOne) (h1' : Q'.graph.IsLevelOne) (hr : Q.IsLSA Set.univ Q.root)
    (hr' : Q'.IsLSA Set.univ Q'.root) (hθ : Q.IsMetric θ) (hθ' : Q'.IsMetric θ')
    (hiso : Nonempty (SDMetricIso Q.unrooted (Q.unrootedParams θ) Q'.unrooted (Q'.unrootedParams θ'))) :
    Q.cf θ = Q'.cf θ' := by
  sorry

end Banos2019Challenge
