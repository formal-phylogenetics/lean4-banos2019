module

public import Banos2019.Coalescent

/-!
# Quartet networks and their reductions: definitions (Baños 2019, Section 5)

Section 5 works with an *LSA quartet network* `Q⊕`: a metric binary rooted level-1 network on four
taxa whose root is the LSA of its taxa (`RootedNetwork.IsLSANetwork`), and with the unrooted network
`Q⁻` it induces.

* `InducesCycleType Q C v n k`: the cycle `C` of `Q⊕`, with hybrid node `v`, induces an `n_k`-cycle
  in `Q⁻`. The paper measures a cycle of `Q⊕` by the cycle it induces in `Q⁻`: of size `C.ncard`, or
  one less when `C` contains the root, which `Q⁻` suppresses; `k` is the number of taxa descending
  from `v`, those below `v` in `Q⊕`. `IsCycleType` is the notion on a semidirected network, and
  `inducesCycleType_iff` relates the two.
* `contractRooted Q P` (`Q₀⊕`): contract the cycles satisfying `P`; the node obtained from a cycle
  through the root is the root.
* `deleteArc Q h` (`Q₁⊕`, `Q₂⊕`): remove the hybrid edge `h`; the other hybrid edge of its child
  then carries every lineage, so its inheritance probability becomes `1` (`deleteArcMetric`).
* `disjointNet Q v h₁ h₂ a b` (`Q_a⊕`, `Q_b⊕`): delete everything below `v`, disjoint `h₁` and `h₂`
  from `v`, and label the new leaf at the end of `h₁` by `a`, the one at the end of `h₂` by `b`.
* `probLineages Q θ c k`, `jointCF`, `condCF`: `P(K = k)` and `CF(Q⊕ | K = k)`, where `K` is the
  number of lineages at the top of the arc `c` (the child edge of the hybrid node `v`: the lineages
  at `v`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Types of cycles -/

/-- In the rooted network `Q`, the cycle `C` with hybrid node `v` *induces an `n_k`-cycle* in the
unrooted network: its size there is `n` (the number of edges of `C`, less one when `C` contains the
root, which the unrooted network suppresses), and exactly `k` taxa descend from `v` (Section 5). -/
def InducesCycleType (Q : RootedNetwork V E X) (C : Set E) (v : V) (n k : ℕ) : Prop :=
  IsCycle Q.graph C ∧ v ∈ cycleNodes Q.graph C ∧ Q.graph.indegree v = 2 ∧
    C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0) = n ∧
    {x | Q.graph.Reaches v (Q.leaf x)}.ncard = k

/-- The hybrid node of the cycle `C` of a semidirected network: two hybrid edges of `C` enter it. -/
def IsHybridNodeOf (G : SemidirectedNetwork V E X) (C : Set E) (v : V) : Prop :=
  ∃ h₁ ∈ C, ∃ h₂ ∈ C, h₁ ≠ h₂ ∧ G.IsDirected h₁ ∧ G.IsDirected h₂ ∧
    G.graph.target h₁ = v ∧ G.graph.target h₂ = v

/-- The cycle `C` of a semidirected network is an *`n_k`-cycle*: it has size `n`, and exactly `k`
taxa descend from its hybrid node (Section 5). -/
def IsCycleType (G : SemidirectedNetwork V E X) (C : Set E) (n k : ℕ) : Prop :=
  IsCycle G.graph C ∧ C.ncard = n ∧ ∃ v, IsHybridNodeOf G C v ∧ {x | DescendsFrom G v x}.ncard = k

/-! ### Contracting cycles, deleting a hybrid edge, disjointing -/

/-- Two nodes of `Q` lie on one cycle satisfying `P`. -/
def RootedContractRel (Q : RootedNetwork V E X) (P : Set E → Prop) (u w : V) : Prop :=
  ∃ C, IsCycle Q.graph C ∧ P C ∧ u ∈ cycleNodes Q.graph C ∧ w ∈ cycleNodes Q.graph C

/-- **`Q₀⊕`**: the rooted network obtained by contracting the cycles satisfying `P`: their edges are
removed and the nodes of each are identified. When the root is on a contracted cycle, the node
obtained is the root. -/
def contractRooted (Q : RootedNetwork V E X) (P : Set E → Prop) :
    RootedNetwork (Quot (RootedContractRel Q P)) {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C} X where
  graph :=
    { source := fun e => Quot.mk _ (Q.graph.source e.1)
      target := fun e => Quot.mk _ (Q.graph.target e.1) }
  root := Quot.mk _ Q.root
  leaf x := Quot.mk _ (Q.leaf x)

instance (Q : RootedNetwork V E X) (P : Set E → Prop) [Finite V] :
    Fintype (Quot (RootedContractRel Q P)) :=
  Fintype.ofFinite _

/-- The parameters of a contracted network: those of the remaining edges. -/
def contractMetric (Q : RootedNetwork V E X) (P : Set E → Prop) (θ : MetricData E) :
    MetricData {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C} :=
  ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩

/-- **`Q₁⊕`, `Q₂⊕`**: the rooted network without the edge `h`. Its nodes of degree two are kept:
they do not affect the coalescent. -/
def deleteArc (Q : RootedNetwork V E X) (h : E) : RootedNetwork V {e // e ≠ h} X where
  graph := { source := fun e => Q.graph.source e.1, target := fun e => Q.graph.target e.1 }
  root := Q.root
  leaf := Q.leaf

/-- The parameters without the hybrid edge `h`: the other hybrid edge of its child carries every
lineage, so its inheritance probability is `1`. -/
def deleteArcMetric (Q : RootedNetwork V E X) (h : E) (θ : MetricData E) : MetricData
    {e // e ≠ h} :=
  ⟨fun e => θ.length e.1,
    fun e => if Q.graph.target e.1 = Q.graph.target h then 1 else θ.inheritance e.1⟩

/-- **`Q_a⊕`** (Section 5, before Lemma 11): delete everything below the hybrid node `v`, *disjoint*
its hybrid edges `h₁`, `h₂` from it (remove `v`, give each a new leaf as child), and label the leaf
at the end of `h₁` by `a` and the one at the end of `h₂` by `b`. `Q_b⊕` swaps `a` and `b`. -/
def disjointNet (Q : RootedNetwork V E X) (v : V) (h₁ h₂ : E) (a b : X) :
    RootedNetwork ({u // ¬ Q.graph.Reaches v u} ⊕ Fin 2)
      {e // ¬ Q.graph.Reaches v (Q.graph.source e)} X where
  graph :=
    { source := fun e => .inl ⟨Q.graph.source e.1, e.2⟩
      target := fun e =>
        if e.1 = h₁ then .inr 0 else if e.1 = h₂ then .inr 1 else
        if hr : Q.graph.Reaches v (Q.graph.target e.1) then .inr 0 else .inl ⟨_, hr⟩ }
  root := if hr : Q.graph.Reaches v Q.root then .inr 0 else .inl ⟨Q.root, hr⟩
  leaf x := if x = a then .inr 0 else if x = b then .inr 1 else
    if hr : Q.graph.Reaches v (Q.leaf x) then .inr 0 else .inl ⟨_, hr⟩

/-- The parameters of `Q_a⊕`: those of the remaining edges, with `h₁` and `h₂` tree edges. -/
def disjointMetric (Q : RootedNetwork V E X) (v : V) (h₁ h₂ : E) (θ : MetricData E) :
    MetricData {e // ¬ Q.graph.Reaches v (Q.graph.source e)} :=
  ⟨fun e => θ.length e.1, fun e => if e.1 = h₁ ∨ e.1 = h₂ then 1 else θ.inheritance e.1⟩

/-! ### The number of lineages at a node -/

variable [Fintype V] [Fintype E] [Fintype X]

/-- `P(K = k)`: the probability under the network multispecies coalescent that `k` lineages are at
the top of the arc `c` (for the child edge `c` of a hybrid node `v`, the number `K_v` of lineages at
`v`). -/
def probLineages (Q : RootedNetwork V E X) (θ : MetricData E) (c : E) (k : ℕ) : ℝ :=
  ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    if #(roots (top c)) = k then historyWeight Q θ 0 bot top else 0

/-- `P(K = k) · CF(Q | K = k)`: the probability that `k` lineages are at the top of `c` and the gene
tree displays `q`. -/
def jointCF (Q : RootedNetwork V E X) (θ : MetricData E) (c : E) (k : ℕ) (q : QuartetTree X) : ℝ :=
  ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    if #(roots (top c)) = k then
      historyWeight Q θ 0 bot top *
        ∑ G, if Displays (unroot G) q then kingmanAbsorption (arrivingForest Q top Q.root) G else 0
    else 0

/-- `CF(Q | K = k)`: the concordance factor of `q` given that `k` lineages are at the top of `c`. -/
def condCF (Q : RootedNetwork V E X) (θ : MetricData E) (c : E) (k : ℕ) (q : QuartetTree X) : ℝ :=
  jointCF Q θ c k q / probLineages Q θ c k

end Banos2019
