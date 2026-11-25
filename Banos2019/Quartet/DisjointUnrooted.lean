module

public import Banos2019.Quartet.DisjointNet
public import Banos2019.Quartet.SemidirectedCycles
public import Banos2019.Network.SuppressMetric

/-!
# The unrooted network of `Q_a⊕`

For a hybrid node `w` of a semidirected network `G` with hybrid edges `h₁`, `h₂`, `cutSD G w h₁ h₂ a b`
is `G` without the nodes joined to `w` by paths avoiding `h₁` and `h₂` (`CutReach`), with `h₁` and `h₂`
ending at two new leaves labelled `a` and `b`, as tree edges. An isomorphism of semidirected networks
maps it to the network cut at the images (`SDMetricIso.cutSD`).

For a binary level-1 network `Q` whose root is the LSA of its taxa, the nodes of `Q⁻` joined to a
hybrid node `w` avoiding its hybrid edges are those below `w` in `Q`, and the unrooted network of
`Q_a⊕ = disjointNet Q w h₁ h₂ a b` is `cutSD Q⁻ w h₁ h₂ a b` (`nonempty_sdMetricIso_disjointNet_cutSD`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace Banos2019

variable {V E X V' E' : Type*}

/-- The nodes joined to `w` by a path of the undirected graph avoiding the edges `h₁` and `h₂`. -/
def CutReach (G : SemidirectedNetwork V E X) (h₁ h₂ : E) (w : V) : V → Prop :=
  Relation.ReflTransGen (fun u u' => ∃ g, g ≠ h₁ ∧ g ≠ h₂ ∧ Joins G.graph g u u') w

/-- **`G` cut below `w`**: without the nodes joined to `w` avoiding `h₁` and `h₂`, the edges `h₁` and
`h₂` ending at two new leaves, labelled `a` and `b`, as tree edges. -/
def cutSD (G : SemidirectedNetwork V E X) (w : V) (h₁ h₂ : E) (a b : X) :
    SemidirectedNetwork ({u // ¬ CutReach G h₁ h₂ w u} ⊕ Fin 2)
      {g // ¬ CutReach G h₁ h₂ w (G.graph.source g)} X where
  graph :=
    { source := fun g => .inl ⟨G.graph.source g.1, g.2⟩
      target := fun g => if g.1 = h₁ then .inr 0 else if g.1 = h₂ then .inr 1 else
        if hr : CutReach G h₁ h₂ w (G.graph.target g.1) then .inr 0 else .inl ⟨_, hr⟩ }
  IsDirected g := G.IsDirected g.1 ∧ g.1 ≠ h₁ ∧ g.1 ≠ h₂
  leaf x := if x = a then .inr 0 else if x = b then .inr 1 else
    if hr : CutReach G h₁ h₂ w (G.leaf x) then .inr 0 else .inl ⟨_, hr⟩

/-- **An isomorphism maps `G` cut below `w` to `G'` cut below the image of `w`.** -/
theorem SDMetricIso.nonempty_cutSD {G : SemidirectedNetwork V E X} {θ : MetricData E}
    {G' : SemidirectedNetwork V' E' X} {θ' : MetricData E'} (ι : SDMetricIso G θ G' θ') (w : V)
    (h₁ h₂ : E) (a b : X) :
    Nonempty (SDMetricIso (cutSD G w h₁ h₂ a b) (restrictMetric θ _)
      (cutSD G' (ι.vert w) (ι.edge h₁) (ι.edge h₂) a b) (restrictMetric θ' _)) := by
  sorry

/-- **The unrooted network of `Q_a⊕` is `Q⁻` cut below the hybrid node.** -/
theorem nonempty_sdMetricIso_disjointNet_cutSD {Q : RootedNetwork V E X}
    (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph) (hX : Nontrivial X)
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root) (θ : MetricData E)
    {w : SemidirectedVertex hQ.1 hX} {h₁ h₂ : SemidirectedArc hQ.1 hQ.2 hX} (hne : h₁ ≠ h₂)
    (hd₁ : (semidirected hQ.1 hQ.2 hX).IsDirected h₁)
    (hd₂ : (semidirected hQ.1 hQ.2 hX).IsDirected h₂)
    (ht₁ : (semidirected hQ.1 hQ.2 hX).graph.target h₁ = w)
    (ht₂ : (semidirected hQ.1 hQ.2 hX).graph.target h₂ = w) {a b : X} (hab : a ≠ b)
    (hb : IsBinaryRootedNetwork (disjointNet Q (sdVert hQ.1 hX w) (sdArc hQ.1 hQ.2 hX h₁)
      (sdArc hQ.1 hQ.2 hX h₂) a b))
    (hl : (disjointNet Q (sdVert hQ.1 hX w) (sdArc hQ.1 hQ.2 hX h₁)
      (sdArc hQ.1 hQ.2 hX h₂) a b).IsLSANetwork) :
    Nonempty (SDMetricIso (unrooted _ hb hX)
      (unrootedMetric _ hb hX (disjointMetric Q (sdVert hQ.1 hX w) (sdArc hQ.1 hQ.2 hX h₁)
        (sdArc hQ.1 hQ.2 hX h₂) θ))
      (cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b)
      (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _)) := by
  sorry

end Banos2019
