module

public import Banos2019.Defs
public import Banos2019.Bridge.Statements
public import Banos2019.Bridge.Examples
public import Banos2019.Bridge.Generic
public import Banos2019.Bridge.Figures
public import Banos2019.Identifiability
public import Banos2019.Quartet.Examples

/-! # Baños 2019: the proofs of the statements of record

Restates each theorem of `Banos2019.Challenge` word for word, in the namespace `Banos2019Challenge`,
and proves it from the library, through the bridges of `Banos2019.Bridge` between the Challenge's
definitions and the library's. It is the entry point of the library. -/

public section

namespace Banos2019Challenge

open Finset Banos2019.Model

/-- **Theorem 3**: for generic numerical parameters, a set `s` of four taxa satisfies the Big Cycle
property if and only if the induced unrooted network `(N⁻)_s` has a 4-cycle. -/
theorem theorem3 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : Network V E X) (hN : N.IsBinaryNetwork) (h1 : N.graph.IsLevelOne) (s : Finset X)
    (hs : #s = 4) :
    N.ForGenericParams fun θ =>
      BigCycleOn (N.cf θ) s ↔ ∃ C, (N.unrooted.induced (s : Set X)).graph.IsCycle C ∧ C.ncard = 4 := by
  exact Banos2019.Model.theorem3 N hN h1 s hs

/-- **Theorem 4**: for generic numerical parameters, the collection of orderings of the quartet
concordance factors identifies `Ñ`: a property `G` of the parameters of each network holds for generic
parameters, and two binary level-1 networks on the same taxa, with parameters satisfying `G` and the same
orderings of concordance factors, have isomorphic networks `Ñ`. Both networks must satisfy `G`: a
network with a `3₂`-cycle (Figure 18) near the parameters of Example 6 and the network of Figure 17 at
the non-generic parameters of Example 7, with the taxa `1` and `2` exchanged, have the same orderings,
and their networks `Ñ` are not isomorphic (`fig17_fig18_tilde`). -/
theorem theorem4 {X : Type} [Fintype X] [DecidableEq X] :
    ∃ G : ∀ (V E : Type) [Fintype V] [Fintype E], Network V E X → Params E → Prop,
      (∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E X),
        N.IsBinaryNetwork → N.graph.IsLevelOne → N.ForGenericParams (G V E N)) ∧
      ∀ (V₁ E₁ V₂ E₂ : Type) [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
        (N₁ : Network V₁ E₁ X) (N₂ : Network V₂ E₂ X),
        N₁.IsBinaryNetwork → N₂.IsBinaryNetwork → N₁.graph.IsLevelOne → N₂.graph.IsLevelOne →
        ∀ θ₁ θ₂, N₁.IsMetric θ₁ → N₂.IsMetric θ₂ → G V₁ E₁ N₁ θ₁ → G V₂ E₂ N₂ θ₂ →
          SameOrdering (N₁.cf θ₁) (N₂.cf θ₂) → Nonempty (SDIso N₁.unrooted.tilde N₂.unrooted.tilde) := by
  exact Banos2019.Model.theorem4

/-- **Proposition 5**: two metric binary level-1 networks on four taxa, each rooted at the LSA of its
taxa, whose metric unrooted networks are isomorphic, have the same concordance factors. -/
theorem proposition5 {V E V' E' X : Type*} [Fintype V] [Fintype E] [Fintype V'] [Fintype E']
    [Fintype X] [DecidableEq X] (hX : Fintype.card X = 4) (Q : Network V E X) (θ : Params E)
    (Q' : Network V' E' X) (θ' : Params E') (hQ : Q.IsBinaryNetwork) (hQ' : Q'.IsBinaryNetwork)
    (h1 : Q.graph.IsLevelOne) (h1' : Q'.graph.IsLevelOne) (hr : Q.IsLSA Set.univ Q.root)
    (hr' : Q'.IsLSA Set.univ Q'.root) (hθ : Q.IsMetric θ) (hθ' : Q'.IsMetric θ')
    (hiso : Nonempty (SDMetricIso Q.unrooted (Q.unrootedParams θ) Q'.unrooted (Q'.unrootedParams θ'))) :
    Q.cf θ = Q'.cf θ' := by
  exact Banos2019.Model.proposition5 hX Q θ Q' θ' hQ hQ' h1 h1' hr hr' hθ hθ' hiso

/-- **Equation (1) on a quartet tree** (a check of the definitions): the balanced rooted quartet tree
`((0,1),(2,3))`, whose root `0` has the children `1` and `2`, with the leaves `3, 4` of the taxa `0, 1`
below `1` and the leaves `5, 6` of the taxa `2, 3` below `2`, with root edges of lengths `t₁`, `t₂` and
pendant edges of length one, is a binary metric network, and its concordance factors are
`1 - ⅔ e^{-(t₁+t₂)}` for the quartet tree `01|23` and `⅓ e^{-(t₁+t₂)}` for `02|13` and `03|12`. -/
theorem equation1_balanced (t₁ t₂ : ℝ) (h₁ : 0 < t₁) (h₂ : 0 < t₂) :
    let N : Network (Fin 7) (Fin 6) (Fin 4) := ⟨⟨![0, 0, 1, 1, 2, 2], ![1, 2, 3, 4, 5, 6]⟩, 0, ![3, 4, 5, 6]⟩
    let θ : Params (Fin 6) := ⟨![t₁, t₂, 1, 1, 1, 1], fun _ => 1⟩
    N.IsBinaryNetwork ∧ N.IsMetric θ ∧
      ∀ q : QuartetTree (Fin 4),
        (q.1 = {{0, 1}, {2, 3}} → N.cf θ q = 1 - 2 / 3 * Real.exp (-(t₁ + t₂))) ∧
        (q.1 = {{0, 2}, {1, 3}} → N.cf θ q = 1 / 3 * Real.exp (-(t₁ + t₂))) ∧
        (q.1 = {{0, 3}, {1, 2}} → N.cf θ q = 1 / 3 * Real.exp (-(t₁ + t₂))) := by
  exact Banos2019.Model.equation1_balanced t₁ t₂ h₁ h₂

/-- **The lowest stable ancestor exists** (a check of the definitions): in a binary rooted network,
`lsa` is the LSA of all the taxa (Definition 4). -/
theorem lsa_isLSA {V E X : Type*} (N : Network V E X) (hN : N.IsBinaryNetwork) :
    N.IsLSA Set.univ N.lsa := by
  exact Banos2019.Model.lsa_isLSA N hN

/-- **The root reaches every node** of a binary rooted network (a check of the definitions):
Definition 1's connectedness follows from its other clauses. -/
theorem root_reaches {V E X : Type*} (N : Network V E X) (hN : N.IsBinaryNetwork) (v : V) :
    N.graph.Reaches N.root v := by
  exact Banos2019.Model.root_reaches N hN v

/-- **"For generic parameters" is not vacuous** (a check of the definitions): the metric parameters
of a binary rooted network do not form a null set, so no binary network satisfies a false property for
generic parameters. -/
theorem not_forGenericParams_false {V E X : Type*} [Fintype E] (N : Network V E X)
    (hN : N.IsBinaryNetwork) : ¬ N.ForGenericParams fun _ => False := by
  exact N.not_forGenericParams_false hN

/-- **Example 6** (a check of the definitions): the network of Figure 18, with a `3₂`-cycle, with the
parameters of the paper: `t₁ = t₂ = -log(6/7)`, `t₃ = -log(1/14)`, `t₄ = -log(13/14)`, `γ = 1/2`. It is
a binary level-1 metric network rooted at the LSA of its taxa, its concordance factors are `32/98` for
`01|23` and `33/98` for `02|13` and `03|12`, and its four taxa do not satisfy the Big Cycle property. -/
theorem example6 :
    let θ := fig18Params (-Real.log (6 / 7)) (-Real.log (6 / 7)) (-Real.log (1 / 14))
      (-Real.log (13 / 14)) (1 / 2)
    fig18Network.IsBinaryNetwork ∧ fig18Network.graph.IsLevelOne ∧
      fig18Network.IsLSA Set.univ fig18Network.root ∧ fig18Network.IsMetric θ ∧
      (∀ q : QuartetTree (Fin 4),
        (q.1 = {{0, 1}, {2, 3}} → fig18Network.cf θ q = 32 / 98) ∧
        (q.1 = {{0, 2}, {1, 3}} → fig18Network.cf θ q = 33 / 98) ∧
        (q.1 = {{0, 3}, {1, 2}} → fig18Network.cf θ q = 33 / 98)) ∧
      ¬ BigCycleOn (fig18Network.cf θ) univ := by
  exact Banos2019.Model.example6_fig18

/-- **Example 7** (a check of the definitions): the network of Figure 17, with a 4-cycle, with
`t₁ = t₂ = -log(48/49)` and `γ = 1/2`, as in the paper, which gives no lengths for the hybrid edges: they
have length one here, and do not change the concordance factors, since at most one lineage crosses them.
It is a binary level-1 metric network rooted at the LSA of its taxa, and its concordance factors are
`33/98` for `01|23` and `03|12` and `32/98` for `02|13`. The paper prints `32/98` for `AB|CD` and `33/98`
for `AC|BD` and `AD|BC`: those are the values with the taxa `1` and `2` exchanged. -/
theorem example7 :
    let θ := fig17Params (-Real.log (48 / 49)) (-Real.log (48 / 49)) (1 / 2)
    fig17Network.IsBinaryNetwork ∧ fig17Network.graph.IsLevelOne ∧
      fig17Network.IsLSA Set.univ fig17Network.root ∧ fig17Network.IsMetric θ ∧
      ∀ q : QuartetTree (Fin 4),
        (q.1 = {{0, 1}, {2, 3}} → fig17Network.cf θ q = 33 / 98) ∧
        (q.1 = {{0, 2}, {1, 3}} → fig17Network.cf θ q = 32 / 98) ∧
        (q.1 = {{0, 3}, {1, 2}} → fig17Network.cf θ q = 33 / 98) := by
  exact Banos2019.Model.example7_fig17

/-- **`N⁻` keeps the cycles of size at least four** (a check of the definitions): `N⁻` of Figure 17 has
a 4-cycle, and `N⁻` of Figure 18 has none, its cycle of four edges passing through the root. -/
theorem fig17_fig18_unrooted :
    (∃ C, fig17Network.unrooted.graph.IsCycle C ∧ C.ncard = 4) ∧
      ¬ ∃ C, fig18Network.unrooted.graph.IsCycle C ∧ C.ncard = 4 := by
  exact Banos2019.Model.fig17_fig18_unrooted

/-- **`Ñ` distinguishes a 4-cycle from a `3₂`-cycle** (a check of the definitions): the networks `Ñ` of
Figures 18 and 17 are not isomorphic. `Ñ` of Figure 18, whose 3-cycle is contracted, has no cycle; `Ñ`
of Figure 17 keeps the 4-cycle. -/
theorem fig17_fig18_tilde :
    ¬ Nonempty (SDIso fig18Network.unrooted.tilde fig17Network.unrooted.tilde) := by
  exact Banos2019.Model.fig17_fig18_tilde

end Banos2019Challenge

end
