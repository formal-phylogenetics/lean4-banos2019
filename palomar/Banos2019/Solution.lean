module

public import Banos2019.Defs
public import Banos2019.Bridge.Statements
public import Banos2019.Bridge.Examples
public import Banos2019.Identifiability
public import Banos2019.Quartet.Examples

/-! # Baños 2019: the proofs of the statements of record

Restates each theorem of `Banos2019.Challenge` word for word, in the namespace `Banos2019Challenge`,
and proves it from the library, through the bridges of `Banos2019.Bridge` between the Challenge's
definitions and the library's. It is the entry point of the library. -/

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

end Banos2019Challenge
