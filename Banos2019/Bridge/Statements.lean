module

public import Banos2019.Bridge.Quartet
public import Banos2019.Identifiability

/-!
# The statements of record, on the Challenge's definitions

`Banos2019.Model.theorem3`, `theorem4`, `proposition5` are the theorems of the Challenge
(`palomar/Banos2019/Challenge.lean`), stated on the definitions of `Banos2019.Defs` and proved from the
library's `Banos2019.theorem3`, `Banos2019.theorem4`, `Banos2019.proposition5` through the bridges of
`Banos2019.Bridge`. The Solution restates them.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace Banos2019.Model

/-- **Theorem 3**, on the Challenge's definitions. -/
theorem theorem3 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : Network V E X) (hN : N.IsBinaryNetwork) (h1 : N.graph.IsLevelOne) (s : Finset X)
    (hs : #s = 4) :
    N.ForGenericParams fun θ =>
      BigCycleOn (N.cf θ) s ↔ ∃ C, (N.unrooted.induced (s : Set X)).graph.IsCycle C ∧ C.ncard = 4 := by
  have hb := N.isBinaryNetwork_iff.mp hN
  obtain rfl : ‹DecidableEq X› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  classical
  refine N.forGenericParams_of hN (fun θ hθ h => ?_)
    (Banos2019.theorem3 hb ((N.graph.isLevelOne_iff).mp h1) hs)
  rw [N.cf_eq, bigCycleOn_iff, h ((N.isMetric_iff hN θ).mp hθ),
    N.exists_fourCycle_induced_iff hN h1 hθ s hs]

/-- **Theorem 4**, on the Challenge's definitions: the property `G` of the parameters is the library's,
read on the same data. -/
theorem theorem4 {X : Type} [Fintype X] [DecidableEq X] [Nontrivial X] :
    ∃ G : ∀ (V E : Type) [Fintype V] [Fintype E], Network V E X → Params E → Prop,
      (∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E X),
        N.IsBinaryNetwork → N.graph.IsLevelOne → N.ForGenericParams (G V E N)) ∧
      ∀ (V₁ E₁ V₂ E₂ : Type) [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
        (N₁ : Network V₁ E₁ X) (N₂ : Network V₂ E₂ X),
        N₁.IsBinaryNetwork → N₂.IsBinaryNetwork → N₁.graph.IsLevelOne → N₂.graph.IsLevelOne →
        ∀ θ₁ θ₂, N₁.IsMetric θ₁ → N₂.IsMetric θ₂ → G V₁ E₁ N₁ θ₁ → G V₂ E₂ N₂ θ₂ →
          SameOrdering (N₁.cf θ₁) (N₂.cf θ₂) → Nonempty (SDIso N₁.unrooted.tilde N₂.unrooted.tilde) := by
  obtain ⟨G, hgen, hid⟩ := Banos2019.theorem4 (X := X) inferInstance
  refine ⟨fun V E _ _ N θ => G V E N.toRooted θ.toMetric, fun V E _ _ N hN h1 => ?_, ?_⟩
  · exact N.forGenericParams_of hN (fun θ _ h => h) (hgen V E N.toRooted (N.isBinaryNetwork_iff.mp hN)
      ((N.graph.isLevelOne_iff).mp h1))
  · intro V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hso
    have hb₁ := N₁.isBinaryNetwork_iff.mp hN₁
    have hb₂ := N₂.isBinaryNetwork_iff.mp hN₂
    rw [N₁.cf_eq, N₂.cf_eq, sameOrdering_iff] at hso
    obtain ⟨ι⟩ := hid V₁ E₁ V₂ E₂ N₁.toRooted N₂.toRooted hb₁ hb₂ ((N₁.graph.isLevelOne_iff).mp h1₁)
      ((N₂.graph.isLevelOne_iff).mp h1₂) θ₁.toMetric θ₂.toMetric ((N₁.isMetric_iff hN₁ θ₁).mp hθ₁)
      ((N₂.isMetric_iff hN₂ θ₂).mp hθ₂) hG₁ hG₂ hso
    obtain ⟨u₁⟩ := N₁.nonempty_sdIso_unrooted hb₁
    obtain ⟨u₂⟩ := N₂.nonempty_sdIso_unrooted hb₂
    exact ⟨SDIso.ofLib ((N₁.unrooted.tildeIso.trans u₁.tildeNetwork).trans
      (ι.trans (N₂.unrooted.tildeIso.trans u₂.tildeNetwork).symm))⟩

/-- **Proposition 5**, on the Challenge's definitions. -/
theorem proposition5 {V E V' E' X : Type*} [Fintype V] [Fintype E] [Fintype V'] [Fintype E']
    [Fintype X] [DecidableEq X] (hX : Fintype.card X = 4) (Q : Network V E X) (θ : Params E)
    (Q' : Network V' E' X) (θ' : Params E') (hQ : Q.IsBinaryNetwork) (hQ' : Q'.IsBinaryNetwork)
    (h1 : Q.graph.IsLevelOne) (h1' : Q'.graph.IsLevelOne) (hr : Q.IsLSA Set.univ Q.root)
    (hr' : Q'.IsLSA Set.univ Q'.root) (hθ : Q.IsMetric θ) (hθ' : Q'.IsMetric θ')
    (hiso : Nonempty (SDMetricIso Q.unrooted (Q.unrootedParams θ) Q'.unrooted (Q'.unrootedParams θ'))) :
    Q.cf θ = Q'.cf θ' := by
  have hL : IsLSAQuartet Q.toRooted θ.toMetric :=
    ⟨Q.isBinaryNetwork_iff.mp hQ, (Q.graph.isLevelOne_iff).mp h1, hr, hX, (Q.isMetric_iff hQ θ).mp hθ⟩
  have hL' : IsLSAQuartet Q'.toRooted θ'.toMetric :=
    ⟨Q'.isBinaryNetwork_iff.mp hQ', (Q'.graph.isLevelOne_iff).mp h1', hr', hX,
      (Q'.isMetric_iff hQ' θ').mp hθ'⟩
  have : Nontrivial X := hL.nontrivial
  obtain ⟨ι⟩ := hiso
  obtain ⟨u⟩ := Q.nonempty_sdMetricIso_unrooted hL.binary θ
  obtain ⟨u'⟩ := Q'.nonempty_sdMetricIso_unrooted hL'.binary θ'
  have key := Banos2019.proposition5 hL hL' ⟨u.symm.trans (ι.toLib.trans u')⟩
  obtain rfl : ‹DecidableEq X› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  classical
  rw [Q.cf_eq, Q'.cf_eq, key]

end Banos2019.Model
