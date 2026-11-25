module

public import Banos2019.Bridge.Quartet
public import Banos2019.Identifiability

/-!
# The statements of record, on the Challenge's definitions

`Banos2019.Model.theorem3`, `theorem4`, `proposition5` are the theorems of the Challenge
(`palomar/Banos2019/Challenge.lean`), stated on the definitions of `Banos2019.Defs` and proved from the
library's `Banos2019.theorem3`, `Banos2019.theorem4`, `Banos2019.proposition5` through the bridges of
`Banos2019.Bridge`. The library's Theorem 4 assumes two taxa; with at most one, `theorem4` holds
because `Ñ` is then the leaf of the taxon alone (`Network.isPoint_unrooted`). `lsa_isLSA` and
`root_reaches` are two of the Challenge's checks of its definitions; the others are in
`Banos2019.Bridge.Examples`, `Banos2019.Bridge.Generic` and `Banos2019.Bridge.Figures`. The Solution
restates them.
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

/-- **Theorem 4** for at least two taxa, on the Challenge's definitions: the property `G` of the
parameters is the library's, read on the same data. -/
theorem theorem4_of_nontrivial {X : Type} [Fintype X] [DecidableEq X] [Nontrivial X] :
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

/-! ### Theorem 4 with at most one taxon

A binary network has a taxon (going down from the root ends at a leaf). With one taxon, the LSA of the
taxa is its leaf, below which there is nothing: `N⁻`, and then `Ñ`, is the leaf alone, without edges, so
any two of them are isomorphic. -/

section Point

variable {V E X : Type*}

/-- A semidirected network that is its leaves alone: no edges, every node a leaf. -/
def SDNetwork.IsPoint (G : SDNetwork V E X) : Prop := IsEmpty E ∧ ∀ v, ∃ x, G.leaf x = v

theorem SDNetwork.IsPoint.suppressExcept {G : SDNetwork V E X} (h : G.IsPoint) (P : Set V) :
    (G.suppressExcept P).IsPoint := by
  refine ⟨⟨fun c => ?_⟩, fun v => ?_⟩
  · obtain ⟨k, p, e, hc, -⟩ := c.2
    exact h.1.false (e ⟨0, hc.pos⟩)
  · obtain ⟨x, hx⟩ := h.2 v.1
    exact ⟨x, Subtype.ext hx⟩

theorem SDNetwork.IsPoint.tilde {G : SDNetwork V E X} (h : G.IsPoint) : G.tilde.IsPoint := by
  rw [SDNetwork.tilde_eq]
  refine SDNetwork.IsPoint.suppressExcept ⟨⟨fun e => h.1.false e.1⟩, fun v => ?_⟩ ∅
  induction v using Quot.ind with
  | mk v =>
    obtain ⟨x, hx⟩ := h.2 v
    exact ⟨x, by rw [← hx]; rfl⟩

/-- Two semidirected networks that are a single leaf are isomorphic. -/
def SDIso.ofIsPoint [Subsingleton X] (x₀ : X) {V' E' : Type*} {G : SDNetwork V E X}
    {G' : SDNetwork V' E' X} (h : G.IsPoint) (h' : G'.IsPoint) : SDIso G G' where
  vert :=
    { toFun := fun _ => G'.leaf x₀
      invFun := fun _ => G.leaf x₀
      left_inv := fun v => by
        obtain ⟨x, rfl⟩ := h.2 v
        rw [Subsingleton.elim x x₀]
      right_inv := fun v => by
        obtain ⟨x, rfl⟩ := h'.2 v
        rw [Subsingleton.elim x x₀] }
  edge := @Equiv.equivOfIsEmpty _ _ h.1 h'.1
  isDirected_iff e := (h.1.false e).elim
  joins e := (h.1.false e).elim
  directed e := (h.1.false e).elim
  leaf x := by
    rw [Subsingleton.elim x x₀]
    rfl

/-- In a binary network, a leaf reaches only itself. -/
theorem Network.eq_of_reaches_leaf {N : Network V E X} (hN : N.IsBinaryNetwork) {x : X} {v : V}
    (h : N.graph.Reaches (N.leaf x) v) : v = N.leaf x := by
  have hb := N.isBinaryNetwork_iff.mp hN
  have := hb.1.finite_arcs
  rcases Relation.ReflTransGen.cases_head h with h | ⟨w, ⟨e, he, -⟩, -⟩
  · exact h.symm
  · have h0 : N.graph.outdegree (N.leaf x) = 0 := (hN.2.2.2.2.2.2.1 x).2
    unfold Digraph.outdegree at h0
    rw [Set.ncard_eq_zero (Set.toFinite _)] at h0
    exact absurd (show e ∈ {e | N.graph.source e = N.leaf x} from he) (by rw [h0]; exact id)

/-- **With one taxon, `N⁻` is its leaf alone.** -/
theorem Network.isPoint_unrooted [Subsingleton X] {N : Network V E X} (hN : N.IsBinaryNetwork)
    (x₀ : X) : N.unrooted.IsPoint := by
  have : Nonempty X := ⟨x₀⟩
  -- the LSA of the taxa is the leaf
  have hl : N.lsa = N.leaf x₀ := by
    have hst : ∀ z ∈ (Set.univ : Set X), N.OnEveryRootPath (N.leaf z) (N.leaf x₀) := fun z _ => by
      rw [Subsingleton.elim z x₀]
      exact fun h => h.2.1 rfl
    exact N.eq_of_reaches_leaf hN ((N.isLSA_lsa hN).2 _ hst)
  refine SDNetwork.IsPoint.suppressExcept ⟨⟨fun e => ?_⟩, fun v => ?_⟩ ∅
  · have h : N.graph.Reaches (N.leaf x₀) (N.graph.source e.1) := hl ▸ e.2
    have hs := N.eq_of_reaches_leaf hN h
    have h0 : N.graph.outdegree (N.leaf x₀) = 0 := (hN.2.2.2.2.2.2.1 x₀).2
    have := (N.isBinaryNetwork_iff.mp hN).1.finite_arcs
    unfold Digraph.outdegree at h0
    rw [Set.ncard_eq_zero (Set.toFinite _)] at h0
    exact absurd (show e.1 ∈ {e | N.graph.source e = N.leaf x₀} from hs) (by rw [h0]; exact id)
  · rcases v.2 with h | ⟨x, hx⟩
    · exact ⟨x₀, Subtype.ext (N.eq_of_reaches_leaf hN (hl ▸ h)).symm⟩
    · exact ⟨x, Subtype.ext hx⟩

end Point

/-- **Theorem 4**, on the Challenge's definitions. With at least two taxa, it is the library's
(`theorem4_of_nontrivial`). A binary network has a taxon, and with one taxon any two networks `Ñ` are
the leaf alone, so isomorphic: `G` is then any property, here the true one. -/
theorem theorem4 {X : Type} [Fintype X] [DecidableEq X] :
    ∃ G : ∀ (V E : Type) [Fintype V] [Fintype E], Network V E X → Params E → Prop,
      (∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E X),
        N.IsBinaryNetwork → N.graph.IsLevelOne → N.ForGenericParams (G V E N)) ∧
      ∀ (V₁ E₁ V₂ E₂ : Type) [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
        (N₁ : Network V₁ E₁ X) (N₂ : Network V₂ E₂ X),
        N₁.IsBinaryNetwork → N₂.IsBinaryNetwork → N₁.graph.IsLevelOne → N₂.graph.IsLevelOne →
        ∀ θ₁ θ₂, N₁.IsMetric θ₁ → N₂.IsMetric θ₂ → G V₁ E₁ N₁ θ₁ → G V₂ E₂ N₂ θ₂ →
          SameOrdering (N₁.cf θ₁) (N₂.cf θ₂) → Nonempty (SDIso N₁.unrooted.tilde N₂.unrooted.tilde) := by
  by_cases hX : Nontrivial X
  · exact theorem4_of_nontrivial
  rw [not_nontrivial_iff_subsingleton] at hX
  refine ⟨fun _ _ _ _ _ _ => True, fun V E _ _ N _ _ => ?_, ?_⟩
  · intro d _
    refine MeasureTheory.measure_mono_null (fun x hx => ?_) MeasureTheory.measure_empty
    obtain ⟨θ, ⟨-, h⟩, -⟩ := hx
    exact (h trivial).elim
  · intro V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ _ _ _ _ _ _ _ _ _
    obtain ⟨x₀, -⟩ := exists_reaches_leaf (N₁.isBinaryNetwork_iff.mp hN₁).1 N₁.root
    exact ⟨SDIso.ofIsPoint x₀ (N₁.isPoint_unrooted hN₁ x₀).tilde (N₂.isPoint_unrooted hN₂ x₀).tilde⟩

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

/-- **The LSA exists**: in a binary rooted network, `lsa` is the lowest stable ancestor of the taxa
(Definition 4). A binary network has taxa: going down from the root ends at a leaf. -/
theorem lsa_isLSA {V E X : Type*} (N : Network V E X) (hN : N.IsBinaryNetwork) :
    N.IsLSA Set.univ N.lsa := by
  have hb := N.isBinaryNetwork_iff.mp hN
  have : Nonempty X := ⟨(exists_reaches_leaf hb.1 N.root).choose⟩
  exact N.isLSA_lsa hN

/-- **The root reaches every node** of a binary rooted network (Definition 1 asks for a connected
graph; the clauses give more). -/
theorem root_reaches {V E X : Type*} (N : Network V E X) (hN : N.IsBinaryNetwork) (v : V) :
    N.graph.Reaches N.root v :=
  (N.isBinaryNetwork_iff.mp hN).1.root_reaches v

end Banos2019.Model
