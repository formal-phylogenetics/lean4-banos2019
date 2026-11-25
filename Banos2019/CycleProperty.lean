module

public import Banos2019.Quartet.Correspondence
public import Banos2019.Quartet.Fig18
public import Banos2019.Quartet.Remove
public import Banos2019.Quartet.Generic

/-!
# The Cycle property and the Big Cycle property (Baños 2019, Sections 6 and 7)

* `proposition6`, `proposition7`, `proposition8`: the ordering of the concordance factors of an LSA
  quartet network without a `3₂`-cycle is that of the network with its 2-cycles and `3₁`-cycles
  contracted; a `3₂`-cycle gives concordance factors on three segments; the Cycle property detects a
  `3₂`-cycle or a 4-cycle.
* `proposition9`, `proposition10`, `theorem3`, `corollary4`, `proposition11`, `lemma12`, `lemma13`:
  the Big Cycle property detects 4-cycles, for generic parameters, and the quartet with the smallest
  concordance factor tells which blocks of the 4-cycle are adjacent.

The inductions of the proofs of Propositions 6 and 7 are `orderedAsQuartetTree_of_onlyTwoTwoThreeOne`
and `onSegmentOfI_of_threeTwo`; `cf_eq_fig17` is the reduction of the proofs of Propositions 10 and 11
to equation (8), and `hasFourCycle_of_bigCycleOn` the direction of Theorem 3 that holds for all
parameters.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

/-! ### Section 6 -/

/-- The cycles of `Q⊕` that induce 2-cycles or `3₁`-cycles. -/
def IsTwoOrThreeOne (Q : RootedNetwork V E X) (C : Set E) : Prop :=
  ∃ v, (∃ k, InducesCycleType Q C v 2 k) ∨ InducesCycleType Q C v 3 1

omit [Fintype V] [Fintype X] in
/-- The two hybrid edges of the hybrid node of a cycle. -/
theorem exists_hybrid_edges {Q : RootedNetwork V E X} {C : Set E} {v : V} {n k : ℕ}
    (hC : InducesCycleType Q C v n k) :
    ∃ h₁ h₂, h₁ ≠ h₂ ∧ Q.graph.target h₁ = v ∧ Q.graph.target h₂ = v ∧ Q.IsHybridArc h₁ := by
  have h2 := hC.2.2.1
  rw [indegree_eq_card_filter_target] at h2
  obtain ⟨h₁, h₂, hne, he⟩ := Finset.card_eq_two.1 h2
  have m₁ : h₁ ∈ univ.filter fun e => Q.graph.target e = v := he ▸ mem_insert_self _ _
  have m₂ : h₂ ∈ univ.filter fun e => Q.graph.target e = v :=
    he ▸ mem_insert_of_mem (mem_singleton_self _)
  have t₁ := (mem_filter.1 m₁).2
  refine ⟨h₁, h₂, hne, t₁, (mem_filter.1 m₂).2, ?_⟩
  unfold IsHybridArc
  rw [t₁, hC.2.2.1]

/-- The cycles of `Q⊕` in the induction of the proof of Proposition 6: no `3₂`-cycle, no 4-cycle,
and, after Corollary 2, no `2₁`- or `2₃`-cycle. -/
def OnlyTwoTwoThreeOne (Q : RootedNetwork V E X) : Prop :=
  (¬ ∃ C v, InducesCycleType Q C v 3 2) ∧ (¬ ∃ C v k, InducesCycleType Q C v 4 k) ∧
    (¬ ∃ C v, InducesCycleType Q C v 2 1) ∧ ¬ ∃ C v, InducesCycleType Q C v 2 3

omit [Fintype V] [Fintype E] [Fintype X] in
theorem SameCyclesBut.onlyTwoTwoThreeOne {V' E' : Type*} {Q' : RootedNetwork V' E' X}
    {Q : RootedNetwork V E X} {P : Set E → Prop} (h : SameCyclesBut Q' Q P)
    (hK : OnlyTwoTwoThreeOne Q) : OnlyTwoTwoThreeOne Q' :=
  ⟨h.not_exists hK.1, fun ⟨C, v, k, hC⟩ => h.not_exists (fun ⟨C', v', h'⟩ => hK.2.1 ⟨C', v', k, h'⟩)
    ⟨C, v, hC⟩, h.not_exists hK.2.2.1, h.not_exists hK.2.2.2⟩

/-- **The induction of the proof of Proposition 6**: if `Q⁻` has only `2₂`- and `3₁`-cycles, its
concordance factors are ordered as the quartet tree of any of its cut edges between two pairs of taxa.
With no cycle, `Q` is a tree (equation (1)); otherwise Lemmas 9 and 10 write the concordance factors
of `Q` as a convex combination of those of networks with one cycle fewer and the same cut edges. -/
theorem orderedAsQuartetTree_of_onlyTwoTwoThreeOne (n : ℕ) :
    ∀ {V' E' : Type} [Fintype V'] [Fintype E'] {Q : RootedNetwork V' E' X} {θ : MetricData E'},
      IsLSAQuartet Q θ → numRootedCycles Q = n → OnlyTwoTwoThreeOne Q →
      ∀ A : Finset X, #A = 2 → Q.HasCutSplit ↑A → OrderedAsQuartetTree (cf Q θ) A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V' E' _ _ Q θ hQ hn hK A hA hcut
  by_cases h0 : numRootedCycles Q = 0
  · -- no cycle: by Corollary 2, which contracts nothing, `Q` is the tree `Q'`; equation (1)
    have hnone : ∀ C, ¬ IsCycle Q.graph C := fun C hC => by
      have := Set.ncard_eq_zero (s := {C | IsCycle Q.graph C}) (finite_setOf_isCycle _)
      exact (this.1 h0 ▸ hC : C ∈ (∅ : Set (Set E')))
    have hP : IsTwoOneOrThree Q =
        fun C => ∃ v, (∃ k, InducesCycleType Q C v 2 k) ∨ InducesCycleType Q C v 3 1 := by
      funext C
      apply propext
      constructor
      · rintro ⟨v, h | h⟩ <;> exact absurd h.1 (hnone C)
      · rintro ⟨v, ⟨k, h⟩ | h⟩ <;> exact absurd h.1 (hnone C)
    obtain ⟨σ, -, hσcut, hcf⟩ := exists_speciesTree_contractRooted hQ hK.1 hK.2.1 _ hP
    rw [corollary2 hQ, hcf]
    exact orderedAsQuartetTree_quartetProb hQ.card_taxa σ hA ((hσcut A hA).1 hcut)
  · -- a cycle, which is a `2₂`- or a `3₁`-cycle
    obtain ⟨C, hC⟩ := Set.nonempty_of_ncard_ne_zero h0
    obtain ⟨v, m, k, hCt⟩ := exists_inducesCycleType_of_isCycle hQ hC
    obtain ⟨h₁, h₂, hne, hh₁, hh₂, hyb⟩ := exists_hybrid_edges hCt
    obtain ⟨hγ₀, hγ₁⟩ := inheritance_mem_Ioo hQ.binary hQ.metric hyb
    rcases inducesCycleType_cases hQ hCt with ⟨rfl, hk₁, hk₃⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩
    · have hk : k = 2 := by
        rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
        · exact absurd ⟨C, v, hCt⟩ hK.2.2.1
        · rfl
        · exact absurd ⟨C, v, hCt⟩ hK.2.2.2
      subst hk
      -- Lemma 9, and the three networks with one cycle fewer
      obtain ⟨V₁, E₁, _, _, Q₁, θ₁, hQ₁, hcf₁, hlt₁, hs₁, hc₁⟩ :=
        exists_lsaQuartet_deleteArc hQ (Or.inl hCt) hh₂
      obtain ⟨V₂, E₂, _, _, Q₂, θ₂, hQ₂, hcf₂, hlt₂, hs₂, hc₂⟩ :=
        exists_lsaQuartet_deleteArc hQ (Or.inl hCt) hh₁
      obtain ⟨V₀, E₀, _, _, Q₀, θ₀, hQ₀, hcf₀, hlt₀, hs₀, hc₀⟩ :=
        exists_lsaQuartet_contractRooted hQ hCt
      have t₁ := ih _ (hn ▸ hlt₁) hQ₁ rfl (hs₁.onlyTwoTwoThreeOne hK) A hA ((hc₁ A hA).2 hcut)
      have t₂ := ih _ (hn ▸ hlt₂) hQ₂ rfl (hs₂.onlyTwoTwoThreeOne hK) A hA ((hc₂ A hA).2 hcut)
      have t₀ := ih _ (hn ▸ hlt₀) hQ₀ rfl (hs₀.onlyTwoTwoThreeOne hK) A hA ((hc₀ A hA).2 hcut)
      have hcfQ : cf Q θ = fun q => θ.inheritance h₁ ^ 2 * cf Q₁ θ₁ q +
          (1 - θ.inheritance h₁) ^ 2 * cf Q₂ θ₂ q +
          2 * θ.inheritance h₁ * (1 - θ.inheritance h₁) * cf Q₀ θ₀ q := by
        funext q
        rw [lemma9 hQ hCt hne hh₁ hh₂ q, hcf₁, hcf₂, hcf₀]
      rw [hcfQ]
      exact OrderedAsQuartetTree.add₃ t₁ t₂ t₀ (by positivity) (pow_pos (by linarith) 2)
        (by have : 0 < 1 - θ.inheritance h₁ := by linarith
            positivity)
    · have hk1 : k = 1 := by
        rcases hk with rfl | rfl
        · rfl
        · exact absurd ⟨C, v, hCt⟩ hK.1
      subst hk1
      -- Lemma 10, and the two networks with one cycle fewer
      obtain ⟨V₁, E₁, _, _, Q₁, θ₁, hQ₁, hcf₁, hlt₁, hs₁, hc₁⟩ :=
        exists_lsaQuartet_deleteArc hQ (Or.inr hCt) hh₂
      obtain ⟨V₂, E₂, _, _, Q₂, θ₂, hQ₂, hcf₂, hlt₂, hs₂, hc₂⟩ :=
        exists_lsaQuartet_deleteArc hQ (Or.inr hCt) hh₁
      have t₁ := ih _ (hn ▸ hlt₁) hQ₁ rfl (hs₁.onlyTwoTwoThreeOne hK) A hA ((hc₁ A hA).2 hcut)
      have t₂ := ih _ (hn ▸ hlt₂) hQ₂ rfl (hs₂.onlyTwoTwoThreeOne hK) A hA ((hc₂ A hA).2 hcut)
      have hcfQ : cf Q θ = fun q => θ.inheritance h₁ * cf Q₁ θ₁ q +
          (1 - θ.inheritance h₁) * cf Q₂ θ₂ q := by
        funext q
        rw [lemma10 hQ (Or.inr hCt) hne hh₁ hh₂ q, hcf₁, hcf₂]
      rw [hcfQ]
      exact OrderedAsQuartetTree.add t₁ t₂ hγ₀ (by linarith)
    · exact absurd ⟨C, v, 1, hCt⟩ hK.2.1

/-- **Proposition 6** (`prop:Cfspreserv`): if `Q⁻` has no `3₂`-cycle, the ordering of `CF(Q)` is that of
`CF(Q')`, where `Q'` is obtained by contracting all 2-cycles and all `3₁`-cycles. -/
theorem proposition6 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    (h32 : ¬ ∃ C v, InducesCycleType Q C v 3 2) :
    SameOrdering (cf Q θ)
      (cf (contractRooted Q (IsTwoOrThreeOne Q)) (contractMetric Q (IsTwoOrThreeOne Q) θ)) := by
  -- Corollary 2: `CF(Q) = CF(Q*)`, `Q*` without the `2₁`- and `2₃`-cycles
  have hc2 := corollary2 hQ
  by_cases h4 : ∃ C v k, InducesCycleType Q C v 4 k
  · -- with a 4-cycle there is no `3₁`-cycle (Lemma 5) and no `2₂`-cycle (Lemma 6): `Q' = Q*`
    obtain ⟨C₄, v₄, k₄, hC₄⟩ := h4
    have hk₄ : k₄ = 1 := by rcases inducesCycleType_cases hQ hC₄ with h | h | h <;> omega
    subst hk₄
    obtain ⟨D₄, hD₄⟩ := (inducesCycleType_iff hQ 4 1).1 ⟨C₄, v₄, hC₄⟩
    have hP : IsTwoOrThreeOne Q = IsTwoOneOrThree Q := by
      funext C
      apply propext
      constructor
      · rintro ⟨v, ⟨k, hk⟩ | h31⟩
        · rcases inducesCycleType_cases hQ hk with ⟨-, hk1, hk3⟩ | ⟨h, -⟩ | ⟨h, -⟩
          · rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
            · exact ⟨v, Or.inl hk⟩
            · obtain ⟨D₂, hD₂⟩ := (inducesCycleType_iff hQ 2 2).1 ⟨C, v, hk⟩
              exact absurd ⟨⟨D₂, hD₂⟩, ⟨D₄, hD₄⟩⟩ (lemma6 hQ).2
            · exact ⟨v, Or.inr hk⟩
          · omega
          · omega
        · obtain ⟨D₃, hD₃⟩ := (inducesCycleType_iff hQ 3 1).1 ⟨C, v, h31⟩
          exact absurd hD₃.2.1 ((lemma5 hQ).2.2.1 ⟨D₄, hD₄.1, hD₄.2.1⟩ D₃ hD₃.1)
      · rintro ⟨v, h | h⟩
        · exact ⟨v, Or.inl ⟨1, h⟩⟩
        · exact ⟨v, Or.inl ⟨3, h⟩⟩
    rw [hP, ← hc2]
    exact fun q r _ => Iff.rfl
  · -- `Q'` is a tree with an internal edge, whose split is that of a cut edge of `Q⊕`
    obtain ⟨σ, ⟨a, b, c, d, habcd, hsplit⟩, hσcut, hcf⟩ :=
      exists_speciesTree_contractRooted hQ h32 h4 (IsTwoOrThreeOne Q) rfl
    -- after Corollary 2, the cycles are `2₂`- and `3₁`-cycles: by induction on their number, the
    -- concordance factors are ordered as the quartet tree of that cut edge
    obtain ⟨V', E', _, _, Q', θ', hQ', hcf', hsame, hcut'⟩ := exists_lsaQuartet_of_corollary2 hQ
    have hK : OnlyTwoTwoThreeOne Q' := by
      refine ⟨hsame.not_exists h32, fun ⟨C, v, k, hC⟩ =>
        hsame.not_exists (fun ⟨C', v', h'⟩ => h4 ⟨C', v', k, h'⟩) ⟨C, v, hC⟩, ?_, ?_⟩
      · rintro ⟨C, v, hC⟩
        obtain ⟨C', v', hnot, hC', -⟩ := (hsame 2 _).1 (HasCycleWithBelow.of_inducesCycleType hC)
        rw [hC.2.2.2.2] at hC'
        exact hnot ⟨v', Or.inl hC'⟩
      · rintro ⟨C, v, hC⟩
        obtain ⟨C', v', hnot, hC', -⟩ := (hsame 2 _).1 (HasCycleWithBelow.of_inducesCycleType hC)
        rw [hC.2.2.2.2] at hC'
        exact hnot ⟨v', Or.inr hC'⟩
    have hA : #({a, b} : Finset X) = 2 := card_pair habcd.1
    have hcutQ : Q.HasCutSplit ↑({a, b} : Finset X) := (hσcut _ hA).2 hsplit
    have t := orderedAsQuartetTree_of_onlyTwoTwoThreeOne _ hQ' rfl hK _ hA ((hcut' _ hA).2 hcutQ)
    rw [hcf', ← hc2] at t
    rw [hcf]
    -- equation (1): `Q'` and `Q` have the ordering of the quartet tree `ab|cd`
    exact t.sameOrdering (orderedAsQuartetTree_quartetProb hQ.card_taxa σ hA hsplit)

/-- The probability simplex `Δ₂`. -/
def simplex2 : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1}

/-- The set `I` of Proposition 7: the points of `Δ₂` with `x > 1/6, y = z`, or `y > 1/6, x = z`, or
`z > 1/6, x = y`. -/
def segmentsI : Set (ℝ × ℝ × ℝ) :=
  simplex2 ∩ {p | (1 / 6 < p.1 ∧ p.2.1 = p.2.2) ∨ (1 / 6 < p.2.1 ∧ p.1 = p.2.2) ∨
    (1 / 6 < p.2.2 ∧ p.1 = p.2.1)}

/-- The concordance factors of the `3₂`-cycle of Figure 18 (equation (9)) with `γ = 1/2` and
`x₄ = x₂` reach every point `(1 - 2y, y, y)` with `0 < y < 5/12` (proof of Proposition 7). Near the
limit `t₂, t₄ → 0`, `t₃ → ∞` of the paper (`x₂` close to `1`, `x₃` close to `0`) the factor of `x₁` in
`CF_{AC|BD}` exceeds `y`; as `t₁` runs over `(0, ∞)`, `x₁` runs over `(0, 1)`, and the intermediate value
`CF_{AC|BD} = y`, which the paper obtains by continuity, is reached at `x₁ = y / K`. -/
theorem exists_fig18_params {y : ℝ} (hy₀ : 0 < y) (hy₁ : y < 5 / 12) :
    ∃ len : Fin 8 → ℝ, (∀ i, 0 < len i) ∧
      let x₁ := Real.exp (-len 4); let x₂ := Real.exp (-len 7); let x₃ := Real.exp (-len 5)
      let x₄ := Real.exp (-len 6); let γ : ℝ := 1 / 2
      ((1 - γ) ^ 2 * (1 - 2 / 3 * (x₁ * x₂)) + 2 * γ * (1 - γ) * (1 - x₁ + 1 / 3 * (x₁ * x₃)) +
          γ ^ 2 * (1 - 2 / 3 * (x₁ * x₄)),
        (1 - γ) ^ 2 * (1 / 3 * (x₁ * x₂)) + γ * (1 - γ) * x₁ * (1 - 1 / 3 * x₃) +
          γ ^ 2 * (1 / 3 * (x₁ * x₄)),
        (1 - γ) ^ 2 * (1 / 3 * (x₁ * x₂)) + γ * (1 - γ) * x₁ * (1 - 1 / 3 * x₃) +
          γ ^ 2 * (1 / 3 * (x₁ * x₄))) = (1 - 2 * y, y, y) := by
  set δ := 5 / 12 - y with hδ
  have hδ₀ : 0 < δ := by linarith
  set u : ℝ := 1 - δ / 2 with hu
  set w : ℝ := δ / 2 with hw
  set K : ℝ := u / 6 + 1 / 4 - w / 12 with hK
  have hu₀ : 0 < u := by linarith
  have hu₁ : u < 1 := by linarith
  have hw₀ : 0 < w := by linarith
  have hw₁ : w < 1 := by linarith
  have hKy : y < K := by rw [hK, hu, hw]; linarith
  have hK₀ : 0 < K := by linarith
  set t : ℝ := y / K with ht
  have ht₀ : 0 < t := div_pos hy₀ hK₀
  have ht₁ : t < 1 := (div_lt_one hK₀).2 hKy
  have hpos : ∀ z : ℝ, 0 < z → z < 1 → 0 < -Real.log z := fun z h₀ h₁ =>
    neg_pos.2 (Real.log_neg h₀ h₁)
  have hexp : ∀ z : ℝ, 0 < z → Real.exp (-(-Real.log z)) = z := fun z h₀ => by
    rw [neg_neg, Real.exp_log h₀]
  refine ⟨![1, 1, 1, 1, -Real.log t, -Real.log w, -Real.log u, -Real.log u], fun i => ?_, ?_⟩
  · have h₁ := hpos _ ht₀ ht₁
    have h₂ := hpos _ hw₀ hw₁
    have h₃ := hpos _ hu₀ hu₁
    fin_cases i <;> simp [h₁, h₂, h₃]
  · simp only [Matrix.cons_val, Fin.isValue]
    rw [hexp t ht₀, hexp w hw₀, hexp u hu₀]
    have hty : t * K = y := by rw [ht]; field_simp
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> rw [← hty, hK] <;> ring

/-- The concordance factors of equation (9) lie on the open segment: `CF_{AB|CD} + 2 CF_{AC|BD} = 1`
and `0 < CF_{AC|BD} < 5/12`, the maximum `5/12` being approached at `γ = 1/2`. -/
theorem fig18_bounds {γ x₁ x₂ x₃ x₄ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (h₁ : 0 < x₁) (h₁' : x₁ < 1)
    (h₂ : 0 < x₂) (h₂' : x₂ < 1) (h₃ : 0 < x₃) (h₃' : x₃ < 1) (h₄ : 0 < x₄) (h₄' : x₄ < 1) :
    let X := (1 - γ) ^ 2 * (1 - 2 / 3 * (x₁ * x₂)) + 2 * γ * (1 - γ) * (1 - x₁ + 1 / 3 * (x₁ * x₃)) +
      γ ^ 2 * (1 - 2 / 3 * (x₁ * x₄))
    let Y := (1 - γ) ^ 2 * (1 / 3 * (x₁ * x₂)) + γ * (1 - γ) * x₁ * (1 - 1 / 3 * x₃) +
      γ ^ 2 * (1 / 3 * (x₁ * x₄))
    X + 2 * Y = 1 ∧ 0 < Y ∧ 1 / 6 < X := by
  intro X Y
  have hγ' : 0 < 1 - γ := by linarith
  have e : X + 2 * Y = 1 := by simp only [X, Y]; ring
  have hY : 0 < Y := by
    simp only [Y]
    have : 0 < 1 - 1 / 3 * x₃ := by linarith
    positivity
  have p₁ : x₁ * x₂ < 1 := by nlinarith
  have p₄ : x₁ * x₄ < 1 := by nlinarith
  have p₃ : x₁ * (1 - 1 / 3 * x₃) < 1 := by nlinarith
  have hY' : Y < 5 / 12 := by
    simp only [Y]
    have a₁ : (1 - γ) ^ 2 * (1 / 3 * (x₁ * x₂)) < (1 - γ) ^ 2 * (1 / 3) := by
      have : 0 < (1 - γ) ^ 2 := by positivity
      nlinarith
    have a₂ : γ * (1 - γ) * x₁ * (1 - 1 / 3 * x₃) < γ * (1 - γ) := by
      have : 0 < γ * (1 - γ) := by positivity
      nlinarith
    have a₃ : γ ^ 2 * (1 / 3 * (x₁ * x₄)) < γ ^ 2 * (1 / 3) := by
      have : 0 < γ ^ 2 := by positivity
      nlinarith
    nlinarith [sq_nonneg (2 * γ - 1)]
  exact ⟨e, hY, by linarith⟩

/-- Concordance factors `(X, Y, Y)` with `X > 1/6`, `Y ≥ 0`, `X + 2Y = 1` on the quartet trees
`ab|cd, ac|bd, ad|bc` lie on the open segment for the cherry `{a, b}`. -/
theorem onSegmentOfI_of_triple (hX : Fintype.card X = 4) {a b c d : X} (h : Distinct4 a b c d)
    {p : QuartetTree X → ℝ} {x y : ℝ} (h₁ : p (quartetTree a b c d h) = x)
    (h₂ : p (quartetTree a c b d (distinct4_acbd h)) = y)
    (h₃ : p (quartetTree a d b c (distinct4_adbc h)) = y) (hx : 1 / 6 < x) (hy : 0 ≤ y)
    (hs : x + 2 * y = 1) : OnSegmentOfI p {a, b} := by
  have huniv : ({a, b, c, d} : Finset X) = univ := eq_univ_of_card _ (by rw [h.card_insert_eq, hX])
  have hall : ∀ q : QuartetTree X, q = quartetTree a b c d h ∨
      q = quartetTree a c b d (distinct4_acbd h) ∨ q = quartetTree a d b c (distinct4_adbc h) := by
    intro q
    have : q ∈ treesOn ({a, b, c, d} : Finset X) := by
      rw [mem_treesOn, huniv]
      exact eq_univ_of_card _ (by rw [q.card_taxa, hX])
    rw [treesOn_eq_triple h] at this
    simpa using this
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  have n₂ : ({a, b} : Finset X) ∉ (quartetTree a c b d (distinct4_acbd h)).val := by
    simp only [quartetTree_val_eq_pair, mem_insert, mem_singleton, not_or]
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have : b ∈ ({a, c} : Finset X) := e ▸ by simp
      simp [Ne.symm hab, hbc] at this
    · have : a ∈ ({b, d} : Finset X) := e ▸ by simp
      simp [hab, had] at this
  have n₃ : ({a, b} : Finset X) ∉ (quartetTree a d b c (distinct4_adbc h)).val := by
    simp only [quartetTree_val_eq_pair, mem_insert, mem_singleton, not_or]
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have : b ∈ ({a, d} : Finset X) := e ▸ by simp
      simp [Ne.symm hab, hbd] at this
    · have : a ∈ ({b, c} : Finset X) := e ▸ by simp
      simp [hab, hac] at this
  refine ⟨fun q hq => ?_, fun r r' hr hr' => ?_, fun q => ?_, ?_⟩
  · rcases hall q with rfl | rfl | rfl
    · rwa [h₁]
    · exact absurd hq n₂
    · exact absurd hq n₃
  · have hval : ∀ r : QuartetTree X, ({a, b} : Finset X) ∉ r.val → p r = y := fun r hr => by
      rcases hall r with rfl | rfl | rfl
      · exact absurd (by simp) hr
      · exact h₂
      · exact h₃
    rw [hval r hr, hval r' hr']
  · rcases hall q with rfl | rfl | rfl
    · rw [h₁]; linarith
    · rw [h₂]; exact hy
    · rw [h₃]; exact hy
  · rw [← huniv, treesOn_eq_triple h, sum_insert (by simp [quartetTree_abcd_ne_acbd h,
      quartetTree_abcd_ne_adbc h]), sum_pair (quartetTree_acbd_ne_adbc h), h₁, h₂, h₃]
    linarith

/-- The concordance factors on the open segment for a pair of taxa lie in `I`. -/
theorem mem_segmentsI_of_onSegmentOfI (hX : Fintype.card X = 4) {a b c d : X} (h : Distinct4 a b c d)
    {p : QuartetTree X → ℝ} {A : Finset X} (hA : #A = 2) (hp : OnSegmentOfI p A) :
    (p (quartetTree a b c d h), p (quartetTree a c b d (distinct4_acbd h)),
      p (quartetTree a d b c (distinct4_adbc h))) ∈ segmentsI := by
  have huniv : ({a, b, c, d} : Finset X) = univ := eq_univ_of_card _ (by rw [h.card_insert_eq, hX])
  have hsum := hp.2.2.2
  rw [← huniv, treesOn_eq_triple h, sum_insert (by simp [quartetTree_abcd_ne_acbd h,
    quartetTree_abcd_ne_adbc h]), sum_pair (quartetTree_acbd_ne_adbc h)] at hsum
  refine ⟨⟨hp.2.2.1 _, hp.2.2.1 _, hp.2.2.1 _, by simp only; linarith⟩, ?_⟩
  -- the quartet tree with the cherry `A` is one of the three
  let qA := quartetOfCherry univ A (by rw [card_univ, hX]) (subset_univ A) hA
  have hqA : A ∈ qA.val := by simp [qA]
  have hmem : qA ∈ treesOn ({a, b, c, d} : Finset X) := by
    rw [mem_treesOn, huniv]
    exact eq_univ_of_card _ (by rw [qA.card_taxa, hX])
  rw [treesOn_eq_triple h] at hmem
  have hne : ∀ r : QuartetTree X, r ≠ qA → A ∉ r.val := fun r hr hAr =>
    hr (quartetTree_eq_of_taxa_eq_of_mem (by
      rw [eq_univ_of_card r.taxa (by rw [r.card_taxa, hX]),
        eq_univ_of_card qA.taxa (by rw [qA.card_taxa, hX])]) hAr hqA)
  simp only [mem_insert, mem_singleton] at hmem
  rcases hmem with e | e | e
  · left
    refine ⟨hp.1 _ (e ▸ hqA), hp.2.1 _ _ (hne _ ?_) (hne _ ?_)⟩
    · rw [e]; exact (quartetTree_abcd_ne_acbd h).symm
    · rw [e]; exact (quartetTree_abcd_ne_adbc h).symm
  · right; left
    refine ⟨hp.1 _ (e ▸ hqA), hp.2.1 _ _ (hne _ ?_) (hne _ ?_)⟩
    · rw [e]; exact quartetTree_abcd_ne_acbd h
    · rw [e]; exact (quartetTree_acbd_ne_adbc h).symm
  · right; right
    refine ⟨hp.1 _ (e ▸ hqA), hp.2.1 _ _ (hne _ ?_) (hne _ ?_)⟩
    · rw [e]; exact quartetTree_abcd_ne_adbc h
    · rw [e]; exact quartetTree_acbd_ne_adbc h

/-- **The induction of the proof of Proposition 7**: if `Q⁻` has a `3₂`-cycle with the taxa `A` below
its hybrid node, and no `2₁`- or `2₃`-cycle, its concordance factors lie on the open segment for `A`.
With no other cycle, `Q⁻` is the network of Figure 18 (equation (9)); otherwise the other cycles are
`2₂`- and `3₁`-cycles (Lemmas 5 and 6), and Lemmas 9 and 10 write the concordance factors as a
convex combination of those of networks with the same `3₂`-cycle and one cycle fewer. -/
theorem onSegmentOfI_of_threeTwo (n : ℕ) :
    ∀ {V' E' : Type} [Fintype V'] [Fintype E'] {Q : RootedNetwork V' E' X} {θ : MetricData E'},
      IsLSAQuartet Q θ → numRootedCycles Q = n → ∀ A : Finset X, #A = 2 → HasCycleWithBelow Q 3 ↑A →
      (¬ ∃ C v, InducesCycleType Q C v 2 1) → (¬ ∃ C v, InducesCycleType Q C v 2 3) →
      OnSegmentOfI (cf Q θ) A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V' E' _ _ Q θ hQ hn A hA h32 h21 h23
  obtain ⟨C₀, v₀, hC₀, hD₀⟩ := h32
  rw [Set.ncard_coe_finset, hA] at hC₀
  have hC₀c : C₀ ∈ {C | IsCycle Q.graph C} := hC₀.1
  by_cases hone : numRootedCycles Q = 1
  · -- the only cycle: Figure 18, equation (9)
    have hall : ∀ C, IsCycle Q.graph C → C = C₀ := by
      obtain ⟨C₁, hC₁⟩ := Set.ncard_eq_one.1 hone
      intro C hC
      have e₁ : C ∈ ({C₁} : Set (Set E')) := hC₁ ▸ hC
      have e₀ : C₀ ∈ ({C₁} : Set (Set E')) := hC₁ ▸ hC₀c
      rw [Set.mem_singleton_iff] at e₁ e₀
      rw [e₁, e₀]
    obtain ⟨a', b', hab, rfl⟩ := Finset.card_eq_two.1 hA
    rw [Finset.coe_pair] at hD₀
    obtain ⟨c', d', h4, len, γ, hlen, hγ₀, hγ₁, hiso⟩ := exists_fig18 hQ hC₀ hall hab hD₀
    have h9 := example5 h4 hQ len γ hiso
    simp only [CF, Prod.mk.injEq] at h9
    obtain ⟨e₁, e₂, e₃⟩ := h9
    have hx : ∀ i, 0 < Real.exp (-len i) ∧ Real.exp (-len i) < 1 := fun i =>
      ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith [hlen i])⟩
    obtain ⟨hs, hY, hX'⟩ := fig18_bounds hγ₀ hγ₁ (hx 4).1 (hx 4).2 (hx 7).1 (hx 7).2 (hx 5).1
      (hx 5).2 (hx 6).1 (hx 6).2
    exact onSegmentOfI_of_triple hQ.card_taxa h4 e₁ e₂ e₃ hX' hY.le hs
  · -- another cycle `C`, a `2₂`- or a `3₁`-cycle
    have hlt : 1 < numRootedCycles Q := by
      have : numRootedCycles Q ≠ 0 := fun h0 => by
        have := (Set.ncard_eq_zero (finite_setOf_isCycle Q.graph)).1 h0
        exact (this ▸ hC₀c : C₀ ∈ (∅ : Set (Set E')))
      omega
    obtain ⟨C, hC, hCC₀⟩ : ∃ C, IsCycle Q.graph C ∧ C ≠ C₀ := by
      obtain ⟨C₁, hC₁, C₂, hC₂, hne⟩ := (Set.one_lt_ncard (finite_setOf_isCycle Q.graph)).1 hlt
      by_cases h : C₁ = C₀
      · exact ⟨C₂, hC₂, fun e => hne (h.trans e.symm)⟩
      · exact ⟨C₁, hC₁, h⟩
    obtain ⟨v, m, k, hCt⟩ := exists_inducesCycleType_of_isCycle hQ hC
    obtain ⟨h₁, h₂, hne, hh₁, hh₂, hyb⟩ := exists_hybrid_edges hCt
    obtain ⟨hγ₀, hγ₁⟩ := inheritance_mem_Ioo hQ.binary hQ.metric hyb
    -- the `3₂`-cycle and the absence of `2₁`-, `2₃`-cycles stay
    have keep : ∀ {V'' E'' : Type} {Q' : RootedNetwork V'' E'' X}, SameCyclesBut Q' Q (· = C) →
        HasCycleWithBelow Q' 3 ↑A ∧ (¬ ∃ C v, InducesCycleType Q' C v 2 1) ∧
          ¬ ∃ C v, InducesCycleType Q' C v 2 3 := fun hs =>
      ⟨(hs 3 ↑A).2 ⟨C₀, v₀, fun e => hCC₀ e.symm, by rwa [Set.ncard_coe_finset, hA], hD₀⟩,
        hs.not_exists h21, hs.not_exists h23⟩
    rcases inducesCycleType_cases hQ hCt with ⟨rfl, hk₁, hk₃⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩
    · have hk : k = 2 := by
        rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
        · exact absurd ⟨C, v, hCt⟩ h21
        · rfl
        · exact absurd ⟨C, v, hCt⟩ h23
      subst hk
      -- Lemma 9
      obtain ⟨V₁, E₁, _, _, Q₁, θ₁, hQ₁, hcf₁, hlt₁, hs₁, -⟩ :=
        exists_lsaQuartet_deleteArc hQ (Or.inl hCt) hh₂
      obtain ⟨V₂, E₂, _, _, Q₂, θ₂, hQ₂, hcf₂, hlt₂, hs₂, -⟩ :=
        exists_lsaQuartet_deleteArc hQ (Or.inl hCt) hh₁
      obtain ⟨V₀, E₀, _, _, Q₀, θ₀, hQ₀, hcf₀, hlt₀, hs₀, -⟩ :=
        exists_lsaQuartet_contractRooted hQ hCt
      obtain ⟨k₁, k₁', k₁''⟩ := keep hs₁
      obtain ⟨k₂, k₂', k₂''⟩ := keep hs₂
      obtain ⟨k₀, k₀', k₀''⟩ := keep hs₀
      have t₁ := ih _ (hn ▸ hlt₁) hQ₁ rfl A hA k₁ k₁' k₁''
      have t₂ := ih _ (hn ▸ hlt₂) hQ₂ rfl A hA k₂ k₂' k₂''
      have t₀ := ih _ (hn ▸ hlt₀) hQ₀ rfl A hA k₀ k₀' k₀''
      have hcfQ : cf Q θ = fun q => θ.inheritance h₁ ^ 2 * cf Q₁ θ₁ q +
          (1 - θ.inheritance h₁) ^ 2 * cf Q₂ θ₂ q +
          2 * θ.inheritance h₁ * (1 - θ.inheritance h₁) * cf Q₀ θ₀ q := by
        funext q
        rw [lemma9 hQ hCt hne hh₁ hh₂ q, hcf₁, hcf₂, hcf₀]
      rw [hcfQ]
      have : 0 < 1 - θ.inheritance h₁ := by linarith
      exact OnSegmentOfI.add₃ t₁ t₂ t₀ (by positivity) (by positivity) (by positivity) (by ring)
    · rcases hk with rfl | rfl
      · -- Lemma 10
        obtain ⟨V₁, E₁, _, _, Q₁, θ₁, hQ₁, hcf₁, hlt₁, hs₁, -⟩ :=
          exists_lsaQuartet_deleteArc hQ (Or.inr hCt) hh₂
        obtain ⟨V₂, E₂, _, _, Q₂, θ₂, hQ₂, hcf₂, hlt₂, hs₂, -⟩ :=
          exists_lsaQuartet_deleteArc hQ (Or.inr hCt) hh₁
        obtain ⟨k₁, k₁', k₁''⟩ := keep hs₁
        obtain ⟨k₂, k₂', k₂''⟩ := keep hs₂
        have t₁ := ih _ (hn ▸ hlt₁) hQ₁ rfl A hA k₁ k₁' k₁''
        have t₂ := ih _ (hn ▸ hlt₂) hQ₂ rfl A hA k₂ k₂' k₂''
        have hcfQ : cf Q θ = fun q => θ.inheritance h₁ * cf Q₁ θ₁ q +
            (1 - θ.inheritance h₁) * cf Q₂ θ₂ q := by
          funext q
          rw [lemma10 hQ (Or.inr hCt) hne hh₁ hh₂ q, hcf₁, hcf₂]
        rw [hcfQ]
        exact OnSegmentOfI.add t₁ t₂ hγ₀ (by linarith) (by ring)
      · -- a second `3₂`-cycle is the first (Lemma 6)
        exact absurd (eq_of_inducesCycleType_three_two hQ hCt hC₀) hCC₀
    · -- a 4-cycle and a 3-cycle (Lemma 5)
      obtain ⟨D₄, hD₄⟩ := (inducesCycleType_iff hQ 4 1).1 ⟨C, v, hCt⟩
      obtain ⟨D₃, hD₃⟩ := (inducesCycleType_iff hQ 3 2).1 ⟨C₀, v₀, hC₀⟩
      exact absurd hD₃.2.1 ((lemma5 hQ).2.2.1 ⟨D₄, hD₄.1, hD₄.2.1⟩ D₃ hD₃.1)

/-- **Proposition 7** (`prop:3c2`): if `Q⁻` has a `3₂`-cycle, `CF(Q)` lies in `I`; and every point of `I`
off the vertices of the simplex is `CF(Q)` for such a `Q`. The paper states the second claim for every
point of `I`. Its proof shows that the image is the union of the three open segments, which do not
contain the vertices `(1, 0, 0)`, `(0, 1, 0)`, `(0, 0, 1)` of `I`: concordance factors are positive. -/
theorem proposition7 [DecidableEq X] (hX : Fintype.card X = 4) {a b c d : X}
    (habcd : Distinct4 a b c d) :
    (∀ {Q : RootedNetwork V E X} {θ : MetricData E}, IsLSAQuartet Q θ →
        (∃ C v, InducesCycleType Q C v 3 2) → CF Q θ a b c d habcd ∈ segmentsI) ∧
      ∀ p ∈ segmentsI, 0 < p.1 → 0 < p.2.1 → 0 < p.2.2 →
        ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (Q : RootedNetwork V' E' X)
          (θ : MetricData E'), IsLSAQuartet Q θ ∧ (∃ C v, InducesCycleType Q C v 3 2) ∧
            CF Q θ a b c d habcd = p := by
  -- the decidable equality of the statement is the classical one
  obtain rfl : ‹DecidableEq X› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  refine ⟨fun {Q θ} hQ h32 => ?_, fun p hp hp₁ hp₂ hp₃ => ?_⟩
  · -- the `3₂`-cycle, with the taxa `a', b'` below its hybrid node
    obtain ⟨C, v, hC⟩ := h32
    obtain ⟨a', b', hab, hD⟩ := Set.ncard_eq_two.1 hC.2.2.2.2
    -- Corollary 2: suppress the `2₁`- and `2₃`-cycles
    obtain ⟨V', E', _, _, Q', θ', hQ', hcf', hsame, -⟩ := exists_lsaQuartet_of_corollary2 hQ
    have hnot : ∀ C' v', InducesCycleType Q C' v' 2 1 ∨ InducesCycleType Q C' v' 2 3 →
        IsTwoOneOrThree Q C' := fun C' v' h => ⟨v', h⟩
    have h32' : HasCycleWithBelow Q' 3 ↑({a', b'} : Finset X) := by
      refine (hsame 3 _).2 ⟨C, v, ?_, ?_, ?_⟩
      · rintro ⟨v', h | h⟩ <;> have := h.2.2.2.1 <;> have := hC.2.2.2.1 <;> omega
      · rw [Finset.coe_pair, Set.ncard_pair hab]
        exact hC
      · rw [Finset.coe_pair]
        exact hD
    have h21 : ¬ ∃ C v, InducesCycleType Q' C v 2 1 := by
      rintro ⟨C', v', hC'⟩
      obtain ⟨C'', v'', hn, hC'', -⟩ := (hsame 2 _).1 (HasCycleWithBelow.of_inducesCycleType hC')
      rw [hC'.2.2.2.2] at hC''
      exact hn (hnot _ _ (Or.inl hC''))
    have h23 : ¬ ∃ C v, InducesCycleType Q' C v 2 3 := by
      rintro ⟨C', v', hC'⟩
      obtain ⟨C'', v'', hn, hC'', -⟩ := (hsame 2 _).1 (HasCycleWithBelow.of_inducesCycleType hC')
      rw [hC'.2.2.2.2] at hC''
      exact hn (hnot _ _ (Or.inr hC''))
    -- Lemmas 9 and 10, by induction: the concordance factors lie on the segment for `{a', b'}`
    have hseg := onSegmentOfI_of_threeTwo _ hQ' rfl _ (card_pair hab) h32' h21 h23
    rw [hcf', ← corollary2 hQ] at hseg
    exact mem_segmentsI_of_onSegmentOfI hX habcd (card_pair hab) hseg
  · -- the network of Figure 18, with the taxa below its hybrid node in the cherry of the large
    -- concordance factor, and parameters on the segment
    obtain ⟨x, y, z⟩ := p
    obtain ⟨⟨-, -, -, hsum⟩, hI⟩ := hp
    simp only at hsum hI hp₁ hp₂ hp₃
    -- Figure 18 on the labels `a', b', c', d'` gives `(1 - 2y, y, y)` for every `0 < y < 5/12`
    have hreal : ∀ {a' b' c' d' : X} (h' : Distinct4 a' b' c' d') {y : ℝ}, 0 < y → y < 5 / 12 →
        ∃ len : Fin 8 → ℝ, ∃ hQ : IsLSAQuartet (q18 a' b' c') (q18Metric len (1 / 2)),
          CF (q18 a' b' c') (q18Metric len (1 / 2)) a' b' c' d' h' = (1 - 2 * y, y, y) := by
      intro a' b' c' d' h' y hy₀ hy₁
      obtain ⟨len, hlen, hcf⟩ := exists_fig18_params hy₀ hy₁
      have hQ := isLSAQuartet_q18 hX h' hlen (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      refine ⟨len, hQ, ?_⟩
      rw [example5 h' hQ len (1 / 2) (inducesNetwork_q18 h' hQ)]
      exact hcf
    have h32 : ∀ {a' b' c' d' : X}, Distinct4 a' b' c' d' → ∃ C v, InducesCycleType (q18 a' b' c') C v 3 2 :=
      fun h' => exists_inducesCycleType_q18 hX h'
    rcases hI with ⟨hx, hyz⟩ | ⟨hy, hxz⟩ | ⟨hz, hxy⟩
    · -- `a, b` below the hybrid node
      obtain ⟨len, hQ, hcf⟩ := hreal habcd hp₂ (by linarith)
      refine ⟨Fin 9, Fin 9, inferInstance, inferInstance, q18 a b c, q18Metric len (1 / 2), hQ,
        h32 habcd, ?_⟩
      rw [hcf, Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨by linarith, rfl, hyz⟩
    · -- `a, c` below the hybrid node
      obtain ⟨len, hQ, hcf⟩ := hreal (distinct4_acbd habcd) hp₁ (by linarith)
      refine ⟨Fin 9, Fin 9, inferInstance, inferInstance, q18 a c b, q18Metric len (1 / 2), hQ,
        h32 (distinct4_acbd habcd), ?_⟩
      simp only [CF, Prod.mk.injEq] at hcf ⊢
      obtain ⟨h₁, h₂, h₃⟩ := hcf
      have e : quartetTree a d c b (distinct4_adbc (distinct4_acbd habcd)) =
          quartetTree a d b c (distinct4_adbc habcd) :=
        quartetTree_eq_of_val_eq _ _ (by rw [Finset.pair_comm c b])
      rw [e] at h₃
      dsimp only at hxz hy
      exact ⟨h₂, by rw [h₁]; linarith, h₃.trans hxz⟩
    · -- `a, d` below the hybrid node
      obtain ⟨len, hQ, hcf⟩ := hreal (distinct4_adbc habcd) hp₁ (by linarith)
      refine ⟨Fin 9, Fin 9, inferInstance, inferInstance, q18 a d b, q18Metric len (1 / 2), hQ,
        h32 (distinct4_adbc habcd), ?_⟩
      simp only [CF, Prod.mk.injEq] at hcf ⊢
      obtain ⟨h₁, h₂, h₃⟩ := hcf
      have e₁ : quartetTree a b d c (distinct4_acbd (distinct4_adbc habcd)) =
          quartetTree a b c d habcd := quartetTree_eq_of_val_eq _ _ (by rw [Finset.pair_comm d c])
      have e₂ : quartetTree a c d b (distinct4_adbc (distinct4_adbc habcd)) =
          quartetTree a c b d (distinct4_acbd habcd) :=
        quartetTree_eq_of_val_eq _ _ (by rw [Finset.pair_comm d b])
      rw [e₁] at h₂
      rw [e₂] at h₃
      dsimp only at hxy hz
      exact ⟨h₂, h₃.trans hxy, by rw [h₁]; linarith⟩

/-- **Proposition 8** (`prop::cpcycle`): if the taxa of `Q` satisfy the Cycle property, `Q⁻` contains a
`3₂`-cycle or a 4-cycle. -/
theorem proposition8 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    (hcp : CyclePropertyOn (cf Q θ) univ) :
    (∃ C v, InducesCycleType Q C v 3 2) ∨ ∃ C v k, InducesCycleType Q C v 4 k := by
  by_contra hno
  obtain ⟨h32, h4⟩ := not_or.1 hno
  -- without a `3₂`-cycle or a 4-cycle, `Q'` is a tree, whose concordance factors are treelike
  obtain ⟨σ, ⟨a, b, c, d, habcd, hsplit⟩, -, hcf⟩ :=
    exists_speciesTree_contractRooted hQ h32 h4 (IsTwoOrThreeOne Q) rfl
  have huniv : ({a, b, c, d} : Finset X) = univ :=
    eq_univ_of_card _ (by rw [habcd.card_insert_eq, hQ.card_taxa])
  have htree : IsTreelikeOn
      (cf (contractRooted Q (IsTwoOrThreeOne Q)) (contractMetric Q (IsTwoOrThreeOne Q) θ)) univ := by
    rw [hcf, ← huniv]
    exact isTreelikeOn_quartetProb hQ.card_taxa σ habcd hsplit
  -- Proposition 6: the concordance factors of `Q` have the ordering of those of `Q'`
  exact hcp (isTreelikeOn_of_sameOrdering (proposition6 hQ h32) htree)

/-! ### Section 7 -/

/-- **Proposition 9** (`prop:Bc4cycle1dir`): if the taxa of `Q` satisfy the Big Cycle property, `Q⁻`
contains a 4-cycle. -/
theorem proposition9 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    (hbc : BigCycleOn (cf Q θ) univ) : ∃ C v k, InducesCycleType Q C v 4 k := by
  -- the Big Cycle property implies the Cycle property
  have hcp : CyclePropertyOn (cf Q θ) univ := fun ⟨q, hq, r, hr, hqr, he, _⟩ => hbc q hq r hr hqr he
  -- Proposition 8: a `3₂`-cycle or a 4-cycle
  refine (proposition8 hQ hcp).resolve_left fun h32 => ?_
  -- Proposition 7: with a `3₂`-cycle, two concordance factors are equal
  obtain ⟨a, b, c, d, habcd, huniv⟩ := exists_distinct4_univ hQ.card_taxa
  have hI := (proposition7 (V := V) (E := E) hQ.card_taxa habcd).1 hQ h32
  rw [← huniv, bigCycleOn_iff_triple _ habcd] at hbc
  obtain ⟨h₁, h₂, h₃⟩ := hbc
  rcases hI.2 with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact h₃ h
  · exact h₂ h
  · exact h₁ h

/-- `Q⁻_s` has a 4-cycle. -/
def HasFourCycle (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (s : Finset X)
    (hs : #s = 4) : Prop :=
  ∃ C v k, InducesCycleType (quartetLSA N hN.1 s hs) C v 4 k

/-- `Q⁻_s` has a `3₂`-cycle. -/
def HasThreeTwoCycle (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (s : Finset X)
    (hs : #s = 4) : Prop :=
  ∃ C v, InducesCycleType (quartetLSA N hN.1 s hs) C v 3 2

/-- The Big Cycle property gives `Q⁻_s` a 4-cycle, for all metric parameters (Proposition 9). -/
theorem hasFourCycle_of_bigCycleOn {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {θ : MetricData E} (hθ : IsMetricNetwork N θ) {s : Finset X}
    (hs : #s = 4) (hbc : BigCycleOn (cf N θ) s) : HasFourCycle N hN s hs := by
  have hbc' : BigCycleOn (cf (quartetLSA N hN.1 s hs) (quartetLSAMetric N hN s hs θ)) univ := by
    rw [cf_quartetLSA hN h1 hθ hs, bigCycleOn_comp_map_iff]
    exact hbc
  exact proposition9 (isLSAQuartet_quartetLSA hN h1 hθ hs) (by convert hbc')

/-- **Corollary 2 and equation (8)**: if `Q⁻` has a 4-cycle `C`, then, with the taxa `a, b, c, d`
named around `C` (`c` in the hybrid block), the concordance factors of `Q⊕` for every metric are
those of Figure 17 (equation (8)), in the lengths of two chains `A`, `B` of edges and the inheritance
probability of a hybrid edge `h` (the map `f ∘ η ∘ ν` of the proof of Proposition 10). -/
theorem cf_eq_fig17 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    {C : Set _} (hC : IsCycle hQ.unrooted.graph C) (hC4 : C.ncard = 4) :
    ∃ (u : Fin 4 → _) (f : Fin 4 → _), IsCycleOf hQ.unrooted.graph 4 u f ∧ Set.range f = C ∧
      ∃ (a b c d : X) (habcd : Distinct4 a b c d),
        a ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u 0) ∧
        b ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u 1) ∧
        c ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u 2) ∧
        d ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u 3) ∧
        ∃ (A B : Finset E) (h : E), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ Q.IsHybridArc h ∧
          ∀ θ', IsMetricNetwork Q θ' →
            CF Q θ' a b c d habcd =
              ((1 - θ'.inheritance h) * (1 - 2 / 3 * Real.exp (-∑ e ∈ A, θ'.length e)) +
                  θ'.inheritance h * (1 / 3 * Real.exp (-∑ e ∈ B, θ'.length e)),
                (1 - θ'.inheritance h) * (1 / 3 * Real.exp (-∑ e ∈ A, θ'.length e)) +
                  θ'.inheritance h * (1 / 3 * Real.exp (-∑ e ∈ B, θ'.length e)),
                (1 - θ'.inheritance h) * (1 / 3 * Real.exp (-∑ e ∈ A, θ'.length e)) +
                  θ'.inheritance h * (1 - 2 / 3 * Real.exp (-∑ e ∈ B, θ'.length e))) := by
  obtain ⟨u, f, hcyc, hf, a, b, c, d, habcd, ha, hb, hc, hd, A, B, h, hA, hB, hAB, hh, hfig⟩ :=
    exists_fig17 hQ hC hC4
  refine ⟨u, f, hcyc, hf, a, b, c, d, habcd, ha, hb, hc, hd, A, B, h, hA, hB, hAB, hh,
    fun θ' hθ' => ?_⟩
  obtain ⟨V', E', _, _, Q', θ'', hQ', len, hcf, hiso, hl4, hl5⟩ := hfig θ' hθ'
  -- equation (8) for the network of Figure 17
  have h8 := example4 habcd hQ' len (θ'.inheritance h) hiso
  -- Corollary 2: contracting the `2₁`- and `2₃`-cycles keeps the concordance factors
  have hc2 := corollary2 (hQ.ofMetric hθ')
  have e : ∀ q, nmscCF Q θ' 0 q = nmscCF Q' θ'' 0 q := fun q => by
    have h₁ := congrFun hc2 q
    have h₂ := congrFun hcf q
    convert h₁.trans h₂.symm using 1
  simp only [CF, e] at h8 ⊢
  rw [← hl4, ← hl5]
  exact h8

/-- The order of the concordance factors of equation (8): `CF_{AC|BD}` is the smallest, strictly, and
`CF_{AB|CD} = CF_{AD|BC}` exactly when `(1 - γ)(1 - x₁) = γ(1 - x₂)`. -/
theorem fig17_order {γ L₁ L₂ : ℝ} {t : ℝ × ℝ × ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (h₁ : 0 < L₁)
    (h₂ : 0 < L₂)
    (h : t =
      ((1 - γ) * (1 - 2 / 3 * Real.exp (-L₁)) + γ * (1 / 3 * Real.exp (-L₂)),
        (1 - γ) * (1 / 3 * Real.exp (-L₁)) + γ * (1 / 3 * Real.exp (-L₂)),
        (1 - γ) * (1 / 3 * Real.exp (-L₁)) + γ * (1 - 2 / 3 * Real.exp (-L₂)))) :
    t.2.1 < t.1 ∧ t.2.1 < t.2.2 ∧
      (t.1 = t.2.2 ↔ (1 - γ) * (1 - Real.exp (-L₁)) = γ * (1 - Real.exp (-L₂))) := by
  subst h
  have e₁ : Real.exp (-L₁) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have e₂ : Real.exp (-L₂) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have p₁ : 0 < (1 - γ) * (1 - Real.exp (-L₁)) := mul_pos (by linarith) (by linarith)
  have p₂ : 0 < γ * (1 - Real.exp (-L₂)) := mul_pos hγ₀ (by linarith)
  refine ⟨by dsimp only; nlinarith, by dsimp only; nlinarith,
    ⟨fun h => by dsimp only at h; linarith, fun h => by dsimp only; linarith⟩⟩

/-- **Proposition 10** (`prop:BCgenerically`): if `Q⁻_s` has a 4-cycle, `s` satisfies the Cycle property,
and for generic numerical parameters it satisfies the Big Cycle property. -/
theorem proposition10 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {s : Finset X} (hs : #s = 4) (h4 : HasFourCycle N hN s hs) :
    (∀ θ, IsMetricNetwork N θ → CyclePropertyOn (cf N θ) s) ∧
      ForGenericParams N fun θ => IsMetricNetwork N θ → BigCycleOn (cf N θ) s := by
  -- the decidable equality on the taxa of `Q⊕_s` that the results on quartet networks use
  let _ : DecidableEq (s : Set X) := fun a b => Classical.propDecidable (a = b)
  have hQb := quartetLSA_isBinaryRootedNetwork hN hs
  -- `Q⊕_s` is an LSA quartet network (named here with one of its metrics)
  have hQ₀ : IsLSAQuartet (quartetLSA N hN.1 s hs) (halfInheritanceMetric (quartetLSA N hN.1 s hs) fun _ => 1) :=
    ⟨hQb, quartetLSA_isLevelOne hN h1 hs, quartetLSA_isLSANetwork hN hs, by simp [hs],
      isMetricNetwork_halfInheritanceMetric hQb fun _ => one_pos⟩
  -- its 4-cycle, the hybrid block `{c}` adjacent to the blocks of `b` and `d`
  obtain ⟨C₀, v₀, k, hC₀⟩ := h4
  obtain ⟨C, hCt⟩ := (inducesCycleType_iff hQ₀ 4 k).1 ⟨C₀, v₀, hC₀⟩
  -- by Corollary 2, `CF(Q⁻_s) = CF(Q')`, and `Q'` is the network of Figure 17: equation (8)
  obtain ⟨-, -, -, -, a, b, c, d, habcd, -, -, -, -, A, B, h, hA, hB, hAB, hh, hCF⟩ :=
    cf_eq_fig17 hQ₀ hCt.1 hCt.2.1
  have huniv : ({a, b, c, d} : Finset _) = univ :=
    eq_univ_of_card _ (by rw [habcd.card_insert_eq]; simp [hs])
  have hsum : ∀ θ' : MetricData _, IsMetricNetwork (quartetLSA N hN.1 s hs) θ' → ∀ A : Finset _,
      A.Nonempty → 0 < ∑ e ∈ A, θ'.length e :=
    fun θ' hθ' A hA => Finset.sum_pos (fun e _ => hθ'.2 e) hA
  have horder : ∀ θ', IsMetricNetwork (quartetLSA N hN.1 s hs) θ' →
      (CF (quartetLSA N hN.1 s hs) θ' a b c d habcd).2.1 <
          (CF (quartetLSA N hN.1 s hs) θ' a b c d habcd).1 ∧
        (CF (quartetLSA N hN.1 s hs) θ' a b c d habcd).2.1 <
          (CF (quartetLSA N hN.1 s hs) θ' a b c d habcd).2.2 ∧
        ((CF (quartetLSA N hN.1 s hs) θ' a b c d habcd).1 =
            (CF (quartetLSA N hN.1 s hs) θ' a b c d habcd).2.2 ↔
          (1 - θ'.inheritance h) * (1 - Real.exp (-∑ e ∈ A, θ'.length e)) =
            θ'.inheritance h * (1 - Real.exp (-∑ e ∈ B, θ'.length e))) := fun θ' hθ' =>
    fig17_order (inheritance_mem_Ioo hQb hθ' hh).1 (inheritance_mem_Ioo hQb hθ' hh).2
      (hsum θ' hθ' A hA) (hsum θ' hθ' B hB) (by convert hCF θ' hθ' using 2)
  simp only [CF] at horder
  refine ⟨fun θ hθ => ?_, ?_⟩
  · -- equation (8) shows that `s` satisfies the Cycle property
    obtain ⟨hy₁, hy₂, -⟩ := horder _ (quartetLSA_isMetricNetwork hN hθ hs)
    rw [← cyclePropertyOn_comp_map_iff s]
    have hcp : CyclePropertyOn
        (cf (quartetLSA N hN.1 s hs) (quartetLSAMetric N hN s hs θ)) univ := by
      rw [← huniv]
      unfold CyclePropertyOn
      rw [isTreelikeOn_iff_triple _ habcd]
      rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linarith
    rw [cf_quartetLSA hN h1 hθ hs] at hcp
    convert hcp
  · -- for generic parameters of `Q⊕_s`, `CF_{AB|CD} ≠ CF_{AD|BC}`: the zero set of an analytic
    -- function that is not identically zero, at the parameters with lengths `(|B| + 1)/|A|` on `A`
    have hnull : (quartetLSA N hN.1 s hs).IsGenericNull {θ' | (quartetLSA N hN.1 s hs).IsMetric θ' ∧
        nmscCF (quartetLSA N hN.1 s hs) θ' 0 (quartetTree a b c d habcd) =
          nmscCF (quartetLSA N hN.1 s hs) θ' 0 (quartetTree a d b c (distinct4_adbc habcd))} := by
      set ℓ : _ → ℝ := fun e => if e ∈ A then ((#B : ℝ) + 1) / #A else 1 with hℓdef
      have hApos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
      have hℓ : ∀ e, 0 < ℓ e := fun e => by
        simp only [hℓdef]
        split_ifs
        · positivity
        · exact one_pos
      have hθw := isMetricNetwork_halfInheritanceMetric hQb hℓ
      refine isGenericNull_nmscCF_eq hθw.1 fun heq => ?_
      have hγ : (halfInheritanceMetric (quartetLSA N hN.1 s hs) ℓ).inheritance h = 1 / 2 := by
        simp [halfInheritanceMetric, hh]
      have hLA : ∑ e ∈ A, (halfInheritanceMetric (quartetLSA N hN.1 s hs) ℓ).length e = #B + 1 := by
        simp only [halfInheritanceMetric, hℓdef]
        rw [Finset.sum_congr rfl fun e he => ite_eq_left he, Finset.sum_const, nsmul_eq_mul]
        field_simp
      have hLB : ∑ e ∈ B, (halfInheritanceMetric (quartetLSA N hN.1 s hs) ℓ).length e = #B := by
        simp only [halfInheritanceMetric, hℓdef]
        rw [Finset.sum_congr rfl fun e he => ite_eq_right (Finset.disjoint_right.1 hAB he),
          Finset.sum_const, nsmul_eq_mul, mul_one]
      have := ((horder _ hθw).2.2.1 heq)
      rw [hγ, hLA, hLB] at this
      have hlt : Real.exp (-((#B : ℝ) + 1)) < Real.exp (-(#B : ℝ)) := Real.exp_lt_exp.2 (by linarith)
      linarith
    -- the parameters of `N` are null where those of `Q⊕_s` are (the map `ν`)
    refine isGenericNull_mono (isGenericNull_inducedMetric hN.1 _ hnull) fun θ hθ => ?_
    simp only [Set.mem_ofPred_eq, not_imp] at hθ
    obtain ⟨hθm, hnbc⟩ := hθ
    have hθs := quartetLSA_isMetricNetwork hN hθm hs
    refine ⟨hθm.1, hθs.1, ?_⟩
    obtain ⟨hy₁, hy₂, -⟩ := horder _ hθs
    have hnbc' : ¬ BigCycleOn (cf (quartetLSA N hN.1 s hs) (quartetLSAMetric N hN s hs θ)) univ := by
      rw [cf_quartetLSA hN h1 hθm hs]
      convert (bigCycleOn_comp_map_iff s (cf N θ)).not.2 hnbc
    rw [← huniv, bigCycleOn_iff_triple _ habcd] at hnbc'
    by_contra hne
    exact hnbc' ⟨hy₁.ne', hne, hy₂.ne⟩

/-- **Theorem 3** (`thm::twocor`): for generic numerical parameters, `s` satisfies the Big Cycle property
if and only if `Q⁻_s` has a 4-cycle. -/
theorem theorem3 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    {s : Finset X} (hs : #s = 4) :
    ForGenericParams N fun θ => IsMetricNetwork N θ → (BigCycleOn (cf N θ) s ↔ HasFourCycle N hN s hs) := by
  by_cases h4 : HasFourCycle N hN s hs
  · -- Proposition 10: with a 4-cycle, the Big Cycle property holds generically
    exact (proposition10 hN h1 hs h4).2.mono fun θ h hθ => ⟨fun _ => h4, fun _ => h hθ⟩
  · -- Proposition 9: the Big Cycle property gives a 4-cycle, for all parameters
    refine forGenericParams_of_forall fun θ hθ => ⟨fun hbc => ?_, fun h => absurd h h4⟩
    have hbc' : BigCycleOn (cf (quartetLSA N hN.1 s hs) (quartetLSAMetric N hN s hs θ)) univ := by
      rw [cf_quartetLSA hN h1 hθ hs, bigCycleOn_comp_map_iff]
      exact hbc
    exact proposition9 (isLSAQuartet_quartetLSA hN h1 hθ hs) (by convert hbc')

/-- **Corollary 4** (`cor::Cpgen`): for generic numerical parameters, if `s` satisfies the Cycle property
but not the Big Cycle property, `Q⁻_s` contains a `3₂`-cycle. -/
theorem corollary4 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    {s : Finset X} (hs : #s = 4) :
    ForGenericParams N fun θ => IsMetricNetwork N θ → CyclePropertyOn (cf N θ) s →
      ¬ BigCycleOn (cf N θ) s → HasThreeTwoCycle N hN s hs := by
  -- Theorem 3: generically, no Big Cycle property means no 4-cycle
  refine (theorem3 hN h1 hs).mono fun θ h hθ hcp hnbc => ?_
  have hn4 : ¬ HasFourCycle N hN s hs := fun h4 => hnbc ((h hθ).2 h4)
  -- Proposition 8: the Cycle property gives a `3₂`-cycle or a 4-cycle
  have hcp' : CyclePropertyOn (cf (quartetLSA N hN.1 s hs) (quartetLSAMetric N hN s hs θ)) univ := by
    rw [cf_quartetLSA hN h1 hθ hs, cyclePropertyOn_comp_map_iff]
    exact hcp
  exact (proposition8 (isLSAQuartet_quartetLSA hN h1 hθ hs) (by convert hcp')).resolve_right hn4

/-- The blocks of the cycle `C` of a semidirected network containing the taxa `x` and `y` are adjacent:
the nodes of `C` they are associated with are joined by an edge of `C`. -/
def AdjacentBlocks {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (x y : X') :
    Prop :=
  ∃ e ∈ C, ∃ u w, Joins G.graph e u w ∧ x ∈ nodeBlock G.graph G.leaf C u ∧
    y ∈ nodeBlock G.graph G.leaf C w

/-- Around a 4-cycle `C` of `N⁻`, with nodes `u 0, …, u 3` in order, the blocks of `u i` and `u j` are
adjacent exactly when `u i` and `u j` are consecutive: two nodes of a cycle are not joined by a walk
avoiding it. -/
theorem adjacentBlocks_iff_of_isCycleOf {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C)
    {u : Fin 4 → _} {f : Fin 4 → _} (hcyc : IsCycleOf (unrooted N hN hX).graph 4 u f)
    (hf : Set.range f = C) {i j : Fin 4} {x y : X}
    (hx : x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C (u i))
    (hy : y ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C (u j)) :
    AdjacentBlocks (unrooted N hN hX) C x y ↔ j = finRotate 4 i ∨ i = finRotate 4 j := by
  have hmem : ∀ k, u k ∈ cycleNodes (unrooted N hN hX).graph C := fun k => by
    refine ⟨f k, hf ▸ ⟨k, rfl⟩, ?_⟩
    rcases hcyc.joins k with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  constructor
  · rintro ⟨e, he, p, q, hj, hxp, hyq⟩
    have hpn : p ∈ cycleNodes (unrooted N hN hX).graph C :=
      ⟨e, he, by rcases hj with ⟨h, -⟩ | ⟨-, h⟩ <;> [exact Or.inl h; exact Or.inr h]⟩
    have hqn : q ∈ cycleNodes (unrooted N hN hX).graph C :=
      ⟨e, he, by rcases hj with ⟨-, h⟩ | ⟨h, -⟩ <;> [exact Or.inr h; exact Or.inl h]⟩
    have hp : p = u i := eq_of_walks_compl_of_mem_cycleNodes hN h1 hX hC hpn (hmem i)
      (DirectedMultigraph.walks_trans _ hxp (DirectedMultigraph.walks_symm _ hx))
    have hq : q = u j := eq_of_walks_compl_of_mem_cycleNodes hN h1 hX hC hqn (hmem j)
      (DirectedMultigraph.walks_trans _ hyq (DirectedMultigraph.walks_symm _ hy))
    subst hp hq
    obtain ⟨k, rfl⟩ := hf ▸ he
    have hk := hcyc.joins k
    have hinj := hcyc.injective_node
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hk with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
    · left; rw [hinj (h₁.symm.trans h₃)]; exact hinj (h₂.symm.trans h₄)
    · right; rw [hinj (h₂.symm.trans h₄)]; exact hinj (h₁.symm.trans h₃)
    · right; rw [hinj (h₁.symm.trans h₃)]; exact hinj (h₂.symm.trans h₄)
    · left; rw [hinj (h₂.symm.trans h₄)]; exact hinj (h₁.symm.trans h₃)
  · rintro (rfl | rfl)
    · exact ⟨f i, hf ▸ ⟨i, rfl⟩, u i, u (finRotate 4 i), hcyc.joins i, hx, hy⟩
    · exact ⟨f j, hf ▸ ⟨j, rfl⟩, u (finRotate 4 j), u j,
        (hcyc.joins j).symm, hx, hy⟩

/-- **Proposition 11** (`prop:isbc`): if `s = {a, b, c, d}` satisfies the Big Cycle property, so that
`Q⁻_s` contains a 4-cycle `C_v`, then `q^BC_s = ac|bd` if and only if the `v`-blocks of `Q⁻_s` containing
`a` and `c` are not adjacent. -/
theorem proposition11 [DecidableEq X] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {θ : MetricData E} (hθ : IsMetricNetwork N θ) {a b c d : X}
    (habcd : Distinct4 a b c d) (hs : #({a, b, c, d} : Finset X) = 4)
    (hbc : BigCycleOn (cf N θ) {a, b, c, d}) {C : Set _}
    (hC : IsCycle (quartetUnrooted N hN {a, b, c, d} hs).graph C) (hC4 : C.ncard = 4) :
    IsBCQuartet (cf N θ) {a, b, c, d} (quartetTree a c b d (distinct4_acbd habcd)) ↔
      ¬ AdjacentBlocks (quartetUnrooted N hN {a, b, c, d} hs) C ⟨a, by simp⟩ ⟨c, by simp⟩ := by
  -- the decidable equalities are the classical ones, those of the results on quartet networks
  obtain rfl : ‹DecidableEq X› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  let _ : DecidableEq (({a, b, c, d} : Finset X) : Set X) := fun a b => Classical.propDecidable (a = b)
  have hQ := isLSAQuartet_quartetLSA hN h1 hθ hs
  have hQb := quartetLSA_isBinaryRootedNetwork hN hs
  -- by Corollary 2, `CF(Q) = CF(Q')`, and `Q'` is the network of Figure 17: equation (8)
  obtain ⟨u, f, hcyc, hf, a', b', c', d', h', ha, hb, hc, hd, A, B, h, hA, hB, -, hh, hCF⟩ :=
    cf_eq_fig17 hQ hC hC4
  have hθs := quartetLSA_isMetricNetwork hN hθ hs
  obtain ⟨hy₁, hy₂, -⟩ := fig17_order (inheritance_mem_Ioo hQb hθs hh).1
    (inheritance_mem_Ioo hQb hθs hh).2 (Finset.sum_pos (fun e _ => hθs.2 e) hA)
    (Finset.sum_pos (fun e _ => hθs.2 e) hB) (hCF _ hθs)
  simp only [CF] at hy₁ hy₂
  have huniv : ({a', b', c', d'} : Finset _) = univ :=
    eq_univ_of_card _ (by rw [h'.card_insert_eq]; simp [hs])
  -- `q^BC_s = a'c'|b'd'`, the quartet of the blocks that are not adjacent
  have hbcQ : IsBCQuartet (cf (quartetLSA N hN.1 {a, b, c, d} hs)
      (quartetLSAMetric N hN {a, b, c, d} hs θ)) univ (quartetTree a' c' b' d' (distinct4_acbd h')) := by
    rw [← huniv, isBCQuartet_acbd_iff _ h']
    exact ⟨hy₁, hy₂⟩
  rw [cf_quartetLSA hN h1 hθ hs] at hbcQ
  -- the quartet tree `ac|bd` on the taxa of `Q⊕_s`
  set x : (({a, b, c, d} : Finset X) : Set X) := ⟨a, by simp⟩
  set y : (({a, b, c, d} : Finset X) : Set X) := ⟨c, by simp⟩
  have hd4 : Distinct4 x ⟨b, by simp⟩ y ⟨d, by simp⟩ := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := habcd
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [x, y, Subtype.ext_iff, *]
  have hmap : (quartetTree x y ⟨b, by simp⟩ ⟨d, by simp⟩ (distinct4_acbd hd4)).map
      Subtype.val_injective = quartetTree a c b d (distinct4_acbd habcd) := by
    apply Subtype.ext
    simp [x, y, QuartetTree.map_val, quartetTree_val_eq_pair]
  rw [← hmap, ← isBCQuartet_comp_map_iff]
  -- `q^BC_s = ac|bd` exactly when `{a, c}` is `{a', c'}` or `{b', d'}`
  have h₁ : IsBCQuartet (fun q => cf N θ (q.map Subtype.val_injective)) univ
      (quartetTree x y ⟨b, by simp⟩ ⟨d, by simp⟩ (distinct4_acbd hd4)) ↔
      (({x, y} : Finset _) = {a', c'} ∨ ({x, y} : Finset _) = {b', d'}) := by
    have hmemT : ({x, y} : Finset _) ∈ (quartetTree a' c' b' d' (distinct4_acbd h')).val ↔
        ({x, y} : Finset _) = {a', c'} ∨ ({x, y} : Finset _) = {b', d'} := by
      simp [quartetTree_val_eq_pair]
    rw [← hmemT]
    constructor
    · intro hq
      rw [← hq.unique hbcQ]
      simp [quartetTree_val_eq_pair]
    · intro hm
      have hq : quartetTree x y ⟨b, by simp⟩ ⟨d, by simp⟩ (distinct4_acbd hd4) =
          quartetTree a' c' b' d' (distinct4_acbd h') := by
        have t₁ : (quartetTree x y ⟨b, by simp⟩ ⟨d, by simp⟩ (distinct4_acbd hd4)).taxa = univ := by
          rw [quartetTree_taxa_eq_insert]
          exact eq_univ_of_card _ (by rw [(distinct4_acbd hd4).card_insert_eq]; simp [hs])
        have t₂ : (quartetTree a' c' b' d' (distinct4_acbd h')).taxa = univ := by
          rw [quartetTree_taxa_eq_insert]
          exact eq_univ_of_card _ (by rw [(distinct4_acbd h').card_insert_eq]; simp [hs])
        exact quartetTree_eq_of_taxa_eq_of_mem (t₁.trans t₂.symm) (by simp [quartetTree_val_eq_pair]) hm
      rw [hq]
      exact hbcQ
  -- the blocks of `a, c` are adjacent exactly when their nodes are consecutive on `C`
  set L : Fin 4 → (({a, b, c, d} : Finset X) : Set X) := ![a', b', c', d'] with hLdef
  have hL : Function.Injective L := h'.injective_vec
  have hrange : ∀ z, ∃ i, L i = z := fun z => by
    have : z ∈ ({a', b', c', d'} : Finset _) := huniv ▸ mem_univ z
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl | rfl | rfl
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  have hLB : ∀ i, L i ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u i) := by
    intro i
    fin_cases i
    exacts [ha, hb, hc, hd]
  obtain ⟨i, hi⟩ := hrange x
  obtain ⟨j, hj⟩ := hrange y
  have hxy : x ≠ y := fun e => habcd.2.1 (congrArg Subtype.val e)
  have hij : i ≠ j := fun e => hxy (hi ▸ hj ▸ congrArg L e)
  have h₂ := adjacentBlocks_iff_of_isCycleOf hQb (quartetLSA_isLevelOne hN h1 hs) hQ.nontrivial hC
    hcyc hf (hi ▸ hLB i) (hj ▸ hLB j)
  rw [h₁, h₂, ← hi, ← hj]
  have hpair : ∀ i j k l : Fin 4,
      ({L i, L j} : Finset (({a, b, c, d} : Finset X) : Set X)) = {L k, L l} ↔
        (i = k ∧ j = l ∨ i = l ∧ j = k) := by
    intro i j k l
    rw [← Finset.coe_inj]
    push_cast
    rw [Set.pair_eq_pair_iff, hL.eq_iff, hL.eq_iff, hL.eq_iff, hL.eq_iff]
  rw [show a' = L 0 from rfl, show b' = L 1 from rfl, show c' = L 2 from rfl,
    show d' = L 3 from rfl, hpair, hpair]
  have key : ∀ i j : Fin 4, i ≠ j →
      (((i = 0 ∧ j = 2 ∨ i = 2 ∧ j = 0) ∨ i = 1 ∧ j = 3 ∨ i = 3 ∧ j = 1) ↔
        ¬(j = finRotate 4 i ∨ i = finRotate 4 j)) := by decide
  exact key i j hij

/-- The cycle `C` of `N⁻`, with hybrid node `v`, separates the taxa of `s`: they are in four distinct
`v`-blocks, and one of them is in the hybrid block (descends from `v`). -/
def SeparatesQuartet {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (v : V')
    (s : Finset X') : Prop :=
  IsCycle G.graph C ∧ IsHybridNodeOf G C v ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ SameBlock G.graph G.leaf C x y) ∧ ∃ x ∈ s, DescendsFrom G v x

/-- **Lemma 12** (`cfs`): for generic numerical parameters, a set `s` of four taxa satisfies the Big
Cycle property if and only if `N⁻` has a cycle `C_v` of size at least 4 for which the taxa of `s` are in
distinct `v`-blocks, one of them in the hybrid block. The paper's statement is garbled ("there exists
`{a,b,c,d}` satisfying the BC property if and only if `N⁻` contains a cycle `C_v` of size `k ≥ 4` with
one of these taxa is in the hybrid block, and the others in distinct `v`-blocks"); its proof and every
use of it are this statement, for each set of four taxa. -/
theorem lemma12 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) :
    ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ s : Finset X, #s = 4 →
      (BigCycleOn (cf N θ) s ↔
        ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s) := by
  -- Theorem 3, for the finitely many sets of four taxa at once
  refine (forGenericParams_iInter (ι := {s : Finset X // #s = 4}) fun s => theorem3 hN h1 s.2).mono
    fun θ h hθ s hs => ?_
  rw [h ⟨s, hs⟩ hθ]
  constructor
  · -- a 4-cycle of `Q⁻_s` comes from a cycle of `N⁻` of size at least four separating `s`
    rintro ⟨C₀, v₀, k, hC₀⟩
    obtain ⟨C, hC, hC4, w, hw, -⟩ :=
      (inducesCycleType_iff (isLSAQuartet_quartetLSA hN h1 hθ hs) 4 k).1 ⟨C₀, v₀, hC₀⟩
    obtain ⟨C', w', h4, hC', hw', hblk, hdesc, -⟩ :=
      exists_separates_of_fourCycle hN h1 hX hs hC hC4 hw
    exact ⟨C', w', h4, hC', hw', hblk, hdesc⟩
  · -- such a cycle of `N⁻` induces a 4-cycle of `Q⁻_s`
    rintro ⟨C, v, h4, hC, hv, hblk, hdesc⟩
    exact exists_fourCycle_of_separates hN h1 hX hs h4 hC hv hblk hdesc

/-- The node of `N` underlying a node of `Q⁻_s`. -/
def quartetNode {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {s : Finset X} (hs : #s = 4)
    (w : SemidirectedVertex (quartetLSA_isBinaryRootedNetwork hN hs).1
      (Finset.one_lt_card_iff_nontrivial.mp (by omega)).coe_sort) : V :=
  w.1.1.1.1

/-- The set `s` of four taxa satisfying the Big Cycle property *determines* the hybrid node `v` of `N`
(`ψ(s) = v`): `v` is the hybrid node of the 4-cycle of `Q⁻_s`. -/
def Determines {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (s : Finset X) (hs : #s = 4)
    (v : V) : Prop :=
  ∃ C w, IsCycle (quartetUnrooted N hN s hs).graph C ∧ C.ncard = 4 ∧
    IsHybridNodeOf (quartetUnrooted N hN s hs) C w ∧ quartetNode hN hs w = v

/-- **Lemma 13** (`3tax`): if `{a, b, c, d}` and `{a, b, c, e}` satisfy the Big Cycle property, they
determine the same hybrid node.

Departure from the paper: the paper cites Lemma 12 for the taxa of a set with the Big Cycle property
being in distinct blocks of the cycle of `N⁻` that the set determines; Lemma 12 holds for generic
parameters, and Lemma 13 is stated for given parameters, so the proof uses the direction of the proof
of Lemma 12 that holds for all parameters: Proposition 9 (`hasFourCycle_of_bigCycleOn`) and
`exists_separates_of_fourCycle`. -/
theorem lemma13 [DecidableEq X] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {θ : MetricData E} (hθ : IsMetricNetwork N θ) {a b c d e : X}
    (h₁ : #({a, b, c, d} : Finset X) = 4) (h₂ : #({a, b, c, e} : Finset X) = 4)
    (hbc₁ : BigCycleOn (cf N θ) {a, b, c, d}) (hbc₂ : BigCycleOn (cf N θ) {a, b, c, e}) (v : V) :
    Determines hN {a, b, c, d} h₁ v ↔ Determines hN {a, b, c, e} h₂ v := by
  -- the decidable equality of the statement is the classical one
  obtain rfl : ‹DecidableEq X› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hd₁ := distinct4_of_card_insert_eq h₁
  have hX : Nontrivial X := ⟨⟨a, b, hd₁.1⟩⟩
  -- a set of four taxa with the Big Cycle property determines a hybrid node (Proposition 9)
  have hex : ∀ {s : Finset X} (hs : #s = 4), BigCycleOn (cf N θ) s → ∃ u, Determines hN s hs u := by
    intro s hs hbc
    obtain ⟨C₀, v₀, k, hC₀⟩ := hasFourCycle_of_bigCycleOn hN h1 hθ hs hbc
    obtain ⟨C, hC, hC4, w, hw, -⟩ :=
      (inducesCycleType_iff (isLSAQuartet_quartetLSA hN h1 hθ hs) 4 k).1 ⟨C₀, v₀, hC₀⟩
    exact ⟨_, C, w, hC, hC4, hw, rfl⟩
  -- two sets containing `a, b, c` determine the same hybrid node
  have huniq : ∀ {s₁ s₂ : Finset X} (hs₁ : #s₁ = 4) (hs₂ : #s₂ = 4) {u₁ u₂ : V},
      a ∈ s₁ → b ∈ s₁ → c ∈ s₁ → a ∈ s₂ → b ∈ s₂ → c ∈ s₂ →
      Determines hN s₁ hs₁ u₁ → Determines hN s₂ hs₂ u₂ → u₁ = u₂ := by
    intro s₁ s₂ hs₁ hs₂ u₁ u₂ ha₁ hb₁ hc₁ ha₂ hb₂ hc₂ hu₁ hu₂
    obtain ⟨C₁, w₁, hC₁, hC₁4, hw₁, rfl⟩ := hu₁
    obtain ⟨C₂, w₂, hC₂, hC₂4, hw₂, rfl⟩ := hu₂
    -- by Lemma 12, the cycles `C_v`, `C_u` of `N⁻` separate the two sets
    obtain ⟨Cv, v', -, hCv, hv', hblk₁, -, hv'w⟩ :=
      exists_separates_of_fourCycle hN h1 hX hs₁ hC₁ hC₁4 hw₁
    obtain ⟨Cu, u', -, hCu, hu', hblk₂, -, hu'w⟩ :=
      exists_separates_of_fourCycle hN h1 hX hs₂ hC₂ hC₂4 hw₂
    by_contra hne
    set G := unrooted N hN hX
    have hmem : ∀ {C : Set _} {x}, IsHybridNodeOf G C x → x ∈ cycleNodes G.graph C := by
      rintro C x ⟨h, hh, -, -, -, -, -, ht, -⟩
      exact ⟨h, hh, Or.inr ht⟩
    -- `C_u ≠ C_v`: a cycle has one hybrid node
    have hCuv : Cv ≠ Cu := by
      rintro rfl
      obtain ⟨⟨x, -, huq⟩, -, -⟩ := lemma3_unrooted hN h1 hX hCv
      have hval : ∀ {y}, IsHybridNodeOf G Cv y → y = x := by
        rintro y ⟨h, hh, h', hh', hne', hd, hd', ht, ht'⟩
        exact huq y ⟨hmem ⟨h, hh, h', hh', hne', hd, hd', ht, ht'⟩, h, h', hne', hd, hd', ht, ht'⟩
      refine hne ?_
      show w₁.1.1.1.1 = w₂.1.1.1.1
      rw [← hv'w, ← hu'w, hval hv', hval hu']
    -- so they have no common node (Lemma 3), and no common edge
    have hdisj : ∀ z, z ∈ cycleNodes G.graph Cv → z ∉ cycleNodes G.graph Cu := fun z hzv hzu =>
      hCuv ((lemma3_unrooted hN h1 hX hCv).2.2 Cu hCu ⟨z, hzv, hzu⟩)
    have hedge : ∀ f ∈ Cu, f ∉ Cv := fun f hfu hfv =>
      hdisj _ ⟨f, hfv, Or.inl rfl⟩ ⟨f, hfu, Or.inl rfl⟩
    -- `C_u` lies in one component `K` of `N⁻ ∖ E(C_v)`, that of its node `u'`
    have hz₀ := hmem hu'
    have hK : ∀ f ∈ Cu, G.graph.Walks Cvᶜ (G.graph.source f) u' := fun f hf =>
      DirectedMultigraph.walks_mono (fun g hg => hedge g hg)
        (walks_cycle_of_mem_cycleNodes G.graph hCu ⟨f, hf, Or.inl rfl⟩ hz₀)
    -- at most one of `a, b, c` is in `K`: they are in distinct `v`-blocks
    have hone : ∀ x ∈ s₁, ∀ y ∈ s₁, x ≠ y → G.graph.Walks Cvᶜ (G.leaf x) u' →
        G.graph.Walks Cvᶜ (G.leaf y) u' → False := fun x hx y hy hxy h₁ h₂ =>
      hblk₁ x hx y hy hxy (h₁.trans (G.graph.walks_symm h₂))
    -- the taxa outside `K` are in one `u`-block: they reach `C_v` avoiding `C_u`
    have hout : ∀ x ∈ s₂, ∀ y ∈ s₂, x ≠ y → ¬ G.graph.Walks Cvᶜ (G.leaf x) u' →
        ¬ G.graph.Walks Cvᶜ (G.leaf y) u' → False := by
      intro x hx y hy hxy h₁ h₂
      have hconn := unrooted_isConnected hN hX
      obtain ⟨zx, hzx, hwx⟩ := exists_walks_cycleNodes_of_not_walks G.graph hconn hK h₁
      obtain ⟨zy, hzy, hwy⟩ := exists_walks_cycleNodes_of_not_walks G.graph hconn hK h₂
      have hCv' : Cv ⊆ Cuᶜ := fun f hfv hfu => hedge f hfu hfv
      refine hblk₂ x hx y hy hxy ?_
      exact ((DirectedMultigraph.walks_mono Set.inter_subset_right hwx).trans
        (DirectedMultigraph.walks_mono hCv' (walks_cycle_of_mem_cycleNodes G.graph hCv hzx hzy))).trans
        (G.graph.walks_symm (DirectedMultigraph.walks_mono Set.inter_subset_right hwy))
    obtain ⟨hab, hac, -, hbc, -, -⟩ := hd₁
    by_cases hA : G.graph.Walks Cvᶜ (G.leaf a) u' <;> by_cases hB : G.graph.Walks Cvᶜ (G.leaf b) u'
    · exact hone a ha₁ b hb₁ hab hA hB
    · by_cases hC : G.graph.Walks Cvᶜ (G.leaf c) u'
      · exact hone a ha₁ c hc₁ hac hA hC
      · exact hout b hb₂ c hc₂ hbc hB hC
    · by_cases hC : G.graph.Walks Cvᶜ (G.leaf c) u'
      · exact hone b hb₁ c hc₁ hbc hB hC
      · exact hout a ha₂ c hc₂ hac hA hC
    · exact hout a ha₂ b hb₂ hab hA hB
  constructor
  · intro hv
    obtain ⟨u, hu⟩ := hex h₂ hbc₂
    rwa [huniq h₁ h₂ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hv hu]
  · intro hv
    obtain ⟨u, hu⟩ := hex h₁ hbc₁
    rwa [huniq h₂ h₁ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hv hu]

end Banos2019
