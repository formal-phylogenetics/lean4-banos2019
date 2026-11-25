module

public import Banos2019.Quartet.Normal
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

/-- **Proposition 6** (`prop:Cfspreserv`): if `Q⁻` has no `3₂`-cycle, the ordering of `CF(Q)` is that of
`CF(Q')`, where `Q'` is obtained by contracting all 2-cycles and all `3₁`-cycles. -/
theorem proposition6 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    (h32 : ¬ ∃ C v, InducesCycleType Q C v 3 2) :
    SameOrdering (cf Q θ)
      (cf (contractRooted Q (IsTwoOrThreeOne Q)) (contractMetric Q (IsTwoOrThreeOne Q) θ)) := by
  sorry

/-- The probability simplex `Δ₂`. -/
def simplex2 : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1}

/-- The set `I` of Proposition 7: the points of `Δ₂` with `x > 1/6, y = z`, or `y > 1/6, x = z`, or
`z > 1/6, x = y`. -/
def segmentsI : Set (ℝ × ℝ × ℝ) :=
  simplex2 ∩ {p | (1 / 6 < p.1 ∧ p.2.1 = p.2.2) ∨ (1 / 6 < p.2.1 ∧ p.1 = p.2.2) ∨
    (1 / 6 < p.2.2 ∧ p.1 = p.2.1)}

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
  sorry

/-- **Proposition 8** (`prop::cpcycle`): if the taxa of `Q` satisfy the Cycle property, `Q⁻` contains a
`3₂`-cycle or a 4-cycle. -/
theorem proposition8 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    (hcp : CyclePropertyOn (cf Q θ) univ) :
    (∃ C v, InducesCycleType Q C v 3 2) ∨ ∃ C v k, InducesCycleType Q C v 4 k := by
  by_contra hno
  obtain ⟨h32, h4⟩ := not_or.1 hno
  -- without a `3₂`-cycle or a 4-cycle, `Q'` is a tree, whose concordance factors are treelike
  obtain ⟨σ, a, b, c, d, habcd, hsplit, hcf⟩ :=
    exists_speciesTree_contractRooted hQ h32 h4 (IsTwoOrThreeOne Q) rfl
  have huniv : ({a, b, c, d} : Finset X) = univ :=
    eq_univ_of_card _ (by rw [habcd.card_eq, hQ.card_taxa])
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
  have hQ₀ : IsLSAQuartet (quartetLSA N hN.1 s hs) (halfMetric (quartetLSA N hN.1 s hs) fun _ => 1) :=
    ⟨hQb, quartetLSA_isLevelOne hN h1 hs, quartetLSA_isLSANetwork hN hs, by simp [hs],
      isMetricNetwork_halfMetric hQb fun _ => one_pos⟩
  -- its 4-cycle, the hybrid block `{c}` adjacent to the blocks of `b` and `d`
  obtain ⟨C₀, v₀, k, hC₀⟩ := h4
  obtain ⟨C, hCt⟩ := (inducesCycleType_iff hQ₀ 4 k).1 ⟨C₀, v₀, hC₀⟩
  -- by Corollary 2, `CF(Q⁻_s) = CF(Q')`, and `Q'` is the network of Figure 17: equation (8)
  obtain ⟨-, -, -, -, a, b, c, d, habcd, -, -, -, -, A, B, h, hA, hB, hAB, hh, hCF⟩ :=
    cf_eq_fig17 hQ₀ hCt.1 hCt.2.1
  have huniv : ({a, b, c, d} : Finset _) = univ :=
    eq_univ_of_card _ (by rw [habcd.card_eq]; simp [hs])
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
      have hθw := isMetricNetwork_halfMetric hQb hℓ
      refine isGenericNull_nmscCF_eq hθw.1 fun heq => ?_
      have hγ : (halfMetric (quartetLSA N hN.1 s hs) ℓ).inheritance h = 1 / 2 := by
        simp [halfMetric, hh]
      have hLA : ∑ e ∈ A, (halfMetric (quartetLSA N hN.1 s hs) ℓ).length e = #B + 1 := by
        simp only [halfMetric, hℓdef]
        rw [Finset.sum_congr rfl fun e he => ite_eq_left he, Finset.sum_const, nsmul_eq_mul]
        field_simp
      have hLB : ∑ e ∈ B, (halfMetric (quartetLSA N hN.1 s hs) ℓ).length e = #B := by
        simp only [halfMetric, hℓdef]
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
    eq_univ_of_card _ (by rw [h'.card_eq]; simp [hs])
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
    simp [x, y, QuartetTree.map_val, quartetTree_val_eq]
  rw [← hmap, ← isBCQuartet_comp_map_iff]
  -- `q^BC_s = ac|bd` exactly when `{a, c}` is `{a', c'}` or `{b', d'}`
  have h₁ : IsBCQuartet (fun q => cf N θ (q.map Subtype.val_injective)) univ
      (quartetTree x y ⟨b, by simp⟩ ⟨d, by simp⟩ (distinct4_acbd hd4)) ↔
      (({x, y} : Finset _) = {a', c'} ∨ ({x, y} : Finset _) = {b', d'}) := by
    have hmemT : ({x, y} : Finset _) ∈ (quartetTree a' c' b' d' (distinct4_acbd h')).val ↔
        ({x, y} : Finset _) = {a', c'} ∨ ({x, y} : Finset _) = {b', d'} := by
      simp [quartetTree_val_eq]
    rw [← hmemT]
    constructor
    · intro hq
      rw [← hq.unique hbcQ]
      simp [quartetTree_val_eq]
    · intro hm
      have hq : quartetTree x y ⟨b, by simp⟩ ⟨d, by simp⟩ (distinct4_acbd hd4) =
          quartetTree a' c' b' d' (distinct4_acbd h') := by
        have t₁ : (quartetTree x y ⟨b, by simp⟩ ⟨d, by simp⟩ (distinct4_acbd hd4)).taxa = univ := by
          rw [quartetTree_taxa_eq]
          exact eq_univ_of_card _ (by rw [(distinct4_acbd hd4).card_eq]; simp [hs])
        have t₂ : (quartetTree a' c' b' d' (distinct4_acbd h')).taxa = univ := by
          rw [quartetTree_taxa_eq]
          exact eq_univ_of_card _ (by rw [(distinct4_acbd h').card_eq]; simp [hs])
        exact quartetTree_eq_of_mem (t₁.trans t₂.symm) (by simp [quartetTree_val_eq]) hm
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
  sorry

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
determine the same hybrid node. -/
theorem lemma13 [DecidableEq X] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {θ : MetricData E} (hθ : IsMetricNetwork N θ) {a b c d e : X}
    (h₁ : #({a, b, c, d} : Finset X) = 4) (h₂ : #({a, b, c, e} : Finset X) = 4)
    (hbc₁ : BigCycleOn (cf N θ) {a, b, c, d}) (hbc₂ : BigCycleOn (cf N θ) {a, b, c, e}) (v : V) :
    Determines hN {a, b, c, d} h₁ v ↔ Determines hN {a, b, c, e} h₂ v := by
  sorry

end Banos2019
