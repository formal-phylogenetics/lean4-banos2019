module

public import Banos2019.Bridge.Unrooted
public import Banos2019.Quartet.Examples
public import Banos2019.Quartet.Fig18
public import Banos2019.Identify.TreeOfCycles

/-!
# The networks of Figures 17 and 18, on the Challenge's definitions

`Model.fig17Network` and `Model.fig18Network` (`Banos2019.Defs`) are the library's rootings `q17`
and `q18` of Figures 17 and 18 (`fig17Network_toRooted`, `fig18Network_toRooted`). So:

* `example6_fig18`, `example7_fig17`: Examples 6 and 7 (`Banos2019.example6`, `Banos2019.example7`).
* `unrooted_q17_fourCycle`, `unrooted_q18_ncard`: `N⁻` of Figure 17 has a 4-cycle; every cycle of
  `N⁻` of Figure 18 has three edges (the cycle of `q18` through the root, which `N⁻` suppresses).
  Both through `inducesCycleType_iff`.
* `fig17_fig18_unrooted`: on the Challenge's `unrooted`.
* `fig17_fig18_tilde`: the networks `Ñ` of Figures 17 and 18 are not isomorphic: that of Figure 17
  has a cycle, from the 4-cycle of `N⁻` (`exists_isCycle_tilde_of_big`), and a cycle of `Ñ` comes
  from a cycle of `N⁻` of size at least four (`exists_isCycle_big_of_mem_cycleNodes_tilde`), which
  Figure 18 does not have.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace Banos2019.Model

theorem distinct4_fin4 : Distinct4 (0 : Fin 4) 1 2 3 := by
  unfold Distinct4
  decide

theorem fig17Network_toRooted : fig17Network.toRooted = q17 (0 : Fin 4) 1 2 := by
  change (⟨⟨_, _⟩, 8, ![0, 1, 2, 3]⟩ : RootedNetwork (Fin 9) (Fin 9) (Fin 4)) =
    ⟨⟨q17Src, q17Tgt⟩, 8, quartetLeaf9 0 1 2⟩
  congr 1
  funext x
  fin_cases x <;> rfl

theorem fig18Network_toRooted : fig18Network.toRooted = q18 (0 : Fin 4) 1 2 := by
  change (⟨⟨_, _⟩, 8, ![0, 1, 2, 3]⟩ : RootedNetwork (Fin 9) (Fin 9) (Fin 4)) =
    ⟨⟨q18Src, q18Tgt⟩, 8, fun x => (figLeaf 0 1 2 x).castSucc⟩
  congr 1
  funext x
  fin_cases x <;> rfl

/-- The lengths of the edges of Figure 17 in the library's terms: pendant edges and hybrid edges of
length one. -/
abbrev fig17Len (t₁ t₂ : ℝ) : Fin 8 → ℝ := ![1, 1, 1, 1, t₁, t₂, 1, 1]

theorem fig17Params_toMetric (t₁ t₂ γ : ℝ) :
    (fig17Params t₁ t₂ γ).toMetric = q17Metric (fig17Len t₁ t₂) γ := by
  rfl

/-- The lengths of the edges of Figure 18 in the library's terms: pendant edges of length one. -/
abbrev fig18Len (t₁ t₂ t₃ t₄ : ℝ) : Fin 8 → ℝ := ![1, 1, 1, 1, t₁, t₃, t₄, t₂]

theorem fig18Params_toMetric (t₁ t₂ t₃ t₄ γ : ℝ) :
    (fig18Params t₁ t₂ t₃ t₄ γ).toMetric = q18Metric (fig18Len t₁ t₂ t₃ t₄) γ := by
  rfl

theorem fig17_isLSAQuartet {t₁ t₂ γ : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    IsLSAQuartet (q17 (0 : Fin 4) 1 2) (q17Metric (fig17Len t₁ t₂) γ) :=
  isLSAQuartet_q17 (by simp) distinct4_fin4 (fun i => by fin_cases i <;> simp [h₁, h₂]) hγ₀ hγ₁

theorem fig18_isLSAQuartet {t₁ t₂ t₃ t₄ γ : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂) (h₃ : 0 < t₃)
    (h₄ : 0 < t₄) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    IsLSAQuartet (q18 (0 : Fin 4) 1 2) (q18Metric (fig18Len t₁ t₂ t₃ t₄) γ) :=
  isLSAQuartet_q18 (by simp) distinct4_fin4 (fun i => by fin_cases i <;> simp [h₁, h₂, h₃, h₄])
    hγ₀ hγ₁

/-- The properties of a network that is a rooting of a figure, on the Challenge's definitions. -/
theorem properties_of_toRooted {N : Network (Fin 9) (Fin 9) (Fin 4)} {θ : Params (Fin 9)}
    {Q : RootedNetwork (Fin 9) (Fin 9) (Fin 4)} {θQ : MetricData (Fin 9)} (hQ : IsLSAQuartet Q θQ)
    (hN : N.toRooted = Q) (hθ : θ.toMetric = θQ) :
    N.IsBinaryNetwork ∧ N.graph.IsLevelOne ∧ N.IsLSA Set.univ N.root ∧ N.IsMetric θ := by
  subst hN hθ
  have hNb : N.IsBinaryNetwork := (Network.isBinaryNetwork_iff N).mpr hQ.binary
  exact ⟨hNb, (Digraph.isLevelOne_iff _).mpr hQ.levelOne, hQ.isLSA,
    (N.isMetric_iff hNb θ).mpr hQ.metric⟩

/-! ### Examples 6 and 7 -/

/-- **Example 6**, on the Challenge's definitions. -/
theorem example6_fig18 :
    let θ := fig18Params (-Real.log (6 / 7)) (-Real.log (6 / 7)) (-Real.log (1 / 14))
      (-Real.log (13 / 14)) (1 / 2)
    fig18Network.IsBinaryNetwork ∧ fig18Network.graph.IsLevelOne ∧
      fig18Network.IsLSA Set.univ fig18Network.root ∧ fig18Network.IsMetric θ ∧
      (∀ q : QuartetTree (Fin 4),
        (q.1 = {{0, 1}, {2, 3}} → fig18Network.cf θ q = 32 / 98) ∧
        (q.1 = {{0, 2}, {1, 3}} → fig18Network.cf θ q = 33 / 98) ∧
        (q.1 = {{0, 3}, {1, 2}} → fig18Network.cf θ q = 33 / 98)) ∧
      ¬ BigCycleOn (fig18Network.cf θ) univ := by
  intro θ
  have a₁ : Real.log (6 / 7) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have a₂ : Real.log (1 / 14) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have a₃ : Real.log (13 / 14) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hQ := fig18_isLSAQuartet (neg_pos.mpr a₁) (neg_pos.mpr a₁) (neg_pos.mpr a₂)
    (neg_pos.mpr a₃) (γ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨hNb, h1, hl, hm⟩ := properties_of_toRooted hQ fig18Network_toRooted
    (fig18Params_toMetric _ _ _ _ _)
  have e := example6 distinct4_fin4 hQ _ rfl rfl rfl rfl (inducesNetwork_q18 distinct4_fin4 hQ)
  simp only [CF, Prod.mk.injEq] at e
  have hcf : ∀ q, fig18Network.cf θ q = Banos2019.cf (q18 (0 : Fin 4) 1 2)
      (q18Metric (fig18Len (-Real.log (6 / 7)) (-Real.log (6 / 7)) (-Real.log (1 / 14))
        (-Real.log (13 / 14))) (1 / 2)) (quartetTreeEquiv q) :=
    fun q => by rw [fig18Network.cf_eq, Function.comp_apply, fig18Network_toRooted,
      fig18Params_toMetric]
  have hvals : ∀ q : QuartetTree (Fin 4),
      (q.1 = {{0, 1}, {2, 3}} → fig18Network.cf θ q = 32 / 98) ∧
      (q.1 = {{0, 2}, {1, 3}} → fig18Network.cf θ q = 33 / 98) ∧
      (q.1 = {{0, 3}, {1, 2}} → fig18Network.cf θ q = 33 / 98) := fun q => by
    refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_⟩
    · rw [hcf, ← e.1]
      exact congrArg _ (Subtype.ext hq)
    · rw [hcf, ← e.2.1]
      exact congrArg _ (Subtype.ext hq)
    · rw [hcf, ← e.2.2]
      exact congrArg _ (Subtype.ext hq)
  refine ⟨hNb, h1, hl, hm, hvals, fun hbc => ?_⟩
  -- `02|13` and `03|12` have the same concordance factor
  have h₀ : IsQuartetTree ({{0, 2}, {1, 3}} : Finset (Finset (Fin 4))) := by
    unfold IsQuartetTree
    decide
  have h₀' : IsQuartetTree ({{0, 3}, {1, 2}} : Finset (Finset (Fin 4))) := by
    unfold IsQuartetTree
    decide
  refine hbc ⟨_, h₀⟩ (mem_treesOn_iff.mpr ?_) ⟨_, h₀'⟩ (mem_treesOn_iff.mpr ?_) ?_ ?_
  · unfold QuartetTree.taxa
    dsimp only
    decide
  · unfold QuartetTree.taxa
    dsimp only
    decide
  · intro h
    have := congrArg Subtype.val h
    dsimp only at this
    exact absurd this (by decide)
  · rw [(hvals ⟨_, h₀⟩).2.1 rfl, (hvals ⟨_, h₀'⟩).2.2 rfl]

/-- **Example 7**, on the Challenge's definitions. -/
theorem example7_fig17 :
    let θ := fig17Params (-Real.log (48 / 49)) (-Real.log (48 / 49)) (1 / 2)
    fig17Network.IsBinaryNetwork ∧ fig17Network.graph.IsLevelOne ∧
      fig17Network.IsLSA Set.univ fig17Network.root ∧ fig17Network.IsMetric θ ∧
      ∀ q : QuartetTree (Fin 4),
        (q.1 = {{0, 1}, {2, 3}} → fig17Network.cf θ q = 33 / 98) ∧
        (q.1 = {{0, 2}, {1, 3}} → fig17Network.cf θ q = 32 / 98) ∧
        (q.1 = {{0, 3}, {1, 2}} → fig17Network.cf θ q = 33 / 98) := by
  intro θ
  have a₁ : Real.log (48 / 49) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hQ := fig17_isLSAQuartet (neg_pos.mpr a₁) (neg_pos.mpr a₁) (γ := 1 / 2) (by norm_num)
    (by norm_num)
  obtain ⟨hNb, h1, hl, hm⟩ := properties_of_toRooted hQ fig17Network_toRooted
    (fig17Params_toMetric _ _ _)
  refine ⟨hNb, h1, hl, hm, fun q => ?_⟩
  have e := (example7 distinct4_fin4 hQ _ rfl rfl (inducesNetwork_q17 hQ)).1
  simp only [CF, Prod.mk.injEq] at e
  have hcf : ∀ q, fig17Network.cf θ q = Banos2019.cf (q17 (0 : Fin 4) 1 2)
      (q17Metric (fig17Len (-Real.log (48 / 49)) (-Real.log (48 / 49))) (1 / 2))
      (quartetTreeEquiv q) :=
    fun q => by rw [fig17Network.cf_eq, Function.comp_apply, fig17Network_toRooted,
      fig17Params_toMetric]
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_⟩
  · rw [hcf, ← e.1]
    exact congrArg _ (Subtype.ext hq)
  · rw [hcf, ← e.2.1]
    exact congrArg _ (Subtype.ext hq)
  · rw [hcf, ← e.2.2]
    exact congrArg _ (Subtype.ext hq)

/-! ### The cycles of `N⁻` and `Ñ` -/

/-- **`N⁻` of Figure 17 has a 4-cycle.** -/
theorem unrooted_q17_fourCycle {M : RootedNetwork (Fin 9) (Fin 9) (Fin 4)}
    (hM : IsBinaryRootedNetwork M) (hX : Nontrivial (Fin 4)) (h : M = q17 (0 : Fin 4) 1 2) :
    ∃ C, IsCycle (unrooted M hM hX).graph C ∧ C.ncard = 4 := by
  subst h
  have hQ := fig17_isLSAQuartet (t₁ := 1) (t₂ := 1) one_pos one_pos (γ := 1 / 2) (by norm_num)
    (by norm_num)
  obtain ⟨k, hk⟩ := inducesCycleType_q17 (a := (0 : Fin 4)) (b := 1) (c := 2)
  obtain ⟨C, hC, h4, -⟩ := (inducesCycleType_iff hQ 4 k).mp ⟨_, _, hk⟩
  exact ⟨C, hC, h4⟩

/-- **Every cycle of `N⁻` of Figure 18 has three edges**: it comes from the cycle of `q18`, of four
edges, through the root, which `N⁻` suppresses. -/
theorem unrooted_q18_ncard {M : RootedNetwork (Fin 9) (Fin 9) (Fin 4)}
    (hM : IsBinaryRootedNetwork M) (hX : Nontrivial (Fin 4))
    (h : M = q18 (0 : Fin 4) 1 2) {C : Set _}
    (hC : IsCycle (unrooted M hM hX).graph C) : C.ncard = 3 := by
  subst h
  have hQ := fig18_isLSAQuartet (t₁ := 1) (t₂ := 1) (t₃ := 1) (t₄ := 1) one_pos one_pos one_pos
    one_pos (γ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨⟨v, ⟨hv, h₁, h₂, hne, hd₁, hd₂, ht₁, ht₂⟩, -⟩, hin, -⟩ :=
    lemma3_unrooted hQ.binary hQ.levelOne hQ.nontrivial hC
  obtain ⟨C', v', hC', -, -, hn, -⟩ := (inducesCycleType_iff hQ C.ncard _).mpr ⟨C, hC, rfl, v,
    ⟨h₁, hin v hv h₁ hd₁ ht₁, h₂, hin v hv h₂ hd₂ ht₂, hne, hd₁, hd₂, ht₁, ht₂⟩, rfl⟩
  rw [q18_cycle_eq hC'] at hn
  have h8 : (q18 (0 : Fin 4) 1 2).root ∈ cycleNodes (q18 (0 : Fin 4) 1 2).graph ↑q18Cycle :=
    ⟨8, by decide, Or.inl rfl⟩
  rw [ite_eq_left h8, Set.ncard_coe_finset] at hn
  rw [← hn]
  rfl

theorem nontrivial_fin4 : Nontrivial (Fin 4) := ⟨⟨0, 1, by decide⟩⟩

/-- **`N⁻` of Figure 17 has a 4-cycle, `N⁻` of Figure 18 none**, on the Challenge's definitions. -/
theorem fig17_fig18_unrooted :
    (∃ C, fig17Network.unrooted.graph.IsCycle C ∧ C.ncard = 4) ∧
      ¬ ∃ C, fig18Network.unrooted.graph.IsCycle C ∧ C.ncard = 4 := by
  have hX := nontrivial_fin4
  have hb₁₇ : IsBinaryRootedNetwork fig17Network.toRooted := by
    rw [fig17Network_toRooted]
    exact (fig17_isLSAQuartet (t₁ := 1) (t₂ := 1) one_pos one_pos (γ := 1 / 2) (by norm_num)
      (by norm_num)).binary
  have hb₁₈ : IsBinaryRootedNetwork fig18Network.toRooted := by
    rw [fig18Network_toRooted]
    exact (fig18_isLSAQuartet (t₁ := 1) (t₂ := 1) (t₃ := 1) (t₄ := 1) one_pos one_pos one_pos
      one_pos (γ := 1 / 2) (by norm_num) (by norm_num)).binary
  obtain ⟨u₁₇⟩ := fig17Network.nonempty_sdIso_unrooted hb₁₇
  obtain ⟨u₁₈⟩ := fig18Network.nonempty_sdIso_unrooted hb₁₈
  simp only [Digraph.isCycle_iff]
  refine ⟨?_, fun h => ?_⟩
  · exact (u₁₇.exists_isCycle_ncard_iff 4).mpr
      (unrooted_q17_fourCycle hb₁₇ hX fig17Network_toRooted)
  · obtain ⟨C, hC, h4⟩ := (u₁₈.exists_isCycle_ncard_iff 4).mp h
    rw [unrooted_q18_ncard hb₁₈ hX fig18Network_toRooted hC] at h4
    exact absurd h4 (by norm_num)

/-- **The networks `Ñ` of Figures 17 and 18 are not isomorphic**, on the Challenge's definitions. -/
theorem fig17_fig18_tilde :
    ¬ Nonempty (SDIso fig18Network.unrooted.tilde fig17Network.unrooted.tilde) := by
  rintro ⟨ι⟩
  have hX := nontrivial_fin4
  have hb₁₇ : IsBinaryRootedNetwork fig17Network.toRooted := by
    rw [fig17Network_toRooted]
    exact (fig17_isLSAQuartet (t₁ := 1) (t₂ := 1) one_pos one_pos (γ := 1 / 2) (by norm_num)
      (by norm_num)).binary
  have hb₁₈ : IsBinaryRootedNetwork fig18Network.toRooted := by
    rw [fig18Network_toRooted]
    exact (fig18_isLSAQuartet (t₁ := 1) (t₂ := 1) (t₃ := 1) (t₄ := 1) one_pos one_pos one_pos
      one_pos (γ := 1 / 2) (by norm_num) (by norm_num)).binary
  have h1₁₇ : IsLevelOne fig17Network.toRooted.graph := by
    rw [fig17Network_toRooted]
    exact q17_isLevelOne
  obtain ⟨u₁₇⟩ := fig17Network.nonempty_sdIso_unrooted hb₁₇
  obtain ⟨u₁₈⟩ := fig18Network.nonempty_sdIso_unrooted hb₁₈
  -- `Ñ` of Figure 17 to `Ñ` of Figure 18, in the library's terms
  let J := ((fig17Network.unrooted.tildeIso.trans u₁₇.tildeNetwork).symm.trans
    ι.toLib.symm).trans (fig18Network.unrooted.tildeIso.trans u₁₈.tildeNetwork)
  -- a cycle of `Ñ` of Figure 17, from the 4-cycle of `N⁻`
  obtain ⟨C, hC, h4⟩ := unrooted_q17_fourCycle hb₁₇ hX fig17Network_toRooted
  obtain ⟨C₁, hC₁, -⟩ := exists_isCycle_tilde_of_big
    (isUnrootedLevelOne_unrooted hb₁₇ h1₁₇ hX) hC h4.ge
  -- its image is a cycle of `Ñ` of Figure 18, which comes from a cycle of `N⁻` of size at least
  -- four
  have hC₂ := J.isCycle_image hC₁
  obtain ⟨w, hw⟩ := hC₂.nonempty_cycleNodes
  obtain ⟨D, -, hD, hD4, -⟩ := exists_isCycle_big_of_mem_cycleNodes_tilde hC₂ hw
  rw [unrooted_q18_ncard hb₁₈ hX fig18Network_toRooted hD] at hD4
  exact absurd hD4 (by norm_num)

end Banos2019.Model
