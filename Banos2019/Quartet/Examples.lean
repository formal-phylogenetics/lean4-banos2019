module

public import Banos2019.Quartet.Reduction
public import Banos2019.Quartet.Fig17
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The examples of Sections 5, 6 and 7 (Baños 2019, Examples 2–7)

The unrooted quartet networks of Figures 15–18, with taxa `a, b, c, d` at the nodes `0, 1, 2, 3`, as
metric semidirected networks on `Fin 8` nodes and `Fin 8` edges. An edge length `t i` of a figure is the
length of the edge so labelled; the other edges (pendant edges, and hybrid edges the figure does not
label) have arbitrary lengths `ℓ`. The concordance factors of an unrooted quartet network are those of
any LSA quartet network inducing it (Proposition 5), so each example is stated for every LSA quartet
network whose metric unrooted network is isomorphic to the figure.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The leaves `a, b, c, d` at the nodes `0, 1, 2, 3`. -/
def figLeaf (a b c : X) (x : X) : Fin 8 := if x = a then 0 else if x = b then 1 else if x = c then 2 else 3

/-- A semidirected network on `Fin 8` given by the ends of its edges, its two hybrid edges `6` and `7`,
and the leaves `a, b, c, d` at `0, 1, 2, 3`. -/
def figNet (src tgt : Fin 8 → Fin 8) (a b c : X) : SemidirectedNetwork (Fin 8) (Fin 8) X :=
  ⟨⟨src, tgt⟩, fun e => e = 6 ∨ e = 7, figLeaf a b c⟩

/-- The parameters of a figure: the lengths `len`, inheritance probability `γ` on the hybrid edge `6`
and `1 - γ` on `7`. -/
def figMetric (len : Fin 8 → ℝ) (γ : ℝ) : MetricData (Fin 8) :=
  ⟨len, fun e => if e = 6 then γ else if e = 7 then 1 - γ else 1⟩

/-- **Figure 15**, a `2₂`-cycle: `a, b` at node 4, which joins node 5 by the edge `t₁` (edge 4); the
hybrid edges from 5 to the hybrid node 6, of lengths `t₄` (edge 6, inheritance `γ`) and `t₃` (edge 7);
node 6 joins node 7, with `c, d`, by `t₂` (edge 5). -/
def fig15 (a b c : X) : SemidirectedNetwork (Fin 8) (Fin 8) X :=
  figNet ![4, 4, 7, 7, 4, 6, 5, 5] ![0, 1, 2, 3, 5, 7, 6, 6] a b c

/-- **Figure 16**, a `3₁`-cycle: `a, b` at node 4, which joins node 5 by `t₁` (edge 4); node 5 joins
node 6, with `c`, by `t₂` (edge 5); the hybrid edges from 6 (edge 6, `γ`) and 5 (edge 7) enter the
hybrid node 7, above `d`. -/
def fig16 (a b c : X) : SemidirectedNetwork (Fin 8) (Fin 8) X :=
  figNet ![4, 4, 6, 7, 4, 5, 6, 5] ![0, 1, 2, 3, 5, 6, 7, 7] a b c

/-- **Figure 17**, a 4-cycle: the nodes 4, 5, 6, 7 of the cycle carry `a, b, c, d`; node 4 joins 7 by
`t₁` (edge 4) and 5 by `t₂` (edge 5); the hybrid edges from 5 (edge 6, `γ`) and 7 (edge 7) enter the
hybrid node 6, above `c`. -/
def fig17 (a b c : X) : SemidirectedNetwork (Fin 8) (Fin 8) X :=
  figNet ![4, 5, 6, 7, 4, 4, 5, 7] ![0, 1, 2, 3, 7, 5, 6, 6] a b c

/-- **Figure 18**, a `3₂`-cycle: `a, b` at node 4, below the hybrid node 5 by `t₁` (edge 4); node 7, with
`d`, joins node 6, with `c`, by `t₃` (edge 5); the hybrid edges from 7 (edge 6, length `t₄`, `γ`) and 6
(edge 7, length `t₂`) enter 5. -/
def fig18 (a b c : X) : SemidirectedNetwork (Fin 8) (Fin 8) X :=
  figNet ![4, 4, 6, 7, 5, 7, 7, 6] ![0, 1, 2, 3, 4, 6, 5, 5] a b c

variable {V E : Type*} [Fintype V] [Fintype E]

/-- `Q⊕` induces the metric unrooted network `(G, μ)`. -/
def InducesNetwork {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    (G : SemidirectedNetwork (Fin 8) (Fin 8) X) (μ : MetricData (Fin 8)) : Prop :=
  Nonempty (SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ) G μ)

/-! ### The parameters of a figure and its rootings -/

omit [Fintype V] [DecidableEq X] in
/-- The lengths of a figure that an LSA quartet network induces are positive. -/
theorem InducesNetwork.len_pos {Q : RootedNetwork V E X} {θ : MetricData E} {hQ : IsLSAQuartet Q θ}
    {G : SemidirectedNetwork (Fin 8) (Fin 8) X} {len : Fin 8 → ℝ} {γ : ℝ}
    (hiso : InducesNetwork hQ G (figMetric len γ)) (i : Fin 8) : 0 < len i := by
  obtain ⟨φ⟩ := hiso
  have h := φ.length (φ.edge.symm i)
  rw [Equiv.apply_symm_apply] at h
  show 0 < (figMetric len γ).length i
  rw [h]
  simp only [unrootedMetric, semidirectedMetric]
  split_ifs
  · exact add_pos (hQ.metric.2 _) (hQ.metric.2 _)
  · exact hQ.metric.2 _

/-- The inheritance probability `γ` of the hybrid edge `6` of a figure that an LSA quartet network
induces is in `(0, 1)`: it is that of a hybrid edge of the network. -/
theorem InducesNetwork.inheritance_mem_Ioo {Q : RootedNetwork V E X} {θ : MetricData E}
    {hQ : IsLSAQuartet Q θ} {src tgt : Fin 8 → Fin 8} {a b c : X} {len : Fin 8 → ℝ} {γ : ℝ}
    (hiso : InducesNetwork hQ (figNet src tgt a b c) (figMetric len γ)) : 0 < γ ∧ γ < 1 := by
  obtain ⟨φ⟩ := hiso
  have hP := hQ.binary.1
  have : Nonempty X := hQ.nontrivial.to_nonempty
  set e := φ.edge.symm 6
  have hd : hQ.unrooted.IsDirected e := by
    rw [← φ.isDirected_iff, Equiv.apply_symm_apply]
    exact Or.inl rfl
  have hh : Q.IsHybridArc e.1.1 :=
    (belowNetwork_isHybridArc_iff (hl := lsa_mem_ancestralVertices hP Set.univ_nonempty)
      (hleaf := fun _ hx => (lsa_spec hP Set.univ Set.univ_nonempty).1.reaches_leaf hP hx)
      hP (lsa_spec hP _ _).1 e.1).1 hd
  have hγ := φ.inheritance e hd
  rw [Equiv.apply_symm_apply] at hγ
  have hγ' : γ = θ.inheritance e.1.1 := hγ
  rw [hγ']
  exact Banos2019.inheritance_mem_Ioo hQ.binary hQ.metric hh

omit [Fintype X] in
theorem figLeaf_castSucc (a b c x : X) : (figLeaf a b c x).castSucc = quartetLeaf9 a b c x := by
  simp only [figLeaf, quartetLeaf9]
  split_ifs <;> rfl

/-- **The metric unrooted network of `q17` is Figure 17.** -/
theorem inducesNetwork_q17 {a b c d : X} (h : Distinct4 a b c d) {len : Fin 8 → ℝ} {γ : ℝ}
    (hQ : IsLSAQuartet (q17 a b c) (q17Metric len γ)) :
    InducesNetwork hQ (fig17 a b c) (figMetric len γ) := by
  have hP := hQ.binary.1
  have hB := hQ.binary.2
  have hXn := hQ.nontrivial
  have : Nonempty X := hXn.to_nonempty
  have hl : lsa hP Set.univ Set.univ_nonempty = 8 :=
    IsLeastStableAncestor.unique hP (lsa_spec hP _ _) (q17_isLSANetwork h)
  have hr : (rootTreeArc hP hB hXn).1 = 8 := by
    obtain ⟨hs, ht⟩ := rootTreeArc_spec hP hB hXn
    have hs' : q17Src (rootTreeArc hP hB hXn).1 = 8 := by
      rw [← hl]
      exact congrArg Subtype.val hs
    have ht' : (q17 a b c).IsTreeArc (rootTreeArc hP hB hXn).1 :=
      (belowNetwork_isTreeArc_iff (hl := lsa_mem_ancestralVertices hP Set.univ_nonempty)
        (hleaf := fun _ hx => (lsa_spec hP Set.univ Set.univ_nonempty).1.reaches_leaf hP hx)
        hP (lsa_spec hP _ _).1 _).1 ht
    rw [q17_isTreeArc_iff] at ht'
    have key : ∀ r : Fin 9, q17Src r = 8 → ¬ (r = 6 ∨ r = 7) → r = 8 := by decide
    exact key _ hs' ht'
  -- the nodes and the edges of `Q⁻`: those of `q17` but the root and the edge `8`
  have hv : ∀ v : SemidirectedVertex hP hXn, v.1.1 ≠ Fin.last 8 := fun v hv => v.2 (Subtype.ext
    (show v.1.1 = lsa hP Set.univ Set.univ_nonempty by rw [hv]; exact hl.symm))
  have he : ∀ e : SemidirectedArc hP hB hXn, e.1.1 ≠ Fin.last 8 := fun e he =>
    e.2 (Subtype.ext (by rw [he]; exact hr.symm))
  let vert : SemidirectedVertex hP hXn ≃ Fin 8 :=
    { toFun := fun v => v.1.1.castPred (hv v)
      invFun := fun i => ⟨⟨i.castSucc, hl ▸ hP.root_reaches _, mem_ancestralVertices_univ hP _⟩,
        fun hi => Fin.castSucc_ne_last i (by
          have := congrArg (fun v => v.1) hi
          simp only at this
          rw [this]
          exact hl)⟩
      left_inv := fun v => Subtype.ext (Subtype.ext (Fin.castSucc_castPred _ _))
      right_inv := fun i => by simp }
  let edge : SemidirectedArc hP hB hXn ≃ Fin 8 :=
    { toFun := fun e => e.1.1.castPred (he e)
      invFun := fun i => ⟨⟨i.castSucc, hl ▸ hP.root_reaches _, mem_ancestralVertices_univ hP _⟩,
        fun hi => Fin.castSucc_ne_last i (by
          have := congrArg (fun e => e.1) hi
          simp only at this
          rw [this]
          exact hr)⟩
      left_inv := fun e => Subtype.ext (Subtype.ext (Fin.castSucc_castPred _ _))
      right_inv := fun i => by simp }
  have hvert : ∀ v, (vert v).castSucc = v.1.1 := fun v => Fin.castSucc_castPred _ (hv v)
  have hedge : ∀ e, (edge e).castSucc = e.1.1 := fun e => Fin.castSucc_castPred _ (he e)
  -- the ends of the edges of `Q⁻`: the edge `7` from the root is merged into one from `7`
  have hroot : ∀ e : SemidirectedArc hP hB hXn,
      (lsaPlus hP hXn).graph.source e.1 = (lsaPlus hP hXn).root ↔ q17Src e.1.1 = 8 := by
    intro e
    rw [← hl]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hsrc : ∀ e, (hQ.unrooted.graph.source e).1.1 =
      if q17Src e.1.1 = 8 then 7 else q17Src e.1.1 := by
    intro e
    show ((unrootAt (lsaPlus hP hXn) (lsaPlus_isPhylogenetic hP hXn)
      (rootTreeArc hP hB hXn)).graph.source e).1.1 = _
    simp only [unrootAt]
    by_cases h8 : q17Src e.1.1 = 8
    · rw [dite_eq_left ((hroot e).2 h8), ite_eq_left h8]
      show q17Tgt (rootTreeArc hP hB hXn).1 = 7
      rw [hr]
      rfl
    · rw [dite_eq_right (fun h' => h8 ((hroot e).1 h')), ite_eq_right h8]
      rfl
  have htgt : ∀ e, (hQ.unrooted.graph.target e).1.1 = q17Tgt e.1.1 := fun e => rfl
  have hdir : ∀ e, hQ.unrooted.IsDirected e ↔ e.1.1 = 6 ∨ e.1.1 = 7 := fun e =>
    ((belowNetwork_isHybridArc_iff (hl := lsa_mem_ancestralVertices hP Set.univ_nonempty)
      (hleaf := fun _ hx => (lsa_spec hP Set.univ Set.univ_nonempty).1.reaches_leaf hP hx)
      hP (lsa_spec hP _ _).1 e.1).trans (q17_isHybridArc_iff e.1.1))
  -- the edge `4` of Figure 17 is the edge `7 → 4` of `q17` read the other way
  have fjoin : ∀ j : Fin 8,
      (((fig17 a b c).graph.source j).castSucc =
          (if q17Src j.castSucc = 8 then 7 else q17Src j.castSucc) ∧
        ((fig17 a b c).graph.target j).castSucc = q17Tgt j.castSucc) ∨
      (((fig17 a b c).graph.source j).castSucc = q17Tgt j.castSucc ∧
        ((fig17 a b c).graph.target j).castSucc =
          (if q17Src j.castSucc = 8 then 7 else q17Src j.castSucc)) := by
    show ∀ j : Fin 8,
      (((![4, 5, 6, 7, 4, 4, 5, 7] : Fin 8 → Fin 8) j).castSucc =
          (if q17Src j.castSucc = 8 then 7 else q17Src j.castSucc) ∧
        ((![0, 1, 2, 3, 7, 5, 6, 6] : Fin 8 → Fin 8) j).castSucc = q17Tgt j.castSucc) ∨
      (((![4, 5, 6, 7, 4, 4, 5, 7] : Fin 8 → Fin 8) j).castSucc = q17Tgt j.castSucc ∧
        ((![0, 1, 2, 3, 7, 5, 6, 6] : Fin 8 → Fin 8) j).castSucc =
          (if q17Src j.castSucc = 8 then 7 else q17Src j.castSucc))
    decide
  have fdir : ∀ j : Fin 8, j = 6 ∨ j = 7 →
      ((fig17 a b c).graph.source j).castSucc =
          (if q17Src j.castSucc = 8 then 7 else q17Src j.castSucc) ∧
        ((fig17 a b c).graph.target j).castSucc = q17Tgt j.castSucc := by
    show ∀ j : Fin 8, j = 6 ∨ j = 7 →
      ((![4, 5, 6, 7, 4, 4, 5, 7] : Fin 8 → Fin 8) j).castSucc =
          (if q17Src j.castSucc = 8 then 7 else q17Src j.castSucc) ∧
        ((![0, 1, 2, 3, 7, 5, 6, 6] : Fin 8 → Fin 8) j).castSucc = q17Tgt j.castSucc
    decide
  have hS : ∀ e, (vert (hQ.unrooted.graph.source e)).castSucc =
      if q17Src (edge e).castSucc = 8 then 7 else q17Src (edge e).castSucc := fun e => by
    rw [hvert, hsrc, hedge]
  have hT : ∀ e, (vert (hQ.unrooted.graph.target e)).castSucc = q17Tgt (edge e).castSucc :=
    fun e => by rw [hvert, htgt, hedge]
  refine ⟨⟨⟨vert, edge, fun e => ?_, fun e => ?_, fun e hd => ?_, fun x => ?_⟩, fun e => ?_,
    fun e _ => ?_⟩⟩
  · rw [hdir, ← hedge e]
    show edge e = 6 ∨ edge e = 7 ↔ _
    generalize edge e = j
    revert j
    decide
  · rcases fjoin (edge e) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨Fin.castSucc_injective _ (by rw [h₁, hS]),
        Fin.castSucc_injective _ (by rw [h₂, hT])⟩
    · exact Or.inr ⟨Fin.castSucc_injective _ (by rw [h₁, hT]),
        Fin.castSucc_injective _ (by rw [h₂, hS])⟩
  · have hj : edge e = 6 ∨ edge e = 7 := by
      rw [hdir, ← hedge e] at hd
      rcases hd with h' | h'
      · exact Or.inl (Fin.castSucc_injective _ h')
      · exact Or.inr (Fin.castSucc_injective _ h')
    obtain ⟨h₁, h₂⟩ := fdir _ hj
    exact ⟨Fin.castSucc_injective _ (by rw [h₁, hS]), Fin.castSucc_injective _ (by rw [h₂, hT])⟩
  · apply Fin.castSucc_injective
    rw [hvert]
    exact figLeaf_castSucc a b c x
  · simp only [figMetric, unrootedMetric, semidirectedMetric]
    rw [hr, ← hedge e]
    split_ifs with h8
    · have h8' : q17Src (edge e).castSucc = 8 := by rw [hedge e]; exact (hroot e).1 h8
      have h7 : edge e = 7 := by
        have key : ∀ j : Fin 8, q17Src j.castSucc = 8 → j = 7 := by decide
        exact key _ h8'
      rw [h7]
      simp [q17Metric]
    · have h8' : q17Src (edge e).castSucc ≠ 8 := fun h' => h8 ((hroot e).2 (by rwa [← hedge e]))
      generalize edge e = j at h8'
      fin_cases j <;> first | exact absurd (by decide) h8' | simp [q17Metric]
  · show (figMetric len γ).inheritance (edge e) = (q17Metric len γ).inheritance e.1.1
    rw [← hedge e]
    generalize edge e = j
    fin_cases j <;> simp [figMetric, q17Metric]

/-- **Example 2** (`ex:2_2`): the concordance factors of the `2₂`-cycle of Figure 15, with `xᵢ = e^{-tᵢ}`:
`CF_{AB|CD} = (1-γ)²(1 - ⅔x₁x₂x₃) + 2γ(1-γ)(1 - ⅔x₁x₂) + γ²(1 - ⅔x₁x₂x₄)` and
`CF_{AC|BD} = CF_{AD|BC} = (1-γ)²(⅓x₁x₂x₃) + 2γ(1-γ)(⅓x₁x₂) + γ²(⅓x₁x₂x₄)`. -/
theorem example2 {a b c d : X} (h : Distinct4 a b c d) {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) (len : Fin 8 → ℝ) (γ : ℝ)
    (hiso : InducesNetwork hQ (fig15 a b c) (figMetric len γ)) :
    let x₁ := Real.exp (-len 4); let x₂ := Real.exp (-len 5); let x₃ := Real.exp (-len 7)
    let x₄ := Real.exp (-len 6)
    CF Q θ a b c d h =
      ((1 - γ) ^ 2 * (1 - 2 / 3 * (x₁ * x₂ * x₃)) + 2 * γ * (1 - γ) * (1 - 2 / 3 * (x₁ * x₂)) +
          γ ^ 2 * (1 - 2 / 3 * (x₁ * x₂ * x₄)),
        (1 - γ) ^ 2 * (1 / 3 * (x₁ * x₂ * x₃)) + 2 * γ * (1 - γ) * (1 / 3 * (x₁ * x₂)) +
          γ ^ 2 * (1 / 3 * (x₁ * x₂ * x₄)),
        (1 - γ) ^ 2 * (1 / 3 * (x₁ * x₂ * x₃)) + 2 * γ * (1 - γ) * (1 / 3 * (x₁ * x₂)) +
          γ ^ 2 * (1 / 3 * (x₁ * x₂ * x₄))) := by
  sorry

/-- **Example 3** (`ex:3_1`): the concordance factors of the `3₁`-cycle of Figure 16:
`CF_{AB|CD} = (1-γ)(1 - ⅔x₁) + γ(1 - ⅔x₁x₂)`, `CF_{AC|BD} = CF_{AD|BC} = (1-γ)(⅓x₁) + γ(⅓x₁x₂)`. -/
theorem example3 {a b c d : X} (h : Distinct4 a b c d) {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) (len : Fin 8 → ℝ) (γ : ℝ)
    (hiso : InducesNetwork hQ (fig16 a b c) (figMetric len γ)) :
    let x₁ := Real.exp (-len 4); let x₂ := Real.exp (-len 5)
    CF Q θ a b c d h =
      ((1 - γ) * (1 - 2 / 3 * x₁) + γ * (1 - 2 / 3 * (x₁ * x₂)),
        (1 - γ) * (1 / 3 * x₁) + γ * (1 / 3 * (x₁ * x₂)),
        (1 - γ) * (1 / 3 * x₁) + γ * (1 / 3 * (x₁ * x₂))) := by
  sorry

/-- **Example 4** (`ex:4_1`): the concordance factors of the 4-cycle of Figure 17:
`CF_{AB|CD} = (1-γ)(1 - ⅔x₁) + γ(⅓x₂)`, `CF_{AC|BD} = (1-γ)(⅓x₁) + γ(⅓x₂)`,
`CF_{AD|BC} = (1-γ)(⅓x₁) + γ(1 - ⅔x₂)`. -/
theorem example4 {a b c d : X} (h : Distinct4 a b c d) {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) (len : Fin 8 → ℝ) (γ : ℝ)
    (hiso : InducesNetwork hQ (fig17 a b c) (figMetric len γ)) :
    let x₁ := Real.exp (-len 4); let x₂ := Real.exp (-len 5)
    CF Q θ a b c d h =
      ((1 - γ) * (1 - 2 / 3 * x₁) + γ * (1 / 3 * x₂), (1 - γ) * (1 / 3 * x₁) + γ * (1 / 3 * x₂),
        (1 - γ) * (1 / 3 * x₁) + γ * (1 - 2 / 3 * x₂)) := by
  intro x₁ x₂
  -- the decidable equality of the statement is the classical one
  obtain rfl : ‹DecidableEq X› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  -- the rooting `q17` of Figure 17, with the same concordance factors (Proposition 5)
  have hX := hQ.card_taxa
  have hlen := hiso.len_pos
  obtain ⟨hγ₀, hγ₁⟩ := hiso.inheritance_mem_Ioo
  have hQ' := isLSAQuartet_q17 hX h hlen hγ₀ hγ₁
  have hcf := proposition5 hQ hQ' ⟨hiso.some.trans (inducesNetwork_q17 h hQ').some.symm⟩
  -- Lemma 10 at the 4-cycle of `q17`, with the hybrid edges `6` (`γ`) and `7`
  obtain ⟨k, hct⟩ := inducesCycleType_q17 (a := a) (b := b) (c := c)
  have hL := fun q => lemma10 hQ' (Or.inl ⟨k, hct⟩) (h₁ := 6) (h₂ := 7) (by decide) rfl rfl q
  -- the two trees `Q₁⊕`, `Q₂⊕` (equation (1))
  obtain ⟨s₁, s₂, s₃⟩ := cf_deleteArc_q17_seven hX h hlen hγ₀ hγ₁
  obtain ⟨u₁, u₂, u₃⟩ := cf_deleteArc_q17_six hX h hlen hγ₀ hγ₁
  have hinh : (q17Metric len γ).inheritance 6 = γ := rfl
  show (cf Q θ _, cf Q θ _, cf Q θ _) = _
  rw [hcf, hL, hL, hL, hinh]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have key : γ * cf (deleteArc (q17 a b c) 7) (deleteArcMetric (q17 a b c) 7 (q17Metric len γ))
          (quartetTree a b c d h) + (1 - γ) * cf (deleteArc (q17 a b c) 6)
          (deleteArcMetric (q17 a b c) 6 (q17Metric len γ)) (quartetTree a b c d h) =
        (1 - γ) * (1 - 2 / 3 * x₁) + γ * (1 / 3 * x₂) := by
      rw [s₂, u₁]; ring
    convert key using 5
  · have key : γ * cf (deleteArc (q17 a b c) 7) (deleteArcMetric (q17 a b c) 7 (q17Metric len γ))
          (quartetTree a c b d (distinct4_acbd h)) + (1 - γ) * cf (deleteArc (q17 a b c) 6)
          (deleteArcMetric (q17 a b c) 6 (q17Metric len γ)) (quartetTree a c b d (distinct4_acbd h)) =
        (1 - γ) * (1 / 3 * x₁) + γ * (1 / 3 * x₂) := by
      rw [s₃, u₂]; ring
    convert key using 5
  · have key : γ * cf (deleteArc (q17 a b c) 7) (deleteArcMetric (q17 a b c) 7 (q17Metric len γ))
          (quartetTree a d b c (distinct4_adbc h)) + (1 - γ) * cf (deleteArc (q17 a b c) 6)
          (deleteArcMetric (q17 a b c) 6 (q17Metric len γ)) (quartetTree a d b c (distinct4_adbc h)) =
        (1 - γ) * (1 / 3 * x₁) + γ * (1 - 2 / 3 * x₂) := by
      rw [s₁, u₃]; ring
    convert key using 5

/-- **Example 5** (`ex:3_2`): the concordance factors of the `3₂`-cycle of Figure 18:
`CF_{AB|CD} = (1-γ)²(1 - ⅔x₁x₂) + 2γ(1-γ)(1 - x₁ + ⅓x₁x₃) + γ²(1 - ⅔x₁x₄)` and
`CF_{AC|BD} = CF_{AD|BC} = (1-γ)²(⅓x₁x₂) + γ(1-γ)x₁(1 - ⅓x₃) + γ²(⅓x₁x₄)`. -/
theorem example5 {a b c d : X} (h : Distinct4 a b c d) {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) (len : Fin 8 → ℝ) (γ : ℝ)
    (hiso : InducesNetwork hQ (fig18 a b c) (figMetric len γ)) :
    let x₁ := Real.exp (-len 4); let x₂ := Real.exp (-len 7); let x₃ := Real.exp (-len 5)
    let x₄ := Real.exp (-len 6)
    CF Q θ a b c d h =
      ((1 - γ) ^ 2 * (1 - 2 / 3 * (x₁ * x₂)) + 2 * γ * (1 - γ) * (1 - x₁ + 1 / 3 * (x₁ * x₃)) +
          γ ^ 2 * (1 - 2 / 3 * (x₁ * x₄)),
        (1 - γ) ^ 2 * (1 / 3 * (x₁ * x₂)) + γ * (1 - γ) * x₁ * (1 - 1 / 3 * x₃) +
          γ ^ 2 * (1 / 3 * (x₁ * x₄)),
        (1 - γ) ^ 2 * (1 / 3 * (x₁ * x₂)) + γ * (1 - γ) * x₁ * (1 - 1 / 3 * x₃) +
          γ ^ 2 * (1 / 3 * (x₁ * x₄))) := by
  sorry

/-- **Example 6** (`ex::cpbc`): the `3₂`-cycle of Figure 18 with `γ = 1/2`, `t₁ = t₂ = -log(6/7)`,
`t₃ = -log(1/14)`, `t₄ = -log(13/14)` has `CF = (32/98, 33/98, 33/98)`: it is not treelike. -/
theorem example6 {a b c d : X} (h : Distinct4 a b c d) {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) (len : Fin 8 → ℝ) (h₁ : len 4 = -Real.log (6 / 7))
    (h₂ : len 7 = -Real.log (6 / 7)) (h₃ : len 5 = -Real.log (1 / 14))
    (h₄ : len 6 = -Real.log (13 / 14))
    (hiso : InducesNetwork hQ (fig18 a b c) (figMetric len (1 / 2))) :
    CF Q θ a b c d h = (32 / 98, 33 / 98, 33 / 98) := by
  -- equation (9) of Example 5, with `x₁ = x₂ = 6/7`, `x₃ = 1/14`, `x₄ = 13/14`
  have e := example5 h hQ len (1 / 2) hiso
  simp only [h₁, h₂, h₃, h₄, neg_neg] at e
  rw [e, Real.exp_log (by norm_num), Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
  norm_num

/-- **Example 7** (`ex::cpbc4`): the 4-cycle of Figure 17 with `γ = 1/2` and `t₁ = t₂ = -log(48/49)` has
the concordance factors of Example 6, up to the labels of the taxa: by equation (8) its concordance
factors are `(33/98, 32/98, 33/98)`, and with `b` and `c` exchanged, `(32/98, 33/98, 33/98)`. The paper
prints `CF_{AB|CD} = 32/98, CF_{AC|BD} = 33/98, CF_{AD|BC} = 33/98` for the labels of Figure 17, which
are the values for the exchanged labels. -/
theorem example7 {a b c d : X} (h : Distinct4 a b c d) {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) (len : Fin 8 → ℝ) (h₁ : len 4 = -Real.log (48 / 49))
    (h₂ : len 5 = -Real.log (48 / 49))
    (hiso : InducesNetwork hQ (fig17 a b c) (figMetric len (1 / 2))) :
    CF Q θ a b c d h = (33 / 98, 32 / 98, 33 / 98) ∧
      CF Q θ a c b d (distinct4_acbd h) = (32 / 98, 33 / 98, 33 / 98) := by
  -- equation (8) of Example 4, with `x₁ = x₂ = 48/49`
  have e := example4 h hQ len (1 / 2) hiso
  simp only [h₁, h₂, neg_neg] at e
  rw [Real.exp_log (by norm_num)] at e
  norm_num at e
  refine ⟨by rw [e]; norm_num, ?_⟩
  -- the same three quartet trees, `ac|bd`, `ab|cd`, `ad|cb`
  have hadcb : quartetTree a d c b (distinct4_adbc (distinct4_acbd h)) =
      quartetTree a d b c (distinct4_adbc h) := Subtype.ext (by
    simp only [quartetTree]
    rw [Finset.pair_comm c b])
  simp only [CF, Prod.mk.injEq] at e ⊢
  rw [hadcb, e.1, e.2.1, e.2.2]
  norm_num

end Banos2019
