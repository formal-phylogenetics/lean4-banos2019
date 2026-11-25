module

public import Banos2019.Quartet.Reduction
public import Banos2019.Quartet.Concrete
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
  sorry

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
