module

public import Banos2019.Quartet.Normal

/-!
# Removing cycles of an LSA quartet network (proofs of Propositions 6 and 7)

The proofs of Propositions 6 and 7 remove the cycles of an LSA quartet network one at a time:
Corollary 2 contracts the `2₁`- and `2₃`-cycles, and Lemmas 9 and 10 write the concordance factors
of the network as a convex combination of those of networks with one cycle fewer. The networks the
lemmas produce (`deleteArc`, `contractRooted`) have nodes of degree two; suppressing them gives LSA
quartet networks with the same concordance factors and the remaining cycles.

* `HasCycleWithBelow Q n D`: a cycle of `Q⊕` induces an `n`-cycle of `Q⁻` with the taxa `D` below its
  hybrid node; `numRootedCycles`; `SameCyclesBut Q' Q P`: the cycles of `Q'` are those of `Q` that do not
  satisfy `P`.
* `inducesCycleType_cases`, `exists_inducesCycleType_of_isCycle`, `eq_of_inducesCycleType_three_two`:
  the cycles of an LSA quartet network.
* `exists_lsaQuartet_of_corollary2`, `exists_lsaQuartet_deleteArc`, `exists_lsaQuartet_contractRooted`:
  the networks of Corollary 2 and of Lemmas 9 and 10, as LSA quartet networks.
* `exists_fig18`: with a single cycle, a `3₂`-cycle, `Q⁻` is the network of Figure 18.
* `OrderedAsQuartetTree`, `OnSegmentOfI`: the orderings of Propositions 6 and 7, kept by convex combinations.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Cycles -/

/-- `Q⊕` has a cycle that induces an `n`-cycle of `Q⁻` with the taxa `D` below its hybrid node. -/
def HasCycleWithBelow (Q : RootedNetwork V E X) (n : ℕ) (D : Set X) : Prop :=
  ∃ C v, InducesCycleType Q C v n D.ncard ∧ {x | Q.graph.Reaches v (Q.leaf x)} = D

/-- The number of cycles of `Q⊕`. -/
def numRootedCycles (Q : RootedNetwork V E X) : ℕ := {C | IsCycle Q.graph C}.ncard

/-- The cycles of `Q'` are those of `Q` that do not satisfy `P`: they induce cycles of the same sizes,
with the same taxa below their hybrid nodes. -/
def SameCyclesBut {V' E' : Type*} (Q' : RootedNetwork V' E' X) (Q : RootedNetwork V E X)
    (P : Set E → Prop) : Prop :=
  ∀ n D, HasCycleWithBelow Q' n D ↔
    ∃ C v, ¬ P C ∧ InducesCycleType Q C v n D.ncard ∧ {x | Q.graph.Reaches v (Q.leaf x)} = D

theorem HasCycleWithBelow.of_inducesCycleType {Q : RootedNetwork V E X} {C : Set E} {v : V} {n k : ℕ}
    (h : InducesCycleType Q C v n k) : HasCycleWithBelow Q n {x | Q.graph.Reaches v (Q.leaf x)} :=
  ⟨C, v, h.2.2.2.2 ▸ h, rfl⟩

theorem HasCycleWithBelow.exists_inducesCycleType {Q : RootedNetwork V E X} {n : ℕ} {D : Set X}
    (h : HasCycleWithBelow Q n D) : ∃ C v, InducesCycleType Q C v n D.ncard := by
  obtain ⟨C, v, hC, -⟩ := h
  exact ⟨C, v, hC⟩

/-- A network without the cycles of types `n_k` for `(n, k)` in `S` keeps none after removing
cycles. -/
theorem SameCyclesBut.not_exists {V' E' : Type*} {Q' : RootedNetwork V' E' X}
    {Q : RootedNetwork V E X} {P : Set E → Prop} (h : SameCyclesBut Q' Q P) {n k : ℕ}
    (hQ : ¬ ∃ C v, InducesCycleType Q C v n k) : ¬ ∃ C v, InducesCycleType Q' C v n k := by
  rintro ⟨C, v, hC⟩
  obtain ⟨C', v', -, hC', -⟩ := (h n _).1 (HasCycleWithBelow.of_inducesCycleType hC)
  rw [hC.2.2.2.2] at hC'
  exact hQ ⟨C', v', hC'⟩

theorem finite_setOf_isCycle [Finite E] (G : DirectedMultigraph V E) :
    {C | IsCycle G C}.Finite :=
  Set.toFinite _

variable [Fintype V] [Fintype E] [Fintype X]

/-- **The cycles of an LSA quartet network** (Section 5, before Lemma 5): a cycle of `Q⊕` induces a
`2₁`-, `2₂`-, `2₃`-, `3₁`-, `3₂`- or `4₁`-cycle of `Q⁻`. Each node of a cycle of `Q⁻` but its hybrid
node has a block of taxa of its own; the hybrid node has at least one taxon below it, and the LSA of
the four taxa none above it. -/
theorem inducesCycleType_cases {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    {C : Set E} {v : V} {n k : ℕ} (hC : InducesCycleType Q C v n k) :
    (n = 2 ∧ 1 ≤ k ∧ k ≤ 3) ∨ (n = 3 ∧ (k = 1 ∨ k = 2)) ∨ (n = 4 ∧ k = 1) := by
  sorry

omit [Fintype V] in
/-- Every cycle of `Q⊕` induces a cycle of `Q⁻`, with the hybrid node of the cycle (Lemma 3). -/
theorem exists_inducesCycleType_of_isCycle {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {C : Set E} (hC : IsCycle Q.graph C) :
    ∃ v n k, InducesCycleType Q C v n k := by
  obtain ⟨⟨v, ⟨hv, h2⟩, -⟩, -, -⟩ := lemma3 hQ.binary hQ.levelOne hC
  exact ⟨v, _, _, hC, hv, h2, rfl, rfl⟩

/-- **`Q⊕` has at most one cycle inducing a `3₂`-cycle** (Lemma 6, for the cycles of `Q⊕`, which
induce distinct cycles of `Q⁻`). -/
theorem eq_of_inducesCycleType_three_two {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {C C' : Set E} {v v' : V} (hC : InducesCycleType Q C v 3 2)
    (hC' : InducesCycleType Q C' v' 3 2) : C = C' := by
  sorry

/-! ### The networks of Corollary 2 and of Lemmas 9 and 10 -/

/-- **The network of Corollary 2**: contracting the cycles of `Q⊕` that induce `2₁`- and
`2₃`-cycles, and suppressing the nodes of degree two this leaves, gives an LSA quartet network with
the other cycles of `Q⊕` and the same cut edges between two pairs of taxa. -/
theorem exists_lsaQuartet_of_corollary2 {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) :
    ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (Q' : RootedNetwork V' E' X)
      (θ' : MetricData E') (_ : IsLSAQuartet Q' θ'),
      cf Q' θ' = cf (contractRooted Q (IsTwoOneOrThree Q)) (contractMetric Q (IsTwoOneOrThree Q) θ) ∧
        SameCyclesBut Q' Q (IsTwoOneOrThree Q) ∧
        ∀ A : Finset X, #A = 2 → (Q'.HasCutSplit ↑A ↔ Q.HasCutSplit ↑A) := by
  sorry

/-- **The networks `Q₁⊕`, `Q₂⊕` of Lemmas 9 and 10**: deleting a hybrid edge of a cycle inducing a
`2₂`- or a `3₁`-cycle, and suppressing the nodes of degree two this leaves (and the edge of the root,
if the root is left with one child), gives an LSA quartet network with the other cycles of `Q⊕` and
the same cut edges between two pairs of taxa: the edges of the cycle that remain are cut edges
between one taxon and three, or between the two pairs that the cycle already separates. -/
theorem exists_lsaQuartet_deleteArc {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {C : Set E} {v : V}
    (hC : InducesCycleType Q C v 2 2 ∨ InducesCycleType Q C v 3 1) {h : E}
    (hh : Q.graph.target h = v) :
    ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (Q' : RootedNetwork V' E' X)
      (θ' : MetricData E') (_ : IsLSAQuartet Q' θ'),
      cf Q' θ' = cf (deleteArc Q h) (deleteArcMetric Q h θ) ∧ numRootedCycles Q' < numRootedCycles Q ∧
        SameCyclesBut Q' Q (· = C) ∧
        ∀ A : Finset X, #A = 2 → (Q'.HasCutSplit ↑A ↔ Q.HasCutSplit ↑A) := by
  sorry

/-- **The network `Q₀⊕` of Lemma 9**: contracting a cycle inducing a `2₂`-cycle, and suppressing the
node of degree two this leaves, gives an LSA quartet network with the other cycles of `Q⊕` and the
same cut edges between two pairs of taxa. -/
theorem exists_lsaQuartet_contractRooted {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {C : Set E} {v : V} (hC : InducesCycleType Q C v 2 2) :
    ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (Q' : RootedNetwork V' E' X)
      (θ' : MetricData E') (_ : IsLSAQuartet Q' θ'),
      cf Q' θ' = cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) ∧
        numRootedCycles Q' < numRootedCycles Q ∧ SameCyclesBut Q' Q (· = C) ∧
        ∀ A : Finset X, #A = 2 → (Q'.HasCutSplit ↑A ↔ Q.HasCutSplit ↑A) := by
  sorry

/-- **A single `3₂`-cycle is the network of Figure 18** (proof of Proposition 7): if the only cycle of
`Q⊕` induces a `3₂`-cycle with `a`, `b` below its hybrid node, `Q⁻` is the network of Figure 18 with
`a`, `b` at the node below the hybrid node and the two other taxa `c`, `d` at the nodes of the
cycle. -/
theorem exists_fig18 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    {C : Set E} {v : V} (hC : InducesCycleType Q C v 3 2) (hone : ∀ C', IsCycle Q.graph C' → C' = C)
    {a b : X} (hab : a ≠ b) (hD : {x | Q.graph.Reaches v (Q.leaf x)} = {a, b}) :
    ∃ (c d : X) (h : Distinct4 a b c d) (len : Fin 8 → ℝ) (γ : ℝ), (∀ i, 0 < len i) ∧ 0 < γ ∧
      γ < 1 ∧ InducesNetwork hQ (fig18 a b c) (figMetric len γ) := by
  sorry

/-! ### Orderings kept by convex combinations -/

variable [DecidableEq X]

/-- The concordance factors `p` are ordered as those of a quartet tree with the cherry `A`: the quartet
tree with the cherry `A` has the largest, strictly, and the two others are equal. -/
def OrderedAsQuartetTree (p : QuartetTree X → ℝ) (A : Finset X) : Prop :=
  (∀ q r : QuartetTree X, A ∈ q.val → A ∉ r.val → p r < p q) ∧
    ∀ r r' : QuartetTree X, A ∉ r.val → A ∉ r'.val → p r = p r'

/-- The concordance factors `p` lie on the open segment of Proposition 7 for the cherry `A`: the
quartet tree with the cherry `A` has more than `1/6`, the two others are equal, and the three are
the coordinates of a point of the simplex. -/
def OnSegmentOfI (p : QuartetTree X → ℝ) (A : Finset X) : Prop :=
  (∀ q : QuartetTree X, A ∈ q.val → 1 / 6 < p q) ∧
    (∀ r r' : QuartetTree X, A ∉ r.val → A ∉ r'.val → p r = p r') ∧ (∀ q, 0 ≤ p q) ∧
    ∑ q ∈ treesOn (univ : Finset X), p q = 1

omit [Fintype X] in
theorem OrderedAsQuartetTree.add {p₁ p₂ : QuartetTree X → ℝ} {A : Finset X} (h₁ : OrderedAsQuartetTree p₁ A)
    (h₂ : OrderedAsQuartetTree p₂ A) {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    OrderedAsQuartetTree (fun q => w₁ * p₁ q + w₂ * p₂ q) A := by
  refine ⟨fun q r hq hr => ?_, fun r r' hr hr' => ?_⟩
  · have := h₁.1 q r hq hr
    have := h₂.1 q r hq hr
    dsimp only
    nlinarith
  · dsimp only
    rw [h₁.2 r r' hr hr', h₂.2 r r' hr hr']

omit [Fintype X] in
theorem OrderedAsQuartetTree.add₃ {p₁ p₂ p₃ : QuartetTree X → ℝ} {A : Finset X} (h₁ : OrderedAsQuartetTree p₁ A)
    (h₂ : OrderedAsQuartetTree p₂ A) (h₃ : OrderedAsQuartetTree p₃ A) {w₁ w₂ w₃ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hw₃ : 0 < w₃) : OrderedAsQuartetTree (fun q => w₁ * p₁ q + w₂ * p₂ q + w₃ * p₃ q) A := by
  refine ⟨fun q r hq hr => ?_, fun r r' hr hr' => ?_⟩
  · have := h₁.1 q r hq hr
    have := h₂.1 q r hq hr
    have := h₃.1 q r hq hr
    dsimp only
    nlinarith
  · dsimp only
    rw [h₁.2 r r' hr hr', h₂.2 r r' hr hr', h₃.2 r r' hr hr']

theorem OnSegmentOfI.add {p₁ p₂ : QuartetTree X → ℝ} {A : Finset X} (h₁ : OnSegmentOfI p₁ A)
    (h₂ : OnSegmentOfI p₂ A) {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    OnSegmentOfI (fun q => w₁ * p₁ q + w₂ * p₂ q) A := by
  refine ⟨fun q hq => ?_, fun r r' hr hr' => ?_, fun q => ?_, ?_⟩
  · have := h₁.1 q hq
    have := h₂.1 q hq
    dsimp only
    nlinarith
  · dsimp only
    rw [h₁.2.1 r r' hr hr', h₂.2.1 r r' hr hr']
  · have := h₁.2.2.1 q
    have := h₂.2.2.1 q
    dsimp only
    positivity
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₁.2.2.2, h₂.2.2.2]
    linarith

theorem OnSegmentOfI.add₃ {p₁ p₂ p₃ : QuartetTree X → ℝ} {A : Finset X} (h₁ : OnSegmentOfI p₁ A)
    (h₂ : OnSegmentOfI p₂ A) (h₃ : OnSegmentOfI p₃ A) {w₁ w₂ w₃ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hw₃ : 0 < w₃) (hw : w₁ + w₂ + w₃ = 1) :
    OnSegmentOfI (fun q => w₁ * p₁ q + w₂ * p₂ q + w₃ * p₃ q) A := by
  refine ⟨fun q hq => ?_, fun r r' hr hr' => ?_, fun q => ?_, ?_⟩
  · have := h₁.1 q hq
    have := h₂.1 q hq
    have := h₃.1 q hq
    dsimp only
    nlinarith
  · dsimp only
    rw [h₁.2.1 r r' hr hr', h₂.2.1 r r' hr hr', h₃.2.1 r r' hr hr']
  · have := h₁.2.2.1 q
    have := h₂.2.2.1 q
    have := h₃.2.2.1 q
    dsimp only
    positivity
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, h₁.2.2.2, h₂.2.2.2, h₃.2.2.2]
    linarith

omit [Fintype X] in
/-- Two families of concordance factors ordered as the same quartet tree have the same ordering. -/
theorem OrderedAsQuartetTree.sameOrdering {p p' : QuartetTree X → ℝ}
    {A : Finset X} (h : OrderedAsQuartetTree p A) (h' : OrderedAsQuartetTree p' A) : SameOrdering p p' := by
  intro q r hqr
  by_cases hq : A ∈ q.val <;> by_cases hr : A ∈ r.val
  · have : q = r := quartetTree_eq_of_taxa_eq_of_mem hqr hq hr
    subst this
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  · exact ⟨fun hle => absurd hle (not_le.2 (h.1 q r hq hr)),
      fun hle => absurd hle (not_le.2 (h'.1 q r hq hr))⟩
  · exact ⟨fun _ => (h'.1 r q hr hq).le, fun _ => (h.1 r q hr hq).le⟩
  · exact ⟨fun _ => (h'.2 q r hq hr).le, fun _ => (h.2 q r hq hr).le⟩

/-- **Equation (1)**: the concordance factors of a species tree with the split `A | Aᶜ` are ordered as
the quartet tree with the cherry `A`. -/
theorem orderedAsQuartetTree_quartetProb (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A : Finset X}
    (hA : #A = 2) (hsplit : A ∈ unroot σ.clusters) :
    OrderedAsQuartetTree (External.AllmanDegnanRhodes2011.quartetProb σ) A := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hA
  -- the two other taxa
  have hc : (univ \ {a, b} : Finset X).card = 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hX, card_pair hab]
  obtain ⟨c, d, hcd, hcd'⟩ := Finset.card_eq_two.1 hc
  have hcm : c ∈ univ \ {a, b} := hcd' ▸ mem_insert_self c {d}
  have hdm : d ∈ univ \ {a, b} := hcd' ▸ mem_insert_of_mem (mem_singleton_self d)
  simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton, not_or] at hcm hdm
  have h4 : Distinct4 a b c d := ⟨hab, Ne.symm hcm.1, Ne.symm hdm.1, Ne.symm hcm.2, Ne.symm hdm.2, hcd⟩
  have huniv : ({a, b, c, d} : Finset X) = univ := eq_univ_of_card _ (by rw [h4.card_insert_eq, hX])
  obtain ⟨h₁, h₂⟩ := External.AllmanDegnanRhodes2011.equation1 hX σ
    (q := quartetTree a b c d h4) rfl hsplit
  -- the internal edge has a positive length
  have hL : 0 < σ.unrootedLength {a, b} := by
    unfold SpeciesTree.unrootedLength
    have hmem : ∃ C ∈ σ.clusters, C ≠ univ ∧ (C = {a, b} ∨ C = ({a, b} : Finset X)ᶜ) := by
      simp only [unroot, mem_union, mem_image, mem_erase] at hsplit
      rcases hsplit with ⟨hne, hC⟩ | ⟨C, ⟨hne, hC⟩, hcomp⟩
      · exact ⟨_, hC, hne, Or.inl rfl⟩
      · exact ⟨C, hC, hne, Or.inr (by rw [← hcomp, compl_compl])⟩
    obtain ⟨C, hC, hne, hCA⟩ := hmem
    exact Finset.sum_pos' (fun C' hC' => (σ.length_pos C' (mem_filter.1 hC').1
      (mem_filter.1 hC').2.1).le) ⟨C, mem_filter.2 ⟨hC, hne, hCA⟩, σ.length_pos C hC hne⟩
  have hx : Real.exp (-σ.unrootedLength {a, b}) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have htaxa : ∀ q : QuartetTree X, q.taxa = univ := fun q =>
    eq_univ_of_card _ (by rw [q.card_taxa, hX])
  have hT : ∀ q : QuartetTree X, {a, b} ∈ q.val → q = quartetTree a b c d h4 := fun q hq =>
    quartetTree_eq_of_taxa_eq_of_mem ((htaxa q).trans (htaxa _).symm) hq (by simp)
  have halt : ∀ r : QuartetTree X, {a, b} ∉ r.val → r ∈ (quartetTree a b c d h4).alternatives :=
    fun r hr => QuartetTree.mem_alternatives.2 ⟨(htaxa r).trans (htaxa _).symm,
      fun e => hr (e ▸ by simp)⟩
  refine ⟨fun q r hq hr => ?_, fun r r' hr hr' => ?_⟩
  · rw [hT q hq, h₁, h₂ r (halt r hr)]
    linarith
  · rw [h₂ r (halt r hr), h₂ r' (halt r' hr')]

end Banos2019
