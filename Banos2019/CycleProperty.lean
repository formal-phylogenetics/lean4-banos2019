module

public import Banos2019.Quartet.Transfer
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
  sorry

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

/-- **Proposition 10** (`prop:BCgenerically`): if `Q⁻_s` has a 4-cycle, `s` satisfies the Cycle property,
and for generic numerical parameters it satisfies the Big Cycle property. -/
theorem proposition10 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {s : Finset X} (hs : #s = 4) (h4 : HasFourCycle N hN s hs) :
    (∀ θ, IsMetricNetwork N θ → CyclePropertyOn (cf N θ) s) ∧
      ForGenericParams N fun θ => IsMetricNetwork N θ → BigCycleOn (cf N θ) s := by
  sorry

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
  sorry

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
