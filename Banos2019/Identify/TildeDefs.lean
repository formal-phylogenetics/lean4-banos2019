module

public import Banos2019.Identify.QuartetCycles

/-!
# The induction of Theorem 4 (Baños 2019, Section 8)

Theorem 4 is proved by induction on the number of cycles of size at least four of `N⁻`.

* `bigCycleCount`: the number of cycles of size at least four.
* `NonDegenerateCF`: on every set of four taxa, the three concordance factors are not all equal.
* `GoodParams`: the generic conditions that the proof uses: the statement of Lemma 12 for every set of
  four taxa, and `NonDegenerateCF`.
* `TildeDetermined m`: for networks `N₁`, `N₂` on the same taxa, with parameters satisfying
  `GoodParams` and the same orderings of concordance factors, and `m` cycles of size at least four in
  `N₁⁻`, the networks `Ñ₁` and `Ñ₂` are isomorphic.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-- The number of cycles of size at least four. -/
def bigCycleCount {V E X : Type*} (G : SemidirectedNetwork V E X) : ℕ :=
  (cyclesOfSizeAtLeast G.graph 4).ncard

/-- On every set of four taxa, the three concordance factors are not all equal. -/
def NonDegenerateCF {X : Type*} [Fintype X] [DecidableEq X] (p : QuartetTree X → ℝ) : Prop :=
  ∀ s : Finset X, #s = 4 → ∃ q ∈ treesOn s, ∃ r ∈ treesOn s, p q ≠ p r

/-- **The generic conditions of Theorem 4**: for metric parameters, the statement of Lemma 12 for
every set of four taxa (the Big Cycle property holds exactly for the sets that a cycle of size at
least four separates), and concordance factors that are not all equal on any set of four taxa. -/
def GoodParams {X : Type*} [Fintype X] [DecidableEq X] (hX : Nontrivial X) {V E : Type*} [Fintype V]
    [Fintype E] (N : RootedNetwork V E X) (θ : MetricData E) : Prop :=
  IsMetricNetwork N θ → ∀ hN : IsBinaryRootedNetwork N,
    (∀ s : Finset X, #s = 4 → (BigCycleOn (cf N θ) s ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s)) ∧
    NonDegenerateCF (cf N θ)

/-- **The claim of the induction of Theorem 4** for `m` cycles of size at least four: two binary
level-1 networks on the same taxa, with parameters satisfying `GoodParams` and the same orderings of
concordance factors, the first with `m` cycles of size at least four in `N⁻`, have isomorphic
networks `Ñ`. -/
def TildeDetermined (m : ℕ) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (hX : Nontrivial X) (V₁ E₁ V₂ E₂ : Type) [Fintype V₁]
    [Fintype E₁] [Fintype V₂] [Fintype E₂] (N₁ : RootedNetwork V₁ E₁ X) (N₂ : RootedNetwork V₂ E₂ X)
    (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂),
    IsLevelOne N₁.graph → IsLevelOne N₂.graph → ∀ θ₁ θ₂, IsMetricNetwork N₁ θ₁ →
    IsMetricNetwork N₂ θ₂ → GoodParams hX N₁ θ₁ → GoodParams hX N₂ θ₂ →
    SameOrdering (cf N₁ θ₁) (cf N₂ θ₂) → bigCycleCount (unrooted N₁ hN₁ hX) = m →
    Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX)))

end Banos2019
