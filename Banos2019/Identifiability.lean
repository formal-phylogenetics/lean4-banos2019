module

public import Banos2019.CycleProperty

/-!
# Identifying cycles in networks (Baños 2019, Sections 8 and 9)

The 4-network blocks, the blocks of each cycle of size at least four and their cyclic order are
determined by the set `S` of sets of four taxa with the Big Cycle property, for generic parameters; with
them, the orderings of the quartet concordance factors determine the network `Ñ` (`theorem4`). "Can be
determined from `S`" is stated as: there is a function of `S` that gives the object for every network
and generic parameters.

* `bcSets`: the set `S`.
* `lemma14`, `lemma15`, `lemma16`, `theorem4`; `proposition12`, `proposition13` (Section 9).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-- The set `S` of the sets of four taxa that satisfy the Big Cycle property. -/
def bcSets {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] (N : RootedNetwork V E X)
    (θ : MetricData E) : Set (Finset X) :=
  {s | #s = 4 ∧ BigCycleOn (cf N θ) s}

/-- The edges of the cycles of size at least four of `N⁻`; their network blocks are the 4-network
blocks. -/
def bigCycleEdges {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') : Set E' :=
  familyEdges (cyclesOfSizeAtLeast G.graph 4)

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **Lemma 14** (`netblo`): for generic parameters, the 4-network blocks of a level-1 network are
determined by `S`. -/
theorem lemma14 (hX : Nontrivial X) :
    ∃ F : Set (Finset X) → X → X → Prop,
      ∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X)
        (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph →
        ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ x y,
          (F (bcSets N θ) x y ↔
            SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf
              (bigCycleEdges (unrooted N hN hX)) x y) := by
  sorry

/-- **Lemma 15** (`blov`): for generic parameters, for every set `s ∈ S`, the blocks of the cycle `C_v`
of `N⁻` whose hybrid node `v` it determines and the size `k_v` of the cycle are determined by `S`, and so
is the hybrid block when `k_v ≥ 5`. -/
theorem lemma15 (hX : Nontrivial X) :
    ∃ (B : Set (Finset X) → Finset X → X → X → Prop) (K : Set (Finset X) → Finset X → ℕ)
      (H : Set (Finset X) → Finset X → Set X),
      ∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X)
        (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph →
        ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ s (hs : s ∈ bcSets N θ),
          ∀ C w, IsCycle (unrooted N hN hX).graph C → IsHybridNodeOf (unrooted N hN hX) C w →
            Determines hN s hs.1 w.1.1 →
              (∀ x y, B (bcSets N θ) s x y ↔
                SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) ∧
              K (bcSets N θ) s = C.ncard ∧
              (5 ≤ C.ncard → H (bcSets N θ) s = {x | DescendsFrom (unrooted N hN hX) w x}) := by
  sorry

/-- **Lemma 16** (`orderofcycles`): for generic parameters, the order of the blocks around each cycle
`C_v` of size at least four (which blocks are adjacent) is determined by the orderings of the
concordance factors. -/
theorem lemma16 (hX : Nontrivial X) :
    ∃ A : (QuartetTree X → QuartetTree X → Prop) → Finset X → X → X → Prop,
      ∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X)
        (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph →
        ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ s (hs : s ∈ bcSets N θ),
          ∀ C w, IsCycle (unrooted N hN hX).graph C → IsHybridNodeOf (unrooted N hN hX) C w →
            Determines hN s hs.1 w.1.1 → ∀ x y,
              (A (fun q r => cf N θ q ≤ cf N θ r) s x y ↔
                AdjacentBlocks (unrooted N hN hX) C x y) := by
  sorry

/-- **Theorem 4** (`thm::main`): under the network multispecies coalescent, for generic parameters, the
orderings of the quartet concordance factors identify the semidirected topological network `Ñ` obtained
from `N⁻` by contracting all 2- and 3-cycles and forgetting the directions of the hybrid edges in
4-cycles, while retaining the directions of the hybrid edges of larger cycles. There is a property `G`
of the parameters of each network, which holds for generic parameters, such that two level-1 networks on
the same taxa, with parameters satisfying `G` and the same orderings of concordance factors, have
isomorphic networks `Ñ`. -/
theorem theorem4 (hX : Nontrivial X) :
    ∃ G : ∀ (V E : Type) [Fintype V] [Fintype E], RootedNetwork V E X → MetricData E → Prop,
      (∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X),
        IsBinaryRootedNetwork N → IsLevelOne N.graph → ForGenericParams N (G V E N)) ∧
      ∀ (V₁ E₁ V₂ E₂ : Type) [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
        (N₁ : RootedNetwork V₁ E₁ X) (N₂ : RootedNetwork V₂ E₂ X)
        (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂),
        IsLevelOne N₁.graph → IsLevelOne N₂.graph →
        ∀ θ₁ θ₂, IsMetricNetwork N₁ θ₁ → IsMetricNetwork N₂ θ₂ → G V₁ E₁ N₁ θ₁ → G V₂ E₂ N₂ θ₂ →
          SameOrdering (cf N₁ θ₁) (cf N₂ θ₂) →
          Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX))) := by
  sorry

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **Proposition 12** (`pub:prop12`; unlabelled in the TeX): for generic parameters, if `s` satisfies the
Cycle property but not the Big Cycle property, and no `{i, j, k, e}` with `i, j, k ∈ s` distinct satisfies
the Big Cycle property, then `N⁻` contains a 3-cycle with at least two taxa descending from its hybrid
node. -/
theorem proposition12 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) :
    ForGenericParams N fun θ => IsMetricNetwork N θ → CyclePropertyOn (cf N θ) s →
      ¬ BigCycleOn (cf N θ) s →
      (¬ ∃ t ⊆ s, #t = 3 ∧ ∃ e ∉ t, BigCycleOn (cf N θ) (insert e t)) →
      ∃ C v, IsCycle (unrooted N hN hX).graph C ∧ C.ncard = 3 ∧
        IsHybridNodeOf (unrooted N hN hX) C v ∧
        2 ≤ {x | DescendsFrom (unrooted N hN hX) v x}.ncard := by
  sorry

/-- **Proposition 13** (`lem::cpto4c`): let `C_v` be a 4-cycle of `N⁻` and `a, b, c, d` taxa in distinct
`v`-blocks. For generic parameters, if for distinct `i, j, k ∈ {a, b, c, d}` some taxon `e` makes
`{i, j, k, e}` satisfy the Cycle property but not the Big Cycle property, then `e` is in the `v`-hybrid
block. -/
theorem proposition13 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _} {v : SemidirectedVertex hN.1 hX}
    (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : C.ncard = 4)
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) {a b c d : X}
    (hblocks : ∀ x ∈ ({a, b, c, d} : Finset X), ∀ y ∈ ({a, b, c, d} : Finset X), x ≠ y →
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) :
    ForGenericParams N fun θ => IsMetricNetwork N θ →
      ∀ i ∈ ({a, b, c, d} : Finset X), ∀ j ∈ ({a, b, c, d} : Finset X),
        ∀ k ∈ ({a, b, c, d} : Finset X), i ≠ j → i ≠ k → j ≠ k → ∀ e,
          #({i, j, k, e} : Finset X) = 4 → CyclePropertyOn (cf N θ) {i, j, k, e} →
          ¬ BigCycleOn (cf N θ) {i, j, k, e} → DescendsFrom (unrooted N hN hX) v e := by
  sorry

end Banos2019
