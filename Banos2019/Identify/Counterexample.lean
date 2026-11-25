module

public import Banos2019.Identify.UnrootedCycles
public import Banos2019.Quartet.Examples
public import Banos2019.Quartet.Transfer

/-!
# Proposition 13 as printed fails (Baños 2019, Section 9)

A binary level-1 network with a 4-cycle `C_v` and a 3-cycle above it: for the taxa `a, b, c, d` in the
four blocks of `C_v` and a fifth taxon `e` in the block of `a`, the quartet network on `{a, b, c, e}`
has no 4-cycle and a `3₂`-cycle from the 3-cycle, so on an open set of parameters `{a, b, c, e}`
satisfies the Cycle property but not the Big Cycle property, while `e` is not in the hybrid block of
`C_v`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-- **The counterexample to Proposition 13 as printed.** -/
theorem proposition13AsPrinted_counterexample :
    ¬ ∀ (V E X : Type) [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
    (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph → ∀ (hX : Nontrivial X) (C : Set _)
    (v : SemidirectedVertex hN.1 hX), IsCycle (unrooted N hN hX).graph C → C.ncard = 4 →
    IsHybridNodeOf (unrooted N hN hX) C v → ∀ a b c d : X,
    (∀ x ∈ ({a, b, c, d} : Finset X), ∀ y ∈ ({a, b, c, d} : Finset X), x ≠ y →
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) →
    ForGenericParams N fun θ => IsMetricNetwork N θ →
      ∀ i ∈ ({a, b, c, d} : Finset X), ∀ j ∈ ({a, b, c, d} : Finset X),
        ∀ k ∈ ({a, b, c, d} : Finset X), i ≠ j → i ≠ k → j ≠ k → ∀ e,
          #({i, j, k, e} : Finset X) = 4 → CyclePropertyOn (cf N θ) {i, j, k, e} →
          ¬ BigCycleOn (cf N θ) {i, j, k, e} → DescendsFrom (unrooted N hN hX) v e := by
  sorry

end Banos2019
