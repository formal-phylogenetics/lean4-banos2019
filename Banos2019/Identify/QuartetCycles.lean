module

public import Banos2019.Identify.CycleOrder

/-!
# The cycles of `Q⁻_s` and those of `N⁻` (Baños 2019, Sections 7–9)

The cycles of the induced quartet network `Q⁻_s` come from the cycles of `N⁻`: a cycle `C_v` of `N⁻`
whose hybrid block contains a taxon of `s` and whose blocks contain taxa of `s` from at least two
blocks induces a cycle of `Q⁻_s`, with hybrid node `v`; its nodes are the nodes of `C_v` whose blocks
contain taxa of `s`, in the same order around the cycle, and its blocks are the traces of those blocks
on `s`. The paper uses this throughout Sections 7–9 ("since the other taxa are in distinct `v`-blocks
of `Q⁻_abcd`, they must be in distinct `v`-blocks of `N⁻`", proof of Lemma 12; "the 4-cycle in
`Q⁻_abcd` and the 3-cycle in `Q⁻_abce`", proof of Proposition 13).

* `determines_iff_separatesQuartet`: `s` determines the hybrid node `v` of `N⁻` (the 4-cycle of `Q⁻_s`
  has hybrid node `v`) exactly when the cycle `C_v` separates `s`.
* `adjacentBlocks_quartetUnrooted_iff`: in the 4-cycle of `Q⁻_s`, the blocks of `a` and `c` are
  adjacent exactly when, in `C_v`, they are joined avoiding the blocks of the other two taxa of `s`.
* `exists_cycle_of_hasThreeTwoCycle`: a `3₂`-cycle of `Q⁻_s` comes from a cycle of `N⁻` in which the
  two taxa of `s` below its hybrid node are in the hybrid block and the other two in two other
  distinct blocks.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] {N : RootedNetwork V E X}

/-- **The hybrid node determined by `s`** (Section 7): `s` determines the hybrid node `v` of `N⁻`
exactly when the cycle `C_v` of `N⁻` separates `s`, its four taxa in four distinct `v`-blocks, one of
them in the hybrid block. The 4-cycle of `Q⁻_s` is the cycle that `C_v` induces on `s`. -/
theorem determines_iff_separatesQuartet (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) (v : SemidirectedVertex hN.1 hX) :
    Determines hN s hs v.1.1 ↔ ∃ C, SeparatesQuartet (unrooted N hN hX) C v s := by
  sorry

/-- **The order of the blocks of the 4-cycle of `Q⁻_s`** is that of the blocks of `C_v` that contain
taxa of `s`: the blocks of `a` and `c` are adjacent in the 4-cycle of `Q⁻_s` exactly when they are
joined along `C_v` avoiding the blocks of the other two taxa. -/
theorem adjacentBlocks_quartetUnrooted_iff [DecidableEq X] (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) {C : Set _} {v : SemidirectedVertex hN.1 hX}
    (hsep : SeparatesQuartet (unrooted N hN hX) C v s) {C' : Set _}
    (hC' : IsCycle (quartetUnrooted N hN s hs).graph C') (hC'4 : C'.ncard = 4) {w}
    (hw : IsHybridNodeOf (quartetUnrooted N hN s hs) C' w) (hwv : quartetNode hN hs w = v.1.1)
    {a c : X} (ha : a ∈ s) (hc : c ∈ s) (hac : a ≠ c) :
    AdjacentBlocks (quartetUnrooted N hN s hs) C' ⟨a, ha⟩ ⟨c, hc⟩ ↔
      JoinedAvoiding (unrooted N hN hX) C ↑((s.erase a).erase c) a c := by
  sorry

/-- **A `3₂`-cycle of `Q⁻_s` comes from a cycle of `N⁻`**, with the same hybrid node: the two taxa
`p`, `q` of `s` below the hybrid node are in the hybrid block of the cycle of `N⁻`, and the other two
taxa `r`, `t` of `s` are in two other blocks, distinct from each other. -/
theorem exists_cycle_of_hasThreeTwoCycle (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) (h32 : HasThreeTwoCycle N hN s hs) :
    ∃ C v, IsCycle (unrooted N hN hX).graph C ∧ IsHybridNodeOf (unrooted N hN hX) C v ∧
      ∃ p ∈ s, ∃ q ∈ s, ∃ r ∈ s, ∃ t ∈ s, p ≠ q ∧ DescendsFrom (unrooted N hN hX) v p ∧
        DescendsFrom (unrooted N hN hX) v q ∧
        ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C p r ∧
        ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C p t ∧
        ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C r t := by
  sorry

end Banos2019
