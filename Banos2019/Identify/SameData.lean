module

public import Banos2019.Identify.TildeDefs
public import Banos2019.Identify.BlocksFromS

/-!
# The cycles that the orderings determine (Baños 2019, proof of Theorem 4)

For two networks with parameters satisfying the conditions of Theorem 4 and the same orderings of
concordance factors, every cycle of size at least four of `N₁⁻` has a counterpart in `N₂⁻` with the
same blocks, the same size, the same adjacent blocks and, for size at least five, the same hybrid
block (Lemmas 15 and 16).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {X : Type} [Fintype X] [DecidableEq X] {V E : Type} [Fintype V] [Fintype E]

/-- **The orderings determine the blocks, the size, the order and the hybrid block of the cycles**
(Lemmas 15 and 16): a cycle of size at least four of `N₁⁻` has a counterpart in `N₂⁻`. -/
theorem exists_bigCycle_sameData {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hX : Nontrivial X) {θ₁ : MetricData E} {θ₂ : MetricData E'} (hθ₁ : IsMetricNetwork N₁ θ₁)
    (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁) (hG₂ : GoodParams hX N₂ θ₂)
    (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂)) {C₁ : Set _} {v₁}
    (hC₁ : C₁ ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4)
    (hv₁ : IsHybridNodeOf (unrooted N₁ hN₁ hX) C₁ v₁) :
    ∃ C₂ v₂, C₂ ∈ cyclesOfSizeAtLeast (unrooted N₂ hN₂ hX).graph 4 ∧
      IsHybridNodeOf (unrooted N₂ hN₂ hX) C₂ v₂ ∧ C₂.ncard = C₁.ncard ∧
      (∀ x y, SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y ↔
        SameBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ x y) ∧
      (∀ x y, AdjacentBlocks (unrooted N₁ hN₁ hX) C₁ x y ↔
        AdjacentBlocks (unrooted N₂ hN₂ hX) C₂ x y) ∧
      (5 ≤ C₁.ncard → ∀ x, DescendsFrom (unrooted N₁ hN₁ hX) v₁ x ↔
        DescendsFrom (unrooted N₂ hN₂ hX) v₂ x) := by
  have h12₁ := (hG₁ hθ₁ hN₁).1
  have h12₂ := (hG₂ hθ₂ hN₂).1
  obtain ⟨hC₁, hC₁4⟩ := hC₁
  -- two taxa in different blocks of `C₁`: one in the hybrid block, one in the block of another node
  obtain ⟨u, hu, huv⟩ := hC₁.exists_mem_cycleNodes_notMem (Set.finite_singleton v₁)
    (by rw [Set.ncard_singleton]; omega)
  obtain ⟨x, hx⟩ := exists_blockNode_eq h1₁ hC₁ hv₁.mem_cycleNodes
  obtain ⟨y, hy⟩ := exists_blockNode_eq h1₁ hC₁ hu
  have hxy : ¬ SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y := by
    rw [sameBlock_iff_blockNode_eq h1₁ hC₁, hx, hy]
    exact fun h => huv h.symm
  -- a set `s` of four taxa that `C₁` separates
  obtain ⟨c, d, h4, hsep₁⟩ := exists_separatesQuartet_of_not_sameBlock h1₁ hC₁ hC₁4 hv₁ hxy
  generalize ({x, y, c, d} : Finset X) = s at h4 hsep₁
  -- the two networks have the same comparisons of concordance factors, so the same `S`
  have hR : (fun q r : QuartetTree X => q.taxa = r.taxa ∧ cf N₁ θ₁ q ≤ cf N₁ θ₁ r) =
      fun q r => q.taxa = r.taxa ∧ cf N₂ θ₂ q ≤ cf N₂ θ₂ r :=
    funext₂ fun q r => propext (and_congr_right (hord q r))
  have hSS : bcSets N₁ θ₁ = bcSets N₂ θ₂ := by
    rw [← bcSetsOf_cf, hR, bcSetsOf_cf]
  -- `s` has the Big Cycle property, so a cycle `C₂` of `N₂⁻` of size at least four separates it
  have hs₁ : s ∈ bcSets N₁ θ₁ := (mem_bcSets_iff_of_lemma12 h12₁ s h4).2 ⟨C₁, v₁, hC₁4, hsep₁⟩
  have hs₂ : s ∈ bcSets N₂ θ₂ := hSS ▸ hs₁
  obtain ⟨C₂, v₂, hC₂4, hsep₂⟩ := (mem_bcSets_iff_of_lemma12 h12₂ s h4).1 hs₂
  -- `s` determines `v₁` and `v₂`: Lemmas 15 and 16 give the same data for `C₁` and `C₂`
  have hdet₁ := (determines_iff_separatesQuartet hN₁ h1₁ hX hs₁.1 v₁).2 ⟨C₁, hsep₁⟩
  have hdet₂ := (determines_iff_separatesQuartet hN₂ h1₂ hX hs₂.1 v₂).2 ⟨C₂, hsep₂⟩
  obtain ⟨hB₁, hK₁, hH₁⟩ := lemma15_core hN₁ h1₁ hX hθ₁ h12₁ hs₁ hC₁ hv₁ hdet₁
  obtain ⟨hB₂, hK₂, hH₂⟩ := lemma15_core hN₂ h1₂ hX hθ₂ h12₂ hs₂ hsep₂.1 hsep₂.2.1 hdet₂
  rw [hSS] at hB₁ hK₁ hH₁
  refine ⟨C₂, v₂, ⟨hsep₂.1, hC₂4⟩, hsep₂.2.1, hK₂.symm.trans hK₁,
    fun x y => (hB₁ x y).symm.trans (hB₂ x y), fun x y => ?_, fun h5 x => ?_⟩
  · have h16₁ := lemma16_core hN₁ h1₁ hX hθ₁ h12₁ hs₁ hC₁ hv₁ hdet₁ x y
    have h16₂ := lemma16_core hN₂ h1₂ hX hθ₂ h12₂ hs₂ hsep₂.1 hsep₂.2.1 hdet₂ x y
    rw [hR] at h16₁
    exact h16₁.symm.trans h16₂
  · have h5₂ : 5 ≤ C₂.ncard := by
      rw [← hK₂, hK₁]
      exact h5
    exact Set.ext_iff.1 ((hH₁ h5).symm.trans (hH₂ h5₂)) x

end Banos2019
