module

public import Banos2019.Identify.TildeDefs
public import Banos2019.Identify.BlocksFromS

/-!
# The data of two networks read from the orderings (Baños 2019, proof of Theorem 4)

Two networks on the same taxa have the *same cycle data* (`SameCycleData`) when every cycle of size
at least four of `N₁⁻` has a counterpart in `N₂⁻` with the same size, the same blocks, the same
adjacent blocks and, for size at least five, the same hybrid block; they have the *same 4-network
blocks* (`SameFourNetworkBlocks`) when two taxa are in one 4-network block of `N₁⁻` exactly when they
are in one 4-network block of `N₂⁻`. The proof of Theorem 4 reads the cycle data from the orderings
of the concordance factors by Lemmas 15 and 16 (TeX l. 1182 for one cycle, l. 1186 for more), and the
4-network blocks by Lemma 14 (TeX l. 1186). Every network of the induction, the networks induced on
sets of taxa included, has its data read from its own orderings.

* `GivesFourNetworkBlocks`, `GivesBlocks`, `GivesAdjacency`: the conclusions of Lemmas 14, 15 and 16
  at given parameters, for given functions of `S` and of the comparisons of concordance factors.
* `bcSets_eq_of_sameOrdering`: the same orderings give the same set `S`.
* `sameFourNetworkBlocks_of_gives`, `sameCycleData_of_gives`: two networks with the same orderings,
  at parameters where the conclusions of Lemma 14, and of Lemmas 15 and 16, hold for the same
  functions, have the same 4-network blocks and the same cycle data.
* `givesFourNetworkBlocks_of_goodParams`, `givesBlocks_of_goodParams`,
  `givesAdjacency_of_goodParams`: at parameters satisfying `GoodParams`, which contains the statement
  of Lemma 12, the conclusions of Lemmas 14, 15 and 16 hold for the functions of their proofs
  (`lemma14_core`, `lemma15_core`, `lemma16_core`).
* `sameFourNetworkBlocks_of_sameOrdering`, `sameCycleData_of_sameOrdering`: so two networks with
  parameters satisfying `GoodParams` and the same orderings have the same 4-network blocks and the
  same cycle data.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-- **The same cycle data**: every cycle `C₁` of size at least four of `G₁`, with hybrid node `v₁`,
has a counterpart `C₂` in `G₂`, with hybrid node `v₂`, of the same size, with the same blocks, the
same adjacent blocks and, for size at least five, the same hybrid block. -/
def SameCycleData {V₁ E₁ V₂ E₂ X' : Type*} (G₁ : SemidirectedNetwork V₁ E₁ X')
    (G₂ : SemidirectedNetwork V₂ E₂ X') : Prop :=
  ∀ C₁ ∈ cyclesOfSizeAtLeast G₁.graph 4, ∀ v₁, IsHybridNodeOf G₁ C₁ v₁ →
    ∃ C₂ v₂, C₂ ∈ cyclesOfSizeAtLeast G₂.graph 4 ∧ IsHybridNodeOf G₂ C₂ v₂ ∧ C₂.ncard = C₁.ncard ∧
      (∀ x y, SameBlock G₁.graph G₁.leaf C₁ x y ↔ SameBlock G₂.graph G₂.leaf C₂ x y) ∧
      (∀ x y, AdjacentBlocks G₁ C₁ x y ↔ AdjacentBlocks G₂ C₂ x y) ∧
      (5 ≤ C₁.ncard → ∀ x, DescendsFrom G₁ v₁ x ↔ DescendsFrom G₂ v₂ x)

/-- **The same 4-network blocks**: two taxa are in one 4-network block of `G₁` exactly when they are
in one 4-network block of `G₂`. -/
def SameFourNetworkBlocks {V₁ E₁ V₂ E₂ X' : Type*} (G₁ : SemidirectedNetwork V₁ E₁ X')
    (G₂ : SemidirectedNetwork V₂ E₂ X') : Prop :=
  ∀ x y, SameBlock G₁.graph G₁.leaf (familyEdges (cyclesOfSizeAtLeast G₁.graph 4)) x y ↔
    SameBlock G₂.graph G₂.leaf (familyEdges (cyclesOfSizeAtLeast G₂.graph 4)) x y

variable {X : Type} [Fintype X] [DecidableEq X] {V E : Type} [Fintype V] [Fintype E]

/-- **The conclusion of Lemma 14** at the parameters `θ`, for the function `F`: `F S` gives the
4-network blocks of `N⁻`. -/
def GivesFourNetworkBlocks (F : Set (Finset X) → X → X → Prop) {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X) (θ : MetricData E) : Prop :=
  IsMetricNetwork N θ → ∀ x y, (F (bcSets N θ) x y ↔
    SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf
      (familyEdges (cyclesOfSizeAtLeast (unrooted N hN hX).graph 4)) x y)

/-- **The conclusion of Lemma 15** at the parameters `θ`, for the functions `B`, `K`, `H`: for every
set `s ∈ S` determining the hybrid node `w` of a cycle `C_w` of `N⁻`, `B S s` gives the blocks of
`C_w`, `K S s` its size and, when the size is at least five, `H S s` its hybrid block. -/
def GivesBlocks (B : Set (Finset X) → Finset X → X → X → Prop) (K : Set (Finset X) → Finset X → ℕ)
    (H : Set (Finset X) → Finset X → Set X) {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (hX : Nontrivial X) (θ : MetricData E) : Prop :=
  IsMetricNetwork N θ → ∀ s (hs : s ∈ bcSets N θ),
    ∀ C w, IsCycle (unrooted N hN hX).graph C → IsHybridNodeOf (unrooted N hN hX) C w →
      Determines hN s hs.1 w.1.1 →
        (∀ x y, B (bcSets N θ) s x y ↔
          SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) ∧
        K (bcSets N θ) s = C.ncard ∧
        (5 ≤ C.ncard → H (bcSets N θ) s = {x | DescendsFrom (unrooted N hN hX) w x})

/-- **The conclusion of Lemma 16** at the parameters `θ`, for the function `A`: for every set `s ∈ S`
determining the hybrid node `w` of a cycle `C_w` of `N⁻`, `A`, applied to the comparisons of the
concordance factors of quartet trees on the same four taxa, gives the adjacent blocks of `C_w`. -/
def GivesAdjacency (A : (QuartetTree X → QuartetTree X → Prop) → Finset X → X → X → Prop)
    {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X)
    (θ : MetricData E) : Prop :=
  IsMetricNetwork N θ → ∀ s (hs : s ∈ bcSets N θ),
    ∀ C w, IsCycle (unrooted N hN hX).graph C → IsHybridNodeOf (unrooted N hN hX) C w →
      Determines hN s hs.1 w.1.1 → ∀ x y,
        (A (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) s x y ↔
          AdjacentBlocks (unrooted N hN hX) C x y)

/-- **The same orderings give the same set `S`**: the Big Cycle property of a set of four taxa is
read from the comparisons of its concordance factors (`bcSetsOf_cf`). -/
theorem bcSets_eq_of_sameOrdering {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} {θ₁ : MetricData E}
    {θ₂ : MetricData E'} (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂)) :
    bcSets N₁ θ₁ = bcSets N₂ θ₂ := by
  have hR : (fun q r : QuartetTree X => q.taxa = r.taxa ∧ cf N₁ θ₁ q ≤ cf N₁ θ₁ r) =
      fun q r => q.taxa = r.taxa ∧ cf N₂ θ₂ q ≤ cf N₂ θ₂ r :=
    funext₂ fun q r => propext (and_congr_right (hord q r))
  rw [← bcSetsOf_cf, hR, bcSetsOf_cf]

/-- **Lemma 14 gives the same 4-network blocks**: for two networks with the same orderings of
concordance factors, at parameters where the conclusion of Lemma 14 holds for the same function `F`,
the set `S` is the same (`bcSets_eq_of_sameOrdering`), and `F S` gives the 4-network blocks of
both. -/
theorem sameFourNetworkBlocks_of_gives {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (hX : Nontrivial X) {θ₁ : MetricData E} {θ₂ : MetricData E'}
    (hθ₁ : IsMetricNetwork N₁ θ₁) (hθ₂ : IsMetricNetwork N₂ θ₂)
    (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂)) {F : Set (Finset X) → X → X → Prop}
    (h14₁ : GivesFourNetworkBlocks F hN₁ hX θ₁) (h14₂ : GivesFourNetworkBlocks F hN₂ hX θ₂) :
    SameFourNetworkBlocks (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX) := fun x y => by
  rw [← h14₁ hθ₁ x y, ← h14₂ hθ₂ x y, bcSets_eq_of_sameOrdering hord]

/-- **Lemmas 15 and 16 give the same cycle data**: for two networks with parameters satisfying
`GoodParams` and the same orderings of concordance factors, at which the conclusions of Lemmas 15 and
16 hold for the same functions, a cycle `C₁` of size at least four of `N₁⁻` separates a set `s` of
four taxa, which has the Big Cycle property (Lemma 12); `s` is in the same set `S` for `N₂`, so a
cycle `C₂` of `N₂⁻` separates it, and `s` determines the hybrid nodes of both (Section 7). The
functions of Lemmas 15 and 16, applied to the same `S`, `s` and comparisons, give the data of both
cycles. -/
theorem sameCycleData_of_gives {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hX : Nontrivial X) {θ₁ : MetricData E} {θ₂ : MetricData E'} (hθ₁ : IsMetricNetwork N₁ θ₁)
    (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁) (hG₂ : GoodParams hX N₂ θ₂)
    (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂))
    {B : Set (Finset X) → Finset X → X → X → Prop} {K : Set (Finset X) → Finset X → ℕ}
    {H : Set (Finset X) → Finset X → Set X}
    {A : (QuartetTree X → QuartetTree X → Prop) → Finset X → X → X → Prop}
    (h15₁ : GivesBlocks B K H hN₁ hX θ₁) (h15₂ : GivesBlocks B K H hN₂ hX θ₂)
    (h16₁ : GivesAdjacency A hN₁ hX θ₁) (h16₂ : GivesAdjacency A hN₂ hX θ₂) :
    SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX) := by
  intro C₁ hC₁ v₁ hv₁
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
  have hSS : bcSets N₁ θ₁ = bcSets N₂ θ₂ := bcSets_eq_of_sameOrdering hord
  -- `s` has the Big Cycle property, so a cycle `C₂` of `N₂⁻` of size at least four separates it
  have hs₁ : s ∈ bcSets N₁ θ₁ := (mem_bcSets_iff_of_lemma12 h12₁ s h4).2 ⟨C₁, v₁, hC₁4, hsep₁⟩
  have hs₂ : s ∈ bcSets N₂ θ₂ := hSS ▸ hs₁
  obtain ⟨C₂, v₂, hC₂4, hsep₂⟩ := (mem_bcSets_iff_of_lemma12 h12₂ s h4).1 hs₂
  -- `s` determines `v₁` and `v₂`: Lemmas 15 and 16 give the same data for `C₁` and `C₂`
  have hdet₁ := (determines_iff_separatesQuartet hN₁ h1₁ hX hs₁.1 v₁).2 ⟨C₁, hsep₁⟩
  have hdet₂ := (determines_iff_separatesQuartet hN₂ h1₂ hX hs₂.1 v₂).2 ⟨C₂, hsep₂⟩
  obtain ⟨hB₁, hK₁, hH₁⟩ := h15₁ hθ₁ s hs₁ C₁ v₁ hC₁ hv₁ hdet₁
  obtain ⟨hB₂, hK₂, hH₂⟩ := h15₂ hθ₂ s hs₂ C₂ v₂ hsep₂.1 hsep₂.2.1 hdet₂
  rw [hSS] at hB₁ hK₁ hH₁
  refine ⟨C₂, v₂, ⟨hsep₂.1, hC₂4⟩, hsep₂.2.1, hK₂.symm.trans hK₁,
    fun x y => (hB₁ x y).symm.trans (hB₂ x y), fun x y => ?_, fun h5 x => ?_⟩
  · have h16₁' := h16₁ hθ₁ s hs₁ C₁ v₁ hC₁ hv₁ hdet₁ x y
    have h16₂' := h16₂ hθ₂ s hs₂ C₂ v₂ hsep₂.1 hsep₂.2.1 hdet₂ x y
    rw [hR] at h16₁'
    exact h16₁'.symm.trans h16₂'
  · have h5₂ : 5 ≤ C₂.ncard := by
      rw [← hK₂, hK₁]
      exact h5
    exact Set.ext_iff.1 ((hH₁ h5).symm.trans (hH₂ h5₂)) x

/-- **The conclusion of Lemma 14 at parameters satisfying `GoodParams`**, for the function of its
proof, the complement of `Y_x` (`lemma14_core`). -/
theorem givesFourNetworkBlocks_of_goodParams {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X)
    {θ : MetricData E} (hG : GoodParams hX N θ) :
    GivesFourNetworkBlocks (fun S x y => y ∉ complementBlock S x) hN hX θ :=
  fun hθ x y => lemma14_core hN h1 hX (hG hθ hN).1 x y

/-- **The conclusion of Lemma 15 at parameters satisfying `GoodParams`**, for the functions of its
proof (`lemma15_core`). -/
theorem givesBlocks_of_goodParams {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {θ : MetricData E} (hG : GoodParams hX N θ) :
    GivesBlocks blockRelation blockCount hybridBlock hN hX θ :=
  fun hθ _ hs _ _ hC hw hdet => lemma15_core hN h1 hX hθ (hG hθ hN).1 hs hC hw hdet

/-- **The conclusion of Lemma 16 at parameters satisfying `GoodParams`**, for the function of its
proof applied to those of Lemma 15 (`lemma16_core`, on the conclusion of `lemma15_core`). -/
theorem givesAdjacency_of_goodParams {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {θ : MetricData E} (hG : GoodParams hX N θ) :
    GivesAdjacency (adjacencyOf blockRelation blockCount hybridBlock) hN hX θ := by
  intro hθ s hs C w hC hw hdet x y
  obtain ⟨hB, hK, hH⟩ := lemma15_core hN h1 hX hθ (hG hθ hN).1 hs hC hw hdet
  exact lemma16_core hN h1 hX hθ (hG hθ hN).1 hs hC hw hdet hB hK hH x y

/-- **The orderings give the same 4-network blocks** for parameters satisfying `GoodParams`: the
argument of Lemma 14 at the parameters of each network (`givesFourNetworkBlocks_of_goodParams`,
`sameFourNetworkBlocks_of_gives`). -/
theorem sameFourNetworkBlocks_of_sameOrdering {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hX : Nontrivial X) {θ₁ : MetricData E} {θ₂ : MetricData E'} (hθ₁ : IsMetricNetwork N₁ θ₁)
    (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁) (hG₂ : GoodParams hX N₂ θ₂)
    (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂)) :
    SameFourNetworkBlocks (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX) :=
  sameFourNetworkBlocks_of_gives hN₁ hN₂ hX hθ₁ hθ₂ hord
    (givesFourNetworkBlocks_of_goodParams hN₁ h1₁ hX hG₁)
    (givesFourNetworkBlocks_of_goodParams hN₂ h1₂ hX hG₂)

/-- **The orderings give the same cycle data** for parameters satisfying `GoodParams`: the arguments
of Lemmas 15 and 16 at the parameters of each network (`givesBlocks_of_goodParams`,
`givesAdjacency_of_goodParams`, `sameCycleData_of_gives`). -/
theorem sameCycleData_of_sameOrdering {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hX : Nontrivial X) {θ₁ : MetricData E} {θ₂ : MetricData E'} (hθ₁ : IsMetricNetwork N₁ θ₁)
    (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁) (hG₂ : GoodParams hX N₂ θ₂)
    (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂)) :
    SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX) :=
  sameCycleData_of_gives hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord
    (givesBlocks_of_goodParams hN₁ h1₁ hX hG₁) (givesBlocks_of_goodParams hN₂ h1₂ hX hG₂)
    (givesAdjacency_of_goodParams hN₁ h1₁ hX hG₁) (givesAdjacency_of_goodParams hN₂ h1₂ hX hG₂)

end Banos2019
