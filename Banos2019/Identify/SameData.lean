module

public import Banos2019.Identify.TildeDefs
public import Banos2019.Identify.BlocksFromS
public import Banos2019.Identify.InducedOrder

/-!
# The cycle data of two networks (Baños 2019, proof of Theorem 4)

Two networks on the same taxa have the *same cycle data* (`SameCycleData`) when every cycle of size
at least four of `N₁⁻` has a counterpart in `N₂⁻` with the same size, the same blocks, the same
adjacent blocks and, for size at least five, the same hybrid block. The proof of Theorem 4 reads
these data from the orderings of the concordance factors by Lemmas 15 and 16 (TeX l.1182 and
l.1186), and its induction uses them for the networks induced on sets of taxa.

* `GivesBlocks`, `GivesAdjacency`: the conclusions of Lemmas 15 and 16 at given parameters, for given
  functions of `S` and of the comparisons of concordance factors.
* `sameCycleData_of_gives`: two networks with the same orderings, at parameters where the
  conclusions of Lemmas 15 and 16 hold for the same functions, have the same cycle data.
* `joinedAvoiding_of_sameBlock_of_adjacentBlocks`: two cycles with the same blocks and the same
  adjacent blocks join the same blocks avoiding the same blocks.
* `SameCycleData.inducedLSA`: the same cycle data pass to the networks induced on a set of taxa,
  whose cycles are traces of those of `N⁻` (`Identify/InducedCycles.lean`) with the order of
  `adjacentBlocks_induced_iff`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-- Two functions with the same fibres have ranges of the same size. -/
theorem ncard_range_eq_of_eq_iff {α β γ : Type*} {f : α → β} {g : α → γ}
    (h : ∀ a b, f a = f b ↔ g a = g b) : (Set.range f).ncard = (Set.range g).ncard := by
  refine Set.ncard_congr (fun u hu => g (Classical.choose hu)) (fun _ _ => ⟨_, rfl⟩) ?_ ?_
  · intro u u' hu hu' huu'
    rw [← Classical.choose_spec hu, ← Classical.choose_spec hu']
    exact (h _ _).2 huu'
  · rintro _ ⟨a, rfl⟩
    exact ⟨f a, ⟨a, rfl⟩, (h _ _).1 (Classical.choose_spec (⟨a, rfl⟩ : f a ∈ Set.range f))⟩

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

variable {X : Type} [Fintype X] [DecidableEq X] {V E : Type} [Fintype V] [Fintype E]

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
  have hSS : bcSets N₁ θ₁ = bcSets N₂ θ₂ := by
    rw [← bcSetsOf_cf, hR, bcSetsOf_cf]
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

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- **Adjacent blocks are the blocks of the two ends of an edge of the cycle.** -/
theorem adjacentBlocks_iff_adjOn_blockNode {N : RootedNetwork V E X} {hN : IsBinaryRootedNetwork N}
    {hX : Nontrivial X} (h1 : IsLevelOne N.graph) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) (x y : X) :
    AdjacentBlocks (unrooted N hN hX) C x y ↔ (unrooted N hN hX).graph.AdjOn C
      (blockNode (unrooted N hN hX) C x) (blockNode (unrooted N hN hX) C y) := by
  constructor
  · rintro ⟨e, he, u, w, hj, hxu, hyw⟩
    have hu : u ∈ cycleNodes (unrooted N hN hX).graph C := by
      rcases hj with ⟨h, -⟩ | ⟨-, h⟩
      exacts [⟨e, he, Or.inl h⟩, ⟨e, he, Or.inr h⟩]
    have hw : w ∈ cycleNodes (unrooted N hN hX).graph C := by
      rcases hj with ⟨-, h⟩ | ⟨h, -⟩
      exacts [⟨e, he, Or.inr h⟩, ⟨e, he, Or.inl h⟩]
    rw [← eq_blockNode h1 hC hu hxu, ← eq_blockNode h1 hC hw hyw]
    exact ⟨e, he, hj⟩
  · rintro ⟨e, he, hj⟩
    exact ⟨e, he, _, _, hj, (blockNode_spec hC x).2, (blockNode_spec hC y).2⟩

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- **Two cycles with the same blocks and the same adjacent blocks join the same blocks avoiding the
same blocks**: the nodes of the first cycle correspond to those of the second through their blocks,
with the same edges between them. -/
theorem joinedAvoiding_of_sameBlock_of_adjacentBlocks {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} {hN₁ : IsBinaryRootedNetwork N₁}
    {hN₂ : IsBinaryRootedNetwork N₂} {hX : Nontrivial X} (h1₁ : IsLevelOne N₁.graph)
    (h1₂ : IsLevelOne N₂.graph) {C₁ C₂ : Set _} (hC₁ : IsCycle (unrooted N₁ hN₁ hX).graph C₁)
    (hC₂ : IsCycle (unrooted N₂ hN₂ hX).graph C₂)
    (hB : ∀ x y, SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y ↔
      SameBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ x y)
    (hA : ∀ x y, AdjacentBlocks (unrooted N₁ hN₁ hX) C₁ x y ↔
      AdjacentBlocks (unrooted N₂ hN₂ hX) C₂ x y)
    {T : Set X} {x y : X} (h : JoinedAvoiding (unrooted N₁ hN₁ hX) C₁ T x y) :
    JoinedAvoiding (unrooted N₂ hN₂ hX) C₂ T x y := by
  rw [joinedAvoiding_iff_reflTransGen hN₁ h1₁ hC₁] at h
  rw [joinedAvoiding_iff_reflTransGen hN₂ h1₂ hC₂]
  -- a taxon of the block of each node of `C₁`
  let τ : SemidirectedVertex hN₁.1 hX → X := fun u =>
    Classical.epsilon fun t => blockNode (unrooted N₁ hN₁ hX) C₁ t = u
  have hτ : ∀ u ∈ cycleNodes (unrooted N₁ hN₁ hX).graph C₁,
      blockNode (unrooted N₁ hN₁ hX) C₁ (τ u) = u := fun u hu =>
    Classical.epsilon_spec (p := fun t => blockNode (unrooted N₁ hN₁ hX) C₁ t = u)
      (exists_blockNode_eq h1₁ hC₁ hu)
  -- the node of `C₂` of the block of the same taxa
  have hβ : ∀ u ∈ cycleNodes (unrooted N₁ hN₁ hX).graph C₁, ∀ t,
      blockNode (unrooted N₁ hN₁ hX) C₁ t = u ↔
        blockNode (unrooted N₂ hN₂ hX) C₂ t = blockNode (unrooted N₂ hN₂ hX) C₂ (τ u) :=
    fun u hu t => by
      rw [← sameBlock_iff_blockNode_eq h1₂ hC₂, ← hB, sameBlock_iff_blockNode_eq h1₁ hC₁, hτ u hu]
  have hend : ∀ {a b}, (unrooted N₁ hN₁ hX).graph.AdjOn C₁ a b →
      a ∈ cycleNodes (unrooted N₁ hN₁ hX).graph C₁ ∧
        b ∈ cycleNodes (unrooted N₁ hN₁ hX).graph C₁ := by
    rintro a b ⟨e, he, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
    exacts [⟨⟨e, he, Or.inl h₁⟩, ⟨e, he, Or.inr h₂⟩⟩, ⟨⟨e, he, Or.inr h₂⟩, ⟨e, he, Or.inl h₁⟩⟩]
  have hT : ∀ u ∈ cycleNodes (unrooted N₁ hN₁ hX).graph C₁,
      u ∈ blockNodes (unrooted N₁ hN₁ hX) C₁ T ↔
        blockNode (unrooted N₂ hN₂ hX) C₂ (τ u) ∈ blockNodes (unrooted N₂ hN₂ hX) C₂ T :=
    fun u hu => by
      rw [mem_blockNodes_iff_blockNode hN₁ h1₁ hC₁, mem_blockNodes_iff_blockNode hN₂ h1₂ hC₂]
      exact exists_congr fun t => and_congr_right fun _ => hβ u hu t
  have hlift := Relation.ReflTransGen.lift (fun u => blockNode (unrooted N₂ hN₂ hX) C₂ (τ u))
    (p := fun a b => (unrooted N₂ hN₂ hX).graph.AdjOn C₂ a b ∧
      a ∉ blockNodes (unrooted N₂ hN₂ hX) C₂ T ∧ b ∉ blockNodes (unrooted N₂ hN₂ hX) C₂ T)
    (fun a b ⟨hab, ha, hb⟩ => by
      obtain ⟨hma, hmb⟩ := hend hab
      refine ⟨?_, fun h => ha ((hT a hma).2 h), fun h => hb ((hT b hmb).2 h)⟩
      rw [← hτ a hma, ← hτ b hmb, ← adjacentBlocks_iff_adjOn_blockNode h1₁ hC₁, hA] at hab
      rwa [← adjacentBlocks_iff_adjOn_blockNode h1₂ hC₂]) _ _ h
  have hx := (hβ _ (blockNode_mem hC₁ x) x).1 rfl
  have hy := (hβ _ (blockNode_mem hC₁ y) y).1 rfl
  dsimp only [Function.onFun] at hlift
  rwa [← hx, ← hy] at hlift

omit [Fintype X] [DecidableEq X] in
/-- **The same cycle data pass to the networks induced on `Y`.** A cycle `C₁'` of size at least four
of `(N₁⊕_Y)⁻` comes from the cycle `C₁` of `N₁⁻` with the same hybrid node, whose blocks with taxa of
`Y` are those of `C₁'` (`exists_unrooted_cycle_of_induced`, `blockNode_eq_iff_induced`); so `C₁` has
size at least four, and its counterpart `C₂` in `N₂⁻` has taxa of `Y` in its hybrid block and in
another block (the hybrid blocks are the same when the size is at least five, and every block of `C₁`
has taxa of `Y` when the size is four). So `C₂` induces a cycle `C₂'` of `(N₂⊕_Y)⁻`
(`exists_induced_cycle_of_unrooted`), with the traces on `Y` of the same blocks, the same hybrid
block, and the same adjacent blocks: those of `C₁` and `C₂` joined avoiding the blocks of the other
taxa of `Y` (`adjacentBlocks_induced_iff`, `joinedAvoiding_of_sameBlock_of_adjacentBlocks`). -/
theorem SameCycleData.inducedLSA {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hX : Nontrivial X) (hD : SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX)) {Y : Set X}
    (hY : Y.Nontrivial) :
    SameCycleData (inducedLSAUnrooted N₁ hN₁ Y hY) (inducedLSAUnrooted N₂ hN₂ Y hY) := by
  have h1Y₁ := isLevelOne_inducedLSA_graph hN₁.1 h1₁ hY
  have h1Y₂ := isLevelOne_inducedLSA_graph hN₂.1 h1₂ hY
  intro C₁' hC₁' w₁ hw₁
  obtain ⟨hC₁'c, hC₁'4⟩ := hC₁'
  -- the cycle `C₁` of `N₁⁻` with the same hybrid node
  obtain ⟨C₁, v₁, hC₁, hv₁, hwv₁⟩ := exists_unrooted_cycle_of_induced hN₁ h1₁ hX hY hw₁
  have hββ₁ : ∀ a b : Y, blockNode (unrooted N₁ hN₁ hX) C₁ a = blockNode (unrooted N₁ hN₁ hX) C₁ b ↔
      blockNode (inducedLSAUnrooted N₁ hN₁ Y hY) C₁' a =
        blockNode (inducedLSAUnrooted N₁ hN₁ Y hY) C₁' b := fun a b =>
    blockNode_eq_iff_induced hN₁ h1₁ hX hY hC₁'c hw₁ hC₁ hv₁ hwv₁ a.2 b.2
  -- the size of `C₁'` is the number of blocks of `C₁` with taxa of `Y`
  have hcard₁ : C₁'.ncard =
      (Set.range fun a : Y => blockNode (unrooted N₁ hN₁ hX) C₁ a).ncard := by
    rw [← ncard_cycleNodes hC₁'c, cycleNodes_eq_range_blockNode _ h1Y₁ hC₁'c]
    exact ncard_range_eq_of_eq_iff fun a b => (hββ₁ a b).symm
  have hsub₁ : (Set.range fun a : Y => blockNode (unrooted N₁ hN₁ hX) C₁ a) ⊆
      cycleNodes (unrooted N₁ hN₁ hX).graph C₁ := by
    rintro _ ⟨a, rfl⟩
    exact blockNode_mem hC₁ _
  have hle₁ : C₁'.ncard ≤ C₁.ncard := by
    rw [hcard₁, ← ncard_cycleNodes hC₁]
    exact Set.ncard_le_ncard hsub₁ (Set.toFinite _)
  -- the counterpart `C₂` of `C₁`
  obtain ⟨C₂, v₂, ⟨hC₂, hC₂4⟩, hv₂, hK, hB, hA, hH⟩ := hD C₁ ⟨hC₁, hC₁'4.trans hle₁⟩ v₁ hv₁
  have hsb₁ := sameBlock_iff_blockNode_eq h1₁ hC₁
  have hsb₂ := sameBlock_iff_blockNode_eq h1₂ hC₂
  -- a taxon of `Y` in the hybrid block of `C₂`
  obtain ⟨a, ha⟩ := exists_blockNode_eq h1Y₁ hC₁'c hw₁.mem_cycleNodes
  have ha₁ : blockNode (unrooted N₁ hN₁ hX) C₁ a = v₁ :=
    (blockNode_eq_hybrid_iff_induced hN₁ h1₁ hX hY hC₁'c hw₁ hC₁ hv₁ hwv₁ a.2).2 ha
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Y, blockNode (unrooted N₂ hN₂ hX) C₂ x₀ = v₂ := by
    by_cases h5 : 5 ≤ C₁.ncard
    · refine ⟨a, (blockNode_eq_iff_descendsFrom h1₂ hC₂ hv₂ a).2 ((hH h5 a).1 ?_)⟩
      exact (blockNode_eq_iff_descendsFrom h1₁ hC₁ hv₁ a).1 ha₁
    · -- every block of the 4-cycle `C₁` has a taxon of `Y`
      have hrange : (Set.range fun a : Y => blockNode (unrooted N₁ hN₁ hX) C₁ a) =
          cycleNodes (unrooted N₁ hN₁ hX).graph C₁ := by
        refine Set.eq_of_subset_of_ncard_le hsub₁ ?_ (Set.toFinite _)
        rw [ncard_cycleNodes hC₁, ← hcard₁]
        omega
      obtain ⟨t, ht⟩ := exists_blockNode_eq h1₂ hC₂ hv₂.mem_cycleNodes
      obtain ⟨b, hb⟩ : blockNode (unrooted N₁ hN₁ hX) C₁ t ∈
          Set.range fun a : Y => blockNode (unrooted N₁ hN₁ hX) C₁ a :=
        hrange ▸ blockNode_mem hC₁ t
      exact ⟨b, ((hsb₂ b t).1 ((hB b t).1 ((hsb₁ b t).2 hb))).trans ht⟩
  -- a taxon of `Y` in another block of `C₂`
  obtain ⟨u, hu, huw⟩ := hC₁'c.exists_mem_cycleNodes_notMem (Set.finite_singleton w₁)
    (by rw [Set.ncard_singleton]; omega)
  obtain ⟨b, hb⟩ := exists_blockNode_eq h1Y₁ hC₁'c hu
  have hab₂ : blockNode (unrooted N₂ hN₂ hX) C₂ a ≠ blockNode (unrooted N₂ hN₂ hX) C₂ b := by
    intro h
    refine huw (Set.mem_singleton_iff.2 (hb.symm.trans (((hββ₁ a b).1 ?_).symm.trans ha)))
    exact (hsb₁ a b).1 ((hB a b).2 ((hsb₂ a b).2 h))
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Y, blockNode (unrooted N₂ hN₂ hX) C₂ y₀ ≠ v₂ := by
    by_cases ha₂ : blockNode (unrooted N₂ hN₂ hX) C₂ a = v₂
    · exact ⟨b, fun h => hab₂ (ha₂.trans h.symm)⟩
    · exact ⟨a, ha₂⟩
  -- the cycle `C₂'` of `(N₂⊕_Y)⁻` induced by `C₂`
  obtain ⟨C₂', w₂, hC₂'c, hw₂, hwv₂⟩ := exists_induced_cycle_of_unrooted hN₂ h1₂ hX hY hv₂ x₀.2 y₀.2
    ((descendsFrom_iff_reaches hN₂ h1₂ hC₂ hv₂ x₀).1
      ((blockNode_eq_iff_descendsFrom h1₂ hC₂ hv₂ x₀).1 hx₀))
    (fun h => hy₀ ((blockNode_eq_iff_descendsFrom h1₂ hC₂ hv₂ y₀).2
      ((descendsFrom_iff_reaches hN₂ h1₂ hC₂ hv₂ y₀).2 h)))
  have hββ₂ : ∀ a b : Y, blockNode (unrooted N₂ hN₂ hX) C₂ a = blockNode (unrooted N₂ hN₂ hX) C₂ b ↔
      blockNode (inducedLSAUnrooted N₂ hN₂ Y hY) C₂' a =
        blockNode (inducedLSAUnrooted N₂ hN₂ Y hY) C₂' b := fun a b =>
    blockNode_eq_iff_induced hN₂ h1₂ hX hY hC₂'c hw₂ hC₂ hv₂ hwv₂ a.2 b.2
  -- the same blocks
  have hβ' : ∀ a b : Y, blockNode (inducedLSAUnrooted N₁ hN₁ Y hY) C₁' a =
      blockNode (inducedLSAUnrooted N₁ hN₁ Y hY) C₁' b ↔
        blockNode (inducedLSAUnrooted N₂ hN₂ Y hY) C₂' a =
          blockNode (inducedLSAUnrooted N₂ hN₂ Y hY) C₂' b := fun a b =>
    (hββ₁ a b).symm.trans ((hsb₁ a b).symm.trans ((hB a b).trans ((hsb₂ a b).trans (hββ₂ a b))))
  have hblk : ∀ a b : Y,
      SameBlock (inducedLSAUnrooted N₁ hN₁ Y hY).graph (inducedLSAUnrooted N₁ hN₁ Y hY).leaf C₁' a b ↔
        SameBlock (inducedLSAUnrooted N₂ hN₂ Y hY).graph (inducedLSAUnrooted N₂ hN₂ Y hY).leaf C₂'
          a b := fun a b =>
    (sameBlock_iff_blockNode_eq h1Y₁ hC₁'c a b).trans
      ((hβ' a b).trans (sameBlock_iff_blockNode_eq h1Y₂ hC₂'c a b).symm)
  -- the same size
  have hcard : C₂'.ncard = C₁'.ncard := by
    rw [← ncard_cycleNodes hC₂'c, ← ncard_cycleNodes hC₁'c,
      cycleNodes_eq_range_blockNode _ h1Y₂ hC₂'c, cycleNodes_eq_range_blockNode _ h1Y₁ hC₁'c]
    exact ncard_range_eq_of_eq_iff fun a b => (hβ' a b).symm
  refine ⟨C₂', w₂, ⟨hC₂'c, by rw [hcard]; exact hC₁'4⟩, hw₂, hcard, hblk, fun a b => ?_,
    fun h5 a => ?_⟩
  · -- the same adjacent blocks
    rw [adjacentBlocks_induced_iff hN₁ h1₁ hX hY hC₁'c (by omega) hw₁ hC₁ hv₁ hwv₁,
      adjacentBlocks_induced_iff hN₂ h1₂ hX hY hC₂'c (by omega) hw₂ hC₂ hv₂ hwv₂]
    have hT : {t | t ∈ Y ∧
        ¬ SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ a t ∧
        ¬ SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ b t} =
        {t | t ∈ Y ∧ ¬ SameBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ a t ∧
          ¬ SameBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ b t} :=
      Set.ext fun t => and_congr_right fun _ => and_congr (not_congr (hB _ _)) (not_congr (hB _ _))
    rw [hT]
    exact and_congr (not_congr (hB a b))
      ⟨joinedAvoiding_of_sameBlock_of_adjacentBlocks h1₁ h1₂ hC₁ hC₂ hB hA,
        joinedAvoiding_of_sameBlock_of_adjacentBlocks h1₂ h1₁ hC₂ hC₁ (fun x y => (hB x y).symm)
          (fun x y => (hA x y).symm)⟩
  · -- the same hybrid block
    have h5' : 5 ≤ C₁.ncard := h5.trans hle₁
    exact (blockNode_eq_iff_descendsFrom h1Y₁ hC₁'c hw₁ a).symm.trans
      ((blockNode_eq_hybrid_iff_induced hN₁ h1₁ hX hY hC₁'c hw₁ hC₁ hv₁ hwv₁ a.2).symm.trans
        ((blockNode_eq_iff_descendsFrom h1₁ hC₁ hv₁ a).trans ((hH h5' a).trans
          ((blockNode_eq_iff_descendsFrom h1₂ hC₂ hv₂ a).symm.trans
            ((blockNode_eq_hybrid_iff_induced hN₂ h1₂ hX hY hC₂'c hw₂ hC₂ hv₂ hwv₂ a.2).trans
              (blockNode_eq_iff_descendsFrom h1Y₂ hC₂'c hw₂ a))))))

end Banos2019
