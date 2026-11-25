module

public import Banos2019.Identify.TildeBase
public import Banos2019.Identify.NonDegenerate
public import Banos2019.Identify.Glue
public import Banos2019.Identify.InducedCycles
public import Banos2019.Identify.TildeCycle
public import Banos2019.Identify.SameData

/-!
# The induction of Theorem 4 (Baños 2019, Section 8)

`TildeDeterminedData m` is the claim of the induction: the claim `TildeDetermined m` for networks
with the same cycle data in both directions (`SameCycleData`, which Lemmas 15 and 16 give for the
networks of Theorem 4) and the same 4-network blocks (`SameFourNetworkBlocks`, which Lemma 14 gives).
It holds for every `m` (`tildeDeterminedData`), by strong induction on `m`:

* `tildeDeterminedData_zero`: no cycle of size at least four (`tildeDetermined_zero`,
  `Identify/TildeBase.lean`).
* `tildeDeterminedData_one`: one cycle `C₁` of size at least four, by strong induction on the number of
  taxa. The cycle `C₂` of `N₂⁻` with the same blocks, adjacent blocks and hybrid block gives the
  isomorphism when the blocks are single taxa (`tilde_sdIso_of_singletonBlocks`). Otherwise a block `P`
  with at least two taxa splits `Ñ` into the networks `Ñ` of the networks induced on `Pᶜ ∪ {s₂}`, which
  has fewer taxa, and on `P ∪ {s₁}`, which has no cycle of size at least four.
* `tildeDeterminedData_of_lt`: for `m ≥ 2` cycles, a leaf of the tree of cycles of `Ñ₁` arises
  from a cycle `C₁` all of whose blocks but that of a node `u₁` are 4-network blocks
  (`exists_leaf_bigCycle`). The cycle `C₂` of `N₂⁻` with the same blocks gives a leaf of the tree of
  cycles of `Ñ₂`, and its node `u₂` with the block of `u₁` (`exists_isLeafNode_counterpart`, from
  the same 4-network blocks). The two networks split at `u₁` and `u₂` into networks with fewer
  cycles of size at least four.

Both steps glue the two pieces (`tilde_sdIso_of_leafCycle`): `Ñ` of `N₁` and of `N₂` are the gluings of
the networks `Ñ` of the pieces (`tilde_sdIso_glue`), and isomorphic pieces glue to isomorphic networks
(`glue_congr`). The pieces satisfy the conditions of Theorem 4 (`Identify/InducedCycles.lean`), have
the same cycle data in both directions (`SameCycleData.inducedLSA`), and so the same 4-network blocks
(`sameFourNetworkBlocks_inducedLSA`).

* `bigCycleCount_inducedLSA_insert_compl_le_one`, `bigCycleCount_inducedLSA_insert_lt`: the numbers of
  cycles of size at least four of the two pieces.
* `isFourNetworkBlock_blockNode_iff`: for two networks with the same 4-network blocks, blocks of two
  cycles with the same taxa are both 4-network blocks or neither.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-- Four elements of `insert a T` include two distinct elements of `T`. -/
theorem exists_ne_mem_of_card_four_subset_insert {α : Type*} [DecidableEq α] {s : Finset α}
    (hs : #s = 4) {a : α} {T : Set α} (h : (s : Set α) ⊆ insert a T) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x ∈ T ∧ y ∈ T := by
  have h1 : 1 < #(s.erase a) := by
    have := Finset.pred_card_le_card_erase (s := s) (a := a)
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h1
  obtain ⟨hxa, hx⟩ := Finset.mem_erase.1 hx
  obtain ⟨hya, hy⟩ := Finset.mem_erase.1 hy
  exact ⟨x, hx, y, hy, hxy, (Set.mem_insert_iff.1 (h (mem_coe.2 hx))).resolve_left hxa,
    (Set.mem_insert_iff.1 (h (mem_coe.2 hy))).resolve_left hya⟩

/-- A cycle does not separate four taxa of `insert a T` when the taxa of `T` are in one of its
blocks. -/
theorem not_separatesQuartet_of_subset_insert {V' E' X' : Type*} [DecidableEq X']
    {G : SemidirectedNetwork V' E' X'} {C : Set E'} {v : V'} {s : Finset X'} (hs : #s = 4) {a : X'}
    {T : Set X'} (hT : ∀ x ∈ T, ∀ y ∈ T, SameBlock G.graph G.leaf C x y)
    (h : (s : Set X') ⊆ insert a T) : ¬ SeparatesQuartet G C v s := by
  intro hsep
  obtain ⟨x, hx, y, hy, hxy, hxT, hyT⟩ := exists_ne_mem_of_card_four_subset_insert hs h
  exact hsep.2.2.1 x hx y hy hxy (hT x hxT y hyT)

/-- **The claim of the induction of Theorem 4** for `m` cycles of size at least four: two binary
level-1 networks on the same taxa, with parameters satisfying `GoodParams`, the same orderings of
concordance factors, the same cycle data in both directions and the same 4-network blocks, the first
with `m` cycles of size at least four in `N⁻`, have isomorphic networks `Ñ`. -/
def TildeDeterminedData (m : ℕ) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (hX : Nontrivial X) (V₁ E₁ V₂ E₂ : Type) [Fintype V₁]
    [Fintype E₁] [Fintype V₂] [Fintype E₂] (N₁ : RootedNetwork V₁ E₁ X) (N₂ : RootedNetwork V₂ E₂ X)
    (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂),
    IsLevelOne N₁.graph → IsLevelOne N₂.graph → ∀ θ₁ θ₂, IsMetricNetwork N₁ θ₁ →
    IsMetricNetwork N₂ θ₂ → GoodParams hX N₁ θ₁ → GoodParams hX N₂ θ₂ →
    SameOrdering (cf N₁ θ₁) (cf N₂ θ₂) → SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX) →
    SameCycleData (unrooted N₂ hN₂ hX) (unrooted N₁ hN₁ hX) →
    SameFourNetworkBlocks (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX) →
    bigCycleCount (unrooted N₁ hN₁ hX) = m →
    Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX)))

/-- **No cycle of size at least four**: the base case `tildeDetermined_zero`, which does not use the
cycle data or the 4-network blocks. -/
theorem tildeDeterminedData_zero : TildeDeterminedData 0 :=
  fun X _ _ hX V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord _ _ _ hc =>
    tildeDetermined_zero X hX V₁ E₁ V₂ E₂ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord hc

variable {X : Type} [Fintype X] [DecidableEq X] {V E : Type} [Fintype V] [Fintype E]

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- The taxa of the block of the node of a cycle whose block contains `x` are those in the same block
as `x`. -/
theorem mem_nodeBlock_blockNode_iff {N : RootedNetwork V E X} {hN : IsBinaryRootedNetwork N}
    {hX : Nontrivial X} (h1 : IsLevelOne N.graph) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) (x z : X) :
    z ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C
        (blockNode (unrooted N hN hX) C x) ↔
      SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x z := by
  rw [sameBlock_iff_blockNode_eq h1 hC]
  constructor
  · intro hz
    exact eq_blockNode h1 hC (blockNode_mem hC x) hz
  · intro h
    rw [h]
    exact (blockNode_spec hC z).2

/-- **The piece on `Pᶜ ∪ {s₂}` has at most one cycle of size at least four** when every cycle of size
at least four of `N⁻` other than `C` has the taxa outside `P` in one of its blocks: only `C` can
separate four of its taxa. -/
theorem bigCycleCount_inducedLSA_insert_compl_le_one {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _}
    {P : Finset X}
    (hleaf : ∀ C' ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4, C' ≠ C → ∀ x y, x ∉ P → y ∉ P →
      SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C' x y)
    (s₂ : X) (hY : ((insert s₂ Pᶜ : Finset X) : Set X).Nontrivial) :
    bigCycleCount (unrooted (inducedLSA N hN.1 _ hY) (inducedLSA_isBinaryRootedNetwork hN hY)
      hY.coe_sort) ≤ 1 := by
  refine (bigCycleCount_inducedLSA_le hN h1 hX hY).trans ?_
  refine (Set.ncard_le_ncard (t := {C}) ?_ (Set.finite_singleton C)).trans (Set.ncard_singleton C).le
  rintro C' ⟨hC', s, hsY, hs4, v, hsep⟩
  by_contra hne
  rw [Set.mem_singleton_iff] at hne
  refine not_separatesQuartet_of_subset_insert hs4 (a := s₂) (T := (↑P)ᶜ)
    (fun x hx y hy => hleaf C' hC' hne x y hx hy) ?_ hsep
  simpa only [coe_insert, coe_compl] using hsY

/-- **The piece on `P ∪ {s₁}` has fewer cycles of size at least four than `N⁻`** when the taxa of `P`
are in one block of the cycle `C` of size at least four: `C` separates no four of its taxa. -/
theorem bigCycleCount_inducedLSA_insert_lt {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _}
    (hC : C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4) {P : Finset X}
    (hP : ∀ x ∈ P, ∀ y ∈ P, SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y)
    (s₁ : X) (hY : ((insert s₁ P : Finset X) : Set X).Nontrivial) :
    bigCycleCount (unrooted (inducedLSA N hN.1 _ hY) (inducedLSA_isBinaryRootedNetwork hN hY)
      hY.coe_sort) < bigCycleCount (unrooted N hN hX) := by
  refine (bigCycleCount_inducedLSA_le hN h1 hX hY).trans_lt ?_
  unfold bigCycleCount
  refine Set.ncard_lt_ncard (LE.le.ssubset_of_not_superset (fun C' hC' => hC'.1) ?_)
    (Set.toFinite _)
  intro hsub
  obtain ⟨-, s, hsY, hs4, v, hsep⟩ := hsub hC
  refine not_separatesQuartet_of_subset_insert hs4 (a := s₁) (T := ↑P) hP ?_ hsep
  simpa only [coe_insert] using hsY

/-- **The claim for a piece**: `TildeDeterminedData k` gives isomorphic networks `Ñ` for the networks
induced on `Y` with `k` cycles of size at least four. Their cycle data in both directions come from
those of `N₁` and `N₂` (`SameCycleData.inducedLSA`), and give their 4-network blocks
(`sameFourNetworkBlocks_inducedLSA`). -/
theorem nonempty_sdIso_tilde_inducedLSA {k : ℕ} (hk : TildeDeterminedData k) {V' E' : Type}
    [Fintype V'] [Fintype E'] {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X}
    (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph)
    (h1₂ : IsLevelOne N₂.graph) (hX : Nontrivial X) {θ₁ : MetricData E} {θ₂ : MetricData E'}
    (hθ₁ : IsMetricNetwork N₁ θ₁) (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁)
    (hG₂ : GoodParams hX N₂ θ₂) (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂))
    (hD : SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX))
    (hD' : SameCycleData (unrooted N₂ hN₂ hX) (unrooted N₁ hN₁ hX)) {Y : Set X} (hY : Y.Nontrivial)
    (hcount : bigCycleCount (unrooted (inducedLSA N₁ hN₁.1 Y hY)
      (inducedLSA_isBinaryRootedNetwork hN₁ hY) hY.coe_sort) = k) :
    Nonempty (SDIso
      (tildeNetwork (unrooted (inducedLSA N₁ hN₁.1 Y hY) (inducedLSA_isBinaryRootedNetwork hN₁ hY)
        hY.coe_sort))
      (tildeNetwork (unrooted (inducedLSA N₂ hN₂.1 Y hY) (inducedLSA_isBinaryRootedNetwork hN₂ hY)
        hY.coe_sort))) :=
  hk Y hY.coe_sort _ _ _ _ _ _ (inducedLSA_isBinaryRootedNetwork hN₁ hY)
    (inducedLSA_isBinaryRootedNetwork hN₂ hY) (inducedLSA_isLevelOne hN₁ h1₁ hY)
    (inducedLSA_isLevelOne hN₂ h1₂ hY) _ _ (inducedLSA_isMetricNetwork hN₁ hθ₁ hY)
    (inducedLSA_isMetricNetwork hN₂ hθ₂ hY) (goodParams_inducedLSA hN₁ h1₁ hX hθ₁ hG₁ hY)
    (goodParams_inducedLSA hN₂ h1₂ hX hθ₂ hG₂ hY)
    (sameOrdering_inducedLSA hN₁ h1₁ hN₂ h1₂ hθ₁ hθ₂ hord hY)
    (hD.inducedLSA hN₁ hN₂ h1₁ h1₂ hX hY) (hD'.inducedLSA hN₂ hN₁ h1₂ h1₁ hX hY)
    (sameFourNetworkBlocks_inducedLSA hN₁ hN₂ h1₁ h1₂ hX hD hD' hY) hcount

/-- **Gluing the pieces**: for nodes `u₁`, `u₂` of cycles of `N₁⁻` and `N₂⁻` with the same block `P`,
if the networks `Ñ` of the networks induced on `Pᶜ ∪ {s₂}` and on `P ∪ {s₁}` are isomorphic, so are
the networks `Ñ` of `N₁` and `N₂`. -/
theorem tilde_sdIso_of_pieces {V' E' : Type} [Fintype V'] [Fintype E'] {N₁ : RootedNetwork V E X}
    {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂)
    (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph) (hX : Nontrivial X) {C₁ : Set _}
    (hC₁ : IsCycle (unrooted N₁ hN₁ hX).graph C₁) {u₁}
    (hu₁ : u₁ ∈ cycleNodes (unrooted N₁ hN₁ hX).graph C₁) {C₂ : Set _}
    (hC₂ : IsCycle (unrooted N₂ hN₂ hX).graph C₂) {u₂}
    (hu₂ : u₂ ∈ cycleNodes (unrooted N₂ hN₂ hX).graph C₂) {P : Finset X}
    (hP₁ : ∀ x, x ∈ P ↔ x ∈ nodeBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ u₁)
    (hP₂ : ∀ x, x ∈ P ↔ x ∈ nodeBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ u₂)
    {s₁ s₂ : X} (hs₁ : s₁ ∉ P) (hs₂ : s₂ ∈ P)
    (hZ₁ : ((insert s₂ Pᶜ : Finset X) : Set X).Nontrivial)
    (hZ₂ : ((insert s₁ P : Finset X) : Set X).Nontrivial)
    (i₁ : Nonempty (SDIso
      (tildeNetwork (unrooted (inducedLSA N₁ hN₁.1 _ hZ₁) (inducedLSA_isBinaryRootedNetwork hN₁ hZ₁)
        hZ₁.coe_sort))
      (tildeNetwork (unrooted (inducedLSA N₂ hN₂.1 _ hZ₁) (inducedLSA_isBinaryRootedNetwork hN₂ hZ₁)
        hZ₁.coe_sort))))
    (i₂ : Nonempty (SDIso
      (tildeNetwork (unrooted (inducedLSA N₁ hN₁.1 _ hZ₂) (inducedLSA_isBinaryRootedNetwork hN₁ hZ₂)
        hZ₂.coe_sort))
      (tildeNetwork (unrooted (inducedLSA N₂ hN₂.1 _ hZ₂) (inducedLSA_isBinaryRootedNetwork hN₂ hZ₂)
        hZ₂.coe_sort)))) :
    Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX))) := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hne₁, hne₂, ⟨A⟩⟩ :=
    tilde_sdIso_glue hN₁ h1₁ hX hC₁ hu₁ hP₁ hs₁ hs₂ hZ₁ hZ₂
  obtain ⟨w₁', w₂', hw₁', hw₂', hne₁', hne₂', ⟨B⟩⟩ :=
    tilde_sdIso_glue hN₂ h1₂ hX hC₂ hu₂ hP₂ hs₁ hs₂ hZ₁ hZ₂
  obtain ⟨j₁⟩ := i₁
  obtain ⟨j₂⟩ := i₂
  obtain ⟨g⟩ := glue_congr hw₁ hw₂ hw₁' hw₂' (blockSide P s₁ s₂) j₁ j₂
  exact ⟨(A.trans g).trans B.symm⟩

/-- **The step of the induction of Theorem 4**: let `u₁` be a node of a cycle `C₁` of size at least
four of `N₁⁻` and `u₂` a node of a cycle `C₂` of `N₂⁻`, both with the block `P`, and `s₂ ∈ P`,
`s₁ ∉ P` two taxa, such that every other cycle of size at least four of `N₁⁻` has the taxa outside `P`
in one of its blocks. If the networks induced on `Pᶜ ∪ {s₂}` (at most one cycle of size at least
four) and on `P ∪ {s₁}` (fewer cycles of size at least four than `N₁⁻`) have isomorphic networks `Ñ`,
so have `N₁` and `N₂`: `Ñ` of each network is the gluing at its node `uᵢ` of the networks `Ñ` of its
pieces (`tilde_sdIso_of_pieces`). -/
theorem tilde_sdIso_of_leafCycle {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hX : Nontrivial X) {C₁ : Set _} (hC₁ : C₁ ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4)
    {u₁} (hu₁ : u₁ ∈ cycleNodes (unrooted N₁ hN₁ hX).graph C₁) {C₂ : Set _}
    (hC₂ : IsCycle (unrooted N₂ hN₂ hX).graph C₂) {u₂}
    (hu₂ : u₂ ∈ cycleNodes (unrooted N₂ hN₂ hX).graph C₂) {P : Finset X}
    (hP₁ : ∀ x, x ∈ P ↔ x ∈ nodeBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ u₁)
    (hP₂ : ∀ x, x ∈ P ↔ x ∈ nodeBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ u₂)
    {s₁ s₂ : X} (hs₁ : s₁ ∉ P) (hs₂ : s₂ ∈ P)
    (hleaf : ∀ C' ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4, C' ≠ C₁ → ∀ x y, x ∉ P →
      y ∉ P → SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C' x y)
    (H₁ : ∀ hY : ((insert s₂ Pᶜ : Finset X) : Set X).Nontrivial,
      bigCycleCount (unrooted (inducedLSA N₁ hN₁.1 _ hY) (inducedLSA_isBinaryRootedNetwork hN₁ hY)
        hY.coe_sort) ≤ 1 →
      Nonempty (SDIso
        (tildeNetwork (unrooted (inducedLSA N₁ hN₁.1 _ hY) (inducedLSA_isBinaryRootedNetwork hN₁ hY)
          hY.coe_sort))
        (tildeNetwork (unrooted (inducedLSA N₂ hN₂.1 _ hY) (inducedLSA_isBinaryRootedNetwork hN₂ hY)
          hY.coe_sort))))
    (H₂ : ∀ hY : ((insert s₁ P : Finset X) : Set X).Nontrivial,
      bigCycleCount (unrooted (inducedLSA N₁ hN₁.1 _ hY) (inducedLSA_isBinaryRootedNetwork hN₁ hY)
        hY.coe_sort) < bigCycleCount (unrooted N₁ hN₁ hX) →
      Nonempty (SDIso
        (tildeNetwork (unrooted (inducedLSA N₁ hN₁.1 _ hY) (inducedLSA_isBinaryRootedNetwork hN₁ hY)
          hY.coe_sort))
        (tildeNetwork (unrooted (inducedLSA N₂ hN₂.1 _ hY) (inducedLSA_isBinaryRootedNetwork hN₂ hY)
          hY.coe_sort)))) :
    Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX))) := by
  have hne : s₁ ≠ s₂ := fun h => hs₁ (h ▸ hs₂)
  have hZ₁ : ((insert s₂ Pᶜ : Finset X) : Set X).Nontrivial :=
    ⟨s₂, by simp, s₁, by simp [hs₁], hne.symm⟩
  have hZ₂ : ((insert s₁ P : Finset X) : Set X).Nontrivial := ⟨s₁, by simp, s₂, by simp [hs₂], hne⟩
  have hPP : ∀ x ∈ P, ∀ y ∈ P,
      SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y := fun x hx y hy =>
    (DirectedMultigraph.walks_symm _ ((hP₁ x).1 hx)).trans ((hP₁ y).1 hy)
  exact tilde_sdIso_of_pieces hN₁ hN₂ h1₁ h1₂ hX hC₁.1 hu₁ hC₂ hu₂ hP₁ hP₂ hs₁ hs₂ hZ₁ hZ₂
    (H₁ hZ₁ (bigCycleCount_inducedLSA_insert_compl_le_one hN₁ h1₁ hX hleaf s₂ hZ₁))
    (H₂ hZ₂ (bigCycleCount_inducedLSA_insert_lt hN₁ h1₁ hX hC₁ hPP s₁ hZ₂))

/-- **One cycle of size at least four** (proof of Theorem 4, the case of one cycle). The cycle data
give a cycle `C₂` of `N₂⁻` with the same blocks, adjacent blocks and hybrid block as the cycle `C₁` of
`N₁⁻`. When the blocks are single taxa, `Ñ₁` and `Ñ₂` are this cycle with a taxon at each node
(`tilde_sdIso_of_singletonBlocks`). Otherwise, for a block `P` with at least two taxa, a taxon
`s₂ ∈ P` and a taxon `s₁ ∉ P`, the networks `Ñ` are the gluings, at the nodes of `C₁` and `C₂` with
the block `P`, of those of the networks induced on `Pᶜ ∪ {s₂}`, which has fewer taxa and at most one
cycle of size at least four (induction on the number of taxa, or `tildeDeterminedData_zero`), and on
`P ∪ {s₁}`, which has none (`tildeDeterminedData_zero`). This is the paper's step of joining the tree
of each block, read with an outgroup, to its node of the cycle. -/
theorem tildeDeterminedData_one : TildeDeterminedData 1 := by
  intro X _ _
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card X = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ihn =>
  intro hX V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord hD hD' _ hc
  -- the cycle `C₁` of size at least four and its counterpart `C₂`
  obtain ⟨C₁, hbig⟩ := Set.ncard_eq_one.1 hc
  have hC₁ : C₁ ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4 := by
    rw [hbig]
    rfl
  obtain ⟨v₁, hv₁⟩ := exists_isHybridNodeOf h1₁ hC₁.1
  obtain ⟨C₂, v₂, hC₂, hv₂, -, hsame, hadj, hhyb⟩ := hD C₁ hC₁ v₁ hv₁
  by_cases hsing : ∀ x y, SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y →
      x = y
  · exact tilde_sdIso_of_singletonBlocks hN₁ hN₂ h1₁ h1₂ hX hC₁ hC₂ hv₁ hv₂ hsing
      (fun x y h => hsing x y ((hsame x y).2 h)) hadj hhyb
  push Not at hsing
  obtain ⟨x, y, hxy, hne⟩ := hsing
  -- the block `P` of `x`, which contains `y`, the nodes of `C₁` and `C₂` with this block, and a
  -- taxon `s₁` of another block
  set P := univ.filter fun z => SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x z
  have hP : ∀ z, z ∈ P ↔ SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x z :=
    fun z => by simp [P]
  have hP₁ : ∀ z, z ∈ P ↔ z ∈ nodeBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁
      (blockNode (unrooted N₁ hN₁ hX) C₁ x) := fun z =>
    (hP z).trans (mem_nodeBlock_blockNode_iff h1₁ hC₁.1 x z).symm
  have hP₂ : ∀ z, z ∈ P ↔ z ∈ nodeBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂
      (blockNode (unrooted N₂ hN₂ hX) C₂ x) := fun z =>
    ((hP z).trans (hsame x z)).trans (mem_nodeBlock_blockNode_iff h1₂ hC₂.1 x z).symm
  obtain ⟨u', hu', hu'x⟩ := hC₁.1.exists_mem_cycleNodes_notMem
    (Set.finite_singleton (blockNode (unrooted N₁ hN₁ hX) C₁ x))
    (by rw [Set.ncard_singleton]; have := hC₁.2; omega)
  obtain ⟨s₁, hs₁⟩ := exists_blockNode_eq h1₁ hC₁.1 hu'
  have hs₁P : s₁ ∉ P := by
    rw [hP, sameBlock_iff_blockNode_eq h1₁ hC₁.1, hs₁]
    exact fun h => hu'x h.symm
  refine tilde_sdIso_of_leafCycle hN₁ hN₂ h1₁ h1₂ hX hC₁ (blockNode_mem hC₁.1 x) hC₂.1
    (blockNode_mem hC₂.1 x) hP₁ hP₂ hs₁P ((hP x).2 .refl) ?_ ?_ ?_
  · -- `C₁` is the only cycle of size at least four
    intro C' hC' hC'C₁
    rw [hbig] at hC'
    exact absurd hC' hC'C₁
  · -- the piece on `Pᶜ ∪ {x}`: fewer taxa, at most one cycle of size at least four
    intro hY hY1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hY1 with h0 | h1
    · exact nonempty_sdIso_tilde_inducedLSA tildeDeterminedData_zero hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁
        hG₂ hord hD hD' hY h0
    · have hyY : y ∉ ((insert x Pᶜ : Finset X) : Set X) := by
        simp only [coe_insert, coe_compl, Set.mem_insert_iff, Set.mem_compl_iff, mem_coe, not_or,
          not_not]
        exact ⟨Ne.symm hne, (hP y).2 hxy⟩
      generalize ((insert x Pᶜ : Finset X) : Set X) = Y at hY hY1 h1 hyY ⊢
      refine ihn _ ?_ Y rfl hY.coe_sort _ _ _ _ _ _ (inducedLSA_isBinaryRootedNetwork hN₁ hY)
        (inducedLSA_isBinaryRootedNetwork hN₂ hY) (inducedLSA_isLevelOne hN₁ h1₁ hY)
        (inducedLSA_isLevelOne hN₂ h1₂ hY) _ _ (inducedLSA_isMetricNetwork hN₁ hθ₁ hY)
        (inducedLSA_isMetricNetwork hN₂ hθ₂ hY) (goodParams_inducedLSA hN₁ h1₁ hX hθ₁ hG₁ hY)
        (goodParams_inducedLSA hN₂ h1₂ hX hθ₂ hG₂ hY)
        (sameOrdering_inducedLSA hN₁ h1₁ hN₂ h1₂ hθ₁ hθ₂ hord hY)
        (hD.inducedLSA hN₁ hN₂ h1₁ h1₂ hX hY) (hD'.inducedLSA hN₂ hN₁ h1₂ h1₁ hX hY)
        (sameFourNetworkBlocks_inducedLSA hN₁ hN₂ h1₁ h1₂ hX hD hD' hY) h1
      rw [← hn]
      exact Fintype.card_subtype_lt hyY
  · -- the piece on `P ∪ {s₁}`: no cycle of size at least four
    intro hY hY1
    exact nonempty_sdIso_tilde_inducedLSA tildeDeterminedData_zero hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁
      hG₂ hord hD hD' hY (by omega)

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- **Blocks with the same taxa are both 4-network blocks or neither**, for two networks with the
same 4-network blocks: when the cycles `C₁` and `C₂` have the same blocks, the blocks of their nodes
with the taxon `t` have the same taxa. -/
theorem isFourNetworkBlock_blockNode_iff {V' E' : Type} [Fintype E'] {N₁ : RootedNetwork V E X}
    {N₂ : RootedNetwork V' E' X} {hN₁ : IsBinaryRootedNetwork N₁} {hN₂ : IsBinaryRootedNetwork N₂}
    {hX : Nontrivial X} (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hF : SameFourNetworkBlocks (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX)) {C₁ C₂ : Set _}
    (hC₁ : IsCycle (unrooted N₁ hN₁ hX).graph C₁) (hC₂ : IsCycle (unrooted N₂ hN₂ hX).graph C₂)
    (hsame : ∀ x y, SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y ↔
      SameBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ x y) (t : X) :
    IsFourNetworkBlock (unrooted N₁ hN₁ hX) C₁ (blockNode (unrooted N₁ hN₁ hX) C₁ t) ↔
      IsFourNetworkBlock (unrooted N₂ hN₂ hX) C₂ (blockNode (unrooted N₂ hN₂ hX) C₂ t) := by
  unfold SameFourNetworkBlocks at hF
  simp only [IsFourNetworkBlock, mem_nodeBlock_blockNode_iff h1₁ hC₁,
    mem_nodeBlock_blockNode_iff h1₂ hC₂, hsame, hF]

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- **The counterpart of a leaf cycle is a leaf cycle** (proof of Theorem 4, TeX l.1186): let `C₁` be
a cycle of size at least four of `N₁⁻` all of whose blocks but that of its node `u₁` are 4-network
blocks, the block of `u₁` not being one, and `C₂` a cycle of size at least four of `N₂⁻` with the
same blocks, the two networks having the same 4-network blocks. The blocks of `C₂` other than the one
with the taxa of the block of `u₁` have the taxa of blocks of other nodes of `C₁`, so they are
4-network blocks (`isFourNetworkBlock_blockNode_iff`), and the node of the tree of cycles of `Ñ₂`
arising from `C₂` is a leaf (`isLeafNode_iff_fourNetworkBlocks_unrooted`). This leaf gives a node
`u₂` of `C₂` all of whose other blocks are 4-network blocks
(`fourNetworkBlocks_of_isLeafNode_unrooted`); the block of `u₂` has the taxa of the block of `u₁`,
the only block of `C₂` that is not a 4-network block. -/
theorem exists_isLeafNode_counterpart {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hX : Nontrivial X) (hF : SameFourNetworkBlocks (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX))
    {C₁ : Set _} (hC₁ : C₁ ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4) {u₁}
    (hu₁ : u₁ ∈ cycleNodes (unrooted N₁ hN₁ hX).graph C₁)
    (hblock₁ : ∀ u' ∈ cycleNodes (unrooted N₁ hN₁ hX).graph C₁, u' ≠ u₁ →
      IsFourNetworkBlock (unrooted N₁ hN₁ hX) C₁ u')
    (hnot₁ : ¬ IsFourNetworkBlock (unrooted N₁ hN₁ hX) C₁ u₁) {C₂ : Set _}
    (hC₂ : C₂ ∈ cyclesOfSizeAtLeast (unrooted N₂ hN₂ hX).graph 4)
    (hsame : ∀ x y, SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y ↔
      SameBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ x y) :
    ∃ w, ArisesFrom (unrooted N₂ hN₂ hX) w C₂ ∧
      IsLeafNode (treeOfCycles (tildeNetwork (unrooted N₂ hN₂ hX))).graph w ∧
      ∃ u₂ ∈ cycleNodes (unrooted N₂ hN₂ hX).graph C₂,
        (∀ u' ∈ cycleNodes (unrooted N₂ hN₂ hX).graph C₂, u' ≠ u₂ →
          IsFourNetworkBlock (unrooted N₂ hN₂ hX) C₂ u') ∧
        ∀ x, x ∈ nodeBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ u₁ ↔
          x ∈ nodeBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ u₂ := by
  obtain ⟨s, hs⟩ := nodeBlock_nonempty_unrooted h1₁ hC₁.1 hu₁
  have hus : u₁ = blockNode (unrooted N₁ hN₁ hX) C₁ s := eq_blockNode h1₁ hC₁.1 hu₁ hs
  -- the blocks of `C₂` other than that of `s` are 4-network blocks
  have hblock₂ : ∀ u' ∈ cycleNodes (unrooted N₂ hN₂ hX).graph C₂,
      u' ≠ blockNode (unrooted N₂ hN₂ hX) C₂ s → IsFourNetworkBlock (unrooted N₂ hN₂ hX) C₂ u' := by
    intro u' hu' hne
    obtain ⟨t, rfl⟩ := exists_blockNode_eq h1₂ hC₂.1 hu'
    refine (isFourNetworkBlock_blockNode_iff h1₁ h1₂ hF hC₁.1 hC₂.1 hsame t).1
      (hblock₁ _ (blockNode_mem hC₁.1 t) fun h => hne ?_)
    rw [← sameBlock_iff_blockNode_eq h1₂ hC₂.1, ← hsame, sameBlock_iff_blockNode_eq h1₁ hC₁.1, h,
      hus]
  -- the node of the tree of cycles of `Ñ₂` arising from `C₂` is a leaf
  obtain ⟨w, hw⟩ := exists_arisesFrom_unrooted hN₂ h1₂ hX hC₂
  have hleaf : IsLeafNode (treeOfCycles (tildeNetwork (unrooted N₂ hN₂ hX))).graph w :=
    (isLeafNode_iff_fourNetworkBlocks_unrooted hN₂ h1₂ hX hC₂ hw).2
      ⟨_, blockNode_mem hC₂.1 s, hblock₂⟩
  -- the node of `C₂` that the leaf gives has the block of `s`, which is not a 4-network block
  obtain ⟨u₂, hu₂, hblock₂'⟩ := fourNetworkBlocks_of_isLeafNode_unrooted hN₂ h1₂ hX hC₂ hw hleaf
  obtain rfl : u₂ = blockNode (unrooted N₂ hN₂ hX) C₂ s := by
    by_contra hne
    refine hnot₁ ?_
    rw [hus]
    exact (isFourNetworkBlock_blockNode_iff h1₁ h1₂ hF hC₁.1 hC₂.1 hsame s).2
      (hblock₂' _ (blockNode_mem hC₂.1 s) (Ne.symm hne))
  refine ⟨w, hw, hleaf, _, hu₂, hblock₂', fun x => ?_⟩
  rw [hus, mem_nodeBlock_blockNode_iff h1₁ hC₁.1, mem_nodeBlock_blockNode_iff h1₂ hC₂.1, hsame]

/-- **The induction step of Theorem 4** (TeX l.1186): for `m ≥ 2` cycles of size at least four, a leaf
of the tree of cycles of `Ñ₁` arises from a cycle `C₁` all of whose blocks but that of a node `u₁`,
`P`, are 4-network blocks, and every other cycle of size at least four has the taxa outside `P` in
one of its blocks (`exists_leaf_bigCycle`). The cycle data give the cycle `C₂` of `N₂⁻` with the
same blocks; with the same 4-network blocks (Lemma 14), the node of the tree of cycles of `Ñ₂`
arising from `C₂` is a leaf, and its node `u₂` whose block is not a 4-network block has the block `P`
(`exists_isLeafNode_counterpart`). Both networks split at these nodes into the networks `Ñ` of the
networks induced on `Pᶜ ∪ {s₂}` and on `P ∪ {s₁}` (`s₂ ∈ P`, `s₁ ∉ P`). The first has at most one
cycle of size at least four, the second fewer than `m`, since `C₁` meets its taxa in two blocks; the
induction hypothesis applies to both. -/
theorem tildeDeterminedData_of_lt {m : ℕ} (hm : 2 ≤ m) (ih : ∀ k < m, TildeDeterminedData k) :
    TildeDeterminedData m := by
  intro X _ _ hX V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord hD hD' hF hc
  -- a leaf of the tree of cycles of `Ñ₁`: the cycle `C₁` and its node `u₁`
  obtain ⟨C₁, u₁, hC₁, hu₁, hblock₁, hnot₁, hleaf⟩ := exists_leaf_bigCycle hN₁ h1₁ hX (hc ▸ hm)
  -- the cycle `C₂` of `N₂⁻` with the same blocks, a leaf of the tree of cycles of `Ñ₂`, and its node
  -- `u₂` with the block of `u₁`
  obtain ⟨v₁, hv₁⟩ := exists_isHybridNodeOf h1₁ hC₁.1
  obtain ⟨C₂, v₂, hC₂, -, -, hsame, -, -⟩ := hD C₁ hC₁ v₁ hv₁
  obtain ⟨-, -, -, u₂, hu₂, -, hu₁₂⟩ :=
    exists_isLeafNode_counterpart hN₁ hN₂ h1₁ h1₂ hX hF hC₁ hu₁ hblock₁ hnot₁ hC₂ hsame
  -- the block `P` of `u₁`, a taxon `s₂` of it, and a taxon `s₁` of the block of another node
  set P := univ.filter fun z =>
    z ∈ nodeBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ u₁
  have hP₁ : ∀ z, z ∈ P ↔
      z ∈ nodeBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ u₁ :=
    fun z => by simp [P]
  have hP₂ : ∀ z, z ∈ P ↔
      z ∈ nodeBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ u₂ :=
    fun z => (hP₁ z).trans (hu₁₂ z)
  obtain ⟨s₂, hs₂⟩ := nodeBlock_nonempty_unrooted h1₁ hC₁.1 hu₁
  obtain ⟨u', hu', hu'u⟩ := hC₁.1.exists_mem_cycleNodes_notMem (Set.finite_singleton u₁)
    (by rw [Set.ncard_singleton]; have := hC₁.2; omega)
  obtain ⟨s₁, hs₁⟩ := nodeBlock_nonempty_unrooted h1₁ hC₁.1 hu'
  have hs₁P : s₁ ∉ P := fun h =>
    hu'u ((eq_blockNode h1₁ hC₁.1 hu' hs₁).trans (eq_blockNode h1₁ hC₁.1 hu₁ ((hP₁ s₁).1 h)).symm)
  refine tilde_sdIso_of_leafCycle hN₁ hN₂ h1₁ h1₂ hX hC₁ hu₁ hC₂.1 hu₂ hP₁ hP₂ hs₁P
    ((hP₁ s₂).2 hs₂) ?_ ?_ ?_
  · intro C' hC' hC'C₁ x y hx hy
    exact hleaf C' hC' hC'C₁ x y (fun h => hx ((hP₁ x).2 h)) (fun h => hy ((hP₁ y).2 h))
  · intro hY hY1
    exact nonempty_sdIso_tilde_inducedLSA (ih _ (by omega)) hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord
      hD hD' hY rfl
  · intro hY hY1
    exact nonempty_sdIso_tilde_inducedLSA (ih _ (by omega)) hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord
      hD hD' hY rfl

/-- **The claim of the induction of Theorem 4 holds for every number of cycles of size at least
four.** -/
theorem tildeDeterminedData (m : ℕ) : TildeDeterminedData m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · exact tildeDeterminedData_zero
    · exact tildeDeterminedData_one
    · exact tildeDeterminedData_of_lt (by omega) ih

end Banos2019
