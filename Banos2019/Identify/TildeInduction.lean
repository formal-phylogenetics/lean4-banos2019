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
with the same cycle data (`SameCycleData`, which Lemmas 15 and 16 give for the networks of Theorem 4).
It holds for every `m` (`tildeDeterminedData`), by strong induction on `m`:

* `tildeDeterminedData_zero`: no cycle of size at least four (`tildeDetermined_zero`,
  `Identify/TildeBase.lean`).
* `tildeDeterminedData_one`: one cycle `C₁` of size at least four, by strong induction on the number of
  taxa. The cycle `C₂` of `N₂⁻` with the same blocks, adjacent blocks and hybrid block gives the
  isomorphism when the blocks are single taxa (`tilde_sdIso_of_singletonBlocks`). Otherwise a block `P`
  with at least two taxa splits `Ñ` into the networks `Ñ` of the networks induced on `Pᶜ ∪ {s₂}`, which
  has fewer taxa, and on `P ∪ {s₁}`, which has no cycle of size at least four.
* `tildeDeterminedData_of_lt`: for `m ≥ 2` cycles, a cycle `C₁` and a node `u` of it with the property
  of a leaf of the tree of cycles (`exists_leaf_bigCycle`) split `Ñ` at the block of `u` into two
  networks with fewer cycles of size at least four.

Both steps glue the two pieces (`tilde_sdIso_of_leafCycle`): `Ñ` of `N₁` and of `N₂` are the gluings of
the networks `Ñ` of the pieces (`tilde_sdIso_glue`), and isomorphic pieces glue to isomorphic networks
(`glue_congr`). The pieces satisfy the conditions of Theorem 4 (`Identify/InducedCycles.lean`) and have
the same cycle data (`SameCycleData.inducedLSA`).

* `bigCycleCount_inducedLSA_insert_compl_le_one`, `bigCycleCount_inducedLSA_insert_lt`: the numbers of
  cycles of size at least four of the two pieces.
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
concordance factors and the same cycle data, the first with `m` cycles of size at least four in `N⁻`,
have isomorphic networks `Ñ`. -/
def TildeDeterminedData (m : ℕ) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (hX : Nontrivial X) (V₁ E₁ V₂ E₂ : Type) [Fintype V₁]
    [Fintype E₁] [Fintype V₂] [Fintype E₂] (N₁ : RootedNetwork V₁ E₁ X) (N₂ : RootedNetwork V₂ E₂ X)
    (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂),
    IsLevelOne N₁.graph → IsLevelOne N₂.graph → ∀ θ₁ θ₂, IsMetricNetwork N₁ θ₁ →
    IsMetricNetwork N₂ θ₂ → GoodParams hX N₁ θ₁ → GoodParams hX N₂ θ₂ →
    SameOrdering (cf N₁ θ₁) (cf N₂ θ₂) → SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX) →
    bigCycleCount (unrooted N₁ hN₁ hX) = m →
    Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX)))

/-- **No cycle of size at least four**: the base case `tildeDetermined_zero`, which does not use the
cycle data. -/
theorem tildeDeterminedData_zero : TildeDeterminedData 0 :=
  fun X _ _ hX V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord _ hc =>
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
induced on `Y` with `k` cycles of size at least four. -/
theorem nonempty_sdIso_tilde_inducedLSA {k : ℕ} (hk : TildeDeterminedData k) {V' E' : Type}
    [Fintype V'] [Fintype E'] {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X}
    (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph)
    (h1₂ : IsLevelOne N₂.graph) (hX : Nontrivial X) {θ₁ : MetricData E} {θ₂ : MetricData E'}
    (hθ₁ : IsMetricNetwork N₁ θ₁) (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁)
    (hG₂ : GoodParams hX N₂ θ₂) (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂))
    (hD : SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX)) {Y : Set X} (hY : Y.Nontrivial)
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
    (hD.inducedLSA hN₁ hN₂ h1₁ h1₂ hX hY) hcount

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

/-- **The step of the induction of Theorem 4**: let `C₁` be a cycle of size at least four of `N₁⁻`, `P`
the block of `C₁` of the taxon `s₂`, and `s₁` a taxon outside `P`, such that every other cycle of size
at least four of `N₁⁻` has the taxa outside `P` in one of its blocks. If the networks induced on
`Pᶜ ∪ {s₂}` (at most one cycle of size at least four) and on `P ∪ {s₁}` (fewer cycles of size at least
four than `N₁⁻`) have isomorphic networks `Ñ`, so have `N₁` and `N₂`.

The cycle `C₂` of `N₂⁻` with the same blocks as `C₁` (the same cycle data) has a node with the block
`P`, and `Ñ` of each network is the gluing of the networks `Ñ` of its pieces
(`tilde_sdIso_of_pieces`). -/
theorem tilde_sdIso_of_leafCycle {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hX : Nontrivial X) (hD : SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX)) {C₁ : Set _}
    (hC₁ : C₁ ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4) {P : Finset X} {s₁ s₂ : X}
    (hP : ∀ x, x ∈ P ↔ SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ s₂ x)
    (hs₁ : s₁ ∉ P)
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
  obtain ⟨v₁, hv₁⟩ := exists_isHybridNodeOf h1₁ hC₁.1
  obtain ⟨C₂, v₂, hC₂, -, -, hsame, -, -⟩ := hD C₁ hC₁ v₁ hv₁
  have hs₂ : s₂ ∈ P := (hP s₂).2 .refl
  have hP₁ : ∀ x, x ∈ P ↔ x ∈ nodeBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁
      (blockNode (unrooted N₁ hN₁ hX) C₁ s₂) := fun x =>
    (hP x).trans (mem_nodeBlock_blockNode_iff h1₁ hC₁.1 s₂ x).symm
  have hP₂ : ∀ x, x ∈ P ↔ x ∈ nodeBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂
      (blockNode (unrooted N₂ hN₂ hX) C₂ s₂) := fun x =>
    ((hP x).trans (hsame s₂ x)).trans (mem_nodeBlock_blockNode_iff h1₂ hC₂.1 s₂ x).symm
  have hne : s₁ ≠ s₂ := fun h => hs₁ (h ▸ hs₂)
  have hZ₁ : ((insert s₂ Pᶜ : Finset X) : Set X).Nontrivial :=
    ⟨s₂, by simp, s₁, by simp [hs₁], hne.symm⟩
  have hZ₂ : ((insert s₁ P : Finset X) : Set X).Nontrivial := ⟨s₁, by simp, s₂, by simp [hs₂], hne⟩
  have hPP : ∀ x ∈ P, ∀ y ∈ P,
      SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y := fun x hx y hy =>
    (DirectedMultigraph.walks_symm _ ((hP x).1 hx)).trans ((hP y).1 hy)
  exact tilde_sdIso_of_pieces hN₁ hN₂ h1₁ h1₂ hX hC₁.1 (blockNode_mem hC₁.1 s₂) hC₂.1
    (blockNode_mem hC₂.1 s₂) hP₁ hP₂ hs₁ hs₂ hZ₁ hZ₂
    (H₁ hZ₁ (bigCycleCount_inducedLSA_insert_compl_le_one hN₁ h1₁ hX hleaf s₂ hZ₁))
    (H₂ hZ₂ (bigCycleCount_inducedLSA_insert_lt hN₁ h1₁ hX hC₁ hPP s₁ hZ₂))

/-- **One cycle of size at least four** (proof of Theorem 4, the case of one cycle). The cycle data
give a cycle `C₂` of `N₂⁻` with the same blocks, adjacent blocks and hybrid block as the cycle `C₁` of
`N₁⁻`. When the blocks are single taxa, `Ñ₁` and `Ñ₂` are this cycle with a taxon at each node
(`tilde_sdIso_of_singletonBlocks`). Otherwise, for a block `P` with at least two taxa, a taxon
`s₂ ∈ P` and a taxon `s₁ ∉ P`, the networks `Ñ` are the gluings of those of the networks induced on
`Pᶜ ∪ {s₂}`, which has fewer taxa and at most one cycle of size at least four (induction on the
number of taxa, or `tildeDeterminedData_zero`), and on `P ∪ {s₁}`, which has none
(`tildeDeterminedData_zero`). This is the paper's step of joining the tree of each block, read with
an outgroup, to its node of the cycle. -/
theorem tildeDeterminedData_one : TildeDeterminedData 1 := by
  intro X _ _
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card X = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ihn =>
  intro hX V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord hD hc
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
  -- the block `P` of `x`, which contains `y`, and a taxon `s₁` of another block
  set P := univ.filter fun z => SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x z
  have hP : ∀ z, z ∈ P ↔ SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x z :=
    fun z => by simp [P]
  obtain ⟨u', hu', hu'x⟩ := hC₁.1.exists_mem_cycleNodes_notMem
    (Set.finite_singleton (blockNode (unrooted N₁ hN₁ hX) C₁ x))
    (by rw [Set.ncard_singleton]; have := hC₁.2; omega)
  obtain ⟨s₁, hs₁⟩ := exists_blockNode_eq h1₁ hC₁.1 hu'
  have hs₁P : s₁ ∉ P := by
    rw [hP, sameBlock_iff_blockNode_eq h1₁ hC₁.1, hs₁]
    exact fun h => hu'x h.symm
  refine tilde_sdIso_of_leafCycle hN₁ hN₂ h1₁ h1₂ hX hD hC₁ hP hs₁P ?_ ?_ ?_
  · -- `C₁` is the only cycle of size at least four
    intro C' hC' hC'C₁
    rw [hbig] at hC'
    exact absurd hC' hC'C₁
  · -- the piece on `Pᶜ ∪ {x}`: fewer taxa, at most one cycle of size at least four
    intro hY hY1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hY1 with h0 | h1
    · exact nonempty_sdIso_tilde_inducedLSA tildeDeterminedData_zero hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁
        hG₂ hord hD hY h0
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
        (hD.inducedLSA hN₁ hN₂ h1₁ h1₂ hX hY) h1
      rw [← hn]
      exact Fintype.card_subtype_lt hyY
  · -- the piece on `P ∪ {s₁}`: no cycle of size at least four
    intro hY hY1
    exact nonempty_sdIso_tilde_inducedLSA tildeDeterminedData_zero hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁
      hG₂ hord hD hY (by omega)

/-- **The induction step of Theorem 4**: for `m ≥ 2` cycles of size at least four, a cycle `C₁` and a
node `u` of it, with block `P`, such that every other cycle of size at least four has the taxa outside
`P` in one of its blocks (`exists_leaf_bigCycle`: the paper's leaf of the tree of cycles), split `Ñ`
into the networks `Ñ` of the networks induced on `Pᶜ ∪ {s₂}` and on `P ∪ {s₁}` (`s₂ ∈ P`, `s₁ ∉ P`).
The first has at most one cycle of size at least four, the second fewer than `m`, since `C₁` meets
its taxa in two blocks; the induction hypothesis applies to both. -/
theorem tildeDeterminedData_of_lt {m : ℕ} (hm : 2 ≤ m) (ih : ∀ k < m, TildeDeterminedData k) :
    TildeDeterminedData m := by
  intro X _ _ hX V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord hD hc
  obtain ⟨C₁, u, hC₁, hu, hleaf⟩ := exists_leaf_bigCycle hN₁ h1₁ hX (hc ▸ hm)
  -- a taxon `s₂` of the block of `u`, and a taxon `s₁` of the block of another node
  obtain ⟨s₂, hs₂⟩ := nodeBlock_nonempty_unrooted h1₁ hC₁.1 hu
  have hus₂ : u = blockNode (unrooted N₁ hN₁ hX) C₁ s₂ := eq_blockNode h1₁ hC₁.1 hu hs₂
  obtain ⟨u', hu', hu'u⟩ := hC₁.1.exists_mem_cycleNodes_notMem (Set.finite_singleton u)
    (by rw [Set.ncard_singleton]; have := hC₁.2; omega)
  obtain ⟨s₁, hs₁⟩ := exists_blockNode_eq h1₁ hC₁.1 hu'
  have hu₀ : ∀ z, z ∈ nodeBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ u ↔
      SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ s₂ z := fun z => by
    rw [hus₂]
    exact mem_nodeBlock_blockNode_iff h1₁ hC₁.1 s₂ z
  set P := univ.filter fun z => SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ s₂ z
  have hP : ∀ z, z ∈ P ↔ SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ s₂ z :=
    fun z => by simp [P]
  have hs₁P : s₁ ∉ P := by
    rw [hP, sameBlock_iff_blockNode_eq h1₁ hC₁.1, hs₁, ← hus₂]
    exact fun h => hu'u h.symm
  refine tilde_sdIso_of_leafCycle hN₁ hN₂ h1₁ h1₂ hX hD hC₁ hP hs₁P ?_ ?_ ?_
  · intro C' hC' hC'C₁ x y hx hy
    exact hleaf C' hC' hC'C₁ x y (by rwa [hu₀, ← hP]) (by rwa [hu₀, ← hP])
  · intro hY hY1
    exact nonempty_sdIso_tilde_inducedLSA (ih _ (by omega)) hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord
      hD hY rfl
  · intro hY hY1
    exact nonempty_sdIso_tilde_inducedLSA (ih _ (by omega)) hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord
      hD hY rfl

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
