module

public import Banos2019.Identify.TildeBase
public import Banos2019.Identify.NonDegenerate
public import Banos2019.Identify.Glue
public import Banos2019.Identify.InducedCycles
public import Banos2019.Identify.TildeCycle
public import Banos2019.Identify.SameData

/-!
# The induction of Theorem 4 (Baños 2019, Section 8)

The claim of the induction is Theorem 4 for `m` cycles of size at least four (`TildeDetermined m`,
`Identify/TildeDefs.lean`): two networks with parameters satisfying `GoodParams` and the same orderings
of concordance factors, the first with `m` cycles of size at least four in `N⁻`, have isomorphic
networks `Ñ`. Each case of the proof (`tilde_sdIso_of_data`) uses the data that the orderings give for
the two networks: for each cycle of size at least four of `N₁⁻`, a cycle of `N₂⁻` with the same
blocks, adjacent blocks and hybrid block (`SameCycleData`), and the same 4-network blocks
(`SameFourNetworkBlocks`). It applies the claim to networks induced on sets of taxa, whose data are
read from their own orderings (`sameCycleData_of_sameOrdering`,
`sameFourNetworkBlocks_of_sameOrdering`: Lemmas 14, 15 and 16 at their parameters). The claim holds
for every `m` (`tildeDetermined`), by strong induction on `m`.

* No cycle of size at least four: `tildeDetermined_zero` (`Identify/TildeBase.lean`).
* One cycle `C` of size at least four: `tilde_sdIso_one_of_sameCycleData`, `tildeDeterminedOneCycle`.
  The tree of each block `P` of `C` with at least two taxa is joined to the node of `P`: `Ñ` is the
  gluing of the network `Ñ` of the network induced on `P ∪ {q}` (a tree; `q ∉ P`), at its leaf `q`,
  to the network `Ñ` of the network induced on `Pᶜ ∪ {x}` (`x ∈ P`), at its leaf `x`. The blocks are
  taken one at a time, by induction on the number of blocks with at least two taxa
  (`nontrivialBlocks`), of which the network induced on `Pᶜ ∪ {x}` has fewer
  (`ncard_nontrivialBlocks_inducedLSA_lt`). With none left, `Ñ` is the cycle with one taxon at each
  node, given by the data (`tilde_sdIso_of_singletonBlocks`).
* More cycles: `tilde_sdIso_of_lt_of_data`. A leaf of the tree of cycles of `Ñ₁` arises from a cycle
  `C₁` all of whose blocks but that of a node `u₁` are 4-network blocks (`exists_leaf_bigCycle`). The
  cycle `C₂` of `N₂⁻` with the same blocks gives a leaf of the tree of cycles of `Ñ₂`, and its node
  `u₂` with the block of `u₁` (`exists_isLeafNode_counterpart`, from the same 4-network blocks). The
  two networks split at `u₁` and `u₂` into networks with fewer cycles of size at least four
  (`tilde_sdIso_of_leafCycle`).

In both cases `Ñ` of `N₁` and of `N₂` are the gluings of the networks `Ñ` of the pieces
(`tilde_sdIso_glue`), and isomorphic pieces glue to isomorphic networks (`glue_congr`,
`tilde_sdIso_of_pieces`). The pieces satisfy the conditions of Theorem 4 (`goodParams_inducedLSA`,
`sameOrdering_inducedLSA`, `Identify/InducedCycles.lean`).

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

omit [Fintype V] in
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

omit [Fintype X] [Fintype V] in
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

/-- **The claim for a piece**: `TildeDetermined k` gives isomorphic networks `Ñ` for the networks
induced on `Y` with `k` cycles of size at least four, which satisfy the conditions of Theorem 4. -/
theorem nonempty_sdIso_tilde_inducedLSA {k : ℕ} (hk : TildeDetermined k) {V' E' : Type}
    [Fintype V'] [Fintype E'] {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X}
    (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph)
    (h1₂ : IsLevelOne N₂.graph) (hX : Nontrivial X) {θ₁ : MetricData E} {θ₂ : MetricData E'}
    (hθ₁ : IsMetricNetwork N₁ θ₁) (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁)
    (hG₂ : GoodParams hX N₂ θ₂) (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂)) {Y : Set X}
    (hY : Y.Nontrivial)
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
    (sameOrdering_inducedLSA hN₁ hN₂ hθ₁ hθ₂ hord hY) hcount

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

/-! ### One cycle of size at least four -/

/-- **Classes of an equivalence relation on a subset**: when `Y` holds one element `x` of a class with
at least two elements and all the elements of the other classes, the classes of the relation on `Y`
with at least two elements are the other classes of `R` with at least two elements, so there are
fewer of them than there are of `R`. -/
theorem ncard_nontrivialClasses_subtype_lt {α : Type*} [Finite α] (R : α → α → Prop)
    (hrefl : ∀ a, R a a) (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    {Y : Set α} {x : α} (hY : ∀ z, z ∈ Y ↔ z = x ∨ ¬ R x z) (hP : {y | R x y}.Nontrivial) :
    {B : Set Y | (∃ a : Y, B = {b : Y | R a b}) ∧ B.Nontrivial}.ncard <
      {B : Set α | (∃ a, B = {b | R a b}) ∧ B.Nontrivial}.ncard := by
  have hmaps : ∀ B ∈ {B : Set Y | (∃ a : Y, B = {b : Y | R a b}) ∧ B.Nontrivial},
      Subtype.val '' B ∈ {B : Set α | (∃ a, B = {b | R a b}) ∧ B.Nontrivial} \ {{y | R x y}} := by
    rintro B ⟨⟨a, rfl⟩, hB⟩
    -- `a` is not in the class of `x`, which meets `Y` in `x` only
    have hxa : ¬ R x a := by
      intro hxa
      obtain ⟨b₁, hb₁, b₂, hb₂, hne⟩ := hB
      have e : ∀ b : Y, R a b → (b : α) = x := fun b hb =>
        ((hY b).1 b.2).resolve_right (not_not.2 (htrans _ _ _ hxa hb))
      exact hne (Subtype.ext ((e b₁ hb₁).trans (e b₂ hb₂).symm))
    -- so the class of `a` lies in `Y`
    have himg : Subtype.val '' {b : Y | R a b} = {b | R a b} := by
      ext z
      refine ⟨?_, fun hz => ⟨⟨z, (hY z).2 (Or.inr fun hxz =>
        hxa (htrans _ _ _ hxz (hsymm _ _ hz)))⟩, hz, rfl⟩⟩
      rintro ⟨b, hb, rfl⟩
      exact hb
    refine ⟨⟨⟨a, himg⟩, hB.image Subtype.val_injective⟩, fun h => hxa ?_⟩
    have hx : x ∈ ({y | R a y} : Set α) := by
      rw [← himg, Set.mem_singleton_iff.1 h]
      exact hrefl x
    exact hsymm _ _ hx
  calc _ = (Set.image (Set.image Subtype.val)
        {B : Set Y | (∃ a : Y, B = {b : Y | R a b}) ∧ B.Nontrivial}).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective.image_injective).symm
    _ ≤ ({B : Set α | (∃ a, B = {b | R a b}) ∧ B.Nontrivial} \ {{y | R x y}}).ncard :=
        Set.ncard_le_ncard (by rintro _ ⟨B, hB, rfl⟩; exact hmaps B hB)
    _ < _ := Set.ncard_sdiff_singleton_lt_of_mem
        (show {y | R x y} ∈ {B : Set α | (∃ a, B = {b | R a b}) ∧ B.Nontrivial} from ⟨⟨x, rfl⟩, hP⟩)

/-- The blocks of the cycle `C` with at least two taxa. -/
def nontrivialBlocks {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') :
    Set (Set X') :=
  {B | (∃ x, B = {y | SameBlock G.graph G.leaf C x y}) ∧ B.Nontrivial}

omit [Fintype V] in
/-- **The network induced on `Pᶜ ∪ {x}` has fewer blocks with at least two taxa**: let `C` be the
only cycle of size at least four of `N⁻`, `P` the block of `x`, with at least two taxa, and
`Y = Pᶜ ∪ {x}`. A cycle `C'` of size at least four of `(N⊕_Y)⁻` comes from a cycle of `N⁻` with the
same hybrid node (`exists_unrooted_cycle_of_induced`), which separates the same four taxa
(`separatesQuartet_induced_iff`), so has size at least four and is `C`. The blocks of `C'` are the
traces on `Y` of those of `C` (`blockNode_eq_iff_induced`): those of `C` other than `P`, and `{x}`. -/
theorem ncard_nontrivialBlocks_inducedLSA_lt {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _}
    (honly : ∀ C' ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4, C' = C) {x : X}
    (hP : {y | SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y}.Nontrivial)
    {Y : Set X}
    (hYx : ∀ z, z ∈ Y ↔ z = x ∨ ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x z)
    (hY : Y.Nontrivial) {C' : Set _}
    (hC' : C' ∈ cyclesOfSizeAtLeast (unrooted (inducedLSA N hN.1 Y hY)
      (inducedLSA_isBinaryRootedNetwork hN hY) hY.coe_sort).graph 4) :
    (nontrivialBlocks (unrooted (inducedLSA N hN.1 Y hY) (inducedLSA_isBinaryRootedNetwork hN hY)
      hY.coe_sort) C').ncard < (nontrivialBlocks (unrooted N hN hX) C).ncard := by
  have h1Y := inducedLSA_isLevelOne hN h1 hY
  obtain ⟨w, hw⟩ := exists_isHybridNodeOf h1Y hC'.1
  obtain ⟨C₀, v, hC₀, hv, hwv⟩ := exists_unrooted_cycle_of_induced hN h1 hX hY hw
  -- `C'` comes from `C`
  obtain ⟨s, hs4, hsep⟩ := exists_separatesQuartet_of_four_le h1Y hC'.1 hC'.2 hw
  have hsep' := (separatesQuartet_induced_iff hN h1 hX hY hC'.1 hw hC₀ hv hwv s).1 hsep
  obtain rfl : C₀ = C := honly C₀
    ⟨hC₀, four_le_ncard_of_separatesQuartet h1 hC₀ hv (by rw [card_map, hs4]) hsep'⟩
  -- its blocks are the traces on `Y` of those of `C`
  have hiff : ∀ a b : Y,
      SameBlock (unrooted (inducedLSA N hN.1 Y hY) (inducedLSA_isBinaryRootedNetwork hN hY)
          hY.coe_sort).graph
        (unrooted (inducedLSA N hN.1 Y hY) (inducedLSA_isBinaryRootedNetwork hN hY)
          hY.coe_sort).leaf C' a b ↔
      SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C₀ a b := fun a b =>
    (sameBlock_iff_blockNode_eq h1Y hC'.1 a b).trans
      ((blockNode_eq_iff_induced hN h1 hX hY hC'.1 hw hC₀ hv hwv a.2 b.2).symm.trans
        (sameBlock_iff_blockNode_eq h1 hC₀ a b).symm)
  have heq : nontrivialBlocks (unrooted (inducedLSA N hN.1 Y hY)
      (inducedLSA_isBinaryRootedNetwork hN hY) hY.coe_sort) C' =
      {B : Set Y | (∃ a : Y, B = {b : Y | SameBlock (unrooted N hN hX).graph
        (unrooted N hN hX).leaf C₀ a b}) ∧ B.Nontrivial} := by
    simp only [nontrivialBlocks, hiff]
  rw [heq]
  exact ncard_nontrivialClasses_subtype_lt
    (fun a b => SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C₀ a b) (fun _ => .refl)
    (fun _ _ h => DirectedMultigraph.walks_symm _ h) (fun _ _ _ h h' => h.trans h') hYx hP

/-- **The claim of the case of one cycle**, for `j` blocks with at least two taxa: two binary level-1
networks on the same taxa, with parameters satisfying `GoodParams` and the same orderings of
concordance factors, the first with one cycle of size at least four in `N⁻`, which has `j` blocks
with at least two taxa, have isomorphic networks `Ñ`. -/
def TildeDeterminedOneCycle (j : ℕ) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (hX : Nontrivial X) (V₁ E₁ V₂ E₂ : Type) [Fintype V₁]
    [Fintype E₁] [Fintype V₂] [Fintype E₂] (N₁ : RootedNetwork V₁ E₁ X) (N₂ : RootedNetwork V₂ E₂ X)
    (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂),
    IsLevelOne N₁.graph → IsLevelOne N₂.graph → ∀ θ₁ θ₂, IsMetricNetwork N₁ θ₁ →
    IsMetricNetwork N₂ θ₂ → GoodParams hX N₁ θ₁ → GoodParams hX N₂ θ₂ →
    SameOrdering (cf N₁ θ₁) (cf N₂ θ₂) → bigCycleCount (unrooted N₁ hN₁ hX) = 1 →
    ∀ C ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4,
      (nontrivialBlocks (unrooted N₁ hN₁ hX) C).ncard = j →
      Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX)))

/-- **One cycle of size at least four** (proof of Theorem 4, TeX l. 1182–1184): let `C₁` be the only
cycle of size at least four of `N₁⁻`, with `j` blocks of at least two taxa, and `C₂` the cycle of
`N₂⁻` with the same blocks, adjacent blocks and, for size at least five, hybrid block, which the data
give (Lemmas 15 and 16). When the blocks are single taxa, `Ñ₁` and `Ñ₂` are this cycle with a taxon at
each node (`tilde_sdIso_of_singletonBlocks`). Otherwise let `P` be a block with at least two taxa, the
block of the node `u` of `C₁`, with `x ∈ P`, and `q ∉ P`. The network induced on `P ∪ {q}` has no
cycle of size at least four, so its networks `Ñ` for `N₁` and `N₂` are isomorphic
(`tildeDetermined_zero`): this is the tree of `P` with the outgroup `q`. A cycle of size at least
four of the network induced on `Pᶜ ∪ {x}` is `C₁` with `P` replaced by `x`, with fewer blocks of at
least two taxa (`ncard_nontrivialBlocks_inducedLSA_lt`), so the claim for fewer blocks applies to that
network (`tildeDetermined_zero` without such a cycle). `Ñ` is the gluing of the first network `Ñ`, at
its leaf `q`, to the second, at its leaf `x`, which joins the root of the tree of `P` to `u` by an
edge (`tilde_sdIso_glue`, `glue_congr`). -/
theorem tilde_sdIso_one_of_sameCycleData {j : ℕ} (ih : ∀ i < j, TildeDeterminedOneCycle i)
    {V' E' : Type} [Fintype V'] [Fintype E'] {N₁ : RootedNetwork V E X}
    {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂)
    (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph) (hX : Nontrivial X)
    {θ₁ : MetricData E} {θ₂ : MetricData E'} (hθ₁ : IsMetricNetwork N₁ θ₁)
    (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁) (hG₂ : GoodParams hX N₂ θ₂)
    (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂))
    (hD : SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX))
    (hc : bigCycleCount (unrooted N₁ hN₁ hX) = 1) {C₁ : Set _}
    (hC₁ : C₁ ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4)
    (hj : (nontrivialBlocks (unrooted N₁ hN₁ hX) C₁).ncard = j) :
    Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX))) := by
  -- `C₁` is the only cycle of size at least four
  have honly : ∀ C ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4, C = C₁ := by
    obtain ⟨C₀, hC₀⟩ := Set.ncard_eq_one.1 hc
    intro C hC
    rw [hC₀] at hC
    have h := hC₁
    rw [hC₀] at h
    exact (Set.mem_singleton_iff.1 hC).trans (Set.mem_singleton_iff.1 h).symm
  -- the cycle `C₂` of `N₂⁻` with the same blocks, adjacent blocks and hybrid block
  obtain ⟨v₁, hv₁⟩ := exists_isHybridNodeOf h1₁ hC₁.1
  obtain ⟨C₂, v₂, hC₂, hv₂, -, hsame, hadj, hhyb⟩ := hD C₁ hC₁ v₁ hv₁
  by_cases hsing : ∀ x y, SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y →
      x = y
  · -- the blocks are single taxa: `Ñ` is the cycle with a taxon at each node
    exact tilde_sdIso_of_singletonBlocks hN₁ hN₂ h1₁ h1₂ hX hC₁ hC₂ hv₁ hv₂ hsing
      (fun x y h => hsing x y ((hsame x y).2 h)) hadj hhyb
  push Not at hsing
  obtain ⟨x, y, hxy, hne⟩ := hsing
  -- the block `P` of `x`, which contains `y`, the nodes of `C₁` and `C₂` with this block, and a
  -- taxon `q` of another block
  set P := univ.filter fun z => SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x z
  have hP : ∀ z, z ∈ P ↔ SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x z :=
    fun z => by simp [P]
  have hP₁ : ∀ z, z ∈ P ↔ z ∈ nodeBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁
      (blockNode (unrooted N₁ hN₁ hX) C₁ x) := fun z =>
    (hP z).trans (mem_nodeBlock_blockNode_iff h1₁ hC₁.1 x z).symm
  have hP₂ : ∀ z, z ∈ P ↔ z ∈ nodeBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂
      (blockNode (unrooted N₂ hN₂ hX) C₂ x) := fun z =>
    ((hP z).trans (hsame x z)).trans (mem_nodeBlock_blockNode_iff h1₂ hC₂.1 x z).symm
  have hPP : ∀ a ∈ P, ∀ b ∈ P,
      SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ a b := fun a ha b hb =>
    (DirectedMultigraph.walks_symm _ ((hP a).1 ha)).trans ((hP b).1 hb)
  obtain ⟨u', hu', hu'x⟩ := hC₁.1.exists_mem_cycleNodes_notMem
    (Set.finite_singleton (blockNode (unrooted N₁ hN₁ hX) C₁ x))
    (by rw [Set.ncard_singleton]; have := hC₁.2; omega)
  obtain ⟨q, hq⟩ := exists_blockNode_eq h1₁ hC₁.1 hu'
  have hqP : q ∉ P := by
    rw [hP, sameBlock_iff_blockNode_eq h1₁ hC₁.1, hq]
    exact fun h => hu'x h.symm
  have hxP : x ∈ P := (hP x).2 .refl
  have hZ₁ : ((insert x Pᶜ : Finset X) : Set X).Nontrivial :=
    ⟨x, by simp, q, by simp [hqP], fun h => hqP (h ▸ hxP)⟩
  have hZ₂ : ((insert q P : Finset X) : Set X).Nontrivial :=
    ⟨q, by simp, x, by simp [hxP], fun h => hqP (h ▸ hxP)⟩
  refine tilde_sdIso_of_pieces hN₁ hN₂ h1₁ h1₂ hX hC₁.1 (blockNode_mem hC₁.1 x) hC₂.1
    (blockNode_mem hC₂.1 x) hP₁ hP₂ hqP hxP hZ₁ hZ₂ ?_ ?_
  · -- the network induced on `Pᶜ ∪ {x}`: `C₁` with `P` replaced by `x`
    have hYx : ∀ z, z ∈ ((insert x Pᶜ : Finset X) : Set X) ↔
        z = x ∨ ¬ SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x z :=
      fun z => by simp [hP]
    have hPnt : {z | SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x z}.Nontrivial :=
      ⟨x, .refl, y, hxy, hne⟩
    have hle := bigCycleCount_inducedLSA_insert_compl_le_one hN₁ h1₁ hX (C := C₁) (P := P)
      (fun C' hC' hne' => absurd (honly C' hC') hne') x hZ₁
    generalize ((insert x Pᶜ : Finset X) : Set X) = Y at hZ₁ hYx hle ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
    · exact nonempty_sdIso_tilde_inducedLSA tildeDetermined_zero hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁
        hG₂ hord hZ₁ h0
    · obtain ⟨C', hC'⟩ := Set.ncard_eq_one.1 h1
      have hC'm : C' ∈ cyclesOfSizeAtLeast (unrooted (inducedLSA N₁ hN₁.1 Y hZ₁)
          (inducedLSA_isBinaryRootedNetwork hN₁ hZ₁) hZ₁.coe_sort).graph 4 := by
        rw [hC']
        rfl
      exact ih _ (hj ▸ ncard_nontrivialBlocks_inducedLSA_lt hN₁ h1₁ hX honly hPnt hYx hZ₁ hC'm) Y
        hZ₁.coe_sort _ _ _ _ _ _ (inducedLSA_isBinaryRootedNetwork hN₁ hZ₁)
        (inducedLSA_isBinaryRootedNetwork hN₂ hZ₁) (inducedLSA_isLevelOne hN₁ h1₁ hZ₁)
        (inducedLSA_isLevelOne hN₂ h1₂ hZ₁) _ _ (inducedLSA_isMetricNetwork hN₁ hθ₁ hZ₁)
        (inducedLSA_isMetricNetwork hN₂ hθ₂ hZ₁) (goodParams_inducedLSA hN₁ h1₁ hX hθ₁ hG₁ hZ₁)
        (goodParams_inducedLSA hN₂ h1₂ hX hθ₂ hG₂ hZ₁)
        (sameOrdering_inducedLSA hN₁ hN₂ hθ₁ hθ₂ hord hZ₁) h1 C' hC'm rfl
  · -- the network induced on `P ∪ {q}`: no cycle of size at least four, the tree of `P` read with
    -- the outgroup `q`
    have hlt := bigCycleCount_inducedLSA_insert_lt hN₁ h1₁ hX hC₁ hPP q hZ₂
    exact nonempty_sdIso_tilde_inducedLSA tildeDetermined_zero hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂
      hord hZ₂ (by omega)

/-- **The case of one cycle holds for any number of blocks with at least two taxa**, by strong
induction on that number: the data of each pair of networks are read from their orderings
(`sameCycleData_of_sameOrdering`), and `tilde_sdIso_one_of_sameCycleData` applies. -/
theorem tildeDeterminedOneCycle (j : ℕ) : TildeDeterminedOneCycle j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro X _ _ hX V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord hc C₁ hC₁ hj
  exact tilde_sdIso_one_of_sameCycleData ih hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord
    (sameCycleData_of_sameOrdering hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord) hc hC₁ hj

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

/-- **More cycles** (proof of Theorem 4, TeX l. 1186–1190): for `m ≥ 2` cycles of size at least
four, a leaf of the tree of cycles of `Ñ₁` arises from a cycle `C₁` all of whose blocks but that of a
node `u₁`, `P`, are 4-network blocks, and every other cycle of size at least four has the taxa outside
`P` in one of its blocks (`exists_leaf_bigCycle`). The data give the cycle `C₂` of `N₂⁻` with the
same blocks (Lemma 15) and the same 4-network blocks (Lemma 14); so the node of the tree of cycles of
`Ñ₂` arising from `C₂` is a leaf, and its node `u₂` whose block is not a 4-network block has the
block `P` (`exists_isLeafNode_counterpart`). Both networks split at these nodes into the networks `Ñ`
of the networks induced on `Pᶜ ∪ {s₂}` and on `P ∪ {s₁}` (`s₂ ∈ P`, `s₁ ∉ P`). The first has at most
one cycle of size at least four, the second fewer than `m`, since `C₁` meets its taxa in two blocks;
the induction hypothesis applies to both. -/
theorem tilde_sdIso_of_lt_of_data {m : ℕ} (hm : 2 ≤ m) (ih : ∀ k < m, TildeDetermined k)
    {V' E' : Type} [Fintype V'] [Fintype E'] {N₁ : RootedNetwork V E X}
    {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂)
    (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph) (hX : Nontrivial X)
    {θ₁ : MetricData E} {θ₂ : MetricData E'} (hθ₁ : IsMetricNetwork N₁ θ₁)
    (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁) (hG₂ : GoodParams hX N₂ θ₂)
    (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂))
    (hD : SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX))
    (hF : SameFourNetworkBlocks (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX))
    (hc : bigCycleCount (unrooted N₁ hN₁ hX) = m) :
    Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX))) := by
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
      hY rfl
  · intro hY hY1
    exact nonempty_sdIso_tilde_inducedLSA (ih _ (by omega)) hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord
      hY rfl

/-- **The induction step of Theorem 4, for networks with their data**: two networks with parameters
satisfying `GoodParams`, the same orderings, a cycle of `N₂⁻` with the same blocks, adjacent blocks
and hybrid block for each cycle of size at least four of `N₁⁻`, and the same 4-network blocks, the
first with `m` cycles of size at least four, have isomorphic networks `Ñ` when the claim holds for
fewer cycles: without such a cycle by `tildeDetermined_zero`, with one by
`tilde_sdIso_one_of_sameCycleData`, with more by `tilde_sdIso_of_lt_of_data`. -/
theorem tilde_sdIso_of_data {m : ℕ} (ih : ∀ k < m, TildeDetermined k) {V' E' : Type} [Fintype V']
    [Fintype E'] {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X}
    (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph)
    (h1₂ : IsLevelOne N₂.graph) (hX : Nontrivial X) {θ₁ : MetricData E} {θ₂ : MetricData E'}
    (hθ₁ : IsMetricNetwork N₁ θ₁) (hθ₂ : IsMetricNetwork N₂ θ₂) (hG₁ : GoodParams hX N₁ θ₁)
    (hG₂ : GoodParams hX N₂ θ₂) (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂))
    (hD : SameCycleData (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX))
    (hF : SameFourNetworkBlocks (unrooted N₁ hN₁ hX) (unrooted N₂ hN₂ hX))
    (hc : bigCycleCount (unrooted N₁ hN₁ hX) = m) :
    Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX))) := by
  rcases m with _ | _ | m
  · exact tildeDetermined_zero X hX V E V' E' N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord hc
  · obtain ⟨C₁, hC₁⟩ := Set.ncard_eq_one.1 hc
    have hC₁m : C₁ ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4 := by
      rw [hC₁]
      rfl
    exact tilde_sdIso_one_of_sameCycleData (fun i _ => tildeDeterminedOneCycle i) hN₁ hN₂ h1₁ h1₂
      hX hθ₁ hθ₂ hG₁ hG₂ hord hD hc hC₁m rfl
  · exact tilde_sdIso_of_lt_of_data (by omega) ih hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord hD hF hc

/-- **The claim of the induction of Theorem 4 holds for every number of cycles of size at least
four**, by strong induction: the data of the two networks are read from their orderings by the
arguments of Lemmas 14, 15 and 16 at their parameters (`sameCycleData_of_sameOrdering`,
`sameFourNetworkBlocks_of_sameOrdering`), and `tilde_sdIso_of_data` applies. -/
theorem tildeDetermined (m : ℕ) : TildeDetermined m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X _ _ hX V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord hc
  exact tilde_sdIso_of_data ih hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord
    (sameCycleData_of_sameOrdering hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord)
    (sameFourNetworkBlocks_of_sameOrdering hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁ hG₂ hord) hc

end Banos2019
