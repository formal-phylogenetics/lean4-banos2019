module

public import Banos2019.Identify.QuartetCycles

/-!
# The blocks and the order of the cycles from `S` (Baños 2019, proofs of Lemmas 14, 15 and 16)

For parameters at which the statement of Lemma 12 holds, the 4-network blocks of `N⁻` are a function
of `S` (`lemma14_core`). For metric parameters at which it holds, the blocks, the size and the hybrid
block of the cycle `C_v` of `N⁻` whose hybrid node a set `s ∈ S` determines are functions of `S` and
`s` (`lemma15_core`), and, given such functions, which of its blocks are adjacent is a function of
the comparisons of the concordance factors of quartet trees on the same four taxa (`lemma16_core`).
Lemmas 14, 15 and 16 (`Banos2019/Identifiability.lean`) are these statements for generic parameters.

* `bcSets`: the set `S`.
* `complementBlock` (`Y_a`): the construction of the proof of Lemma 14 from `S`.
* `extensions` (`Z_T`), `blockRelation`, `blockCount`, `hybridBlock`: the constructions of the proof
  of Lemma 15 from `S`.
* `bcSetsOf`, `IsBCQuartetOf`: `S` and `q^BC_s`, read from the comparisons of concordance factors.
* `AdjacencyTest`, `IsNextBlock`, `placedBlocks`, `IsInBlockAt`, `FollowsBlock`, `adjacencyOf`: the
  procedure of the proof of Lemma 16. The test of Proposition 11 gives the adjacent blocks of a
  4-cycle and the two blocks `A_p`, `A_q` adjacent to the hybrid block `A₁` of a larger cycle; the
  other blocks are then placed one after the other from `A_q`, and the adjacent blocks are the
  consecutive ones.
* `adjacencyTest_iff`, `isBCQuartetOf_cf_iff_lt`, `followsBlock_iff`: what the test of
  Proposition 11 and the test of a step give, and the order the steps build, along a listing of the
  cycle from its hybrid node (`IsCycleOf.reverse`, `IsCycleOf.reflTransGen_apply_zero`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-- The set `S` of the sets of four taxa that satisfy the Big Cycle property. -/
def bcSets {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] (N : RootedNetwork V E X)
    (θ : MetricData E) : Set (Finset X) :=
  {s | #s = 4 ∧ BigCycleOn (cf N θ) s}

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ### The blocks of a cycle from `S` (proof of Lemma 15) -/

/-- `Z_T` (proof of Lemma 15): the taxa `e` with `T ∪ {e} ∈ S`. -/
def extensions (S : Set (Finset X)) (T : Finset X) : Set X := {e | insert e T ∈ S}

/-- The test of `k_v = 4` (proof of Lemma 15): the four sets `Z_{s ∖ {t}}`, `t ∈ s`, are pairwise
disjoint. -/
def ExtensionsDisjoint (S : Set (Finset X)) (s : Finset X) : Prop :=
  ∀ t ∈ s, ∀ t' ∈ s, t ≠ t' → Disjoint (extensions S (s.erase t)) (extensions S (s.erase t'))

/-- The taxon `t` of `s` in the hybrid block when `k_v ≥ 5` (proof of Lemma 15): `Z_{s ∖ {t}}` is
disjoint from the other three sets `Z_{s ∖ {t'}}`. -/
def IsHybridTaxon (S : Set (Finset X)) (s : Finset X) (t : X) : Prop :=
  t ∈ s ∧ ∀ t' ∈ s, t' ≠ t → Disjoint (extensions S (s.erase t)) (extensions S (s.erase t'))

/-- The blocks when `k_v = 4` (proof of Lemma 15): `Z_{s ∖ {t}}` is the block of `t`. -/
def SameBlockFour (S : Set (Finset X)) (s : Finset X) (x y : X) : Prop :=
  ∃ t ∈ s, x ∈ extensions S (s.erase t) ∧ y ∈ extensions S (s.erase t)

/-- The blocks when `k_v ≥ 5` (proof of Lemma 15). Let `a` be the taxon of `s` in the hybrid block, `d`
another taxon of `s`, `T = s ∖ {d}`, and `c ∈ T` other than `a`. A taxon `y ∉ Z_T` is in the block of
the `g ∈ T` for which `{y} ∪ s ∖ {g} ∈ S` (the paper's `{y, u, w, d}`); two taxa `x, y ∈ Z_T` are in the
same block when `{x, y} ∪ T ∖ {c} ∉ S` (the steps for `y ∉ Z_T`, applied to `T ∪ {x}` in place of
`s`). -/
def SameBlockFive (S : Set (Finset X)) (s : Finset X) (x y : X) : Prop :=
  ∃ a d c, d ∈ s ∧ c ∈ s.erase d ∧ a ≠ d ∧ c ≠ a ∧ IsHybridTaxon S s a ∧
    ((x ∉ extensions S (s.erase d) ∧ y ∉ extensions S (s.erase d) ∧
        ∃ g ∈ s.erase d, x ∈ extensions S (s.erase g) ∧ y ∈ extensions S (s.erase g)) ∨
      (x ∈ extensions S (s.erase d) ∧ y ∈ extensions S (s.erase d) ∧
        insert y (insert x ((s.erase d).erase c)) ∉ S))

/-- The blocks of the cycle determined by `s`, from `S` (proof of Lemma 15). -/
def blockRelation (S : Set (Finset X)) (s : Finset X) (x y : X) : Prop :=
  (ExtensionsDisjoint S s ∧ SameBlockFour S s x y) ∨
    (¬ ExtensionsDisjoint S s ∧ SameBlockFive S s x y)

/-- The size of the cycle determined by `s`, from `S`: four, or the number of blocks
(proof of Lemma 15). -/
def blockCount (S : Set (Finset X)) (s : Finset X) : ℕ :=
  if ExtensionsDisjoint S s then 4 else (Set.range fun x => {y | blockRelation S s x y}).ncard

/-- The hybrid block of the cycle determined by `s` when it has size at least five, from `S`: the set
`Z_{s ∖ {a}}` of the taxon `a` of `s` in the hybrid block (proof of Lemma 15). -/
def hybridBlock (S : Set (Finset X)) (s : Finset X) : Set X :=
  {x | ∃ t, IsHybridTaxon S s t ∧ x ∈ extensions S (s.erase t)}

section Determined

variable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}

omit [Fintype X] [DecidableEq X] [Fintype V] [Fintype E] in
theorem determines_congr {hN : IsBinaryRootedNetwork N} {s s' : Finset X} (h : s = s')
    (hs : #s = 4) (hs' : #s' = 4) (v : V) : Determines hN s hs v ↔ Determines hN s' hs' v := by
  subst h
  rfl

/-- **A set of `S` sharing three taxa with a set of `S` that determines `v` determines `v`** (Lemma 13). -/
theorem determines_insert_erase (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    {θ : MetricData E} (hθ : IsMetricNetwork N θ) {s : Finset X} (hs : s ∈ bcSets N θ) {t : X}
    (ht : t ∈ s) {e : X} (he : insert e (s.erase t) ∈ bcSets N θ) {v : V}
    (hv : Determines hN s hs.1 v) : Determines hN (insert e (s.erase t)) he.1 v := by
  obtain ⟨p, q, r, -, -, -, hpqr⟩ :=
    card_eq_three.1 (show #(s.erase t) = 3 by rw [card_erase_of_mem ht, hs.1])
  have hs_eq : s = {p, q, r, t} := by
    rw [← insert_erase ht, hpqr]
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  have he_eq : insert e (s.erase t) = {p, q, r, e} := by
    rw [hpqr]
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  have h₁ : #({p, q, r, t} : Finset X) = 4 := hs_eq ▸ hs.1
  have h₂ : #({p, q, r, e} : Finset X) = 4 := he_eq ▸ he.1
  have hbc₁ : BigCycleOn (cf N θ) {p, q, r, t} := by
    have := hs.2
    rw [hs_eq] at this
    convert this
  have hbc₂ : BigCycleOn (cf N θ) {p, q, r, e} := by
    have := he.2
    rw [he_eq] at this
    convert this
  rw [determines_congr he_eq he.1 h₂]
  exact (lemma13 hN h1 hθ h₁ h₂ hbc₁ hbc₂ v).1 ((determines_congr hs_eq hs.1 h₁ v).1 hv)

/-- **The sets of `S` sharing three taxa with a set that determines the hybrid node `v` of `C_v` are
the sets of four taxa that `C_v` separates** (Lemmas 12 and 13). -/
theorem mem_bcSets_insert_erase_iff (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {θ : MetricData E} (hθ : IsMetricNetwork N θ)
    (hS : ∀ s : Finset X, #s = 4 → (s ∈ bcSets N θ ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s))
    {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) {s : Finset X} (hs : s ∈ bcSets N θ)
    (hdet : Determines hN s hs.1 v.1.1) {t : X} (ht : t ∈ s) (e : X) :
    insert e (s.erase t) ∈ bcSets N θ ↔
      #(insert e (s.erase t)) = 4 ∧ SeparatesQuartet (unrooted N hN hX) C v (insert e (s.erase t)) := by
  constructor
  · intro he
    obtain ⟨C', hsep⟩ := (determines_iff_separatesQuartet hN h1 hX he.1 v).1
      (determines_insert_erase hN h1 hθ hs ht he hdet)
    obtain rfl := hv.cycle_eq h1 hC hsep.1 hsep.2.1 |>.symm
    exact ⟨he.1, hsep⟩
  · rintro ⟨h4, hsep⟩
    exact (hS _ h4).2 ⟨C, v, four_le_ncard_of_separatesQuartet h1 hC hv h4 hsep, hsep⟩

/-- **`Z_{s ∖ {t}}` in terms of the blocks** (proof of Lemma 15): for `s ∈ S` determining the hybrid
node `v` of `C_v`, with `a ∈ s` in the hybrid block, a taxon `e` is in `Z_{s ∖ {t}}` exactly when its
block is not that of a taxon of `s ∖ {t}`, and is the hybrid block if `t = a`. -/
theorem mem_extensions_iff (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {θ : MetricData E} (hθ : IsMetricNetwork N θ)
    (hS : ∀ s : Finset X, #s = 4 → (s ∈ bcSets N θ ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s))
    {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) {s : Finset X} (hs : s ∈ bcSets N θ)
    (hdet : Determines hN s hs.1 v.1.1) (hinj : Set.InjOn (blockNode (unrooted N hN hX) C) s)
    {a : X} (ha : a ∈ s) (hβa : blockNode (unrooted N hN hX) C a = v) {t : X} (ht : t ∈ s) (e : X) :
    e ∈ extensions (bcSets N θ) (s.erase t) ↔
      blockNode (unrooted N hN hX) C e ∉ blockNode (unrooted N hN hX) C '' ↑(s.erase t) ∧
        (blockNode (unrooted N hN hX) C e = v ∨ t ≠ a) := by
  set β := blockNode (unrooted N hN hX) C
  have h3 : #(s.erase t) = 3 := by rw [card_erase_of_mem ht, hs.1]
  have hinjT : Set.InjOn β ↑(s.erase t) := hinj.mono (by simp)
  have hhyb : (∃ z ∈ s.erase t, β z = v) ↔ t ≠ a := by
    constructor
    · rintro ⟨z, hz, hzv⟩ rfl
      obtain ⟨hzt, hz⟩ := mem_erase.1 hz
      exact hzt (hinj hz ha (hzv.trans hβa.symm))
    · intro hta
      exact ⟨a, mem_erase.2 ⟨Ne.symm hta, ha⟩, hβa⟩
  change insert e (s.erase t) ∈ bcSets N θ ↔ _
  rw [mem_bcSets_insert_erase_iff hN h1 hX hθ hS hC hv hs hdet ht e,
    separatesQuartet_iff h1 hC hv]
  constructor
  · rintro ⟨h4, hinj', z, hz, hzv⟩
    have heT : e ∉ s.erase t := fun he => by
      rw [card_insert_of_mem he, h3] at h4
      norm_num at h4
    rw [coe_insert, Set.injOn_insert (fun h => heT (mem_coe.1 h))] at hinj'
    refine ⟨hinj'.2, ?_⟩
    rcases mem_insert.1 hz with rfl | hz
    · exact Or.inl hzv
    · exact Or.inr (hhyb.1 ⟨z, hz, hzv⟩)
  · rintro ⟨hβe, hev⟩
    have heT : e ∉ s.erase t := fun he => hβe ⟨e, he, rfl⟩
    refine ⟨by rw [card_insert_of_notMem heT, h3], ?_, ?_⟩
    · rw [coe_insert, Set.injOn_insert (fun h => heT (mem_coe.1 h))]
      exact ⟨hinjT, hβe⟩
    · rcases hev with hev | hev
      · exact ⟨e, mem_insert_self _ _, hev⟩
      · obtain ⟨z, hz, hzv⟩ := hhyb.2 hev
        exact ⟨z, mem_insert_of_mem hz, hzv⟩

/-- The statement of Lemma 12 at `θ`, for the sets of `S`. -/
theorem mem_bcSets_iff_of_lemma12 {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}
    {θ : MetricData E}
    (h12 : ∀ s : Finset X, #s = 4 → (BigCycleOn (cf N θ) s ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s))
    (s : Finset X) (h4 : #s = 4) :
    s ∈ bcSets N θ ↔ ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s :=
  ⟨fun h => (h12 s h4).1 (by convert h.2), fun h => ⟨h4, by convert (h12 s h4).2 h⟩⟩

end Determined

/-! ### The 4-network blocks from `S` (proof of Lemma 14) -/

/-- `Y_a` (proof of Lemma 14): the taxa other than `a` of the sets of `S` that contain `a`. -/
def complementBlock (S : Set (Finset X)) (a : X) : Set X :=
  ⋃ s ∈ {s | s ∈ S ∧ a ∈ s}, ↑(s.erase a)

/-- **The 4-network blocks from `S`** (Lemma 14 at given parameters): at parameters at which the
statement of Lemma 12 holds, the 4-network block of `x` is the complement of `Y_x`. A set of four
taxa with the Big Cycle property is separated by a cycle of size at least four (Lemma 12), so its
taxa are in distinct 4-network blocks. Conversely, a taxon `y` outside the 4-network block of `x` is
in another block than `x` of some cycle `C_v` of size at least four (Lemma 4); with taxa `c`, `d` of
two other blocks, one of the four in the hybrid block, `{x, y, c, d}` has the Big Cycle property
(Lemma 12), and `y ∈ Y_x`. -/
theorem lemma14_core {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X)
    {θ : MetricData E}
    (h12 : ∀ s : Finset X, #s = 4 → (BigCycleOn (cf N θ) s ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s)) (x y : X) :
    y ∉ complementBlock (bcSets N θ) x ↔
      SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf
        (familyEdges (cyclesOfSizeAtLeast (unrooted N hN hX).graph 4)) x y := by
  have hS := mem_bcSets_iff_of_lemma12 h12
  constructor
  · -- a taxon outside the 4-network block of `x` is in `Y_x`
    intro hy
    by_contra hnb
    obtain ⟨C, ⟨hC, hC4⟩, hCxy⟩ := lemma4 (unrooted N hN hX).leaf (unrooted_isConnected hN hX)
      (unrooted_isLevelOne hN h1 hX)
      (fun C (hC : C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4) => hC.1) hnb
    obtain ⟨v, hv⟩ := exists_isHybridNodeOf h1 hC
    obtain ⟨c, d, h4, hsep⟩ := exists_separatesQuartet_of_not_sameBlock h1 hC hC4 hv hCxy
    have hxy : y ≠ x := fun h => hCxy (h ▸ .refl)
    refine hy (Set.mem_biUnion (x := {x, y, c, d}) ⟨(hS _ h4).2 ⟨C, v, hC4, hsep⟩, by simp⟩ ?_)
    simp [hxy]
  · -- the taxa of a set of `S` are in distinct 4-network blocks
    intro hsb hy
    obtain ⟨s, ⟨hsS, hxs⟩, hys⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨hyx, hys⟩ := mem_erase.1 hys
    obtain ⟨C, v, hC4, hsep⟩ := (hS s hsS.1).1 hsS
    exact hsep.2.2.1 x hxs y hys (Ne.symm hyx)
      (hsb.mono (Set.subset_sUnion_of_mem (show C ∈ cyclesOfSizeAtLeast _ 4 from ⟨hsep.1, hC4⟩)))

/-- **The blocks, the size and the hybrid block of a cycle from `S`** (Lemma 15 at given parameters):
for metric parameters at which the statement of Lemma 12 holds and `s ∈ S` determining the hybrid
node `w` of the cycle `C_w` of `N⁻`, `blockRelation S s` gives the blocks of `C_w`, `blockCount S s`
its size and, when the size is at least five, `hybridBlock S s` its hybrid block. -/
theorem lemma15_core {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X)
    {θ : MetricData E} (hθ : IsMetricNetwork N θ)
    (h12 : ∀ s : Finset X, #s = 4 → (BigCycleOn (cf N θ) s ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s))
    {s : Finset X} (hs : s ∈ bcSets N θ) {C : Set _} {w : SemidirectedVertex hN.1 hX}
    (hC : IsCycle (unrooted N hN hX).graph C) (hw : IsHybridNodeOf (unrooted N hN hX) C w)
    (hdet : Determines hN s hs.1 w.1.1) :
    (∀ x y, blockRelation (bcSets N θ) s x y ↔
        SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) ∧
      blockCount (bcSets N θ) s = C.ncard ∧
      (5 ≤ C.ncard → hybridBlock (bcSets N θ) s = {x | DescendsFrom (unrooted N hN hX) w x}) := by
  have hS := mem_bcSets_iff_of_lemma12 h12
  -- `s` is separated by `C_w` (Lemma 12): its taxa are in distinct blocks, `a` in the hybrid block
  obtain ⟨C', hsep⟩ := (determines_iff_separatesQuartet hN h1 hX hs.1 w).1 hdet
  rw [← hw.cycle_eq h1 hC hsep.1 hsep.2.1] at hsep
  obtain ⟨hinj, a, ha, hβa⟩ := (separatesQuartet_iff h1 hC hw s).1 hsep
  have hC4 := four_le_ncard_of_separatesQuartet h1 hC hw hs.1 hsep
  have hZ : ∀ {t : X} (ht : t ∈ s) (e : X), _ := fun {t} ht e =>
    mem_extensions_iff hN h1 hX hθ hS hC hw hs hdet hinj ha hβa (t := t) ht e
  set β := blockNode (unrooted N hN hX) C with hβ
  set S := bcSets N θ with hSdef
  have := hN.1.finite_vertices
  have himg : (β '' ↑s).ncard = 4 := by rw [hinj.ncard_image, Set.ncard_coe_finset, hs.1]
  have hsub : β '' ↑s ⊆ cycleNodes (unrooted N hN hX).graph C := by
    rintro _ ⟨x, -, rfl⟩
    exact blockNode_mem hC x
  have hsame : ∀ x y, SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y ↔
      β x = β y :=
    sameBlock_iff_blockNode_eq h1 hC
  -- the other three taxa `p, q, r` of `s`
  obtain ⟨p, q, r, hpq, hpr, hqr, hpqr⟩ :=
    card_eq_three.1 (show #(s.erase a) = 3 by rw [card_erase_of_mem ha, hs.1])
  have hmem : ∀ z ∈ ({p, q, r} : Finset X), z ≠ a ∧ z ∈ s := fun z hz => mem_erase.1 (hpqr ▸ hz)
  obtain ⟨hpa, hp⟩ := hmem p (by simp)
  obtain ⟨hqa, hq⟩ := hmem q (by simp)
  obtain ⟨hra, hr⟩ := hmem r (by simp)
  rcases hC4.eq_or_lt with h4 | h5
  · -- `k_v = 4`: the blocks are the images of the four taxa of `s`, and `Z_{s ∖ {t}}` is that of `t`
    have hnodes : cycleNodes (unrooted N hN hX).graph C = β '' ↑s :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_cycleNodes hC, ← h4, himg])
        (Set.toFinite _)).symm
    have hZ4 : ∀ t ∈ s, ∀ e, e ∈ extensions S (s.erase t) ↔ β e = β t := by
      intro t ht e
      rw [hZ ht e]
      constructor
      · rintro ⟨hβe, -⟩
        obtain ⟨z, hz, hze⟩ : β e ∈ β '' ↑s := hnodes ▸ blockNode_mem hC e
        by_contra hne
        exact hβe ⟨z, mem_erase.2 ⟨fun h => hne (h ▸ hze.symm), hz⟩, hze⟩
      · intro he
        refine ⟨?_, ?_⟩
        · rintro ⟨z, hz, hze⟩
          obtain ⟨hzt, hz⟩ := mem_erase.1 hz
          exact hzt (hinj hz ht (hze.trans he))
        · by_cases hta : t = a
          · left
            rw [he, hta, hβa]
          · exact Or.inr hta
    have hED : ExtensionsDisjoint S s := by
      intro t ht t' ht' htt'
      refine Set.disjoint_left.2 fun e he he' => ?_
      rw [hZ4 t ht] at he
      rw [hZ4 t' ht'] at he'
      exact htt' (hinj ht ht' (he.symm.trans he'))
    refine ⟨fun x y => ?_, ?_, fun h => by omega⟩
    · rw [hsame]
      simp only [blockRelation, hED, true_and, not_true_eq_false, false_and, or_false,
        SameBlockFour]
      constructor
      · rintro ⟨t, ht, hx, hy⟩
        rw [hZ4 t ht] at hx hy
        exact hx.trans hy.symm
      · intro hxy
        obtain ⟨t, ht, hxt⟩ : β x ∈ β '' ↑s := hnodes ▸ blockNode_mem hC x
        exact ⟨t, ht, (hZ4 t ht x).2 hxt.symm, (hZ4 t ht y).2 (hxy ▸ hxt.symm)⟩
    · simp only [blockCount, hED, ↓reduceIte]
      exact h4
  · -- `k_v ≥ 5`: a taxon `e₀` in a block other than those of `s`
    obtain ⟨u₀, hu₀, hu₀s⟩ :=
      hC.exists_mem_cycleNodes_notMem (Set.toFinite (β '' ↑s)) (by omega)
    obtain ⟨e₀, rfl⟩ := exists_blockNode_eq h1 hC hu₀
    have he₀ : ∀ t ∈ s, t ≠ a → e₀ ∈ extensions S (s.erase t) := fun t ht hta =>
      (hZ ht e₀).2 ⟨fun ⟨z, hz, hze⟩ => hu₀s ⟨z, mem_of_mem_erase hz, hze⟩, Or.inr hta⟩
    -- `Z_{s ∖ {a}}` is the hybrid block; for `t ≠ a`, `Z_{s ∖ {t}}` is the rest of the blocks
    have hZa : ∀ e, e ∈ extensions S (s.erase a) ↔ β e = w := by
      intro e
      rw [hZ ha e]
      simp only [ne_eq, not_true_eq_false, or_false]
      constructor
      · exact fun h => h.2
      · intro he
        refine ⟨?_, he⟩
        rintro ⟨z, hz, hze⟩
        obtain ⟨hza, hz⟩ := mem_erase.1 hz
        exact hza (hinj hz ha (hze.trans (he.trans hβa.symm)))
    have hZt : ∀ t ∈ s, t ≠ a → ∀ e, e ∈ extensions S (s.erase t) ↔ β e ∉ β '' ↑(s.erase t) := by
      intro t ht hta e
      rw [hZ ht e]
      simp only [ne_eq, hta, not_false_eq_true, or_true, and_true]
    -- the taxon `a` is the one whose set `Z_{s ∖ {a}}` meets no other
    have hHT : ∀ t, IsHybridTaxon S s t ↔ t = a := by
      intro t
      constructor
      · rintro ⟨ht, hdisj⟩
        by_contra hta
        obtain ⟨t', ht', ht't, ht'a⟩ : ∃ t' ∈ s, t' ≠ t ∧ t' ≠ a := by
          by_cases htp : t = p
          · exact ⟨q, hq, fun h => hpq (htp.symm.trans h.symm), hqa⟩
          · exact ⟨p, hp, Ne.symm htp, hpa⟩
        exact Set.disjoint_left.1 (hdisj t' ht' ht't) (he₀ t ht hta) (he₀ t' ht' ht'a)
      · rintro rfl
        refine ⟨ha, fun t' ht' ht'a => Set.disjoint_left.2 fun e he he' => ?_⟩
        rw [hZa] at he
        rw [hZt t' ht' ht'a] at he'
        exact he' ⟨t, mem_erase.2 ⟨Ne.symm ht'a, ha⟩, hβa.trans he.symm⟩
    have hnED : ¬ ExtensionsDisjoint S s := fun hED =>
      Set.disjoint_left.1 (hED p hp q hq hpq) (he₀ p hp hpa) (he₀ q hq hqa)
    -- a taxon `x ∉ Z_{s ∖ {d}}` is in the block of `g ∈ s ∖ {d}` exactly when `x ∈ Z_{s ∖ {g}}`
    have hcase₁ : ∀ d ∈ s, d ≠ a → ∀ x, x ∉ extensions S (s.erase d) → ∀ g ∈ s.erase d,
        (x ∈ extensions S (s.erase g) ↔ β x = β g) := by
      intro d hd hda x hx g hg
      rw [hZt d hd hda, not_not] at hx
      obtain ⟨m, hm, hmx⟩ := hx
      obtain ⟨hgd, hg⟩ := mem_erase.1 hg
      rw [hZ hg x]
      constructor
      · rintro ⟨hxg, -⟩
        by_contra hne
        exact hxg ⟨m, mem_erase.2 ⟨fun h => hne (h ▸ hmx.symm), mem_of_mem_erase hm⟩, hmx⟩
      · intro hxg
        refine ⟨?_, ?_⟩
        · rintro ⟨z, hz, hzx⟩
          obtain ⟨hzg, hz⟩ := mem_erase.1 hz
          exact hzg (hinj hz hg (hzx.trans hxg))
        · by_cases hga : g = a
          · left
            rw [hxg, hga, hβa]
          · exact Or.inr hga
    -- two taxa `x, y ∈ Z_{s ∖ {d}}`: `{x, y} ∪ (s ∖ {d}) ∖ {c} ∈ S` exactly when their blocks differ
    have hcase₂ : ∀ d ∈ s, d ≠ a → ∀ c ∈ s.erase d, c ≠ a → ∀ x y,
        x ∈ extensions S (s.erase d) → y ∈ extensions S (s.erase d) →
        (insert y (insert x ((s.erase d).erase c)) ∈ S ↔ β y ≠ β x) := by
      intro d hd hda c hc hca x y hx hy
      have hZd := hZt d hd hda
      have hdetx := determines_insert_erase hN h1 hθ hs hd hx hdet
      obtain ⟨hinjx, -⟩ := (separatesQuartet_iff h1 hC hw _).1
        ((mem_bcSets_insert_erase_iff hN h1 hX hθ hS hC hw hs hdet hd x).1 hx).2
      have hcx : c ≠ x := by
        rintro rfl
        rw [hZd] at hx
        exact hx ⟨c, hc, rfl⟩
      have heq : insert x ((s.erase d).erase c) = (insert x (s.erase d)).erase c := by
        rw [erase_insert_of_ne (Ne.symm hcx)]
      have hax : a ∈ insert x (s.erase d) := mem_insert_of_mem (mem_erase.2 ⟨Ne.symm hda, ha⟩)
      rw [heq]
      change y ∈ extensions S ((insert x (s.erase d)).erase c) ↔ _
      rw [mem_extensions_iff hN h1 hX hθ hS hC hw hx hdetx hinjx hax hβa
        (mem_insert_of_mem hc) y]
      simp only [hca, ne_eq, not_false_eq_true, or_true, and_true]
      rw [← heq]
      constructor
      · intro h hyx
        exact h ⟨x, mem_insert_self _ _, hyx.symm⟩
      · rintro hyx ⟨m, hm, hmy⟩
        rcases mem_insert.1 hm with rfl | hm
        · exact hyx hmy.symm
        · rw [hZd] at hy
          exact hy ⟨m, mem_of_mem_erase hm, hmy⟩
    -- the blocks
    have hB : ∀ x y, blockRelation S s x y ↔ β x = β y := by
      intro x y
      simp only [blockRelation, hnED, false_and, not_false_eq_true, true_and, false_or]
      constructor
      · rintro ⟨a', d, c, hd, hc, ha'd, hca', hHa', hcase⟩
        obtain rfl := (hHT a').1 hHa'
        rcases hcase with ⟨hx, hy, g, hg, hxg, hyg⟩ | ⟨hx, hy, hxy⟩
        · exact ((hcase₁ d hd (Ne.symm ha'd) x hx g hg).1 hxg).trans
            ((hcase₁ d hd (Ne.symm ha'd) y hy g hg).1 hyg).symm
        · by_contra hne
          exact hxy ((hcase₂ d hd (Ne.symm ha'd) c hc hca' x y hx hy).2 (Ne.symm hne))
      · intro hxy
        refine ⟨a, p, q, hp, mem_erase.2 ⟨Ne.symm hpq, hq⟩, Ne.symm hpa, hqa, (hHT a).2 rfl, ?_⟩
        have hZp := hZt p hp hpa
        by_cases hx : x ∈ extensions S (s.erase p)
        · have hy : y ∈ extensions S (s.erase p) := by
            rw [hZp] at hx ⊢
            rwa [← hxy]
          right
          refine ⟨hx, hy, fun h => ?_⟩
          exact (hcase₂ p hp hpa q (mem_erase.2 ⟨Ne.symm hpq, hq⟩) hqa x y hx hy).1 h hxy.symm
        · have hy : y ∉ extensions S (s.erase p) := by
            rw [hZp] at hx ⊢
            rwa [← hxy]
          left
          have hx' := hx
          rw [hZp, not_not] at hx'
          obtain ⟨g, hg, hgx⟩ := hx'
          exact ⟨hx, hy, g, hg, (hcase₁ p hp hpa x hx g hg).2 hgx.symm,
            (hcase₁ p hp hpa y hy g hg).2 (hxy ▸ hgx.symm)⟩
    refine ⟨fun x y => (hB x y).trans (hsame x y).symm, ?_, fun _ => ?_⟩
    · -- the number of blocks
      simp only [blockCount, hnED, ↓reduceIte]
      have hrange : (Set.range fun x => {y | blockRelation S s x y}) =
          (fun u => {y | β y = u}) '' cycleNodes (unrooted N hN hX).graph C := by
        ext B
        constructor
        · rintro ⟨x, rfl⟩
          refine ⟨β x, blockNode_mem hC x, ?_⟩
          ext y
          simp only [Set.mem_ofPred_eq, hB]
          exact eq_comm
        · rintro ⟨u, hu, rfl⟩
          obtain ⟨x, rfl⟩ := exists_blockNode_eq h1 hC hu
          refine ⟨x, ?_⟩
          ext y
          simp only [Set.mem_ofPred_eq, hB]
          exact eq_comm
      rw [hrange, Set.InjOn.ncard_image, ncard_cycleNodes hC]
      intro u hu u' hu' huu'
      obtain ⟨x, rfl⟩ := exists_blockNode_eq h1 hC hu
      exact (Set.ext_iff.1 huu' x).1 rfl
    · -- the hybrid block
      ext x
      simp only [hybridBlock, hHT, exists_eq_left, Set.mem_ofPred_eq, hZa]
      exact blockNode_eq_iff_descendsFrom h1 hC hw x

/-! ### The order of the blocks from the orderings (proof of Lemma 16) -/

/-- The sets of four taxa with the Big Cycle property, read from the comparisons `R` of the
concordance factors of quartet trees on the same four taxa: no two of their trees compare both ways. -/
def bcSetsOf (R : QuartetTree X → QuartetTree X → Prop) : Set (Finset X) :=
  {s | #s = 4 ∧ ∀ q ∈ treesOn s, ∀ r ∈ treesOn s, q ≠ r → ¬ (R q r ∧ R r q)}

/-- `q` is `q^BC_s`, read from the comparisons `R`: below the other two trees on `s`. -/
def IsBCQuartetOf (R : QuartetTree X → QuartetTree X → Prop) (s : Finset X) (q : QuartetTree X) :
    Prop :=
  q ∈ treesOn s ∧ ∀ r ∈ treesOn s, r ≠ q → R q r ∧ ¬ R r q

/-- The test of Proposition 11 for the blocks of `x` and `y` (proof of Lemma 16), read from the
comparisons `R` and the blocks `Bl`: `x` and `y` are in different blocks, and `q^BC_{xyzz'} ≠ xy|zz'`
for all `z, z'` such that `x, y, z, z'` are in four distinct blocks. -/
def AdjacencyTest (Bl : X → X → Prop) (R : QuartetTree X → QuartetTree X → Prop) (x y : X) : Prop :=
  ¬ Bl x y ∧ ∀ z z' (h : Distinct4 x y z z'), ¬ Bl x z → ¬ Bl x z' → ¬ Bl y z → ¬ Bl y z' →
    ¬ Bl z z' → ¬ IsBCQuartetOf R {x, z, y, z'} (quartetTree x y z z' h)

/-- A step of the order of the blocks around the cycle (proof of Lemma 16), read from the comparisons
`R` and the blocks `Bl`. With `a` in the hybrid block `A₁`, `p` in a block `A_p` adjacent to `A₁`, and
`F` the taxa of the blocks already placed, the block of `t` is the next one when `t` is neither in `F`
nor in `A_p`, and `q^BC_{atpx} ≠ at|xp` for every taxon `x` in none of `F`, `A_p` and the block of
`t`. -/
def IsNextBlock (Bl : X → X → Prop) (R : QuartetTree X → QuartetTree X → Prop) (a p : X)
    (F : Set X) (t : X) : Prop :=
  t ∉ F ∧ ¬ Bl p t ∧ ∀ x (h : Distinct4 a t x p), x ∉ F → ¬ Bl p x → ¬ Bl t x →
    ¬ IsBCQuartetOf R {a, x, t, p} (quartetTree a t x p h)

/-- The taxa of the blocks placed after `m` steps (proof of Lemma 16): the hybrid block `A₁` of `a`
and the block `A_q` of `q` adjacent to it, followed by the `m` blocks that `IsNextBlock` gives in
turn, the other block `A_p` of `p` adjacent to `A₁` being set aside. -/
def placedBlocks (Bl : X → X → Prop) (R : QuartetTree X → QuartetTree X → Prop) (a p q : X) :
    ℕ → Set X
  | 0 => {t | Bl a t ∨ Bl q t}
  | m + 1 => placedBlocks Bl R a p q m ∪ {t | IsNextBlock Bl R a p (placedBlocks Bl R a p q m) t}

/-- `t` is in the `i`-th block from the hybrid block `A₁` of `a` (`i = 0`) around the cycle, on the
side of the block `A_q` of `q` (`i = 1`), the block `A_p` of `p` being the other block adjacent to
`A₁` (proof of Lemma 16). -/
def IsInBlockAt (Bl : X → X → Prop) (R : QuartetTree X → QuartetTree X → Prop) (a p q : X) :
    ℕ → X → Prop
  | 0, t => Bl a t
  | 1, t => Bl q t
  | m + 2, t => IsNextBlock Bl R a p (placedBlocks Bl R a p q m) t

/-- The block of `y` follows that of `x` in the order `A₁, A_q, …, A_p` of the `k` blocks around the
cycle, from the hybrid block `A₁` of `a` (proof of Lemma 16): they are the `i`-th and the `(i + 1)`-th
blocks, or the `(k - 2)`-th block and `A_p`, or `A_p` and `A₁`. -/
def FollowsBlock (Bl : X → X → Prop) (R : QuartetTree X → QuartetTree X → Prop) (k : ℕ)
    (a p q x y : X) : Prop :=
  (∃ i, IsInBlockAt Bl R a p q i x ∧ IsInBlockAt Bl R a p q (i + 1) y) ∨
    (IsInBlockAt Bl R a p q (k - 2) x ∧ Bl p y) ∨ (Bl p x ∧ Bl a y)

/-- The adjacent blocks of the cycle determined by `s`, read from the comparisons `R` and from the
blocks `B`, the size `K` and the hybrid block `H` given by `S` (proof of Lemma 16). For a cycle of
size four, `x` and `y` pass the test of Proposition 11 (`AdjacencyTest`). For a larger cycle, with `a`
in the hybrid block `A₁`, the taxa `p` and `q` in different blocks pass that test with `a`, so that
their blocks `A_p` and `A_q` are the two blocks adjacent to `A₁`; the blocks are ordered from `A₁` and
`A_q` by the test of `IsNextBlock`, and the blocks of `x` and `y` are consecutive in this order. -/
def adjacencyOf (B : Set (Finset X) → Finset X → X → X → Prop) (K : Set (Finset X) → Finset X → ℕ)
    (H : Set (Finset X) → Finset X → Set X) (R : QuartetTree X → QuartetTree X → Prop) (s : Finset X)
    (x y : X) : Prop :=
  (K (bcSetsOf R) s = 4 ∧ AdjacencyTest (B (bcSetsOf R) s) R x y) ∨
    (K (bcSetsOf R) s ≠ 4 ∧ ∃ a ∈ H (bcSetsOf R) s, ∃ p q,
      AdjacencyTest (B (bcSetsOf R) s) R a p ∧ AdjacencyTest (B (bcSetsOf R) s) R a q ∧
        ¬ B (bcSetsOf R) s p q ∧
        (FollowsBlock (B (bcSetsOf R) s) R (K (bcSetsOf R) s) a p q x y ∨
          FollowsBlock (B (bcSetsOf R) s) R (K (bcSetsOf R) s) a p q y x))

/-! ### Walks along a cycle -/

section CycleWalk

variable {V' E' : Type*} {G : DirectedMultigraph V' E'}

/-- **A cycle read backwards is a cycle**: the nodes `v 0, v (-1), v (-2), …`. -/
theorem IsCycleOf.reverse {n : ℕ} {v : Fin (n + 1) → V'} {e : Fin (n + 1) → E'}
    (hC : IsCycleOf G (n + 1) v e) :
    IsCycleOf G (n + 1) (fun i => v (-i)) (fun i => e (-i - 1)) where
  pos := hC.pos
  joins i := by
    have h := hC.joins (-i - 1)
    simp only [finRotate_apply, sub_add_cancel] at h ⊢
    rw [neg_add']
    exact Or.symm h
  injective_node := hC.injective_node.comp neg_injective
  injective_edge := hC.injective_edge.comp fun i j h => by simpa using h

/-- **A walk along a cycle from `v 0` to `v j` avoiding a set `F` of nodes**, when none of the nodes
`v 0, …, v j` is in `F`. -/
theorem IsCycleOf.reflTransGen_apply_zero {n : ℕ} {v : Fin (n + 1) → V'} {e : Fin (n + 1) → E'}
    (hC : IsCycleOf G (n + 1) v e) {F : Set V'} (j : Fin (n + 1)) (hF : ∀ l ≤ j, v l ∉ F) :
    Relation.ReflTransGen (fun p q => G.AdjOn (Set.range e) p q ∧ p ∉ F ∧ q ∉ F) (v 0) (v j) := by
  obtain ⟨m, hm⟩ := j
  induction m with
  | zero => exact .refl
  | succ m ih =>
    have hm' : m < n + 1 := by omega
    have hstep : finRotate (n + 1) ⟨m, hm'⟩ = ⟨m + 1, hm⟩ := Fin.ext (by
      rw [coe_finRotate_of_ne_last fun h => by
        have := congrArg Fin.val h
        rw [Fin.val_last] at this
        exact absurd this (by simp only; omega)])
    have hj := hC.joins ⟨m, hm'⟩
    rw [hstep] at hj
    exact (ih hm' fun l hl => hF l (hl.trans (Fin.mk_le_mk.2 (Nat.le_succ m)))).tail
      ⟨⟨e ⟨m, hm'⟩, ⟨_, rfl⟩, hj⟩, hF _ (Fin.mk_le_mk.2 (Nat.le_succ m)), hF _ le_rfl⟩

end CycleWalk

section Comparisons

variable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E}

/-- The Big Cycle property, with the instances of this section. -/
theorem bigCycleOn_iff_mem_bcSets {s : Finset X} (hs : #s = 4) :
    BigCycleOn (cf N θ) s ↔ s ∈ bcSets N θ :=
  ⟨fun h => ⟨hs, by convert h⟩, fun h => by convert h.2⟩

/-- The comparisons of the concordance factors give `S`. -/
theorem bcSetsOf_cf :
    bcSetsOf (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) = bcSets N θ := by
  ext s
  simp only [bcSetsOf, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hs, h⟩
    refine (bigCycleOn_iff_mem_bcSets hs).1 fun q hq r hr hqr hcf => h q hq r hr hqr ?_
    have hq' := (mem_filter.1 hq).2
    have hr' := (mem_filter.1 hr).2
    exact ⟨⟨hq'.trans hr'.symm, hcf.le⟩, ⟨hr'.trans hq'.symm, hcf.ge⟩⟩
  · intro h
    refine ⟨h.1, fun q hq r hr hqr ⟨h₁, h₂⟩ => ?_⟩
    exact (bigCycleOn_iff_mem_bcSets h.1).2 h q hq r hr hqr (le_antisymm h₁.2 h₂.2)

/-- The comparisons of the concordance factors give `q^BC_s`. -/
theorem isBCQuartetOf_cf (s : Finset X) (q : QuartetTree X) :
    IsBCQuartetOf (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) s q ↔
      IsBCQuartet (cf N θ) s q := by
  unfold IsBCQuartetOf IsBCQuartet
  refine and_congr_right fun hq => forall₂_congr fun r hr => imp_congr_right fun _ => ?_
  have hqr : q.taxa = r.taxa := (mem_filter.1 hq).2.trans (mem_filter.1 hr).2.symm
  constructor
  · rintro ⟨⟨-, h₁⟩, h₂⟩
    exact lt_of_le_of_ne h₁ fun h => h₂ ⟨hqr.symm, h.ge⟩
  · intro h
    exact ⟨⟨hqr, h.le⟩, fun ⟨_, h'⟩ => not_le.2 h h'⟩

/-- **Proposition 11 for a set of four taxa that `C_v` separates**: `q^BC ≠ xy|zz'` exactly when the
blocks of `x` and `y` are joined along `C_v` avoiding those of `z` and `z'`. The 4-cycle of `Q⁻_{xyzz'}`
is the cycle induced by `C_v`, with the same order of the blocks. -/
theorem not_isBCQuartet_iff_joinedAvoiding (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) (hθ : IsMetricNetwork N θ)
    (hS : ∀ s : Finset X, #s = 4 → (s ∈ bcSets N θ ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s))
    {C : Set _} (hC4 : 4 ≤ C.ncard) {w : SemidirectedVertex hN.1 hX}
    {x y z z' : X} (h : Distinct4 x y z z')
    (hsep : SeparatesQuartet (unrooted N hN hX) C w {x, y, z, z'}) :
    ¬ IsBCQuartet (cf N θ) {x, z, y, z'} (quartetTree x y z z' h) ↔
      JoinedAvoiding (unrooted N hN hX) C {z, z'} x y := by
  obtain ⟨hxy, hxz, hxz', hyz, hyz', hzz'⟩ := h
  have hD : Distinct4 x z y z' := ⟨hxz, hxy, hxz', hyz.symm, hzz', hyz'⟩
  have heq : ({x, z, y, z'} : Finset X) = {x, y, z, z'} := by
    ext m
    simp only [mem_insert, mem_singleton]
    tauto
  have h4 : #({x, z, y, z'} : Finset X) = 4 := Distinct4.card_insert_eq hD
  have hsep' : SeparatesQuartet (unrooted N hN hX) C w {x, z, y, z'} := by
    rw [heq]
    exact hsep
  have hbc : BigCycleOn (cf N θ) {x, z, y, z'} :=
    (bigCycleOn_iff_mem_bcSets h4).2 ((hS _ h4).2 ⟨C, w, hC4, hsep'⟩)
  obtain ⟨CQ, wQ, hCQ, hCQ4, hwQ, hwQv⟩ :=
    (determines_iff_separatesQuartet hN h1 hX h4 w).2 ⟨C, hsep'⟩
  have h11 := proposition11 hN h1 hθ hD h4 hbc hCQ hCQ4
  have hadj := adjacentBlocks_quartetUnrooted_iff hN h1 hX h4 hsep' hCQ hCQ4 hwQ hwQv
    (a := x) (c := y) (by simp) (by simp) hxy
  have herase : (({x, z, y, z'} : Finset X).erase x).erase y = {z, z'} := by
    ext m
    simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hmy, hmx, hm⟩
      tauto
    · rintro (rfl | rfl)
      · exact ⟨hyz.symm, hxz.symm, Or.inr (Or.inl rfl)⟩
      · exact ⟨hyz'.symm, hxz'.symm, Or.inr (Or.inr (Or.inr rfl))⟩
  have hcoe : (↑({z, z'} : Finset X) : Set X) = {z, z'} := by simp
  rw [herase, hcoe] at hadj
  exact (not_congr h11).trans (not_not.trans hadj)

/-- **The test of Proposition 11 gives the blocks adjacent to the hybrid block, and the adjacent blocks
of a cycle of size four.** Two taxa `x` and `y`, with `x` in the hybrid block of `C_w` or `C_w` of size
four, pass `AdjacencyTest` exactly when their blocks are adjacent: the sets of four taxa in distinct
blocks that contain them are then the sets that `C_w` separates. -/
theorem adjacencyTest_iff (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) (hθ : IsMetricNetwork N θ)
    (hS : ∀ s : Finset X, #s = 4 → (s ∈ bcSets N θ ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s))
    {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : 4 ≤ C.ncard)
    {w : SemidirectedVertex hN.1 hX} (hw : IsHybridNodeOf (unrooted N hN hX) C w)
    {Bl : X → X → Prop}
    (hBl : ∀ a b, Bl a b ↔ blockNode (unrooted N hN hX) C a = blockNode (unrooted N hN hX) C b)
    {x y : X} (hx : C.ncard = 4 ∨ blockNode (unrooted N hN hX) C x = w) :
    AdjacencyTest Bl (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) x y ↔
      AdjacentBlocks (unrooted N hN hX) C x y := by
  rw [adjacentBlocks_iff_forall_joinedAvoiding h1 hC hC4 hw x y, sameBlock_iff_blockNode_eq h1 hC]
  simp only [AdjacencyTest, isBCQuartetOf_cf, hBl]
  set β := blockNode (unrooted N hN hX) C
  refine and_congr_right fun hxy => ?_
  -- four taxa in distinct blocks, one of them in the hybrid block or the cycle of size four, are
  -- separated by the cycle
  have hsep : ∀ z z', Distinct4 x y z z' → β x ≠ β z → β x ≠ β z' → β y ≠ β z → β y ≠ β z' →
      β z ≠ β z' → SeparatesQuartet (unrooted N hN hX) C w {x, y, z, z'} := by
    intro z z' h hxz hxz' hyz hyz' hzz'
    have hinj := injOn_four hxy hxz hxz' hyz hyz' hzz'
    refine (separatesQuartet_iff h1 hC hw _).2 ⟨hinj, ?_⟩
    rcases hx with h4 | hxw
    · have := hN.1.finite_vertices
      have hnodes : β '' ↑({x, y, z, z'} : Finset X) = cycleNodes (unrooted N hN hX).graph C := by
        refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
        · rintro _ ⟨m, -, rfl⟩
          exact blockNode_mem hC m
        · rw [ncard_cycleNodes hC, h4, hinj.ncard_image, Set.ncard_coe_finset,
            Distinct4.card_insert_eq h]
      obtain ⟨m, hm, hmw⟩ := hnodes ▸ hw.mem_cycleNodes
      exact ⟨m, hm, hmw⟩
    · exact ⟨x, by simp, hxw⟩
  constructor
  · intro hL z z' h4' hsep'
    have h := distinct4_of_card_insert_eq h4'
    obtain ⟨hinj, -⟩ := (separatesQuartet_iff h1 hC hw _).1 hsep'
    exact (not_isBCQuartet_iff_joinedAvoiding hN h1 hX hθ hS hC4 h hsep').1
      (hL z z' h (fun e => h.2.1 (hinj (by simp) (by simp) e))
        (fun e => h.2.2.1 (hinj (by simp) (by simp) e))
        (fun e => h.2.2.2.1 (hinj (by simp) (by simp) e))
        (fun e => h.2.2.2.2.1 (hinj (by simp) (by simp) e))
        (fun e => h.2.2.2.2.2 (hinj (by simp) (by simp) e)))
  · intro hR z z' h hxz hxz' hyz hyz' hzz'
    have hsep' := hsep z z' h hxz hxz' hyz hyz' hzz'
    exact (not_isBCQuartet_iff_joinedAvoiding hN h1 hX hθ hS hC4 h hsep').2
      (hR z z' h.card_insert_eq hsep')

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- **Adjacent blocks along a listing of the cycle**: with the nodes of `C` listed as `v 0, …, v n`
and `ι t` the index of the node of the block of `t`, the blocks of `x` and `y` are adjacent exactly
when `ι x` and `ι y` are consecutive, in one order or the other. -/
theorem adjacentBlocks_iff_index_finRotate {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}
    (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {n : ℕ}
    {v : Fin (n + 1) → SemidirectedVertex hN.1 hX} {e : Fin (n + 1) → _}
    (hcyc : IsCycleOf (unrooted N hN hX).graph (n + 1) v e) (hrange : Set.range e = C)
    {ι : X → Fin (n + 1)} (hι : ∀ t, v (ι t) = blockNode (unrooted N hN hX) C t) (x y : X) :
    AdjacentBlocks (unrooted N hN hX) C x y ↔
      ι y = finRotate (n + 1) (ι x) ∨ ι x = finRotate (n + 1) (ι y) := by
  subst hrange
  have hmem : ∀ i, v i ∈ cycleNodes (unrooted N hN hX).graph (Set.range e) := fun i => by
    rw [hcyc.cycleNodes_eq]
    exact ⟨i, rfl⟩
  have hblock : ∀ i t, t ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf
      (Set.range e) (v i) ↔ i = ι t := fun i t => by
    rw [← hcyc.injective_node.eq_iff, hι]
    exact ⟨eq_blockNode h1 hC (hmem i), by intro h; rw [h]; exact (blockNode_spec hC t).2⟩
  constructor
  · rintro ⟨f, ⟨l, rfl⟩, u, u', hj, hxu, hyu'⟩
    rcases hcyc.eq_or_eq_of_joins hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hblock] at hxu hyu'
      rw [← hxu, ← hyu']
      exact Or.inl rfl
    · rw [hblock] at hxu hyu'
      rw [← hxu, ← hyu']
      exact Or.inr rfl
  · rintro (h | h)
    · refine ⟨e (ι x), ⟨_, rfl⟩, v (ι x), v (ι y), ?_, (hblock _ _).2 rfl, (hblock _ _).2 rfl⟩
      rw [h]
      exact hcyc.joins (ι x)
    · refine ⟨e (ι y), ⟨_, rfl⟩, v (ι x), v (ι y), ?_, (hblock _ _).2 rfl, (hblock _ _).2 rfl⟩
      rw [h]
      exact Or.symm (hcyc.joins (ι y))

/-- **The test of the step of the order (Proposition 11)**: with the nodes of `C_w` listed as
`v 0 = w, v 1, …, v n`, `a` in the hybrid block, `p` in the block of `v n`, and `t`, `x` in two other
distinct blocks, `q^BC_{atpx} = at|xp` exactly when the block of `x` comes before that of `t` from
`v 1`. The blocks of `a` and `t` are joined avoiding those of `x` and `p` exactly along `v 0, …, v (ι t)`,
which avoids `x` when it comes after `t`; otherwise `x` and `p` cut the cycle between `a` and `t`. -/
theorem isBCQuartetOf_cf_iff_lt (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) (hθ : IsMetricNetwork N θ)
    (hS : ∀ s : Finset X, #s = 4 → (s ∈ bcSets N θ ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s))
    {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : 4 ≤ C.ncard)
    {w : SemidirectedVertex hN.1 hX} (hw : IsHybridNodeOf (unrooted N hN hX) C w) {n : ℕ}
    {v : Fin (n + 1) → SemidirectedVertex hN.1 hX} {e : Fin (n + 1) → _}
    (hcyc : IsCycleOf (unrooted N hN hX).graph (n + 1) v e) (hrange : Set.range e = C)
    (h0 : v 0 = w) {ι : X → Fin (n + 1)} (hι : ∀ t, v (ι t) = blockNode (unrooted N hN hX) C t)
    {a t x p : X} (h : Distinct4 a t x p) (ha : ι a = 0) (hp : ι p = Fin.last n)
    (ht0 : (ι t : ℕ) ≠ 0) (htn : (ι t : ℕ) ≠ n) (hx0 : (ι x : ℕ) ≠ 0) (hxn : (ι x : ℕ) ≠ n)
    (hxt : (ι x : ℕ) ≠ ι t) :
    IsBCQuartetOf (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) {a, x, t, p}
        (quartetTree a t x p h) ↔ (ι x : ℕ) < ι t := by
  subst hrange
  rw [isBCQuartetOf_cf]
  have hmem : ∀ i, v i ∈ cycleNodes (unrooted N hN hX).graph (Set.range e) := fun i => by
    rw [hcyc.cycleNodes_eq]
    exact ⟨i, rfl⟩
  have hblock : ∀ i s, s ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf
      (Set.range e) (v i) ↔ i = ι s := fun i s => by
    rw [← hcyc.injective_node.eq_iff, hι]
    exact ⟨eq_blockNode h1 hC (hmem i), by intro h; rw [h]; exact (blockNode_spec hC s).2⟩
  have hβ : ∀ {u u' : X}, (ι u : ℕ) ≠ ι u' →
      blockNode (unrooted N hN hX) (Set.range e) u ≠ blockNode (unrooted N hN hX) (Set.range e) u' :=
    fun hne heq => hne (by rw [← hι, ← hι] at heq; rw [hcyc.injective_node heq])
  have ha' : (ι a : ℕ) = 0 := by rw [ha, Fin.val_zero]
  have hp' : (ι p : ℕ) = n := by rw [hp, Fin.val_last]
  have htlt := (ι t).isLt
  have hsep : SeparatesQuartet (unrooted N hN hX) (Set.range e) w {a, t, x, p} :=
    (separatesQuartet_iff h1 hC hw _).2 ⟨injOn_four (hβ (by omega)) (hβ (by omega))
      (hβ (by omega)) (hβ (by omega)) (hβ (by omega)) (hβ (by omega)), a, by simp,
      by rw [← hι, ha, h0]⟩
  rw [← not_iff_not, not_isBCQuartet_iff_joinedAvoiding hN h1 hX hθ hS hC4 h hsep, not_lt]
  -- the nodes of the blocks of `x` and `p`
  have hmemF : ∀ l, v l ∈ blockNodes (unrooted N hN hX) (Set.range e) {x, p} ↔
      (l : ℕ) = ι x ∨ (l : ℕ) = n := by
    intro l
    simp only [blockNodes, Set.mem_ofPred_eq, hmem, true_and, Set.mem_insert_iff,
      Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left, hblock, Fin.ext_iff, hp']
  constructor
  · rintro ⟨u, u', hu, hu', hau, htu', hwalk⟩
    obtain ⟨i, rfl⟩ : u ∈ Set.range v := hcyc.cycleNodes_eq ▸ hu
    obtain ⟨i', rfl⟩ : u' ∈ Set.range v := hcyc.cycleNodes_eq ▸ hu'
    rw [hblock] at hau htu'
    subst hau htu'
    have key := hcyc.mem_image_Ioo_iff_of_reflTransGen ((hmemF (ι x)).2 (Or.inl rfl))
      ((hmemF (Fin.last n)).2 (Or.inr (Fin.val_last n))) hwalk
    rw [ha, hcyc.injective_node.mem_set_image, hcyc.injective_node.mem_set_image] at key
    simp only [Set.mem_Ioo, Fin.lt_def, Fin.val_zero, Fin.val_last] at key
    by_contra hlt
    have := key.2 ⟨by omega, by omega⟩
    omega
  · intro hle
    refine ⟨v (ι a), v (ι t), hmem _, hmem _, (hblock _ _).2 rfl, (hblock _ _).2 rfl, ?_⟩
    rw [ha]
    refine hcyc.reflTransGen_apply_zero (ι t) fun l hl => ?_
    rw [hmemF]
    rw [Fin.le_def] at hl
    omega

/-- **The order of the blocks from the hybrid block** (proof of Lemma 16): with the nodes of `C_w`
listed as `v 0 = w, v 1, …, v n`, `a` in the hybrid block, `q` in the block of `v 1` and `p` in that of
`v n`, the `i`-th block of the order that `IsNextBlock` builds is the block of `v i` (for `i < n`), so
the block of `y` follows that of `x` exactly when `ι y` follows `ι x`. When the blocks of
`v 0, …, v (m + 1)` are placed, the block of `v (m + 2)` passes the test of `IsNextBlock`, and a block
further on fails it at a taxon of the block of `v (m + 2)` (`isBCQuartetOf_cf_iff_lt`). -/
theorem followsBlock_iff (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) (hθ : IsMetricNetwork N θ)
    (hS : ∀ s : Finset X, #s = 4 → (s ∈ bcSets N θ ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s))
    {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : 4 ≤ C.ncard)
    {w : SemidirectedVertex hN.1 hX} (hw : IsHybridNodeOf (unrooted N hN hX) C w)
    {Bl : X → X → Prop}
    (hBl : ∀ a b, Bl a b ↔ blockNode (unrooted N hN hX) C a = blockNode (unrooted N hN hX) C b)
    {n : ℕ} {v : Fin (n + 1) → SemidirectedVertex hN.1 hX} {e : Fin (n + 1) → _}
    (hcyc : IsCycleOf (unrooted N hN hX).graph (n + 1) v e) (hrange : Set.range e = C)
    (h0 : v 0 = w) {ι : X → Fin (n + 1)} (hι : ∀ t, v (ι t) = blockNode (unrooted N hN hX) C t)
    {a p q : X} (ha : ι a = 0) (hp : ι p = Fin.last n) (hq : ι q = 1) (x y : X) :
    FollowsBlock Bl (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) (n + 1) a p q x y ↔
      ι y = finRotate (n + 1) (ι x) := by
  set R := fun q r : QuartetTree X => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r with hR
  have hk : C.ncard = n + 1 := by
    rw [← hrange, Set.ncard_range_of_injective hcyc.injective_edge, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hn : 3 ≤ n := by omega
  have hBlι : ∀ t t', Bl t t' ↔ (ι t : ℕ) = ι t' := fun t t' => by
    rw [hBl, ← hι, ← hι, hcyc.injective_node.eq_iff, Fin.val_inj]
  have hsurj : ∀ i, ∃ t, ι t = i := fun i => by
    obtain ⟨t, ht⟩ := exists_blockNode_eq h1 hC (u := v i)
      (by rw [← hrange, hcyc.cycleNodes_eq]; exact ⟨i, rfl⟩)
    exact ⟨t, hcyc.injective_node (by rw [hι, ht])⟩
  have ha' : (ι a : ℕ) = 0 := by rw [ha, Fin.val_zero]
  have hp' : (ι p : ℕ) = n := by rw [hp, Fin.val_last]
  have hq' : (ι q : ℕ) = 1 := by rw [hq, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hlt : ∀ t, (ι t : ℕ) < n + 1 := fun t => (ι t).isLt
  have hne : ∀ {t t' : X}, (ι t : ℕ) ≠ ι t' → t ≠ t' := fun h e => h (by rw [e])
  -- the step: after the blocks of `v 0, …, v (m + 1)`, the next block is that of `v (m + 2)`
  have hnext : ∀ m t, IsNextBlock Bl R a p {t | (ι t : ℕ) ≤ min (m + 1) (n - 1)} t ↔
      (ι t : ℕ) = m + 2 ∧ m + 2 < n := by
    intro m t
    have htest := fun x (h : Distinct4 a t x p) => isBCQuartetOf_cf_iff_lt hN h1 hX hθ hS hC hC4 hw
      hcyc hrange h0 hι h ha hp
    simp only [IsNextBlock, Set.mem_ofPred_eq, hBlι, hp']
    have htn := hlt t
    constructor
    · rintro ⟨ht, htp, hall⟩
      by_contra hcon
      obtain ⟨x, hx⟩ := hsurj ⟨m + 2, by omega⟩
      have hx' : (ι x : ℕ) = m + 2 := by rw [hx]
      have h : Distinct4 a t x p := ⟨hne (by omega), hne (by omega), hne (by omega),
        hne (by omega), hne (by omega), hne (by omega)⟩
      exact hall x h (by omega) (by omega) (by omega)
        ((htest x h (by omega) (by omega) (by omega) (by omega) (by omega)).2 (by omega))
    · rintro ⟨ht, hmn⟩
      refine ⟨by omega, by omega, fun x h hxF hxp hxt hbc => ?_⟩
      have := (htest x h (by omega) (by omega) (by omega) (by omega) (by omega)).1 hbc
      omega
  -- the blocks placed after `m` steps
  have hplaced : ∀ m, placedBlocks Bl R a p q m = {t | (ι t : ℕ) ≤ min (m + 1) (n - 1)} := by
    intro m
    induction m with
    | zero =>
      ext t
      simp only [placedBlocks, Set.mem_ofPred_eq, hBlι, ha', hq']
      omega
    | succ m ih =>
      ext t
      simp only [placedBlocks, ih, Set.mem_union, Set.mem_ofPred_eq, hnext]
      omega
  have hat : ∀ i t, IsInBlockAt Bl R a p q i t ↔ (ι t : ℕ) = i ∧ i < n := by
    intro i t
    match i with
    | 0 =>
      simp only [IsInBlockAt, hBlι, ha']
      omega
    | 1 =>
      simp only [IsInBlockAt, hBlι, hq']
      omega
    | m + 2 => simp only [IsInBlockAt, hplaced, hnext]
  have hrot : ι y = finRotate (n + 1) (ι x) ↔
      (ι y : ℕ) = if (ι x : ℕ) = n then 0 else (ι x : ℕ) + 1 := by
    rw [Fin.ext_iff, coe_finRotate]
    by_cases hx : (ι x : ℕ) = n
    · rw [ite_eq_left (Fin.ext (by rw [hx, Fin.val_last])), ite_eq_left hx]
    · rw [ite_eq_right (fun h => hx (by rw [h, Fin.val_last])), ite_eq_right hx]
  rw [hrot]
  simp only [FollowsBlock, hat, hBlι, ha', hp']
  have hxl := hlt x
  have hyl := hlt y
  constructor
  · rintro (⟨i, ⟨hxi, hi⟩, hyi, -⟩ | ⟨⟨hx, -⟩, hy⟩ | ⟨hx, hy⟩)
    · rw [ite_eq_right (by omega)]
      omega
    · rw [ite_eq_right (by omega)]
      omega
    · rw [ite_eq_left (by omega)]
      omega
  · intro h
    split_ifs at h with hx
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · by_cases hxn : (ι x : ℕ) + 1 < n
      · exact Or.inl ⟨ι x, ⟨rfl, by omega⟩, by omega, hxn⟩
      · exact Or.inr (Or.inl ⟨⟨by omega, by omega⟩, by omega⟩)

end Comparisons

/-- **The adjacent blocks of a cycle from the comparisons of concordance factors** (Lemma 16 at given
parameters): for metric parameters at which the statement of Lemma 12 holds, `s ∈ S` determining
the hybrid node `w` of the cycle `C_w` of `N⁻`, and functions `B`, `K`, `H` of `S` and `s` giving the
blocks, the size and the hybrid block of `C_w` (the conclusion of Lemma 15), `adjacencyOf B K H`
applied to the comparisons of the concordance factors of quartet trees on the same four taxa gives
the adjacent blocks of `C_w`.

For `C_w` of size four, the sets of four taxa in distinct blocks are the sets that `C_w` separates,
and Proposition 11 gives the adjacent blocks (`adjacencyTest_iff`). For a larger cycle, with the nodes
of `C_w` listed as `v 0 = w, v 1, …, v n`, the test of Proposition 11 with a taxon `a` of the hybrid
block gives the two blocks adjacent to it, those of `v 1` and `v n`; listing the cycle the other way
if needed, `q` is in the block of `v 1` and `p` in that of `v n`, and the order that `IsNextBlock`
builds is that of `v 0, v 1, …, v n` (`followsBlock_iff`). -/
theorem lemma16_core {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X)
    {θ : MetricData E} (hθ : IsMetricNetwork N θ)
    (h12 : ∀ s : Finset X, #s = 4 → (BigCycleOn (cf N θ) s ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s))
    {s : Finset X} (hs : s ∈ bcSets N θ) {C : Set _} {w : SemidirectedVertex hN.1 hX}
    (hC : IsCycle (unrooted N hN hX).graph C) (hw : IsHybridNodeOf (unrooted N hN hX) C w)
    (hdet : Determines hN s hs.1 w.1.1) {B : Set (Finset X) → Finset X → X → X → Prop}
    {K : Set (Finset X) → Finset X → ℕ} {H : Set (Finset X) → Finset X → Set X}
    (hB : ∀ x y, B (bcSets N θ) s x y ↔
      SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y)
    (hK : K (bcSets N θ) s = C.ncard)
    (hH : 5 ≤ C.ncard → H (bcSets N θ) s = {x | DescendsFrom (unrooted N hN hX) w x}) (x y : X) :
    adjacencyOf B K H (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) s x y ↔
      AdjacentBlocks (unrooted N hN hX) C x y := by
  simp only [adjacencyOf, bcSetsOf_cf]
  -- `s` is separated by `C_w`
  obtain ⟨C', hsep⟩ := (determines_iff_separatesQuartet hN h1 hX hs.1 w).1 hdet
  rw [← hw.cycle_eq h1 hC hsep.1 hsep.2.1] at hsep
  have hC4 := four_le_ncard_of_separatesQuartet h1 hC hw hs.1 hsep
  have hS := mem_bcSets_iff_of_lemma12 h12
  have hBβ : ∀ a b, B (bcSets N θ) s a b ↔
      blockNode (unrooted N hN hX) C a = blockNode (unrooted N hN hX) C b :=
    fun a b => (hB a b).trans (sameBlock_iff_blockNode_eq h1 hC a b)
  rw [hK]
  rcases hC4.eq_or_lt with h4 | h5
  · -- `k_v = 4`: Proposition 11
    simp only [← h4, true_and, ne_eq, not_true_eq_false, false_and, or_false]
    exact adjacencyTest_iff hN h1 hX hθ hS hC hC4 hw hBβ (Or.inl h4.symm)
  -- `k_v ≥ 5`: the nodes `v 0 = w, v 1, …, v n` of `C_w`, and the index `ι t` of the block of `t`
  have h5' : C.ncard ≠ 4 := by omega
  simp only [h5', false_and, false_or, ne_eq, not_false_eq_true, true_and]
  rw [hH h5]
  obtain ⟨n, v, e, hcyc, hrange, h0⟩ := hC.exists_isCycleOf_apply_zero hw.mem_cycleNodes
  have hk : C.ncard = n + 1 := by
    rw [← hrange, Set.ncard_range_of_injective hcyc.injective_edge, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [hk]
  have hι' : ∀ t, ∃ i, v i = blockNode (unrooted N hN hX) C t := fun t => by
    have : blockNode (unrooted N hN hX) C t ∈ Set.range v := by
      rw [← hcyc.cycleNodes_eq, hrange]
      exact blockNode_mem hC t
    exact this
  choose ι hι using hι'
  have hsurj : ∀ i, ∃ t, ι t = i := fun i => by
    obtain ⟨t, ht⟩ := exists_blockNode_eq h1 hC (u := v i)
      (by rw [← hrange, hcyc.cycleNodes_eq]; exact ⟨i, rfl⟩)
    exact ⟨t, hcyc.injective_node (by rw [hι, ht])⟩
  have hH' : ∀ a, a ∈ {x | DescendsFrom (unrooted N hN hX) w x} ↔ ι a = 0 := fun a => by
    rw [Set.mem_ofPred_eq, ← blockNode_eq_iff_descendsFrom h1 hC hw, ← hι, ← h0,
      hcyc.injective_node.eq_iff]
  -- the blocks adjacent to the hybrid block (Proposition 11)
  have htest : ∀ a p, ι a = 0 → (AdjacencyTest (B (bcSets N θ) s)
      (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) a p ↔ ι p = 1 ∨ ι p = Fin.last n) := by
    intro a p ha
    rw [adjacencyTest_iff hN h1 hX hθ hS hC hC4 hw hBβ (Or.inr (by rw [← hι, ha, h0])),
      adjacentBlocks_iff_index_finRotate h1 hC hcyc hrange hι, ha, finRotate_apply_zero, eq_comm (a := 0),
      (finRotate (n + 1)).injective.eq_iff' (finRotate_last (n := n))]
  have hpq : ∀ p q, ¬ B (bcSets N θ) s p q ↔ ι p ≠ ι q := fun p q => by
    rw [hBβ, ← hι, ← hι, hcyc.injective_node.eq_iff]
  constructor
  · rintro ⟨a, ha, p, q, hap, haq, hBpq, hfol⟩
    rw [hH'] at ha
    rw [htest a p ha] at hap
    rw [htest a q ha] at haq
    rw [hpq] at hBpq
    rw [adjacentBlocks_iff_index_finRotate h1 hC hcyc hrange hι]
    rcases haq with hq | hq <;> rcases hap with hp | hp
    · exact absurd (hp.trans hq.symm) hBpq
    · -- `q` in the block of `v 1`, `p` in that of `v n`
      rwa [followsBlock_iff hN h1 hX hθ hS hC hC4 hw hBβ hcyc hrange h0 hι ha hp hq,
        followsBlock_iff hN h1 hX hθ hS hC hC4 hw hBβ hcyc hrange h0 hι ha hp hq] at hfol
    · -- `q` in the block of `v n`, `p` in that of `v 1`: the cycle listed the other way
      have hrange' : Set.range (fun i : Fin (n + 1) => e (-i - 1)) = C := by
        rw [← hrange]
        exact Function.Surjective.range_comp (fun j => ⟨-(j + 1), by simp⟩) e
      have hι'' : ∀ t, v (-(-ι t)) = blockNode (unrooted N hN hX) C t := fun t => by
        rw [neg_neg, hι]
      have hfr := fun x y => followsBlock_iff (ι := fun t => -ι t) hN h1 hX hθ hS hC hC4 hw hBβ
        hcyc.reverse hrange' (show v (-0) = w by rw [neg_zero, h0]) hι''
        (show -ι a = 0 by rw [ha, neg_zero]) (show -ι p = Fin.last n by
          rw [hp, ← Fin.neg_last, neg_neg]) (show -ι q = 1 by rw [hq, Fin.neg_last]) x y
      rw [hfr, hfr] at hfol
      simp only [finRotate_apply] at hfol ⊢
      rcases hfol with h | h
      · refine Or.inr ?_
        calc ι x = -(-ι x + 1) + 1 := by abel
          _ = ι y + 1 := by rw [← h, neg_neg]
      · refine Or.inl ?_
        calc ι y = -(-ι y + 1) + 1 := by abel
          _ = ι x + 1 := by rw [← h, neg_neg]
    · exact absurd (hp.trans hq.symm) hBpq
  · intro hadj
    obtain ⟨a, ha⟩ := hsurj 0
    obtain ⟨p, hp⟩ := hsurj (Fin.last n)
    obtain ⟨q, hq⟩ := hsurj 1
    refine ⟨a, (hH' a).2 ha, p, q, (htest a p ha).2 (Or.inr hp), (htest a q ha).2 (Or.inl hq),
      (hpq p q).2 ?_, ?_⟩
    · rw [hp, hq, Ne, Fin.ext_iff, Fin.val_last, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [followsBlock_iff hN h1 hX hθ hS hC hC4 hw hBβ hcyc hrange h0 hι ha hp hq,
        followsBlock_iff hN h1 hX hθ hS hC hC4 hw hBβ hcyc hrange h0 hι ha hp hq]
      exact (adjacentBlocks_iff_index_finRotate h1 hC hcyc hrange hι x y).1 hadj

end Banos2019
