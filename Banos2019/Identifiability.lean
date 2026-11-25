module

public import Banos2019.Identify.Generic
public import Banos2019.Identify.QuartetCycles

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

/-- `Y_a` (proof of Lemma 14): the taxa other than `a` of the sets of `S` that contain `a`. -/
def complementBlock (S : Set (Finset X)) (a : X) : Set X :=
  ⋃ s ∈ {s | s ∈ S ∧ a ∈ s}, ↑(s.erase a)

/-- **Lemma 14** (`netblo`): for generic parameters, the 4-network blocks of a level-1 network are
determined by `S`.

The proof is the paper's: the 4-network block of `a` is the complement of `Y_a`. A set of four taxa with
the Big Cycle property is separated by a cycle of size at least four (Lemma 12), so its taxa are in
distinct 4-network blocks. Conversely, a taxon `b` outside the 4-network block of `a` is in another
block than `a` of some cycle `C_v` of size at least four (Lemma 4); with taxa `c`, `d` of two other
blocks, one of the four in the hybrid block, `{a, b, c, d}` has the Big Cycle property (Lemma 12), and
`b ∈ Y_a`.
Departure from the paper: the paper leaves out `|X| < 3` ("nothing to prove"; there is no set of four
taxa when `|X| < 4`) and derives the case `|X| = 4` from Proposition 9, which gives only one of the two
inclusions; its argument for `|X| ≥ 5` uses no bound on `|X|`, and the proof applies it to every `X`. -/
theorem lemma14 (hX : Nontrivial X) :
    ∃ F : Set (Finset X) → X → X → Prop,
      ∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X)
        (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph →
        ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ x y,
          (F (bcSets N θ) x y ↔
            SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf
              (bigCycleEdges (unrooted N hN hX)) x y) := by
  refine ⟨fun S x y => y ∉ complementBlock S x, ?_⟩
  intro V E _ _ N hN h1
  refine (lemma12 hN h1 hX).imp fun θ h12 hθ x y => ?_
  have h12 := h12 hθ
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
    refine hy (Set.mem_biUnion (x := {x, y, c, d}) ⟨⟨h4, (h12 _ h4).2 ⟨C, v, hC4, hsep⟩⟩, by simp⟩ ?_)
    simp [hxy]
  · -- the taxa of a set of `S` are in distinct 4-network blocks
    intro hsb hy
    obtain ⟨s, ⟨hsS, hxs⟩, hys⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨hyx, hys⟩ := mem_erase.1 hys
    obtain ⟨C, v, hC4, hsep⟩ := (h12 s hsS.1).1 hsS.2
    exact hsep.2.2.1 x hxs y hys (Ne.symm hyx)
      (hsb.mono (Set.subset_sUnion_of_mem (show C ∈ cyclesOfSizeAtLeast _ 4 from ⟨hsep.1, hC4⟩)))

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

end Determined

/-- **Lemma 15** (`blov`): for generic parameters, for every set `s ∈ S`, the blocks of the cycle `C_v`
of `N⁻` whose hybrid node `v` it determines and the size `k_v` of the cycle are determined by `S`, and so
is the hybrid block when `k_v ≥ 5`.

The proof is the paper's. The taxa of `s` are in four distinct blocks of `C_v`, one in the hybrid block
(Lemma 12), and a set of `S` sharing three taxa with `s` determines `v` too (Lemma 13), so it is a set of
four taxa that `C_v` separates: `Z_{s ∖ {t}}` is the union of the blocks other than those of `s ∖ {t}`,
or the hybrid block when `t` is the taxon `a` of `s` in it (`mem_extensions_iff`). When `k_v = 4`, the
four sets `Z_{s ∖ {t}}` are the four blocks; when `k_v ≥ 5`, those for `t ≠ a` meet, and `Z_{s ∖ {a}}`
is the hybrid block. The other blocks come from the sets `{y} ∪ s ∖ {g}` and, for the taxa outside the
blocks of `s`, from the same steps applied to `T ∪ {x}` (`SameBlockFive`). -/
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
  refine ⟨blockRelation, blockCount, hybridBlock, ?_⟩
  intro V E _ _ N hN h1
  refine (lemma12 hN h1 hX).imp fun θ h12 hθ s hs C w hC hw hdet => ?_
  have hS : ∀ s : Finset X, #s = 4 → (s ∈ bcSets N θ ↔
      ∃ C v, 4 ≤ C.ncard ∧ SeparatesQuartet (unrooted N hN hX) C v s) :=
    fun s h4 => ⟨fun h => (h12 hθ s h4).1 h.2, fun h => ⟨h4, (h12 hθ s h4).2 h⟩⟩
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

/-- **Lemma 16** (`orderofcycles`): for generic parameters, the order of the blocks around each cycle
`C_v` of size at least four (which blocks are adjacent) is determined by the orderings of the
concordance factors: the function `A` sees only how the concordance factors of quartet trees on the same
four taxa compare (Definition 15). -/
theorem lemma16 (hX : Nontrivial X) :
    ∃ A : (QuartetTree X → QuartetTree X → Prop) → Finset X → X → X → Prop,
      ∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X)
        (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph →
        ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ s (hs : s ∈ bcSets N θ),
          ∀ C w, IsCycle (unrooted N hN hX).graph C → IsHybridNodeOf (unrooted N hN hX) C w →
            Determines hN s hs.1 w.1.1 → ∀ x y,
              (A (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) s x y ↔
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
node.

The paper's proof: by Proposition 8, `Q⁻_s` has a `3₂`-cycle, so three taxa of `s` are in distinct
blocks of a cycle `C_v` of `N⁻`; no extension of three of them satisfies the Big Cycle property, so
`C_v` has size less than four; and by Proposition 7, `C_v` has size three with two taxa of `s` below `v`.
Departure from the paper: Proposition 8 gives a `3₂`-cycle or a 4-cycle, and only for generic parameters
does the failure of the Big Cycle property exclude the 4-cycle (Theorem 3): that is Corollary 4, which
the proof uses. A fourth block of `C_v` would give, with a taxon of `s` in the hybrid block and two in
other blocks, a set of four taxa with the Big Cycle property (Lemma 12). The two taxa below `v` come from
the type `3₂` of the cycle, and Proposition 7 (where the concordance factors lie) is not needed. -/
theorem proposition12 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) :
    ForGenericParams N fun θ => IsMetricNetwork N θ → CyclePropertyOn (cf N θ) s →
      ¬ BigCycleOn (cf N θ) s →
      (¬ ∃ t ⊆ s, #t = 3 ∧ ∃ e ∉ t, BigCycleOn (cf N θ) (insert e t)) →
      ∃ C v, IsCycle (unrooted N hN hX).graph C ∧ C.ncard = 3 ∧
        IsHybridNodeOf (unrooted N hN hX) C v ∧
        2 ≤ {x | DescendsFrom (unrooted N hN hX) v x}.ncard := by
  refine ((corollary4 hN h1 hs).and (lemma12 hN h1 hX)).imp ?_
  rintro θ ⟨h4, h12⟩ hθ hcp hbc hno
  -- the `3₂`-cycle of `Q⁻_s` and the cycle `C_v` of `N⁻` it comes from
  obtain ⟨C, v, hC, hv, p, hp, q, hq, r, hr, t, ht, hpq, hdp, hdq, hpr, hpt, hrt⟩ :=
    exists_cycle_of_hasThreeTwoCycle hN h1 hX hs (h4 hθ (by convert hcp) (by convert hbc))
  have hβp := (blockNode_eq_iff_descendsFrom h1 hC hv p).2 hdp
  rw [sameBlock_iff_blockNode_eq h1 hC] at hpr hpt hrt
  set β := blockNode (unrooted N hN hX) C
  have hsub : ({β p, β r, β t} : Set _) ⊆ cycleNodes (unrooted N hN hX).graph C := by
    rintro u (rfl | rfl | rfl) <;> exact blockNode_mem hC _
  have h3 : ({β p, β r, β t} : Set _).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨_, _, _, hpr, hpt, hrt, rfl⟩
  refine ⟨C, v, hC, le_antisymm ?_ ?_, hv, ?_⟩
  · -- a fourth block would give a set of four taxa with the Big Cycle property (Lemma 12)
    by_contra hlt
    obtain ⟨u, hu, hun⟩ :=
      hC.exists_mem_cycleNodes_notMem (Set.toFinite {β p, β r, β t}) (by omega)
    obtain ⟨e, rfl⟩ := exists_blockNode_eq h1 hC hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hun
    obtain ⟨hep, her, het⟩ := hun
    have hne : ∀ {a b : X}, β a ≠ β b → a ≠ b := fun h h' => h (h' ▸ rfl)
    refine hno ⟨{p, r, t}, ?_, card_eq_three.2 ⟨p, r, t, hne hpr, hne hpt, hne hrt, rfl⟩, e, ?_, ?_⟩
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hne hep, hne her, hne het⟩
    · have h4' := card_four_of_ne (hne hep) (hne her) (hne het) (hne hpr) (hne hpt) (hne hrt)
      convert (h12 hθ _ h4').2 ⟨C, v, by omega, (separatesQuartet_iff h1 hC hv _).2
        ⟨injOn_four hep her het hpr hpt hrt, p, by simp, hβp⟩⟩
  · -- three taxa of `s` in distinct blocks
    rw [← ncard_cycleNodes hC, ← h3]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  · -- two taxa descend from the hybrid node
    rw [← Set.ncard_pair hpq]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro x (rfl | rfl)
    · exact hdp
    · exact hdq

/-- No cycle of `G` other than `C` has three taxa of `T` in pairwise distinct blocks. -/
def OnlyCycleSeparatingThree {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E')
    (T : Finset X') : Prop :=
  ∀ C', IsCycle G.graph C' → C' ≠ C → ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T, x ≠ y → x ≠ z → y ≠ z →
    SameBlock G.graph G.leaf C' x y ∨ SameBlock G.graph G.leaf C' x z ∨
      SameBlock G.graph G.leaf C' y z

/-- **Proposition 13** (`lem::cpto4c`), corrected: let `C_v` be a 4-cycle of `N⁻` and `a, b, c, d` taxa
in distinct `v`-blocks. For generic parameters, if for distinct `i, j, k ∈ {a, b, c, d}` some taxon `e`
makes `{i, j, k, e}` satisfy the Cycle property but not the Big Cycle property, and no cycle of `N⁻`
other than `C_v` has three of `i, j, k, e` in distinct blocks, then `e` is in the `v`-hybrid block.

The paper states this without the last hypothesis, and its proof asserts that the 4-cycle of `Q⁻_abcd`
and the `3₂`-cycle of `Q⁻_abce` "have to have the same hybrid edges, otherwise the level-1 condition
would be violated". The `3₂`-cycle can come from another cycle of `N⁻`, and then the conclusion fails:
`proposition13_asPrinted_false`.

The proof is the paper's. Say `l` is the fourth of `a, b, c, d`. The taxon `e` is not in the block of
`l`, or `i, j, k, e` would be in the four blocks of `C_v`, one of them the hybrid block, and would
satisfy the Big Cycle property (Lemma 12); so `e` is in the block of one of `i, j, k`, say `g`. By
Corollary 4, `Q⁻_ijke` has a `3₂`-cycle, which comes from a cycle of `N⁻` with three of `i, j, k, e` in
distinct blocks: by the added hypothesis, from `C_v`. Its two taxa below the hybrid node are in the
hybrid block of `C_v`, and the only two of `i, j, k, e` in one block are `g` and `e`.
Departure from the paper: the step that the two cycles have the same hybrid edges is replaced by the
added hypothesis, as above; the paper also fixes the order of the cycle by Theorem 4 and the hybrid
node of `{e, j, k, l}` by Lemma 13 before that step, which the corrected argument does not use. -/
theorem proposition13 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _} {v : SemidirectedVertex hN.1 hX}
    (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : C.ncard = 4)
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) {a b c d : X}
    (hblocks : ∀ x ∈ ({a, b, c, d} : Finset X), ∀ y ∈ ({a, b, c, d} : Finset X), x ≠ y →
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) :
    ForGenericParams N fun θ => IsMetricNetwork N θ →
      ∀ i ∈ ({a, b, c, d} : Finset X), ∀ j ∈ ({a, b, c, d} : Finset X),
        ∀ k ∈ ({a, b, c, d} : Finset X), i ≠ j → i ≠ k → j ≠ k → ∀ e,
          #({i, j, k, e} : Finset X) = 4 →
          OnlyCycleSeparatingThree (unrooted N hN hX) C {i, j, k, e} →
          CyclePropertyOn (cf N θ) {i, j, k, e} →
          ¬ BigCycleOn (cf N θ) {i, j, k, e} → DescendsFrom (unrooted N hN hX) v e := by
  refine ((ForGenericParams.forall (ι := {s : Finset X // #s = 4})
    fun s => corollary4 hN h1 s.2).and (lemma12 hN h1 hX)).imp ?_
  rintro θ ⟨h4, h12⟩ hθ i hi j hj k hk hij hik hjk e he4 honly hcp hbc
  set β := blockNode (unrooted N hN hX) C
  have hβ : ∀ x ∈ ({a, b, c, d} : Finset X), ∀ y ∈ ({a, b, c, d} : Finset X), x ≠ y → β x ≠ β y :=
    fun x hx y hy hxy => (sameBlock_iff_blockNode_eq h1 hC x y).not.1 (hblocks x hx y hy hxy)
  have hβij := hβ i hi j hj hij
  have hβik := hβ i hi k hk hik
  have hβjk := hβ j hj k hk hjk
  -- the blocks of `i, j, k` and a fourth block: the four blocks of `C_v`
  have hsub : ({β i, β j, β k} : Set _) ⊆ cycleNodes (unrooted N hN hX).graph C := by
    rintro u (rfl | rfl | rfl) <;> exact blockNode_mem hC _
  have h3 : ({β i, β j, β k} : Set _).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨_, _, _, hβij, hβik, hβjk, rfl⟩
  obtain ⟨u₄, hu₄, hu₄ijk⟩ :=
    hC.exists_mem_cycleNodes_notMem (Set.toFinite {β i, β j, β k}) (by omega)
  have hnodes : cycleNodes (unrooted N hN hX).graph C = insert u₄ {β i, β j, β k} := by
    refine (Set.eq_of_subset_of_ncard_le (Set.insert_subset hu₄ hsub) ?_ (Set.toFinite _)).symm
    rw [ncard_cycleNodes hC, hC4, Set.ncard_insert_of_notMem hu₄ijk, h3]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu₄ijk
  obtain ⟨hu₄i, hu₄j, hu₄k⟩ := hu₄ijk
  -- `e` is not in the fourth block: otherwise `{i, j, k, e}` would satisfy the Big Cycle property
  have he₄ : β e ≠ u₄ := by
    intro h
    apply hbc
    have hv' := hv.mem_cycleNodes
    rw [hnodes] at hv'
    convert (h12 hθ _ he4).2 ⟨C, v, by omega, (separatesQuartet_iff h1 hC hv _).2
      ⟨injOn_four hβij hβik (fun h' => hu₄i (h.symm.trans h'.symm)) hβjk
        (fun h' => hu₄j (h.symm.trans h'.symm)) (fun h' => hu₄k (h.symm.trans h'.symm)), ?_⟩⟩
    rcases hv' with h' | h' | h' | h'
    · exact ⟨e, by simp, h.trans h'.symm⟩
    · exact ⟨i, by simp, h'.symm⟩
    · exact ⟨j, by simp, h'.symm⟩
    · exact ⟨k, by simp, h'.symm⟩
  -- so `e` is in the block of one of `i, j, k`
  obtain ⟨g, hg, hge⟩ : ∃ g ∈ ({i, j, k} : Finset X), β g = β e := by
    have he' := blockNode_mem hC e
    rw [hnodes] at he'
    rcases he' with h' | h' | h' | h'
    · exact absurd h' he₄
    · exact ⟨i, by simp, h'.symm⟩
    · exact ⟨j, by simp, h'.symm⟩
    · exact ⟨k, by simp, h'.symm⟩
  -- by Corollary 4, `Q⁻_ijke` has a `3₂`-cycle; it comes from `C_v`
  obtain ⟨C', w, hC', hw, p, hp, q, hq, r, hr, t, ht, hpq, hdp, hdq, hpr, hpt, hrt⟩ :=
    exists_cycle_of_hasThreeTwoCycle hN h1 hX he4
      (h4 ⟨_, he4⟩ hθ (by convert hcp) (by convert hbc))
  have hCC' : C' = C := by
    by_contra hCC'
    have hsb : ∀ {x y : X}, ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C' x y →
        x ≠ y := fun h h' => h (h' ▸ .refl)
    rcases honly C' hC' hCC' p hp r hr t ht (hsb hpr) (hsb hpt) (hsb hrt) with h | h | h
    · exact hpr h
    · exact hpt h
    · exact hrt h
  subst hCC'
  have hwv : w = v := hw.eq h1 hC' hv
  subst hwv
  -- its two taxa below the hybrid node are `g` and `e`
  have hβp := (blockNode_eq_iff_descendsFrom h1 hC' hw p).2 hdp
  have hβq := (blockNode_eq_iff_descendsFrom h1 hC' hw q).2 hdq
  have hpair : ∀ x ∈ ({i, j, k, e} : Finset X), ∀ y ∈ ({i, j, k, e} : Finset X), x ≠ y →
      β x = β y → x = e ∨ y = e := by
    intro x hx y hy hxy hβxy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
        | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hxy
        | exact absurd hβxy ‹_› | exact absurd hβxy.symm ‹_›
  rcases hpair p hp q hq hpq (hβp.trans hβq.symm) with rfl | rfl
  · exact hdp
  · exact hdq

/-- **Proposition 13 as printed**: for every binary level-1 network, 4-cycle `C_v` of `N⁻`, and taxa
`a, b, c, d` in distinct `v`-blocks, for generic parameters, if `{i, j, k, e}` with distinct
`i, j, k ∈ {a, b, c, d}` satisfies the Cycle property but not the Big Cycle property, then `e` is in the
`v`-hybrid block. -/
def Proposition13AsPrinted : Prop :=
  ∀ (V E X : Type) [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
    (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph → ∀ (hX : Nontrivial X) (C : Set _)
    (v : SemidirectedVertex hN.1 hX), IsCycle (unrooted N hN hX).graph C → C.ncard = 4 →
    IsHybridNodeOf (unrooted N hN hX) C v → ∀ a b c d : X,
    (∀ x ∈ ({a, b, c, d} : Finset X), ∀ y ∈ ({a, b, c, d} : Finset X), x ≠ y →
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) →
    ForGenericParams N fun θ => IsMetricNetwork N θ →
      ∀ i ∈ ({a, b, c, d} : Finset X), ∀ j ∈ ({a, b, c, d} : Finset X),
        ∀ k ∈ ({a, b, c, d} : Finset X), i ≠ j → i ≠ k → j ≠ k → ∀ e,
          #({i, j, k, e} : Finset X) = 4 → CyclePropertyOn (cf N θ) {i, j, k, e} →
          ¬ BigCycleOn (cf N θ) {i, j, k, e} → DescendsFrom (unrooted N hN hX) v e

/-- **Proposition 13 as printed is false.** In the network with edges `r → a`, `r → t`, `t → p`,
`t → u`, `p → e`, `p → u`, `u → w`, `w → x`, `w → y`, `x → b`, `x → v`, `y → c`, `y → v`, `v → d`,
`C_v = {wx, xv, wy, yv}` is a 4-cycle of `N⁻` with blocks `{a, e}`, `{b}`, `{c}`, `{d}` and hybrid block
`{d}`. In `Q⁻_abce` the cycle `C_v` disappears and the 3-cycle `t, p, u` is a `3₂`-cycle with hybrid
block `{b, c}` (Figure 18 relabelled), so on an open set of parameters around those of Example 6,
`{a, b, c, e}` satisfies the Cycle property but not the Big Cycle property, while `e` is not in the
`v`-hybrid block. -/
theorem proposition13_asPrinted_false : ¬ Proposition13AsPrinted := by
  sorry

end Banos2019
