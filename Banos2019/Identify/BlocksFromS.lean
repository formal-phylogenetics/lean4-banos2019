module

public import Banos2019.Identify.QuartetCycles

/-!
# The blocks and the order of a cycle from `S` (Baños 2019, proofs of Lemmas 15 and 16)

For metric parameters at which the statement of Lemma 12 holds, the blocks, the size and the hybrid
block of the cycle `C_v` of `N⁻` whose hybrid node a set `s ∈ S` determines are functions of `S` and
`s` (`lemma15_core`), and, given such functions, which of its blocks are adjacent is a function of
the comparisons of the concordance factors of quartet trees on the same four taxa (`lemma16_core`).
Lemmas 15 and 16 (`Banos2019/Identifiability.lean`) are these statements for generic parameters.

* `bcSets`: the set `S`.
* `extensions` (`Z_T`), `blockRelation`, `blockCount`, `hybridBlock`: the constructions of the proof
  of Lemma 15 from `S`.
* `bcSetsOf`, `IsBCQuartetOf`, `adjacencyOf`: `S`, `q^BC_s` and the adjacent blocks, read from the
  comparisons of concordance factors and from the blocks, the size and the hybrid block (proof of
  Lemma 16).
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

end Comparisons

/-- The adjacent blocks of the cycle determined by `s`, read from the comparisons `R` and from the
blocks `B`, the size `K` and the hybrid block `H` given by `S` (proof of Lemma 16): `x` and `y` are in
different blocks, and `q^BC_{xyzz'} ≠ xy|zz'` for all `z, z'` such that `x, y, z, z'` are in four
distinct blocks and, when the cycle has size at least five, one of them is the hybrid block. -/
def adjacencyOf (B : Set (Finset X) → Finset X → X → X → Prop) (K : Set (Finset X) → Finset X → ℕ)
    (H : Set (Finset X) → Finset X → Set X) (R : QuartetTree X → QuartetTree X → Prop) (s : Finset X)
    (x y : X) : Prop :=
  ¬ B (bcSetsOf R) s x y ∧ ∀ z z' (h : Distinct4 x y z z'),
    ¬ B (bcSetsOf R) s x z → ¬ B (bcSetsOf R) s x z' → ¬ B (bcSetsOf R) s y z →
    ¬ B (bcSetsOf R) s y z' → ¬ B (bcSetsOf R) s z z' →
    (K (bcSetsOf R) s = 4 ∨ x ∈ H (bcSetsOf R) s ∨ y ∈ H (bcSetsOf R) s ∨
      z ∈ H (bcSetsOf R) s ∨ z' ∈ H (bcSetsOf R) s) →
    ¬ IsBCQuartetOf R {x, z, y, z'} (quartetTree x y z z' h)

/-- **The adjacent blocks of a cycle from the comparisons of concordance factors** (Lemma 16 at given
parameters): for metric parameters at which the statement of Lemma 12 holds, `s ∈ S` determining
the hybrid node `w` of the cycle `C_w` of `N⁻`, and functions `B`, `K`, `H` of `S` and `s` giving the
blocks, the size and the hybrid block of `C_w` (the conclusion of Lemma 15), `adjacencyOf B K H`
applied to the comparisons of the concordance factors of quartet trees on the same four taxa gives
the adjacent blocks of `C_w`. -/
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
  simp only [adjacencyOf, bcSetsOf_cf, isBCQuartetOf_cf]
  -- `s` is separated by `C_w`
  obtain ⟨C', hsep⟩ := (determines_iff_separatesQuartet hN h1 hX hs.1 w).1 hdet
  rw [← hw.cycle_eq h1 hC hsep.1 hsep.2.1] at hsep
  have hC4 := four_le_ncard_of_separatesQuartet h1 hC hw hs.1 hsep
  set β := blockNode (unrooted N hN hX) C
  have hBβ : ∀ a b, B (bcSets N θ) s a b ↔ β a = β b :=
    fun a b => (hB a b).trans (sameBlock_iff_blockNode_eq h1 hC a b)
  rw [adjacentBlocks_iff_forall_joinedAvoiding h1 hC hC4 hw x y, ← hB x y]
  refine and_congr_right fun hxy => forall₂_congr fun z z' => ?_
  rw [hBβ] at hxy
  -- the sets of four taxa that `C_w` separates, from the blocks and the hybrid block
  have hsepiff : ∀ h : Distinct4 x y z z',
      ((¬ B (bcSets N θ) s x z ∧ ¬ B (bcSets N θ) s x z' ∧ ¬ B (bcSets N θ) s y z ∧
        ¬ B (bcSets N θ) s y z' ∧ ¬ B (bcSets N θ) s z z') ∧
        (K (bcSets N θ) s = 4 ∨ x ∈ H (bcSets N θ) s ∨ y ∈ H (bcSets N θ) s ∨
          z ∈ H (bcSets N θ) s ∨ z' ∈ H (bcSets N θ) s)) ↔
      SeparatesQuartet (unrooted N hN hX) C w {x, y, z, z'} := by
    intro h
    simp only [hBβ]
    rw [separatesQuartet_iff h1 hC hw]
    have := hN.1.finite_vertices
    by_cases h4 : C.ncard = 4
    · -- four blocks on a 4-cycle: one of them is the hybrid block
      refine ⟨fun ⟨⟨hxz, hxz', hyz, hyz', hzz'⟩, _⟩ => ?_, fun ⟨hinj, _⟩ => ?_⟩
      · have hinj := injOn_four hxy hxz hxz' hyz hyz' hzz'
        have hnodes : β '' ↑({x, y, z, z'} : Finset X) =
            cycleNodes (unrooted N hN hX).graph C := by
          refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
          · rintro _ ⟨m, -, rfl⟩
            exact blockNode_mem hC m
          · rw [ncard_cycleNodes hC, h4, hinj.ncard_image, Set.ncard_coe_finset,
              Distinct4.card_insert_eq h]
        obtain ⟨m, hm, hmw⟩ := hnodes ▸ hw.mem_cycleNodes
        exact ⟨hinj, m, hm, hmw⟩
      · refine ⟨⟨fun e => h.2.1 (hinj (by simp) (by simp) e), fun e => h.2.2.1 (hinj (by simp)
          (by simp) e), fun e => h.2.2.2.1 (hinj (by simp) (by simp) e),
          fun e => h.2.2.2.2.1 (hinj (by simp) (by simp) e),
          fun e => h.2.2.2.2.2 (hinj (by simp) (by simp) e)⟩, Or.inl (hK.trans h4)⟩
    · -- at least five blocks: the hybrid block is `H S s`
      have hH5 := hH (by omega)
      have hK4 : K (bcSets N θ) s ≠ 4 := hK ▸ h4
      have hmemH : ∀ m, m ∈ H (bcSets N θ) s ↔ β m = w := fun m => by
        rw [hH5]
        exact (blockNode_eq_iff_descendsFrom h1 hC hw m).symm
      simp only [hmemH, hK4, false_or]
      constructor
      · rintro ⟨⟨hxz, hxz', hyz, hyz', hzz'⟩, hhyb⟩
        refine ⟨injOn_four hxy hxz hxz' hyz hyz' hzz', ?_⟩
        rcases hhyb with hm | hm | hm | hm
        · exact ⟨x, by simp, hm⟩
        · exact ⟨y, by simp, hm⟩
        · exact ⟨z, by simp, hm⟩
        · exact ⟨z', by simp, hm⟩
      · rintro ⟨hinj, m, hm, hmw⟩
        refine ⟨⟨fun e => h.2.1 (hinj (by simp) (by simp) e), fun e => h.2.2.1 (hinj (by simp)
          (by simp) e), fun e => h.2.2.2.1 (hinj (by simp) (by simp) e),
          fun e => h.2.2.2.2.1 (hinj (by simp) (by simp) e),
          fun e => h.2.2.2.2.2 (hinj (by simp) (by simp) e)⟩, ?_⟩
        simp only [mem_insert, mem_singleton] at hm
        rcases hm with rfl | rfl | rfl | rfl
        · exact Or.inl hmw
        · exact Or.inr (Or.inl hmw)
        · exact Or.inr (Or.inr (Or.inl hmw))
        · exact Or.inr (Or.inr (Or.inr hmw))
  -- for a set that `C_w` separates, `q^BC ≠ xy|zz'` exactly when the blocks of `x` and `y` are
  -- joined avoiding those of `z` and `z'` (Proposition 11)
  have hS := mem_bcSets_iff_of_lemma12 h12
  have hcore : ∀ h : Distinct4 x y z z', SeparatesQuartet (unrooted N hN hX) C w {x, y, z, z'} →
      (¬ IsBCQuartet (cf N θ) {x, z, y, z'} (quartetTree x y z z' h) ↔
        JoinedAvoiding (unrooted N hN hX) C {z, z'} x y) := fun h hsep' =>
    not_isBCQuartet_iff_joinedAvoiding hN h1 hX hθ hS hC4 h hsep'
  constructor
  · intro hL h4' hsep'
    have h := distinct4_of_card_insert_eq h4'
    obtain ⟨⟨hxz, hxz', hyz, hyz', hzz'⟩, hhyb⟩ := (hsepiff h).2 hsep'
    exact (hcore h hsep').1 (hL h hxz hxz' hyz hyz' hzz' hhyb)
  · intro hR h hxz hxz' hyz hyz' hzz' hhyb
    have hsep' := (hsepiff h).1 ⟨⟨hxz, hxz', hyz, hyz', hzz'⟩, hhyb⟩
    exact (hcore h hsep').2 (hR (Distinct4.card_insert_eq h) hsep')

end Banos2019
