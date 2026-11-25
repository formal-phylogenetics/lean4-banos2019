module

public import Banos2019.Quartet.Reduction
public import Banos2019.Network.Suppress

/-!
# Quartet trees on four taxa, and the quartet networks of a network

* `treesOn_eq_triple`: the three quartet trees `ab|cd`, `ac|bd`, `ad|bc` on four distinct taxa.
* `bigCycleOn_iff_triple`, `isTreelikeOn_iff_triple`, `isBCQuartet_iff_triple`: the Big Cycle
  property, treelikeness and `q^BC` in terms of the three concordance factors.
* `treesOn_eq_image`, `bigCycleOn_comp_map_iff`, `isTreelikeOn_comp_map_iff`: a set `s` of four taxa
  and the taxa `↥s` of a quartet network on `s` have the same quartet trees.
* `cf_quartetLSA`: the concordance factors of `Q⊕_s`, an LSA quartet network with the parameters it
  inherits (`quartetLSA_isLSAQuartet`), are those of `N` on `s` (Theorem 2).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-! ### The three quartet trees on four taxa -/

section Triple

variable {X : Type*} [DecidableEq X] {a b c d : X}

theorem Distinct4.card_insert_eq (h : Distinct4 a b c d) : #({a, b, c, d} : Finset X) = 4 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
    card_pair hcd]

theorem distinct4_of_card_insert_eq (h : #({a, b, c, d} : Finset X) = 4) : Distinct4 a b c d :=
  ne_of_card_four h

omit [DecidableEq X] in
/-- Four distinct taxa, listed. -/
theorem Distinct4.injective_vec (h : Distinct4 a b c d) : Function.Injective ![a, b, c, d] := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> simp_all [eq_comm]

@[simp] theorem quartetTree_val_eq_pair (h : Distinct4 a b c d) :
    (quartetTree a b c d h).val = {{a, b}, {c, d}} := rfl

theorem quartetTree_taxa_eq_insert (h : Distinct4 a b c d) :
    (quartetTree a b c d h).taxa = {a, b, c, d} := by
  ext x
  simp [QuartetTree.taxa]
  tauto

/-- `ab|cd` is `cd|ab`, `ba|cd`, … -/
theorem quartetTree_eq_of_val_eq {a' b' c' d' : X} (h : Distinct4 a b c d)
    (h' : Distinct4 a' b' c' d')
    (hv : ({{a, b}, {c, d}} : Finset (Finset X)) = {{a', b'}, {c', d'}}) :
    quartetTree a b c d h = quartetTree a' b' c' d' h' :=
  Subtype.ext hv

/-- Two quartet trees on the same four taxa are equal when they have a common cherry. -/
theorem quartetTree_eq_of_taxa_eq_of_mem {q r : QuartetTree X}
    (hqr : q.taxa = r.taxa) {B : Finset X}
    (hq : B ∈ q.val) (hr : B ∈ r.val) : q = r :=
  QuartetTree.eq_of_taxa_eq_of_mem hqr hq hr

theorem quartetTree_abcd_ne_acbd (h : Distinct4 a b c d) :
    quartetTree a b c d h ≠ quartetTree a c b d (distinct4_acbd h) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  intro e
  have h1 : ({a, b} : Finset X) ∈ (quartetTree a c b d (distinct4_acbd h)).val :=
    e ▸ (by simp)
  simp only [quartetTree_val_eq_pair, mem_insert, mem_singleton] at h1
  rcases h1 with h1 | h1
  · have : b ∈ ({a, c} : Finset X) := h1 ▸ (by simp)
    simp [Ne.symm hab, hbc] at this
  · have : a ∈ ({b, d} : Finset X) := h1 ▸ (by simp)
    simp [hab, had] at this

theorem quartetTree_abcd_ne_adbc (h : Distinct4 a b c d) :
    quartetTree a b c d h ≠ quartetTree a d b c (distinct4_adbc h) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  intro e
  have h1 : ({a, b} : Finset X) ∈ (quartetTree a d b c (distinct4_adbc h)).val :=
    e ▸ (by simp)
  simp only [quartetTree_val_eq_pair, mem_insert, mem_singleton] at h1
  rcases h1 with h1 | h1
  · have : b ∈ ({a, d} : Finset X) := h1 ▸ (by simp)
    simp [Ne.symm hab, hbd] at this
  · have : a ∈ ({b, c} : Finset X) := h1 ▸ (by simp)
    simp [hab, hac] at this

theorem quartetTree_acbd_ne_adbc (h : Distinct4 a b c d) :
    quartetTree a c b d (distinct4_acbd h) ≠ quartetTree a d b c (distinct4_adbc h) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  intro e
  have h1 : ({a, c} : Finset X) ∈ (quartetTree a d b c (distinct4_adbc h)).val :=
    e ▸ (by simp)
  simp only [quartetTree_val_eq_pair, mem_insert, mem_singleton] at h1
  rcases h1 with h1 | h1
  · have : c ∈ ({a, d} : Finset X) := h1 ▸ (by simp)
    simp [Ne.symm hac, hcd] at this
  · have : a ∈ ({b, c} : Finset X) := h1 ▸ (by simp)
    simp [hab, hac] at this

variable [Fintype X]

/-- Four taxa make up a set of four taxa. -/
theorem exists_distinct4_univ (hX : Fintype.card X = 4) :
    ∃ a b c d : X, ∃ _ : Distinct4 a b c d, ({a, b, c, d} : Finset X) = univ := by
  let e := (Fintype.equivFinOfCardEq hX).symm
  refine ⟨e 0, e 1, e 2, e 3, ⟨e.injective.ne (by decide), e.injective.ne (by decide),
    e.injective.ne (by decide), e.injective.ne (by decide), e.injective.ne (by decide),
    e.injective.ne (by decide)⟩, eq_univ_iff_forall.2 fun x => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective x
  simp only [mem_insert, mem_singleton, e.injective.eq_iff]
  fin_cases i <;> simp

/-- **The three quartet trees on four distinct taxa**: `ab|cd`, `ac|bd`, `ad|bc`. -/
theorem treesOn_eq_triple (h : Distinct4 a b c d) :
    treesOn ({a, b, c, d} : Finset X) =
      {quartetTree a b c d h, quartetTree a c b d (distinct4_acbd h),
        quartetTree a d b c (distinct4_adbc h)} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  have h4 := Distinct4.card_insert_eq h
  ext r
  simp only [mem_treesOn, mem_insert, mem_singleton]
  constructor
  · intro hr
    have har : a ∈ r.taxa := hr ▸ (by simp)
    obtain ⟨B, hB, haB⟩ : ∃ B ∈ r.val, a ∈ B := by
      simpa [QuartetTree.taxa, mem_sup] using har
    have hBq : B ⊆ {a, b, c, d} := hr ▸ r.subset_taxa hB
    have hBc := r.card_of_mem hB
    obtain ⟨x, hx⟩ : ∃ x, B.erase a = {x} :=
      card_eq_one.1 (by rw [card_erase_of_mem haB]; omega)
    have hBe : B = {a, x} := by rw [← hx, insert_erase haB]
    have hxa : x ≠ a := by
      intro hxa
      have : x ∈ B.erase a := by simp [hx]
      exact (mem_erase.1 this).1 hxa
    have hxq : x ∈ ({a, b, c, d} : Finset X) := hBq (by rw [hBe]; simp)
    simp only [mem_insert, mem_singleton] at hxq
    rcases hxq with rfl | rfl | rfl | rfl
    · exact absurd rfl hxa
    · left
      exact quartetTree_eq_of_taxa_eq_of_mem (B := {a, x}) (by rw [hr, quartetTree_taxa_eq_insert])
        (hBe ▸ hB) (by simp)
    · right; left
      exact quartetTree_eq_of_taxa_eq_of_mem (B := {a, x}) (by
        rw [hr, quartetTree_taxa_eq_insert]; ext y; simp; tauto) (hBe ▸ hB) (by simp)
    · right; right
      exact quartetTree_eq_of_taxa_eq_of_mem (B := {a, x}) (by
        rw [hr, quartetTree_taxa_eq_insert]; ext y; simp; tauto) (hBe ▸ hB) (by simp)
  · rintro (rfl | rfl | rfl)
    · exact quartetTree_taxa_eq_insert _
    · rw [quartetTree_taxa_eq_insert]; ext y; simp; tauto
    · rw [quartetTree_taxa_eq_insert]; ext y; simp; tauto

/-- The Big Cycle property on four distinct taxa: the three concordance factors differ. -/
theorem bigCycleOn_iff_triple (p : QuartetTree X → ℝ) (h : Distinct4 a b c d) :
    BigCycleOn p {a, b, c, d} ↔
      p (quartetTree a b c d h) ≠ p (quartetTree a c b d (distinct4_acbd h)) ∧
        p (quartetTree a b c d h) ≠ p (quartetTree a d b c (distinct4_adbc h)) ∧
        p (quartetTree a c b d (distinct4_acbd h)) ≠
          p (quartetTree a d b c (distinct4_adbc h)) := by
  have n1 := quartetTree_abcd_ne_acbd h
  have n2 := quartetTree_abcd_ne_adbc h
  have n3 := quartetTree_acbd_ne_adbc h
  unfold BigCycleOn
  rw [treesOn_eq_triple h]
  constructor
  · intro H
    exact ⟨H _ (by simp) _ (by simp) n1, H _ (by simp) _ (by simp) n2, H _ (by simp) _ (by simp) n3⟩
  · rintro ⟨h1, h2, h3⟩ q hq r hr hqr
    simp only [mem_insert, mem_singleton] at hq hr
    rcases hq with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
      first | exact absurd rfl hqr | assumption | exact Ne.symm ‹_›

/-- Treelikeness on four distinct taxa: the two smallest of the three concordance factors are equal.
-/
theorem isTreelikeOn_iff_triple (p : QuartetTree X → ℝ) (h : Distinct4 a b c d) :
    IsTreelikeOn p {a, b, c, d} ↔
      let x := p (quartetTree a b c d h)
      let y := p (quartetTree a c b d (distinct4_acbd h))
      let z := p (quartetTree a d b c (distinct4_adbc h))
      (y = z ∧ y ≤ x) ∨ (x = z ∧ x ≤ y) ∨ (x = y ∧ x ≤ z) := by
  have n1 := quartetTree_abcd_ne_acbd h
  have n2 := quartetTree_abcd_ne_adbc h
  have n3 := quartetTree_acbd_ne_adbc h
  unfold IsTreelikeOn
  rw [treesOn_eq_triple h]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨q, hq, r, hr, hqr, hpqr, hmin⟩
    have m1 := hmin _ (Or.inl rfl)
    have m2 := hmin _ (Or.inr (Or.inl rfl))
    have m3 := hmin _ (Or.inr (Or.inr rfl))
    rcases hq with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hqr
      | (right; right; exact ⟨hpqr, m3⟩)
      | (right; left; exact ⟨hpqr, m2⟩)
      | (left; exact ⟨hpqr, m1⟩)
      | (right; right; exact ⟨hpqr.symm, hpqr ▸ m3⟩)
      | (right; left; exact ⟨hpqr.symm, hpqr ▸ m2⟩)
      | (left; exact ⟨hpqr.symm, hpqr ▸ m1⟩)
  · rintro (⟨hyz, hyx⟩ | ⟨hxz, hxy⟩ | ⟨hxy, hxz⟩)
    · refine ⟨_, Or.inr (Or.inl rfl), _, Or.inr (Or.inr rfl), n3, hyz, ?_⟩
      rintro u (rfl | rfl | rfl)
      · exact hyx
      · exact le_rfl
      · exact hyz.le
    · refine ⟨_, Or.inl rfl, _, Or.inr (Or.inr rfl), n2, hxz, ?_⟩
      rintro u (rfl | rfl | rfl)
      · exact le_rfl
      · exact hxy
      · exact hxz.le
    · refine ⟨_, Or.inl rfl, _, Or.inr (Or.inl rfl), n1, hxy, ?_⟩
      rintro u (rfl | rfl | rfl)
      · exact le_rfl
      · exact hxy.le
      · exact hxz

/-- `q^BC = ac|bd` on four distinct taxa: the concordance factor of `ac|bd` is the smallest,
strictly. -/
theorem isBCQuartet_acbd_iff (p : QuartetTree X → ℝ) (h : Distinct4 a b c d) :
    IsBCQuartet p {a, b, c, d} (quartetTree a c b d (distinct4_acbd h)) ↔
      p (quartetTree a c b d (distinct4_acbd h)) < p (quartetTree a b c d h) ∧
        p (quartetTree a c b d (distinct4_acbd h)) <
          p (quartetTree a d b c (distinct4_adbc h)) := by
  have n1 := quartetTree_abcd_ne_acbd h
  have n3 := quartetTree_acbd_ne_adbc h
  unfold IsBCQuartet
  rw [treesOn_eq_triple h]
  simp only [mem_insert, mem_singleton, true_or, or_true, true_and]
  constructor
  · intro H
    exact ⟨H _ (Or.inl rfl) n1, H _ (Or.inr (Or.inr rfl)) n3.symm⟩
  · rintro ⟨h1, h2⟩ r (rfl | rfl | rfl) hr
    · exact h1
    · exact absurd rfl hr
    · exact h2

end Triple

/-- `q^BC` is unique. -/
theorem IsBCQuartet.unique {X : Type*} [Fintype X] [DecidableEq X] {p : QuartetTree X → ℝ}
    {s : Finset X} {q r : QuartetTree X} (hq : IsBCQuartet p s q) (hr : IsBCQuartet p s r) :
    q = r := by
  by_contra hne
  exact lt_asymm (hq.2 r hr.1 (Ne.symm hne)) (hr.2 q hq.1 hne)

/-- Treelikeness depends only on the ordering of the concordance factors. -/
theorem isTreelikeOn_of_sameOrdering {X : Type*} [Fintype X] [DecidableEq X]
    {p p' : QuartetTree X → ℝ} (h : SameOrdering p p') {s : Finset X} (ht : IsTreelikeOn p' s) :
    IsTreelikeOn p s := by
  obtain ⟨q, hq, r, hr, hqr, he, hmin⟩ := ht
  have hqt := mem_treesOn.1 hq
  have hrt := mem_treesOn.1 hr
  refine ⟨q, hq, r, hr, hqr, le_antisymm ((h q r (hqt.trans hrt.symm)).2 he.le)
    ((h r q (hrt.trans hqt.symm)).2 he.ge), fun u hu => ?_⟩
  exact (h q u (hqt.trans (mem_treesOn.1 hu).symm)).2 (hmin u hu)

/-! ### The taxa of a quartet network on `s` -/

section Subtype

variable {X : Type*} [Fintype X] [DecidableEq X] (s : Finset X) [DecidableEq (s : Set X)]

omit [DecidableEq (s : Set X)] [Fintype X] in
theorem image_val_univ_finsetCoe : (univ : Finset (s : Set X)).image Subtype.val = s := by
  ext x
  simp

/-- The quartet trees on `s` are the images of the quartet trees on all of `↥s`. -/
theorem treesOn_eq_image :
    treesOn s = (treesOn (univ : Finset (s : Set X))).image
      (QuartetTree.map Subtype.val_injective) := by
  ext q
  simp only [mem_treesOn, mem_image]
  constructor
  · intro hq
    obtain ⟨q₀, rfl⟩ := QuartetTree.exists_map_eq Subtype.val_injective q
      (by rw [hq, image_val_univ_finsetCoe])
    refine ⟨q₀, ?_, rfl⟩
    apply image_injective Subtype.val_injective
    rw [← QuartetTree.map_taxa Subtype.val_injective, hq, image_val_univ_finsetCoe]
  · rintro ⟨q₀, hq₀, rfl⟩
    rw [QuartetTree.map_taxa, hq₀, image_val_univ_finsetCoe]

theorem bigCycleOn_comp_map_iff (p : QuartetTree X → ℝ) :
    BigCycleOn (fun q => p (q.map Subtype.val_injective)) (univ : Finset (s : Set X)) ↔
      BigCycleOn p s := by
  unfold BigCycleOn
  rw [treesOn_eq_image s]
  simp only [forall_mem_image]
  refine forall₂_congr fun q _ => forall₂_congr fun r _ => ?_
  exact ⟨fun H hqr => H fun e => hqr (congrArg _ e),
    fun H hqr => H fun e => hqr (QuartetTree.map_injective Subtype.val_injective e)⟩

theorem isTreelikeOn_comp_map_iff (p : QuartetTree X → ℝ) :
    IsTreelikeOn (fun q => p (q.map Subtype.val_injective)) (univ : Finset (s : Set X)) ↔
      IsTreelikeOn p s := by
  unfold IsTreelikeOn
  rw [treesOn_eq_image s]
  simp only [exists_mem_image, forall_mem_image]
  refine exists_congr
    fun q => and_congr_right fun _ => exists_congr fun r => and_congr_right fun _ => ?_
  exact and_congr ⟨fun H e => H (QuartetTree.map_injective Subtype.val_injective e),
    fun H e => H (congrArg _ e)⟩ (and_congr_right fun _ =>
      ⟨fun H u hu => H u hu, fun H u hu => H hu⟩)

theorem isBCQuartet_comp_map_iff (p : QuartetTree X → ℝ) (q : QuartetTree (s : Set X)) :
    IsBCQuartet (fun q => p (q.map Subtype.val_injective)) (univ : Finset (s : Set X)) q ↔
      IsBCQuartet p s (q.map Subtype.val_injective) := by
  unfold IsBCQuartet
  rw [treesOn_eq_image s]
  simp only [forall_mem_image]
  refine and_congr ⟨fun h => mem_image_of_mem _ h, fun h => ?_⟩ (forall₂_congr fun r _ => ?_)
  · obtain ⟨q', hq', e⟩ := mem_image.1 h
    rwa [← QuartetTree.map_injective Subtype.val_injective e]
  · exact ⟨fun H hrq => H fun e => hrq (congrArg _ e),
      fun H hrq => H fun e => hrq (QuartetTree.map_injective Subtype.val_injective e)⟩

theorem cyclePropertyOn_comp_map_iff (p : QuartetTree X → ℝ) :
    CyclePropertyOn (fun q => p (q.map Subtype.val_injective)) (univ : Finset (s : Set X)) ↔
      CyclePropertyOn p s :=
  not_congr (isTreelikeOn_comp_map_iff s p)

end Subtype

/-! ### The concordance factors of `Q⊕_s` -/

section Induced

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

/-- The concordance factors of `Q⊕_s` are those of `N` on `s` (**Theorem 2**). -/
theorem cf_quartetLSA {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {θ : MetricData E} (hθ : IsMetricNetwork N θ) {s : Finset X}
    (hs : #s = 4) [inst : DecidableEq (s : Set X)] :
    cf (quartetLSA N hN.1 s hs) (quartetLSAMetric N hN s hs θ) =
      fun q => cf N θ (q.map Subtype.val_injective) := by
  obtain rfl : inst = fun a b => Subtype.instDecidableEq a b := Subsingleton.elim _ _
  exact funext (theorem2 hN h1 hθ hs)

end Induced

end Banos2019
