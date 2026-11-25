module

public import Banos2019.Quartet.Reduction

/-!
# Quartet trees on four taxa, and the quartet networks of a network

* `treesOn_eq_triple`: the three quartet trees `ab|cd`, `ac|bd`, `ad|bc` on four distinct taxa.
* `bigCycleOn_iff_triple`, `isTreelikeOn_iff_triple`, `isBCQuartet_iff_triple`: the Big Cycle
  property, treelikeness and `q^BC` in terms of the three concordance factors.
* `treesOn_eq_image`, `bigCycleOn_comp_map_iff`, `isTreelikeOn_comp_map_iff`: a set `s` of four taxa
  and the taxa `↥s` of a quartet network on `s` have the same quartet trees.
* `isLSAQuartet_quartetLSA`: `Q⊕_s`, with the parameters it inherits, is an LSA quartet network;
  `cf_quartetLSA`: its concordance factors are those of `N` on `s` (Theorem 2).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-! ### The three quartet trees on four taxa -/

section Triple

variable {X : Type*} [DecidableEq X] {a b c d : X}

theorem Distinct4.card_eq (h : Distinct4 a b c d) : #({a, b, c, d} : Finset X) = 4 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
    card_pair hcd]

theorem distinct4_of_card_eq (h : #({a, b, c, d} : Finset X) = 4) : Distinct4 a b c d :=
  ne_of_card_four h

@[simp] theorem quartetTree_val_eq (h : Distinct4 a b c d) :
    (quartetTree a b c d h).val = {{a, b}, {c, d}} := rfl

theorem quartetTree_taxa_eq (h : Distinct4 a b c d) :
    (quartetTree a b c d h).taxa = {a, b, c, d} := by
  ext x
  simp [QuartetTree.taxa]
  tauto

/-- `ab|cd` is `cd|ab`, `ba|cd`, … -/
theorem quartetTree_eq_of_val {a' b' c' d' : X} (h : Distinct4 a b c d) (h' : Distinct4 a' b' c' d')
    (hv : ({{a, b}, {c, d}} : Finset (Finset X)) = {{a', b'}, {c', d'}}) :
    quartetTree a b c d h = quartetTree a' b' c' d' h' :=
  Subtype.ext hv

/-- Two quartet trees on the same four taxa are equal when they have a common cherry. -/
theorem quartetTree_eq_of_mem {q r : QuartetTree X} (hqr : q.taxa = r.taxa) {B : Finset X}
    (hq : B ∈ q.val) (hr : B ∈ r.val) : q = r :=
  QuartetTree.eq_of_taxa_eq_of_mem hqr hq hr

theorem quartetTree_abcd_ne_acbd (h : Distinct4 a b c d) :
    quartetTree a b c d h ≠ quartetTree a c b d (distinct4_acbd h) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  intro e
  have h1 : ({a, b} : Finset X) ∈ (quartetTree a c b d (distinct4_acbd h)).val :=
    e ▸ (by simp)
  simp only [quartetTree_val_eq, mem_insert, mem_singleton] at h1
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
  simp only [quartetTree_val_eq, mem_insert, mem_singleton] at h1
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
  simp only [quartetTree_val_eq, mem_insert, mem_singleton] at h1
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
  have h4 := Distinct4.card_eq h
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
      exact quartetTree_eq_of_mem (B := {a, x}) (by rw [hr, quartetTree_taxa_eq]) (hBe ▸ hB) (by simp)
    · right; left
      exact quartetTree_eq_of_mem (B := {a, x}) (by
        rw [hr, quartetTree_taxa_eq]; ext y; simp; tauto) (hBe ▸ hB) (by simp)
    · right; right
      exact quartetTree_eq_of_mem (B := {a, x}) (by
        rw [hr, quartetTree_taxa_eq]; ext y; simp; tauto) (hBe ▸ hB) (by simp)
  · rintro (rfl | rfl | rfl)
    · exact quartetTree_taxa_eq _
    · rw [quartetTree_taxa_eq]; ext y; simp; tauto
    · rw [quartetTree_taxa_eq]; ext y; simp; tauto

/-- The Big Cycle property on four distinct taxa: the three concordance factors differ. -/
theorem bigCycleOn_iff_triple (p : QuartetTree X → ℝ) (h : Distinct4 a b c d) :
    BigCycleOn p {a, b, c, d} ↔
      p (quartetTree a b c d h) ≠ p (quartetTree a c b d (distinct4_acbd h)) ∧
        p (quartetTree a b c d h) ≠ p (quartetTree a d b c (distinct4_adbc h)) ∧
        p (quartetTree a c b d (distinct4_acbd h)) ≠ p (quartetTree a d b c (distinct4_adbc h)) := by
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

/-- Treelikeness on four distinct taxa: the two smallest of the three concordance factors are equal. -/
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

/-- `q^BC = ac|bd` on four distinct taxa: the concordance factor of `ac|bd` is the smallest, strictly. -/
theorem isBCQuartet_acbd_iff (p : QuartetTree X → ℝ) (h : Distinct4 a b c d) :
    IsBCQuartet p {a, b, c, d} (quartetTree a c b d (distinct4_acbd h)) ↔
      p (quartetTree a c b d (distinct4_acbd h)) < p (quartetTree a b c d h) ∧
        p (quartetTree a c b d (distinct4_acbd h)) < p (quartetTree a d b c (distinct4_adbc h)) := by
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

omit [DecidableEq (s : Set X)] in
theorem image_val_univ_coe : (univ : Finset (s : Set X)).image Subtype.val = s := by
  ext x
  simp

/-- The quartet trees on `s` are the images of the quartet trees on all of `↥s`. -/
theorem treesOn_eq_image :
    treesOn s = (treesOn (univ : Finset (s : Set X))).image (QuartetTree.map Subtype.val_injective) := by
  ext q
  simp only [mem_treesOn, mem_image]
  constructor
  · intro hq
    obtain ⟨q₀, rfl⟩ := QuartetTree.exists_map_eq Subtype.val_injective q
      (by rw [hq, image_val_univ_coe])
    refine ⟨q₀, ?_, rfl⟩
    apply image_injective Subtype.val_injective
    rw [← QuartetTree.map_taxa Subtype.val_injective, hq, image_val_univ_coe]
  · rintro ⟨q₀, hq₀, rfl⟩
    rw [QuartetTree.map_taxa, hq₀, image_val_univ_coe]

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
  refine exists_congr fun q => and_congr_right fun _ => exists_congr fun r => and_congr_right fun _ => ?_
  exact and_congr ⟨fun H e => H (QuartetTree.map_injective Subtype.val_injective e),
    fun H e => H (congrArg _ e)⟩ (and_congr_right fun _ => ⟨fun H u hu => H u hu, fun H u hu => H hu⟩)

theorem cyclePropertyOn_comp_map_iff (p : QuartetTree X → ℝ) :
    CyclePropertyOn (fun q => p (q.map Subtype.val_injective)) (univ : Finset (s : Set X)) ↔
      CyclePropertyOn p s :=
  not_congr (isTreelikeOn_comp_map_iff s p)

end Subtype

/-! ### `Q⊕_s` is an LSA quartet network -/

section Induced

variable {V E X : Type*}

/-- A path avoiding a kept vertex `w` gives a path of the suppressed network avoiding `w`, from the end
of the chain of its first vertex. -/
theorem suppress_reflTransGen_avoiding {M : RootedNetwork V E X} (hM : M.IsPhylogenetic)
    (w : {v // ¬ M.IsChainVertex v}) {a b : V} (hb : ¬ M.IsChainVertex b) (hbw : b ≠ w.1)
    (h : Relation.ReflTransGen (fun x y => M.graph.Adj x y ∧ x ≠ w.1 ∧ y ≠ w.1) a b) :
    Relation.ReflTransGen (fun x y => (M.suppress hM).graph.Adj x y ∧ x ≠ w ∧ y ≠ w)
        ⟨chainEnd hM a, not_isChainVertex_chainEnd hM a⟩ ⟨b, hb⟩ ∧
      chainEnd hM a ≠ w.1 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have he : chainEnd hM b = b := chainEnd_eq_self hM hb
    refine ⟨?_, by rw [he]; exact hbw⟩
    have : (⟨chainEnd hM b, not_isChainVertex_chainEnd hM b⟩ : {v // ¬ M.IsChainVertex v}) =
        ⟨b, hb⟩ := Subtype.ext he
    rw [this]
  | @head a c hac _ ih =>
    obtain ⟨ihp, ihw⟩ := ih
    by_cases ha : M.IsChainVertex a
    · have he : chainEnd hM a = chainEnd hM c := chainEnd_eq_of_adj hM ha hac.1
      have : (⟨chainEnd hM a, not_isChainVertex_chainEnd hM a⟩ : {v // ¬ M.IsChainVertex v}) =
          ⟨chainEnd hM c, not_isChainVertex_chainEnd hM c⟩ := Subtype.ext he
      rw [this, he]
      exact ⟨ihp, ihw⟩
    · have he : chainEnd hM a = a := chainEnd_eq_self hM ha
      have : (⟨chainEnd hM a, not_isChainVertex_chainEnd hM a⟩ : {v // ¬ M.IsChainVertex v}) =
          ⟨a, ha⟩ := Subtype.ext he
      rw [this, he]
      refine ⟨Relation.ReflTransGen.head ⟨?_, fun h => hac.2.1 (congrArg Subtype.val h),
        fun h => ihw (congrArg Subtype.val h)⟩ ihp, hac.2.1⟩
      obtain ⟨f, hfs, hft⟩ := hac.1
      exact ⟨⟨f, hfs ▸ ha⟩, Subtype.ext hfs, Subtype.ext (by
        show chainEnd hM (M.graph.target f) = chainEnd hM c
        rw [hft])⟩

/-- A stable ancestor of the suppressed network is one of the network. -/
theorem suppress_isStableAncestor {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) {Y : Set X}
    {w : {v // ¬ M.IsChainVertex v}} (hw : (M.suppress hM).IsStableAncestor Y w) :
    M.IsStableAncestor Y w.1 := by
  intro x hx hp
  obtain ⟨hr, hl, hpath⟩ := hp
  have h := suppress_reflTransGen_avoiding hM w (not_isChainVertex_leaf hM x) hl hpath
  have he : chainEnd hM M.root = M.root := chainEnd_eq_self hM (not_isChainVertex_root hM)
  have : (⟨chainEnd hM M.root, not_isChainVertex_chainEnd hM M.root⟩ :
      {v // ¬ M.IsChainVertex v}) = (M.suppress hM).root := Subtype.ext he
  rw [this] at h
  exact hw x hx ⟨fun e => hr (congrArg Subtype.val e), fun e => hl (congrArg Subtype.val e), h.1⟩

/-- A stable ancestor of the part below the LSA is one of the network. -/
theorem lsaNetwork_isStableAncestor {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {Y : Set X}
    (hY : Y.Nonempty) {w : N.belowVertices (lsa hN Y hY) Y}
    (hw : (lsaNetwork hN Y hY).IsStableAncestor Set.univ w) : N.IsStableAncestor Y w.1 := by
  obtain ⟨hst, -⟩ := lsa_spec hN Y hY
  intro x hx hp
  have hs := hp.suffix_of_not_hasPathAvoiding (hst x hx)
  obtain ⟨hlw, hxw, hpath⟩ := hs
  -- lift the path from the LSA to `x` into the part below the LSA
  have hlift : ∀ a, N.graph.Reaches (lsa hN Y hY) a →
      Relation.ReflTransGen (fun u v => N.graph.Adj u v ∧ u ≠ w.1 ∧ v ≠ w.1) a (N.leaf x) →
      ∀ ha : a ∈ N.belowVertices (lsa hN Y hY) Y,
      Relation.ReflTransGen (fun u v => (lsaNetwork hN Y hY).graph.Adj u v ∧ u ≠ w ∧ v ≠ w)
        ⟨a, ha⟩ ((lsaNetwork hN Y hY).leaf ⟨x, hx⟩) := by
    intro a hla hax
    induction hax using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => .refl
    | @head a c hac hcx ih =>
      intro ha
      obtain ⟨⟨f, hfs, hft⟩, haw, hcw⟩ := hac
      have hlc : N.graph.Reaches (lsa hN Y hY) c := hla.tail ⟨f, hfs, hft⟩
      have hcY : c ∈ N.ancestralVertices Y :=
        ⟨x, hx, Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hcx⟩
      have hc : c ∈ N.belowVertices (lsa hN Y hY) Y := ⟨hlc, hcY⟩
      have hf : f ∈ N.belowArcs (lsa hN Y hY) Y :=
        ⟨hfs ▸ hla, by show N.graph.target f ∈ N.ancestralVertices Y; rw [hft]; exact hcY⟩
      refine Relation.ReflTransGen.head ⟨⟨⟨f, hf⟩, Subtype.ext hfs,
        (Subtype.ext hft : (lsaNetwork hN Y hY).graph.target ⟨f, hf⟩ = ⟨c, hc⟩)⟩,
        fun h => haw (congrArg Subtype.val h), fun h => hcw (congrArg Subtype.val h)⟩ (ih hlc hc)
  refine hw ⟨x, hx⟩ (Set.mem_univ _) ⟨fun h => hlw (congrArg Subtype.val h),
    fun h => hxw (congrArg Subtype.val h), ?_⟩
  exact hlift _ .refl hpath (lsa_mem_ancestralVertices hN hY |> fun h => ⟨.refl, h⟩)

/-- **The induced network is an LSA network**: its root is the LSA of its taxa. -/
theorem inducedNetwork_isLSANetwork {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {Y : Set X}
    (hY : Y.Nontrivial) : (inducedNetwork hN Y hY).IsLSANetwork := by
  refine ⟨root_isStableAncestor _ _, fun w hw => ?_⟩
  have hM := lsaNetwork_isPhylogenetic hN hY
  have h₁ := lsaNetwork_isStableAncestor hN hY.nonempty (suppress_isStableAncestor hM hw)
  have h₂ := (lsa_spec hN Y hY.nonempty).2 _ h₁
  have hw' : w.1.1 = lsa hN Y hY.nonempty :=
    eq_of_reaches_of_reaches hN.acyclic h₂ w.1.2.1
  have : w = (inducedNetwork hN Y hY).root := Subtype.ext (Subtype.ext hw')
  rw [this]
  exact .refl

variable [Fintype V] [Fintype E] [Fintype X]

/-- The parameters of `Q⊕_s` inherited from `N`. -/
abbrev quartetLSAMetric (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (s : Finset X)
    (hs : #s = 4) (θ : MetricData E) :=
  inducedMetric hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty θ

/-- The parameters that `Q⊕_s` inherits from a metric are a metric: every edge, a chain of edges of
`N`, has positive length. -/
theorem quartetLSA_isMetricNetwork {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    {θ : MetricData E} (hθ : IsMetricNetwork N θ) {s : Finset X} (hs : #s = 4) :
    IsMetricNetwork (quartetLSA N hN.1 s hs) (quartetLSAMetric N hN s hs θ) := by
  refine ⟨isMetric_inducedMetric hN.1 _ hθ.1, fun e => ?_⟩
  simp only [quartetLSAMetric, inducedMetric, belowMetric]
  exact Finset.sum_pos (fun f _ => hθ.2 _) ⟨e.1, Finset.mem_filter.mpr ⟨@Finset.mem_univ _ (Fintype.ofFinite _) _, Or.inl rfl⟩⟩

/-- `Q⊕_s` is the LSA network of its taxa. -/
theorem quartetLSA_isLSANetwork {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    {s : Finset X} (hs : #s = 4) : (quartetLSA N hN.1 s hs).IsLSANetwork :=
  inducedNetwork_isLSANetwork hN.1 _

/-- `Q⊕_s` of a level-1 network is level-1: a cycle of the induced network is made of chains of edges
of `N` that form a cycle of `N`, and two cycles sharing a chain share its edges. -/
theorem quartetLSA_isLevelOne {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {s : Finset X} (hs : #s = 4) :
    IsLevelOne (quartetLSA N hN.1 s hs).graph := by
  sorry

/-- **`Q⊕_s` is an LSA quartet network.** -/
theorem isLSAQuartet_quartetLSA {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {θ : MetricData E} (hθ : IsMetricNetwork N θ) {s : Finset X}
    (hs : #s = 4) : IsLSAQuartet (quartetLSA N hN.1 s hs) (quartetLSAMetric N hN s hs θ) where
  binary := quartetLSA_isBinaryRootedNetwork hN hs
  levelOne := quartetLSA_isLevelOne hN h1 hs
  isLSA := quartetLSA_isLSANetwork hN hs
  card_taxa := by simp [hs]
  metric := quartetLSA_isMetricNetwork hN hθ hs

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
