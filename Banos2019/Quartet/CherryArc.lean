module

public import Banos2019.Quartet.Conditioning
public import Phylogenetics.NMSC.TreeCF

/-!
# Two taxa below an arc (Example 5)

Let `c` be the only arc into a cut vertex `r` below which lie exactly two taxa `a` and `b`, at children
of `r`. The two lineages arrive at `r` apart, and coalesce along `c` with probability `1 - e^{-t}`,
`t` the length of `c` (`kingmanTransition_singletons_cherry`).

* `eq_or_eq_of_isGoodForest_of_lineages_eq_pair`: a binary forest on two lineages is the two
  singletons, with or without their cherry.
* `rootDist_cutLower_cherry`: the forest arriving at `r` is `{{a}, {b}}`.
* `arcLaw_cherry`, `probLineages_cherry_one`, `probLineages_cherry_two`: the number `K` of lineages at
  the top of `c` is `1` with probability `1 - e^{-t}` and `2` with probability `e^{-t}`.
* `jointCF_cherry_one`, `condCF_cherry_one`: for four taxa, given `K = 1` the cherry `{a, b}` decides
  the quartet tree: `CF(· | K = 1)` is `1` on the quartet trees with the cherry `{a, b}`, `0` on the
  others.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

omit [Fintype X] in
/-- **A binary forest on two lineages** is the two singletons, with or without their cherry. -/
theorem eq_or_eq_of_isGoodForest_of_lineages_eq_pair {F : Finset (Finset X)} (hF : IsGoodForest F)
    {a b : X} (hab : a ≠ b) (hl : lineages F = {a, b}) :
    F = ({a, b} : Finset X).image (fun x => ({x} : Finset X)) ∨
      F = insert {a, b} (({a, b} : Finset X).image fun x => ({x} : Finset X)) := by
  have hsub : ∀ A ∈ F, A = {a} ∨ A = {b} ∨ A = {a, b} := by
    intro A hA
    obtain ⟨y, hy⟩ := hF.1.1 A hA
    have hAs : ∀ x ∈ A, x = a ∨ x = b := fun x hx => by
      have : x ∈ ({a, b} : Finset X) := hl ▸ mem_lineages.2 ⟨A, hA, hx⟩
      simpa using this
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A
    · refine Or.inr (Or.inr (Subset.antisymm (fun x hx => ?_) ?_))
      · rcases hAs x hx with rfl | rfl <;> simp
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
    · refine Or.inl (Subset.antisymm (fun x hx => ?_) (singleton_subset_iff.2 ha))
      rcases hAs x hx with rfl | rfl
      · exact mem_singleton_self _
      · exact absurd hx hb
    · refine Or.inr (Or.inl (Subset.antisymm (fun x hx => ?_) (singleton_subset_iff.2 hb)))
      rcases hAs x hx with rfl | rfl
      · exact absurd hx ha
      · exact mem_singleton_self _
    · rcases hAs y hy with rfl | rfl
      · exact absurd hy ha
      · exact absurd hy hb
  have hsa : {a} ∈ F := by
    obtain ⟨A, hA, haA⟩ := mem_lineages.1 (hl ▸ mem_insert_self a {b} : a ∈ lineages F)
    exact hF.singleton_mem hA haA
  have hsb : {b} ∈ F := by
    obtain ⟨A, hA, hbA⟩ := mem_lineages.1
      (hl ▸ mem_insert_of_mem (mem_singleton_self b) : b ∈ lineages F)
    exact hF.singleton_mem hA hbA
  have himg : ({a, b} : Finset X).image (fun x => ({x} : Finset X)) = {{a}, {b}} := by
    simp [image_insert, image_singleton]
  rw [himg]
  by_cases hab' : {a, b} ∈ F
  · right
    ext A
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hA
      rcases hsub A hA with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · rintro (rfl | rfl | rfl) <;> assumption
  · left
    ext A
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hA
      rcases hsub A hA with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h ▸ hA) hab'
    · rintro (rfl | rfl) <;> assumption

section Cherry

variable {N : RootedNetwork V E X} {r : V} {a b : X}

/-- **The forest arriving at a cut vertex above two taxa only, at its children**, is the two
singletons: in the support of its law it is a binary forest on the two lineages, and their cherry is
not a cluster at the top of an arc into one of the two leaves. -/
theorem rootDist_cutLower_cherry (hN : N.IsPhylogenetic) (hc : IsCut N r) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hab : a ≠ b) (hbelow : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = a ∨ x = b)
    (hr : ∀ x, N.leaf x ≠ r)
    (harcs : ∀ e, N.graph.source e = r → N.graph.target e = N.leaf a ∨ N.graph.target e = N.leaf b)
    (F₁ : Finset (Finset X)) :
    rootDist (cutLower N r hc) (cutLowerMetric N r θ) 0
        (lowerInj (cutVertices N r) (taxaInj N univ)) F₁ =
      if F₁ = ({a, b} : Finset X).image (fun x => ({x} : Finset X)) then 1 else 0 := by
  have hinj := validInj_taxaInj (N := N) univ
  have hsupp : ∀ F, rootDist (cutLower N r hc) (cutLowerMetric N r θ) 0
      (lowerInj (cutVertices N r) (taxaInj N univ)) F ≠ 0 →
      F = ({a, b} : Finset X).image (fun x => ({x} : Finset X)) := by
    intro F h
    obtain ⟨hg, hl⟩ := good_of_rootDist_cutLower_ne_zero hN hc hinj h
    have hlin : lineages F = {a, b} := by
      ext x
      rw [hl x]
      simp only [mem_insert, mem_singleton]
      constructor
      · rintro ⟨u, hu, hxu⟩
        obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
        exact (hbelow x).1 hu
      · intro hx
        exact ⟨N.leaf x, (hbelow x).2 hx, mem_lineages_taxaInj.2 ⟨mem_univ _, rfl⟩⟩
    rcases eq_or_eq_of_isGoodForest_of_lineages_eq_pair hg hab hlin with h' | h'
    · exact h'
    exfalso
    -- the cherry `{a, b}` would be a cluster at the top of an arc out of `r`
    have hmem : ({a, b} : Finset X) ∈ F := h' ▸ mem_insert_self _ _
    unfold rootDist at h
    obtain ⟨b₁, -, hb⟩ := exists_ne_zero_of_sum_ne_zero h
    obtain ⟨t₁, -, ht⟩ := exists_ne_zero_of_sum_ne_zero hb
    have hw := left_ne_zero_of_mul ht
    have harr : arriving (cutLower N r hc) (lowerInj (cutVertices N r) (taxaInj N univ)) t₁
        (cutLower N r hc).root = F := by
      by_contra hne
      rw [ite_eq_right hne, mul_zero] at ht
      exact ht rfl
    let ι : {e // N.graph.target e = r} ≃ {e // N.graph.target e = r} := Equiv.refl _
    have hgl := isGlued_cut N r hN hc θ ι
    let bot := joinArcs (cutArcs N r ι) (fun _ => ∅) (fun _ => ∅) b₁
    let top := joinArcs (cutArcs N r ι) (fun _ => ∅) (fun _ => ∅) t₁
    have hset : strictBelow N r = ((univ : Finset {w // N.graph.Reaches r w}).erase
        (cutLower N r hc).root).map (Function.Embedding.subtype _) := by
      ext w
      simp only [mem_strictBelow, mem_map, mem_erase, mem_univ, and_true,
        Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨hw, hne⟩
        exact ⟨⟨w, hw⟩, fun h => hne (congrArg Subtype.val h), rfl⟩
      · rintro ⟨w', hne, rfl⟩
        exact ⟨w'.2, fun h => hne (Subtype.ext h)⟩
    have hprod : ∏ w ∈ strictBelow N r, vertexWeight N θ 0 (taxaInj N univ) w bot top ≠ 0 := by
      rw [hset, prod_map]
      refine ne_of_eq_of_ne (prod_congr rfl fun w hw' =>
        hgl.vertexWeight_lower (taxaInj N univ) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) b₁
          t₁ (ne_of_mem_erase hw')) (by unfold injWeight at hw; convert hw)
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_strictBelow hN r) hprod
    have harr' : arriving N (taxaInj N univ) top r = F := by
      rw [← harr]
      exact hgl.arriving_lower (taxaInj N univ) (fun _ => ∅) (fun _ => ∅) t₁ (cutLower N r hc).root
    rw [← harr'] at hmem
    simp only [arriving, mem_union, mem_biUnion, mem_filter, mem_univ, true_and] at hmem
    rcases hmem with hmem | ⟨e, he, hmem⟩
    · -- no taxon is at `r`
      have : a ∈ lineages (taxaInj N univ r) := mem_lineages.2 ⟨_, hmem, mem_insert_self a {b}⟩
      exact hr a (mem_lineages_taxaInj.1 this).2
    · -- the lineages of the top of `e` are below its target, a leaf
      have hte := target_mem_strictBelow_of_source hN he
      obtain ⟨u, hu, hxu⟩ := hF.below e hte a (mem_lineages.2 ⟨_, hmem, mem_insert_self a {b}⟩)
      obtain ⟨u', hu', hxu'⟩ := hF.below e hte b
        (mem_lineages.2 ⟨_, hmem, mem_insert_of_mem (mem_singleton_self b)⟩)
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu'
      have : Finite E := hN.finite_arcs
      have hleaf : ∀ x, N.graph.outdegree (N.leaf x) = 0 := fun x => (hN.leaves _).2 ⟨x, rfl⟩
      rcases harcs e he with h | h
      · rw [h] at hu'
        exact hab (hN.leaf_injective (N.graph.eq_of_reaches_of_outdegree_eq_zero hu' (hleaf a))).symm
      · rw [h] at hu
        exact hab (hN.leaf_injective (N.graph.eq_of_reaches_of_outdegree_eq_zero hu (hleaf b)))
  have hsum := sum_rootDist_cutLower hN hc hθ ⟨le_rfl, zero_le_one⟩ hinj
  rw [Finset.sum_eq_single (({a, b} : Finset X).image (fun x => ({x} : Finset X)))
    (fun F _ hF => by_contra fun h => hF (hsupp F h)) (by simp)] at hsum
  split_ifs with h
  · rw [h, hsum]
  · by_contra h'
    exact h (hsupp F₁ h')

/-- The two singletons are two roots. -/
theorem card_roots_pair_singletons (hab : a ≠ b) :
    #(roots (({a, b} : Finset X).image fun x => ({x} : Finset X))) = 2 := by
  have h : roots (({a, b} : Finset X).image fun x => ({x} : Finset X)) =
      ({a, b} : Finset X).image fun x => ({x} : Finset X) := by
    ext A
    rw [mem_roots]
    refine ⟨fun h => h.1, fun hA => ⟨hA, fun B hB hAB => ?_⟩⟩
    obtain ⟨x, -, rfl⟩ := mem_image.1 hA
    obtain ⟨y, -, rfl⟩ := mem_image.1 hB
    rw [singleton_subset_iff, mem_singleton] at hAB
    rw [hAB]
  rw [h, card_image_of_injective _ (fun x y h => singleton_injective h), card_pair hab]

/-- With their cherry, the two singletons are one root. -/
theorem card_roots_insert_pair_singletons (hab : a ≠ b) :
    #(roots (insert {a, b} (({a, b} : Finset X).image fun x => ({x} : Finset X)))) = 1 := by
  rw [card_eq_one]
  refine ⟨{a, b}, ?_⟩
  ext A
  rw [mem_roots, mem_singleton]
  constructor
  · rintro ⟨hA, hmax⟩
    refine (hmax _ (mem_insert_self _ _) ?_).symm
    exact (by
      rcases mem_insert.1 hA with rfl | hA
      · exact Subset.rfl
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hA
        exact singleton_subset_iff.2 hx)
  · rintro rfl
    refine ⟨mem_insert_self _ _, fun B hB hAB => ?_⟩
    rcases mem_insert.1 hB with rfl | hB
    · rfl
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hB
      have h2 := card_le_card hAB
      rw [card_pair hab, card_singleton] at h2
      omega

variable {c : E}

/-- **The forest at the top of the arc `c` above the cut vertex**: the two singletons, which coalesce
along `c`. -/
theorem arcLaw_cherry (hN : N.IsPhylogenetic) (hc : IsCut N r) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hab : a ≠ b) (hbelow : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = a ∨ x = b)
    (hr : ∀ x, N.leaf x ≠ r)
    (harcs : ∀ e, N.graph.source e = r → N.graph.target e = N.leaf a ∨ N.graph.target e = N.leaf b)
    (t : Finset (Finset X)) :
    arcLaw N r hc θ 0 c (taxaInj N univ) t =
      kingmanTransition (θ.length c) (({a, b} : Finset X).image fun x => ({x} : Finset X)) t := by
  unfold arcLaw
  simp only [rootDist_cutLower_cherry hN hc hθ hab hbelow hr harcs, ite_mul, one_mul, zero_mul,
    sum_ite_eq', mem_univ, ite_true]

/-- From the two singletons, the coalescent leads only to them or to their cherry. -/
theorem eq_or_eq_of_kingmanTransition_pair_ne_zero (hab : a ≠ b) {ℓ : ℝ} {t : Finset (Finset X)}
    (h : kingmanTransition ℓ (({a, b} : Finset X).image fun x => ({x} : Finset X)) t ≠ 0) :
    t = ({a, b} : Finset X).image (fun x => ({x} : Finset X)) ∨
      t = insert {a, b} (({a, b} : Finset X).image fun x => ({x} : Finset X)) := by
  obtain ⟨hg, -, hl⟩ := kingmanTransition_support_good (isGoodForest_singletons _) h
  rw [lineages_image_singleton] at hl
  exact eq_or_eq_of_isGoodForest_of_lineages_eq_pair hg hab hl

/-- **`P(K = 1) = 1 - e^{-t}`**: one lineage at the top of `c` when the two coalesce along it. -/
theorem probLineages_cherry_one (hN : N.IsPhylogenetic) (hc : IsCut N r) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hcr : N.graph.target c = r) (huniq : ∀ g, N.graph.target g = r → g = c)
    (hab : a ≠ b) (hbelow : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = a ∨ x = b)
    (hr : ∀ x, N.leaf x ≠ r)
    (harcs : ∀ e, N.graph.source e = r → N.graph.target e = N.leaf a ∨ N.graph.target e = N.leaf b) :
    probLineages N θ c 1 = 1 - Real.exp (-θ.length c) := by
  rw [probLineages_eq_sum_arc hN hθ hc hcr huniq,
    Finset.sum_eq_single (insert {a, b} (({a, b} : Finset X).image fun x => ({x} : Finset X)))]
  · rw [ite_eq_left (card_roots_insert_pair_singletons hab),
      arcLaw_cherry hN hc hθ hab hbelow hr harcs, kingmanTransition_singletons_cherry (card_pair hab)]
  · intro t _ ht
    split_ifs with h1
    · rw [arcLaw_cherry hN hc hθ hab hbelow hr harcs]
      by_contra h0
      rcases eq_or_eq_of_kingmanTransition_pair_ne_zero hab h0 with rfl | rfl
      · rw [card_roots_pair_singletons hab] at h1
        omega
      · exact ht rfl
    · rfl
  · simp

/-- **`P(K = 2) = e^{-t}`**: two lineages at the top of `c` when they do not coalesce along it. -/
theorem probLineages_cherry_two (hN : N.IsPhylogenetic) (hc : IsCut N r) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hcr : N.graph.target c = r) (huniq : ∀ g, N.graph.target g = r → g = c)
    (hab : a ≠ b) (hbelow : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = a ∨ x = b)
    (hr : ∀ x, N.leaf x ≠ r)
    (harcs : ∀ e, N.graph.source e = r → N.graph.target e = N.leaf a ∨ N.graph.target e = N.leaf b) :
    probLineages N θ c 2 = Real.exp (-θ.length c) := by
  rw [probLineages_eq_sum_arc hN hθ hc hcr huniq,
    Finset.sum_eq_single (({a, b} : Finset X).image fun x => ({x} : Finset X))]
  · rw [ite_eq_left (card_roots_pair_singletons hab), arcLaw_cherry hN hc hθ hab hbelow hr harcs,
      kingmanTransition_apply_self (isGoodForest_singletons _).1, card_roots_pair_singletons hab]
    norm_num
  · intro t _ ht
    split_ifs with h2
    · rw [arcLaw_cherry hN hc hθ hab hbelow hr harcs]
      by_contra h0
      rcases eq_or_eq_of_kingmanTransition_pair_ne_zero hab h0 with rfl | rfl
      · exact ht rfl
      · rw [card_roots_insert_pair_singletons hab] at h2
        omega
    · rfl
  · simp

/-- **Given one lineage at the top of `c`, the cherry `{a, b}` decides the quartet tree**:
`P(K = 1) CF(· | K = 1)` is `P(K = 1)` on the quartet trees with the cherry `{a, b}`, `0` on the
others. -/
theorem jointCF_cherry_one (hN : N.IsPhylogenetic) (hc : IsCut N r) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hX : Fintype.card X = 4) (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) (hab : a ≠ b)
    (hbelow : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = a ∨ x = b) (hr : ∀ x, N.leaf x ≠ r)
    (harcs : ∀ e, N.graph.source e = r → N.graph.target e = N.leaf a ∨ N.graph.target e = N.leaf b)
    (q : QuartetTree X) :
    jointCF N θ c 1 q = (1 - Real.exp (-θ.length c)) * if ({a, b} : Finset X) ∈ q.val then 1 else 0 := by
  have h1 : θ.inheritance c = 1 := hθ.2.2.1 c (isTreeArc_of_unique hcr huniq)
  have hlen : 0 < θ.length c := hθ.1 c (isTreeArc_of_unique hcr huniq)
  set T := insert {a, b} (({a, b} : Finset X).image fun x => ({x} : Finset X)) with hT
  rw [jointCF_eq_sum_arc hN hc hcr huniq h1 1 q, Finset.sum_eq_single T]
  · rw [ite_eq_left (card_roots_insert_pair_singletons hab), arcLaw_cherry hN hc hθ hab hbelow hr harcs,
      kingmanTransition_singletons_cherry (card_pair hab), sum_displays_injDist hX]
    have hne : arcLaw N r hc θ 0 c (taxaInj N univ) T ≠ 0 := by
      rw [arcLaw_cherry hN hc hθ hab hbelow hr harcs, kingmanTransition_singletons_cherry (card_pair hab)]
      have : Real.exp (-θ.length c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
      linarith
    have hv := validInj_of_arcLaw_ne_zero hN hc hcr (validInj_taxaInj univ) hne
    have hmem : ({a, b} : Finset X) ∈ liftInj N c (taxaInj N univ) T (N.graph.source c) := by
      simp only [liftInj, ite_true, mem_union]
      exact Or.inr (mem_insert_self _ _)
    rw [cherryMass_of_mem hN hθ ⟨le_rfl, zero_le_one⟩ hv hmem (card_pair hab)
      (by rw [taxa_eq_univ hX q]; exact subset_univ _)]
  · intro t _ ht
    split_ifs with h1'
    · rw [arcLaw_cherry hN hc hθ hab hbelow hr harcs]
      by_cases h0 : kingmanTransition (θ.length c)
          (({a, b} : Finset X).image fun x => ({x} : Finset X)) t = 0
      · rw [h0, zero_mul]
      · rcases eq_or_eq_of_kingmanTransition_pair_ne_zero hab h0 with rfl | rfl
        · rw [card_roots_pair_singletons hab] at h1'
          omega
        · exact absurd rfl ht
    · rfl
  · simp

/-- **`CF(· | K = 1)`**: `1` on the quartet trees with the cherry `{a, b}`, `0` on the others. -/
theorem condCF_cherry_one (hN : N.IsPhylogenetic) (hc : IsCut N r) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hX : Fintype.card X = 4) (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) (hab : a ≠ b)
    (hbelow : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = a ∨ x = b) (hr : ∀ x, N.leaf x ≠ r)
    (harcs : ∀ e, N.graph.source e = r → N.graph.target e = N.leaf a ∨ N.graph.target e = N.leaf b)
    (q : QuartetTree X) :
    condCF N θ c 1 q = if ({a, b} : Finset X) ∈ q.val then 1 else 0 := by
  have hlen : 0 < θ.length c := hθ.1 c (isTreeArc_of_unique hcr huniq)
  have hpos : 1 - Real.exp (-θ.length c) ≠ 0 := by
    have : Real.exp (-θ.length c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  rw [condCF, jointCF_cherry_one hN hc hθ hX hcr huniq hab hbelow hr harcs q,
    probLineages_cherry_one hN hc hθ hcr huniq hab hbelow hr harcs, mul_div_cancel_left₀ _ hpos]

end Cherry

end Banos2019
