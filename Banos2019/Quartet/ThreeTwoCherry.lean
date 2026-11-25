module

public import Banos2019.Quartet.CherryArc
public import Banos2019.Quartet.Contract
public import Banos2019.Quartet.SemidirectedCycles

/-!
# Below the hybrid node of the only cycle (Lemma 11, in the proof of Proposition 5)

When `C` is the only cycle of a binary level-1 network and two taxa `a`, `b` lie below its hybrid node
`v`, the child `u` of `v` is the parent of the leaves `a` and `b`: below `u` every node has a single
parent, so two children of a node below `u` have no taxon in common
(`cherry_below_hybrid_of_single_cycle`). The number `K` of lineages at `v` and the concordance factors
of the contracted network given `K = 1` are then those of Example 5
(`probLineages_cherry_of_single_cycle`, `condCF_contractRooted_cherry_of_single_cycle`), read off the
length of the edge from `v` to `u`, which an isomorphism of the unrooted networks keeps
(`length_child_eq_of_sdMetricIso`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Below

variable {N : RootedNetwork V E X}

/-- **Below a node under which every node has a single parent arc, two nodes above a common node are
comparable.** -/
theorem reaches_or_reaches_of_unique_parent {w : V}
    (huniq : ∀ z, N.graph.Reaches w z → ∀ e f : E, N.graph.target e = z → N.graph.target f = z →
      e = f)
    {u u' y : V} (hu : N.graph.Reaches w u) (huy : N.graph.Reaches u y)
    (hu'y : N.graph.Reaches u' y) : N.graph.Reaches u u' ∨ N.graph.Reaches u' u := by
  induction huy generalizing u' with
  | refl => exact Or.inr hu'y
  | @tail a b hua hab ih =>
    rcases Relation.ReflTransGen.cases_tail hu'y with h | ⟨c, hu'c, hcb⟩
    · subst h
      exact Or.inl (hua.tail hab)
    · obtain ⟨e, he1, he2⟩ := hab
      obtain ⟨f, hf1, hf2⟩ := hcb
      have hef : e = f := huniq b ((hu.trans hua).tail ⟨e, he1, he2⟩) e f he2 hf2
      subst hef
      have hca : c = a := hf1.symm.trans he1
      subst hca
      exact ih hu'c

end Below

variable [Fintype V] [Fintype E] [Fintype X] {Q : RootedNetwork V E X}

/-- **The child of the hybrid node of the only cycle is the parent of the two taxa below the hybrid
node**: it is not a leaf, and its two child arcs end at the leaves `a` and `b`. Below it every node
has a single parent (a second parent would put it on a cycle, the only cycle `C`, and make it the
hybrid node of `C`, above it), so two siblings below it have no taxon in common, and a child that is not
a leaf would have both `a` and `b` below it. -/
theorem cherry_below_hybrid_of_single_cycle (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    {C : Set E} (hC : IsCycle Q.graph C) (hone : ∀ C', IsCycle Q.graph C' → C' = C) {v : V}
    (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2) {c : E}
    (hc : Q.graph.source c = v) {a b : X} (hab : a ≠ b)
    (hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b) :
    (∀ x, Q.graph.Reaches (Q.graph.target c) (Q.leaf x) ↔ x = a ∨ x = b) ∧
      (∀ x, Q.leaf x ≠ Q.graph.target c) ∧
      ∀ e, Q.graph.source e = Q.graph.target c →
        Q.graph.target e = Q.leaf a ∨ Q.graph.target e = Q.leaf b := by
  have := hQ.1.finite_arcs
  set w := Q.graph.target c with hw_def
  obtain ⟨c', hc', hcu'⟩ := existsUnique_child_of_hybrid hQ h2
  have hcu : ∀ g, Q.graph.source g = v → g = c := fun g hg =>
    (hcu' g hg).trans (hcu' c hc).symm
  have hacyc : ∀ {x y}, Q.graph.Reaches x y → Q.graph.Adj y x → False := fun h hab =>
    hQ.1.acyclic _ (Relation.TransGen.tail' h hab)
  -- the taxa below `w`
  have hbw : ∀ x, Q.graph.Reaches w (Q.leaf x) ↔ x = a ∨ x = b := by
    intro x
    rw [← hbelow x]
    constructor
    · exact fun h => Relation.ReflTransGen.head ⟨c, hc, rfl⟩ h
    · intro h
      rcases eq_or_reaches_of_unique_child hcu h with h' | h'
      · have := hQ.1.leaf_indegree x
        rw [h', h2] at this
        exact absurd this (by norm_num)
      · exact h'
  -- below `w`, every node has a single parent arc
  have huniq : ∀ z, Q.graph.Reaches w z → ∀ e f : E, Q.graph.target e = z →
      Q.graph.target f = z → e = f := by
    intro z hz e f he hf
    by_contra hne
    obtain ⟨C', hC', heC', -⟩ := exists_isCycle_of_target_eq hQ h1 hne (he.trans hf.symm)
    have hCC := hone C' hC'
    subst hCC
    have hzC : z ∈ cycleNodes Q.graph C' := he ▸ target_mem_cycleNodes heC'
    have hz2 : Q.graph.indegree z = 2 :=
      le_antisymm (hQ.indegree_le_two z) (two_le_indegree_of_two_targets hQ hne he hf)
    have hzv : z = v := (lemma3 hQ h1 hC').1.unique ⟨hzC, hz2⟩ ⟨hv, h2⟩
    subst hzv
    exact hQ.1.acyclic z (Relation.TransGen.head' ⟨c, hc, rfl⟩ hz)
  -- `w` is not a leaf
  have hr : ∀ x, Q.leaf x ≠ w := by
    intro x hx
    have h0 : Q.graph.outdegree (Q.leaf x) = 0 := (hQ.1.leaves _).2 ⟨x, rfl⟩
    have ha := (hbw a).2 (Or.inl rfl)
    have hb := (hbw b).2 (Or.inr rfl)
    rw [← hx] at ha hb
    have ha' := Q.graph.eq_of_reaches_of_outdegree_eq_zero ha h0
    have hb' := Q.graph.eq_of_reaches_of_outdegree_eq_zero hb h0
    exact hab (hQ.1.leaf_injective (ha'.trans hb'.symm))
  refine ⟨hbw, hr, ?_⟩
  -- two siblings below `w` have no taxon in common
  have hsib : ∀ e e', e ≠ e' → Q.graph.source e = Q.graph.source e' →
      Q.graph.Reaches w (Q.graph.source e) → ∀ x, Q.graph.Reaches (Q.graph.target e) (Q.leaf x) →
        ¬ Q.graph.Reaches (Q.graph.target e') (Q.leaf x) := by
    intro e e' hne hs hws x hx hx'
    have hwe : Q.graph.Reaches w (Q.graph.target e) := hws.tail ⟨e, rfl, rfl⟩
    have hwe' : Q.graph.Reaches w (Q.graph.target e') := hws.tail ⟨e', hs.symm, rfl⟩
    have key : ∀ g g', g ≠ g' → Q.graph.source g = Q.graph.source g' →
        Q.graph.Reaches w (Q.graph.target g') →
        ¬ Q.graph.Reaches (Q.graph.target g) (Q.graph.target g') := by
      intro g g' hgg hs' hwg' hgg'
      rcases Relation.ReflTransGen.cases_tail hgg' with h | ⟨p, hp, f, hf1, hf2⟩
      · exact hgg (huniq _ hwg' g g' h.symm rfl)
      · have hfg : f = g' := huniq _ hwg' f g' hf2 rfl
        subst hfg
        exact hacyc (hf1 ▸ hp) ⟨g, hs', rfl⟩
    rcases reaches_or_reaches_of_unique_parent huniq hwe hx hx' with h | h
    · exact key e e' hne hs hwe' h
    · exact key e' e (Ne.symm hne) hs.symm hwe h
  -- `w` has two child arcs
  have hwr : w ≠ Q.root := hQ.1.target_ne_root c
  have hin : ∀ z, Q.graph.Reaches w z → z ≠ Q.root → Q.graph.indegree z = 1 := by
    intro z hz hzr
    refine le_antisymm ?_ (hQ.1.nonroot_indegree z hzr)
    unfold DirectedMultigraph.indegree
    rw [Set.ncard_le_one (Set.toFinite _)]
    exact fun e he f hf => huniq z hz e f he hf
  have hout2 : ∀ z, Q.graph.Reaches w z → z ≠ Q.root → Q.graph.outdegree z ≠ 0 →
      Q.graph.outdegree z = 2 := by
    intro z hz hzr h0
    have := hQ.2.2 z hzr h0
    rw [hin z hz hzr] at this
    omega
  have hwout : Q.graph.outdegree w ≠ 0 := fun h0 => by
    obtain ⟨x, hx⟩ := (hQ.1.leaves w).1 h0
    exact hr x hx
  have hother : ∀ z, Q.graph.Reaches w z → z ≠ Q.root → Q.graph.outdegree z ≠ 0 → ∀ e,
      Q.graph.source e = z → ∃ e', e' ≠ e ∧ Q.graph.source e' = z := by
    intro z hz hzr h0 e he
    obtain ⟨g, g', hgg, hs⟩ := Set.ncard_eq_two.1 (hout2 z hz hzr h0)
    have hg : Q.graph.source g = z := (Set.ext_iff.1 hs g).2 (Or.inl rfl)
    have hg' : Q.graph.source g' = z := (Set.ext_iff.1 hs g').2 (Or.inr rfl)
    by_cases hge : g = e
    · exact ⟨g', fun h => hgg (hge.trans h.symm), hg'⟩
    · exact ⟨g, hge, hg⟩
  intro e he
  obtain ⟨e', hne, he'⟩ := hother w .refl hwr hwout e he
  obtain ⟨x', hx'⟩ := exists_reaches_leaf hQ.1 (Q.graph.target e')
  have hwx' : Q.graph.Reaches w (Q.leaf x') := (Relation.ReflTransGen.single ⟨e', he', rfl⟩).trans hx'
  set u := Q.graph.target e with hu_def
  have hwu : Q.graph.Reaches w u := .single ⟨e, he, rfl⟩
  by_cases hu0 : Q.graph.outdegree u = 0
  · obtain ⟨z, hz⟩ := (hQ.1.leaves u).1 hu0
    have hzw : Q.graph.Reaches w (Q.leaf z) := hz ▸ hwu
    rcases (hbw z).1 hzw with rfl | rfl
    · exact Or.inl hz.symm
    · exact Or.inr hz.symm
  · exfalso
    have hur : u ≠ Q.root := hQ.1.target_ne_root e
    obtain ⟨g, hg⟩ : ∃ g, Q.graph.source g = u := by
      by_contra hno
      push Not at hno
      apply hu0
      unfold DirectedMultigraph.outdegree
      rw [Set.ncard_eq_zero (Set.toFinite _)]
      exact Set.eq_empty_of_forall_notMem hno
    obtain ⟨g', hgg, hg'⟩ := hother u hwu hur hu0 g hg
    obtain ⟨y, hy⟩ := exists_reaches_leaf hQ.1 (Q.graph.target g)
    obtain ⟨y', hy'⟩ := exists_reaches_leaf hQ.1 (Q.graph.target g')
    have hyy : y ≠ y' := by
      rintro rfl
      exact hsib g g' (Ne.symm hgg) (hg.trans hg'.symm) (hg ▸ hwu) y hy hy'
    have hwy : Q.graph.Reaches w (Q.leaf y) :=
      hwu.trans ((Relation.ReflTransGen.single ⟨g, hg, rfl⟩).trans hy)
    have hwy' : Q.graph.Reaches w (Q.leaf y') :=
      hwu.trans ((Relation.ReflTransGen.single ⟨g', hg', rfl⟩).trans hy')
    have huy : Q.graph.Reaches u (Q.leaf y) := (Relation.ReflTransGen.single ⟨g, hg, rfl⟩).trans hy
    have huy' : Q.graph.Reaches u (Q.leaf y') :=
      (Relation.ReflTransGen.single ⟨g', hg', rfl⟩).trans hy'
    have hx'y : x' = y ∨ x' = y' := by
      rcases (hbw x').1 hwx' with h | h <;> rcases (hbw y).1 hwy with h' | h' <;>
        rcases (hbw y').1 hwy' with h'' | h'' <;>
        first
        | exact Or.inl (h.trans h'.symm)
        | exact Or.inr (h.trans h''.symm)
        | exact absurd (h'.trans h''.symm) hyy
    have hws : Q.graph.Reaches w (Q.graph.source e) := by rw [he]; exact .refl
    rcases hx'y with rfl | rfl
    · exact hsib e e' (Ne.symm hne) (he.trans he'.symm) hws x' huy hx'
    · exact hsib e e' (Ne.symm hne) (he.trans he'.symm) hws x' huy' hx'

/-- **`P(K = 1) = 1 - e^{-ℓ(c)}` and `P(K = 2) = e^{-ℓ(c)}`** for the lineages at the hybrid node `v`
of the only cycle, with two taxa below `v` and `c` the edge out of `v` (Example 5). -/
theorem probLineages_cherry_of_single_cycle (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    {C : Set E} (hC : IsCycle Q.graph C) (hone : ∀ C', IsCycle Q.graph C' → C' = C) {v : V}
    (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2) {c : E}
    (hc : Q.graph.source c = v) {a b : X} (hab : a ≠ b)
    (hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b) {θ : MetricData E}
    (hθ : Q.IsMetric θ) :
    probLineages Q θ c 1 = 1 - Real.exp (-θ.length c) ∧
      probLineages Q θ c 2 = Real.exp (-θ.length c) := by
  obtain ⟨c', -, hcu'⟩ := existsUnique_child_of_hybrid hQ h2
  have hcu : ∀ g, Q.graph.source g = v → g = c := fun g hg =>
    (hcu' g hg).trans (hcu' c hc).symm
  obtain ⟨hcut, huniq⟩ := isCut_child_of_hybrid hQ h1 h2 hc hcu
  obtain ⟨hbw, hr, harcs⟩ := cherry_below_hybrid_of_single_cycle hQ h1 hC hone hv h2 hc hab hbelow
  exact ⟨probLineages_cherry_one hQ.1 hcut hθ rfl huniq hab hbw (fun x h => hr x h) harcs,
    probLineages_cherry_two hQ.1 hcut hθ rfl huniq hab hbw (fun x h => hr x h) harcs⟩

/-- **`CF(Q₀⊕ | K = 1)`** for the only cycle `C`, with two taxa `a`, `b` below its hybrid node: in the
network with `C` contracted, given one lineage at the top of the edge `c` out of the hybrid node, the
cherry `{a, b}` decides the quartet tree (Example 5). -/
theorem condCF_contractRooted_cherry_of_single_cycle (hQ : IsBinaryRootedNetwork Q)
    (h1 : IsLevelOne Q.graph) {C : Set E} (hC : IsCycle Q.graph C)
    (hone : ∀ C', IsCycle Q.graph C' → C' = C) {v : V} (hv : v ∈ cycleNodes Q.graph C)
    (h2 : Q.graph.indegree v = 2) {c : E} (hc : Q.graph.source c = v) {a b : X} (hab : a ≠ b)
    (hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b) {θ : MetricData E}
    (hθ : Q.IsMetric θ) (hX : Fintype.card X = 4)
    (c₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'}) (hc₀ : c₀.1 = c) (q : QuartetTree X) :
    condCF (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) c₀ 1 q =
      if ({a, b} : Finset X) ∈ q.val then 1 else 0 := by
  obtain ⟨c', -, hcu'⟩ := existsUnique_child_of_hybrid hQ h2
  have hcu : ∀ g, Q.graph.source g = v → g = c := fun g hg =>
    (hcu' g hg).trans (hcu' c hc).symm
  obtain ⟨hcut, huniq⟩ := isCut_child_of_hybrid hQ h1 h2 hc hcu
  obtain ⟨hbw, hr, harcs⟩ := cherry_below_hybrid_of_single_cycle hQ h1 hC hone hv h2 hc hab hbelow
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ h1 hC hv h2
  have hS : ∀ w, Q.graph.Reaches (Q.graph.target c) w → w ∉ cycleNodes Q.graph C := fun w hw hwC =>
    hQ.1.acyclic v (Relation.TransGen.head' ⟨c, hc, rfl⟩
      (hw.trans (reaches_hybrid hQ h1 hC hv h2 w hwC)))
  have hw0 : Q.graph.target c ∉ cycleNodes Q.graph C := hS _ .refl
  set Q₀ := contractRooted Q (· = C)
  have hr₀ : ∀ x, Q₀.leaf x ≠ Quot.mk _ (Q.graph.target c) := fun x hx =>
    hr x ((mk_eq_mk_iff_of_notMem' hC hw0).1 hx)
  have hbelow₀ : ∀ x, Q₀.graph.Reaches (Quot.mk _ (Q.graph.target c)) (Q₀.leaf x) ↔
      x = a ∨ x = b := fun x =>
    (reaches_contract_iff hC hS _).trans (hbw x)
  have huniq₀ : ∀ g, Q₀.graph.target g = Quot.mk _ (Q.graph.target c) → g = c₀ := fun g hg =>
    Subtype.ext (by rw [hc₀]; exact huniq g.1 ((mk_eq_mk_iff_of_notMem' hC hw0).1 hg))
  have harcs₀ : ∀ e, Q₀.graph.source e = Quot.mk _ (Q.graph.target c) →
      Q₀.graph.target e = Q₀.leaf a ∨ Q₀.graph.target e = Q₀.leaf b := by
    intro e he
    rcases harcs e.1 ((mk_eq_mk_iff_of_notMem' hC hw0).1 he) with h | h
    · exact Or.inl (congrArg (Quot.mk _) h)
    · exact Or.inr (congrArg (Quot.mk _) h)
  have hcr : Q₀.graph.target c₀ = Quot.mk _ (Q.graph.target c) := by
    show Quot.mk _ (Q.graph.target c₀.1) = _
    rw [hc₀]
  exact condCF_cherry_one (hK.isPhylogenetic hQ.1) (isCut_contract hC hcut hS) (hK.isMetric hθ) hX
    hcr huniq₀ hab hbelow₀ hr₀ harcs₀ q

/-- **The edge out of a hybrid node has the length of the corresponding edge**: for an isomorphism
`φ` of the metric unrooted networks of two binary level-1 LSA networks, the edge `c` out of a hybrid
node `v`, a tree edge of `Q⁻` from `v`, goes to the edge of `Q̃⁻` from `φ v` that is not hybrid, the
edge `c'` out of `φ v`. -/
theorem length_child_eq_of_sdMetricIso {V' E' : Type*} [Fintype V'] [Fintype E']
    {Q' : RootedNetwork V' E' X} (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    (hl : Q.IsLSANetwork) (hQ' : IsBinaryRootedNetwork Q') (hl' : Q'.IsLSANetwork)
    (hX : Nontrivial X) {θ : MetricData E} {θ' : MetricData E'}
    (φ : SDMetricIso (unrooted Q hQ hX) (unrootedMetric Q hQ hX θ) (unrooted Q' hQ' hX)
      (unrootedMetric Q' hQ' hX θ'))
    {w : SemidirectedVertex hQ.1 hX} (h2 : Q.graph.indegree (sdVert hQ.1 hX w) = 2)
    (h2' : Q'.graph.indegree (sdVert hQ'.1 hX (φ.vert w)) = 2) {c : E}
    (hc : Q.graph.source c = sdVert hQ.1 hX w) {c' : E'}
    (hc' : Q'.graph.source c' = sdVert hQ'.1 hX (φ.vert w)) :
    θ'.length c' = θ.length c := by
  have := hQ.1.finite_arcs
  have := hQ'.1.finite_arcs
  have hr := lsa_univ_eq_root hQ.1 hX hl
  have hr' := lsa_univ_eq_root hQ'.1 hX hl'
  have hvr : sdVert hQ.1 hX w ≠ lsa hQ.1 Set.univ Set.univ_nonempty := sdVert_ne_lsa hQ.1 hX w
  have hvr' : sdVert hQ'.1 hX (φ.vert w) ≠ lsa hQ'.1 Set.univ Set.univ_nonempty :=
    sdVert_ne_lsa hQ'.1 hX _
  -- the edge `cb` of `Q⁻` of `c`
  have hcne : c ≠ sdRootArc hQ.1 hQ.2 hX := fun h => by
    have := (sdRootArc_spec hQ.1 hQ.2 hX).1
    rw [← h, hc] at this
    exact hvr this
  obtain ⟨cb, hcb⟩ := (mem_range_sdArc hQ.1 hQ.2 hX c).2
    ⟨by rw [hr]; exact hQ.1.root_reaches _, hcne⟩
  have hcs : Q.graph.source (sdArc hQ.1 hQ.2 hX cb) ≠ lsa hQ.1 Set.univ Set.univ_nonempty := by
    rw [hcb, hc]
    exact hvr
  have hsrc : (unrooted Q hQ hX).graph.source cb = w := by
    apply sdVert_injective hQ.1 hX
    rcases sdVert_source_cases hQ.1 hQ.2 hX cb with ⟨-, h⟩ | ⟨h, -⟩
    · rw [h, hcb, hc]
    · exact absurd h hcs
  -- `c` is a tree arc
  obtain ⟨c₁, -, hcu₁⟩ := existsUnique_child_of_hybrid hQ h2
  have hcu : ∀ g, Q.graph.source g = sdVert hQ.1 hX w → g = c := fun g hg =>
    (hcu₁ g hg).trans (hcu₁ c hc).symm
  obtain ⟨-, huniq⟩ := isCut_child_of_hybrid hQ h1 h2 hc hcu
  have hct : ¬ (unrooted Q hQ hX).IsDirected cb := by
    rw [semidirected_isDirected_iff, hcb]
    unfold IsHybridArc
    have : Q.graph.indegree (Q.graph.target c) ≤ 1 := by
      unfold DirectedMultigraph.indegree
      rw [Set.ncard_le_one (Set.toFinite _)]
      exact fun g hg g' hg' => (huniq g hg).trans (huniq g' hg').symm
    omega
  -- the edge `φ cb` of `Q̃⁻` is the arc `c'`
  obtain ⟨c₂, -, hcu₂⟩ := existsUnique_child_of_hybrid hQ' h2'
  have hd : sdArc hQ'.1 hQ'.2 hX (φ.edge cb) = c' := by
    rcases φ.joins cb with ⟨hs, -⟩ | ⟨-, ht⟩
    · rw [hsrc] at hs
      rcases sdVert_source_cases hQ'.1 hQ'.2 hX (φ.edge cb) with ⟨-, h'⟩ | ⟨-, h'⟩
      · rw [hs] at h'
        exact (hcu₂ _ h'.symm).trans (hcu₂ c' hc').symm
      · exfalso
        rw [hs] at h'
        have ht1 := (sdRootArc_spec hQ'.1 hQ'.2 hX).2
        unfold IsTreeArc at ht1
        rw [← h', h2'] at ht1
        exact absurd ht1 (by norm_num)
    · exfalso
      rw [hsrc] at ht
      apply hct
      rw [← φ.isDirected_iff, semidirected_isDirected_iff]
      unfold IsHybridArc
      rw [← sdVert_target, ht, h2']
  have hds : Q'.graph.source (sdArc hQ'.1 hQ'.2 hX (φ.edge cb)) ≠
      lsa hQ'.1 Set.univ Set.univ_nonempty := by
    rw [hd, hc']
    exact hvr'
  have hlen := φ.length cb
  rw [semidirectedMetric_length, semidirectedMetric_length, if_neg hds, if_neg hcs, hd, hcb] at hlen
  exact hlen

end Banos2019
