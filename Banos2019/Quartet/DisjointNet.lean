module

public import Banos2019.Quartet.HybridGlue
public import Banos2019.Quartet.Trees

/-!
# The network `Q_a⊕` of Lemma 11

`disjointNet Q v h₁ h₂ a b` is the part of `Q` not below the hybrid node `v`, with the hybrid edges
`h₁`, `h₂` ending at two new leaves, labelled `a` and `b`, the two taxa below `v`. Its process is
that of the part of `Q` not below `v` with the lineage of `a` at the source of `h₁` and that of `b`
at the source of `h₂`: each new leaf carries a single lineage up its edge, and gluing removes the
two leaves one after the other (`NMSC.IsGlued.rootDist_eq_unit`), the first at the cut vertex of its
leaf (`isGlued_cut`), the second by an explicit gluing onto the part of `Q` not below `v`.

* `disjointNet_isPhylogenetic`, `disjointNet_isNormalized`.
* `rootDist_disjointNet`: the law at the root is `hybridUpperLaw` with `{{a}}` and `{{b}}`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] {Q : RootedNetwork V E X} {v : V}
  {h₁ h₂ : E} {a b : X}

/-- A single lineage does not coalesce. -/
theorem kingmanTransition_singleton (x : X) (t : ℝ) (G : Finset (Finset X)) :
    kingmanTransition t {{x}} G = if G = {{x}} then 1 else 0 := by
  refine kingmanTransition_of_card_roots_le_one ⟨fun A hA => ?_, fun A hA B hB => ?_⟩ ?_ t G
  · rw [mem_singleton.1 hA]
    exact singleton_nonempty x
  · rw [mem_singleton.1 hA, mem_singleton.1 hB]
    exact Or.inl le_rfl
  · exact (card_le_card (roots_subset _)).trans (by simp)

omit [Fintype V] [Fintype E] [Fintype X] in
theorem disjointNet_target_h₁ (e : {e // ¬ Q.graph.Reaches v (Q.graph.source e)}) (he : e.1 = h₁) :
    (disjointNet Q v h₁ h₂ a b).graph.target e = .inr 0 := by
  simp [disjointNet, he]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem disjointNet_target_h₂ (hne : h₁ ≠ h₂) (e : {e // ¬ Q.graph.Reaches v (Q.graph.source e)})
    (he : e.1 = h₂) : (disjointNet Q v h₁ h₂ a b).graph.target e = .inr 1 := by
  simp [disjointNet, he, Ne.symm hne]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem disjointNet_root (hr : ¬ Q.graph.Reaches v Q.root) :
    (disjointNet Q v h₁ h₂ a b).root = .inl ⟨Q.root, hr⟩ := by
  simp [disjointNet, hr]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem disjointNet_leaf_a : (disjointNet Q v h₁ h₂ a b).leaf a = .inr 0 := by
  simp [disjointNet]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem disjointNet_leaf_b (hab : a ≠ b) : (disjointNet Q v h₁ h₂ a b).leaf b = .inr 1 := by
  simp [disjointNet, Ne.symm hab]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem disjointNet_leaf_of_ne (hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b) {x : X}
    (hxa : x ≠ a) (hxb : x ≠ b) :
    ∃ hx : ¬ Q.graph.Reaches v (Q.leaf x),
      (disjointNet Q v h₁ h₂ a b).leaf x = .inl ⟨Q.leaf x, hx⟩ := by
  have hx : ¬ Q.graph.Reaches v (Q.leaf x) := fun h => ((hbelow x).1 h).elim hxa hxb
  exact ⟨hx, by simp [disjointNet, hxa, hxb, hx]⟩

section Disjoint

variable (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph) (h2 : Q.graph.indegree v = 2)
  (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) (hab : a ≠ b)
  (hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b)
include hQ h1 h2 hne hh₁ hh₂

omit [Fintype V] [Fintype E] [Fintype X] h1 in
/-- The arcs into `v` are `h₁` and `h₂`. -/
theorem hpar_of_hybrid : ∀ f, Q.graph.target f = v → f = h₁ ∨ f = h₂ := by
  have := hQ.1.finite_arcs
  exact fun f hf => mem_pair_of_target_of_indegree_eq_two h2 hne hh₁ hh₂ f hf

omit [Fintype V] [Fintype E] [Fintype X] hne hh₁ hh₂ in
/-- The hybrid node `v` is a cut vertex. -/
theorem isCut_hybrid : IsCut Q v := by
  have := hQ.1.finite_arcs
  have hvr : v ≠ Q.root := fun h => by
    have := hQ.1.root_indegree
    rw [← h, h2] at this
    omega
  exact ⟨fun h => hvr (eq_of_reaches_of_reaches hQ.1.acyclic h (hQ.1.root_reaches v)),
    fun e he hne' => reaches_source_of_below_hybrid hQ h1 h2 he hne'⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- An arc off the part below `v` that enters it is `h₁` or `h₂`. -/
theorem eq_of_reaches_target (e : {e // ¬ Q.graph.Reaches v (Q.graph.source e)})
    (he : Q.graph.Reaches v (Q.graph.target e.1)) : e.1 = h₁ ∨ e.1 = h₂ := by
  by_cases hev : Q.graph.target e.1 = v
  · exact hpar_of_hybrid hQ h2 hne hh₁ hh₂ e.1 hev
  · exact absurd ((isCut_hybrid hQ h1 h2).entry e.1 he hev) e.2

omit [Fintype V] [Fintype E] [Fintype X] in
theorem disjointNet_target_of_ne (e : {e // ¬ Q.graph.Reaches v (Q.graph.source e)})
    (h₁' : e.1 ≠ h₁) (h₂' : e.1 ≠ h₂) :
    ∃ he : ¬ Q.graph.Reaches v (Q.graph.target e.1),
      (disjointNet Q v h₁ h₂ a b).graph.target e = .inl ⟨Q.graph.target e.1, he⟩ := by
  have he : ¬ Q.graph.Reaches v (Q.graph.target e.1) := fun h =>
    (eq_of_reaches_target hQ h1 h2 hne hh₁ hh₂ e h).elim h₁' h₂'
  exact ⟨he, by simp [disjointNet, h₁', h₂', he]⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The ends in `Q` of the arcs of `Q_a⊕`: the new leaves stand for `v`. -/
theorem disjointNet_target_elim (e : {e // ¬ Q.graph.Reaches v (Q.graph.source e)}) :
    Sum.elim Subtype.val (fun _ => v) ((disjointNet Q v h₁ h₂ a b).graph.target e) =
      Q.graph.target e.1 := by
  by_cases he₁ : e.1 = h₁
  · rw [disjointNet_target_h₁ e he₁, he₁, hh₁]
    rfl
  by_cases he₂ : e.1 = h₂
  · rw [disjointNet_target_h₂ hne e he₂, he₂, hh₂]
    rfl
  obtain ⟨he, h⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) e he₁ he₂
  rw [h]
  rfl

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A node off the part below `v`, reached from the root of `Q`, is reached from the root of
`Q_a⊕`. -/
theorem disjointNet_reaches_inl {w : V} (hr : ¬ Q.graph.Reaches v Q.root)
    (h : Q.graph.Reaches Q.root w) (hw : ¬ Q.graph.Reaches v w) :
    (disjointNet Q v h₁ h₂ a b).graph.Reaches (.inl ⟨Q.root, hr⟩) (.inl ⟨w, hw⟩) := by
  induction h with
  | refl => exact .refl
  | @tail z w hz hzw ih =>
    obtain ⟨f, hfs, hft⟩ := hzw
    have hz' : ¬ Q.graph.Reaches v z := fun h' => hw (h'.tail ⟨f, hfs, hft⟩)
    have hf₁ : f ≠ h₁ := fun h' => hw (by rw [← hft, h', hh₁]; exact .refl)
    have hf₂ : f ≠ h₂ := fun h' => hw (by rw [← hft, h', hh₂]; exact .refl)
    obtain ⟨he, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b)
      ⟨f, hfs ▸ hz'⟩ hf₁ hf₂
    refine (ih hz').tail ⟨⟨f, hfs ▸ hz'⟩, by simp [disjointNet, hfs], ?_⟩
    rw [ht]
    simp [hft]

variable (hab : a ≠ b) (hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b)
include hab hbelow

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **`Q_a⊕` is a phylogenetic network.** -/
theorem disjointNet_isPhylogenetic : (disjointNet Q v h₁ h₂ a b).IsPhylogenetic := by
  set D := disjointNet Q v h₁ h₂ a b
  have hQ' := hQ.1
  have := hQ'.finite_arcs
  have := hQ'.finite_vertices
  have hvr : v ≠ Q.root := fun h => by
    have := hQ'.root_indegree
    rw [← h, h2] at this
    omega
  have hr : ¬ Q.graph.Reaches v Q.root := fun h => hvr (eq_of_reaches_of_reaches hQ'.acyclic h
    (hQ'.root_reaches v))
  have hroot : D.root = .inl ⟨Q.root, hr⟩ := disjointNet_root hr
  have hπ := disjointNet_target_elim hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b)
  have hsv : ∀ {h}, Q.graph.target h = v → ¬ Q.graph.Reaches v (Q.graph.source h) := fun hh h =>
    hQ'.acyclic _ (Relation.TransGen.tail' h ⟨_, rfl, hh⟩)
  -- the arcs out of a node `inl u` are those of `Q` out of `u`
  have hout : ∀ u : {u // ¬ Q.graph.Reaches v u},
      D.graph.outdegree (.inl u) = Q.graph.outdegree u.1 := by
    intro u
    unfold DirectedMultigraph.outdegree
    refine Set.ncard_congr (fun e _ => e.1) (fun e he => ?_) (fun e f _ _ h => Subtype.ext h)
      fun e he => ⟨⟨e, by rw [show Q.graph.source e = u.1 from he]; exact u.2⟩, ?_, rfl⟩
    · have : (Sum.inl ⟨Q.graph.source e.1, e.2⟩ : {u // ¬ Q.graph.Reaches v u} ⊕ Fin 2) =
          .inl u := he
      exact congrArg Subtype.val (Sum.inl_injective this)
    · show (Sum.inl ⟨Q.graph.source e, _⟩ : {u // ¬ Q.graph.Reaches v u} ⊕ Fin 2) = .inl u
      exact congrArg Sum.inl (Subtype.ext he)
  have hout_inr : ∀ i : Fin 2, D.graph.outdegree (.inr i) = 0 := fun i =>
    (D.graph.outdegree_eq_zero_iff _).2 fun e he => Sum.inl_ne_inr he
  have hleaf : ∀ z, (z = a ∧ D.leaf z = .inr 0) ∨ (z = b ∧ D.leaf z = .inr 1) ∨
      (z ≠ a ∧ z ≠ b ∧ ∃ hz : ¬ Q.graph.Reaches v (Q.leaf z), D.leaf z = .inl ⟨Q.leaf z, hz⟩) := by
    intro z
    by_cases hza : z = a
    · exact Or.inl ⟨hza, by rw [hza]; exact disjointNet_leaf_a⟩
    by_cases hzb : z = b
    · exact Or.inr (Or.inl ⟨hzb, by rw [hzb]; exact disjointNet_leaf_b hab⟩)
    exact Or.inr (Or.inr ⟨hza, hzb, disjointNet_leaf_of_ne hbelow hza hzb⟩)
  refine
    { finite_vertices := inferInstance
      finite_arcs := inferInstance
      finite_taxa := hQ'.finite_taxa
      acyclic := fun y hy => hQ'.acyclic _ (Relation.TransGen.lift (Sum.elim Subtype.val
        (fun _ => v)) (fun x y ⟨e, hs, ht⟩ => ⟨e.1, by rw [← hs]; rfl, by rw [← ht, hπ]⟩) y y hy)
      root_reaches := fun y => ?_
      root_indegree := (D.graph.indegree_eq_zero_iff _).2 fun e he => ?_
      nonroot_indegree := fun y hy => ?_
      leaf_injective := fun x y h => ?_
      leaf_indegree := fun x => ?_
      leaves := fun y => ?_ }
  · rw [hroot]
    rcases y with u | i
    · exact disjointNet_reaches_inl hQ h1 h2 hne hh₁ hh₂ hr (hQ'.root_reaches u.1) u.2
    · have key : ∀ {h} (hh : Q.graph.target h = v),
          D.graph.Reaches (.inl ⟨Q.root, hr⟩) (D.graph.target ⟨h, hsv hh⟩) := by
        intro h hh
        exact (disjointNet_reaches_inl hQ h1 h2 hne hh₁ hh₂ hr (hQ'.root_reaches _) (hsv hh)).tail
          ⟨⟨h, hsv hh⟩, rfl, rfl⟩
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
      · have := key hh₁
        rwa [disjointNet_target_h₁ (a := a) (b := b) (h₂ := h₂) ⟨h₁, hsv hh₁⟩ rfl] at this
      · have := key hh₂
        rwa [disjointNet_target_h₂ (a := a) (b := b) hne ⟨h₂, hsv hh₂⟩ rfl] at this
  · rw [hroot] at he
    have := hπ e
    rw [he] at this
    exact (hQ'.target_ne_root e.1) this.symm
  · rcases y with u | i
    · have hur : u.1 ≠ Q.root := fun h => hy (by rw [hroot]; exact congrArg Sum.inl (Subtype.ext h))
      obtain ⟨f, hf⟩ := (Q.graph.one_le_indegree_iff _).1 (hQ'.nonroot_indegree _ hur)
      have hfs : ¬ Q.graph.Reaches v (Q.graph.source f) := fun h' =>
        u.2 (h'.tail ⟨f, rfl, hf⟩)
      have hf₁ : f ≠ h₁ := fun h' => u.2 (by rw [← hf, h', hh₁]; exact .refl)
      have hf₂ : f ≠ h₂ := fun h' => u.2 (by rw [← hf, h', hh₂]; exact .refl)
      obtain ⟨he, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b)
        ⟨f, hfs⟩ hf₁ hf₂
      refine (D.graph.one_le_indegree_iff _).2 ⟨⟨f, hfs⟩, ?_⟩
      rw [ht]
      exact congrArg Sum.inl (Subtype.ext hf)
    · have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
      · exact (D.graph.one_le_indegree_iff _).2 ⟨⟨h₁, hsv hh₁⟩, disjointNet_target_h₁ _ rfl⟩
      · exact (D.graph.one_le_indegree_iff _).2 ⟨⟨h₂, hsv hh₂⟩, disjointNet_target_h₂ hne _ rfl⟩
  · rcases hleaf x with ⟨hxa, hx'⟩ | ⟨hxb, hx'⟩ | ⟨hxa, hxb, hx, hx'⟩ <;>
      rcases hleaf y with ⟨hya, hy'⟩ | ⟨hyb, hy'⟩ | ⟨hya, hyb, hy, hy'⟩ <;>
      rw [hx', hy'] at h <;> first
        | exact hxa.trans hya.symm
        | exact hxb.trans hyb.symm
        | exact hQ'.leaf_injective (congrArg Subtype.val (Sum.inl_injective h))
        | exact absurd h Sum.inl_ne_inr
        | exact absurd h Sum.inr_ne_inl
        | exact absurd h (by simp)
  · refine (D.graph.indegree_eq_one_iff _).2 ?_
    rcases hleaf x with ⟨hxa, hx'⟩ | ⟨hxb, hx'⟩ | ⟨hxa, hxb, hx, h'⟩
    · refine ⟨⟨h₁, hsv hh₁⟩, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
      · rw [hx'] at hf
        by_cases hf₁ : f.1 = h₁
        · exact Subtype.ext hf₁
        by_cases hf₂ : f.1 = h₂
        · rw [disjointNet_target_h₂ hne f hf₂] at hf
          exact absurd hf (by simp)
        obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) f hf₁ hf₂
        rw [ht] at hf
        exact absurd hf Sum.inl_ne_inr
      · rw [hf, hx']
        exact disjointNet_target_h₁ _ rfl
    · refine ⟨⟨h₂, hsv hh₂⟩, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
      · rw [hx'] at hf
        by_cases hf₂ : f.1 = h₂
        · exact Subtype.ext hf₂
        by_cases hf₁ : f.1 = h₁
        · rw [disjointNet_target_h₁ f hf₁] at hf
          exact absurd hf (by simp)
        obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) f hf₁ hf₂
        rw [ht] at hf
        exact absurd hf Sum.inl_ne_inr
      · rw [hf, hx']
        exact disjointNet_target_h₂ hne _ rfl
    obtain ⟨g, hg⟩ := (Q.graph.indegree_eq_one_iff _).1 (hQ'.leaf_indegree x)
    have hgt : Q.graph.target g = Q.leaf x := (hg g).2 rfl
    have hgs : ¬ Q.graph.Reaches v (Q.graph.source g) := fun h'' => hx (h''.tail ⟨g, rfl, hgt⟩)
    refine ⟨⟨g, hgs⟩, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
    · rw [h'] at hf
      by_cases hf₁ : f.1 = h₁
      · rw [disjointNet_target_h₁ f hf₁] at hf
        exact absurd hf Sum.inr_ne_inl
      by_cases hf₂ : f.1 = h₂
      · rw [disjointNet_target_h₂ hne f hf₂] at hf
        exact absurd hf Sum.inr_ne_inl
      obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) f hf₁ hf₂
      rw [ht] at hf
      exact Subtype.ext ((hg f.1).1 (congrArg Subtype.val (Sum.inl_injective hf)))
    · rw [hf, h']
      have hg₁ : g ≠ h₁ := fun h'' => hx (by rw [← hgt, h'', hh₁]; exact .refl)
      have hg₂ : g ≠ h₂ := fun h'' => hx (by rw [← hgt, h'', hh₂]; exact .refl)
      obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b)
        ⟨g, hgs⟩ hg₁ hg₂
      rw [ht]
      exact congrArg Sum.inl (Subtype.ext hgt)
  · rcases y with u | i
    · rw [hout, hQ'.leaves]
      constructor
      · rintro ⟨x, hx⟩
        have hxa : x ≠ a := fun h => u.2 (hx ▸ (hbelow x).2 (Or.inl h))
        have hxb : x ≠ b := fun h => u.2 (hx ▸ (hbelow x).2 (Or.inr h))
        obtain ⟨_, h'⟩ := disjointNet_leaf_of_ne hbelow hxa hxb
        exact ⟨x, h'.trans (congrArg Sum.inl (Subtype.ext hx))⟩
      · rintro ⟨x, hx⟩
        by_cases hxa : x = a
        · rw [hxa, disjointNet_leaf_a] at hx
          exact absurd hx Sum.inr_ne_inl
        by_cases hxb : x = b
        · rw [hxb, disjointNet_leaf_b hab] at hx
          exact absurd hx Sum.inr_ne_inl
        obtain ⟨_, h'⟩ := disjointNet_leaf_of_ne hbelow hxa hxb
        rw [h'] at hx
        exact ⟨x, congrArg Subtype.val (Sum.inl_injective hx)⟩
    · rw [hout_inr]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
      · exact ⟨a, disjointNet_leaf_a⟩
      · exact ⟨b, disjointNet_leaf_b hab⟩

omit [Fintype V] [Fintype E] [Fintype X] hQ h1 h2 hne hh₁ hh₂ in
/-- The taxa at the new leaves of `Q_a⊕`. -/
theorem disjointNet_leaf_eq_inr (x : X) (i : Fin 2) :
    (disjointNet Q v h₁ h₂ a b).leaf x = .inr i ↔ (x = a ∧ i = 0) ∨ (x = b ∧ i = 1) := by
  by_cases hxa : x = a
  · rw [hxa, disjointNet_leaf_a]
    constructor
    · intro h
      exact Or.inl ⟨rfl, (Sum.inr_injective h).symm⟩
    · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
      · rfl
      · exact absurd h hab
  by_cases hxb : x = b
  · rw [hxb, disjointNet_leaf_b hab]
    constructor
    · intro h
      exact Or.inr ⟨rfl, (Sum.inr_injective h).symm⟩
    · rintro (⟨h, -⟩ | ⟨-, rfl⟩)
      · exact absurd h.symm hab
      · rfl
  obtain ⟨_, h'⟩ := disjointNet_leaf_of_ne hbelow hxa hxb
  rw [h']
  simp [hxa, hxb]

omit [Fintype V] [Fintype X] hab hbelow in
/-- The arcs of `Q_a⊕` into a node `inl w` are those of `Q` into `w`. -/
theorem disjointNet_sum_target_inl (w : {u // ¬ Q.graph.Reaches v u}) (g : E → ℝ) :
    ∑ e, (if (disjointNet Q v h₁ h₂ a b).graph.target e = .inl w then g e.1 else 0) =
      ∑ e, (if Q.graph.target e = w.1 then g e else 0) := by
  rw [← sum_filter, ← sum_filter]
  have hsv : ∀ {h}, Q.graph.target h = v → ¬ Q.graph.Reaches v (Q.graph.source h) := fun hh h =>
    hQ.1.acyclic _ (Relation.TransGen.tail' h ⟨_, rfl, hh⟩)
  refine sum_bij (fun e _ => e.1) (fun e he => mem_filter.2 ⟨mem_univ _, ?_⟩)
    (fun e _ f _ h => Subtype.ext h) (fun e he => ?_) fun _ _ => rfl
  · have he' := (mem_filter.1 he).2
    by_cases he₁ : e.1 = h₁
    · rw [disjointNet_target_h₁ e he₁] at he'
      exact absurd he' Sum.inr_ne_inl
    by_cases he₂ : e.1 = h₂
    · rw [disjointNet_target_h₂ hne e he₂] at he'
      exact absurd he' Sum.inr_ne_inl
    obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) e he₁ he₂
    rw [ht] at he'
    exact congrArg Subtype.val (Sum.inl_injective he')
  · have he' : Q.graph.target e = w.1 := (mem_filter.1 he).2
    have hes : ¬ Q.graph.Reaches v (Q.graph.source e) := fun h => w.2 (he' ▸ h.tail ⟨e, rfl, rfl⟩)
    have he₁ : e ≠ h₁ := fun h => w.2 (by rw [← he', h, hh₁]; exact .refl)
    have he₂ : e ≠ h₂ := fun h => w.2 (by rw [← he', h, hh₂]; exact .refl)
    obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b)
      ⟨e, hes⟩ he₁ he₂
    refine ⟨⟨e, hes⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    rw [ht]
    exact congrArg Sum.inl (Subtype.ext he')

omit [Fintype V] [Fintype E] [Fintype X] hab hbelow in
/-- An arc of `Q_a⊕` into a node `inl w` is not `h₁` or `h₂`. -/
theorem disjointNet_ne_of_target_inl {w : {u // ¬ Q.graph.Reaches v u}}
    {e : {e // ¬ Q.graph.Reaches v (Q.graph.source e)}}
    (he : (disjointNet Q v h₁ h₂ a b).graph.target e = .inl w) :
    e.1 ≠ h₁ ∧ e.1 ≠ h₂ ∧ Q.graph.target e.1 = w.1 := by
  by_cases he₁ : e.1 = h₁
  · rw [disjointNet_target_h₁ e he₁] at he
    exact absurd he Sum.inr_ne_inl
  by_cases he₂ : e.1 = h₂
  · rw [disjointNet_target_h₂ hne e he₂] at he
    exact absurd he Sum.inr_ne_inl
  obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) e he₁ he₂
  rw [ht] at he
  exact ⟨he₁, he₂, congrArg Subtype.val (Sum.inl_injective he)⟩

omit [Fintype V] [Fintype E] [Fintype X] hab hbelow in
/-- The arcs of `Q_a⊕` into a node `inl w` are those of `Q` into `w`. -/
theorem disjointNet_indegree_inl (w : {u // ¬ Q.graph.Reaches v u}) :
    (disjointNet Q v h₁ h₂ a b).graph.indegree (.inl w) = Q.graph.indegree w.1 := by
  unfold DirectedMultigraph.indegree
  refine Set.ncard_congr (fun e _ => e.1)
    (fun e (he : (disjointNet Q v h₁ h₂ a b).graph.target e = .inl w) =>
      (disjointNet_ne_of_target_inl hQ h1 h2 hne hh₁ hh₂ he).2.2)
    (fun e f _ _ h => Subtype.ext h) fun e he => ?_
  have he' : Q.graph.target e = w.1 := he
  have hes : ¬ Q.graph.Reaches v (Q.graph.source e) := fun h => w.2 (he' ▸ h.tail ⟨e, rfl, rfl⟩)
  have he₁ : e ≠ h₁ := fun h => w.2 (by rw [← he', h, hh₁]; exact .refl)
  have he₂ : e ≠ h₂ := fun h => w.2 (by rw [← he', h, hh₂]; exact .refl)
  obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b)
    ⟨e, hes⟩ he₁ he₂
  refine ⟨⟨e, hes⟩, ?_, rfl⟩
  show (disjointNet Q v h₁ h₂ a b).graph.target ⟨e, hes⟩ = .inl w
  rw [ht]
  exact congrArg Sum.inl (Subtype.ext he')

omit [Fintype V] [Fintype X] in
/-- **The parameters of `Q_a⊕` are normalized**: `h₁`, `h₂` are tree arcs into the new leaves, of
inheritance `1`, and the other arcs keep their ends in `Q`. -/
theorem disjointNet_isNormalized {θ : MetricData E} (hθ : Q.IsNormalized θ) :
    (disjointNet Q v h₁ h₂ a b).IsNormalized (disjointMetric Q v h₁ h₂ θ) := by
  have := hQ.1.finite_arcs
  -- the new leaves have one parent
  have hD := disjointNet_isPhylogenetic hQ h1 h2 hne hh₁ hh₂ hab hbelow
  have hinr : ∀ i : Fin 2, (disjointNet Q v h₁ h₂ a b).graph.indegree (.inr i) ≤ 1 := by
    intro i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · rw [← disjointNet_leaf_a, hD.leaf_indegree]
    · rw [← disjointNet_leaf_b hab, hD.leaf_indegree]
  refine ⟨fun e he => ?_, fun y hy => ?_⟩
  · show (if e.1 = h₁ ∨ e.1 = h₂ then (1 : ℝ) else θ.inheritance e.1) = 1
    split_ifs with h'
    · rfl
    · push Not at h'
      obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) e h'.1 h'.2
      unfold IsTreeArc at he
      rw [ht, disjointNet_indegree_inl hQ h1 h2 hne hh₁ hh₂] at he
      exact hθ.1 e.1 he
  · rcases y with w | i
    · rw [disjointNet_indegree_inl hQ h1 h2 hne hh₁ hh₂] at hy
      rw [← hθ.2 w.1 hy, ← disjointNet_sum_target_inl hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) w]
      refine sum_congr rfl fun e _ => ?_
      by_cases he : (disjointNet Q v h₁ h₂ a b).graph.target e = .inl w
      · obtain ⟨he₁, he₂, -⟩ := disjointNet_ne_of_target_inl hQ h1 h2 hne hh₁ hh₂ he
        rw [ite_eq_left he, ite_eq_left he]
        show (if e.1 = h₁ ∨ e.1 = h₂ then (1 : ℝ) else θ.inheritance e.1) = θ.inheritance e.1
        rw [ite_eq_right (by tauto)]
      · rw [ite_eq_right he, ite_eq_right he]
    · exact absurd (hinr i) (by omega)

omit [Fintype V] [Fintype E] hQ h1 h2 hne hh₁ hh₂ in
/-- The lineages of the taxa at a node of `Q_a⊕`. -/
theorem taxaInj_disjointNet_inr (i : Fin 2) :
    taxaInj (disjointNet Q v h₁ h₂ a b) univ (.inr i) = if i = 0 then {{a}} else {{b}} := by
  unfold taxaInj
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  ext A
  simp only [mem_image, mem_filter, mem_univ, true_and, disjointNet_leaf_eq_inr hab hbelow]
  rcases hi with rfl | rfl
  · rw [ite_eq_left rfl, mem_singleton]
    constructor
    · rintro ⟨x, (⟨hx, -⟩ | ⟨-, h⟩), hA⟩
      · rw [← hA, hx]
      · exact absurd h (by decide)
    · intro hA
      exact ⟨a, Or.inl ⟨rfl, rfl⟩, hA.symm⟩
  · rw [ite_eq_right (by decide), mem_singleton]
    constructor
    · rintro ⟨x, (⟨-, h⟩ | ⟨hx, -⟩), hA⟩
      · exact absurd h (by decide)
      · rw [← hA, hx]
    · intro hA
      exact ⟨b, Or.inr ⟨rfl, rfl⟩, hA.symm⟩

omit [Fintype V] [Fintype E] hQ h1 h2 hne hh₁ hh₂ in
theorem taxaInj_disjointNet_inl (u : {u // ¬ Q.graph.Reaches v u}) :
    taxaInj (disjointNet Q v h₁ h₂ a b) univ (.inl u) = taxaInj Q univ u.1 := by
  unfold taxaInj
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  by_cases hxa : x = a
  · rw [hxa, disjointNet_leaf_a]
    refine ⟨fun h => absurd h Sum.inr_ne_inl, fun h => absurd (h ▸ (hbelow a).2 (Or.inl rfl)) u.2⟩
  by_cases hxb : x = b
  · rw [hxb, disjointNet_leaf_b hab]
    refine ⟨fun h => absurd h Sum.inr_ne_inl, fun h => absurd (h ▸ (hbelow b).2 (Or.inr rfl)) u.2⟩
  obtain ⟨_, h'⟩ := disjointNet_leaf_of_ne hbelow hxa hxb
  rw [h']
  exact ⟨fun h => congrArg Subtype.val (Sum.inl_injective h),
    fun h => congrArg Sum.inl (Subtype.ext h)⟩

/-- **The process of `Q_a⊕` is that of the part of `Q` not below `v` with the lineages of `a` and
`b` at the sources of `h₁` and `h₂`.** The leaf of `b` is a cut vertex whose single lineage goes up
`h₂` unchanged (`isGlued_cut`, `NMSC.IsGlued.rootDist_eq_unit`); what remains is the part not below
`v` with the leaf of `a` below `h₁`, glued in the same way. -/
theorem rootDist_disjointNet (θ : MetricData E) (F : Finset (Finset X)) :
    rootDist (disjointNet Q v h₁ h₂ a b) (disjointMetric Q v h₁ h₂ θ) 0
        (taxaInj (disjointNet Q v h₁ h₂ a b) univ) F =
      hybridUpperLaw hQ.1 (isCut_hybrid hQ h1 h2) hne hh₁ hh₂ (hpar_of_hybrid hQ h2 hne hh₁ hh₂) θ
        (taxaInj Q univ) {{a}} {{b}} F := by
  set D := disjointNet Q v h₁ h₂ a b with hD_def
  have hD := disjointNet_isPhylogenetic hQ h1 h2 hne hh₁ hh₂ hab hbelow
  have := hQ.1.finite_arcs
  have hsv : ∀ {h}, Q.graph.target h = v → ¬ Q.graph.Reaches v (Q.graph.source h) := fun hh h =>
    hQ.1.acyclic _ (Relation.TransGen.tail' h ⟨_, rfl, hh⟩)
  have hout0 : ∀ i : Fin 2, D.graph.outdegree (.inr i) = 0 := fun i =>
    (D.graph.outdegree_eq_zero_iff _).2 fun e he => Sum.inl_ne_inr he
  have hreach : ∀ (i : Fin 2) y, D.graph.Reaches (.inr i) y → y = .inr i := fun i y h =>
    D.graph.eq_of_reaches_of_outdegree_eq_zero h (hout0 i)
  have hvr : v ≠ Q.root := fun h => by
    have := hQ.1.root_indegree
    rw [← h, h2] at this
    omega
  have hr : ¬ Q.graph.Reaches v Q.root := fun h => hvr (eq_of_reaches_of_reaches hQ.1.acyclic h
    (hQ.1.root_reaches v))
  have hroot : D.root = .inl ⟨Q.root, hr⟩ := disjointNet_root hr
  -- the leaf of `b`
  set r₁ : {u // ¬ Q.graph.Reaches v u} ⊕ Fin 2 := .inr 1
  have hc₁ : IsCut D r₁ := ⟨fun h => by
      have := hreach 1 _ h
      rw [hroot] at this
      exact Sum.inl_ne_inr this, fun e he hne' => absurd (hreach 1 _ he) hne'⟩
  set c₁ : {e // ¬ Q.graph.Reaches v (Q.graph.source e)} := ⟨h₂, hsv hh₂⟩
  have hcr₁ : D.graph.target c₁ = r₁ := disjointNet_target_h₂ hne c₁ rfl
  have huniq₁ : ∀ g, D.graph.target g = r₁ → g = c₁ := by
    intro g hg
    by_cases hg₂ : g.1 = h₂
    · exact Subtype.ext hg₂
    by_cases hg₁ : g.1 = h₁
    · rw [disjointNet_target_h₁ g hg₁] at hg
      exact absurd (Sum.inr_injective hg) (by decide)
    obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) g hg₁ hg₂
    rw [ht] at hg
    exact absurd hg Sum.inl_ne_inr
  have hg₁ := isGlued_cut D r₁ hD hc₁ (disjointMetric Q v h₁ h₂ θ) (unitArc hcr₁ huniq₁)
  have h1₁ : (disjointMetric Q v h₁ h₂ θ).inheritance
      (cutArcs D r₁ (unitArc hcr₁ huniq₁) (.inr (.inl ()))) = 1 := by
    change (if h₂ = h₁ ∨ h₂ = h₂ then (1 : ℝ) else θ.inheritance h₂) = 1
    rw [ite_eq_left (Or.inr rfl)]
  have hlow₁ : lowerInj (cutVertices D r₁) (taxaInj D univ) = atRoot (cutLower D r₁ hc₁) {{b}} := by
    funext w
    unfold lowerInj atRoot
    rw [cutVertices_inr]
    have hw := hreach 1 _ w.2
    rw [ite_eq_left (Subtype.ext hw : w = (cutLower D r₁ hc₁).root), hw,
      taxaInj_disjointNet_inr hab hbelow, ite_eq_right (by decide)]
  rw [hg₁.rootDist_eq_unit le_rfl h1₁, hlow₁]
  simp only [rootDist_atRoot (cutLower_acyclic D r₁ hD hc₁)
    (fun e h => e.2.2 (congrArg Subtype.val h)), ite_mul, one_mul, zero_mul, sum_ite_eq',
    mem_univ, ite_true, kingmanTransition_singleton]
  -- the leaf of `a`, glued onto the part of `Q` not below `v`
  have hcv := isCut_hybrid hQ h1 h2
  have hnr : ∀ y, y ≠ r₁ → ¬ D.graph.Reaches r₁ y := fun y hy h => hy (hreach 1 y h)
  have h01 : (Sum.inr 0 : {u // ¬ Q.graph.Reaches v u} ⊕ Fin 2) ≠ r₁ := fun h =>
    absurd (Sum.inr_injective h) (by decide)
  let ψ : {u // ¬ Q.graph.Reaches v u} ⊕ Unit → {w // ¬ D.graph.Reaches r₁ w} :=
    Sum.elim (fun u => ⟨.inl u, hnr _ Sum.inl_ne_inr⟩) (fun _ => ⟨.inr 0, hnr _ h01⟩)
  have hψ : Function.Bijective ψ := by
    refine ⟨?_, fun w => ?_⟩
    · rintro (u | ⟨⟩) (u' | ⟨⟩) h
      · exact congrArg Sum.inl (Sum.inl_injective (congrArg Subtype.val h))
      · exact absurd (congrArg Subtype.val h) Sum.inl_ne_inr
      · exact absurd (congrArg Subtype.val h) Sum.inr_ne_inl
      · rfl
    · rcases hw : w.1 with u | i
      · exact ⟨.inl u, Subtype.ext hw.symm⟩
      · have hi : i = 0 := by
          by_contra hi
          have hi1 : i = 1 := by fin_cases i <;> simp_all
          exact w.2 (hw ▸ hi1 ▸ .refl)
        exact ⟨.inr (), Subtype.ext (by rw [hw, hi]; rfl)⟩
  have hU : ∀ e : {e // ¬ Q.graph.Reaches v (Q.graph.target e)},
      ¬ Q.graph.Reaches v (Q.graph.source e.1) := fun e h => e.2 (h.tail ⟨e.1, rfl, rfl⟩)
  have hU₁ : ∀ e : {e // ¬ Q.graph.Reaches v (Q.graph.target e)}, e.1 ≠ h₁ := fun e h =>
    e.2 (by rw [h, hh₁]; exact .refl)
  have hU₂ : ∀ e : {e // ¬ Q.graph.Reaches v (Q.graph.target e)}, e.1 ≠ h₂ := fun e h =>
    e.2 (by rw [h, hh₂]; exact .refl)
  have htU : ∀ e : {e // ¬ Q.graph.Reaches v (Q.graph.target e)},
      D.graph.target ⟨e.1, hU e⟩ = .inl ⟨Q.graph.target e.1, e.2⟩ := fun e => by
    obtain ⟨_, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b)
      ⟨e.1, hU e⟩ (hU₁ e) (hU₂ e)
    exact ht
  set c₀ : {e // ¬ Q.graph.Reaches v (Q.graph.source e)} := ⟨h₁, hsv hh₁⟩
  have hct₀ : D.graph.target c₀ = .inr 0 := disjointNet_target_h₁ c₀ rfl
  let φ : {e // ¬ Q.graph.Reaches v (Q.graph.target e)} ⊕ Unit ⊕ Empty →
      {e // ¬ D.graph.Reaches r₁ (D.graph.target e)} :=
    Sum.elim (fun e => ⟨⟨e.1, hU e⟩, by rw [htU e]; exact hnr _ Sum.inl_ne_inr⟩)
      (Sum.elim (fun _ => ⟨c₀, by rw [hct₀]; exact hnr _ h01⟩) Empty.elim)
  have hφ : Function.Bijective φ := by
    refine ⟨?_, fun f => ?_⟩
    · rintro (e | ⟨⟩ | e) (e' | ⟨⟩ | e') h <;> first
        | exact e.elim
        | exact e'.elim
        | rfl
        | exact absurd (congrArg (fun x => x.1.1) h) (hU₁ e)
        | exact absurd (congrArg (fun x => x.1.1) h).symm (hU₁ e')
        | exact congrArg Sum.inl (Subtype.ext (congrArg (fun x => x.1.1) h))
    · by_cases hf₁ : f.1.1 = h₁
      · exact ⟨.inr (.inl ()), Subtype.ext (Subtype.ext hf₁.symm)⟩
      by_cases hf₂ : f.1.1 = h₂
      · exfalso
        have := f.2
        rw [disjointNet_target_h₂ hne f.1 hf₂] at this
        exact this .refl
      obtain ⟨hft, _⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) f.1 hf₁ hf₂
      exact ⟨.inl ⟨f.1.1, hft⟩, rfl⟩
  have hg₂ : IsGlued (cutUpper D r₁ hc₁) (cutUpperMetric D r₁ (disjointMetric Q v h₁ h₂ θ))
      (cutUpper Q v hcv) (cutUpperMetric Q v θ) (pointNetwork X) pointMetric
      (Equiv.ofBijective ψ hψ) (Equiv.ofBijective φ hφ) (fun _ => ⟨Q.graph.source h₁, hsv hh₁⟩)
      (fun _ => θ.length h₁) :=
    { source₀ := fun e => rfl
      target₀ := fun e => Subtype.ext (htU e)
      sourceP := fun _ => rfl
      targetP := fun _ => Subtype.ext hct₀
      source₁ := fun e => e.elim
      target₁ := fun e => e.elim
      root := Subtype.ext hroot
      not_target_root := fun e => e.elim
      length₀ := fun _ => rfl
      lengthP := fun _ => rfl
      length₁ := fun e => e.elim
      inheritance₀ := fun e => by
        change (if e.1 = h₁ ∨ e.1 = h₂ then (1 : ℝ) else θ.inheritance e.1) = θ.inheritance e.1
        rw [ite_eq_right (by have := hU₁ e; have := hU₂ e; tauto)]
      inheritance₁ := fun e => e.elim }
  have h1₂ : (cutUpperMetric D r₁ (disjointMetric Q v h₁ h₂ θ)).inheritance
      (Equiv.ofBijective φ hφ (.inr (.inl ()))) = 1 := by
    change (if h₁ = h₁ ∨ h₁ = h₂ then (1 : ℝ) else θ.inheritance h₁) = 1
    rw [ite_eq_left (Or.inl rfl)]
  rw [hg₂.rootDist_eq_unit le_rfl h1₂]
  have hlow₂ : lowerInj (Equiv.ofBijective ψ hψ) (upperInj (cutVertices D r₁)
      (cutSource D r₁ hD (unitArc hcr₁ huniq₁)) (taxaInj D univ) fun _ => {{b}}) () = {{a}} := by
    unfold lowerInj upperInj
    rw [Equiv.ofBijective_apply, cutVertices_inl]
    change taxaInj D univ (.inr 0) ∪ _ = _
    rw [taxaInj_disjointNet_inr hab hbelow, ite_eq_left rfl]
    ext A
    simp only [mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
    constructor
    · rintro (h | ⟨p, hp, -⟩)
      · exact h
      · exact absurd (congrArg Subtype.val hp) Sum.inl_ne_inr
    · exact fun h => Or.inl h
  simp only [rootDist_pointNetwork, hlow₂, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ,
    ite_true, kingmanTransition_singleton]
  rw [Finset.sum_ite_eq', ite_eq_left (mem_univ _)]
  -- the injected forests are those of `hybridUpperLaw`
  unfold hybridUpperLaw
  congr 1
  funext u
  ext A
  rw [mem_upperInj_boolArcs]
  unfold upperInj
  simp only [Equiv.ofBijective_apply, cutVertices_inl, mem_union, mem_biUnion, mem_filter,
    mem_univ, true_and]
  change (A ∈ taxaInj D univ (.inl u) ∨ ∃ p, cutSource D r₁ hD (unitArc hcr₁ huniq₁) p =
      ⟨.inl u, hnr _ Sum.inl_ne_inr⟩ ∧ A ∈ ({{b}} : Finset (Finset X))) ∨
      (∃ p : Unit, (⟨Q.graph.source h₁, hsv hh₁⟩ : {u // ¬ Q.graph.Reaches v u}) = u ∧
        A ∈ ({{a}} : Finset (Finset X))) ↔ _
  rw [taxaInj_disjointNet_inl hab hbelow]
  constructor
  · rintro ((hA | ⟨p, hp, hA⟩) | ⟨p, hp, hA⟩)
    · exact Or.inl hA
    · exact Or.inr
        (Or.inr ⟨(congrArg Subtype.val (Sum.inl_injective (congrArg Subtype.val hp))).symm,
        hA⟩)
    · exact Or.inr (Or.inl ⟨(congrArg Subtype.val hp).symm, hA⟩)
  · rintro (hA | ⟨hu, hA⟩ | ⟨hu, hA⟩)
    · exact Or.inl (Or.inl hA)
    · exact Or.inr ⟨(), Subtype.ext hu.symm, hA⟩
    · exact Or.inl (Or.inr ⟨(), Subtype.ext (congrArg Sum.inl (Subtype.ext hu.symm)), hA⟩)

end Disjoint

end Banos2019
