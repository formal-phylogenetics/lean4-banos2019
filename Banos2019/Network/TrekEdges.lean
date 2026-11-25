module

public import Banos2019.Network.SDPath

/-!
# The edges of `N⁻` on simple treks between taxa of `Z`

For a binary network `N` and a set `Z` of at least two taxa, an edge of `N⁻` is on a simple trek
between two taxa of `Z` exactly when, as an arc of `N`, it is below `LSA(Z)` and above a taxon of `Z`
(`mem_trekEdges_iff`): the edges of `K` are those of the LSA network `N⊕_Z` before suppression. This
is the step `M' = K` (or `M⁻ = K` when `LSA(Z) = LSA(X)`) of the proof of Proposition 1. One
direction is Lemma 17, given as the hypothesis `h17`; for the other, a simple trek of `N⁻` is first
"uphill" and then "downhill" (`exists_dtrek_of_sdtrek`), so it is a simple trek of `N⁺` with a top
`u`, and `u` is below `LSA(Z)` since the trek is simple. The edge of `N⁻` that replaces the two arcs
out of `LSA(X)` is on such a trek only when `LSA(Z) = LSA(X)`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-- The image of a directed path by a map of the nodes and edges that keeps the ends of its edges. -/
theorem IsDPath.map {V' E' : Type*} {H : DirectedMultigraph V E} {H' : DirectedMultigraph V' E'}
    (fv : V' → V) (fe : E' → E) {u w : V'} {S : Set V'} {P : Set E'} (h : IsDPath H' u w S P)
    (hP : ∀ e ∈ P, H.source (fe e) = fv (H'.source e) ∧ H.target (fe e) = fv (H'.target e)) :
    IsDPath H (fv u) (fv w) (fv '' S) (fe '' P) := by
  induction h with
  | nil u =>
    rw [Set.image_singleton, Set.image_empty]
    exact .nil _
  | @cons e w S P h ih =>
    obtain ⟨hs, ht⟩ := hP e (Set.mem_insert _ _)
    rw [Set.image_insert_eq, Set.image_insert_eq, ← hs]
    exact .cons (fe e) (ht ▸ ih fun f hf => hP f (Set.mem_insert_of_mem _ hf))

/-- A nontrivial directed path is an edge followed by a path. -/
theorem IsDPath.exists_cons {H : DirectedMultigraph V E} (hA : H.IsAcyclic) {u w : V} {S : Set V}
    {P : Set E} (h : IsDPath H u w S P) (hne : u ≠ w) :
    ∃ e S' P', H.source e = u ∧ IsDPath H (H.target e) w S' P' ∧ S = insert u S' ∧
      P = insert e P' ∧ u ∉ S' := by
  cases h with
  | nil => exact absurd rfl hne
  | @cons e _ S' P' h' =>
    exact ⟨e, S', P', rfl, h', rfl, rfl, fun hm =>
      not_reaches_target_source_of_isAcyclic hA e (h'.reaches_of_mem hm).1⟩

section Network

variable {N : RootedNetwork V E X}

/-- A path from the root to `t`, when `m` does not reach `t`, avoids `m`. -/
theorem reflTransGen_avoiding_of_not_reaches {a t m : V} (h : N.graph.Reaches a t)
    (hm : ¬ N.graph.Reaches m t) :
    Relation.ReflTransGen (fun a c => N.graph.Adj a c ∧ a ≠ m ∧ c ≠ m) a t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a c hac hct ih =>
    exact ih.head ⟨hac, fun h => hm (h ▸ hct.head hac), fun h => hm (h ▸ hct)⟩

/-- A directed path from `t` to a taxon of `Z`, when the stable ancestor `m` of `Z` does not reach
`t`, passes through `m`. -/
theorem mem_of_isDPath_of_not_reaches (hN : N.IsPhylogenetic) {Z : Set X} {m : V}
    (hm : N.IsStableAncestor Z m) {z : X} (hz : z ∈ Z) {t : V} {S : Set V} {P : Set E}
    (h : IsDPath N.graph t (N.leaf z) S P) (hmt : ¬ N.graph.Reaches m t) : m ∈ S := by
  by_contra hmS
  refine hm z hz ⟨fun h' => hmt (h' ▸ hN.root_reaches t), fun h' => hmS (h' ▸ h.end_mem), ?_⟩
  exact (reflTransGen_avoiding_of_not_reaches (hN.root_reaches t) hmt).trans
    (h.reflTransGen_avoiding hmS)

/-- **The top of a simple trek between taxa of `Z` is below a stable ancestor of `Z`**: else both
paths would pass through it. -/
theorem reaches_top_of_dtrek (hN : N.IsPhylogenetic) {Z : Set X} {m : V}
    (hm : N.IsStableAncestor Z m) {x y : X} (hx : x ∈ Z) (hy : y ∈ Z) {t : V} {S₁ S₂ : Set V}
    {P₁ P₂ : Set E} (h₁ : IsDPath N.graph t (N.leaf x) S₁ P₁)
    (h₂ : IsDPath N.graph t (N.leaf y) S₂ P₂) (hS : S₁ ∩ S₂ = {t}) : N.graph.Reaches m t := by
  by_contra hmt
  have := (Set.eq_singleton_iff_unique_mem.mp hS).2 m
    ⟨mem_of_isDPath_of_not_reaches hN hm hx h₁ hmt, mem_of_isDPath_of_not_reaches hN hm hy h₂ hmt⟩
  exact hmt (this ▸ .refl)

/-- The LSA of all the taxa is above the LSA of `Z`. -/
theorem lsa_univ_reaches [Nonempty X] (hN : N.IsPhylogenetic) {Z : Set X} (hZ : Z.Nonempty) :
    N.graph.Reaches (lsa hN Set.univ Set.univ_nonempty) (lsa hN Z hZ) :=
  (lsa_spec hN Z hZ).2 _ fun x _ => (lsa_spec hN Set.univ Set.univ_nonempty).1 x (Set.mem_univ x)

/-- Three distinct arcs do not leave a node of outdegree two. -/
theorem not_three_of_outdegree_eq_two [Finite E] {v : V} (hv : N.graph.outdegree v = 2)
    {a b c : E} (ha : N.graph.source a = v) (hb : N.graph.source b = v) (hc : N.graph.source c = v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have h3 : ({a, b, c} : Set E).ncard = 3 := Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub : ({a, b, c} : Set E) ⊆ {e | N.graph.source e = v} := by
    rintro e (rfl | rfl | rfl) <;> assumption
  have := Set.ncard_le_ncard hsub
  unfold DirectedMultigraph.outdegree at hv
  omega

variable (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X)

/-- No edge of `N⁻` enters the child of `rootTreeArc`. -/
theorem sdArc_target_ne (g : SemidirectedArc hN.1 hN.2 hX) :
    N.graph.target (sdArc hN.1 hN.2 hX g) ≠ N.graph.target (sdRootArc hN.1 hN.2 hX) := by
  intro h
  obtain ⟨e₀, he₀⟩ := (N.graph.indegree_eq_one_iff _).mp (sdRootArc_spec hN.1 hN.2 hX).2
  have h₁ := (he₀ _).mp h
  have h₂ := (he₀ (sdRootArc hN.1 hN.2 hX)).mp rfl
  exact ((mem_range_sdArc hN.1 hN.2 hX _).mp ⟨g, rfl⟩).2 (h₁.trans h₂.symm)

/-- The source of an edge of `N⁻` is its source in `N`, unless it leaves `LSA(X)`. -/
theorem sdVert_source_of_ne (g : SemidirectedArc hN.1 hN.2 hX)
    (hg : N.graph.source (sdArc hN.1 hN.2 hX g) ≠ lsa hN.1 Set.univ Set.univ_nonempty) :
    sdVert hN.1 hX ((semidirected hN.1 hN.2 hX).graph.source g) =
      N.graph.source (sdArc hN.1 hN.2 hX g) := by
  classical
  rw [sdVert_source]
  simp [hg]

theorem sdVert_source_of_eq (g : SemidirectedArc hN.1 hN.2 hX)
    (hg : N.graph.source (sdArc hN.1 hN.2 hX g) = lsa hN.1 Set.univ Set.univ_nonempty) :
    sdVert hN.1 hX ((semidirected hN.1 hN.2 hX).graph.source g) =
      N.graph.target (sdRootArc hN.1 hN.2 hX) := by
  classical
  rw [sdVert_source]
  simp [hg]

/-- A path of `N⁻` along the directions, from a node other than the child of `rootTreeArc`, is a
path of `N`. -/
theorem reaches_of_sd_reaches {a b : SemidirectedVertex hN.1 hX}
    (h : (semidirected hN.1 hN.2 hX).graph.Reaches a b)
    (ha : sdVert hN.1 hX a ≠ N.graph.target (sdRootArc hN.1 hN.2 hX)) :
    N.graph.Reaches (sdVert hN.1 hX a) (sdVert hN.1 hX b) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a c hac _ ih =>
    obtain ⟨g, rfl, rfl⟩ := hac
    have hs : N.graph.source (sdArc hN.1 hN.2 hX g) ≠ lsa hN.1 Set.univ Set.univ_nonempty :=
      fun h' => ha (sdVert_source_of_eq hN hX g h')
    refine (ih ?_).head ⟨sdArc hN.1 hN.2 hX g, (sdVert_source_of_ne hN hX g hs).symm, rfl⟩
    exact sdArc_target_ne hN hX g

/-- `N⁻` has no directed cycle. -/
theorem semidirected_isAcyclic : (semidirected hN.1 hN.2 hX).graph.IsAcyclic := by
  have step : ∀ (g : SemidirectedArc hN.1 hN.2 hX),
      sdVert hN.1 hX ((semidirected hN.1 hN.2 hX).graph.source g) ≠
        N.graph.target (sdRootArc hN.1 hN.2 hX) →
      N.graph.Adj (sdVert hN.1 hX ((semidirected hN.1 hN.2 hX).graph.source g))
        (sdVert hN.1 hX ((semidirected hN.1 hN.2 hX).graph.target g)) := by
    intro g hg
    have hs : N.graph.source (sdArc hN.1 hN.2 hX g) ≠ lsa hN.1 Set.univ Set.univ_nonempty :=
      fun h'' => hg (sdVert_source_of_eq hN hX g h'')
    exact ⟨sdArc hN.1 hN.2 hX g, (sdVert_source_of_ne hN hX g hs).symm, rfl⟩
  have key : ∀ a b, Relation.TransGen (semidirected hN.1 hN.2 hX).graph.Adj a b →
      sdVert hN.1 hX b ≠ N.graph.target (sdRootArc hN.1 hN.2 hX) ∧
        (sdVert hN.1 hX a ≠ N.graph.target (sdRootArc hN.1 hN.2 hX) →
          Relation.TransGen N.graph.Adj (sdVert hN.1 hX a) (sdVert hN.1 hX b)) := by
    intro a b h
    induction h with
    | single hab =>
      obtain ⟨g, rfl, rfl⟩ := hab
      exact ⟨sdArc_target_ne hN hX g, fun ha => .single (step g ha)⟩
    | tail _ hcb ih =>
      obtain ⟨g, rfl, rfl⟩ := hcb
      exact ⟨sdArc_target_ne hN hX g, fun ha => (ih.2 ha).tail (step g ih.1)⟩
  intro a h
  exact hN.1.acyclic _ ((key a a h).2 (key a a h).1)

/-- Two edges of `N⁻` entering a node are hybrid. -/
theorem semidirected_isDirected_of_target_eq (g g' : SemidirectedArc hN.1 hN.2 hX) (hne : g ≠ g')
    (ht : (semidirected hN.1 hN.2 hX).graph.target g = (semidirected hN.1 hN.2 hX).graph.target g') :
    (semidirected hN.1 hN.2 hX).IsDirected g := by
  have := hN.1.finite_arcs
  rw [semidirected_isDirected_iff]
  have ht' : N.graph.target (sdArc hN.1 hN.2 hX g) = N.graph.target (sdArc hN.1 hN.2 hX g') :=
    congrArg (sdVert hN.1 hX) ht
  have hne' : sdArc hN.1 hN.2 hX g ≠ sdArc hN.1 hN.2 hX g' := fun h =>
    hne (sdArc_injective hN.1 hN.2 hX h)
  have hsub : ({sdArc hN.1 hN.2 hX g, sdArc hN.1 hN.2 hX g'} : Set E) ⊆
      {f | N.graph.target f = N.graph.target (sdArc hN.1 hN.2 hX g)} := by
    rintro f (rfl | rfl)
    · rfl
    · exact ht'.symm
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hne'] at this
  exact this

/-- In a simple trek of `N⁻` along the directions between taxa of `Z`, the edge out of `LSA(X)`
makes `LSA(Z) = LSA(X)`: in `N`, the trek goes up to `LSA(X)` and down, and its top is below
`LSA(Z)`. -/
theorem lsa_eq_of_dtrek {Z : Set X} (hZ : Z.Nonempty) {x y : X} (hx : x ∈ Z) (hy : y ∈ Z)
    {u : SemidirectedVertex hN.1 hX} {Sa Sb : Set (SemidirectedVertex hN.1 hX)}
    {Pa Pb : Set (SemidirectedArc hN.1 hN.2 hX)}
    (ha : IsDPath (semidirected hN.1 hN.2 hX).graph u ((semidirected hN.1 hN.2 hX).leaf x) Sa Pa)
    (hb : IsDPath (semidirected hN.1 hN.2 hX).graph u ((semidirected hN.1 hN.2 hX).leaf y) Sb Pb)
    (hab : Sa ∩ Sb = {u}) {g' : SemidirectedArc hN.1 hN.2 hX} (hg' : g' ∈ Pa)
    (hρ : N.graph.source (sdArc hN.1 hN.2 hX g') = lsa hN.1 Set.univ Set.univ_nonempty) :
    lsa hN.1 Z hZ = lsa hN.1 Set.univ Set.univ_nonempty := by
  have hA := semidirected_isAcyclic hN hX
  have := hN.1.finite_arcs
  set G := semidirected hN.1 hN.2 hX
  set ρ := lsa hN.1 Set.univ Set.univ_nonempty
  have hsg := sdVert_source_of_eq hN hX g' hρ
  -- the edge `g'` leaves the top `u`, the child of `rootTreeArc`
  have hu : G.graph.source g' = u := by
    rcases ha.eq_or_target (ha.ends_mem hg').1 with h | ⟨e, -, he⟩
    · exact h
    · exfalso
      have := congrArg (sdVert hN.1 hX) he
      rw [hsg] at this
      exact sdArc_target_ne hN hX e this
  have hu' : sdVert hN.1 hX u = N.graph.target (sdRootArc hN.1 hN.2 hX) := hu ▸ hsg
  obtain ⟨Sa', Pa', ha', rfl, rfl, huSa'⟩ := ha.uncons hA hg' hu
  have hsrc : ∀ e : SemidirectedArc hN.1 hN.2 hX, N.graph.source (sdArc hN.1 hN.2 hX e) = ρ →
      G.graph.source e = u := fun e he =>
    sdVert_injective hN.1 hX ((sdVert_source_of_eq hN hX e he).trans hu'.symm)
  have hne₁ : ∀ e : SemidirectedArc hN.1 hN.2 hX, sdArc hN.1 hN.2 hX e ≠ sdRootArc hN.1 hN.2 hX :=
    fun e => ((mem_range_sdArc hN.1 hN.2 hX _).mp ⟨e, rfl⟩).2
  -- the other edges leave nodes other than `LSA(X)` in `N`
  have hfree : ∀ e ∈ Pa' ∪ Pb, N.graph.source (sdArc hN.1 hN.2 hX e) ≠ ρ := by
    rintro e (he | he) heρ
    · exact huSa' (hsrc e heρ ▸ (ha'.ends_mem he).1)
    · have hne₃ : sdArc hN.1 hN.2 hX e ≠ sdArc hN.1 hN.2 hX g' := by
        intro h
        have h' := sdArc_injective hN.1 hN.2 hX h
        subst h'
        have : G.graph.target e = u := (Set.eq_singleton_iff_unique_mem.mp hab).2 _
          ⟨Set.mem_insert_of_mem _ ha'.start_mem, (hb.ends_mem he).2⟩
        exact huSa' (this ▸ ha'.start_mem)
      exact not_three_of_outdegree_eq_two (lsa_univ_outdegree hN.1 hN.2) heρ hρ
        (sdRootArc_spec hN.1 hN.2 hX).1 hne₃ (hne₁ e) (hne₁ g')
  -- the two paths of `N` from `LSA(X)`
  have hA' : IsDPath N.graph ρ (N.leaf x) (insert ρ (sdVert hN.1 hX '' Sa'))
      (insert (sdArc hN.1 hN.2 hX g') (sdArc hN.1 hN.2 hX '' Pa')) := by
    have hm := ha'.map (sdVert hN.1 hX) (sdArc hN.1 hN.2 hX) fun e he =>
      ⟨(sdVert_source_of_ne hN hX e (hfree e (Or.inl he))).symm, rfl⟩
    have := IsDPath.cons (sdArc hN.1 hN.2 hX g') hm
    rw [hρ] at this
    exact this
  have hB' : IsDPath N.graph ρ (N.leaf y) (insert ρ (sdVert hN.1 hX '' Sb))
      (insert (sdRootArc hN.1 hN.2 hX) (sdArc hN.1 hN.2 hX '' Pb)) := by
    have hm := hb.map (sdVert hN.1 hX) (sdArc hN.1 hN.2 hX) fun e he =>
      ⟨(sdVert_source_of_ne hN hX e (hfree e (Or.inr he))).symm, rfl⟩
    rw [hu'] at hm
    have := IsDPath.cons (sdRootArc hN.1 hN.2 hX) hm
    rw [(sdRootArc_spec hN.1 hN.2 hX).1] at this
    exact this
  have hS : insert ρ (sdVert hN.1 hX '' Sa') ∩ insert ρ (sdVert hN.1 hX '' Sb) = {ρ} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨Set.mem_insert _ _, Set.mem_insert _ _⟩, ?_⟩
    rintro s ⟨hs₁, hs₂⟩
    rcases hs₁ with hs₁ | ⟨a, ha, rfl⟩
    · exact hs₁
    rcases hs₂ with hs₂ | ⟨b, hb', hab'⟩
    · exact hs₂
    · have := sdVert_injective hN.1 hX hab'
      subst this
      have : b = u := (Set.eq_singleton_iff_unique_mem.mp hab).2 _ ⟨Set.mem_insert_of_mem _ ha, hb'⟩
      exact absurd (this ▸ ha) huSa'
  exact eq_of_reaches_of_reaches hN.1.acyclic
    (reaches_top_of_dtrek hN.1 (lsa_spec hN.1 Z hZ).1 hx hy hA' hB' hS) (lsa_univ_reaches hN.1 hZ)

/-- **The edges of `K` are in the LSA network**: an edge of `N⁻` on a simple trek between taxa of
`Z` is, in `N`, below `LSA(Z)` and above a taxon of `Z`. -/
theorem mem_belowArcs_of_mem_trekEdges {Z : Set X} (hZ : Z.Nonempty)
    (g : SemidirectedArc hN.1 hN.2 hX) (hg : g ∈ trekEdges (semidirected hN.1 hN.2 hX) Z) :
    sdArc hN.1 hN.2 hX g ∈ N.belowArcs (lsa hN.1 Z hZ) Z := by
  set G := semidirected hN.1 hN.2 hX
  obtain ⟨x, hx, y, hy, t, P₁, P₂, ⟨S₁, S₂, ⟨h₁, h₂⟩, hS⟩, hgP⟩ := hg
  obtain ⟨u, Sa, Pa, Sb, Pb, ha, hb, hab, hsub, -⟩ := exists_dtrek_of_sdtrek
    (semidirected_isAcyclic hN hX) (semidirected_isDirected_of_target_eq hN hX) h₁.isSDP h₂.isSDP hS
  have hgab := hsub hgP
  refine ⟨?_, ?_⟩
  · by_cases hρ : ∃ g' ∈ Pa ∪ Pb,
        N.graph.source (sdArc hN.1 hN.2 hX g') = lsa hN.1 Set.univ Set.univ_nonempty
    · obtain ⟨g', hg', hg'ρ⟩ := hρ
      have hm : lsa hN.1 Z hZ = lsa hN.1 Set.univ Set.univ_nonempty := by
        rcases hg' with hg' | hg'
        · exact lsa_eq_of_dtrek hN hX hZ hx hy ha hb hab hg' hg'ρ
        · exact lsa_eq_of_dtrek hN hX hZ hy hx hb ha (by rw [Set.inter_comm]; exact hab) hg' hg'ρ
      rw [hm]
      exact ((mem_range_sdArc hN.1 hN.2 hX _).mp ⟨g, rfl⟩).1
    · push Not at hρ
      have hma := ha.map (sdVert hN.1 hX) (sdArc hN.1 hN.2 hX) fun e he =>
        ⟨(sdVert_source_of_ne hN hX e (hρ e (Or.inl he))).symm, rfl⟩
      have hmb := hb.map (sdVert hN.1 hX) (sdArc hN.1 hN.2 hX) fun e he =>
        ⟨(sdVert_source_of_ne hN hX e (hρ e (Or.inr he))).symm, rfl⟩
      have hS' : sdVert hN.1 hX '' Sa ∩ sdVert hN.1 hX '' Sb = {sdVert hN.1 hX u} := by
        rw [← Set.image_inter (sdVert_injective hN.1 hX), hab, Set.image_singleton]
      have htop := reaches_top_of_dtrek hN.1 (lsa_spec hN.1 Z hZ).1 hx hy hma hmb hS'
      rw [← sdVert_source_of_ne hN hX g (hρ g hgab)]
      rcases hgab with hg | hg
      · exact htop.trans (hma.reaches_of_mem ⟨_, (ha.ends_mem hg).1, rfl⟩).1
      · exact htop.trans (hmb.reaches_of_mem ⟨_, (hb.ends_mem hg).1, rfl⟩).1
  · rcases hgab with hg | hg
    · exact ⟨x, hx, reaches_of_sd_reaches hN hX (ha.reaches_of_mem (ha.ends_mem hg).2).2
        (sdArc_target_ne hN hX g)⟩
    · exact ⟨y, hy, reaches_of_sd_reaches hN hX (hb.reaches_of_mem (hb.ends_mem hg).2).2
        (sdArc_target_ne hN hX g)⟩

/-- The case of `mem_trekEdges_of_mem_belowArcs` where the trek of `N` has top `LSA(X)` and its first
path starts with `rootTreeArc`: in `N⁻`, the top is the child of `rootTreeArc`, and the second path
starts with the edge that replaces the two arcs out of `LSA(X)`. -/
theorem mem_trekEdges_of_root {Z : Set X} {x y : X} (hx : x ∈ Z) (hy : y ∈ Z) {fb : E}
    {S₁ S₂ : Set V} {P₁ P₂ : Set E}
    (hfb : N.graph.source fb = lsa hN.1 Set.univ Set.univ_nonempty)
    (hfab : sdRootArc hN.1 hN.2 hX ≠ fb)
    (h₁ : IsDPath N.graph (N.graph.target (sdRootArc hN.1 hN.2 hX)) (N.leaf x) S₁ P₁)
    (h₂ : IsDPath N.graph (N.graph.target fb) (N.leaf y) S₂ P₂)
    (hρ₁ : lsa hN.1 Set.univ Set.univ_nonempty ∉ S₁) (hρ₂ : lsa hN.1 Set.univ Set.univ_nonempty ∉ S₂)
    (hS : S₁ ∩ S₂ = ∅)
    (hρS : ∀ s ∈ S₁ ∪ S₂, N.graph.Reaches (lsa hN.1 Set.univ Set.univ_nonempty) s)
    (g : SemidirectedArc hN.1 hN.2 hX)
    (hg : sdArc hN.1 hN.2 hX g ∈ insert (sdRootArc hN.1 hN.2 hX) P₁ ∪ insert fb P₂) :
    g ∈ trekEdges (semidirected hN.1 hN.2 hX) Z := by
  have hA := semidirected_isAcyclic hN hX
  set G := semidirected hN.1 hN.2 hX
  set ρ := lsa hN.1 Set.univ Set.univ_nonempty
  set f₁ := sdRootArc hN.1 hN.2 hX
  have hsf₁ : N.graph.source f₁ = ρ := (sdRootArc_spec hN.1 hN.2 hX).1
  obtain ⟨tv, htv⟩ := (mem_range_sdVert hN.1 hX (N.graph.target f₁)).mpr
    ⟨.single ⟨f₁, hsf₁, rfl⟩, fun h => not_reaches_target_source_of_isAcyclic hN.1.acyclic f₁ (by
      rw [h, hsf₁]; exact .refl)⟩
  obtain ⟨es, hes⟩ := (mem_range_sdArc hN.1 hN.2 hX fb).mpr ⟨hfb ▸ .refl, hfab.symm⟩
  have hsrc : G.graph.source es = tv := sdVert_injective hN.1 hX
    ((sdVert_source_of_eq hN hX es (hes ▸ hfb)).trans htv.symm)
  -- the arcs of the two paths are edges of `N⁻` with the same ends
  have hlift : ∀ {S : Set V} {P : Set E} {a b : V}, IsDPath N.graph a b S P → ρ ∉ S →
      (∀ s ∈ S, N.graph.Reaches ρ s) → ∀ e ∈ P, ∃ e', sdArc hN.1 hN.2 hX e' = e ∧
        N.graph.source e = sdVert hN.1 hX (G.graph.source e') ∧
          N.graph.target e = sdVert hN.1 hX (G.graph.target e') := by
    intro S P a b h hρ hR e he
    have hse := (h.ends_mem he).1
    have hne : N.graph.source e ≠ ρ := fun h' => hρ (h' ▸ hse)
    obtain ⟨e', rfl⟩ := (mem_range_sdArc hN.1 hN.2 hX e).mpr ⟨hR _ hse, fun h' => hne (h' ▸ hsf₁)⟩
    exact ⟨e', rfl, (sdVert_source_of_ne hN hX e' hne).symm, rfl⟩
  have pb₁ := h₁.pullback (sdVert hN.1 hX) (sdArc hN.1 hN.2 hX) (sdVert_injective hN.1 hX)
    (sdArc_injective hN.1 hN.2 hX) (hlift h₁ hρ₁ fun s hs => hρS s (Or.inl hs)) htv
    (w' := G.leaf x) rfl
  have pb₂ := h₂.pullback (sdVert hN.1 hX) (sdArc hN.1 hN.2 hX) (sdVert_injective hN.1 hX)
    (sdArc_injective hN.1 hN.2 hX) (hlift h₂ hρ₂ fun s hs => hρS s (Or.inr hs))
    (u' := G.graph.target es) (by rw [← hes]; rfl) (w' := G.leaf y) rfl
  have path₂ := IsDPath.cons es pb₂
  rw [hsrc] at path₂
  refine ⟨x, hx, y, hy, tv, _, _, ⟨_, _, ⟨pb₁.isSDPath hA rfl, path₂.isSDPath hA rfl⟩, ?_⟩, ?_⟩
  · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨?_, Set.mem_insert _ _⟩, ?_⟩
    · show sdVert hN.1 hX tv ∈ S₁
      rw [htv]
      exact h₁.start_mem
    · rintro s ⟨hs₁, rfl | hs₂⟩
      · rfl
      · have : sdVert hN.1 hX s ∈ S₁ ∩ S₂ := ⟨hs₁, hs₂⟩
        rw [hS] at this
        exact absurd this (Set.notMem_empty _)
  · rcases hg with (h | h) | (h | h)
    · exact absurd h ((mem_range_sdArc hN.1 hN.2 hX _).mp ⟨g, rfl⟩).2
    · exact Or.inl h
    · exact Or.inr (Or.inl (sdArc_injective hN.1 hN.2 hX (h.trans hes.symm)))
    · exact Or.inr (Or.inr h)

/-- **The edges of the LSA network are in `K`** (by Lemma 17, the hypothesis `h17`): an arc of `N`
below `LSA(Z)` and above a taxon of `Z` is, as an edge of `N⁻`, on a simple trek between taxa of `Z`.
The trek of Lemma 17 is a trek of `N⁻`; when its top is `LSA(X)`, its two arcs out of `LSA(X)` are
replaced by the edge of `N⁻` that joins their children. -/
theorem mem_trekEdges_of_mem_belowArcs {Z : Set X} (hZ : Z.Nonempty)
    (h17 : ∀ e : E, N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source e) →
      (∃ z ∈ Z, N.graph.Reaches (N.graph.target e) (N.leaf z)) →
      ∃ x ∈ Z, ∃ y ∈ Z, ∃ t P₁ P₂, IsSimpleTrek (⟨N.graph, fun _ => True, N.leaf⟩ :
        SemidirectedNetwork V E X) (N.leaf x) (N.leaf y) t P₁ P₂ ∧ e ∈ P₁ ∪ P₂ ∧
        ∀ f ∈ P₁ ∪ P₂, N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source f))
    (g : SemidirectedArc hN.1 hN.2 hX) (hg : sdArc hN.1 hN.2 hX g ∈ N.belowArcs (lsa hN.1 Z hZ) Z) :
    g ∈ trekEdges (semidirected hN.1 hN.2 hX) Z := by
  have hA := semidirected_isAcyclic hN hX
  have hAN := hN.1.acyclic
  have := hN.1.finite_arcs
  set G := semidirected hN.1 hN.2 hX
  set ρ := lsa hN.1 Set.univ Set.univ_nonempty
  set m := lsa hN.1 Z hZ
  set f₁ := sdRootArc hN.1 hN.2 hX
  have hsf₁ : N.graph.source f₁ = ρ := (sdRootArc_spec hN.1 hN.2 hX).1
  obtain ⟨x, hx, y, hy, t, P₁, P₂, ⟨S₁, S₂, ⟨h₁, h₂⟩, hS⟩, hgP, hbelow⟩ := h17 _ hg.1 hg.2
  have h₁' : IsDPath N.graph t (N.leaf x) S₁ P₁ := h₁.isSDP.isDPath_of_forall fun _ => trivial
  have h₂' : IsDPath N.graph t (N.leaf y) S₂ P₂ := h₂.isSDP.isDPath_of_forall fun _ => trivial
  have hρm : N.graph.Reaches ρ m := lsa_univ_reaches hN.1 hZ
  have hmt : N.graph.Reaches m t := by
    rcases hgP with h | h
    · obtain ⟨e₀, he₀, hs⟩ := h₁'.exists_first ⟨_, h⟩
      exact hs ▸ hbelow e₀ (Or.inl he₀)
    · obtain ⟨e₀, he₀, hs⟩ := h₂'.exists_first ⟨_, h⟩
      exact hs ▸ hbelow e₀ (Or.inr he₀)
  have hρS : ∀ s ∈ S₁ ∪ S₂, N.graph.Reaches ρ s := by
    rintro s (hs | hs)
    · exact hρm.trans (hmt.trans (h₁'.reaches_of_mem hs).1)
    · exact hρm.trans (hmt.trans (h₂'.reaches_of_mem hs).1)
  have hleaf : ∀ z, N.leaf z ≠ ρ := fun z =>
    IsStableAncestor.leaf_ne hN.1 Set.nontrivial_univ
      (lsa_spec hN.1 Set.univ Set.univ_nonempty).1 z
  by_cases htρ : t = ρ
  · -- the top is `LSA(X)`: the trek starts with the two arcs out of it
    rw [htρ] at h₁' h₂' hS
    obtain ⟨fa, S₁', P₁', hfa, h₁'', rfl, rfl, hρ₁⟩ := h₁'.exists_cons hAN (hleaf x).symm
    obtain ⟨fb, S₂', P₂', hfb, h₂'', rfl, rfl, hρ₂⟩ := h₂'.exists_cons hAN (hleaf y).symm
    have hdisj : S₁' ∩ S₂' = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun s ⟨hs₁, hs₂⟩ => ?_
      have : s = ρ := (Set.eq_singleton_iff_unique_mem.mp hS).2 s
        ⟨Set.mem_insert_of_mem _ hs₁, Set.mem_insert_of_mem _ hs₂⟩
      exact hρ₁ (this ▸ hs₁)
    have hfab : fa ≠ fb := by
      rintro rfl
      have : N.graph.target fa ∈ S₁' ∩ S₂' := ⟨h₁''.start_mem, h₂''.start_mem⟩
      rw [hdisj] at this
      exact absurd this (Set.notMem_empty _)
    have hρS' : ∀ s ∈ S₁' ∪ S₂', N.graph.Reaches ρ s := fun s hs =>
      hρS s (hs.imp (Set.mem_insert_of_mem _) (Set.mem_insert_of_mem _))
    have hf₁ : fa = f₁ ∨ fb = f₁ := by
      by_contra h
      push Not at h
      exact not_three_of_outdegree_eq_two (lsa_univ_outdegree hN.1 hN.2) hfa hfb hsf₁ hfab h.1 h.2
    rcases hf₁ with rfl | rfl
    · exact mem_trekEdges_of_root hN hX hx hy hfb hfab h₁'' h₂'' hρ₁ hρ₂ hdisj hρS' g hgP
    · obtain ⟨x', hx', y', hy', t', Q₁, Q₂, htrek, hgQ⟩ := mem_trekEdges_of_root hN hX hy hx hfa
        hfab.symm h₂'' h₁'' hρ₂ hρ₁ (by rw [Set.inter_comm]; exact hdisj)
        (fun s hs => hρS' s hs.symm) g (by rw [Set.union_comm]; exact hgP)
      exact ⟨x', hx', y', hy', t', Q₁, Q₂, htrek, hgQ⟩
  · -- otherwise the trek is a trek of `N⁻`
    have hne : ∀ s ∈ S₁ ∪ S₂, s ≠ ρ := by
      rintro s hs rfl
      have hts : N.graph.Reaches t ρ := by
        rcases hs with hs | hs
        · exact (h₁'.reaches_of_mem hs).1
        · exact (h₂'.reaches_of_mem hs).1
      exact htρ (eq_of_reaches_of_reaches hAN hts (hρm.trans hmt))
    have hlift : ∀ e ∈ P₁ ∪ P₂, ∃ e', sdArc hN.1 hN.2 hX e' = e ∧
        N.graph.source e = sdVert hN.1 hX (G.graph.source e') ∧
          N.graph.target e = sdVert hN.1 hX (G.graph.target e') := by
      intro e he
      have hse : N.graph.source e ∈ S₁ ∪ S₂ := he.elim (fun h => Or.inl (h₁'.ends_mem h).1)
        (fun h => Or.inr (h₂'.ends_mem h).1)
      obtain ⟨e', rfl⟩ := (mem_range_sdArc hN.1 hN.2 hX e).mpr
        ⟨hρS _ hse, fun h' => hne _ hse (h' ▸ hsf₁)⟩
      exact ⟨e', rfl, (sdVert_source_of_ne hN hX e' (hne _ hse)).symm, rfl⟩
    obtain ⟨tv, htv⟩ := (mem_range_sdVert hN.1 hX t).mpr ⟨hρm.trans hmt, htρ⟩
    have pb₁ := h₁'.pullback (sdVert hN.1 hX) (sdArc hN.1 hN.2 hX) (sdVert_injective hN.1 hX)
      (sdArc_injective hN.1 hN.2 hX) (fun e he => hlift e (Or.inl he)) htv (w' := G.leaf x) rfl
    have pb₂ := h₂'.pullback (sdVert hN.1 hX) (sdArc hN.1 hN.2 hX) (sdVert_injective hN.1 hX)
      (sdArc_injective hN.1 hN.2 hX) (fun e he => hlift e (Or.inr he)) htv (w' := G.leaf y) rfl
    refine ⟨x, hx, y, hy, tv, _, _, ⟨_, _, ⟨pb₁.isSDPath hA rfl, pb₂.isSDPath hA rfl⟩, ?_⟩, hgP⟩
    rw [← Set.preimage_inter, hS]
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => sdVert_injective hN.1 hX (h.trans htv.symm), fun h => h ▸ htv⟩

/-- **The edges of `N⁻` on simple treks between taxa of `Z`** are those of the LSA network `N⊕_Z`
before suppression (the step `M' = K` of the proof of Proposition 1; `h17` is Lemma 17). -/
theorem mem_trekEdges_iff {Z : Set X} (hZ : Z.Nonempty)
    (h17 : ∀ e : E, N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source e) →
      (∃ z ∈ Z, N.graph.Reaches (N.graph.target e) (N.leaf z)) →
      ∃ x ∈ Z, ∃ y ∈ Z, ∃ t P₁ P₂, IsSimpleTrek (⟨N.graph, fun _ => True, N.leaf⟩ :
        SemidirectedNetwork V E X) (N.leaf x) (N.leaf y) t P₁ P₂ ∧ e ∈ P₁ ∪ P₂ ∧
        ∀ f ∈ P₁ ∪ P₂, N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source f))
    (g : SemidirectedArc hN.1 hN.2 hX) :
    g ∈ trekEdges (semidirected hN.1 hN.2 hX) Z ↔
      sdArc hN.1 hN.2 hX g ∈ N.belowArcs (lsa hN.1 Z hZ) Z :=
  ⟨mem_belowArcs_of_mem_trekEdges hN hX hZ g, mem_trekEdges_of_mem_belowArcs hN hX hZ h17 g⟩

end Network

end Banos2019
