module

public import Banos2019.Quartet.DisjointNet
public import Banos2019.Quartet.SemidirectedCycles
public import Banos2019.Network.SuppressMetric
public import Banos2019.Quartet.RootedIsoUnrooted

/-!
# The unrooted network of `Q_a⊕`

For a hybrid node `w` of a semidirected network `G` with hybrid edges `h₁`, `h₂`, `cutSD G w h₁ h₂ a b`
is `G` without the nodes joined to `w` by paths avoiding `h₁` and `h₂` (`CutReach`), with `h₁` and `h₂`
ending at two new leaves labelled `a` and `b`, as tree edges. An isomorphism of semidirected networks
keeps `CutReach` (`SDIso.cutReach_iff`) and, when `h₁` and `h₂` are hybrid, maps the cut network to the
network cut at the images (`SDMetricIso.nonempty_cutSD_of_isDirected`).

For a binary level-1 network `Q` whose root is the LSA of its taxa, the nodes of `Q⁻` joined to a
hybrid node `w` avoiding its hybrid edges are those below `w` in `Q` (`cutReach_semidirected_iff`: the
arcs entering the part below `w` enter `w`, `isCut_hybrid`), and the unrooted network of
`Q_a⊕ = disjointNet Q w h₁ h₂ a b` is `cutSD Q⁻ w h₁ h₂ a b` (`nonempty_sdMetricIso_disjointNet_cutSD`):
its nodes are the nodes of `Q⁻` not below `w` and the two new leaves, and its edges the arcs of `Q`
out of these nodes, the two arcs at the root merged, possibly in the other order than in `Q⁻`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace Banos2019

variable {V E X V' E' : Type*}

/-- The nodes joined to `w` by a path of the undirected graph avoiding the edges `h₁` and `h₂`. -/
def CutReach (G : SemidirectedNetwork V E X) (h₁ h₂ : E) (w : V) : V → Prop :=
  Relation.ReflTransGen (fun u u' => ∃ g, g ≠ h₁ ∧ g ≠ h₂ ∧ Joins G.graph g u u') w

/-- **`G` cut below `w`**: without the nodes joined to `w` avoiding `h₁` and `h₂`, the edges `h₁` and
`h₂` ending at two new leaves, labelled `a` and `b`, as tree edges. -/
def cutSD (G : SemidirectedNetwork V E X) (w : V) (h₁ h₂ : E) (a b : X) :
    SemidirectedNetwork ({u // ¬ CutReach G h₁ h₂ w u} ⊕ Fin 2)
      {g // ¬ CutReach G h₁ h₂ w (G.graph.source g)} X where
  graph :=
    { source := fun g => .inl ⟨G.graph.source g.1, g.2⟩
      target := fun g => if g.1 = h₁ then .inr 0 else if g.1 = h₂ then .inr 1 else
        if hr : CutReach G h₁ h₂ w (G.graph.target g.1) then .inr 0 else .inl ⟨_, hr⟩ }
  IsDirected g := G.IsDirected g.1 ∧ g.1 ≠ h₁ ∧ g.1 ≠ h₂
  leaf x := if x = a then .inr 0 else if x = b then .inr 1 else
    if hr : CutReach G h₁ h₂ w (G.leaf x) then .inr 0 else .inl ⟨_, hr⟩

/-- An edge other than `h₁`, `h₂` has both ends joined to `w` avoiding `h₁`, `h₂`, or none. -/
theorem cutReach_source_iff_target {G : SemidirectedNetwork V E X} {h₁ h₂ : E} {w : V} {g : E}
    (hg₁ : g ≠ h₁) (hg₂ : g ≠ h₂) :
    CutReach G h₁ h₂ w (G.graph.source g) ↔ CutReach G h₁ h₂ w (G.graph.target g) :=
  ⟨fun h => h.tail ⟨g, hg₁, hg₂, Or.inl ⟨rfl, rfl⟩⟩,
    fun h => h.tail ⟨g, hg₁, hg₂, Or.inr ⟨rfl, rfl⟩⟩⟩

theorem SDIso.cutReach_of {G : SemidirectedNetwork V E X} {G' : SemidirectedNetwork V' E' X}
    (ι : SDIso G G') {h₁ h₂ : E} {w u : V} (h : CutReach G h₁ h₂ w u) :
    CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) (ι.vert u) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨g, hg₁, hg₂, hj⟩ := hs
    exact ih.tail ⟨ι.edge g, ι.edge.injective.ne hg₁, ι.edge.injective.ne hg₂,
      ι.joins_of_joins hj⟩

/-- **An isomorphism keeps the nodes joined to `w` avoiding `h₁` and `h₂`.** -/
theorem SDIso.cutReach_iff {G : SemidirectedNetwork V E X} {G' : SemidirectedNetwork V' E' X}
    (ι : SDIso G G') (h₁ h₂ : E) (w u : V) :
    CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) (ι.vert u) ↔ CutReach G h₁ h₂ w u := by
  refine ⟨fun h => ?_, ι.cutReach_of⟩
  have := ι.symm.cutReach_of h
  simpa [SDIso.symm] using this

/-- **An isomorphism maps `G` cut below `w` to `G'` cut below the image of `w`**, when the edges
`h₁`, `h₂` are hybrid. -/
theorem SDMetricIso.nonempty_cutSD_of_isDirected {G : SemidirectedNetwork V E X}
    {θ : MetricData E} {G' : SemidirectedNetwork V' E' X} {θ' : MetricData E'}
    (ι : SDMetricIso G θ G' θ') (w : V) {h₁ h₂ : E} (hd₁ : G.IsDirected h₁)
    (hd₂ : G.IsDirected h₂) (a b : X) :
    Nonempty (SDMetricIso (cutSD G w h₁ h₂ a b) (restrictMetric θ _)
      (cutSD G' (ι.vert w) (ι.edge h₁) (ι.edge h₂) a b) (restrictMetric θ' _)) := by
  have hc := ι.cutReach_iff h₁ h₂ w
  -- the sources of the edges of the cut network
  have hsrc : ∀ g, ¬ CutReach G h₁ h₂ w (G.graph.source g) ↔
      ¬ CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) (G'.graph.source (ι.edge g)) := by
    intro g
    refine not_congr ?_
    by_cases hg : g = h₁ ∨ g = h₂
    · have hd : G.IsDirected g := by rcases hg with rfl | rfl <;> assumption
      rw [(ι.directed g hd).1, hc]
    · push Not at hg
      rcases ι.joins g with ⟨h₁', -⟩ | ⟨h₁', -⟩
      · rw [h₁', hc]
      · rw [h₁', hc, cutReach_source_iff_target hg.1 hg.2]
  let vert : ({u // ¬ CutReach G h₁ h₂ w u} ⊕ Fin 2) ≃
      ({u // ¬ CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) u} ⊕ Fin 2) :=
    Equiv.sumCongr (ι.vert.subtypeEquiv fun u => not_congr (hc u).symm) (Equiv.refl _)
  let edge : {g // ¬ CutReach G h₁ h₂ w (G.graph.source g)} ≃
      {g // ¬ CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) (G'.graph.source g)} :=
    ι.edge.subtypeEquiv hsrc
  have hvert : ∀ (u : V) (hu : ¬ CutReach G h₁ h₂ w u),
      vert (.inl ⟨u, hu⟩) = .inl ⟨ι.vert u, (not_congr (hc u)).2 hu⟩ := fun _ _ => rfl
  -- the targets of the edges other than `h₁`, `h₂`
  have htgt : ∀ (g : {g // ¬ CutReach G h₁ h₂ w (G.graph.source g)}), g.1 ≠ h₁ → g.1 ≠ h₂ →
      ∃ ht : ¬ CutReach G h₁ h₂ w (G.graph.target g.1),
        (cutSD G w h₁ h₂ a b).graph.target g = .inl ⟨_, ht⟩ := by
    intro g hg₁ hg₂
    have ht : ¬ CutReach G h₁ h₂ w (G.graph.target g.1) :=
      (not_congr (cutReach_source_iff_target hg₁ hg₂)).1 g.2
    exact ⟨ht, by simp [cutSD, hg₁, hg₂, ht]⟩
  have htgt' : ∀ (g : {g // ¬ CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) (G'.graph.source g)}),
      g.1 ≠ ι.edge h₁ → g.1 ≠ ι.edge h₂ →
      ∃ ht : ¬ CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) (G'.graph.target g.1),
        (cutSD G' (ι.vert w) (ι.edge h₁) (ι.edge h₂) a b).graph.target g = .inl ⟨_, ht⟩ := by
    intro g hg₁ hg₂
    have ht : ¬ CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) (G'.graph.target g.1) :=
      (not_congr (cutReach_source_iff_target hg₁ hg₂)).1 g.2
    exact ⟨ht, by simp [cutSD, hg₁, hg₂, ht]⟩
  have hs_eq : ∀ g : {g // ¬ CutReach G h₁ h₂ w (G.graph.source g)},
      G'.graph.source (ι.edge g.1) = ι.vert (G.graph.source g.1) →
      (cutSD G' (ι.vert w) (ι.edge h₁) (ι.edge h₂) a b).graph.source (edge g) =
        vert ((cutSD G w h₁ h₂ a b).graph.source g) := fun g h =>
    congrArg Sum.inl (Subtype.ext h)
  refine ⟨⟨⟨vert, edge, fun g => ?_, fun g => ?_, fun g hg => ?_, fun x => ?_⟩, fun g => ?_,
    fun g hg => ?_⟩⟩
  · change (G'.IsDirected (ι.edge g.1) ∧ ι.edge g.1 ≠ ι.edge h₁ ∧ ι.edge g.1 ≠ ι.edge h₂) ↔
      (G.IsDirected g.1 ∧ g.1 ≠ h₁ ∧ g.1 ≠ h₂)
    rw [ι.isDirected_iff, ι.edge.injective.ne_iff, ι.edge.injective.ne_iff]
  · by_cases hg₁ : g.1 = h₁
    · have hs := (ι.directed g.1 (by rw [hg₁]; exact hd₁)).1
      refine Or.inl ⟨hs_eq g hs, ?_⟩
      change _ = vert ((cutSD G w h₁ h₂ a b).graph.target g)
      simp [cutSD, hg₁, vert, edge]
    by_cases hg₂ : g.1 = h₂
    · have hs := (ι.directed g.1 (by rw [hg₂]; exact hd₂)).1
      refine Or.inl ⟨hs_eq g hs, ?_⟩
      change _ = vert ((cutSD G w h₁ h₂ a b).graph.target g)
      have hne₁ : ι.edge h₂ ≠ ι.edge h₁ := fun h => hg₁ (hg₂.trans (ι.edge.injective h))
      have hh : ¬ h₂ = h₁ := fun h => hg₁ (hg₂.trans h)
      simp [cutSD, hg₂, vert, edge, hh, hne₁]
    obtain ⟨ht, hgt⟩ := htgt g hg₁ hg₂
    obtain ⟨ht', hgt'⟩ := htgt' (edge g) (ι.edge.injective.ne hg₁) (ι.edge.injective.ne hg₂)
    unfold Joins
    rw [hgt, hgt']
    rcases ι.joins g.1 with ⟨hs, htt⟩ | ⟨hs, htt⟩
    · exact Or.inl ⟨hs_eq g hs, congrArg Sum.inl (Subtype.ext htt)⟩
    · exact Or.inr ⟨congrArg Sum.inl (Subtype.ext hs), congrArg Sum.inl (Subtype.ext htt)⟩
  · obtain ⟨hd, hg₁, hg₂⟩ := hg
    obtain ⟨hs, htt⟩ := ι.directed g.1 hd
    obtain ⟨ht, hgt⟩ := htgt g hg₁ hg₂
    obtain ⟨ht', hgt'⟩ := htgt' (edge g) (ι.edge.injective.ne hg₁) (ι.edge.injective.ne hg₂)
    refine ⟨hs_eq g hs, ?_⟩
    rw [hgt, hgt']
    exact congrArg Sum.inl (Subtype.ext htt)
  · change (if x = a then _ else _) = vert (if x = a then _ else _)
    by_cases hxa : x = a
    · simp [hxa, vert]
    by_cases hxb : x = b
    · subst hxb
      simp [hxa, vert]
    simp only [hxa, hxb, ↓reduceIte]
    by_cases hx : CutReach G h₁ h₂ w (G.leaf x)
    · have hx' : CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) (G'.leaf x) := by
        rw [ι.leaf, hc]; exact hx
      simp [hx, hx', vert]
    · have hx' : ¬ CutReach G' (ι.edge h₁) (ι.edge h₂) (ι.vert w) (G'.leaf x) := by
        rw [ι.leaf, hc]; exact hx
      simp only [hx, hx', ↓reduceDIte]
      exact congrArg Sum.inl (Subtype.ext (ι.leaf x))
  · exact ι.length g.1
  · exact ι.inheritance g.1 hg.1

section Semidirected

variable {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q) (hX : Nontrivial X)
  (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root)
include hQ hr

/-- The target of a hybrid edge of `Q⁻` has indegree two in `Q`. -/
theorem cutSD_indegree_eq_two {w : SemidirectedVertex hQ.1 hX}
    {h₁ : SemidirectedArc hQ.1 hQ.2 hX} (hd₁ : (semidirected hQ.1 hQ.2 hX).IsDirected h₁)
    (ht₁ : (semidirected hQ.1 hQ.2 hX).graph.target h₁ = w) :
    Q.graph.indegree (sdVert hQ.1 hX w) = 2 := by
  have hH₁ : Q.graph.target (sdArc hQ.1 hQ.2 hX h₁) = sdVert hQ.1 hX w :=
    (sdVert_target hQ.1 hQ.2 hX h₁).symm.trans (congrArg _ ht₁)
  have hvr : sdVert hQ.1 hX w ≠ Q.root := by
    rw [← hr]
    exact sdVert_ne_lsa hQ.1 hX w
  have hge : 2 ≤ Q.graph.indegree (sdVert hQ.1 hX w) := by
    have := (semidirected_isDirected_iff hQ.1 hQ.2 hX h₁).1 hd₁
    unfold IsHybridArc at this
    rwa [hH₁] at this
  have h0 : Q.graph.outdegree (sdVert hQ.1 hX w) ≠ 0 := fun h0 => by
    obtain ⟨x, hx⟩ := (hQ.1.leaves _).1 h0
    have := hQ.1.leaf_indegree x
    rw [hx] at this
    omega
  have h3 := hQ.2.2 _ hvr h0
  omega

omit hr in
/-- The arc of `Q` that `Q⁻` merges does not enter a node of indegree two. -/
theorem cutSD_target_sdRootArc_ne {v : V} (h2 : Q.graph.indegree v = 2) :
    Q.graph.target (sdRootArc hQ.1 hQ.2 hX) ≠ v := fun h => by
  have := (sdRootArc_spec hQ.1 hQ.2 hX).2
  unfold IsTreeArc at this
  rw [h, h2] at this
  omega

/-- **The nodes of `Q⁻` joined to a hybrid node `w` avoiding its hybrid edges are those below `w` in
`Q`.** -/
theorem cutReach_semidirected_iff (h1 : IsLevelOne Q.graph) {w : SemidirectedVertex hQ.1 hX}
    {h₁ h₂ : SemidirectedArc hQ.1 hQ.2 hX} (hne : h₁ ≠ h₂)
    (hd₁ : (semidirected hQ.1 hQ.2 hX).IsDirected h₁)
    (ht₁ : (semidirected hQ.1 hQ.2 hX).graph.target h₁ = w)
    (ht₂ : (semidirected hQ.1 hQ.2 hX).graph.target h₂ = w) (u : SemidirectedVertex hQ.1 hX) :
    CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w u ↔
      Q.graph.Reaches (sdVert hQ.1 hX w) (sdVert hQ.1 hX u) := by
  have h2 := cutSD_indegree_eq_two hQ hX hr hd₁ ht₁
  have hH₁ : Q.graph.target (sdArc hQ.1 hQ.2 hX h₁) = sdVert hQ.1 hX w :=
    (sdVert_target hQ.1 hQ.2 hX h₁).symm.trans (congrArg _ ht₁)
  have hH₂ : Q.graph.target (sdArc hQ.1 hQ.2 hX h₂) = sdVert hQ.1 hX w :=
    (sdVert_target hQ.1 hQ.2 hX h₂).symm.trans (congrArg _ ht₂)
  have hneH : sdArc hQ.1 hQ.2 hX h₁ ≠ sdArc hQ.1 hQ.2 hX h₂ := fun h =>
    hne (sdArc_injective _ _ _ h)
  have hcut := isCut_hybrid hQ h1 h2
  have hpar := hpar_of_hybrid hQ h2 hneH hH₁ hH₂
  have heR : Q.graph.source (sdRootArc hQ.1 hQ.2 hX) = Q.root :=
    (sdRootArc_spec hQ.1 hQ.2 hX).1.trans hr
  have heRt := cutSD_target_sdRootArc_ne hQ hX h2
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail x y _ hs ih =>
      obtain ⟨g, hg₁, hg₂, hj⟩ := hs
      rcases hj with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · rcases sdVert_source_cases hQ.1 hQ.2 hX g with ⟨-, hsrc⟩ | ⟨-, hsrc⟩
        · rw [hs] at hsrc
          rw [← ht, sdVert_target]
          exact ih.tail ⟨_, hsrc.symm, rfl⟩
        · rw [hs] at hsrc
          rw [hsrc] at ih
          have := hcut.entry _ ih heRt
          rw [heR] at this
          exact absurd this hcut.not_reaches_root
      · rw [← ht, sdVert_target] at ih
        by_cases hv : Q.graph.target (sdArc hQ.1 hQ.2 hX g) = sdVert hQ.1 hX w
        · rcases hpar _ hv with h | h
          · exact absurd (sdArc_injective _ _ _ h) hg₁
          · exact absurd (sdArc_injective _ _ _ h) hg₂
        · have := hcut.entry _ ih hv
          rcases sdVert_source_cases hQ.1 hQ.2 hX g with ⟨-, hsrc⟩ | ⟨hm, -⟩
          · rw [← hs, hsrc]
            exact this
          · rw [hm, hr] at this
            exact absurd this hcut.not_reaches_root
  · intro h
    suffices H : ∀ t, Q.graph.Reaches (sdVert hQ.1 hX w) t → ∀ u : SemidirectedVertex hQ.1 hX,
        sdVert hQ.1 hX u = t → CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w u from H _ h u rfl
    intro t ht
    induction ht with
    | refl =>
      intro u hu
      rw [sdVert_injective hQ.1 hX hu]
      exact .refl
    | @tail z t hz hzt ih =>
      intro u hu
      obtain ⟨f, hfs, hft⟩ := hzt
      have hzr : z ≠ Q.root := fun h => hcut.not_reaches_root (h ▸ hz)
      obtain ⟨u', hu'⟩ := exists_sdVert_of_ne hQ.1 hX hr hzr
      have hfr : Q.graph.source f ≠ Q.root := hfs ▸ hzr
      obtain ⟨g, hgf, hgs, hgt⟩ := exists_sdArc_of_ne hQ.1 hQ.2 hX hr hfr
      have hgh : ∀ k, sdArc hQ.1 hQ.2 hX k = f →
          Q.graph.target (sdArc hQ.1 hQ.2 hX k) = sdVert hQ.1 hX w → False := fun k hk hkt =>
        hQ.1.acyclic _ (Relation.TransGen.tail' hz ⟨f, hfs, hk ▸ hkt⟩)
      have hg₁ : g ≠ h₁ := by
        rintro rfl
        exact hgh g hgf hH₁
      have hg₂ : g ≠ h₂ := by
        rintro rfl
        exact hgh g hgf hH₂
      exact (ih u' hu').tail ⟨g, hg₁, hg₂, Or.inl
        ⟨sdVert_injective hQ.1 hX (hgs.trans (hfs.trans hu'.symm)),
          sdVert_injective hQ.1 hX (hgt.trans (hft.trans hu.symm))⟩⟩

end Semidirected

/-- **The unrooted network of `Q_a⊕` is `Q⁻` cut below the hybrid node.** -/
theorem nonempty_sdMetricIso_disjointNet_cutSD {Q : RootedNetwork V E X}
    (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph) (hX : Nontrivial X)
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root) (θ : MetricData E)
    {w : SemidirectedVertex hQ.1 hX} {h₁ h₂ : SemidirectedArc hQ.1 hQ.2 hX} (hne : h₁ ≠ h₂)
    (hd₁ : (semidirected hQ.1 hQ.2 hX).IsDirected h₁)
    (ht₁ : (semidirected hQ.1 hQ.2 hX).graph.target h₁ = w)
    (ht₂ : (semidirected hQ.1 hQ.2 hX).graph.target h₂ = w) {a b : X} (hab : a ≠ b)
    (hb : IsBinaryRootedNetwork (disjointNet Q (sdVert hQ.1 hX w) (sdArc hQ.1 hQ.2 hX h₁)
      (sdArc hQ.1 hQ.2 hX h₂) a b))
    (hl : (disjointNet Q (sdVert hQ.1 hX w) (sdArc hQ.1 hQ.2 hX h₁)
      (sdArc hQ.1 hQ.2 hX h₂) a b).IsLSANetwork) :
    Nonempty (SDMetricIso (unrooted _ hb hX)
      (unrootedMetric _ hb hX (disjointMetric Q (sdVert hQ.1 hX w) (sdArc hQ.1 hQ.2 hX h₁)
        (sdArc hQ.1 hQ.2 hX h₂) θ))
      (cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b)
      (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _)) := by
  classical
  have h2 := cutSD_indegree_eq_two hQ hX hr hd₁ ht₁
  have cr := cutReach_semidirected_iff hQ hX hr h1 hne hd₁ ht₁ ht₂
  have heRt := cutSD_target_sdRootArc_ne hQ hX h2
  have hH₁ : Q.graph.target (sdArc hQ.1 hQ.2 hX h₁) = sdVert hQ.1 hX w :=
    (sdVert_target hQ.1 hQ.2 hX h₁).symm.trans (congrArg _ ht₁)
  have hH₂ : Q.graph.target (sdArc hQ.1 hQ.2 hX h₂) = sdVert hQ.1 hX w :=
    (sdVert_target hQ.1 hQ.2 hX h₂).symm.trans (congrArg _ ht₂)
  have hneH : sdArc hQ.1 hQ.2 hX h₁ ≠ sdArc hQ.1 hQ.2 hX h₂ := fun h =>
    hne (sdArc_injective _ _ _ h)
  have hcut := isCut_hybrid hQ h1 h2
  have heR : Q.graph.source (sdRootArc hQ.1 hQ.2 hX) = Q.root :=
    (sdRootArc_spec hQ.1 hQ.2 hX).1.trans hr
  have heRnh : ¬ Q.IsHybridArc (sdRootArc hQ.1 hQ.2 hX) := fun h => by
    have := (sdRootArc_spec hQ.1 hQ.2 hX).2
    unfold IsTreeArc at this
    unfold IsHybridArc at h
    omega
  have heRreach : ¬ Q.graph.Reaches (sdVert hQ.1 hX w)
      (Q.graph.target (sdRootArc hQ.1 hQ.2 hX)) := fun h => by
    have := hcut.entry _ h heRt
    rw [heR] at this
    exact hcut.not_reaches_root this
  have csrc : ∀ g, CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w
      ((semidirected hQ.1 hQ.2 hX).graph.source g) ↔
      Q.graph.Reaches (sdVert hQ.1 hX w) (Q.graph.source (sdArc hQ.1 hQ.2 hX g)) := by
    intro g
    rcases sdVert_source_cases hQ.1 hQ.2 hX g with ⟨-, hs⟩ | ⟨hm, hs⟩
    · rw [cr, hs]
    · rw [cr, hs, hm, hr]
      exact iff_of_false heRreach hcut.not_reaches_root
  have cleaf : ∀ x, CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w
      ((semidirected hQ.1 hQ.2 hX).leaf x) ↔ Q.graph.Reaches (sdVert hQ.1 hX w) (Q.leaf x) :=
    fun x => by rw [cr, sdVert_leaf]
  -- the root arcs of `Q`
  have hroot2 : ∀ f g k : E, f ≠ g → Q.graph.source f = Q.root → Q.graph.source g = Q.root →
      Q.graph.source k = Q.root → k = f ∨ k = g := by
    intro f g k hfg hf hg hk
    obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 hQ.2.1
    have m : ∀ z, Q.graph.source z = Q.root → z = x ∨ z = y := fun z hz => by
      have : z ∈ {e | Q.graph.source e = Q.root} := hz
      rw [hs] at this
      simpa using this
    rcases m f hf with r1 | r1 <;> rcases m g hg with r2 | r2 <;> rcases m k hk with r3 | r3 <;>
      subst_vars <;> simp_all
  generalize hv : sdVert hQ.1 hX w = v at hb hl cr heRt h2 hH₁ hH₂ hcut heRreach csrc cleaf ⊢
  generalize hE₁ : sdArc hQ.1 hQ.2 hX h₁ = H₁ at hb hl hH₁ hneH ⊢
  generalize hE₂ : sdArc hQ.1 hQ.2 hX h₂ = H₂ at hb hl hH₂ hneH ⊢
  have hρ : ¬ Q.graph.Reaches v Q.root := hcut.not_reaches_root
  have hrN : lsa hb.1 Set.univ Set.univ_nonempty = (disjointNet Q v H₁ H₂ a b).root :=
    lsa_univ_eq_root hb.1 hX hl
  have hNroot : (disjointNet Q v H₁ H₂ a b).root = .inl ⟨Q.root, hρ⟩ := disjointNet_root hρ
  have hleafA : (disjointNet Q v H₁ H₂ a b).leaf a = .inr 0 := disjointNet_leaf_a
  have hleafB : (disjointNet Q v H₁ H₂ a b).leaf b = .inr 1 := disjointNet_leaf_b hab
  have hin : ∀ i : Fin 2, (disjointNet Q v H₁ H₂ a b).graph.indegree (.inr i) = 1 := by
    intro i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · rw [← hleafA]
      exact hb.1.leaf_indegree a
    · rw [← hleafB]
      exact hb.1.leaf_indegree b
  have hybN : ∀ z, (disjointNet Q v H₁ H₂ a b).IsHybridArc z ↔
      z.1 ≠ H₁ ∧ z.1 ≠ H₂ ∧ Q.IsHybridArc z.1 := by
    intro z
    unfold IsHybridArc
    by_cases hz₁ : z.1 = H₁
    · rw [disjointNet_target_h₁ (h₂ := H₂) (a := a) (b := b) z hz₁, hin]
      simp [hz₁]
    by_cases hz₂ : z.1 = H₂
    · rw [disjointNet_target_h₂ (a := a) (b := b) hneH z hz₂, hin]
      simp [hz₂]
    obtain ⟨hz, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hneH hH₁ hH₂ (a := a) (b := b) z hz₁ hz₂
    rw [ht, disjointNet_indegree_inl hQ h1 h2 hneH hH₁ hH₂ (a := a) (b := b)]
    simp [hz₁, hz₂]
  have hsrcRoot : ∀ z : {e // ¬ Q.graph.Reaches v (Q.graph.source e)},
      (disjointNet Q v H₁ H₂ a b).graph.source z = lsa hb.1 Set.univ Set.univ_nonempty ↔
        Q.graph.source z.1 = Q.root := by
    intro z
    rw [hrN, hNroot]
    show (Sum.inl ⟨Q.graph.source z.1, z.2⟩ : {u // ¬ Q.graph.Reaches v u} ⊕ Fin 2) = _ ↔ _
    exact ⟨fun h => congrArg Subtype.val (Sum.inl_injective h),
      fun h => congrArg Sum.inl (Subtype.ext h)⟩
  -- the nodes
  let ν : ({u // ¬ CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w u} ⊕ Fin 2) →
      ({u // ¬ Q.graph.Reaches v u} ⊕ Fin 2) :=
    Sum.elim (fun u => .inl ⟨sdVert hQ.1 hX u.1, (not_congr (cr u.1)).1 u.2⟩) Sum.inr
  have hνne : ∀ s, ν s ≠ (disjointNet Q v H₁ H₂ a b).root := by
    rw [hNroot]
    rintro (⟨u, hu⟩ | i) h
    · have := congrArg Subtype.val (Sum.inl_injective h)
      exact sdVert_ne_lsa hQ.1 hX u (this.trans hr.symm)
    · exact Sum.inr_ne_inl h
  have hνinj : Function.Injective ν := by
    rintro (⟨u, hu⟩ | i) (⟨u', hu'⟩ | i') h
    · have := congrArg Subtype.val (Sum.inl_injective h)
      obtain rfl := sdVert_injective hQ.1 hX this
      rfl
    · exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inr_ne_inl
    · rw [Sum.inr_injective h]
  let vertFun : ({u // ¬ CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w u} ⊕ Fin 2) →
      SemidirectedVertex hb.1 hX := fun s =>
    (sdVertEquiv hb.1 hX).symm ⟨ν s, by rw [hrN]; exact ⟨hb.1.root_reaches _, hνne s⟩⟩
  have hvf : ∀ s, sdVert hb.1 hX (vertFun s) = ν s := fun s => sdVert_sdVertEquiv_symm hb.1 hX _
  have hvbij : Function.Bijective vertFun := by
    refine ⟨fun s s' h => hνinj ((hvf s).symm.trans ((congrArg (sdVert hb.1 hX) h).trans
      (hvf s'))), fun y => ?_⟩
    have hy : sdVert hb.1 hX y ≠ (disjointNet Q v H₁ H₂ a b).root := by
      rw [← hrN]
      exact sdVert_ne_lsa hb.1 hX y
    rcases hyy : sdVert hb.1 hX y with ⟨x, hx⟩ | i
    · have hxr : x ≠ Q.root := fun h =>
        hy (by rw [hyy, hNroot]; exact congrArg Sum.inl (Subtype.ext h))
      obtain ⟨u, hu⟩ := exists_sdVert_of_ne hQ.1 hX hr hxr
      have hu' : ¬ CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w u := by
        rw [cr, hu]
        exact hx
      refine ⟨.inl ⟨u, hu'⟩, sdVert_injective hb.1 hX ?_⟩
      rw [hvf, hyy]
      exact congrArg Sum.inl (Subtype.ext hu)
    · exact ⟨.inr i, sdVert_injective hb.1 hX (by rw [hvf, hyy]; rfl)⟩
  let vert := Equiv.ofBijective vertFun hvbij
  have hvert : ∀ s, sdVert hb.1 hX (vert s) = ν s := hvf
  have key : ∀ (s : {u // ¬ CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w u} ⊕ Fin 2)
      (y : SemidirectedVertex hb.1 hX), sdVert hb.1 hX y = ν s → y = vert s := fun s y h =>
    sdVert_injective hb.1 hX (h.trans (hvert s).symm)
  -- the edges
  let arcN : {g // ¬ CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w
      ((semidirected hQ.1 hQ.2 hX).graph.source g)} → {e // ¬ Q.graph.Reaches v (Q.graph.source e)} :=
    fun g => ⟨sdArc hQ.1 hQ.2 hX g.1, (not_congr (csrc g.1)).1 g.2⟩
  let eRN : {e // ¬ Q.graph.Reaches v (Q.graph.source e)} :=
    ⟨sdRootArc hQ.1 hQ.2 hX, by rw [heR]; exact hρ⟩
  let τ := Equiv.swap eRN (sdRootArc hb.1 hb.2 hX)
  have harcne : ∀ g, arcN g ≠ eRN := fun g h => by
    have : sdArc hQ.1 hQ.2 hX g.1 = sdRootArc hQ.1 hQ.2 hX :=
      congrArg (fun z : {e // ¬ Q.graph.Reaches v (Q.graph.source e)} => z.1) h
    exact sdArc_ne_sdRootArc hQ.1 hQ.2 hX g.1 this
  have hτne : ∀ g, τ (arcN g) ≠ sdRootArc hb.1 hb.2 hX := fun g h => by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
    exact harcne g h
  let edgeFun : {g // ¬ CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w
      ((semidirected hQ.1 hQ.2 hX).graph.source g)} → SemidirectedArc hb.1 hb.2 hX := fun g =>
    (sdArcEquiv hb.1 hb.2 hX).symm ⟨τ (arcN g), by rw [hrN]; exact ⟨hb.1.root_reaches _, hτne g⟩⟩
  have hef : ∀ g, sdArc hb.1 hb.2 hX (edgeFun g) = τ (arcN g) := fun g =>
    sdArc_sdArcEquiv_symm hb.1 hb.2 hX _
  have hebij : Function.Bijective edgeFun := by
    refine ⟨fun g g' h => ?_, fun y => ?_⟩
    · have h' := τ.injective ((hef g).symm.trans ((congrArg _ h).trans (hef g')))
      have : sdArc hQ.1 hQ.2 hX g.1 = sdArc hQ.1 hQ.2 hX g'.1 :=
        congrArg (fun z : {e // ¬ Q.graph.Reaches v (Q.graph.source e)} => z.1) h'
      exact Subtype.ext (sdArc_injective _ _ _ this)
    · have ht : sdArc hb.1 hb.2 hX y ≠ sdRootArc hb.1 hb.2 hX := sdArc_ne_sdRootArc hb.1 hb.2 hX y
      have hz : τ (sdArc hb.1 hb.2 hX y) ≠ eRN := fun h => by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
        exact ht h
      have hz' : (τ (sdArc hb.1 hb.2 hX y)).1 ≠ sdRootArc hQ.1 hQ.2 hX := fun h =>
        hz (Subtype.ext h)
      obtain ⟨g', hg'⟩ := (mem_range_sdArc hQ.1 hQ.2 hX (τ (sdArc hb.1 hb.2 hX y)).1).2
        ⟨by rw [hr]; exact hQ.1.root_reaches _, hz'⟩
      have hg'c : ¬ CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w
          ((semidirected hQ.1 hQ.2 hX).graph.source g') := by
        rw [csrc, hg']
        exact (τ (sdArc hb.1 hb.2 hX y)).2
      refine ⟨⟨g', hg'c⟩, sdArc_injective hb.1 hb.2 hX ?_⟩
      rw [hef]
      have : arcN ⟨g', hg'c⟩ = τ (sdArc hb.1 hb.2 hX y) := Subtype.ext hg'
      rw [this, Equiv.swap_apply_self]
  let edge := Equiv.ofBijective edgeFun hebij
  have hedge : ∀ g, sdArc hb.1 hb.2 hX (edge g) = τ (arcN g) := hef
  -- the arc of `Q_a⊕` merged in its unrooted network
  have hfRsrc : Q.graph.source (sdRootArc hb.1 hb.2 hX).1 = Q.root :=
    (hsrcRoot _).1 (sdRootArc_spec hb.1 hb.2 hX).1
  have hfRnh : ¬ (disjointNet Q v H₁ H₂ a b).IsHybridArc (sdRootArc hb.1 hb.2 hX) := fun h => by
    have := (sdRootArc_spec hb.1 hb.2 hX).2
    unfold IsTreeArc at this
    unfold IsHybridArc at h
    omega
  have heRNnh : ¬ (disjointNet Q v H₁ H₂ a b).IsHybridArc eRN := fun h =>
    heRnh ((hybN eRN).1 h).2.2
  have hcases : ∀ g, (Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) ≠ Q.root ∧ τ (arcN g) = arcN g) ∨
      (Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) = Q.root ∧ sdRootArc hb.1 hb.2 hX = eRN ∧
        τ (arcN g) = arcN g) ∨
      (Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) = Q.root ∧ sdRootArc hb.1 hb.2 hX = arcN g ∧
        τ (arcN g) = eRN) := by
    intro g
    by_cases hs : Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) = Q.root
    · rcases hroot2 _ _ _ (sdArc_ne_sdRootArc hQ.1 hQ.2 hX g.1).symm heR hs hfRsrc with h | h
      · have hf : sdRootArc hb.1 hb.2 hX = eRN := Subtype.ext h
        refine Or.inr (Or.inl ⟨hs, hf, ?_⟩)
        show Equiv.swap eRN (sdRootArc hb.1 hb.2 hX) (arcN g) = arcN g
        rw [hf, Equiv.swap_self]
        rfl
      · have hf : sdRootArc hb.1 hb.2 hX = arcN g := Subtype.ext h
        refine Or.inr (Or.inr ⟨hs, hf, ?_⟩)
        show Equiv.swap eRN (sdRootArc hb.1 hb.2 hX) (arcN g) = eRN
        rw [← hf, Equiv.swap_apply_right]
    · refine Or.inl ⟨hs, Equiv.swap_apply_of_ne_of_ne (harcne g) fun h => hs ?_⟩
      exact (congrArg (fun z : {e // ¬ Q.graph.Reaches v (Q.graph.source e)} =>
        Q.graph.source z.1) h).trans hfRsrc
  -- the ends of the edges
  have hRsrc1 : ∀ g, (disjointNet Q v H₁ H₂ a b).graph.source (τ (arcN g)) ≠
      lsa hb.1 Set.univ Set.univ_nonempty →
      sdVert hb.1 hX ((semidirected hb.1 hb.2 hX).graph.source (edgeFun g)) =
        (disjointNet Q v H₁ H₂ a b).graph.source (τ (arcN g)) := fun g h => by
    rw [sdVert_source, hef, ite_eq_right h]
  have hRsrc2 : ∀ g, (disjointNet Q v H₁ H₂ a b).graph.source (τ (arcN g)) =
      lsa hb.1 Set.univ Set.univ_nonempty →
      sdVert hb.1 hX ((semidirected hb.1 hb.2 hX).graph.source (edgeFun g)) =
        (disjointNet Q v H₁ H₂ a b).graph.target (sdRootArc hb.1 hb.2 hX) := fun g h => by
    rw [sdVert_source, hef, ite_eq_left h]
  have hRtgt : ∀ g, sdVert hb.1 hX ((semidirected hb.1 hb.2 hX).graph.target (edgeFun g)) =
      (disjointNet Q v H₁ H₂ a b).graph.target (τ (arcN g)) := fun g => by
    rw [sdVert_target, hef]
  have hNtgt : ∀ g, (disjointNet Q v H₁ H₂ a b).graph.target (arcN g) =
      ν ((cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).graph.target g) := by
    intro g
    by_cases hg₁ : g.1 = h₁
    · have : (arcN g).1 = H₁ := by
        show sdArc hQ.1 hQ.2 hX g.1 = H₁
        rw [hg₁, hE₁]
      rw [disjointNet_target_h₁ (h₂ := H₂) (a := a) (b := b) (arcN g) this]
      simp [cutSD, hg₁, ν]
    by_cases hg₂ : g.1 = h₂
    · have : (arcN g).1 = H₂ := by
        show sdArc hQ.1 hQ.2 hX g.1 = H₂
        rw [hg₂, hE₂]
      have hh : ¬ h₂ = h₁ := fun h => hne h.symm
      rw [disjointNet_target_h₂ (a := a) (b := b) hneH (arcN g) this]
      simp [cutSD, hg₂, hh, ν]
    have hz₁ : (arcN g).1 ≠ H₁ := fun h => hg₁ (sdArc_injective _ _ _ (h.trans hE₁.symm))
    have hz₂ : (arcN g).1 ≠ H₂ := fun h => hg₂ (sdArc_injective _ _ _ (h.trans hE₂.symm))
    obtain ⟨hz, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hneH hH₁ hH₂ (a := a) (b := b) (arcN g)
      hz₁ hz₂
    have hS : ¬ CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w
        ((semidirected hQ.1 hQ.2 hX).graph.target g.1) :=
      (not_congr (cutReach_source_iff_target hg₁ hg₂)).1 g.2
    have hSt : (cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).graph.target g = .inl ⟨_, hS⟩ := by
      simp [cutSD, hg₁, hg₂, hS]
    rw [ht, hSt]
    exact congrArg Sum.inl (Subtype.ext (sdVert_target hQ.1 hQ.2 hX g.1).symm)
  have hNsrc : ∀ g, Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) ≠ Q.root →
      (disjointNet Q v H₁ H₂ a b).graph.source (arcN g) =
        ν ((cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).graph.source g) := by
    intro g hs
    rcases sdVert_source_cases hQ.1 hQ.2 hX g.1 with ⟨-, hs'⟩ | ⟨hm, -⟩
    · exact congrArg Sum.inl (Subtype.ext hs'.symm)
    · exact absurd (hm.trans hr) hs
  have hNsrcR : ∀ g, Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) = Q.root →
      (disjointNet Q v H₁ H₂ a b).graph.target eRN =
        ν ((cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).graph.source g) := by
    intro g hs
    have h₁' : eRN.1 ≠ H₁ := fun h => heRt (by
      rw [show sdRootArc hQ.1 hQ.2 hX = H₁ from h]
      exact hH₁)
    have h₂' : eRN.1 ≠ H₂ := fun h => heRt (by
      rw [show sdRootArc hQ.1 hQ.2 hX = H₂ from h]
      exact hH₂)
    obtain ⟨hz, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hneH hH₁ hH₂ (a := a) (b := b) eRN h₁' h₂'
    rw [ht]
    rcases sdVert_source_cases hQ.1 hQ.2 hX g.1 with ⟨hne', -⟩ | ⟨-, hs'⟩
    · exact absurd (hs.trans hr.symm) hne'
    · exact congrArg Sum.inl (Subtype.ext hs'.symm)
  have hexact : ∀ g, τ (arcN g) = arcN g →
      sdVert hb.1 hX ((semidirected hb.1 hb.2 hX).graph.source (edgeFun g)) =
        ν ((cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).graph.source g) ∧
      sdVert hb.1 hX ((semidirected hb.1 hb.2 hX).graph.target (edgeFun g)) =
        ν ((cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).graph.target g) := by
    intro g hτ
    refine ⟨?_, by rw [hRtgt, hτ]; exact hNtgt g⟩
    by_cases hs : Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) = Q.root
    · rw [hRsrc2 g (by rw [hτ]; exact (hsrcRoot _).2 hs)]
      rcases hroot2 _ _ _ (sdArc_ne_sdRootArc hQ.1 hQ.2 hX g.1).symm heR hs hfRsrc with h | h
      · rw [show sdRootArc hb.1 hb.2 hX = eRN from Subtype.ext h]
        exact hNsrcR g hs
      · have hf : sdRootArc hb.1 hb.2 hX = arcN g := Subtype.ext h
        exfalso
        apply harcne g
        rw [← hτ]
        show Equiv.swap eRN (sdRootArc hb.1 hb.2 hX) (arcN g) = eRN
        rw [← hf, Equiv.swap_apply_right]
    · rw [hRsrc1 g (by rw [hτ]; exact fun h => hs ((hsrcRoot _).1 h)), hτ]
      exact hNsrc g hs
  have hswap : ∀ g, sdRootArc hb.1 hb.2 hX = arcN g → τ (arcN g) = eRN →
      sdVert hb.1 hX ((semidirected hb.1 hb.2 hX).graph.source (edgeFun g)) =
        ν ((cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).graph.target g) ∧
      sdVert hb.1 hX ((semidirected hb.1 hb.2 hX).graph.target (edgeFun g)) =
        ν ((cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).graph.source g) := by
    intro g hf hτ
    refine ⟨?_, ?_⟩
    · rw [hRsrc2 g (by rw [hτ]; exact (hsrcRoot eRN).2 heR), hf]
      exact hNtgt g
    · rw [hRtgt, hτ]
      exact hNsrcR g (by rw [← hfRsrc, hf])
  have hSdir : ∀ g, (cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).IsDirected g ↔
      (disjointNet Q v H₁ H₂ a b).IsHybridArc (arcN g) := by
    intro g
    rw [hybN]
    change ((semidirected hQ.1 hQ.2 hX).IsDirected g.1 ∧ g.1 ≠ h₁ ∧ g.1 ≠ h₂) ↔
      (sdArc hQ.1 hQ.2 hX g.1 ≠ H₁ ∧ sdArc hQ.1 hQ.2 hX g.1 ≠ H₂ ∧
        Q.IsHybridArc (sdArc hQ.1 hQ.2 hX g.1))
    rw [semidirected_isDirected_iff, ← hE₁, ← hE₂, (sdArc_injective hQ.1 hQ.2 hX).ne_iff,
      (sdArc_injective hQ.1 hQ.2 hX).ne_iff]
    tauto
  have hnotswap : ∀ g, (cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).IsDirected g →
      τ (arcN g) = arcN g := by
    intro g hd
    rcases hcases g with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, hf, -⟩
    · exact h
    · exact h
    · exact absurd ((hSdir g).1 hd) (by rw [← hf]; exact hfRnh)
  suffices ψ : Nonempty (SDMetricIso (cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b)
      (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _) (unrooted _ hb hX)
      (unrootedMetric _ hb hX (disjointMetric Q v H₁ H₂ θ))) from ψ.map SDMetricIso.symm
  refine ⟨⟨⟨vert, edge, fun g => ?_, fun g => ?_, fun g hd => ?_, fun x => ?_⟩, fun g => ?_,
    fun g hd => ?_⟩⟩
  · -- the hybrid edges
    show (semidirected hb.1 hb.2 hX).IsDirected (edge g) ↔ _
    rw [semidirected_isDirected_iff, hedge, hSdir]
    rcases hcases g with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, hf, h⟩
    · rw [h]
    · rw [h]
    · rw [h]
      exact iff_of_false heRNnh (by rw [← hf]; exact hfRnh)
  · -- the ends
    rcases hcases g with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, hf, h⟩
    · obtain ⟨h₁', h₂'⟩ := hexact g h
      exact Or.inl ⟨key _ _ h₁', key _ _ h₂'⟩
    · obtain ⟨h₁', h₂'⟩ := hexact g h
      exact Or.inl ⟨key _ _ h₁', key _ _ h₂'⟩
    · obtain ⟨h₁', h₂'⟩ := hswap g hf h
      exact Or.inr ⟨key _ _ h₁', key _ _ h₂'⟩
  · -- the hybrid edges keep their direction
    obtain ⟨h₁', h₂'⟩ := hexact g (hnotswap g hd)
    exact ⟨key _ _ h₁', key _ _ h₂'⟩
  · -- the taxa
    apply key
    rw [sdVert_leaf]
    by_cases hxa : x = a
    · rw [hxa, hleafA]
      simp [cutSD, ν]
    by_cases hxb : x = b
    · have hba : ¬ b = a := fun h => hab h.symm
      rw [hxb, hleafB]
      simp [cutSD, hba, ν]
    by_cases hx : Q.graph.Reaches v (Q.leaf x)
    · have hN : (disjointNet Q v H₁ H₂ a b).leaf x = .inr 0 := by
        simp [disjointNet, hxa, hxb, hx]
      have hS : (cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).leaf x = .inr 0 := by
        simp [cutSD, hxa, hxb, (cleaf x).2 hx]
      rw [hN, hS]
      rfl
    · have hS' : ¬ CutReach (semidirected hQ.1 hQ.2 hX) h₁ h₂ w
          ((semidirected hQ.1 hQ.2 hX).leaf x) := fun h => hx ((cleaf x).1 h)
      have hN : (disjointNet Q v H₁ H₂ a b).leaf x = .inl ⟨Q.leaf x, hx⟩ := by
        simp [disjointNet, hxa, hxb, hx]
      have hS : (cutSD (semidirected hQ.1 hQ.2 hX) w h₁ h₂ a b).leaf x = .inl ⟨_, hS'⟩ := by
        simp [cutSD, hxa, hxb, hS']
      rw [hN, hS]
      exact congrArg Sum.inl (Subtype.ext (sdVert_leaf hQ.1 hQ.2 hX x).symm)
  · -- the lengths
    change (semidirectedMetric hb.1 hb.2 hX (disjointMetric Q v H₁ H₂ θ)).length (edge g) =
      (semidirectedMetric hQ.1 hQ.2 hX θ).length g.1
    rw [semidirectedMetric_length, semidirectedMetric_length, hedge]
    rcases hcases g with ⟨hs, h⟩ | ⟨hs, hf, h⟩ | ⟨hs, hf, h⟩
    · rw [h, ite_eq_right (fun h' => hs ((hsrcRoot _).1 h')), ite_eq_right (fun h' => hs (h'.trans hr))]
      rfl
    · rw [h, ite_eq_left ((hsrcRoot _).2 hs), ite_eq_left (hs.trans hr.symm), hf]
      rfl
    · rw [h, ite_eq_left ((hsrcRoot eRN).2 heR), ite_eq_left (hs.trans hr.symm), hf]
      exact add_comm _ _
  · -- the inheritance probabilities
    change (disjointMetric Q v H₁ H₂ θ).inheritance (sdArc hb.1 hb.2 hX (edge g)) =
      θ.inheritance (sdArc hQ.1 hQ.2 hX g.1)
    rw [hedge, hnotswap g hd]
    obtain ⟨-, hg₁, hg₂⟩ := hd
    show (if sdArc hQ.1 hQ.2 hX g.1 = H₁ ∨ sdArc hQ.1 hQ.2 hX g.1 = H₂ then (1 : ℝ)
      else θ.inheritance (sdArc hQ.1 hQ.2 hX g.1)) = _
    rw [ite_eq_right]
    rintro (h | h)
    · exact hg₁ (sdArc_injective _ _ _ (h.trans hE₁.symm))
    · exact hg₂ (sdArc_injective _ _ _ (h.trans hE₂.symm))

end Banos2019
