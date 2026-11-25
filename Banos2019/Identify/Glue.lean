module

public import Banos2019.Identify.TildeDefs
public import Banos2019.Identify.TildeBase
public import Banos2019.Bridge.Quartet

/-!
# Gluing two networks at leaves (Baños 2019, proof of Theorem 4)

"We obtain `Ñ` by identifying `s₁` in `N₂` with `s₂` in `N₁` and suppressing that node." Gluing
`G₁` at its leaf `x₁` to `G₂` at its leaf `x₂`: remove the two leaves and their edges, and join
their neighbours `w₁`, `w₂` by a new edge, which is the result of identifying the two leaves and
suppressing the node of degree two that this leaves. The taxa of the glued network are given by a map
`τ` to the taxa of the two pieces.

* `glue`: the glued network; `IsLeafNeighbour`: `w` is the neighbour of the leaf `x`.
* `glue_congr`: isomorphic pieces glue to isomorphic networks.
* `tilde_sdIso_glue`: for a node `u` of a cycle of `N⁻`, with block `P`, `Ñ` is the gluing of the
  networks `Ñ` of the induced networks on `P ∪ {s₁}` and on `Pᶜ ∪ {s₂}` (`s₁ ∉ P`, `s₂ ∈ P`).

The proof cuts `N⁻` at the edge `f` of `u` off its cycle, which lies on no cycle; `P` is the set of
taxa on the far side of `f`.

* `pendantSide R S a ι`: the side `S` of a network, with a pendant leaf at `a`;
  `halfNet G f y ι`: the side of `y` of the edge `f`, with `f` as the pendant edge.
  `nonempty_sdIso_glue_pendantSide`: a network with an undirected edge across a cut is the gluing
  of its two sides.
* `IsUnrootedLevelOne`: the properties of `N⁻` that the construction of `Ñ` uses
  (`isUnrootedLevelOne_unrooted`), kept by isomorphisms (`IsUnrootedLevelOne.of_sdIso`).
* `tildeContracted G`: `Ñ` before its suppression. `tilde_cut`: the edge `ε` of `Ñ` through `f` is
  undirected and is the only edge of `Ñ` joining the two sides of `f`.
* `tilde_halfNet`: `Ñ` of a half is the half of `Ñ`: contraction and suppression commute with taking
  a side (`nonempty_sdIso_tildeContracted_halfNet`, `nonempty_sdIso_suppress_pendantSide`).
* `tilde_sdIso_pendantSide_of_side`: when the other side holds one taxon, `Ñ` is its own half, the
  nodes of that side other than the taxon lying on 2-cycles (`exists_two_cycle_of_side`).
* `exists_halfNet_inducedUnrooted`: for `Z` the taxa of the side of `y` and one taxon of the other
  side, the side of `y` of `N⁻` is a side of `(N⁻)_Z`: the edges at the side lie on simple treks
  between taxa of `Z` (`mem_trekEdges_of_side`), and suppression keeps the side
  (`exists_halfNet_restrict`). `(N⁻)_Z` is `(N⊕_Z)⁻` up to isomorphism, by Proposition 1
  (`nonempty_sdIso_inducedUnrooted_unrooted_inducedLSA`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

section Glue

variable {V₁ E₁ X₁ V₂ E₂ X₂ X : Type*}

/-- `w` is the neighbour of the leaf `x`: every edge at the leaf joins it to `w`, and there is one. -/
def IsLeafNeighbour {V E X' : Type*} (G : SemidirectedNetwork V E X') (x : X') (w : V) : Prop :=
  w ≠ G.leaf x ∧ (∃ e, Joins G.graph e (G.leaf x) w) ∧
    ∀ e, (G.graph.source e = G.leaf x ∨ G.graph.target e = G.leaf x) → Joins G.graph e (G.leaf x) w

/-- The leaf of a taxon of the glued network, sent by `τ` to a taxon of one of the pieces; a taxon
sent to a removed leaf goes to `w₁` (this does not happen in the uses). -/
def glueLeaf (G₁ : SemidirectedNetwork V₁ E₁ X₁) (G₂ : SemidirectedNetwork V₂ E₂ X₂) (x₁ : X₁)
    (x₂ : X₂) (w₁ : {v // v ≠ G₁.leaf x₁}) (τ : X → X₁ ⊕ X₂) (x : X) :
    {v // v ≠ G₁.leaf x₁} ⊕ {v // v ≠ G₂.leaf x₂} :=
  match τ x with
  | .inl y => if h : G₁.leaf y = G₁.leaf x₁ then .inl w₁ else .inl ⟨G₁.leaf y, h⟩
  | .inr y => if h : G₂.leaf y = G₂.leaf x₂ then .inl w₁ else .inr ⟨G₂.leaf y, h⟩

/-- **Gluing** `G₁` at the leaf `x₁` to `G₂` at the leaf `x₂`: the leaves and their edges are removed,
and a new undirected edge joins the neighbours `w₁` and `w₂`. -/
def glue (G₁ : SemidirectedNetwork V₁ E₁ X₁) (G₂ : SemidirectedNetwork V₂ E₂ X₂) (x₁ : X₁) (x₂ : X₂)
    (w₁ : {v // v ≠ G₁.leaf x₁}) (w₂ : {v // v ≠ G₂.leaf x₂}) (τ : X → X₁ ⊕ X₂) :
    SemidirectedNetwork ({v // v ≠ G₁.leaf x₁} ⊕ {v // v ≠ G₂.leaf x₂})
      ({e // G₁.graph.source e ≠ G₁.leaf x₁ ∧ G₁.graph.target e ≠ G₁.leaf x₁} ⊕
        {e // G₂.graph.source e ≠ G₂.leaf x₂ ∧ G₂.graph.target e ≠ G₂.leaf x₂} ⊕ Unit) X where
  graph :=
    { source := fun e => match e with
        | .inl e => .inl ⟨G₁.graph.source e.1, e.2.1⟩
        | .inr (.inl e) => .inr ⟨G₂.graph.source e.1, e.2.1⟩
        | .inr (.inr _) => .inl w₁
      target := fun e => match e with
        | .inl e => .inl ⟨G₁.graph.target e.1, e.2.2⟩
        | .inr (.inl e) => .inr ⟨G₂.graph.target e.1, e.2.2⟩
        | .inr (.inr _) => .inr w₂ }
  IsDirected e := match e with
    | .inl e => G₁.IsDirected e.1
    | .inr (.inl e) => G₂.IsDirected e.1
    | .inr (.inr _) => False
  leaf := glueLeaf G₁ G₂ x₁ x₂ w₁ τ

variable {V₁' E₁' V₂' E₂' : Type*}

/-- **An isomorphism takes the neighbour of a leaf to the neighbour of the leaf.** -/
theorem IsLeafNeighbour.map {V E V' E' X' : Type*} {G : SemidirectedNetwork V E X'}
    {G' : SemidirectedNetwork V' E' X'} {x : X'} {w : V} {w' : V'} (hw : IsLeafNeighbour G x w)
    (ι : SDIso G G') (hw' : IsLeafNeighbour G' x w') : ι.vert w = w' := by
  obtain ⟨e, he⟩ := hw.2.1
  have h := ι.joins_of_joins he
  rw [← ι.leaf] at h
  exact Joins.eq_right h (hw'.2.2 _ (Joins.incident_left h))

/-- **The neighbour of a leaf, carried by an isomorphism.** -/
theorem IsLeafNeighbour.of_sdIso {V E V' E' X' : Type*} {G : SemidirectedNetwork V E X'}
    {G' : SemidirectedNetwork V' E' X'} {x : X'} {w : V} (hw : IsLeafNeighbour G x w)
    (ι : SDIso G G') : IsLeafNeighbour G' x (ι.vert w) := by
  refine ⟨fun h => hw.1 (ι.vert.injective (h.trans (ι.leaf x))), ?_, fun e' he' => ?_⟩
  · obtain ⟨e, he⟩ := hw.2.1
    refine ⟨ι.edge e, ?_⟩
    rw [ι.leaf]
    exact ι.joins_of_joins he
  · obtain ⟨e, rfl⟩ := ι.edge.surjective e'
    rw [ι.leaf, ι.incident_iff] at he'
    rw [ι.leaf]
    exact ι.joins_of_joins (hw.2.2 e he')

/-- **Isomorphic pieces glue to isomorphic networks.** -/
theorem glue_congr {G₁ : SemidirectedNetwork V₁ E₁ X₁} {G₂ : SemidirectedNetwork V₂ E₂ X₂}
    {G₁' : SemidirectedNetwork V₁' E₁' X₁} {G₂' : SemidirectedNetwork V₂' E₂' X₂} {x₁ : X₁} {x₂ : X₂}
    {w₁ : V₁} {w₂ : V₂} {w₁' : V₁'} {w₂' : V₂'} (hw₁ : IsLeafNeighbour G₁ x₁ w₁)
    (hw₂ : IsLeafNeighbour G₂ x₂ w₂) (hw₁' : IsLeafNeighbour G₁' x₁ w₁')
    (hw₂' : IsLeafNeighbour G₂' x₂ w₂') (τ : X → X₁ ⊕ X₂) (i₁ : SDIso G₁ G₁') (i₂ : SDIso G₂ G₂') :
    Nonempty (SDIso (glue G₁ G₂ x₁ x₂ ⟨w₁, hw₁.1⟩ ⟨w₂, hw₂.1⟩ τ)
      (glue G₁' G₂' x₁ x₂ ⟨w₁', hw₁'.1⟩ ⟨w₂', hw₂'.1⟩ τ)) := by
  have hn₁ : i₁.vert w₁ = w₁' := hw₁.map i₁ hw₁'
  have hn₂ : i₂.vert w₂ = w₂' := hw₂.map i₂ hw₂'
  have hV₁ : ∀ v, v ≠ G₁.leaf x₁ ↔ i₁.vert v ≠ G₁'.leaf x₁ := fun v => by
    rw [i₁.leaf]
    exact i₁.vert.injective.ne_iff.symm
  have hV₂ : ∀ v, v ≠ G₂.leaf x₂ ↔ i₂.vert v ≠ G₂'.leaf x₂ := fun v => by
    rw [i₂.leaf]
    exact i₂.vert.injective.ne_iff.symm
  have hE₁ : ∀ e, (G₁.graph.source e ≠ G₁.leaf x₁ ∧ G₁.graph.target e ≠ G₁.leaf x₁) ↔
      (G₁'.graph.source (i₁.edge e) ≠ G₁'.leaf x₁ ∧
        G₁'.graph.target (i₁.edge e) ≠ G₁'.leaf x₁) := fun e => by
    simp only [ne_eq, ← not_or, i₁.leaf, i₁.incident_iff]
  have hE₂ : ∀ e, (G₂.graph.source e ≠ G₂.leaf x₂ ∧ G₂.graph.target e ≠ G₂.leaf x₂) ↔
      (G₂'.graph.source (i₂.edge e) ≠ G₂'.leaf x₂ ∧
        G₂'.graph.target (i₂.edge e) ≠ G₂'.leaf x₂) := fun e => by
    simp only [ne_eq, ← not_or, i₂.leaf, i₂.incident_iff]
  refine ⟨{ vert := Equiv.sumCongr (i₁.vert.subtypeEquiv hV₁) (i₂.vert.subtypeEquiv hV₂)
            edge := Equiv.sumCongr (i₁.edge.subtypeEquiv hE₁)
              (Equiv.sumCongr (i₂.edge.subtypeEquiv hE₂) (Equiv.refl Unit))
            isDirected_iff := ?_, joins := ?_, directed := ?_, leaf := ?_ }⟩
  · rintro (e | e | u)
    · exact i₁.isDirected_iff e.1
    · exact i₂.isDirected_iff e.1
    · exact Iff.rfl
  · rintro (e | e | u)
    · have := i₁.joins e.1
      simp only [Joins, glue, Equiv.sumCongr_apply, Sum.map_inl, Equiv.subtypeEquiv_apply,
        Sum.inl.injEq, Subtype.mk.injEq] at this ⊢
      exact this
    · have := i₂.joins e.1
      simp only [Joins, glue, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        Equiv.subtypeEquiv_apply, Sum.inr.injEq, Subtype.mk.injEq] at this ⊢
      exact this
    · left
      simp only [glue, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.subtypeEquiv_apply,
        Sum.inl.injEq, Sum.inr.injEq, Subtype.mk.injEq]
      exact ⟨hn₁.symm, hn₂.symm⟩
  · rintro (e | e | u) he
    · have := i₁.directed e.1 he
      simp only [glue, Equiv.sumCongr_apply, Sum.map_inl, Equiv.subtypeEquiv_apply,
        Sum.inl.injEq, Subtype.mk.injEq]
      exact this
    · have := i₂.directed e.1 he
      simp only [glue, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.subtypeEquiv_apply,
        Sum.inr.injEq, Subtype.mk.injEq]
      exact this
    · exact he.elim
  · intro x
    simp only [glue, glueLeaf]
    rcases hτ : τ x with y | y
    · by_cases h : G₁.leaf y = G₁.leaf x₁
      · have h' : G₁'.leaf y = G₁'.leaf x₁ := by rw [i₁.leaf, i₁.leaf, h]
        simp only [h, h', ↓reduceDIte, Equiv.sumCongr_apply, Sum.map_inl,
          Equiv.subtypeEquiv_apply, Sum.inl.injEq, Subtype.mk.injEq]
        exact hn₁.symm
      · have h' : G₁'.leaf y ≠ G₁'.leaf x₁ := by rwa [i₁.leaf, i₁.leaf, Ne, i₁.vert.apply_eq_iff_eq]
        simp only [h, h', ↓reduceDIte, Equiv.sumCongr_apply, Sum.map_inl,
          Equiv.subtypeEquiv_apply, Sum.inl.injEq, Subtype.mk.injEq]
        exact i₁.leaf y
    · by_cases h : G₂.leaf y = G₂.leaf x₂
      · have h' : G₂'.leaf y = G₂'.leaf x₂ := by rw [i₂.leaf, i₂.leaf, h]
        simp only [h, h', ↓reduceDIte, Equiv.sumCongr_apply, Sum.map_inl,
          Equiv.subtypeEquiv_apply, Sum.inl.injEq, Subtype.mk.injEq]
        exact hn₁.symm
      · have h' : G₂'.leaf y ≠ G₂'.leaf x₂ := by rwa [i₂.leaf, i₂.leaf, Ne, i₂.vert.apply_eq_iff_eq]
        simp only [h, h', ↓reduceDIte, Equiv.sumCongr_apply, Sum.map_inr,
          Equiv.subtypeEquiv_apply, Sum.inr.injEq, Subtype.mk.injEq]
        exact i₂.leaf y

end Glue

section Pendant

variable {V E X : Type*}

/-- **One side of a network, with a pendant leaf**: the nodes of `S` and the edges between them, and
a new leaf joined to the node `a ∈ S` by a new undirected edge. The taxa are those of `Z`, sent to
the taxa of the network by `ι`: a taxon keeps the leaf of its image when that leaf is in `S`, and
goes to the new leaf otherwise. -/
def pendantSide {Z : Type*} (R : SemidirectedNetwork V E X) (S : Set V) (a : S) (ι : Z → X) :
    SemidirectedNetwork (S ⊕ Unit)
      ({e // R.graph.source e ∈ S ∧ R.graph.target e ∈ S} ⊕ Unit) Z where
  graph :=
    { source := fun e => match e with
        | .inl e => .inl ⟨R.graph.source e.1, e.2.1⟩
        | .inr _ => .inl a
      target := fun e => match e with
        | .inl e => .inl ⟨R.graph.target e.1, e.2.2⟩
        | .inr _ => .inr () }
  IsDirected e := match e with
    | .inl e => R.IsDirected e.1
    | .inr _ => False
  leaf x := if h : R.leaf (ι x) ∈ S then .inl ⟨R.leaf (ι x), h⟩ else .inr ()

theorem pendantSide_leaf_of_notMem {Z : Type*} {R : SemidirectedNetwork V E X} {S : Set V} {a : S}
    {ι : Z → X} {z : Z} (hz : R.leaf (ι z) ∉ S) : (pendantSide R S a ι).leaf z = .inr () := by
  simp only [pendantSide, hz, ↓reduceDIte]

theorem pendantSide_leaf_of_mem {Z : Type*} {R : SemidirectedNetwork V E X} {S : Set V} {a : S}
    {ι : Z → X} {z : Z} (hz : R.leaf (ι z) ∈ S) :
    (pendantSide R S a ι).leaf z = .inl ⟨R.leaf (ι z), hz⟩ := by
  simp only [pendantSide, hz, ↓reduceDIte]

/-- **The new leaf of `pendantSide` hangs from `a`.** -/
theorem isLeafNeighbour_pendantSide {Z : Type*} {R : SemidirectedNetwork V E X} {S : Set V} (a : S)
    {ι : Z → X} {z : Z} (hz : R.leaf (ι z) ∉ S) :
    IsLeafNeighbour (pendantSide R S a ι) z (.inl a) := by
  rw [IsLeafNeighbour, pendantSide_leaf_of_notMem hz]
  refine ⟨Sum.inl_ne_inr, ⟨.inr (), Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
  rintro (e | e) he
  · simp [pendantSide] at he
  · exact Or.inr ⟨rfl, rfl⟩

/-- **A network with an undirected edge `ε` across a cut is the gluing of its two sides**, each with
a pendant leaf at the end of `ε`: `S₁` and `S₂` partition the nodes, `ε` joins `a ∈ S₁` to `b ∈ S₂`,
and every other edge has its two ends on the same side. -/
theorem nonempty_sdIso_glue_pendantSide (R : SemidirectedNetwork V E X) {S₁ S₂ : Set V}
    (hS : ∀ v, v ∈ S₂ ↔ v ∉ S₁) {ε : E} {a b : V} (ha : a ∈ S₁) (hb : b ∈ S₂)
    (hε : Joins R.graph ε a b) (hεd : ¬ R.IsDirected ε)
    (hcross : ∀ e, e ≠ ε → (R.graph.source e ∈ S₁ ↔ R.graph.target e ∈ S₁))
    {Z₁ Z₂ : Type*} {ι₁ : Z₁ → X} {ι₂ : Z₂ → X} {z₁ : Z₁} {z₂ : Z₂} (hz₁ : R.leaf (ι₁ z₁) ∉ S₁)
    (hz₂ : R.leaf (ι₂ z₂) ∉ S₂) {τ : X → Z₁ ⊕ Z₂}
    (hτ₁ : ∀ x y, τ x = .inl y → ι₁ y = x ∧ R.leaf x ∈ S₁)
    (hτ₂ : ∀ x y, τ x = .inr y → ι₂ y = x ∧ R.leaf x ∈ S₂) :
    Nonempty (SDIso R (glue (pendantSide R S₁ ⟨a, ha⟩ ι₁) (pendantSide R S₂ ⟨b, hb⟩ ι₂) z₁ z₂
      ⟨.inl ⟨a, ha⟩, (isLeafNeighbour_pendantSide ⟨a, ha⟩ hz₁).1⟩
      ⟨.inl ⟨b, hb⟩, (isLeafNeighbour_pendantSide ⟨b, hb⟩ hz₂).1⟩ τ)) := by
  set R₁ := pendantSide R S₁ ⟨a, ha⟩ ι₁
  set R₂ := pendantSide R S₂ ⟨b, hb⟩ ι₂
  have hl₁ : R₁.leaf z₁ = .inr () := pendantSide_leaf_of_notMem hz₁
  have hl₂ : R₂.leaf z₂ = .inr () := pendantSide_leaf_of_notMem hz₂
  have hn₁ : ∀ s : S₁, (.inl s : S₁ ⊕ Unit) ≠ R₁.leaf z₁ := fun s => by
    rw [hl₁]
    exact Sum.inl_ne_inr
  have hn₂ : ∀ s : S₂, (.inl s : S₂ ⊕ Unit) ≠ R₂.leaf z₂ := fun s => by
    rw [hl₂]
    exact Sum.inl_ne_inr
  have hS₂ : ∀ {v}, v ∉ S₁ → v ∈ S₂ := fun h => (hS _).mpr h
  have hbS₁ : b ∉ S₁ := (hS b).mp hb
  have hεS : ∀ e, e ≠ ε → R.graph.source e ∉ S₁ → R.graph.target e ∉ S₁ := fun e he h h' =>
    h ((hcross e he).mpr h')
  -- the nodes
  let vert : V ≃ {v // v ≠ R₁.leaf z₁} ⊕ {v // v ≠ R₂.leaf z₂} :=
    { toFun := fun v => if h : v ∈ S₁ then .inl ⟨.inl ⟨v, h⟩, hn₁ _⟩
        else .inr ⟨.inl ⟨v, hS₂ h⟩, hn₂ _⟩
      invFun := fun w => match w with
        | .inl ⟨.inl s, _⟩ => s.1
        | .inl ⟨.inr _, _⟩ => a
        | .inr ⟨.inl s, _⟩ => s.1
        | .inr ⟨.inr _, _⟩ => a
      left_inv := fun v => by
        by_cases h : v ∈ S₁ <;> simp [h]
      right_inv := by
        rintro (⟨(s | u), hs⟩ | ⟨(s | u), hs⟩)
        · simp [s.2]
        · exact (hs (by rw [hl₁])).elim
        · have : s.1 ∉ S₁ := (hS _).mp s.2
          simp [this]
        · exact (hs (by rw [hl₂])).elim }
  have hvert₁ : ∀ v (h : v ∈ S₁), vert v = .inl ⟨.inl ⟨v, h⟩, hn₁ _⟩ := fun v h => by
    simp only [vert, Equiv.coe_fn_mk, h, ↓reduceDIte]
  have hvert₂ : ∀ v (h : v ∉ S₁), vert v = .inr ⟨.inl ⟨v, hS₂ h⟩, hn₂ _⟩ := fun v h => by
    simp only [vert, Equiv.coe_fn_mk, h, ↓reduceDIte]
  -- the edges
  have hε₁ : ∀ e, R.graph.source e ∈ S₁ → R.graph.target e ∈ S₁ → e ≠ ε := by
    rintro e h₁ h₂ rfl
    rcases hε with ⟨-, h⟩ | ⟨h, -⟩
    · exact hbS₁ (h ▸ h₂)
    · exact hbS₁ (h ▸ h₁)
  have hε₂ : ∀ e, R.graph.source e ∈ S₂ → R.graph.target e ∈ S₂ → e ≠ ε := by
    rintro e h₁ h₂ rfl
    rcases hε with ⟨h, -⟩ | ⟨-, h⟩
    · exact (hS a).mp (h ▸ h₁) ha
    · exact (hS a).mp (h ▸ h₂) ha
  let edge : E ≃ {e // R₁.graph.source e ≠ R₁.leaf z₁ ∧ R₁.graph.target e ≠ R₁.leaf z₁} ⊕
      {e // R₂.graph.source e ≠ R₂.leaf z₂ ∧ R₂.graph.target e ≠ R₂.leaf z₂} ⊕ Unit :=
    { toFun := fun e => if he : e = ε then .inr (.inr ()) else
        if hs : R.graph.source e ∈ S₁ then .inl ⟨.inl ⟨e, hs, (hcross e he).mp hs⟩, hn₁ _, hn₁ _⟩
        else .inr (.inl ⟨.inl ⟨e, hS₂ hs, hS₂ (hεS e he hs)⟩, hn₂ _, hn₂ _⟩)
      invFun := fun g => match g with
        | .inl ⟨.inl e, _⟩ => e.1
        | .inl ⟨.inr _, _⟩ => ε
        | .inr (.inl ⟨.inl e, _⟩) => e.1
        | .inr (.inl ⟨.inr _, _⟩) => ε
        | .inr (.inr _) => ε
      left_inv := fun e => by
        by_cases he : e = ε
        · subst he
          simp
        · by_cases hs : R.graph.source e ∈ S₁ <;> simp [he, hs]
      right_inv := by
        rintro (⟨(e | u), h⟩ | ⟨(e | u), h⟩ | u)
        · simp [hε₁ e.1 e.2.1 e.2.2, e.2.1]
        · exact (h.2 (by rw [hl₁]; rfl)).elim
        · have : R.graph.source e.1 ∉ S₁ := (hS _).mp e.2.1
          simp [hε₂ e.1 e.2.1 e.2.2, this]
        · exact (h.2 (by rw [hl₂]; rfl)).elim
        · simp }
  have hedgeε : edge ε = .inr (.inr ()) := by simp [edge]
  have hedge₁ : ∀ e (he : e ≠ ε) (hs : R.graph.source e ∈ S₁),
      edge e = .inl ⟨.inl ⟨e, hs, (hcross e he).mp hs⟩, hn₁ _, hn₁ _⟩ := fun e he hs => by
    simp only [edge, Equiv.coe_fn_mk, he, hs, ↓reduceDIte]
  have hedge₂ : ∀ e (he : e ≠ ε) (hs : R.graph.source e ∉ S₁),
      edge e = .inr (.inl ⟨.inl ⟨e, hS₂ hs, hS₂ (hεS e he hs)⟩, hn₂ _, hn₂ _⟩) := fun e he hs => by
    simp only [edge, Equiv.coe_fn_mk, he, hs, ↓reduceDIte]
  refine ⟨{ vert := vert
            edge := edge
            isDirected_iff := fun e => ?_
            joins := fun e => ?_
            directed := fun e hd => ?_
            leaf := fun x => ?_ }⟩
  · by_cases he : e = ε
    · subst he
      rw [hedgeε]
      exact ⟨False.elim, fun h => hεd h⟩
    · by_cases hs : R.graph.source e ∈ S₁
      · rw [hedge₁ e he hs]
        exact Iff.rfl
      · rw [hedge₂ e he hs]
        exact Iff.rfl
  · by_cases he : e = ε
    · subst he
      rw [hedgeε]
      rcases hε with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂, hvert₁ a ha, hvert₂ b hbS₁]
        exact Or.inl ⟨rfl, rfl⟩
      · rw [h₁, h₂, hvert₁ a ha, hvert₂ b hbS₁]
        exact Or.inr ⟨rfl, rfl⟩
    · by_cases hs : R.graph.source e ∈ S₁
      · rw [hedge₁ e he hs, hvert₁ _ hs, hvert₁ _ ((hcross e he).mp hs)]
        exact Or.inl ⟨rfl, rfl⟩
      · rw [hedge₂ e he hs, hvert₂ _ hs, hvert₂ _ (hεS e he hs)]
        exact Or.inl ⟨rfl, rfl⟩
  · have he : e ≠ ε := by
      rintro rfl
      exact hεd hd
    by_cases hs : R.graph.source e ∈ S₁
    · rw [hedge₁ e he hs, hvert₁ _ hs, hvert₁ _ ((hcross e he).mp hs)]
      exact ⟨rfl, rfl⟩
    · rw [hedge₂ e he hs, hvert₂ _ hs, hvert₂ _ (hεS e he hs)]
      exact ⟨rfl, rfl⟩
  · show glueLeaf R₁ R₂ z₁ z₂ _ τ x = _
    unfold glueLeaf
    rcases hτ : τ x with y | y
    · obtain ⟨rfl, hy⟩ := hτ₁ x y hτ
      have hy' : R₁.leaf y = .inl ⟨R.leaf (ι₁ y), hy⟩ := pendantSide_leaf_of_mem hy
      rw [hvert₁ _ hy]
      simp only [hy', hl₁, reduceCtorEq, ↓reduceDIte]
    · obtain ⟨rfl, hy⟩ := hτ₂ x y hτ
      have hy' : R₂.leaf y = .inl ⟨R.leaf (ι₂ y), hy⟩ := pendantSide_leaf_of_mem hy
      rw [hvert₂ _ ((hS _).mp hy)]
      simp only [hy', hl₂, reduceCtorEq, ↓reduceDIte]

/-- **A network whose nodes outside `S` reduce to one node `b`, joined only by an undirected edge
`ε` to `a ∈ S`, is its side `S` with a pendant leaf at `a`.** -/
theorem nonempty_sdIso_pendantSide (R : SemidirectedNetwork V E X) {S : Set V} {ε : E} {a b : V}
    (ha : a ∈ S) (hb : ∀ v, v ∉ S ↔ v = b) (hε : Joins R.graph ε a b) (hεd : ¬ R.IsDirected ε)
    (honly : ∀ e, e ≠ ε → R.graph.source e ∈ S ∧ R.graph.target e ∈ S) :
    Nonempty (SDIso R (pendantSide R S ⟨a, ha⟩ id)) := by
  have hbS : b ∉ S := (hb b).mpr rfl
  let vert : V ≃ S ⊕ Unit :=
    { toFun := fun v => if h : v ∈ S then .inl ⟨v, h⟩ else .inr ()
      invFun := fun w => match w with
        | .inl s => s.1
        | .inr _ => b
      left_inv := fun v => by
        by_cases h : v ∈ S
        · simp [h]
        · obtain rfl := (hb v).mp h
          simp [hbS]
      right_inv := by
        rintro (s | u)
        · simp [s.2]
        · simp [hbS] }
  have hvert : ∀ v (h : v ∈ S), vert v = .inl ⟨v, h⟩ := fun v h => by
    simp only [vert, Equiv.coe_fn_mk, h, ↓reduceDIte]
  have hvertb : vert b = .inr () := by
    simp only [vert, Equiv.coe_fn_mk, hbS, ↓reduceDIte]
  have hεS : ∀ e, R.graph.source e ∈ S → R.graph.target e ∈ S → e ≠ ε := by
    rintro e h₁ h₂ rfl
    rcases hε with ⟨-, h⟩ | ⟨h, -⟩
    · exact hbS (h ▸ h₂)
    · exact hbS (h ▸ h₁)
  let edge : E ≃ {e // R.graph.source e ∈ S ∧ R.graph.target e ∈ S} ⊕ Unit :=
    { toFun := fun e => if he : e = ε then .inr () else .inl ⟨e, honly e he⟩
      invFun := fun g => match g with
        | .inl e => e.1
        | .inr _ => ε
      left_inv := fun e => by
        by_cases he : e = ε
        · subst he
          simp
        · simp [he]
      right_inv := by
        rintro (e | u)
        · simp [hεS e.1 e.2.1 e.2.2]
        · simp }
  have hedgeε : edge ε = .inr () := by simp [edge]
  have hedge : ∀ e (he : e ≠ ε), edge e = .inl ⟨e, honly e he⟩ := fun e he => by
    simp only [edge, Equiv.coe_fn_mk, he, ↓reduceDIte]
  refine ⟨{ vert := vert
            edge := edge
            isDirected_iff := fun e => ?_
            joins := fun e => ?_
            directed := fun e hd => ?_
            leaf := fun x => ?_ }⟩
  · by_cases he : e = ε
    · subst he
      rw [hedgeε]
      exact ⟨False.elim, fun h => hεd h⟩
    · rw [hedge e he]
      exact Iff.rfl
  · by_cases he : e = ε
    · subst he
      rw [hedgeε]
      rcases hε with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂, hvert a ha, hvertb]
        exact Or.inl ⟨rfl, rfl⟩
      · rw [h₁, h₂, hvert a ha, hvertb]
        exact Or.inr ⟨rfl, rfl⟩
    · rw [hedge e he, hvert _ (honly e he).1, hvert _ (honly e he).2]
      exact Or.inl ⟨rfl, rfl⟩
  · have he : e ≠ ε := by
      rintro rfl
      exact hεd hd
    rw [hedge e he, hvert _ (honly e he).1, hvert _ (honly e he).2]
    exact ⟨rfl, rfl⟩
  · by_cases h : R.leaf x ∈ S
    · rw [hvert _ h, pendantSide_leaf_of_mem (ι := id) h]
      rfl
    · rw [pendantSide_leaf_of_notMem (ι := id) h, (hb _).mp h, hvertb]

end Pendant


section Cut

variable {V E X : Type*}

/-- The nodes joined to `y` by a walk avoiding the edge `f`: the side of `y` when `f` is a bridge.
-/
def cutSide (G : DirectedMultigraph V E) (f : E) (y : V) : Set V := {x | G.Walks {f}ᶜ y x}

/-- **An edge on no cycle is a bridge**: its ends are not joined by a walk avoiding it. -/
theorem not_walks_of_forall_notMem {G : DirectedMultigraph V E} {f : E}
    (hf : ∀ C, IsCycle G C → f ∉ C) : ¬ G.Walks {f}ᶜ (G.source f) (G.target f) := fun h => by
  obtain ⟨C, hC, hfC, -⟩ := exists_isCycle_of_walks (F := {f}ᶜ) (fun h => h rfl) (G.walks_symm h)
  exact hf C hC hfC

/-- **The two sides of an edge on no cycle**: in a connected network, a node is on the side of
exactly one end of an edge `f` that lies on no cycle. -/
theorem mem_cutSide_iff_notMem {G : DirectedMultigraph V E} (hG : G.IsConnected) {f : E}
    (hf : ∀ C, IsCycle G C → f ∉ C) {y y' : V} (hj : Joins G f y y') (x : V) :
    x ∈ cutSide G f y' ↔ x ∉ cutSide G f y := by
  have hb := not_walks_of_forall_notMem hf
  constructor
  · intro h' h
    have hyy : G.Walks {f}ᶜ y y' := (show G.Walks {f}ᶜ y x from h).trans (G.walks_symm h')
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hb (h₁ ▸ h₂ ▸ hyy)
    · exact hb (h₁ ▸ h₂ ▸ G.walks_symm hyy)
  · intro h
    rcases walks_compl_or_of_isConnected hG f x with h' | h' <;>
      rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact absurd (h₁ ▸ h') h
    · exact h₁ ▸ h'
    · exact h₂ ▸ h'
    · exact absurd (h₂ ▸ h') h

/-- The network of `Ñ` before suppression: the 2- and 3-cycles contracted and the hybrid edges of
the 4-cycles undirected. `tildeNetwork G` suppresses its nodes of degree two. -/
abbrev tildeContracted (G : SemidirectedNetwork V E X) :=
  undirectEdges (contractCycles G fun C => C.ncard ≤ 3)
    {e | ∃ C, IsCycle G.graph C ∧ C.ncard = 4 ∧ e.1 ∈ C}

/-- The nodes of `Ñ` on the side of `y` of the edge `f`. -/
def tildeCutSide (G : SemidirectedNetwork V E X) (f : E) (y : V) :
    Set {u // IsBranch (tildeContracted G) ∅ u} :=
  {w | ∃ x ∈ cutSide G.graph f y, w.1 = Quot.mk _ x}

/-- **The side of `y` of the edge `f`, with `f` as a pendant edge**: the nodes on the side of `y`,
the edges between them, and a new leaf joined to `y`. -/
abbrev halfNet (G : SemidirectedNetwork V E X) (f : E) (y : V) {Z : Type*} (ι : Z → X) :=
  pendantSide G (cutSide G.graph f y) ⟨y, Relation.ReflTransGen.refl⟩ ι

/-- **The properties of `N⁻` that the construction of `Ñ` uses**, for `N` binary and level-1: `N⁻`
is connected and has no loops, its taxa have degree one and its other nodes degree three, two cycles
with a common node are the same, its hybrid edges lie on cycles, and on each side of an edge that
lies on no cycle there is a taxon. -/
structure IsUnrootedLevelOne (G : SemidirectedNetwork V E X) : Prop where
  connected : G.graph.IsConnected
  loopless : ∀ e, G.graph.source e ≠ G.graph.target e
  degree_leaf : ∀ x, degree G.graph (G.leaf x) = 1
  degree_of_not_leaf : ∀ v, (¬ ∃ x, G.leaf x = v) → degree G.graph v = 3
  cycle_eq : ∀ C C', IsCycle G.graph C → IsCycle G.graph C' →
    (cycleNodes G.graph C ∩ cycleNodes G.graph C').Nonempty → C = C'
  mem_cycle_of_isDirected : ∀ e, G.IsDirected e → ∃ C, IsCycle G.graph C ∧ e ∈ C
  exists_leaf_side : ∀ e, (∀ C, IsCycle G.graph C → e ∉ C) → ∀ w,
    (G.graph.source e = w ∨ G.graph.target e = w) → ∃ x, G.leaf x ∈ cutSide G.graph e w

/-- **`N⁻` has the properties of `IsUnrootedLevelOne`** for a binary level-1 network `N`. -/
theorem isUnrootedLevelOne_unrooted [Finite V] [Finite E] {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X) :
    IsUnrootedLevelOne (unrooted N hN hX) where
  connected := unrooted_isConnected hN hX
  loopless := unrooted_source_ne_target hN
  degree_leaf := unrooted_degree_leaf hN
  degree_of_not_leaf := unrooted_degree_of_not_leaf hN
  cycle_eq _ C' hC hC' hn := (lemma3_unrooted hN h1 hX hC).2.2 C' hC' hn
  mem_cycle_of_isDirected := unrooted_mem_cycle_of_isDirected hN h1
  exists_leaf_side e he w hw := by
    set G := unrooted N hN hX
    have hnr : ¬ N.graph.Reaches (N.graph.target e.1.1) (N.graph.source e.1.1) := fun h =>
      hN.1.acyclic _ (Relation.TransGen.head' ⟨e.1.1, rfl, rfl⟩ h)
    -- a taxon below the target of `e`
    have htgt : ∃ x, G.leaf x ∈ cutSide G.graph e (G.graph.target e) := by
      obtain ⟨x, hx⟩ := Phylogenetics.RootedNetwork.exists_reaches_leaf hN.1
        (N.graph.target e.1.1)
      obtain ⟨w', hw'x, hw'⟩ := unrooted_walks_of_avoidingReach hN e (G.graph.target e)
        (avoidingReach_of_reaches hx hnr)
      exact ⟨x, (unrooted_node_ext (u := w') (w := G.leaf x) hw'x) ▸ hw'⟩
    rcases hw with rfl | rfl
    · -- a taxon reached from the root avoiding `e`: else the target of `e` would be a stable
      -- ancestor of all the taxa, strictly below `LSA(X)`
      have hb := not_walks_of_forall_notMem he
      have hsep := unrooted_separates hN e hb
      obtain ⟨x, hx⟩ : ∃ x, N.AvoidingReach e.1.1 N.root (N.leaf x) := by
        by_contra hne
        push Not at hne
        have hst : N.IsStableAncestor Set.univ (N.graph.target e.1.1) := by
          rintro x - ⟨-, -, hp⟩
          refine hne x (Relation.ReflTransGen.mono ?_ _ _ hp)
          rintro a b ⟨⟨f, hfs, hft⟩, -, hb⟩
          exact ⟨f, fun h => hb (h ▸ hft.symm), hfs, hft⟩
        have hl := (lsa_spec hN.1 Set.univ Set.univ_nonempty).2 _ hst
        exact hN.1.acyclic _ (Relation.TransGen.head' ⟨e.1.1, rfl, rfl⟩ (hl.trans e.1.2.1))
      refine ⟨x, (mem_cutSide_iff_notMem (unrooted_isConnected hN hX) he
        (Or.inr ⟨rfl, rfl⟩ : Joins G.graph e (G.graph.target e) (G.graph.source e)) _).mpr ?_⟩
      exact fun h => hsep.1 x h hx
    · exact htgt

/-- **An isomorphism carries walks.** -/
theorem SDIso.walks_image {V' E' : Type*} {G : SemidirectedNetwork V E X}
    {G' : SemidirectedNetwork V' E' X} (ι : SDIso G G') {F : Set E} {u w : V}
    (h : G.graph.Walks F u w) : G'.graph.Walks (ι.edge '' F) (ι.vert u) (ι.vert w) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨e, he, hj⟩ := hst
    exact ih.tail ⟨ι.edge e, Set.mem_image_of_mem _ he, ι.joins_of_joins hj⟩

/-- **`IsUnrootedLevelOne` is kept by isomorphisms.** -/
theorem IsUnrootedLevelOne.of_sdIso [Finite E] {V' E' : Type*} {G : SemidirectedNetwork V E X}
    {G' : SemidirectedNetwork V' E' X} (hG : IsUnrootedLevelOne G) (ι : SDIso G G') :
    IsUnrootedLevelOne G' where
  connected u' w' := by
    have h := ι.walks_image (hG.connected (ι.vert.symm u') (ι.vert.symm w'))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact walks_mono (Set.subset_univ _) h
  loopless e' h := by
    obtain ⟨e, rfl⟩ := ι.edge.surjective e'
    rcases ι.joins e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hG.loopless e (ι.vert.injective (h₁.symm.trans (h.trans h₂)))
    · exact hG.loopless e (ι.vert.injective (h₂.symm.trans (h.symm.trans h₁)))
  degree_leaf x := by
    rw [ι.leaf, ι.degree_eq]
    exact hG.degree_leaf x
  degree_of_not_leaf v' hv' := by
    obtain ⟨v, rfl⟩ := ι.vert.surjective v'
    rw [ι.degree_eq]
    exact hG.degree_of_not_leaf v fun h => hv' ((ι.isLeaf_iff v).mpr h)
  cycle_eq C₁ C₂ h₁ h₂ hn := by
    rw [ι.isCycle_iff_symm_image] at h₁ h₂
    have : ι.edge.symm '' C₁ = ι.edge.symm '' C₂ := by
      refine hG.cycle_eq _ _ h₁ h₂ ?_
      obtain ⟨u', hu₁, hu₂⟩ := hn
      refine ⟨ι.vert.symm u', ?_, ?_⟩
      · have := ι.symm.cycleNodes_image C₁
        rw [show ι.symm.edge = ι.edge.symm from rfl] at this
        rw [this]
        exact Set.mem_image_of_mem _ hu₁
      · have := ι.symm.cycleNodes_image C₂
        rw [show ι.symm.edge = ι.edge.symm from rfl] at this
        rw [this]
        exact Set.mem_image_of_mem _ hu₂
    have h' := congrArg (Set.image ι.edge) this
    rwa [ι.edge.image_symm_image, ι.edge.image_symm_image] at h'
  mem_cycle_of_isDirected e' he' := by
    obtain ⟨e, rfl⟩ := ι.edge.surjective e'
    obtain ⟨C, hC, heC⟩ := hG.mem_cycle_of_isDirected e ((ι.isDirected_iff e).mp he')
    exact ⟨_, ι.isCycle_image hC, Set.mem_image_of_mem _ heC⟩
  exists_leaf_side e' he' w' hw' := by
    obtain ⟨e, rfl⟩ := ι.edge.surjective e'
    obtain ⟨w, rfl⟩ := ι.vert.surjective w'
    have he : ∀ C, IsCycle G.graph C → e ∉ C := fun C hC heC =>
      he' _ (ι.isCycle_image hC) (Set.mem_image_of_mem _ heC)
    obtain ⟨x, hx⟩ := hG.exists_leaf_side e he w ((ι.incident_iff e w).mp hw')
    refine ⟨x, ?_⟩
    rw [ι.leaf]
    refine walks_mono ?_ (ι.walks_image hx)
    rintro _ ⟨g, hg, rfl⟩ h
    exact hg (ι.edge.injective (Set.mem_singleton_iff.mp h))

/-- A node of a cycle is not a taxon. -/
theorem IsUnrootedLevelOne.not_leaf_of_mem [Finite E] {G : SemidirectedNetwork V E X}
    (hG : IsUnrootedLevelOne G) {C : Set E} (hC : IsCycle G.graph C) {u : V}
    (hu : u ∈ cycleNodes G.graph C) : ¬ ∃ x, G.leaf x = u := by
  rintro ⟨x, rfl⟩
  have h2 := hC.ncard_incident hG.loopless hu
  have hd := degree_eq_ncard_incident hG.loopless (G.leaf x)
  rw [hG.degree_leaf x] at hd
  have := Set.ncard_le_ncard (s := {e | e ∈ C ∧ (G.graph.source e = G.leaf x ∨
    G.graph.target e = G.leaf x)}) (t := {e | G.graph.source e = G.leaf x ∨
    G.graph.target e = G.leaf x}) (fun e he => he.2) (Set.toFinite _)
  omega

/-- **A node of a cycle has an edge on no cycle**: its third edge, off the cycle. -/
theorem IsUnrootedLevelOne.exists_offCycle [Finite E] {G : SemidirectedNetwork V E X}
    (hG : IsUnrootedLevelOne G) {C : Set E} (hC : IsCycle G.graph C) {u : V}
    (hu : u ∈ cycleNodes G.graph C) :
    ∃ f, (G.graph.source f = u ∨ G.graph.target f = u) ∧ f ∉ C ∧
      ∀ C', IsCycle G.graph C' → f ∉ C' := by
  have h2 := hC.ncard_incident hG.loopless hu
  have hd := degree_eq_ncard_incident hG.loopless u
  rw [hG.degree_of_not_leaf u (hG.not_leaf_of_mem hC hu)] at hd
  obtain ⟨f, hf, hfC⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (t := {e | G.graph.source e = u ∨ G.graph.target e = u})
    (s := {e | e ∈ C ∧ (G.graph.source e = u ∨ G.graph.target e = u)}) (by omega) (Set.toFinite _)
  have hfC' : f ∉ C := fun h => hfC ⟨h, hf⟩
  refine ⟨f, hf, hfC', fun C' hC' hfC'' => hfC' ?_⟩
  have hu' : u ∈ cycleNodes G.graph C' := hf.elim (fun h => ⟨f, hfC'', Or.inl h⟩)
    (fun h => ⟨f, hfC'', Or.inr h⟩)
  rwa [hG.cycle_eq C C' hC hC' ⟨u, hu, hu'⟩]

/-- **The block of a node of a cycle is the far side of its edge off the cycle.** -/
theorem IsUnrootedLevelOne.mem_nodeBlock_iff [Finite E] {G : SemidirectedNetwork V E X}
    (hG : IsUnrootedLevelOne G) {C : Set E} (hC : IsCycle G.graph C) {u : V}
    (hu : u ∈ cycleNodes G.graph C) {f : E} (hfC : f ∉ C) {v : V} (hj : Joins G.graph f u v)
    (x : X) : x ∈ nodeBlock G.graph G.leaf C u ↔ G.leaf x ∈ cutSide G.graph f v := by
  have hf : ∀ C', IsCycle G.graph C' → f ∉ C' := fun C' hC' hfC' => hfC <| by
    have hu' : u ∈ cycleNodes G.graph C' := hj.incident_left.elim (fun h => ⟨f, hfC', Or.inl h⟩)
      (fun h => ⟨f, hfC', Or.inr h⟩)
    rwa [hG.cycle_eq C C' hC hC' ⟨u, hu, hu'⟩]
  -- the edges at `u` are `f` and edges of `C`
  have hfu : ∀ g, (G.graph.source g = u ∨ G.graph.target g = u) → g ∉ C → g = f := by
    intro g hg hgC
    have h2 := hC.ncard_incident hG.loopless hu
    have hd := degree_eq_ncard_incident hG.loopless u
    rw [hG.degree_of_not_leaf u (hG.not_leaf_of_mem hC hu)] at hd
    by_contra hne
    have hsub : insert g (insert f {e | e ∈ C ∧ (G.graph.source e = u ∨ G.graph.target e = u)}) ⊆
        {e | G.graph.source e = u ∨ G.graph.target e = u} := by
      rintro e (rfl | rfl | he)
      · exact hg
      · exact hj.incident_left
      · exact he.2
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h₁ : g ∉ insert f {e | e ∈ C ∧ (G.graph.source e = u ∨ G.graph.target e = u)} := by
      rintro (h | h)
      exacts [hne h, hgC h.1]
    have h₂ : f ∉ {e | e ∈ C ∧ (G.graph.source e = u ∨ G.graph.target e = u)} := fun h => hfC h.1
    rw [Set.ncard_insert_of_notMem h₁, Set.ncard_insert_of_notMem h₂] at this
    omega
  -- the nodes of `C` are on the side of `u`
  have hCu : ∀ w ∈ cycleNodes G.graph C, w ∈ cutSide G.graph f u := by
    intro w hw
    obtain ⟨g, hg, -⟩ := id hu
    refine walks_mono (fun e he => ?_) (hC.walks_sdiff_singleton hg hu hw)
    intro h
    exact hfC (Set.mem_singleton_iff.1 h ▸ he.1)
  have hcut := mem_cutSide_iff_notMem hG.connected hf hj
  have hnl := hG.not_leaf_of_mem hC hu
  constructor
  · intro h
    -- along a walk avoiding `C`, every node is `u` or on the side of `v`
    suffices key : ∀ w, G.graph.Walks Cᶜ u w → w = u ∨ w ∈ cutSide G.graph f v by
      rcases key _ h with h' | h'
      · exact absurd ⟨x, h'⟩ hnl
      · exact h'
    intro w hw
    induction hw with
    | refl => exact Or.inl rfl
    | @tail a b _ hab ih =>
      obtain ⟨g, hgC, hg⟩ := hab
      rcases ih with rfl | ha
      · have hgf := hfu g (hg.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)) hgC
        subst hgf
        right
        rw [Joins.eq_right hg hj]
        exact Relation.ReflTransGen.refl
      · by_cases hgf : g = f
        · subst hgf
          have hb : b = u ∨ b = v := by
            rcases Joins.incident_right hg with h | h <;> rcases hj with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
            · exact Or.inl (h.symm.trans h₃)
            · exact Or.inr (h.symm.trans h₃)
            · exact Or.inr (h.symm.trans h₄)
            · exact Or.inl (h.symm.trans h₄)
          rcases hb with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr Relation.ReflTransGen.refl
        · exact Or.inr (Relation.ReflTransGen.tail ha ⟨g, hgf, hg⟩)
  · intro h
    -- the walk from `v` avoiding `f` avoids `C`, which is on the side of `u`
    have hv : G.graph.Walks Cᶜ u v := .single ⟨f, hfC, hj⟩
    refine hv.trans ?_
    suffices key : ∀ w, G.graph.Walks {f}ᶜ v w → G.graph.Walks Cᶜ v w from key _ h
    intro w hw
    induction hw with
    | refl => exact .refl
    | @tail a b hva hab ih =>
      obtain ⟨g, hgf, hg⟩ := hab
      refine ih.tail ⟨g, fun hgC => ?_, hg⟩
      have ha : a ∈ cycleNodes G.graph C :=
        hg.elim (fun h => ⟨g, hgC, Or.inl h.1⟩) (fun h => ⟨g, hgC, Or.inr h.2⟩)
      exact (hcut a).mp hva (hCu a ha)

/-! ### The contracted network of `Ñ` -/

/-- **Every edge lies on a chain** when the edges at the nodes removed by suppression are bridges: a
longest path through removed nodes containing the edge ends at kept nodes, since a removed node has
a second edge, which leads to a new node. -/
theorem exists_isChain_mem_of_bridge [Finite V] [Finite E] {K : SemidirectedNetwork V E X}
    {P : Set V} (hloop : ∀ e, K.graph.source e ≠ K.graph.target e)
    (hbr : ∀ e u, ¬ IsBranch K P u → (K.graph.source e = u ∨ K.graph.target e = u) →
      ¬ K.graph.Walks {e}ᶜ (K.graph.source e) (K.graph.target e)) (g : E) :
    ∃ c, IsChain K P c ∧ g ∈ c := by
  -- extending a path through suppressed nodes at its last node
  have hext : ∀ (n k : ℕ) (p : Fin (k + 1) → V) (e : Fin k → E), Nat.card V - k = n → 0 < k →
      IsPathOf K.graph Set.univ k p e →
      (∀ i : Fin (k + 1), i ≠ 0 → i ≠ Fin.last k → ¬ IsBranch K P (p i)) → g ∈ Set.range e →
      ∃ (k' : ℕ) (p' : Fin (k' + 1) → V) (e' : Fin k' → E), 0 < k' ∧
        IsPathOf K.graph Set.univ k' p' e' ∧
        (∀ i : Fin (k' + 1), i ≠ 0 → i ≠ Fin.last k' → ¬ IsBranch K P (p' i)) ∧
        g ∈ Set.range e' ∧ p' 0 = p 0 ∧ IsBranch K P (p' (Fin.last k')) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro k p e hn hk hP hin hg
    by_cases hb : IsBranch K P (p (Fin.last k))
    · exact ⟨k, p, e, hk, hP, hin, hg, rfl, hb⟩
    have hdeg : degree K.graph (p (Fin.last k)) = 2 := by
      by_contra h
      exact hb (Or.inl h)
    obtain ⟨j, hj⟩ : ∃ j : Fin k, j.succ = Fin.last k :=
      ⟨⟨k - 1, by omega⟩, Fin.ext (by simp; omega)⟩
    have hinc : K.graph.source (e j) = p (Fin.last k) ∨ K.graph.target (e j) = p (Fin.last k) := by
      rcases hP.link j with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr (hj ▸ h)
      · exact Or.inl (hj ▸ h)
    obtain ⟨f, hfe, hf⟩ := exists_ne_incident_of_degree_eq_two hdeg (hloop (e j)) hinc
    -- the other end `z` of `f`
    set z := if K.graph.source f = p (Fin.last k) then K.graph.target f else K.graph.source f
      with hz_def
    have hfz : (K.graph.source f = p (Fin.last k) ∧ K.graph.target f = z) ∨
        (K.graph.source f = z ∧ K.graph.target f = p (Fin.last k)) := by
      by_cases hs : K.graph.source f = p (Fin.last k)
      · exact Or.inl ⟨hs, by simp [z, hs]⟩
      · exact Or.inr ⟨by simp [z, hs], hf.resolve_left hs⟩
    -- `f` is not on the path
    have hfP : f ∉ Set.range e := by
      rintro ⟨l, rfl⟩
      rcases hP.eq_or_eq_of_end l hf with h | h
      · have := congrArg Fin.val (hP.injective h)
        simp at this
        omega
      · apply hfe
        congr 1
        have h' := hP.injective h
        exact Fin.succ_injective _ (h'.symm.trans hj.symm)
    -- `z` is a new node, else `f`, an edge at a removed node, would close a cycle with the path
    have hz : z ∉ Set.range p := by
      rintro ⟨i, hi⟩
      have hw : K.graph.Walks {f}ᶜ (p i) (p (Fin.last k)) := by
        refine walks_mono (fun f' hf' => ?_) (hP.walks_of_le (Fin.le_last i))
        obtain ⟨l, -, -, rfl⟩ := hf'
        exact fun h => hfP ⟨l, h⟩
      apply hbr f _ hb hf
      rcases hfz with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂, ← hi]
        exact K.graph.walks_symm hw
      · rw [h₁, h₂, ← hi]
        exact hw
    have hP' := hP.snoc hz (Set.mem_univ f) hfz
    have hcard : k + 2 ≤ Nat.card V := by
      have := Nat.card_le_card_of_injective _ hP'.injective
      simp at this
      omega
    obtain ⟨k', p', e', hk', hP'', hin', hg', h0, hb'⟩ := ih (Nat.card V - (k + 1)) (by omega)
      (k + 1) _ _ rfl (by omega) hP' (fun i hi0 hil => by
        induction i using Fin.lastCases with
        | last => exact absurd rfl hil
        | cast i =>
          rw [Fin.snoc_castSucc]
          by_cases hil' : i = Fin.last k
          · subst hil'
            exact hb
          · exact hin i (fun h => hi0 (by rw [h]; rfl)) hil')
      (by
        obtain ⟨l, rfl⟩ := hg
        exact ⟨l.castSucc, Fin.snoc_castSucc (α := fun _ => E) ..⟩)
    refine ⟨k', p', e', hk', hP'', hin', hg', ?_, hb'⟩
    rw [h0]
    exact Fin.snoc_castSucc (α := fun _ => V) (i := 0) ..
  -- the edge `g` alone, extended at both ends
  have hg0 : IsPathOf K.graph Set.univ 1 ![K.graph.source g, K.graph.target g] ![g] := by
    refine ⟨fun _ => Set.mem_univ _, fun i => ?_, fun i j h => ?_⟩
    · fin_cases i
      exact Or.inl ⟨rfl, rfl⟩
    · fin_cases i <;> fin_cases j
      · rfl
      · exact absurd h (hloop g)
      · exact absurd h.symm (hloop g)
      · rfl
  obtain ⟨k₁, p₁, e₁, hk₁, hP₁, hin₁, hg₁, -, hb₁⟩ := hext _ 1 _ _ rfl one_pos hg0
    (fun i hi0 hil => by fin_cases i <;> simp_all) ⟨0, rfl⟩
  obtain ⟨k₂, p₂, e₂, hk₂, hP₂, hin₂, hg₂, h0₂, hb₂⟩ := hext _ k₁ _ _ rfl hk₁ hP₁.rev
    (fun i hi0 hil => hin₁ (Fin.rev i)
      (fun h' => hil (by rw [← Fin.rev_rev i, h', Fin.rev_zero]))
      (fun h' => hi0 (by rw [← Fin.rev_rev i, h', Fin.rev_last])))
    (by
      obtain ⟨l, rfl⟩ := hg₁
      exact ⟨Fin.rev l, by simp⟩)
  refine ⟨Set.range e₂, ⟨k₂, p₂, e₂, ⟨hk₂, fun i => hP₂.link i, hin₂, ⟨?_, hb₂⟩,
    hP₂.injective_edge⟩, rfl⟩, hg₂⟩
  rw [h0₂]
  simpa using hb₁

section TildeContracted

variable [Finite E] {G : SemidirectedNetwork V E X} (hG : IsUnrootedLevelOne G)
include hG

/-- A node of a cycle has degree three. -/
theorem IsUnrootedLevelOne.degree_of_mem {C : Set E} (hC : IsCycle G.graph C) {u : V}
    (hu : u ∈ cycleNodes G.graph C) : degree G.graph u = 3 :=
  hG.degree_of_not_leaf u (hG.not_leaf_of_mem hC hu)

omit [Finite E] in
/-- **Contracting the 2- and 3-cycles identifies exactly the nodes of each.** -/
theorem tildeContracted_mk_eq_iff {a b : V} :
    (Quot.mk _ a : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) = Quot.mk _ b ↔
      a = b ∨ ∃ C, IsCycle G.graph C ∧ C.ncard ≤ 3 ∧ a ∈ cycleNodes G.graph C ∧
        b ∈ cycleNodes G.graph C := by
  constructor
  · intro h
    have hg := Quot.eqvGen_exact h
    clear h
    induction hg with
    | rel x y hxy =>
      obtain ⟨C, hC, hP, hx, hy⟩ := hxy
      exact Or.inr ⟨C, hC, hP, hx, hy⟩
    | refl => exact Or.inl rfl
    | symm x y _ ih =>
      rcases ih with rfl | ⟨C, hC, hP, h₁, h₂⟩
      exacts [Or.inl rfl, Or.inr ⟨C, hC, hP, h₂, h₁⟩]
    | trans x y z _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨C, hC, hP, h₁, h₂⟩
      · exact ih₂
      · rcases ih₂ with rfl | ⟨C', hC', hP', h₁', h₂'⟩
        · exact Or.inr ⟨C, hC, hP, h₁, h₂⟩
        · obtain rfl := hG.cycle_eq C C' hC hC' ⟨y, h₂, h₁'⟩
          exact Or.inr ⟨C, hC, hP, h₁, h₂'⟩
  · rintro (rfl | ⟨C, hC, hP, h₁, h₂⟩)
    · rfl
    · exact Quot.sound ⟨C, hC, hP, h₁, h₂⟩

omit [Finite E] in
/-- A node on no 2- or 3-cycle keeps its degree in the contraction. -/
theorem degree_tildeContracted_of_notMem {v : V}
    (hv : ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → v ∉ cycleNodes G.graph C) :
    degree (tildeContracted G).graph (Quot.mk _ v) = degree G.graph v := by
  have hcls : ∀ w, (Quot.mk _ w : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) =
      Quot.mk _ v ↔ w = v := fun w => by
    rw [tildeContracted_mk_eq_iff hG]
    constructor
    · rintro (h | ⟨C, hC, hP, -, hvC⟩)
      exacts [h, absurd hvC (hv C hC hP)]
    · exact Or.inl
  have hall : ∀ e : E, (G.graph.source e = v ∨ G.graph.target e = v) →
      ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → e ∉ C := by
    intro e he C hC hP heC
    rcases he with he | he
    · exact hv C hC hP ⟨e, heC, Or.inl he⟩
    · exact hv C hC hP ⟨e, heC, Or.inr he⟩
  unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree
  congr 1
  · refine Set.ncard_congr (fun e _ => e.1) (fun e he => (hcls _).1 he)
      (fun e e' _ _ h => Subtype.ext h) fun e he => ⟨⟨e, hall e (Or.inr he)⟩, (hcls _).2 he, rfl⟩
  · refine Set.ncard_congr (fun e _ => e.1) (fun e he => (hcls _).1 he)
      (fun e e' _ _ h => Subtype.ext h) fun e he => ⟨⟨e, hall e (Or.inl he)⟩, (hcls _).2 he, rfl⟩

omit [Finite E] in
/-- **The contracted network has no loops**: an edge joining two nodes of a cycle `C` would close a
cycle sharing their nodes with `C`, so would be an edge of `C`. -/
theorem tildeContracted_loopless (g) :
    (tildeContracted G).graph.source g ≠ (tildeContracted G).graph.target g := by
  intro h
  rcases (tildeContracted_mk_eq_iff hG).1 h with h' | ⟨C, hC, hP, hs, ht⟩
  · exact hG.loopless g.1 h'
  · have hgC : g.1 ∉ C := g.2 C hC hP
    obtain ⟨c, hc, -⟩ := id hs
    have hw : G.graph.Walks C (G.graph.target g.1) (G.graph.source g.1) :=
      walks_mono Set.sdiff_subset (hC.walks_sdiff_singleton hc ht hs)
    obtain ⟨D, hD, hgD, hDC⟩ := exists_isCycle_of_walks hgC hw
    have := hG.cycle_eq C D hC hD ⟨G.graph.source g.1, hs, ⟨g.1, hgD, Or.inl rfl⟩⟩
    exact hgC (this ▸ hgD)

/-- **A contracted 2- or 3-cycle has degree its size.** -/
theorem degree_tildeContracted_of_mem {C : Set E} (hC : IsCycle G.graph C) (hP : C.ncard ≤ 3)
    {v : V} (hv : v ∈ cycleNodes G.graph C) :
    degree (tildeContracted G).graph (Quot.mk _ v) = C.ncard := by
  have hloop := hG.loopless
  have hcls : ∀ w, (Quot.mk _ w : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) =
      Quot.mk _ v ↔ w ∈ cycleNodes G.graph C := fun w => by
    rw [tildeContracted_mk_eq_iff hG]
    constructor
    · rintro (rfl | ⟨C', hC', -, hw, hv'⟩)
      · exact hv
      · rwa [hG.cycle_eq C' C hC' hC ⟨v, hv', hv⟩] at hw
    · intro hw
      exact Or.inr ⟨C, hC, hP, hw, hv⟩
  -- one edge off the cycle at each of its nodes
  have hone : ∀ w ∈ cycleNodes G.graph C,
      {e | (G.graph.source e = w ∨ G.graph.target e = w) ∧ e ∉ C}.ncard = 1 := by
    intro w hw
    have h2 := hC.ncard_incident hloop hw
    have hd := degree_eq_ncard_incident hloop w
    rw [hG.degree_of_mem hC hw] at hd
    have := Set.ncard_inter_add_ncard_sdiff_eq_ncard
      {e | G.graph.source e = w ∨ G.graph.target e = w} C
    have hi : {e | G.graph.source e = w ∨ G.graph.target e = w} ∩ C =
        {e | e ∈ C ∧ (G.graph.source e = w ∨ G.graph.target e = w)} := by
      ext e
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hi, h2] at this
    have hd' : {e | G.graph.source e = w ∨ G.graph.target e = w} \ C =
        {e | (G.graph.source e = w ∨ G.graph.target e = w) ∧ e ∉ C} := rfl
    rw [hd'] at this
    omega
  have hoff : ∀ w ∈ cycleNodes G.graph C, ∀ e e' : E, ((G.graph.source e = w ∨
      G.graph.target e = w) ∧ e ∉ C) → ((G.graph.source e' = w ∨ G.graph.target e' = w) ∧ e' ∉ C) →
      e = e' := by
    intro w hw e e' he he'
    obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 (hone w hw)
    have h1 : e ∈ ({e₀} : Set E) := he₀ ▸ he
    have h2 : e' ∈ ({e₀} : Set E) := he₀ ▸ he'
    rw [Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  have hloopT := tildeContracted_loopless hG
  rw [degree_eq_ncard_incident hloopT, ← ncard_cycleNodes hC]
  refine Set.ncard_congr (fun e _ => if G.graph.source e.1 ∈ cycleNodes G.graph C then
    G.graph.source e.1 else G.graph.target e.1) ?_ ?_ ?_
  · intro e he
    split_ifs with h
    · exact h
    · rcases he with he | he
      · exact absurd ((hcls _).1 he) h
      · exact (hcls _).1 he
  · intro e e' he he' heq
    have hnot : ∀ f : {e // ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → e ∉ C}, f.1 ∉ C := fun f =>
      f.2 C hC hP
    have hinc : ∀ f : {e // ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → e ∉ C},
        f ∈ {e : {e // ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → e ∉ C} |
          (tildeContracted G).graph.source e = Quot.mk _ v ∨
            (tildeContracted G).graph.target e = Quot.mk _ v} →
        (if G.graph.source f.1 ∈ cycleNodes G.graph C then G.graph.source f.1
          else G.graph.target f.1) ∈ cycleNodes G.graph C ∧
        ((G.graph.source f.1 = (if G.graph.source f.1 ∈ cycleNodes G.graph C then
          G.graph.source f.1 else G.graph.target f.1) ∨ G.graph.target f.1 =
          (if G.graph.source f.1 ∈ cycleNodes G.graph C then G.graph.source f.1
            else G.graph.target f.1)) ∧ f.1 ∉ C) := by
      intro f hf
      split_ifs with h
      · exact ⟨h, Or.inl rfl, hnot f⟩
      · refine ⟨?_, Or.inr rfl, hnot f⟩
        rcases hf with hf | hf
        · exact absurd ((hcls _).1 hf) h
        · exact (hcls _).1 hf
    obtain ⟨hw, he₁⟩ := hinc e he
    obtain ⟨-, he₂⟩ := hinc e' he'
    rw [← heq] at he₂
    exact Subtype.ext (hoff _ hw _ _ he₁ he₂)
  · intro w hw
    obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 (hone w hw)
    have hmem : e₀ ∈ {e | (G.graph.source e = w ∨ G.graph.target e = w) ∧ e ∉ C} := by
      rw [he₀]; exact Set.mem_singleton _
    obtain ⟨hinc, hnC⟩ := hmem
    -- `e₀` is on no 2- or 3-cycle
    have hoffc : ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e₀ ∉ C' := by
      intro C' hC' _ he₀C'
      have hwC' : w ∈ cycleNodes G.graph C' := by
        rcases hinc with h | h
        exacts [⟨e₀, he₀C', Or.inl h⟩, ⟨e₀, he₀C', Or.inr h⟩]
      rw [hG.cycle_eq C' C hC' hC ⟨w, hwC', hw⟩] at he₀C'
      exact hnC he₀C'
    refine ⟨⟨e₀, hoffc⟩, ?_, ?_⟩
    · rcases hinc with h | h
      · exact Or.inl ((hcls _).2 (h ▸ hw))
      · exact Or.inr ((hcls _).2 (h ▸ hw))
    · split_ifs with h
      · rcases hinc with h' | h'
        · exact h'
        · exact absurd (((hcls _).2 h).trans ((hcls _).2 (h' ▸ hw)).symm)
            (hloopT ⟨e₀, hoffc⟩)
      · exact hinc.resolve_left fun h' => h (h' ▸ hw)

/-- **A node of the contracted network is kept by suppression exactly when its degree is not
two**: a taxon has degree one. -/
theorem isBranch_tildeContracted_iff (q : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) :
    IsBranch (tildeContracted G) ∅ q ↔ degree (tildeContracted G).graph q ≠ 2 := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | ⟨x, rfl⟩ | h
  · exact h
  · change degree (tildeContracted G).graph (Quot.mk _ (G.leaf x)) ≠ 2
    rw [degree_tildeContracted_of_notMem hG fun C hC _ hx => hG.not_leaf_of_mem hC hx ⟨x, rfl⟩,
      hG.degree_leaf x]
    omega
  · exact absurd h (Set.notMem_empty _)

/-- **An edge at a node of degree two of the contracted network lies on no cycle**: an edge on a
cycle of size at least four has ends of degree three, which no contraction touches. -/
theorem notMem_cycle_of_degree_eq_two {q : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)}
    (hq : degree (tildeContracted G).graph q = 2) {g}
    (hg : (tildeContracted G).graph.source g = q ∨ (tildeContracted G).graph.target g = q) :
    ∀ C, IsCycle G.graph C → g.1 ∉ C := by
  intro D hD hgD
  have hbig : ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → ∀ w ∈ cycleNodes G.graph D,
      w ∉ cycleNodes G.graph C := fun C hC hP w hwD hwC =>
    g.2 C hC hP (hG.cycle_eq D C hD hC ⟨w, hwD, hwC⟩ ▸ hgD)
  obtain ⟨w, hw, rfl⟩ : ∃ w ∈ cycleNodes G.graph D, Quot.mk _ w = q := by
    rcases hg with h | h
    · exact ⟨_, ⟨g.1, hgD, Or.inl rfl⟩, h⟩
    · exact ⟨_, ⟨g.1, hgD, Or.inr rfl⟩, h⟩
  rw [degree_tildeContracted_of_notMem hG fun C hC hP => hbig C hC hP w hw,
    hG.degree_of_mem hD hw] at hq
  omega

omit [Finite E] hG in
/-- **An edge of the contracted network whose ends are joined without it lies on a cycle** of the
network. -/
theorem exists_mem_cycle_of_tildeContracted_walks {g}
    (h : (tildeContracted G).graph.Walks {g}ᶜ ((tildeContracted G).graph.source g)
      ((tildeContracted G).graph.target g)) : ∃ C, IsCycle G.graph C ∧ g.1 ∈ C := by
  by_contra hn
  push Not at hn
  have hw := walks_of_contract_walks (G := G) (P := fun C => C.ncard ≤ 3)
    (a := G.graph.source g.1) (b := G.graph.target g.1) h
  have hnot : g.1 ∉ Subtype.val '' ({g}ᶜ : Set _) ∪ {e | ∃ C, IsCycle G.graph C ∧ e ∈ C} := by
    rintro (⟨g', hg', hgg⟩ | ⟨C, hC, hgC⟩)
    · exact hg' (Subtype.ext hgg)
    · exact hn C hC hgC
  obtain ⟨C, hC, hgC, -⟩ := exists_isCycle_of_walks hnot (G.graph.walks_symm hw)
  exact hn C hC hgC

/-- **The edges at the nodes of the contracted network removed by suppression are bridges.** -/
theorem tildeContracted_bridge (e) (u : Quot (ContractRel G.graph fun C => C.ncard ≤ 3))
    (hu : ¬ IsBranch (tildeContracted G) ∅ u)
    (he : (tildeContracted G).graph.source e = u ∨ (tildeContracted G).graph.target e = u) :
    ¬ (tildeContracted G).graph.Walks {e}ᶜ ((tildeContracted G).graph.source e)
      ((tildeContracted G).graph.target e) := by
  intro hw
  have hdeg : degree (tildeContracted G).graph u = 2 := by
    by_contra h
    exact hu (Or.inl h)
  obtain ⟨C, hC, heC⟩ := exists_mem_cycle_of_tildeContracted_walks hw
  exact notMem_cycle_of_degree_eq_two hG hdeg he C hC heC

/-- **Every edge of the contracted network lies on a chain.** -/
theorem exists_isChain_tildeContracted [Finite V] (g) :
    ∃ c, IsChain (tildeContracted G) ∅ c ∧ g ∈ c :=
  exists_isChain_mem_of_bridge (tildeContracted_loopless hG) (tildeContracted_bridge hG) g

/-- **The ends of a hybrid edge of the contracted network are kept by suppression**: a hybrid edge
lies on a cycle of size at least four, whose nodes have degree three. -/
theorem tildeContracted_isBranch_of_isDirected {e} (hd : (tildeContracted G).IsDirected e) :
    IsBranch (tildeContracted G) ∅ ((tildeContracted G).graph.source e) ∧
      IsBranch (tildeContracted G) ∅ ((tildeContracted G).graph.target e) := by
  obtain ⟨D, hD, heD⟩ := hG.mem_cycle_of_isDirected _ hd.1
  have hbig : ∀ w ∈ cycleNodes G.graph D, ∀ C, IsCycle G.graph C → C.ncard ≤ 3 →
      w ∉ cycleNodes G.graph C := fun w hwD C hC hP hwC =>
    e.2 C hC hP (hG.cycle_eq D C hD hC ⟨w, hwD, hwC⟩ ▸ heD)
  have hb : ∀ w ∈ cycleNodes G.graph D,
      IsBranch (tildeContracted G) ∅ (Quot.mk _ w) := fun w hw => by
    rw [isBranch_tildeContracted_iff hG, degree_tildeContracted_of_notMem hG (hbig w hw),
      hG.degree_of_mem hD hw]
    omega
  exact ⟨hb _ ⟨e.1, heD, Or.inl rfl⟩, hb _ ⟨e.1, heD, Or.inr rfl⟩⟩

/-- **The edges of a chain of at least two edges lie on no cycle**: each is at an inner node, of
degree two. -/
theorem IsChainOf.notMem_cycle_tildeContracted {k : ℕ} {p} {e : Fin k → _}
    (h : IsChainOf (tildeContracted G) ∅ k p e) (hk : 2 ≤ k) (i : Fin k) :
    ∀ C, IsCycle G.graph C → (e i).1 ∉ C := by
  have hinner : ∀ j : Fin (k + 1), j ≠ 0 → j ≠ Fin.last k →
      degree (tildeContracted G).graph (p j) = 2 := fun j h0 hl => by
    by_contra hd
    exact h.inner j h0 hl (Or.inl hd)
  by_cases hi : (i : ℕ) = 0
  · have h1 : i.succ ≠ 0 := Fin.succ_ne_zero i
    have h2 : i.succ ≠ Fin.last k := fun h' => by
      have := congrArg Fin.val h'
      simp at this
      omega
    exact notMem_cycle_of_degree_eq_two hG (hinner _ h1 h2) (h.joins i).incident_right
  · have h1 : i.castSucc ≠ 0 := fun h' => hi (by simpa using congrArg Fin.val h')
    exact notMem_cycle_of_degree_eq_two hG (hinner _ h1 (Fin.castSucc_ne_last i))
      (h.joins i).incident_left

end TildeContracted

/-! ### The two sides of an edge on no cycle, in `Ñ` -/

section Sides

variable {G : SemidirectedNetwork V E X} {f : E} {y y' : V}

/-- The nodes of the contracted network on the side of `y` of the edge `f`. -/
def contractSide (G : SemidirectedNetwork V E X) (f : E) (y : V) :
    Set (Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) :=
  {q | ∃ x ∈ cutSide G.graph f y, q = Quot.mk _ x}

theorem mem_tildeCutSide_iff {w : {u // IsBranch (tildeContracted G) ∅ u}} :
    w ∈ tildeCutSide G f y ↔ w.1 ∈ contractSide G f y := Iff.rfl

/-- The nodes identified by the contraction are on the same side of an edge on no cycle. -/
theorem mem_cutSide_of_mk_eq (hf : ∀ C, IsCycle G.graph C → f ∉ C) {a b : V}
    (h : (Quot.mk _ a : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) = Quot.mk _ b)
    (ha : a ∈ cutSide G.graph f y) : b ∈ cutSide G.graph f y := by
  have hw : G.graph.Walks {e | ∃ C, IsCycle G.graph C ∧ e ∈ C} a b := walks_of_contract_eq h
  refine Relation.ReflTransGen.trans ha (walks_mono ?_ hw)
  rintro e ⟨C, hC, heC⟩ hef
  exact hf C hC (Set.mem_singleton_iff.1 hef ▸ heC)

theorem mk_mem_contractSide_iff (hf : ∀ C, IsCycle G.graph C → f ∉ C) (a : V) :
    Quot.mk _ a ∈ contractSide G f y ↔ a ∈ cutSide G.graph f y :=
  ⟨fun ⟨_, hx, h⟩ => mem_cutSide_of_mk_eq hf h.symm hx, fun h => ⟨a, h, rfl⟩⟩

/-- A node of the contracted network is on the side of exactly one end of `f`. -/
theorem mem_contractSide_iff_notMem (hG : G.graph.IsConnected) (hf : ∀ C, IsCycle G.graph C → f ∉ C)
    (hj : Joins G.graph f y y') (q : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) :
    q ∈ contractSide G f y' ↔ q ∉ contractSide G f y := by
  induction q using Quot.ind with
  | mk a =>
    rw [mk_mem_contractSide_iff hf, mk_mem_contractSide_iff hf]
    exact mem_cutSide_iff_notMem hG hf hj a

/-- An edge of the contracted network other than `f` has its ends on the same side of `f`. -/
theorem source_mem_contractSide_iff (hf : ∀ C, IsCycle G.graph C → f ∉ C) {g} (hg : g.1 ≠ f) :
    (tildeContracted G).graph.source g ∈ contractSide G f y ↔
      (tildeContracted G).graph.target g ∈ contractSide G f y := by
  change Quot.mk _ _ ∈ _ ↔ Quot.mk _ _ ∈ _
  rw [mk_mem_contractSide_iff hf, mk_mem_contractSide_iff hf]
  have hstep : G.graph.AdjOn {f}ᶜ (G.graph.source g.1) (G.graph.target g.1) :=
    ⟨g.1, hg, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨fun h => Relation.ReflTransGen.tail h hstep,
    fun h => Relation.ReflTransGen.tail h (G.graph.adjOn_symm hstep)⟩

/-- Along a sequence of linked nodes, a property kept by each link is kept. -/
theorem iff_of_forall_link {α : Type*} {k : ℕ} (p : Fin (k + 1) → α) (S : α → Prop) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k)
    (h : ∀ l (hl : l < k), i ≤ l → l < j → (S (p ⟨l, by omega⟩) ↔ S (p ⟨l + 1, by omega⟩))) :
    S (p ⟨i, by omega⟩) ↔ S (p ⟨j, by omega⟩) := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact Iff.rfl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact Iff.rfl
    · exact (ih (by omega) (by omega) fun l hl h₁ h₂ => h l hl h₁ (by omega)).trans
        (h j (by omega) (by omega) (by omega))

/-- **The ends of a chain of the contracted network are on the same side of `f`** when the chain
does not contain `f`, and on opposite sides when it does. -/
theorem IsChainOf.mem_contractSide_iff (hG : G.graph.IsConnected)
    (hf : ∀ C, IsCycle G.graph C → f ∉ C) (hj : Joins G.graph f y y') {k : ℕ} {p} {e : Fin k → _}
    (h : IsChainOf (tildeContracted G) ∅ k p e) :
    ((∀ i, (e i).1 ≠ f) → (p 0 ∈ contractSide G f y ↔ p (Fin.last k) ∈ contractSide G f y)) ∧
      ((∃ i, (e i).1 = f) → (p 0 ∈ contractSide G f y ↔ p (Fin.last k) ∉ contractSide G f y)) := by
  have hlink : ∀ l (hl : l < k), (e ⟨l, hl⟩).1 ≠ f →
      (p ⟨l, by omega⟩ ∈ contractSide G f y ↔ p ⟨l + 1, by omega⟩ ∈ contractSide G f y) := by
    intro l hl hne
    have hjl := h.joins ⟨l, hl⟩
    have := source_mem_contractSide_iff (y := y) hf hne
    rcases hjl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at this
      exact this
    · rw [h₁, h₂] at this
      exact this.symm
  have hlast : Fin.last k = ⟨k, by omega⟩ := rfl
  have h0 : (0 : Fin (k + 1)) = ⟨0, by omega⟩ := rfl
  refine ⟨fun hne => ?_, fun ⟨i, hi⟩ => ?_⟩
  · rw [hlast, h0]
    exact iff_of_forall_link p (· ∈ contractSide G f y) (Nat.zero_le _) le_rfl
      fun l hl _ _ => hlink l hl (hne _)
  · have hne : ∀ l (hl : l < k), l ≠ i → (e ⟨l, hl⟩).1 ≠ f := fun l hl hli h' => hli <| by
      have := h.injective_edge (Subtype.ext (h'.trans hi.symm))
      exact congrArg Fin.val this
    have h₁ := iff_of_forall_link p (· ∈ contractSide G f y) (Nat.zero_le i.val) (Nat.le_of_lt i.2)
      fun l hl _ h' => hlink l hl (hne l hl (by omega))
    have h₂ := iff_of_forall_link p (· ∈ contractSide G f y) (Nat.succ_le_of_lt i.2) le_rfl
      fun l hl h' _ => hlink l hl (hne l hl (by omega))
    -- the ends of `f`
    have hmid : p ⟨i, by omega⟩ ∈ contractSide G f y ↔
        p ⟨i + 1, by omega⟩ ∉ contractSide G f y := by
      have hji := h.joins i
      have hy : Quot.mk _ y ∈ contractSide G f y := ⟨y, Relation.ReflTransGen.refl, rfl⟩
      have hy' : Quot.mk _ y' ∉ contractSide G f y := by
        rw [← mem_contractSide_iff_notMem hG hf hj]
        exact ⟨y', Relation.ReflTransGen.refl, rfl⟩
      have hs : (tildeContracted G).graph.source (e i) = Quot.mk _ (G.graph.source f) :=
        congrArg (Quot.mk _) (congrArg G.graph.source hi)
      have ht : (tildeContracted G).graph.target (e i) = Quot.mk _ (G.graph.target f) :=
        congrArg (Quot.mk _) (congrArg G.graph.target hi)
      change p i.castSucc ∈ _ ↔ p i.succ ∉ _
      rcases hji with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hj with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ <;>
        rw [← h₁, ← h₂, hs, ht] <;> simp only [h₃, h₄] <;> tauto
    rw [hlast, h0]
    rw [h₁, hmid, h₂]

end Sides

/-! ### The far side of a bridge -/

section Bridges

variable {G : DirectedMultigraph V E}

/-- An edge on no cycle does not join its ends avoiding itself. -/
theorem not_walks_of_joins {e : E} (he : ∀ C, IsCycle G C → e ∉ C) {a b : V} (hj : Joins G e a b) :
    ¬ G.Walks {e}ᶜ a b := by
  intro h
  rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact not_walks_of_forall_notMem he (h₁ ▸ h₂ ▸ h)
  · exact not_walks_of_forall_notMem he (h₁ ▸ h₂ ▸ G.walks_symm h)

/-- A node at an edge joining `a` and `b` is `a` or `b`. -/
theorem Joins.eq_or_eq {e : E} {a b c : V} (hj : Joins G e a b)
    (hc : G.source e = c ∨ G.target e = c) : c = a ∨ c = b := by
  rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hc with h | h
  · exact Or.inl (h.symm.trans h₁)
  · exact Or.inr (h.symm.trans h₂)
  · exact Or.inr (h.symm.trans h₁)
  · exact Or.inl (h.symm.trans h₂)

/-- An edge at a node joins it to some node. -/
theorem exists_joins_of_incident {e : E} {a : V} (h : G.source e = a ∨ G.target e = a) :
    ∃ b, Joins G e a b := by
  rcases h with h | h
  · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨rfl, h⟩⟩

/-- **The far sides of two bridges whose near ends are joined avoiding both are disjoint.** -/
theorem notMem_cutSide_of_walks {e₁ e₂ : E} (he₁ : ∀ C, IsCycle G C → e₁ ∉ C)
    (he₂ : ∀ C, IsCycle G C → e₂ ∉ C) (hne : e₁ ≠ e₂) {x₁ z₁ x₂ z₂ : V} (hj₁ : Joins G e₁ x₁ z₁)
    (hj₂ : Joins G e₂ x₂ z₂) (hw : G.Walks ({e₁}ᶜ ∩ {e₂}ᶜ) x₁ x₂) {w : V}
    (hw₁ : w ∈ cutSide G e₁ z₁) : w ∉ cutSide G e₂ z₂ := by
  intro hw₂
  have hx₁ : x₁ ∉ cutSide G e₂ z₂ := fun h => not_walks_of_joins he₂ hj₂
    (G.walks_symm (Relation.ReflTransGen.trans h (walks_mono Set.inter_subset_right hw)))
  have hz₁ : z₁ ∉ cutSide G e₂ z₂ := fun h => hx₁ (Relation.ReflTransGen.tail h
    ⟨e₁, hne, Or.symm hj₁⟩)
  -- along a walk avoiding `e₁` from `w`, the far side of `e₂` is left only through `e₂`, at `x₂`
  have key : ∀ u, G.Walks {e₁}ᶜ w u → u ∈ cutSide G e₂ z₂ ∨ G.Walks {e₁}ᶜ x₂ u := by
    intro u hu
    induction hu with
    | refl => exact Or.inl hw₂
    | @tail a b _ hab ih =>
      obtain ⟨g, hg, hgj⟩ := hab
      rcases ih with ha | ha
      · by_cases hge : g = e₂
        · subst hge
          rcases hj₂.eq_or_eq (Joins.incident_right hgj) with rfl | rfl
          · exact Or.inr .refl
          · exact Or.inl .refl
        · exact Or.inl (Relation.ReflTransGen.tail ha ⟨g, hge, hgj⟩)
      · exact Or.inr (ha.tail ⟨g, hg, hgj⟩)
  rcases key z₁ (G.walks_symm hw₁) with h | h
  · exact hz₁ h
  · exact not_walks_of_joins he₁ hj₁ ((walks_mono Set.inter_subset_left hw).trans h)

/-- **The far side of a bridge off `f`, on the side of `y'` of `f` and away from `y`, is on the side
of `y'`.** -/
theorem mem_cutSide_of_mem_cutSide {f e : E} {y y' x z : V} (hj : Joins G f y y') (hef : e ≠ f)
    (hje : Joins G e x z) (hx : x ∈ cutSide G f y') (hy : y ∉ cutSide G e z) {w : V}
    (hw : w ∈ cutSide G e z) : w ∈ cutSide G f y' := by
  have hz : z ∈ cutSide G f y' := Relation.ReflTransGen.tail hx ⟨e, hef, hje⟩
  change G.Walks {e}ᶜ z w at hw
  induction hw with
  | refl => exact hz
  | @tail a b hza hab ih =>
    obtain ⟨g, hg, hgj⟩ := hab
    by_cases hgf : g = f
    · subst hgf
      rcases hj.eq_or_eq (Joins.incident_right hgj) with rfl | rfl
      · exact absurd (hza.tail ⟨_, hg, hgj⟩) hy
      · exact .refl
    · exact Relation.ReflTransGen.tail ih ⟨g, hgf, hgj⟩

end Bridges

/-- **On a side with one taxon, every other node lies on a 2-cycle**: a node of degree three
there, on no cycle or on a cycle of size at least three, has three bridges, at it or at three
nodes of its cycle, whose far sides are disjoint; two of them are away from the other side, and
each holds a taxon, so two distinct taxa would be on that side. -/
theorem IsUnrootedLevelOne.exists_two_cycle_of_side [Finite E] {G : SemidirectedNetwork V E X}
    (hG : IsUnrootedLevelOne G) {f : E} (hf : ∀ C, IsCycle G.graph C → f ∉ C) {y y' : V}
    (hj : Joins G.graph f y y') {z₀ : X} (hz₀ : ∀ x, G.leaf x ∈ cutSide G.graph f y' ↔ x = z₀)
    {x : V} (hx : x ∈ cutSide G.graph f y') (hnl : ¬ ∃ t, G.leaf t = x) :
    ∃ D, IsCycle G.graph D ∧ D.ncard = 2 ∧ x ∈ cycleNodes G.graph D := by
  set B := cutSide G.graph f y'
  have hyB : y ∉ B := (mem_cutSide_iff_notMem hG.connected hf hj y).mp.mt
    (not_not.mpr Relation.ReflTransGen.refl)
  -- the far side of a bridge at a node of `B`, away from `y`, holds the leaf of `z₀`
  have hfar : ∀ (e : E) (a z : V), (∀ C, IsCycle G.graph C → e ∉ C) → Joins G.graph e a z →
      a ∈ B → y ∉ cutSide G.graph e z → G.leaf z₀ ∈ cutSide G.graph e z := by
    intro e a z he hje haB hy
    have hef : e ≠ f := by
      rintro rfl
      have ha : a = y' := (hj.eq_or_eq hje.incident_left).resolve_left fun h => hyB (h ▸ haB)
      subst ha
      exact hy (Joins.eq_right (Or.symm hj) hje ▸ .refl)
    obtain ⟨t, ht⟩ := hG.exists_leaf_side e he z hje.incident_right
    have htB := mem_cutSide_of_mem_cutSide hj hef hje haB hy ht
    rwa [(hz₀ t).mp htB] at ht
  -- two bridges at nodes of `B` joined avoiding both, both far sides away from `y`: impossible
  have two : ∀ (e₁ e₂ : E) (x₁ x₂ z₁ z₂ : V), (∀ C, IsCycle G.graph C → e₁ ∉ C) →
      (∀ C, IsCycle G.graph C → e₂ ∉ C) → e₁ ≠ e₂ → Joins G.graph e₁ x₁ z₁ →
      Joins G.graph e₂ x₂ z₂ → x₁ ∈ B → x₂ ∈ B → G.graph.Walks ({e₁}ᶜ ∩ {e₂}ᶜ) x₁ x₂ →
      y ∉ cutSide G.graph e₁ z₁ → y ∉ cutSide G.graph e₂ z₂ → False :=
    fun e₁ e₂ x₁ x₂ z₁ z₂ he₁ he₂ hne hj₁ hj₂ hx₁ hx₂ hw hy₁ hy₂ =>
      notMem_cutSide_of_walks he₁ he₂ hne hj₁ hj₂ hw (hfar e₁ x₁ z₁ he₁ hj₁ hx₁ hy₁)
        (hfar e₂ x₂ z₂ he₂ hj₂ hx₂ hy₂)
  -- three such bridges: impossible, as at most one far side holds `y`
  have three : ∀ (e₁ e₂ e₃ : E) (x₁ x₂ x₃ z₁ z₂ z₃ : V), (∀ C, IsCycle G.graph C → e₁ ∉ C) →
      (∀ C, IsCycle G.graph C → e₂ ∉ C) → (∀ C, IsCycle G.graph C → e₃ ∉ C) → e₁ ≠ e₂ →
      e₁ ≠ e₃ → e₂ ≠ e₃ → Joins G.graph e₁ x₁ z₁ → Joins G.graph e₂ x₂ z₂ →
      Joins G.graph e₃ x₃ z₃ → x₁ ∈ B → x₂ ∈ B → x₃ ∈ B →
      G.graph.Walks ({e₁}ᶜ ∩ {e₂}ᶜ) x₁ x₂ → G.graph.Walks ({e₁}ᶜ ∩ {e₃}ᶜ) x₁ x₃ →
      G.graph.Walks ({e₂}ᶜ ∩ {e₃}ᶜ) x₂ x₃ → False := by
    intro e₁ e₂ e₃ x₁ x₂ x₃ z₁ z₂ z₃ he₁ he₂ he₃ h12 h13 h23 hj₁ hj₂ hj₃ hx₁ hx₂ hx₃ hw12 hw13 hw23
    by_cases hy₁ : y ∈ cutSide G.graph e₁ z₁
    · exact two e₂ e₃ x₂ x₃ z₂ z₃ he₂ he₃ h23 hj₂ hj₃ hx₂ hx₃ hw23
        (fun h => notMem_cutSide_of_walks he₁ he₂ h12 hj₁ hj₂ hw12 hy₁ h)
        (fun h => notMem_cutSide_of_walks he₁ he₃ h13 hj₁ hj₃ hw13 hy₁ h)
    · by_cases hy₂ : y ∈ cutSide G.graph e₂ z₂
      · exact two e₁ e₃ x₁ x₃ z₁ z₃ he₁ he₃ h13 hj₁ hj₃ hx₁ hx₃ hw13 hy₁
          (fun h => notMem_cutSide_of_walks he₂ he₃ h23 hj₂ hj₃ hw23 hy₂ h)
      · exact two e₁ e₂ x₁ x₂ z₁ z₂ he₁ he₂ h12 hj₁ hj₂ hx₁ hx₂ hw12 hy₁ hy₂
  have hdeg := hG.degree_of_not_leaf x hnl
  by_cases hcyc : ∃ D, IsCycle G.graph D ∧ x ∈ cycleNodes G.graph D
  · obtain ⟨D, hD, hxD⟩ := hcyc
    have h2 : 2 ≤ D.ncard := by
      have := hD.ncard_incident hG.loopless hxD
      rw [← this]
      exact Set.ncard_le_ncard (fun e he => he.1) (Set.toFinite _)
    by_cases hD2 : D.ncard = 2
    · exact ⟨D, hD, hD2, hxD⟩
    exfalso
    have h3 : 2 < (cycleNodes G.graph D).ncard := by
      rw [ncard_cycleNodes hD]
      omega
    obtain ⟨d₁, hd₁, d₂, hd₂, d₃, hd₃, h12, h13, h23⟩ :=
      (Set.two_lt_ncard (Set.finite_of_ncard_ne_zero (by omega))).mp h3
    obtain ⟨g, hg, -⟩ := id hxD
    -- the nodes of `D` are joined along `D`, which avoids every bridge
    have hDw : ∀ d ∈ cycleNodes G.graph D, ∀ d' ∈ cycleNodes G.graph D, ∀ F : Set E,
        (∀ e ∈ D, e ∈ F) → G.graph.Walks F d d' := fun d hd d' hd' F hF =>
      walks_mono (F := D \ {g}) (fun e he => hF e he.1) (hD.walks_sdiff_singleton hg hd hd')
    have hDB : ∀ d ∈ cycleNodes G.graph D, d ∈ B := fun d hd =>
      Relation.ReflTransGen.trans hx (hDw x hxD d hd {f}ᶜ fun e he h => hf D hD
        (Set.mem_singleton_iff.mp h ▸ he))
    -- the edges off `D`
    obtain ⟨e₁, hi₁, he₁D, he₁⟩ := hG.exists_offCycle hD hd₁
    obtain ⟨e₂, hi₂, he₂D, he₂⟩ := hG.exists_offCycle hD hd₂
    obtain ⟨e₃, hi₃, he₃D, he₃⟩ := hG.exists_offCycle hD hd₃
    obtain ⟨z₁, hj₁⟩ := exists_joins_of_incident hi₁
    obtain ⟨z₂, hj₂⟩ := exists_joins_of_incident hi₂
    obtain ⟨z₃, hj₃⟩ := exists_joins_of_incident hi₃
    have hoff : ∀ e e' : E, e ∉ D → e' ∉ D → ∀ d ∈ cycleNodes G.graph D,
        ∀ d' ∈ cycleNodes G.graph D, G.graph.Walks ({e}ᶜ ∩ {e'}ᶜ) d d' :=
      fun e e' he he' d hd d' hd' => hDw d hd d' hd' _ fun e'' he'' =>
        ⟨fun h => he (Set.mem_singleton_iff.mp h ▸ he''),
          fun h => he' (Set.mem_singleton_iff.mp h ▸ he'')⟩
    -- the edges off `D` at distinct nodes are distinct: else a chord of `D`
    have hdist : ∀ e d d', (∀ C, IsCycle G.graph C → e ∉ C) → e ∉ D →
        d ∈ cycleNodes G.graph D → d' ∈ cycleNodes G.graph D → d ≠ d' →
        (G.graph.source e = d ∨ G.graph.target e = d) →
        ¬ (G.graph.source e = d' ∨ G.graph.target e = d') := by
      intro e d d' he heD hd hd' hdd' hid hid'
      obtain ⟨z, hjz⟩ := exists_joins_of_incident hid
      have hz : z = d' := ((hjz.eq_or_eq hid').resolve_left fun h => hdd' h.symm).symm
      subst hz
      exact not_walks_of_joins he hjz (hDw d hd z hd' {e}ᶜ fun e' he' h =>
        heD (Set.mem_singleton_iff.mp h ▸ he'))
    have hne : ∀ {e e' d d'}, (∀ C, IsCycle G.graph C → e ∉ C) → e ∉ D →
        d ∈ cycleNodes G.graph D → d' ∈ cycleNodes G.graph D → d ≠ d' →
        (G.graph.source e = d ∨ G.graph.target e = d) →
        (G.graph.source e' = d' ∨ G.graph.target e' = d') → e ≠ e' := by
      rintro e e' d d' he heD hd hd' hdd' hid hid' rfl
      exact hdist e d d' he heD hd hd' hdd' hid hid'
    exact three e₁ e₂ e₃ d₁ d₂ d₃ z₁ z₂ z₃ he₁ he₂ he₃ (hne he₁ he₁D hd₁ hd₂ h12 hi₁ hi₂)
      (hne he₁ he₁D hd₁ hd₃ h13 hi₁ hi₃) (hne he₂ he₂D hd₂ hd₃ h23 hi₂ hi₃) hj₁ hj₂ hj₃
      (hDB d₁ hd₁) (hDB d₂ hd₂) (hDB d₃ hd₃) (hoff e₁ e₂ he₁D he₂D d₁ hd₁ d₂ hd₂)
      (hoff e₁ e₃ he₁D he₃D d₁ hd₁ d₃ hd₃) (hoff e₂ e₃ he₂D he₃D d₂ hd₂ d₃ hd₃)
  · -- on no cycle: three bridges at `x`
    exfalso
    push Not at hcyc
    have hinc := degree_eq_ncard_incident hG.loopless x
    rw [hdeg] at hinc
    obtain ⟨e₁, hi₁, e₂, hi₂, e₃, hi₃, h12, h13, h23⟩ :=
      (Set.two_lt_ncard (Set.toFinite _)).mp (show 2 < {e | G.graph.source e = x ∨
        G.graph.target e = x}.ncard by omega)
    have hbr : ∀ e, (G.graph.source e = x ∨ G.graph.target e = x) →
        ∀ C, IsCycle G.graph C → e ∉ C := fun e hi C hC heC =>
      hcyc C hC (hi.elim (fun h => ⟨e, heC, Or.inl h⟩) fun h => ⟨e, heC, Or.inr h⟩)
    obtain ⟨z₁, hj₁⟩ := exists_joins_of_incident hi₁
    obtain ⟨z₂, hj₂⟩ := exists_joins_of_incident hi₂
    obtain ⟨z₃, hj₃⟩ := exists_joins_of_incident hi₃
    exact three e₁ e₂ e₃ x x x z₁ z₂ z₃ (hbr e₁ hi₁) (hbr e₂ hi₂) (hbr e₃ hi₃) h12 h13 h23 hj₁
      hj₂ hj₃ hx hx hx .refl .refl .refl

/-- The ends of an edge of `Ñ` are the first and last nodes of its chain. -/
theorem tildeNetwork_ends {G : SemidirectedNetwork V E X}
    (c' : {c // IsChain (tildeContracted G) ∅ c}) :
    (((tildeNetwork G).graph.source c').1 = (chainRep _ ∅ c'.2).p 0 ∧
        ((tildeNetwork G).graph.target c').1 = (chainRep _ ∅ c'.2).p (Fin.last _)) ∨
      (((tildeNetwork G).graph.source c').1 = (chainRep _ ∅ c'.2).p (Fin.last _) ∧
        ((tildeNetwork G).graph.target c').1 = (chainRep _ ∅ c'.2).p 0) := by
  obtain ⟨c', hc'⟩ := c'
  erw [suppressExcept_source_val hc', suppressExcept_target_val hc']
  unfold ChainRep.src ChainRep.tgt
  split_ifs
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- An edge of `Ñ` at a node has an edge of its chain at that node. -/
theorem exists_mem_incident_of_tildeNetwork {G : SemidirectedNetwork V E X}
    {c' : {c // IsChain (tildeContracted G) ∅ c}} {w : {u // IsBranch (tildeContracted G) ∅ u}}
    (h : (tildeNetwork G).graph.source c' = w ∨ (tildeNetwork G).graph.target c' = w) :
    ∃ g ∈ c'.1, (tildeContracted G).graph.source g = w.1 ∨
      (tildeContracted G).graph.target g = w.1 := by
  set r := chainRep (tildeContracted G) ∅ c'.2
  have hk := r.isChainOf.pos
  have hmem : ∀ i, r.e i ∈ c'.1 := fun i => (Set.ext_iff.1 r.range_eq _).1 ⟨i, rfl⟩
  have h0 : ∃ g ∈ c'.1, (tildeContracted G).graph.source g = r.p 0 ∨
      (tildeContracted G).graph.target g = r.p 0 :=
    ⟨r.e ⟨0, hk⟩, hmem _, (r.isChainOf.joins ⟨0, hk⟩).incident_left⟩
  have hl : ∃ g ∈ c'.1, (tildeContracted G).graph.source g = r.p (Fin.last r.k) ∨
      (tildeContracted G).graph.target g = r.p (Fin.last r.k) := by
    have hlast : (⟨r.k - 1, by omega⟩ : Fin r.k).succ = Fin.last r.k := Fin.ext (by simp; omega)
    have := (r.isChainOf.joins ⟨r.k - 1, by omega⟩).incident_right
    rw [hlast] at this
    exact ⟨_, hmem _, this⟩
  have hw : w.1 = r.p 0 ∨ w.1 = r.p (Fin.last r.k) := by
    rcases tildeNetwork_ends c' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases h with rfl | rfl
    · exact Or.inl h₁
    · exact Or.inr h₂
    · exact Or.inr h₁
    · exact Or.inl h₂
  rcases hw with hw | hw <;> rw [hw]
  exacts [h0, hl]

/-- **The cut of `Ñ` at an edge on no cycle** (proof of Theorem 4, "`Ñ ∖ {u}` has two components"):
an edge `f` of `N⁻` on no cycle, joining `y` and `y'`, lies on an undirected edge `ε` of `Ñ` joining
a node on the side of `y` to a node on the side of `y'`; every other edge of `Ñ` has its two ends on
the same side, and the nodes of `Ñ` on the side of `y'` are those not on the side of `y`. -/
theorem tilde_cut [Finite V] [Finite E] {G : SemidirectedNetwork V E X} (hG : IsUnrootedLevelOne G)
    {f : E} (hf : ∀ C, IsCycle G.graph C → f ∉ C) {y y' : V} (hj : Joins G.graph f y y') :
    ∃ (ε : {c // IsChain (tildeContracted G) ∅ c}) (a b : {u // IsBranch (tildeContracted G) ∅ u}),
      (∃ g ∈ ε.1, g.1 = f) ∧ a ∈ tildeCutSide G f y ∧ b ∈ tildeCutSide G f y' ∧
      Joins (tildeNetwork G).graph ε a b ∧ ¬ (tildeNetwork G).IsDirected ε ∧
      (∀ e, e ≠ ε → ((tildeNetwork G).graph.source e ∈ tildeCutSide G f y ↔
        (tildeNetwork G).graph.target e ∈ tildeCutSide G f y)) ∧
      (∀ w, w ∈ tildeCutSide G f y' ↔ w ∉ tildeCutSide G f y) ∧
      ∀ x, (tildeNetwork G).leaf x ∈ tildeCutSide G f y ↔ G.leaf x ∈ cutSide G.graph f y := by
  classical
  have hfK : ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → f ∉ C := fun C hC _ => hf C hC
  obtain ⟨c, hc, hfc⟩ := exists_isChain_tildeContracted hG ⟨f, hfK⟩
  have hends := @tildeNetwork_ends V E X G
  set ε : {c // IsChain (tildeContracted G) ∅ c} := ⟨c, hc⟩ with hε_def
  have hfr : ∃ i, ((chainRep _ ∅ hc).e i).1 = f := by
    rw [← (chainRep _ ∅ hc).range_eq] at hfc
    obtain ⟨i, hi⟩ := hfc
    exact ⟨i, congrArg Subtype.val hi⟩
  -- `ε` joins the two sides
  have hεside : (tildeNetwork G).graph.source ε ∈ tildeCutSide G f y ↔
      (tildeNetwork G).graph.target ε ∉ tildeCutSide G f y := by
    rw [mem_tildeCutSide_iff, mem_tildeCutSide_iff]
    have h := ((chainRep _ ∅ hc).isChainOf.mem_contractSide_iff hG.connected hf hj).2 hfr
    rcases hends ε with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> tauto
  -- every other edge has its ends on one side
  have hcross : ∀ e, e ≠ ε → ((tildeNetwork G).graph.source e ∈ tildeCutSide G f y ↔
      (tildeNetwork G).graph.target e ∈ tildeCutSide G f y) := by
    intro e he
    rw [mem_tildeCutSide_iff, mem_tildeCutSide_iff]
    have hne : ∀ i, ((chainRep _ ∅ e.2).e i).1 ≠ f := by
      intro i hi
      apply he
      have hmem : ((chainRep _ ∅ e.2).e i) ∈ e.1 :=
        (Set.ext_iff.1 (chainRep _ ∅ e.2).range_eq _).1 ⟨i, rfl⟩
      have heq : (chainRep _ ∅ e.2).e i = ⟨f, hfK⟩ := Subtype.ext hi
      rw [heq] at hmem
      exact Subtype.ext (e.2.eq_of_mem hc hmem hfc)
    have h := ((chainRep _ ∅ e.2).isChainOf.mem_contractSide_iff hG.connected hf hj).1 hne
    rcases hends e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> tauto
  -- `ε` is undirected: its edges lie on no cycle
  have hund : ¬ (tildeNetwork G).IsDirected ε := by
    set r := chainRep (tildeContracted G) ∅ hc
    have hnd : ∀ i, ¬ (tildeContracted G).IsDirected (r.e i) := by
      intro i hd
      obtain ⟨C, hC, hiC⟩ := hG.mem_cycle_of_isDirected _ hd.1
      by_cases hk : 2 ≤ r.k
      · exact r.isChainOf.notMem_cycle_tildeContracted hG hk i C hC hiC
      · obtain ⟨j, hj'⟩ := hfr
        have hij : i = j := Fin.ext (by have := r.isChainOf.pos; omega)
        rw [hij, hj'] at hiC
        exact hf C hC hiC
    rintro (⟨⟨i, hi⟩, -⟩ | ⟨⟨i, hi⟩, -⟩) <;> exact hnd i hi
  have hcompl : ∀ w, w ∈ tildeCutSide G f y' ↔ w ∉ tildeCutSide G f y := fun w => by
    rw [mem_tildeCutSide_iff, mem_tildeCutSide_iff]
    exact mem_contractSide_iff_notMem hG.connected hf hj w.1
  have hleaf : ∀ x, (tildeNetwork G).leaf x ∈ tildeCutSide G f y ↔
      G.leaf x ∈ cutSide G.graph f y := fun x => mk_mem_contractSide_iff hf (G.leaf x)
  by_cases hs : (tildeNetwork G).graph.source ε ∈ tildeCutSide G f y
  · exact ⟨ε, _, _, ⟨⟨f, hfK⟩, hfc, rfl⟩, hs, (hcompl _).mpr (hεside.mp hs),
      Or.inl ⟨rfl, rfl⟩, hund, hcross, hcompl, hleaf⟩
  · have ht : (tildeNetwork G).graph.target ε ∈ tildeCutSide G f y := by
      by_contra ht
      exact hs (hεside.mpr ht)
    exact ⟨ε, _, _, ⟨⟨f, hfK⟩, hfc, rfl⟩, ht, (hcompl _).mpr hs, Or.inr ⟨rfl, rfl⟩, hund,
      hcross, hcompl, hleaf⟩

/-! ### Edges of a suppressed network -/

section SuppressEnds

variable {W F : Type*} {K : SemidirectedNetwork W F X}

/-- The ends of an edge of the suppressed network are the first and last nodes of its chain. -/
theorem suppress_ends_val (c' : {c // IsChain K ∅ c}) :
    (((suppress K).graph.source c').1 = (chainRep K ∅ c'.2).p 0 ∧
        ((suppress K).graph.target c').1 = (chainRep K ∅ c'.2).p (Fin.last _)) ∨
      (((suppress K).graph.source c').1 = (chainRep K ∅ c'.2).p (Fin.last _) ∧
        ((suppress K).graph.target c').1 = (chainRep K ∅ c'.2).p 0) := by
  obtain ⟨c', hc'⟩ := c'
  rw [suppressExcept_source_val hc', suppressExcept_target_val hc']
  unfold ChainRep.src ChainRep.tgt
  split_ifs
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- **A chain with a hybrid edge is that edge**, when the ends of the hybrid edges are kept. -/
theorem IsChainOf.eq_one_of_isDirected
    (hdirb : ∀ e, K.IsDirected e → IsBranch K ∅ (K.graph.source e) ∧
      IsBranch K ∅ (K.graph.target e)) {k : ℕ} {p : Fin (k + 1) → W} {e : Fin k → F}
    (h : IsChainOf K ∅ k p e) {i : Fin k} (hi : K.IsDirected (e i)) : k = 1 := by
  have hb := hdirb _ hi
  have hb₁ : IsBranch K ∅ (p i.castSucc) := by
    rcases h.joins i with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact h₁ ▸ hb.1
    · exact h₂ ▸ hb.2
  have hb₂ : IsBranch K ∅ (p i.succ) := by
    rcases h.joins i with ⟨-, h₂⟩ | ⟨h₁, -⟩
    · exact h₂ ▸ hb.2
    · exact h₁ ▸ hb.1
  rw [h.isBranch_iff] at hb₁ hb₂
  rcases hb₁ with h₁ | h₁
  · rcases hb₂ with h₂ | h₂
    · exact absurd h₂ (Fin.succ_ne_zero i)
    · have := congrArg Fin.val h₁
      have := congrArg Fin.val h₂
      simp at *
      omega
  · exact absurd h₁ (Fin.castSucc_ne_last i)

/-- **A chain with a hybrid edge points toward an end**, when the ends of the hybrid edges are kept.
-/
theorem ChainRep.pointsTo_of_isDirected {c : Set F}
    (hloop : ∀ e, K.graph.source e ≠ K.graph.target e)
    (hdirb : ∀ e, K.IsDirected e → IsBranch K ∅ (K.graph.source e) ∧
      IsBranch K ∅ (K.graph.target e)) (r : ChainRep K ∅ c) {i : Fin r.k}
    (hi : K.IsDirected (r.e i)) :
    (r.PointsForward ∧ ¬ r.PointsBackward ∧ K.graph.target (r.e i) = r.p (Fin.last r.k)) ∨
      (r.PointsBackward ∧ ¬ r.PointsForward ∧ K.graph.target (r.e i) = r.p 0) := by
  have hk := r.isChainOf.eq_one_of_isDirected hdirb hi
  have hall : ∀ i' : Fin r.k, i' = i := fun i' => Fin.ext (by have := i'.2; have := i.2; omega)
  have hc : i.castSucc = 0 := Fin.ext (by have := i.2; simp; omega)
  have hs : i.succ = Fin.last r.k := Fin.ext (by have := i.2; simp; omega)
  have hne : r.p 0 ≠ r.p (Fin.last r.k) := by
    intro h'
    rcases r.isChainOf.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hloop _ (by rw [h₁, h₂, hc, hs, h'])
    · exact hloop _ (by rw [h₁, h₂, hc, hs, h'])
  rcases r.isChainOf.joins i with ⟨-, h₂⟩ | ⟨-, h₂⟩
  · rw [hs] at h₂
    refine Or.inl ⟨⟨⟨i, hi⟩, fun i' _ => by rw [hall i', hs]; exact h₂⟩, fun ⟨_, hb⟩ => ?_, h₂⟩
    have := hb i hi
    rw [hc, h₂] at this
    exact hne this.symm
  · rw [hc] at h₂
    refine Or.inr ⟨⟨⟨i, hi⟩, fun i' _ => by rw [hall i', hc]; exact h₂⟩, fun ⟨_, hf⟩ => ?_, h₂⟩
    have := hf i hi
    rw [hs, h₂] at this
    exact hne this

/-- **The suppressed network has no loops** when the edges at the removed nodes are bridges: a chain
from a node back to itself would be a cycle through such an edge. -/
theorem suppress_source_ne_target (hloop : ∀ e, K.graph.source e ≠ K.graph.target e)
    (hbr : ∀ e u, ¬ IsBranch K ∅ u → (K.graph.source e = u ∨ K.graph.target e = u) →
      ¬ K.graph.Walks {e}ᶜ (K.graph.source e) (K.graph.target e))
    (c' : {c // IsChain K ∅ c}) : (suppress K).graph.source c' ≠ (suppress K).graph.target c' := by
  intro h
  set r := chainRep K ∅ c'.2
  have heq : r.p 0 = r.p (Fin.last r.k) := by
    rcases suppress_ends_val c' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [← h₁, ← h₂, h]
    · rw [← h₁, ← h₂, h]
  have hk := r.isChainOf.pos
  set i₀ : Fin r.k := ⟨0, hk⟩
  have h0 : i₀.castSucc = 0 := rfl
  by_cases hk1 : r.k = 1
  · have hs : i₀.succ = Fin.last r.k := Fin.ext (by simp [i₀]; omega)
    rcases r.isChainOf.joins i₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hloop _ (by rw [h₁, h₂, h0, hs, heq])
    · exact hloop _ (by rw [h₁, h₂, h0, hs, heq])
  · -- the first edge, at an inner node, is joined around by the rest of the chain
    have hin : ¬ IsBranch K ∅ (r.p i₀.succ) := r.isChainOf.inner _ (Fin.succ_ne_zero _)
      (fun h' => by have := congrArg Fin.val h'; simp [i₀] at this; omega)
    have hw : K.graph.Walks {r.e i₀}ᶜ (r.p i₀.succ) (r.p 0) := by
      rw [heq]
      refine walks_mono (fun f hf => ?_) (walks_of_joins_le r.isChainOf.joins (Fin.le_last _))
      obtain ⟨l, hl, -, rfl⟩ := hf
      intro h'
      have := r.isChainOf.injective_edge (Set.mem_singleton_iff.mp h')
      rw [this] at hl
      simp [i₀] at hl
    have hbr' := hbr (r.e i₀) _ hin (r.isChainOf.joins i₀).incident_right
    rcases r.isChainOf.joins i₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂, h0] at hbr'
      exact hbr' (K.graph.walks_symm hw)
    · rw [h₁, h₂, h0] at hbr'
      exact hbr' hw

end SuppressEnds

/-! ### Suppression and one side of a cut -/

section SuppressSide

variable {W F Z : Type*} {K : SemidirectedNetwork W F X} {S : Set W} {a : S} {ι : Z → X}
  {fK : F} {s' : W}

/-- In a network whose taxa do not have degree two, the nodes kept by suppression are those of
degree other than two. -/
theorem isBranch_iff_degree_ne (hleaf : ∀ x, degree K.graph (K.leaf x) ≠ 2) (u : W) :
    IsBranch K ∅ u ↔ degree K.graph u ≠ 2 := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | ⟨x, rfl⟩ | h
  · exact h
  · exact hleaf x
  · exact absurd h (Set.notMem_empty _)

theorem pendantSide_loopless (hloop : ∀ e, K.graph.source e ≠ K.graph.target e)
    (e : {e // K.graph.source e ∈ S ∧ K.graph.target e ∈ S} ⊕ Unit) :
    (pendantSide K S a ι).graph.source e ≠ (pendantSide K S a ι).graph.target e := by
  rcases e with e | u
  · intro h
    exact hloop e.1 (congrArg Subtype.val (Sum.inl_injective h))
  · exact Sum.inl_ne_inr

variable (hj : Joins K.graph fK a.1 s') (hs' : s' ∉ S)
include hj hs'

/-- `fK` is not an edge of the side `S`. -/
theorem ne_of_mem_side (e : {e // K.graph.source e ∈ S ∧ K.graph.target e ∈ S}) : e.1 ≠ fK := by
  rintro h
  rcases hj with ⟨-, h₂⟩ | ⟨h₁, -⟩
  · exact hs' (h₂ ▸ h ▸ e.2.2)
  · exact hs' (h₁ ▸ h ▸ e.2.1)

variable (hcross : ∀ e, e ≠ fK → (K.graph.source e ∈ S ↔ K.graph.target e ∈ S))
include hcross

/-- **A node of the side keeps its degree**, the pendant edge replacing `fK`. -/
theorem degree_pendantSide_inl [Finite F] (hloop : ∀ e, K.graph.source e ≠ K.graph.target e)
    (x : S) : degree (pendantSide K S a ι).graph (.inl x) = degree K.graph x.1 := by
  rw [degree_eq_ncard_incident (pendantSide_loopless hloop), degree_eq_ncard_incident hloop]
  refine Set.ncard_congr (fun e _ => Sum.elim (fun e' => e'.1) (fun _ => fK) e) ?_ ?_ ?_
  · rintro (e | u) he
    · simpa [pendantSide, Subtype.ext_iff] using he
    · have hax : a = x := by simpa [pendantSide] using he
      subst hax
      exact hj.incident_left
  · rintro (e₁ | u₁) (e₂ | u₂) - - h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact absurd h (ne_of_mem_side hj hs' e₁)
    · exact absurd h.symm (ne_of_mem_side hj hs' e₂)
    · rfl
  · intro g hg
    by_cases hgf : g = fK
    · subst hgf
      have hxa : x.1 = a.1 := ((hj.eq_or_eq hg).resolve_right fun h => hs' (h ▸ x.2))
      refine ⟨.inr (), Or.inl ?_, rfl⟩
      exact congrArg Sum.inl (Subtype.ext hxa.symm)
    · have hS : K.graph.source g ∈ S ∧ K.graph.target g ∈ S := by
        rcases hg with h | h
        · exact ⟨h ▸ x.2, (hcross g hgf).mp (h ▸ x.2)⟩
        · exact ⟨(hcross g hgf).mpr (h ▸ x.2), h ▸ x.2⟩
      refine ⟨.inl ⟨g, hS⟩, ?_, rfl⟩
      simpa [pendantSide, Subtype.ext_iff] using hg

omit hj hs' hcross in
/-- The new leaf has degree one. -/
theorem degree_pendantSide_inr [Finite F] (hloop : ∀ e, K.graph.source e ≠ K.graph.target e) :
    degree (pendantSide K S a ι).graph (.inr ()) = 1 := by
  rw [degree_eq_ncard_incident (pendantSide_loopless hloop), Set.ncard_eq_one]
  refine ⟨.inr (), Set.ext fun e => ?_⟩
  rcases e with e | u
  · simp [pendantSide]
  · simp [pendantSide]

/-- **A node of the side is kept by suppression exactly when it is kept in the network.** -/
theorem isBranch_pendantSide_inl_iff [Finite F] (hloop : ∀ e, K.graph.source e ≠ K.graph.target e)
    (hleaf : ∀ x, degree K.graph (K.leaf x) ≠ 2) (x : S) :
    IsBranch (pendantSide K S a ι) ∅ (.inl x) ↔ IsBranch K ∅ x.1 := by
  rw [isBranch_iff_degree_ne hleaf, ← degree_pendantSide_inl hj hs' hcross hloop x]
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | ⟨z, hz⟩ | h
  · exact h
  · have hz' : K.leaf (ι z) = x.1 := by
      by_cases h' : K.leaf (ι z) ∈ S
      · rw [pendantSide_leaf_of_mem h'] at hz
        exact congrArg Subtype.val (Sum.inl_injective hz)
      · rw [pendantSide_leaf_of_notMem h'] at hz
        exact absurd hz Sum.inr_ne_inl
    rw [degree_pendantSide_inl hj hs' hcross hloop x, ← hz']
    exact hleaf _
  · exact absurd h (Set.notMem_empty _)

omit hj hs' hcross in
theorem isBranch_pendantSide_inr [Finite F] (hloop : ∀ e, K.graph.source e ≠ K.graph.target e) :
    IsBranch (pendantSide K S a ι) ∅ (.inr ()) :=
  Or.inl (by rw [degree_pendantSide_inr hloop]; omega)

omit hj hs' in
/-- **The nodes of a chain of `K` up to an edge `fK` are on one side.** -/
theorem IsChainOf.mem_side_iff {P : Set W} {k : ℕ} {p : Fin (k + 1) → W} {e : Fin k → F}
    (h : IsChainOf K P k p e) {i j : ℕ} (hij : i ≤ j) (hj' : j ≤ k)
    (hne : ∀ l (hl : l < k), i ≤ l → l < j → e ⟨l, hl⟩ ≠ fK) :
    p ⟨i, by omega⟩ ∈ S ↔ p ⟨j, by omega⟩ ∈ S := by
  refine iff_of_forall_link p (· ∈ S) hij hj' fun l hl h₁ h₂ => ?_
  have := hcross _ (hne l hl h₁ h₂)
  rcases h.joins ⟨l, hl⟩ with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · rw [e₁, e₂] at this
    exact this
  · rw [e₁, e₂] at this
    exact this.symm

/-- **A chain of `K` on the side `S` is a chain of the side with its pendant edge.** -/
theorem IsChainOf.pendantSide_inl [Finite F] (hloop : ∀ e, K.graph.source e ≠ K.graph.target e)
    (hleaf : ∀ x, degree K.graph (K.leaf x) ≠ 2) {k : ℕ} {p : Fin (k + 1) → W} {e : Fin k → F}
    (h : IsChainOf K ∅ k p e) (hp : ∀ j, p j ∈ S) :
    IsChainOf (pendantSide K S a ι) ∅ k (fun j => .inl ⟨p j, hp j⟩)
      (fun i => .inl ⟨e i, by
        rcases h.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact ⟨h₁ ▸ hp _, h₂ ▸ hp _⟩
        · exact ⟨h₁ ▸ hp _, h₂ ▸ hp _⟩⟩) where
  pos := h.pos
  joins i := by
    rcases h.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨congrArg Sum.inl (Subtype.ext h₁), congrArg Sum.inl (Subtype.ext h₂)⟩
    · exact Or.inr ⟨congrArg Sum.inl (Subtype.ext h₁), congrArg Sum.inl (Subtype.ext h₂)⟩
  inner j h0 hl hb := h.inner j h0 hl
    ((isBranch_pendantSide_inl_iff hj hs' hcross hloop hleaf ⟨p j, hp j⟩).mp hb)
  ends := ⟨(isBranch_pendantSide_inl_iff hj hs' hcross hloop hleaf _).mpr h.ends.1,
    (isBranch_pendantSide_inl_iff hj hs' hcross hloop hleaf _).mpr h.ends.2⟩
  injective_edge i i' he := h.injective_edge (congrArg Subtype.val (Sum.inl_injective he))

/-- **The chain of `K` through `fK`, cut at `fK`, is the chain of the pendant edge**: its part on
the side `S`, followed by the pendant edge. -/
theorem IsChainOf.exists_pendantSide_inr [Finite F]
    (hloop : ∀ e, K.graph.source e ≠ K.graph.target e)
    (hleaf : ∀ x, degree K.graph (K.leaf x) ≠ 2) {k : ℕ} {p : Fin (k + 1) → W} {e : Fin k → F}
    (h : IsChainOf K ∅ k p e) {i₀ : Fin k} (hi₀ : e i₀ = fK) (hp0 : p 0 ∈ S) :
    ∃ (k' : ℕ) (p' : Fin (k' + 1) → S ⊕ Unit) (e' : Fin k' → _),
      IsChainOf (pendantSide K S a ι) ∅ k' p' e' ∧
      Set.range e' = insert (.inr ()) {g | ∃ e'' : {e // K.graph.source e ∈ S ∧
        K.graph.target e ∈ S}, g = .inl e'' ∧ e''.1 ∈ Set.range e} ∧
      p' 0 = .inl ⟨p 0, hp0⟩ ∧ p' (Fin.last k') = .inr () := by
  set n := i₀.val with hn
  have hnk : n < k := i₀.2
  have hne : ∀ l (hl : l < k), l ≠ n → e ⟨l, hl⟩ ≠ fK := fun l hl hln h' => hln <| by
    have := h.injective_edge (h'.trans hi₀.symm)
    exact congrArg Fin.val this
  -- the nodes up to `fK` are on the side `S`
  have hS : ∀ j (hjn : j ≤ n), p ⟨j, by omega⟩ ∈ S := fun j hjn =>
    (h.mem_side_iff hcross (Nat.zero_le j) (by omega) fun l hl _ h' =>
      hne l hl (by omega)).mp hp0
  -- `fK` joins `p n`, on the side, to `p (n + 1) = s'`
  have hpn : p ⟨n, by omega⟩ = a.1 := by
    have hjn := h.joins i₀
    rw [hi₀] at hjn
    have hinc : K.graph.source fK = p ⟨n, by omega⟩ ∨ K.graph.target fK = p ⟨n, by omega⟩ :=
      hjn.incident_left
    exact (hj.eq_or_eq hinc).resolve_right fun h' => hs' (h' ▸ hS n le_rfl)
  have hFS : ∀ l (hl : l < n), K.graph.source (e ⟨l, by omega⟩) ∈ S ∧
      K.graph.target (e ⟨l, by omega⟩) ∈ S := fun l hl => by
    rcases h.joins ⟨l, by omega⟩ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨h₁ ▸ hS l (by omega), h₂ ▸ hS (l + 1) (by omega)⟩
    · exact ⟨h₁ ▸ hS (l + 1) (by omega), h₂ ▸ hS l (by omega)⟩
  set p' : Fin (n + 2) → S ⊕ Unit := fun j =>
    if hj' : j.val ≤ n then .inl ⟨p ⟨j.val, by omega⟩, hS j.val hj'⟩ else .inr () with hp'_def
  set e' : Fin (n + 1) → {e // K.graph.source e ∈ S ∧ K.graph.target e ∈ S} ⊕ Unit := fun l =>
    if hl : l.val < n then .inl ⟨e ⟨l.val, by omega⟩, hFS l.val hl⟩ else .inr () with he'_def
  refine ⟨n + 1, p', e', ⟨Nat.succ_pos n, fun l => ?_, fun j h0 hl hb => ?_, ⟨?_, ?_⟩,
    fun l₁ l₂ h' => ?_⟩, ?_, ?_, ?_⟩
  · -- the edges join consecutive nodes
    by_cases hl : l.val < n
    · have h₁ : p' l.castSucc = .inl ⟨p ⟨l.val, by omega⟩, hS l.val (by omega)⟩ := by
        simp only [p', Fin.val_castSucc, show l.val ≤ n by omega, ↓reduceDIte]
      have h₂ : p' l.succ = .inl ⟨p ⟨l.val + 1, by omega⟩, hS (l.val + 1) (by omega)⟩ := by
        simp only [p', Fin.val_succ, show l.val + 1 ≤ n by omega, ↓reduceDIte]
      have h₃ : e' l = .inl ⟨e ⟨l.val, by omega⟩, hFS l.val hl⟩ := by
        simp only [e', hl, ↓reduceDIte]
      rw [h₁, h₂, h₃]
      rcases h.joins ⟨l.val, by omega⟩ with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
      · exact Or.inl ⟨congrArg Sum.inl (Subtype.ext k₁), congrArg Sum.inl (Subtype.ext k₂)⟩
      · exact Or.inr ⟨congrArg Sum.inl (Subtype.ext k₁), congrArg Sum.inl (Subtype.ext k₂)⟩
    · have hln : l.val = n := by omega
      have h₁ : p' l.castSucc = .inl a := by
        simp only [p', Fin.val_castSucc, show l.val ≤ n by omega, ↓reduceDIte]
        congr 1
        exact Subtype.ext (by simp only [hln]; exact hpn)
      have h₂ : p' l.succ = .inr () := by
        simp only [p', Fin.val_succ, show ¬ (l.val + 1 ≤ n) by omega, ↓reduceDIte]
      have h₃ : e' l = .inr () := by
        simp only [e', hl, ↓reduceDIte]
      rw [h₁, h₂, h₃]
      exact Or.inl ⟨rfl, rfl⟩
  · -- the inner nodes are inner nodes of the chain of `K`
    have hjn : j.val ≤ n := by
      have : j.val ≠ n + 1 := fun h' => hl (Fin.ext h')
      omega
    have hpj : p' j = .inl ⟨p ⟨j.val, by omega⟩, hS j.val hjn⟩ := by
      simp only [p', hjn, ↓reduceDIte]
    rw [hpj] at hb
    refine h.inner ⟨j.val, by omega⟩ (fun h' => h0 (Fin.ext (by simpa using congrArg Fin.val h')))
      (fun h' => by have := congrArg Fin.val h'; simp at this; omega)
      ((isBranch_pendantSide_inl_iff hj hs' hcross hloop hleaf _).mp hb)
  · have hp0' : p' 0 = .inl ⟨p 0, hp0⟩ := by
      simp only [p', Fin.val_zero, Nat.zero_le, ↓reduceDIte]
      rfl
    rw [hp0']
    exact (isBranch_pendantSide_inl_iff hj hs' hcross hloop hleaf _).mpr h.ends.1
  · have hlast : p' (Fin.last (n + 1)) = .inr () := by
      simp only [p', Fin.val_last, show ¬ (n + 1 ≤ n) by omega, ↓reduceDIte]
    rw [hlast]
    exact isBranch_pendantSide_inr hloop
  · -- the edges are distinct
    by_cases hl₁ : l₁.val < n <;> by_cases hl₂ : l₂.val < n <;>
      simp only [e', hl₁, hl₂, ↓reduceDIte, reduceCtorEq, Sum.inl.injEq, Subtype.mk.injEq] at h'
    · exact Fin.ext (by simpa using congrArg Fin.val (h.injective_edge h'))
    · exact Fin.ext (by omega)
  · -- the edges are the pendant edge and those of the chain on the side `S`
    ext g
    constructor
    · rintro ⟨l, rfl⟩
      by_cases hl : l.val < n
      · simp only [e', hl, ↓reduceDIte]
        exact Or.inr ⟨_, rfl, ⟨_, rfl⟩⟩
      · simp only [e', hl, ↓reduceDIte]
        exact Or.inl rfl
    · rintro (rfl | ⟨e'', rfl, ⟨m, hm⟩⟩)
      · exact ⟨⟨n, by omega⟩, by simp [e']⟩
      · have hmn : m.val ≠ n := fun h' => ne_of_mem_side hj hs' e'' <| by
          rw [← hm, ← hi₀]
          exact congrArg e (Fin.ext h')
        by_cases hm' : m.val < n
        · refine ⟨⟨m.val, by omega⟩, ?_⟩
          simp only [e', hm', ↓reduceDIte, Sum.inl.injEq]
          exact Subtype.ext hm
        · -- past `fK`, the nodes are off the side
          exfalso
          have hoff : p ⟨m.val, by omega⟩ ∉ S := by
            have hs1 : p ⟨n + 1, by omega⟩ ∉ S := by
              have hjn := h.joins i₀
              rw [hi₀] at hjn
              have hinc : K.graph.source fK = p ⟨n + 1, by omega⟩ ∨
                  K.graph.target fK = p ⟨n + 1, by omega⟩ := hjn.incident_right
              rcases hj.eq_or_eq hinc with h' | h'
              · -- `p n = p (n + 1)` would make `fK` a loop
                intro _
                have := hpn.trans h'.symm
                rcases hjn with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
                · exact hloop fK (k₁.trans (this.trans k₂.symm))
                · exact hloop fK (k₁.trans (this.symm.trans k₂.symm))
              · rw [h']
                exact hs'
            exact (h.mem_side_iff hcross (by omega : n + 1 ≤ m.val) (by omega)
              fun l hl h₁ _ => hne l hl (by omega)).not.mp hs1 |> fun h' => by
                simpa using h'
          have := e''.2
          rw [← hm] at this
          rcases h.joins m with ⟨k₁, -⟩ | ⟨-, k₂⟩
          · exact hoff (k₁ ▸ this.1)
          · exact hoff (k₂ ▸ this.2)
  · simp only [p', Fin.val_zero, Nat.zero_le, ↓reduceDIte]
    rfl
  · simp only [p', Fin.val_last, show ¬ (n + 1 ≤ n) by omega, ↓reduceDIte]

/-- **Suppressing the side of a cut is the side of the suppressed network**: for an edge `fK`
joining `a ∈ S` to `s' ∉ S`, the only edge across `S`, suppressing `S` with `fK` as a pendant edge
gives the nodes of the suppressed network in `S`, with the chain `ε` of `fK` as a pendant edge at
its end `b ∈ S`. The edges at the removed nodes are bridges, the taxa do not have degree two, and
the ends of the hybrid edges are kept. -/
theorem nonempty_sdIso_suppress_pendantSide [Finite W] [Finite F]
    (hloop : ∀ e, K.graph.source e ≠ K.graph.target e)
    (hbr : ∀ e u, ¬ IsBranch K ∅ u → (K.graph.source e = u ∨ K.graph.target e = u) →
      ¬ K.graph.Walks {e}ᶜ (K.graph.source e) (K.graph.target e))
    (hleaf : ∀ x, degree K.graph (K.leaf x) ≠ 2)
    (hdirb : ∀ e, K.IsDirected e → IsBranch K ∅ (K.graph.source e) ∧
      IsBranch K ∅ (K.graph.target e)) (hfd : ¬ K.IsDirected fK)
    {ε : {c // IsChain K ∅ c}} (hεf : fK ∈ ε.1) {b : {u // IsBranch K ∅ u}} (hb : b.1 ∈ S)
    (hbε : (suppress K).graph.source ε = b ∨ (suppress K).graph.target ε = b) :
    Nonempty (SDIso (suppress (pendantSide K S a ι))
      (pendantSide (suppress K) {w | w.1 ∈ S} ⟨b, hb⟩ ι)) := by
  classical
  set P := pendantSide K S a ι with hP_def
  have hbrP := isBranch_pendantSide_inl_iff (ι := ι) hj hs' hcross hloop hleaf
  -- the nodes
  let φ : {u // IsBranch P ∅ u} ≃ ↥{w : {u // IsBranch K ∅ u} | w.1 ∈ S} ⊕ Unit :=
    { toFun := fun u => match u with
        | ⟨.inl x, hx⟩ => .inl ⟨⟨x.1, (hbrP x).mp hx⟩, x.2⟩
        | ⟨.inr _, _⟩ => .inr ()
      invFun := fun w => match w with
        | .inl w => ⟨.inl ⟨w.1.1, w.2⟩, (hbrP ⟨w.1.1, w.2⟩).mpr w.1.2⟩
        | .inr _ => ⟨.inr (), isBranch_pendantSide_inr hloop⟩
      left_inv := by rintro ⟨(x | u), hx⟩ <;> rfl
      right_inv := by rintro (w | u) <;> rfl }
  -- every edge is on a chain
  have hex : ∀ e, ∃ c, IsChain K ∅ c ∧ e ∈ c := exists_isChain_mem_of_bridge hloop hbr
  -- the nodes of a chain without `fK` are on one side
  have hside : ∀ c' : {c // IsChain K ∅ c}, fK ∉ c'.1 → ∀ j,
      (chainRep K ∅ c'.2).p j ∈ S ↔ (chainRep K ∅ c'.2).p 0 ∈ S := fun c' hf j =>
    ((chainRep K ∅ c'.2).isChainOf.mem_side_iff hcross (Nat.zero_le j.val) (by omega)
      fun l hl _ _ h' => hf ((chainRep K ∅ c'.2).range_eq ▸ ⟨⟨l, hl⟩, h'⟩)).symm
  have hmem : ∀ c' : {c // IsChain K ∅ c}, ∀ i, (chainRep K ∅ c'.2).e i ∈ c'.1 := fun c' i =>
    (Set.ext_iff.1 (chainRep K ∅ c'.2).range_eq _).1 ⟨i, rfl⟩
  -- `ε` has an end on each side
  set rε := chainRep K ∅ ε.2
  obtain ⟨i₀, hi₀⟩ : ∃ i, rε.e i = fK := by
    have := hεf
    rw [← rε.range_eq] at this
    exact this
  have hεside : rε.p 0 ∈ S ↔ rε.p (Fin.last rε.k) ∉ S := by
    have hne : ∀ l (hl : l < rε.k), l ≠ i₀.val → rε.e ⟨l, hl⟩ ≠ fK := fun l hl hln h' => hln <| by
      have := rε.isChainOf.injective_edge (h'.trans hi₀.symm)
      exact congrArg Fin.val this
    have h₁ := rε.isChainOf.mem_side_iff hcross (Nat.zero_le i₀.val) (by omega)
      fun l hl _ h' => hne l hl (by omega)
    have h₂ := rε.isChainOf.mem_side_iff hcross (Nat.succ_le_of_lt i₀.2) le_rfl
      fun l hl h' _ => hne l hl (by omega)
    have hji := rε.isChainOf.joins i₀
    rw [hi₀] at hji
    have hmid : rε.p i₀.castSucc ∈ S ↔ rε.p i₀.succ ∉ S := by
      rcases hji with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩ <;> rcases hj with ⟨k₃, k₄⟩ | ⟨k₃, k₄⟩
      · rw [← k₁, ← k₂, k₃, k₄]; exact ⟨fun _ => hs', fun _ => a.2⟩
      · rw [← k₁, ← k₂, k₃, k₄]; exact ⟨fun h => absurd h hs', fun h => absurd a.2 h⟩
      · rw [← k₁, ← k₂, k₃, k₄]; exact ⟨fun h => absurd h hs', fun h => absurd a.2 h⟩
      · rw [← k₁, ← k₂, k₃, k₄]; exact ⟨fun _ => hs', fun _ => a.2⟩
    exact h₁.trans (hmid.trans (not_congr h₂))
  -- a chain whose ends are on the side `S` does not contain `fK`
  have hnotε : ∀ c' : {c // IsChain K ∅ c}, ((suppress K).graph.source c').1 ∈ S →
      ((suppress K).graph.target c').1 ∈ S → fK ∉ c'.1 := by
    intro c' h₁ h₂ hf
    have hc' : c' = ε := Subtype.ext (c'.2.eq_of_mem ε.2 hf hεf)
    subst hc'
    rcases suppress_ends_val c' with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
    · rw [k₁] at h₁; rw [k₂] at h₂; exact hεside.mp h₁ h₂
    · rw [k₁] at h₁; rw [k₂] at h₂; exact hεside.mp h₂ h₁
  -- on such a chain, all the nodes are on the side `S`
  have hallS : ∀ c' : {c // IsChain K ∅ c}, ((suppress K).graph.source c').1 ∈ S →
      ((suppress K).graph.target c').1 ∈ S → ∀ j, (chainRep K ∅ c'.2).p j ∈ S := by
    intro c' h₁ h₂ j
    have hf := hnotε c' h₁ h₂
    refine (hside c' hf j).mpr ?_
    rcases suppress_ends_val c' with ⟨k₁, -⟩ | ⟨-, k₂⟩
    · rwa [k₁] at h₁
    · rwa [k₂] at h₂
  -- the chain of an edge of `K`
  let chainK : F → {c // IsChain K ∅ c} := fun e => ⟨(hex e).choose, (hex e).choose_spec.1⟩
  have hchainK : ∀ e, e ∈ (chainK e).1 := fun e => (hex e).choose_spec.2
  -- the chain of an edge of the side, not on `ε`, has its ends on the side
  have hchainS : ∀ e : {e // K.graph.source e ∈ S ∧ K.graph.target e ∈ S}, e.1 ∉ ε.1 →
      (suppress K).graph.source (chainK e.1) ∈ {w : {u // IsBranch K ∅ u} | w.1 ∈ S} ∧
        (suppress K).graph.target (chainK e.1) ∈ {w : {u // IsBranch K ∅ u} | w.1 ∈ S} := by
    intro e he
    have hf : fK ∉ (chainK e.1).1 := fun hf =>
      he (((chainK e.1).2.eq_of_mem ε.2 hf hεf) ▸ hchainK e.1)
    set r := chainRep K ∅ (chainK e.1).2
    obtain ⟨i, hi⟩ : ∃ i, r.e i = e.1 := by
      have := hchainK e.1
      rw [← r.range_eq] at this
      exact this
    have h0 : r.p 0 ∈ S := by
      refine (hside _ hf i.castSucc).mp ?_
      rcases r.isChainOf.joins i with ⟨k₁, -⟩ | ⟨-, k₂⟩
      · rw [← k₁, hi]; exact e.2.1
      · rw [← k₂, hi]; exact e.2.2
    have hl : r.p (Fin.last r.k) ∈ S := (hside _ hf _).mpr h0
    rcases suppress_ends_val (chainK e.1) with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
    · exact ⟨show _ ∈ S from k₁ ▸ h0, show _ ∈ S from k₂ ▸ hl⟩
    · exact ⟨show _ ∈ S from k₁ ▸ hl, show _ ∈ S from k₂ ▸ h0⟩
  -- the chains of the side
  let chainOf : ({d : {c // IsChain K ∅ c} // (suppress K).graph.source d ∈
      {w : {u // IsBranch K ∅ u} | w.1 ∈ S} ∧ (suppress K).graph.target d ∈
      {w : {u // IsBranch K ∅ u} | w.1 ∈ S}} ⊕ Unit) →
      Set ({e // K.graph.source e ∈ S ∧ K.graph.target e ∈ S} ⊕ Unit) := fun f' => match f' with
    | .inl d => {g | ∃ e'', g = .inl e'' ∧ e''.1 ∈ d.1.1}
    | .inr _ => insert (.inr ()) {g | ∃ e'', g = .inl e'' ∧ e''.1 ∈ ε.1}
  -- an edge of the side goes to the chain through it
  let ψ : ({e // K.graph.source e ∈ S ∧ K.graph.target e ∈ S} ⊕ Unit) →
      ({d : {c // IsChain K ∅ c} //
      (suppress K).graph.source d ∈ {w : {u // IsBranch K ∅ u} | w.1 ∈ S} ∧
      (suppress K).graph.target d ∈ {w : {u // IsBranch K ∅ u} | w.1 ∈ S}} ⊕ Unit) := fun g =>
    match g with
    | .inl e => if he : e.1 ∈ ε.1 then .inr () else .inl ⟨chainK e.1, hchainS e he⟩
    | .inr _ => .inr ()
  -- the chain of `ε` read from its end on the side `S`
  obtain ⟨k', p', e', hP', hrange, hp0', hlast'⟩ : ∃ (k' : ℕ) (p' : Fin (k' + 1) → S ⊕ Unit)
      (e' : Fin k' → _), IsChainOf P ∅ k' p' e' ∧ Set.range e' = insert (.inr ())
        {g | ∃ e'' : {e // K.graph.source e ∈ S ∧ K.graph.target e ∈ S}, g = .inl e'' ∧
          e''.1 ∈ ε.1} ∧ p' 0 = .inl ⟨b.1, hb⟩ ∧ p' (Fin.last k') = .inr () := by
    have hbends : b.1 = rε.p 0 ∨ b.1 = rε.p (Fin.last rε.k) := by
      rcases suppress_ends_val ε with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩ <;> rcases hbε with h | h <;>
        rw [← h]
      exacts [Or.inl k₁, Or.inr k₂, Or.inr k₁, Or.inl k₂]
    by_cases h0 : rε.p 0 ∈ S
    · obtain ⟨k', p', e', h', hr, hp0, hl⟩ :=
        rε.isChainOf.exists_pendantSide_inr hj hs' hcross (ι := ι) hloop hleaf hi₀ h0
      have hb0 : b.1 = rε.p 0 := hbends.resolve_right fun h => hεside.mp h0 (h ▸ hb)
      refine ⟨k', p', e', h', by rw [hr, rε.range_eq], ?_, hl⟩
      rw [hp0]
      congr 2
      exact hb0.symm
    · have hl : rε.p (Fin.last rε.k) ∈ S := by
        by_contra hl
        exact h0 (hεside.mpr hl)
      have hrev := rε.isChainOf.reverse
      have hi₀' : (rε.e ∘ Fin.rev) (Fin.rev i₀) = fK := by simp [hi₀]
      have hp0r : (rε.p ∘ Fin.rev) 0 ∈ S := by simpa using hl
      obtain ⟨k', p', e', h', hr, hp0, hl'⟩ :=
        hrev.exists_pendantSide_inr hj hs' hcross (ι := ι) hloop hleaf hi₀' hp0r
      have hbl : b.1 = rε.p (Fin.last rε.k) := hbends.resolve_left fun h => h0 (h ▸ hb)
      refine ⟨k', p', e', h', ?_, ?_, hl'⟩
      · rw [hr, Fin.rev_surjective.range_comp, rε.range_eq]
      · rw [hp0]
        congr 2
        simp [hbl]
  -- the chains of the side, other than that of the pendant edge
  have hrepL : ∀ d : {d : {c // IsChain K ∅ c} // (suppress K).graph.source d ∈
      {w : {u // IsBranch K ∅ u} | w.1 ∈ S} ∧ (suppress K).graph.target d ∈
      {w : {u // IsBranch K ∅ u} | w.1 ∈ S}}, ∃ (q : Fin ((chainRep K ∅ d.1.2).k + 1) → S ⊕ Unit)
      (g : Fin (chainRep K ∅ d.1.2).k → _), IsChainOf P ∅ _ q g ∧ Set.range g = chainOf (.inl d) ∧
      ∀ j, q j = .inl ⟨(chainRep K ∅ d.1.2).p j, hallS d.1 d.2.1 d.2.2 j⟩ := by
    intro d
    set r := chainRep K ∅ d.1.2
    refine ⟨_, _, r.isChainOf.pendantSide_inl hj hs' hcross hloop hleaf (hallS d.1 d.2.1 d.2.2),
      ?_, fun j => rfl⟩
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl, hmem d.1 i⟩
    · rintro ⟨e'', rfl, he''⟩
      rw [← r.range_eq] at he''
      obtain ⟨i, hi⟩ := he''
      exact ⟨i, congrArg Sum.inl (Subtype.ext hi)⟩
  have hchain : ∀ f', IsChain P ∅ (chainOf f') := by
    rintro (d | u)
    · obtain ⟨q, g, hq, hg, -⟩ := hrepL d
      exact ⟨_, q, g, hq, hg⟩
    · exact ⟨k', p', e', hP', hrange⟩
  have hψ : ∀ g, g ∈ chainOf (ψ g) := by
    rintro (e | u)
    · by_cases he : e.1 ∈ ε.1
      · simp only [ψ, he, ↓reduceDIte, chainOf]
        exact Or.inr ⟨e, rfl, he⟩
      · simp only [ψ, he, ↓reduceDIte, chainOf]
        exact ⟨e, rfl, hchainK e.1⟩
    · exact Or.inl rfl
  have hψ' : ∀ f', ∀ g ∈ chainOf f', ψ g = f' := by
    rintro (d | u) g hg
    · obtain ⟨e, rfl, he⟩ := hg
      have hf := hnotε d.1 d.2.1 d.2.2
      have heε : e.1 ∉ ε.1 := fun h => hf ((d.1.2.eq_of_mem ε.2 he h) ▸ hεf)
      simp only [ψ, heε, ↓reduceDIte]
      congr 1
      exact Subtype.ext (Subtype.ext ((chainK e.1).2.eq_of_mem d.1.2 (hchainK e.1) he))
    · rcases hg with rfl | ⟨e, rfl, he⟩
      · rfl
      · simp only [ψ, he, ↓reduceDIte]
  -- a hybrid edge of `ε` would be `fK`
  have hεund : ∀ e ∈ ε.1, ¬ K.IsDirected e := by
    intro e he hd
    rw [← rε.range_eq] at he
    obtain ⟨i, rfl⟩ := he
    have hk := rε.isChainOf.eq_one_of_isDirected hdirb hd
    have hii : i = i₀ := Fin.ext (by have := i.2; have := i₀.2; omega)
    rw [hii, hi₀] at hd
    exact hfd hd
  set R := pendantSide (suppress K) {w : {u // IsBranch K ∅ u} | w.1 ∈ S} ⟨b, hb⟩ ι
  have hends : ∀ f', chainEnds P ∅ (chainOf f') =
      {(φ.symm (R.graph.source f')).1, (φ.symm (R.graph.target f')).1} := by
    rintro (d | u)
    · obtain ⟨q, g, hq, hg, hqv⟩ := hrepL d
      have hs : (φ.symm (R.graph.source (.inl d))).1 =
          (.inl ⟨((suppress K).graph.source d.1).1, d.2.1⟩ : S ⊕ Unit) := rfl
      have ht : (φ.symm (R.graph.target (.inl d))).1 =
          (.inl ⟨((suppress K).graph.target d.1).1, d.2.2⟩ : S ⊕ Unit) := rfl
      rw [← hg, hq.chainEnds_eq, hqv, hqv, hs, ht]
      rcases suppress_ends_val d.1 with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
      · simp only [k₁, k₂]
      · simp only [k₁, k₂]
        exact Set.pair_comm _ _
    · rw [show chainOf (.inr u) = Set.range e' from hrange.symm, hP'.chainEnds_eq, hp0', hlast']
      rfl
  have hne : ∀ f', R.graph.source f' ≠ R.graph.target f' := by
    rintro (d | u) h
    · have := congrArg Subtype.val (Sum.inl_injective h)
      exact suppress_source_ne_target hloop hbr d.1 this
    · exact Sum.inl_ne_inr h
  have hdir : ∀ f', R.IsDirected f' ↔ ∃ g ∈ chainOf f', P.IsDirected g := by
    rintro (d | u)
    · set r := chainRep K ∅ d.1.2
      change r.PointsForward ∨ r.PointsBackward ↔ _
      have hFSd : ∀ i, K.graph.source (r.e i) ∈ S ∧ K.graph.target (r.e i) ∈ S := fun i => by
        rcases r.isChainOf.joins i with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
        · exact ⟨k₁ ▸ hallS d.1 d.2.1 d.2.2 _, k₂ ▸ hallS d.1 d.2.1 d.2.2 _⟩
        · exact ⟨k₁ ▸ hallS d.1 d.2.1 d.2.2 _, k₂ ▸ hallS d.1 d.2.1 d.2.2 _⟩
      constructor
      · rintro (⟨⟨i, hi⟩, -⟩ | ⟨⟨i, hi⟩, -⟩) <;>
          exact ⟨.inl ⟨r.e i, hFSd i⟩, ⟨⟨r.e i, hFSd i⟩, rfl, hmem d.1 i⟩, hi⟩
      · rintro ⟨g, ⟨e, rfl, he⟩, hd⟩
        rw [← r.range_eq] at he
        obtain ⟨i, hi⟩ := he
        have hd' : K.IsDirected (r.e i) := hi ▸ hd
        rcases ChainRep.pointsTo_of_isDirected hloop hdirb r hd' with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
    · constructor
      · intro h
        exact h.elim
      · rintro ⟨g, hg, hd⟩
        rcases hg with rfl | ⟨e, rfl, he⟩
        · exact hd
        · exact hεund e.1 he hd
  have hdir_tgt : ∀ f', ∀ g ∈ chainOf f', P.IsDirected g →
      P.graph.target g = (φ.symm (R.graph.target f')).1 := by
    rintro (d | u) g hg hd
    · obtain ⟨e, rfl, he⟩ := hg
      set r := chainRep K ∅ d.1.2
      rw [← r.range_eq] at he
      obtain ⟨i, hi⟩ := he
      have hd' : K.IsDirected (r.e i) := hi ▸ hd
      have hl : P.graph.target (.inl e) = (.inl ⟨K.graph.target e.1, e.2.2⟩ : S ⊕ Unit) := rfl
      have hr : (φ.symm (R.graph.target (.inl d))).1 =
          (.inl ⟨((suppress K).graph.target d.1).1, d.2.2⟩ : S ⊕ Unit) := rfl
      rw [hl, hr]
      congr 1
      apply Subtype.ext
      change K.graph.target e.1 = ((suppressExcept K ∅).graph.target ⟨d.1.1, d.1.2⟩).1
      rw [suppressExcept_target_val, ← hi]
      unfold ChainRep.tgt
      rcases ChainRep.pointsTo_of_isDirected hloop hdirb r hd' with ⟨-, hb', ht⟩ | ⟨hb', -, ht⟩ <;>
        split_ifs with hpb
      · exact absurd hpb hb'
      · exact ht
      · exact ht
      · exact absurd hb' hpb
    · rcases hg with rfl | ⟨e, rfl, he⟩
      · exact hd.elim
      · exact absurd hd (hεund e.1 he)
  have hleafR : ∀ z, R.leaf z = φ ⟨P.leaf z, Or.inr (Or.inl ⟨z, rfl⟩)⟩ := by
    intro z
    by_cases h : K.leaf (ι z) ∈ S
    · have hPl : P.leaf z = .inl ⟨K.leaf (ι z), h⟩ := pendantSide_leaf_of_mem h
      have hRl : R.leaf z = .inl ⟨(suppress K).leaf (ι z), h⟩ := pendantSide_leaf_of_mem (ι := ι)
        (S := {w : {u // IsBranch K ∅ u} | w.1 ∈ S}) h
      rw [hRl]
      have : (⟨P.leaf z, Or.inr (Or.inl ⟨z, rfl⟩)⟩ : {u // IsBranch P ∅ u}) =
          ⟨.inl ⟨K.leaf (ι z), h⟩, by rw [← hPl]; exact Or.inr (Or.inl ⟨z, rfl⟩)⟩ :=
        Subtype.ext hPl
      rw [this]
      rfl
    · have hPl : P.leaf z = .inr () := pendantSide_leaf_of_notMem h
      have hRl : R.leaf z = .inr () := pendantSide_leaf_of_notMem (ι := ι)
        (S := {w : {u // IsBranch K ∅ u} | w.1 ∈ S}) h
      rw [hRl]
      have : (⟨P.leaf z, Or.inr (Or.inl ⟨z, rfl⟩)⟩ : {u // IsBranch P ∅ u}) =
          ⟨.inr (), by rw [← hPl]; exact Or.inr (Or.inl ⟨z, rfl⟩)⟩ := Subtype.ext hPl
      rw [this]
      rfl
  obtain ⟨ι', -⟩ := exists_sdIso_suppressExcept (R := R) φ chainOf hchain ψ hψ hψ' hends hne hdir
    hdir_tgt hleafR
  exact ⟨ι'⟩

end SuppressSide

/-! ### The contracted network of a half -/

/-- **Injective maps of graphs that keep the ends of the edges carry cycles to cycles.** -/
theorem isCycle_image_of_joins {V₁ E₁ V₂ E₂ : Type*} {G₁ : DirectedMultigraph V₁ E₁}
    {G₂ : DirectedMultigraph V₂ E₂} (φ : V₁ → V₂) (ψ : E₁ → E₂) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (hj : ∀ e, Joins G₂ (ψ e) (φ (G₁.source e)) (φ (G₁.target e)))
    {C : Set E₁} (hC : IsCycle G₁ C) : IsCycle G₂ (ψ '' C) := by
  obtain ⟨k, v, e, hc, rfl⟩ := hC
  refine ⟨k, φ ∘ v, ψ ∘ e, ⟨hc.pos, fun i => ?_, hφ.comp hc.injective_node,
    hψ.comp hc.injective_edge⟩, Set.range_comp ..⟩
  have h := hj (e i)
  rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂] at h
    exact h
  · rw [h₁, h₂] at h
    exact Or.symm h

section HalfContract

variable {G : SemidirectedNetwork V E X} {f : E} {y y' : V} {Z : Type*} {ι : Z → X}

/-- The edge of the network of an edge of the half: an edge of the side, or `f` for the pendant
edge. -/
def halfEdge (G : SemidirectedNetwork V E X) (f : E) (y : V) :
    {e // G.graph.source e ∈ cutSide G.graph f y ∧ G.graph.target e ∈ cutSide G.graph f y} ⊕ Unit →
      E :=
  Sum.elim Subtype.val fun _ => f

/-- The node of the network of a node of the half: a node of the side, or `y'` for the new leaf. -/
def halfNode (G : SemidirectedNetwork V E X) (f : E) (y y' : V) :
    ↥(cutSide G.graph f y) ⊕ Unit → V :=
  Sum.elim Subtype.val fun _ => y'

variable (hG : G.graph.IsConnected) (hf : ∀ C, IsCycle G.graph C → f ∉ C)
  (hj : Joins G.graph f y y')
include hG hf hj

theorem y'_notMem_cutSide : y' ∉ cutSide G.graph f y := by
  rw [← mem_cutSide_iff_notMem hG hf hj]
  exact Relation.ReflTransGen.refl

theorem halfEdge_injective : Function.Injective (halfEdge G f y) := by
  have hy' := y'_notMem_cutSide hG hf hj
  rintro (e₁ | u₁) (e₂ | u₂) h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact absurd h (ne_of_mem_side (a := ⟨y, Relation.ReflTransGen.refl⟩) hj hy' e₁)
  · exact absurd h.symm (ne_of_mem_side (a := ⟨y, Relation.ReflTransGen.refl⟩) hj hy' e₂)
  · rfl

/-- **A cycle of the half is a cycle of the network**, through the maps `halfNode` and `halfEdge`.
-/
theorem isCycle_halfEdge_image {C : Set _} (hC : IsCycle (halfNet G f y ι).graph C) :
    IsCycle G.graph (halfEdge G f y '' C) := by
  have hy' := y'_notMem_cutSide hG hf hj
  refine isCycle_image_of_joins (halfNode G f y y') (halfEdge G f y) ?_
    (halfEdge_injective hG hf hj) ?_ hC
  · rintro (x₁ | u₁) (x₂ | u₂) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have h' : x₁.1 = y' := h
      exact absurd (h' ▸ x₁.2) hy'
    · have h' : y' = x₂.1 := h
      exact absurd (h' ▸ x₂.2) hy'
    · rfl
  · rintro (e | u)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact hj

/-- The pendant edge lies on no cycle of the half. -/
theorem inr_notMem_of_isCycle_halfNet {C : Set _} (hC : IsCycle (halfNet G f y ι).graph C) :
    .inr () ∉ C := fun h => hf _ (isCycle_halfEdge_image hG hf hj hC) ⟨_, h, rfl⟩

/-- The new leaf lies on no cycle of the half. -/
theorem inr_notMem_cycleNodes_halfNet {C : Set _} (hC : IsCycle (halfNet G f y ι).graph C) :
    .inr () ∉ cycleNodes (halfNet G f y ι).graph C := by
  rintro ⟨g, hg, hinc⟩
  rcases g with g | u
  · rcases hinc with h | h <;> exact Sum.inl_ne_inr h
  · exact inr_notMem_of_isCycle_halfNet hG hf hj hC hg

omit hG hj in
/-- **A cycle of the network at a node of the side is a cycle of the half.** -/
theorem isCycle_halfNet_of_isCycle {D : Set E} (hD : IsCycle G.graph D) {x : V}
    (hx : x ∈ cycleNodes G.graph D) (hxA : x ∈ cutSide G.graph f y) :
    ∃ C, IsCycle (halfNet G f y ι).graph C ∧ halfEdge G f y '' C = D ∧ C.ncard = D.ncard ∧
      ∀ w (hw : w ∈ cutSide G.graph f y), w ∈ cycleNodes G.graph D →
        (.inl ⟨w, hw⟩ : ↥(cutSide G.graph f y) ⊕ Unit) ∈ cycleNodes (halfNet G f y ι).graph C := by
  -- the nodes of `D` are on the side of `y`
  have hDA : ∀ w ∈ cycleNodes G.graph D, w ∈ cutSide G.graph f y := by
    intro w hw
    obtain ⟨g, hg, -⟩ := id hx
    refine Relation.ReflTransGen.trans hxA (walks_mono ?_ (hD.walks_sdiff_singleton hg hx hw))
    intro e he h
    exact hf D hD (Set.mem_singleton_iff.mp h ▸ he.1)
  obtain ⟨k, v, e, hc, rfl⟩ := hD
  have hvA : ∀ i, v i ∈ cutSide G.graph f y := fun i => hDA _ (by
    rw [hc.cycleNodes_eq]
    exact ⟨i, rfl⟩)
  have heA : ∀ i, G.graph.source (e i) ∈ cutSide G.graph f y ∧
      G.graph.target (e i) ∈ cutSide G.graph f y := fun i => by
    rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨h₁ ▸ hvA _, h₂ ▸ hvA _⟩
    · exact ⟨h₁ ▸ hvA _, h₂ ▸ hvA _⟩
  set e' : Fin k → {e // G.graph.source e ∈ cutSide G.graph f y ∧
      G.graph.target e ∈ cutSide G.graph f y} ⊕ Unit := fun i => .inl ⟨e i, heA i⟩
  have he'inj : Function.Injective e' := fun i j h =>
    hc.injective_edge (congrArg Subtype.val (Sum.inl_injective h))
  have hc' : IsCycleOf (halfNet G f y ι).graph k (fun i => .inl ⟨v i, hvA i⟩) e' := by
    refine ⟨hc.pos, fun i => ?_, fun i j h => hc.injective_node
      (congrArg Subtype.val (Sum.inl_injective h)), he'inj⟩
    rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨congrArg Sum.inl (Subtype.ext h₁), congrArg Sum.inl (Subtype.ext h₂)⟩
    · exact Or.inr ⟨congrArg Sum.inl (Subtype.ext h₁), congrArg Sum.inl (Subtype.ext h₂)⟩
  refine ⟨Set.range e', ⟨k, _, e', hc', rfl⟩, ?_, ?_, fun w hw hwD => ?_⟩
  · rw [← Set.range_comp]
    rfl
  · rw [← Set.image_univ, ← Set.image_univ, Set.ncard_image_of_injective _ he'inj,
      Set.ncard_image_of_injective _ hc.injective_edge]
  · rw [hc.cycleNodes_eq] at hwD
    obtain ⟨i, rfl⟩ := hwD
    rw [hc'.cycleNodes_eq]
    exact ⟨i, rfl⟩

/-- **An edge of the side is on a cycle of a given size of the half exactly when it is on one of the
network.** -/
theorem exists_isCycle_halfNet_iff (Pn : ℕ → Prop)
    (e : {e // G.graph.source e ∈ cutSide G.graph f y ∧ G.graph.target e ∈ cutSide G.graph f y}) :
    (∃ C, IsCycle (halfNet G f y ι).graph C ∧ Pn C.ncard ∧ .inl e ∈ C) ↔
      ∃ D, IsCycle G.graph D ∧ Pn D.ncard ∧ e.1 ∈ D := by
  constructor
  · rintro ⟨C, hC, hP, he⟩
    have hinj : Set.InjOn (halfEdge G f y) C := (halfEdge_injective hG hf hj).injOn
    refine ⟨_, isCycle_halfEdge_image hG hf hj hC, ?_, ⟨_, he, rfl⟩⟩
    rwa [hinj.ncard_image]
  · rintro ⟨D, hD, hP, he⟩
    obtain ⟨C, hC, hCD, hn, hnodes⟩ := isCycle_halfNet_of_isCycle (ι := ι) hf hD
      ⟨e.1, he, Or.inl rfl⟩ e.2.1
    refine ⟨C, hC, hn ▸ hP, ?_⟩
    -- the edge `inl e` is the edge of `C` over `e`
    have : e.1 ∈ halfEdge G f y '' C := hCD ▸ he
    obtain ⟨g, hg, hge⟩ := this
    rcases g with g | u
    · exact (show g = e from Subtype.ext hge) ▸ hg
    · exact absurd hg (inr_notMem_of_isCycle_halfNet hG hf hj hC)

omit hG in
/-- **The contracted network of a half is the side of the contracted network**, with the pendant
edge at the class of `y`. -/
theorem nonempty_sdIso_tildeContracted_halfNet [Finite E] (hG : IsUnrootedLevelOne G) :
    Nonempty (SDIso (tildeContracted (halfNet G f y ι))
      (pendantSide (tildeContracted G) (contractSide G f y)
        ⟨Quot.mk _ y, ⟨y, Relation.ReflTransGen.refl, rfl⟩⟩ ι)) := by
  classical
  have hcon := hG.connected
  set H := halfNet G f y ι with hH_def
  -- the classes of the contraction of the half
  have hrel : ∀ u w, ContractRel H.graph (fun C => C.ncard ≤ 3) u w → ∃ x₁ x₂, u = .inl x₁ ∧
      w = .inl x₂ ∧ (Quot.mk _ x₁.1 : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) =
        Quot.mk _ x₂.1 := by
    rintro u w ⟨C, hC, hP, hu, hw⟩
    have hC' := isCycle_halfEdge_image hcon hf hj hC
    have hn : (halfEdge G f y '' C).ncard ≤ 3 := by
      rwa [(halfEdge_injective hcon hf hj).injOn.ncard_image]
    have hnode : ∀ x, (.inl x : ↥(cutSide G.graph f y) ⊕ Unit) ∈ cycleNodes H.graph C →
        x.1 ∈ cycleNodes G.graph (halfEdge G f y '' C) := by
      rintro x ⟨g, hg, hinc⟩
      rcases g with g | g
      · refine ⟨g.1, ⟨.inl g, hg, rfl⟩, ?_⟩
        rcases hinc with h | h
        · exact Or.inl (congrArg Subtype.val (Sum.inl_injective h))
        · exact Or.inr (congrArg Subtype.val (Sum.inl_injective h))
      · exact absurd hg (inr_notMem_of_isCycle_halfNet hcon hf hj hC)
    rcases u with x₁ | u'
    · rcases w with x₂ | w'
      · exact ⟨x₁, x₂, rfl, rfl, Quot.sound ⟨_, hC', hn, hnode x₁ hu, hnode x₂ hw⟩⟩
      · exact absurd hw (inr_notMem_cycleNodes_halfNet hcon hf hj hC)
    · exact absurd hu (inr_notMem_cycleNodes_halfNet hcon hf hj hC)
  have hlift : ∀ x₁ x₂ : ↥(cutSide G.graph f y),
      (Quot.mk _ x₁.1 : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) = Quot.mk _ x₂.1 →
      (Quot.mk _ (.inl x₁) : Quot (ContractRel H.graph fun C => C.ncard ≤ 3)) =
        Quot.mk _ (.inl x₂) := by
    intro x₁ x₂ h
    rcases (tildeContracted_mk_eq_iff hG).1 h with h' | ⟨D, hD, hP, h₁, h₂⟩
    · rw [Subtype.ext h']
    · obtain ⟨C, hC, -, hn, hnodes⟩ := isCycle_halfNet_of_isCycle (ι := ι) hf hD h₁ x₁.2
      exact Quot.sound ⟨C, hC, show C.ncard ≤ 3 by omega, hnodes _ x₁.2 h₁, hnodes _ x₂.2 h₂⟩
  -- the nodes
  let F₀ : ↥(cutSide G.graph f y) ⊕ Unit → ↥(contractSide G f y) ⊕ Unit :=
    Sum.elim (fun x => .inl ⟨Quot.mk _ x.1, ⟨x.1, x.2, rfl⟩⟩) fun _ => .inr ()
  have hF₀ : ∀ u w, ContractRel H.graph (fun C => C.ncard ≤ 3) u w → F₀ u = F₀ w := by
    intro u w h
    obtain ⟨x₁, x₂, rfl, rfl, hq⟩ := hrel u w h
    exact congrArg Sum.inl (Subtype.ext hq)
  have hrep : ∀ q ∈ contractSide G f y, ∃ x : ↥(cutSide G.graph f y), q = Quot.mk _ x.1 :=
    fun q ⟨x, hx, hq⟩ => ⟨⟨x, hx⟩, hq⟩
  let vert : Quot (ContractRel H.graph fun C => C.ncard ≤ 3) ≃ ↥(contractSide G f y) ⊕ Unit :=
    { toFun := Quot.lift F₀ hF₀
      invFun := Sum.elim (fun q => Quot.mk _ (.inl (hrep q.1 q.2).choose))
        fun _ => Quot.mk _ (.inr ())
      left_inv := by
        intro q
        induction q using Quot.ind with
        | mk u =>
          rcases u with x | u
          · exact hlift _ _ (hrep _ ⟨x.1, x.2, rfl⟩).choose_spec.symm
          · rfl
      right_inv := by
        rintro (q | u)
        · exact congrArg Sum.inl (Subtype.ext (hrep q.1 q.2).choose_spec.symm)
        · rfl }
  -- the edges
  have hsmall : ∀ e : {e // G.graph.source e ∈ cutSide G.graph f y ∧
      G.graph.target e ∈ cutSide G.graph f y},
      (∀ C, IsCycle H.graph C → C.ncard ≤ 3 → .inl e ∉ C) ↔
        ∀ D, IsCycle G.graph D → D.ncard ≤ 3 → e.1 ∉ D := fun e => by
    have := exists_isCycle_halfNet_iff (ι := ι) hcon hf hj (· ≤ 3) e
    constructor
    · intro h D hD hP he
      obtain ⟨C, hC, hPC, heC⟩ := this.mpr ⟨D, hD, hP, he⟩
      exact h C hC hPC heC
    · intro h C hC hP he
      obtain ⟨D, hD, hPD, heD⟩ := this.mp ⟨C, hC, hP, he⟩
      exact h D hD hPD heD
  have hpend : ∀ C, IsCycle H.graph C → C.ncard ≤ 3 → .inr () ∉ C := fun C hC _ =>
    inr_notMem_of_isCycle_halfNet hcon hf hj hC
  let edge : {h : _ // ∀ C, IsCycle H.graph C → C.ncard ≤ 3 → h ∉ C} ≃
      {g : {e // ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → e ∉ C} //
        (tildeContracted G).graph.source g ∈ contractSide G f y ∧
        (tildeContracted G).graph.target g ∈ contractSide G f y} ⊕ Unit :=
    { toFun := fun h => match h with
        | ⟨.inl e, he⟩ => .inl ⟨⟨e.1, (hsmall e).mp he⟩, ⟨_, e.2.1, rfl⟩, ⟨_, e.2.2, rfl⟩⟩
        | ⟨.inr _, _⟩ => .inr ()
      invFun := fun g => match g with
        | .inl g => ⟨.inl ⟨g.1.1, (mk_mem_contractSide_iff hf _).mp g.2.1,
            (mk_mem_contractSide_iff hf _).mp g.2.2⟩, (hsmall _).mpr g.1.2⟩
        | .inr _ => ⟨.inr (), hpend⟩
      left_inv := by rintro ⟨(e | u), he⟩ <;> rfl
      right_inv := by rintro (g | u) <;> rfl }
  refine ⟨{ vert := vert
            edge := edge
            isDirected_iff := fun h => ?_
            joins := fun h => ?_
            directed := fun h hd => ?_
            leaf := fun z => ?_ }⟩
  · rcases h with ⟨e | u, he⟩
    · have := exists_isCycle_halfNet_iff (ι := ι) hcon hf hj (· = 4) e
      exact and_congr Iff.rfl (not_congr this.symm)
    · exact ⟨False.elim, fun h => h.1⟩
  · rcases h with ⟨e | u, he⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases h with ⟨e | u, he⟩
    · exact ⟨rfl, rfl⟩
    · exact hd.1.elim
  · by_cases hz : G.leaf (ι z) ∈ cutSide G.graph f y
    · have hH : H.leaf z = .inl ⟨G.leaf (ι z), hz⟩ := pendantSide_leaf_of_mem hz
      have hK : (tildeContracted G).leaf (ι z) ∈ contractSide G f y := ⟨_, hz, rfl⟩
      rw [pendantSide_leaf_of_mem hK]
      change _ = vert (Quot.mk _ (H.leaf z))
      rw [hH]
      rfl
    · have hH : H.leaf z = .inr () := pendantSide_leaf_of_notMem hz
      have hK : (tildeContracted G).leaf (ι z) ∉ contractSide G f y := fun h =>
        hz ((mk_mem_contractSide_iff hf _).mp h)
      rw [pendantSide_leaf_of_notMem hK]
      change _ = vert (Quot.mk _ (H.leaf z))
      rw [hH]
      rfl

end HalfContract

/-- **`Ñ` of a half is the half of `Ñ`**: `Ñ` of the side of `y` of an edge `f` on no cycle, with
`f` as a pendant edge, is the side of `y` of `Ñ`, with the edge `ε` of `Ñ` through `f` as a pendant
edge. -/
theorem tilde_halfNet [Finite V] [Finite E] {G : SemidirectedNetwork V E X}
    (hG : IsUnrootedLevelOne G) {f : E} (hf : ∀ C, IsCycle G.graph C → f ∉ C) {y y' : V}
    (hj : Joins G.graph f y y') {ε : {c // IsChain (tildeContracted G) ∅ c}}
    (hεf : ∃ g ∈ ε.1, g.1 = f) {a : {u // IsBranch (tildeContracted G) ∅ u}}
    (ha : a ∈ tildeCutSide G f y)
    (haε : (tildeNetwork G).graph.source ε = a ∨ (tildeNetwork G).graph.target ε = a)
    {Z : Type*} (ι : Z → X) :
    Nonempty (SDIso (tildeNetwork (halfNet G f y ι))
      (pendantSide (tildeNetwork G) (tildeCutSide G f y) ⟨a, ha⟩ ι)) := by
  classical
  have hfK : ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → f ∉ C := fun C hC _ => hf C hC
  obtain ⟨i₁⟩ := nonempty_sdIso_tildeContracted_halfNet (ι := ι) hf hj hG
  have hεf' : (⟨f, hfK⟩ : {e // ∀ C, IsCycle G.graph C → C.ncard ≤ 3 → e ∉ C}) ∈ ε.1 := by
    obtain ⟨g, hg, hgf⟩ := hεf
    rwa [show g = ⟨f, hfK⟩ from Subtype.ext hgf] at hg
  have hjK : Joins (tildeContracted G).graph ⟨f, hfK⟩ (Quot.mk _ y) (Quot.mk _ y') := by
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨congrArg (Quot.mk _) h₁, congrArg (Quot.mk _) h₂⟩
    · exact Or.inr ⟨congrArg (Quot.mk _) h₁, congrArg (Quot.mk _) h₂⟩
  have hs'K : Quot.mk _ y' ∉ contractSide G f y := fun h =>
    y'_notMem_cutSide hG.connected hf hj ((mk_mem_contractSide_iff hf y').mp h)
  have hcrossK : ∀ e, e ≠ ⟨f, hfK⟩ → ((tildeContracted G).graph.source e ∈ contractSide G f y ↔
      (tildeContracted G).graph.target e ∈ contractSide G f y) := fun e he =>
    source_mem_contractSide_iff hf fun h => he (Subtype.ext h)
  have hleafK : ∀ x, degree (tildeContracted G).graph ((tildeContracted G).leaf x) ≠ 2 := by
    intro x
    change degree _ (Quot.mk _ (G.leaf x)) ≠ 2
    rw [degree_tildeContracted_of_notMem hG fun C hC _ hx => hG.not_leaf_of_mem hC hx ⟨x, rfl⟩,
      hG.degree_leaf x]
    omega
  have hfdK : ¬ (tildeContracted G).IsDirected ⟨f, hfK⟩ := fun h => by
    obtain ⟨C, hC, hfC⟩ := hG.mem_cycle_of_isDirected f h.1
    exact hf C hC hfC
  obtain ⟨i₂⟩ := nonempty_sdIso_suppress_pendantSide (ι := ι) (K := tildeContracted G)
    (S := contractSide G f y)
    (a := ⟨Quot.mk _ y, ⟨y, Relation.ReflTransGen.refl, rfl⟩⟩) hjK hs'K hcrossK
    (tildeContracted_loopless hG) (tildeContracted_bridge hG) hleafK
    (fun e hd => tildeContracted_isBranch_of_isDirected hG hd) hfdK hεf' ha haε
  exact ⟨(i₁.suppressExcept fun _ => Iff.rfl).trans i₂⟩

/-- **`Ñ` is its own half when the other side has one taxon**: when the only taxon on the side of
`y'` of an edge `f` on no cycle is `z₀`, the nodes of `Ñ` on that side reduce to the leaf of `z₀`,
and `Ñ` is its side of `y` with the edge `ε` through `f` as a pendant edge. -/
theorem tilde_sdIso_pendantSide_of_side [Finite V] [Finite E] {G : SemidirectedNetwork V E X}
    (hG : IsUnrootedLevelOne G) {f : E} (hf : ∀ C, IsCycle G.graph C → f ∉ C) {y y' : V}
    (hj : Joins G.graph f y y') {z₀ : X} (hz₀ : ∀ x, G.leaf x ∈ cutSide G.graph f y' ↔ x = z₀)
    {ε : {c // IsChain (tildeContracted G) ∅ c}} (hεf : ∃ g ∈ ε.1, g.1 = f)
    {a : {u // IsBranch (tildeContracted G) ∅ u}} (ha : a ∈ tildeCutSide G f y)
    (haε : (tildeNetwork G).graph.source ε = a ∨ (tildeNetwork G).graph.target ε = a) :
    Nonempty (SDIso (tildeNetwork G)
      (pendantSide (tildeNetwork G) (tildeCutSide G f y) ⟨a, ha⟩ id)) := by
  classical
  obtain ⟨ε₀, a₀, b₀, ⟨g₀, hg₀, hg₀f⟩, ha₀, hb₀, hj₀, hund, hcross, hcompl, -⟩ := tilde_cut hG hf hj
  -- `ε` is the edge `ε₀` of `Ñ` through `f`
  obtain ⟨g, hg, hgf⟩ := hεf
  have hεε : ε₀ = ε := Subtype.ext (ε₀.2.eq_of_mem ε.2 hg₀
    (by rwa [show g₀ = g from Subtype.ext (hg₀f.trans hgf.symm)]))
  subst hεε
  -- the nodes of `Ñ` on the side of `y'` reduce to the leaf of `z₀`
  have hside : ∀ w, w ∈ tildeCutSide G f y' → w.1 = Quot.mk _ (G.leaf z₀) := by
    intro w hw
    obtain ⟨x, hx, hwx⟩ := hw
    by_cases hl : ∃ t, G.leaf t = x
    · obtain ⟨t, rfl⟩ := hl
      rw [hwx, (hz₀ t).mp hx]
    · obtain ⟨D, hD, hD2, hxD⟩ := hG.exists_two_cycle_of_side hf hj hz₀ hx hl
      have := (isBranch_tildeContracted_iff hG _).mp w.2
      rw [hwx, degree_tildeContracted_of_mem hG hD (by omega) hxD, hD2] at this
      exact absurd rfl this
  have hb : ∀ w, w ∉ tildeCutSide G f y ↔ w = b₀ := by
    intro w
    constructor
    · intro h
      exact Subtype.ext ((hside w ((hcompl w).mpr h)).trans (hside b₀ hb₀).symm)
    · intro h
      rw [h]
      exact (hcompl b₀).mp hb₀
  have haa : a = a₀ := by
    have : a ≠ b₀ := fun h => (hcompl b₀).mp hb₀ (h ▸ ha)
    rcases hj₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases haε with h | h
    · exact h.symm.trans h₁
    · exact absurd (h.symm.trans h₂) this
    · exact absurd (h.symm.trans h₁) this
    · exact h.symm.trans h₂
  -- the leaf of `z₀` has one edge in the contracted network
  have hdeg1 : degree (tildeContracted G).graph b₀.1 = 1 := by
    rw [hside b₀ hb₀, degree_tildeContracted_of_notMem hG
      (fun C hC _ hx => hG.not_leaf_of_mem hC hx ⟨z₀, rfl⟩), hG.degree_leaf]
  have hone : ∀ g₁ g₂, ((tildeContracted G).graph.source g₁ = b₀.1 ∨
      (tildeContracted G).graph.target g₁ = b₀.1) → ((tildeContracted G).graph.source g₂ = b₀.1 ∨
      (tildeContracted G).graph.target g₂ = b₀.1) → g₁ = g₂ := by
    intro g₁ g₂ h₁ h₂
    rw [degree_eq_ncard_incident (tildeContracted_loopless hG)] at hdeg1
    obtain ⟨g', hg'⟩ := Set.ncard_eq_one.mp hdeg1
    have m₁ : g₁ ∈ ({g'} : Set _) := hg' ▸ h₁
    have m₂ : g₂ ∈ ({g'} : Set _) := hg' ▸ h₂
    exact (Set.mem_singleton_iff.mp m₁).trans (Set.mem_singleton_iff.mp m₂).symm
  -- so every other edge of `Ñ` is on the side of `y`
  have honly : ∀ e, e ≠ ε₀ → (tildeNetwork G).graph.source e ∈ tildeCutSide G f y ∧
      (tildeNetwork G).graph.target e ∈ tildeCutSide G f y := by
    intro e he
    have hs : (tildeNetwork G).graph.source e ∈ tildeCutSide G f y := by
      by_contra hs
      apply he
      obtain ⟨g₁, hg₁, hi₁⟩ := exists_mem_incident_of_tildeNetwork (Or.inl ((hb _).mp hs))
      obtain ⟨g₂, hg₂, hi₂⟩ := exists_mem_incident_of_tildeNetwork hj₀.incident_right
      exact Subtype.ext (e.2.eq_of_mem ε₀.2 hg₁ (hone g₁ g₂ hi₁ hi₂ ▸ hg₂))
    exact ⟨hs, (hcross e he).mp hs⟩
  exact nonempty_sdIso_pendantSide (tildeNetwork G) ha hb (by rw [haa]; exact hj₀) hund honly

/-! ### A network restricted to edges containing those at one side -/

section RestrictSide

variable [Finite E] {G : SemidirectedNetwork V E X} (hG : IsUnrootedLevelOne G) {f : E} {y : V}
  {T : Set E} (hT : ∀ g, (G.graph.source g ∈ cutSide G.graph f y ∨
    G.graph.target g ∈ cutSide G.graph f y) → g ∈ T) (Z : Set X)
include hG hT

/-- A node of the side is kept by the restriction. -/
theorem mem_keptNodes_of_side {x : V} (hx : x ∈ cutSide G.graph f y) : x ∈ keptNodes G T Z := by
  have hd : 1 ≤ degree G.graph x := by
    by_cases hl : ∃ t, G.leaf t = x
    · obtain ⟨t, rfl⟩ := hl
      rw [hG.degree_leaf]
    · rw [hG.degree_of_not_leaf x hl]
      omega
  rw [degree_eq_ncard_incident hG.loopless] at hd
  obtain ⟨g, hg⟩ := Set.nonempty_of_ncard_ne_zero
    (by omega : {e | G.graph.source e = x ∨ G.graph.target e = x}.ncard ≠ 0)
  refine Or.inl ⟨g, hT g ?_, hg⟩
  rcases hg with h | h
  · exact Or.inl (h ▸ hx)
  · exact Or.inr (h ▸ hx)

omit [Finite E] hT in
/-- The restriction has no loops. -/
theorem restrict_loopless (e : T) :
    (restrict G T Z).graph.source e ≠ (restrict G T Z).graph.target e := fun h =>
  hG.loopless e.1 (congrArg Subtype.val h)

/-- **A node of the side keeps its degree in the restriction.** -/
theorem degree_restrict_of_side {x : V} (hx : x ∈ cutSide G.graph f y) :
    degree (restrict G T Z).graph ⟨x, mem_keptNodes_of_side hG hT Z hx⟩ = degree G.graph x := by
  rw [degree_eq_ncard_incident (restrict_loopless hG Z), degree_eq_ncard_incident hG.loopless]
  refine Set.ncard_congr (fun e _ => e.1) ?_ (fun e e' _ _ h => Subtype.ext h) ?_
  · intro e he
    rcases he with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · intro g hg
    refine ⟨⟨g, hT g ?_⟩, ?_, rfl⟩
    · rcases hg with h | h
      · exact Or.inl (h ▸ hx)
      · exact Or.inr (h ▸ hx)
    · rcases hg with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)

/-- **A node of the side is kept by the suppression of the restriction**: its degree is one or
three. -/
theorem isBranch_restrict_of_side {x : V} (hx : x ∈ cutSide G.graph f y) :
    IsBranch (restrict G T Z) ∅ ⟨x, mem_keptNodes_of_side hG hT Z hx⟩ := by
  refine Or.inl ?_
  rw [degree_restrict_of_side hG hT Z hx]
  by_cases hl : ∃ t, G.leaf t = x
  · obtain ⟨t, rfl⟩ := hl
    rw [hG.degree_leaf]
    omega
  · rw [hG.degree_of_not_leaf x hl]
    omega

/-- The node of the suppressed restriction of a node of the side. -/
def sideNode (hG : IsUnrootedLevelOne G)
    (hT : ∀ g, (G.graph.source g ∈ cutSide G.graph f y ∨ G.graph.target g ∈ cutSide G.graph f y) →
      g ∈ T) (Z : Set X) (x : ↥(cutSide G.graph f y)) :
    {u // IsBranch (restrict G T Z) ∅ u} :=
  ⟨⟨x.1, mem_keptNodes_of_side hG hT Z x.2⟩, isBranch_restrict_of_side hG hT Z x.2⟩

theorem sideNode_val (x : ↥(cutSide G.graph f y)) : (sideNode hG hT Z x).1.1 = x.1 := rfl

/-- An edge of the side, alone, is a chain of the restriction. -/
theorem isChainOf_single (e : {e // G.graph.source e ∈ cutSide G.graph f y ∧
    G.graph.target e ∈ cutSide G.graph f y}) :
    IsChainOf (restrict G T Z) ∅ 1
      ![⟨G.graph.source e.1, mem_keptNodes_of_side hG hT Z e.2.1⟩,
        ⟨G.graph.target e.1, mem_keptNodes_of_side hG hT Z e.2.2⟩]
      ![⟨e.1, hT e.1 (Or.inl e.2.1)⟩] where
  pos := one_pos
  joins i := by
    fin_cases i
    exact Or.inl ⟨rfl, rfl⟩
  inner j h0 hl := by
    fin_cases j
    · exact absurd rfl h0
    · exact absurd rfl hl
  ends := ⟨isBranch_restrict_of_side hG hT Z e.2.1, isBranch_restrict_of_side hG hT Z e.2.2⟩
  injective_edge i j _ := by
    fin_cases i
    fin_cases j
    rfl

/-- The edge of the suppressed restriction of an edge of the side. -/
def sideEdge (e : {e // G.graph.source e ∈ cutSide G.graph f y ∧
    G.graph.target e ∈ cutSide G.graph f y}) : {c : Set T // IsChain (restrict G T Z) ∅ c} :=
  ⟨{⟨e.1, hT e.1 (Or.inl e.2.1)⟩}, ⟨1, _, _, isChainOf_single hG hT Z e, by
    ext g
    simp⟩⟩

/-- **An edge of the side is an edge of the suppressed restriction**, with the same ends and
direction. -/
theorem sideEdge_spec (e : {e // G.graph.source e ∈ cutSide G.graph f y ∧
    G.graph.target e ∈ cutSide G.graph f y}) :
    Joins (suppress (restrict G T Z)).graph (sideEdge hG hT Z e)
      (sideNode hG hT Z ⟨_, e.2.1⟩) (sideNode hG hT Z ⟨_, e.2.2⟩) ∧
    ((suppress (restrict G T Z)).IsDirected (sideEdge hG hT Z e) ↔ G.IsDirected e.1) ∧
    (G.IsDirected e.1 → (suppress (restrict G T Z)).graph.source (sideEdge hG hT Z e) =
      sideNode hG hT Z ⟨_, e.2.1⟩ ∧ (suppress (restrict G T Z)).graph.target (sideEdge hG hT Z e) =
      sideNode hG hT Z ⟨_, e.2.2⟩) := by
  set r₁ : ChainRep (restrict G T Z) ∅ (sideEdge hG hT Z e).1 :=
    ⟨1, _, _, isChainOf_single hG hT Z e, by ext g; simp [sideEdge]⟩
  have hnb : ¬ r₁.PointsBackward := by
    rintro ⟨⟨i, hi⟩, hb⟩
    have := hb i hi
    fin_cases i
    exact hG.loopless e.1 (congrArg Subtype.val this).symm
  have hsrc : r₁.src = ⟨G.graph.source e.1, mem_keptNodes_of_side hG hT Z e.2.1⟩ := by
    unfold ChainRep.src
    split_ifs
    rfl
  have htgt : r₁.tgt = ⟨G.graph.target e.1, mem_keptNodes_of_side hG hT Z e.2.2⟩ := by
    unfold ChainRep.tgt
    split_ifs
    rfl
  have hdir : r₁.PointsForward ∨ r₁.PointsBackward ↔ G.IsDirected e.1 := by
    constructor
    · rintro (⟨⟨i, hi⟩, -⟩ | ⟨⟨i, hi⟩, -⟩) <;> fin_cases i <;> exact hi
    · intro hd
      exact Or.inl ⟨⟨0, hd⟩, fun i _ => by fin_cases i; rfl⟩
  refine ⟨?_, (suppressExcept_isDirected_iff _ r₁).trans hdir, fun hd => ?_⟩
  · rcases suppressExcept_ends (sideEdge hG hT Z e).2 r₁ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨Subtype.ext (h₁.trans hsrc), Subtype.ext (h₂.trans htgt)⟩
    · exact Or.inr ⟨Subtype.ext (h₁.trans htgt), Subtype.ext (h₂.trans hsrc)⟩
  · have := suppressExcept_ends_of_directed (sideEdge hG hT Z e).2 r₁ (hdir.mpr hd)
    exact ⟨Subtype.ext (this.1.trans hsrc), Subtype.ext (this.2.trans htgt)⟩

omit hG hT [Finite E] in
/-- A chain can be read from either of its ends in the suppressed network. -/
theorem exists_chainRep_head {W F X' : Type*} {K : SemidirectedNetwork W F X'}
    (c : {c // IsChain K ∅ c}) {w : W}
    (hw : ((suppress K).graph.source c).1 = w ∨ ((suppress K).graph.target c).1 = w) :
    ∃ r : ChainRep K ∅ c.1, r.p 0 = w := by
  rcases suppress_ends_val c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hw with hw | hw
  · exact ⟨chainRep K ∅ c.2, h₁.symm.trans hw⟩
  · exact ⟨(chainRep K ∅ c.2).reverse, by
      change (chainRep K ∅ c.2).p (Fin.rev 0) = w
      rw [Fin.rev_zero, ← h₂, hw]⟩
  · exact ⟨(chainRep K ∅ c.2).reverse, by
      change (chainRep K ∅ c.2).p (Fin.rev 0) = w
      rw [Fin.rev_zero, ← h₁, hw]⟩
  · exact ⟨chainRep K ∅ c.2, h₂.symm.trans hw⟩

/-- **An edge of the suppressed restriction at a node of the side** is the edge through `f`, or an
edge of the side. -/
theorem eq_sideEdge_of_incident (c : {c : Set T // IsChain (restrict G T Z) ∅ c})
    (x : ↥(cutSide G.graph f y))
    (hx : (suppress (restrict G T Z)).graph.source c = sideNode hG hT Z x ∨
      (suppress (restrict G T Z)).graph.target c = sideNode hG hT Z x) :
    (∃ g ∈ c.1, g.1 = f) ∨ ∃ e, c = sideEdge hG hT Z e := by
  obtain ⟨r, hr0⟩ := exists_chainRep_head c (w := (sideNode hG hT Z x).1)
    (hx.imp (congrArg Subtype.val) (congrArg Subtype.val))
  have hk := r.isChainOf.pos
  set g := r.e ⟨0, hk⟩
  have hgc : g ∈ c.1 := (Set.ext_iff.1 r.range_eq g).1 ⟨_, rfl⟩
  by_cases hgf : g.1 = f
  · exact Or.inl ⟨g, hgc, hgf⟩
  right
  have hj0 := r.isChainOf.joins ⟨0, hk⟩
  have h0 : (⟨0, hk⟩ : Fin r.k).castSucc = 0 := rfl
  rw [h0, hr0] at hj0
  -- the other end of `g` is on the side, so is kept: the chain is `g` alone
  have hx' : x.1 ∈ cutSide G.graph f y := x.2
  have hother : ((r.p (⟨0, hk⟩ : Fin r.k).succ).1) ∈ cutSide G.graph f y := by
    refine Relation.ReflTransGen.tail hx' ⟨g.1, hgf, ?_⟩
    rcases hj0 with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
    · exact Or.inl ⟨congrArg Subtype.val k₁, congrArg Subtype.val k₂⟩
    · exact Or.inr ⟨congrArg Subtype.val k₁, congrArg Subtype.val k₂⟩
  have hb1 : IsBranch (restrict G T Z) ∅ (r.p (⟨0, hk⟩ : Fin r.k).succ) :=
    isBranch_restrict_of_side hG hT Z hother
  rw [r.isChainOf.isBranch_iff] at hb1
  have hk1 : r.k = 1 := by
    rcases hb1 with h | h
    · exact absurd h (Fin.succ_ne_zero _)
    · have := congrArg Fin.val h
      simp at this
      omega
  have hgS : G.graph.source g.1 ∈ cutSide G.graph f y ∧
      G.graph.target g.1 ∈ cutSide G.graph f y := by
    rcases hj0 with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
    · have e₁ : G.graph.source g.1 = x.1 := congrArg Subtype.val k₁
      have e₂ : G.graph.target g.1 = (r.p (⟨0, hk⟩ : Fin r.k).succ).1 := congrArg Subtype.val k₂
      rw [e₁, e₂]
      exact ⟨hx', hother⟩
    · have e₁ : G.graph.source g.1 = (r.p (⟨0, hk⟩ : Fin r.k).succ).1 := congrArg Subtype.val k₁
      have e₂ : G.graph.target g.1 = x.1 := congrArg Subtype.val k₂
      rw [e₁, e₂]
      exact ⟨hother, hx'⟩
  refine ⟨⟨g.1, hgS⟩, Subtype.ext ?_⟩
  rw [← r.range_eq]
  ext g'
  simp only [sideEdge, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    have : i = ⟨0, hk⟩ := Fin.ext (by have := i.2; omega)
    rw [this]
  · rintro rfl
    exact ⟨⟨0, hk⟩, rfl⟩

omit [Finite E] hG hT in
/-- A walk of the restriction is a walk of the network. -/
theorem walks_val_of_restrict {F : Set T} {a b : keptNodes G T Z}
    (h : (restrict G T Z).graph.Walks F a b) : G.graph.Walks (Subtype.val '' F) a.1 b.1 := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨g, hg, hj⟩ := hst
    refine ih.tail ⟨g.1, ⟨g, hg, rfl⟩, ?_⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
    · exact Or.inr ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩

variable {y' : V} (hf : ∀ C, IsCycle G.graph C → f ∉ C) (hj : Joins G.graph f y y')
include hf hj

/-- **The chain of `f` in the restriction**, read from `y`: `f` first, its other end `y'`, and its
last node off the side of `y`. -/
theorem exists_chainRep_f {c₀ : Set T} (hc₀ : IsChain (restrict G T Z) ∅ c₀) {g₀ : T}
    (hg₀ : g₀ ∈ c₀) (hg₀f : g₀.1 = f) :
    ∃ r : ChainRep (restrict G T Z) ∅ c₀, r.p 0 = (sideNode hG hT Z ⟨y, .refl⟩).1 ∧
      (r.p (Fin.last r.k)).1 ∉ cutSide G.graph f y := by
  have hy : y ∈ cutSide G.graph f y := Relation.ReflTransGen.refl
  set yR := (sideNode hG hT Z ⟨y, hy⟩).1
  have hyb : IsBranch (restrict G T Z) ∅ yR := (sideNode hG hT Z ⟨y, hy⟩).2
  have hinc : (restrict G T Z).graph.source g₀ = yR ∨ (restrict G T Z).graph.target g₀ = yR := by
    rcases hj.incident_left with h | h
    · exact Or.inl (Subtype.ext ((congrArg G.graph.source hg₀f).trans h))
    · exact Or.inr (Subtype.ext ((congrArg G.graph.target hg₀f).trans h))
  -- `y` is an end of the chain
  have hend : ((suppress (restrict G T Z)).graph.source ⟨c₀, hc₀⟩).1 = yR ∨
      ((suppress (restrict G T Z)).graph.target ⟨c₀, hc₀⟩).1 = yR := by
    have hmem : yR ∈ chainEnds (restrict G T Z) ∅ c₀ := ⟨hyb, g₀, hg₀, hinc⟩
    have hce := (chainRep _ ∅ hc₀).isChainOf.chainEnds_eq
    rw [(chainRep _ ∅ hc₀).range_eq] at hce
    rw [hce] at hmem
    rcases suppress_ends_val ⟨c₀, hc₀⟩ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hmem with h | h
    · exact Or.inl (h₁.trans h.symm)
    · exact Or.inr (h₂.trans (Set.mem_singleton_iff.mp h).symm)
    · exact Or.inr (h₂.trans h.symm)
    · exact Or.inl (h₁.trans (Set.mem_singleton_iff.mp h).symm)
  obtain ⟨r, hr0⟩ := exists_chainRep_head ⟨c₀, hc₀⟩ hend
  refine ⟨r, hr0, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, r.e i = g₀ := (Set.ext_iff.1 r.range_eq g₀).2 hg₀
  have hk := r.isChainOf.pos
  -- the edges of the chain other than `f`
  have hwalk : ∀ a b : Fin (r.k + 1), a ≤ b → ((i : ℕ) < a ∨ (b : ℕ) ≤ i) →
      G.graph.Walks {f}ᶜ (r.p a).1 (r.p b).1 := by
    intro a b hab hi'
    refine walks_mono ?_ (walks_val_of_restrict Z (walks_of_joins_le r.isChainOf.joins hab))
    rintro _ ⟨g, ⟨l, hl₁, hl₂, rfl⟩, rfl⟩ h
    have hl : r.e l = g₀ := Subtype.ext ((Set.mem_singleton_iff.mp h).trans hg₀f.symm)
    have := r.isChainOf.injective_edge (hl.trans hi.symm)
    subst this
    omega
  have hj0 := r.isChainOf.joins i
  rw [hi] at hj0
  -- `f` is the first edge
  have hi0 : (i : ℕ) = 0 := by
    rcases r.isChainOf.val_of_incident hyb (hi ▸ hinc) with ⟨-, h⟩ | ⟨hl, h⟩
    · exact h
    · by_contra hne
      -- the chain would close a cycle through `f`
      have hw := hwalk 0 i.castSucc (Fin.zero_le _) (Or.inr (by simp))
      rw [hr0] at hw
      have hl' : r.p i.succ = yR := by
        rw [hl]
        congr 1
        exact Fin.ext (by simp; omega)
      rw [hl'] at hj0
      have hjf : Joins G.graph f (r.p i.castSucc).1 y := by
        rcases hj0 with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
        · exact Or.inl ⟨hg₀f ▸ congrArg Subtype.val k₁, hg₀f ▸ congrArg Subtype.val k₂⟩
        · exact Or.inr ⟨hg₀f ▸ congrArg Subtype.val k₁, hg₀f ▸ congrArg Subtype.val k₂⟩
      exact not_walks_of_joins hf hjf (G.graph.walks_symm hw)
  -- its other end is `y'`, and the rest of the chain is on the side of `y'`
  have hc0 : i.castSucc = 0 := Fin.ext (by simpa using hi0)
  rw [hc0, hr0] at hj0
  have hjf : Joins G.graph f y (r.p i.succ).1 := by
    rcases hj0 with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
    · exact Or.inl ⟨hg₀f ▸ congrArg Subtype.val k₁, hg₀f ▸ congrArg Subtype.val k₂⟩
    · exact Or.inr ⟨hg₀f ▸ congrArg Subtype.val k₁, hg₀f ▸ congrArg Subtype.val k₂⟩
  have hy' : (r.p i.succ).1 = y' := Joins.eq_right hjf hj
  have hw := hwalk i.succ (Fin.last r.k) (Fin.le_last _) (Or.inl (by simp))
  rw [hy'] at hw
  exact (mem_cutSide_iff_notMem hG.connected hf hj _).mp hw

omit [Finite E] hG hT hf hj in
/-- An edge of a suppressed network joins the first and last nodes of any order on its chain. -/
theorem joins_suppress_of_chainRep {W F X' : Type*} [Finite F] {K : SemidirectedNetwork W F X'}
    {c : Set F} (hc : IsChain K ∅ c) (r : ChainRep K ∅ c) :
    Joins (suppress K).graph ⟨c, hc⟩ ⟨r.p 0, r.isChainOf.ends.1⟩
      ⟨r.p (Fin.last r.k), r.isChainOf.ends.2⟩ := by
  have hsrc : r.src = r.p 0 ∧ r.tgt = r.p (Fin.last r.k) ∨
      r.src = r.p (Fin.last r.k) ∧ r.tgt = r.p 0 := by
    unfold ChainRep.src ChainRep.tgt
    split_ifs
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  rcases suppressExcept_ends hc r with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rcases hsrc with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
  · exact Or.inl ⟨Subtype.ext (h₁.trans k₁), Subtype.ext (h₂.trans k₂)⟩
  · exact Or.inr ⟨Subtype.ext (h₁.trans k₁), Subtype.ext (h₂.trans k₂)⟩
  · exact Or.inr ⟨Subtype.ext (h₁.trans k₂), Subtype.ext (h₂.trans k₁)⟩
  · exact Or.inl ⟨Subtype.ext (h₁.trans k₂), Subtype.ext (h₂.trans k₁)⟩

/-- **The side of `y` of `G` is a side of `G` restricted to edges containing those at the side,
with the nodes of degree two suppressed**: the edge through `f` lies on no cycle, the taxa on its
other side are `z₀` alone, and the two sides of `y`, with their pendant edges, are isomorphic. -/
theorem exists_halfNet_restrict {z₀ : X} (hz₀ : G.leaf z₀ ∉ cutSide G.graph f y)
    (hZ : ∀ x, x ∈ Z ↔ G.leaf x ∈ cutSide G.graph f y ∨ x = z₀)
    (hfc : ∃ c, IsChain (restrict G T Z) ∅ c ∧ ∃ g ∈ c, g.1 = f)
    (hHc : (suppress (restrict G T Z)).graph.IsConnected) :
    ∃ fH yH yH', (∀ C, IsCycle (suppress (restrict G T Z)).graph C → fH ∉ C) ∧
      Joins (suppress (restrict G T Z)).graph fH yH yH' ∧
      (∀ z, (suppress (restrict G T Z)).leaf z ∈
        cutSide (suppress (restrict G T Z)).graph fH yH' ↔ z.1 = z₀) ∧
      Nonempty (SDIso (halfNet (suppress (restrict G T Z)) fH yH id)
        (halfNet G f y (Subtype.val : Z → X))) := by
  classical
  set H := suppress (restrict G T Z) with hH
  obtain ⟨c₀, hc₀, g₀, hg₀, hg₀f⟩ := hfc
  obtain ⟨r, hr0, hlast⟩ := exists_chainRep_f hG hT Z hf hj hc₀ hg₀ hg₀f
  have hy : y ∈ cutSide G.graph f y := Relation.ReflTransGen.refl
  set fH : {c // IsChain (restrict G T Z) ∅ c} := ⟨c₀, hc₀⟩
  set yH := sideNode hG hT Z ⟨y, hy⟩
  set yH' : {u // IsBranch (restrict G T Z) ∅ u} := ⟨r.p (Fin.last r.k), r.isChainOf.ends.2⟩
  have hjH : Joins H.graph fH yH yH' := by
    have := joins_suppress_of_chainRep hc₀ r
    have h0 : (⟨r.p 0, r.isChainOf.ends.1⟩ : {u // IsBranch (restrict G T Z) ∅ u}) = yH :=
      Subtype.ext hr0
    rwa [h0] at this
  have hne : ∀ e, sideEdge hG hT Z e ≠ fH := by
    intro e h
    have : g₀ ∈ (sideEdge hG hT Z e).1 := by rw [h]; exact hg₀
    simp only [sideEdge, Set.mem_singleton_iff] at this
    have hf' := ne_of_mem_side (K := G) (S := cutSide G.graph f y) (a := ⟨y, hy⟩) hj
      (y'_notMem_cutSide hG.connected hf hj) e
    exact hf' ((congrArg Subtype.val this).symm.trans hg₀f)
  -- the side of `yH` is the image of the side of `y`
  have hside : ∀ w, w ∈ cutSide H.graph fH yH ↔ ∃ x, w = sideNode hG hT Z x := by
    intro w
    constructor
    · intro hw
      change H.graph.Walks {fH}ᶜ yH w at hw
      induction hw with
      | refl => exact ⟨_, rfl⟩
      | @tail a b _ hab ih =>
        obtain ⟨x, rfl⟩ := ih
        obtain ⟨c, hcf, hcj⟩ := hab
        have hcj' : Joins H.graph c (sideNode hG hT Z x) b := hcj
        rcases eq_sideEdge_of_incident hG hT Z c x hcj'.incident_left with
          ⟨g, hg, hgf⟩ | ⟨e, rfl⟩
        · have hgg : g = g₀ := Subtype.ext (hgf.trans hg₀f.symm)
          exact absurd (Subtype.ext (c.2.eq_of_mem hc₀ hg (hgg ▸ hg₀))) hcf
        · have hJ : Joins H.graph (sideEdge hG hT Z e) (sideNode hG hT Z ⟨_, e.2.1⟩)
              (sideNode hG hT Z ⟨_, e.2.2⟩) := (sideEdge_spec hG hT Z e).1
          rcases hJ.eq_or_eq hcj'.incident_right with h | h
          · exact ⟨_, h⟩
          · exact ⟨_, h⟩
    · rintro ⟨x, rfl⟩
      suffices key : ∀ v (hv : G.graph.Walks {f}ᶜ y v),
          sideNode hG hT Z ⟨v, hv⟩ ∈ cutSide H.graph fH yH from key x.1 x.2
      intro v hv
      induction hv with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b hya hab ih =>
        obtain ⟨g, hgf, hgj⟩ := hab
        have hyb : G.graph.Walks {f}ᶜ y b := hya.tail ⟨g, hgf, hgj⟩
        have hgS : G.graph.source g ∈ cutSide G.graph f y ∧
            G.graph.target g ∈ cutSide G.graph f y := by
          rcases hgj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact ⟨h₁ ▸ hya, h₂ ▸ hyb⟩
          · exact ⟨h₁ ▸ hyb, h₂ ▸ hya⟩
        have hJ := (sideEdge_spec hG hT Z ⟨g, hgS⟩).1
        refine Relation.ReflTransGen.tail ih ⟨sideEdge hG hT Z ⟨g, hgS⟩, hne _, ?_⟩
        rcases hgj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · have e₁ : sideNode hG hT Z ⟨G.graph.source g, hgS.1⟩ = sideNode hG hT Z ⟨a, hya⟩ :=
            congrArg _ (Subtype.ext h₁)
          have e₂ : sideNode hG hT Z ⟨G.graph.target g, hgS.2⟩ = sideNode hG hT Z ⟨b, hyb⟩ :=
            congrArg _ (Subtype.ext h₂)
          rw [e₁, e₂] at hJ
          exact hJ
        · have e₁ : sideNode hG hT Z ⟨G.graph.source g, hgS.1⟩ = sideNode hG hT Z ⟨b, hyb⟩ :=
            congrArg _ (Subtype.ext h₁)
          have e₂ : sideNode hG hT Z ⟨G.graph.target g, hgS.2⟩ = sideNode hG hT Z ⟨a, hya⟩ :=
            congrArg _ (Subtype.ext h₂)
          rw [e₁, e₂] at hJ
          exact Or.symm hJ
  have hyH' : yH' ∉ cutSide H.graph fH yH := by
    intro h
    obtain ⟨x, hx⟩ := (hside _).mp h
    have hv : (r.p (Fin.last r.k)).1 = x.1 := congrArg (fun w => w.1.1) hx
    exact hlast (by rw [hv]; exact x.2)
  -- `fH` lies on no cycle
  have hbr : ∀ C, IsCycle H.graph C → fH ∉ C := by
    intro C hC hfC
    have hw := walks_mono (F := C \ {fH}) (F' := {fH}ᶜ) (fun g hg => hg.2)
      (hC.walks_diff_singleton hfC)
    rcases hjH with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at hw
      exact hyH' (H.graph.walks_symm hw)
    · rw [h₁, h₂] at hw
      exact hyH' hw
  -- the taxa
  have hleafS : ∀ z, H.leaf z ∈ cutSide H.graph fH yH ↔ G.leaf z.1 ∈ cutSide G.graph f y := by
    intro z
    rw [hside]
    constructor
    · rintro ⟨x, hx⟩
      have hv : G.leaf z.1 = x.1 := congrArg (fun w => w.1.1) hx
      rw [hv]
      exact x.2
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
  have hleaves : ∀ z, H.leaf z ∈ cutSide H.graph fH yH' ↔ z.1 = z₀ := by
    intro z
    rw [mem_cutSide_iff_notMem hHc hbr hjH, hleafS]
    constructor
    · intro h
      exact ((hZ z.1).mp z.2).resolve_left h
    · intro h
      rw [h]
      exact hz₀
  refine ⟨fH, yH, yH', hbr, hjH, hleaves, ?_⟩
  -- the isomorphism of the two sides
  have hxof : ∀ w ∈ cutSide H.graph fH yH, w.1.1 ∈ cutSide G.graph f y := fun w hw => by
    obtain ⟨x, rfl⟩ := (hside w).mp hw
    exact x.2
  have hcof : ∀ c : {c // IsChain (restrict G T Z) ∅ c}, H.graph.source c ∈ cutSide H.graph fH yH →
      H.graph.target c ∈ cutSide H.graph fH yH → ∃ e, c = sideEdge hG hT Z e := by
    intro c h₁ h₂
    obtain ⟨x, hx⟩ := (hside _).mp h₁
    rcases eq_sideEdge_of_incident hG hT Z c x (Or.inl hx) with ⟨g, hg, hgf⟩ | h
    · have hgg : g = g₀ := Subtype.ext (hgf.trans hg₀f.symm)
      have hc : c = fH := Subtype.ext (c.2.eq_of_mem hc₀ hg (hgg ▸ hg₀))
      subst hc
      rcases hjH with ⟨-, k₂⟩ | ⟨k₁, -⟩
      · exact absurd (k₂ ▸ h₂) hyH'
      · exact absurd (k₁ ▸ h₁) hyH'
    · exact h
  have hsideE : ∀ e, H.graph.source (sideEdge hG hT Z e) ∈ cutSide H.graph fH yH ∧
      H.graph.target (sideEdge hG hT Z e) ∈ cutSide H.graph fH yH := by
    intro e
    have hJ := (sideEdge_spec hG hT Z e).1
    rcases hJ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;>
      exact ⟨(hside _).mpr ⟨_, rfl⟩, (hside _).mpr ⟨_, rfl⟩⟩
  have hsideE_inj : ∀ e e', sideEdge hG hT Z e = sideEdge hG hT Z e' → e = e' := by
    intro e e' h
    have := congrArg Subtype.val h
    simp only [sideEdge, Set.singleton_eq_singleton_iff, Subtype.mk.injEq] at this
    exact Subtype.ext this
  let vert : ↥(cutSide H.graph fH yH) ⊕ Unit ≃ ↥(cutSide G.graph f y) ⊕ Unit :=
    { toFun := fun w => match w with
        | .inl w => .inl ⟨w.1.1.1, hxof w.1 w.2⟩
        | .inr _ => .inr ()
      invFun := fun x => match x with
        | .inl x => .inl ⟨sideNode hG hT Z x, (hside _).mpr ⟨x, rfl⟩⟩
        | .inr _ => .inr ()
      left_inv := by rintro (w | u) <;> rfl
      right_inv := by rintro (x | u) <;> rfl }
  let edge : {c // H.graph.source c ∈ cutSide H.graph fH yH ∧
      H.graph.target c ∈ cutSide H.graph fH yH} ⊕ Unit ≃
      {e // G.graph.source e ∈ cutSide G.graph f y ∧ G.graph.target e ∈ cutSide G.graph f y} ⊕
        Unit :=
    { toFun := fun c => match c with
        | .inl c => .inl (hcof c.1 c.2.1 c.2.2).choose
        | .inr _ => .inr ()
      invFun := fun e => match e with
        | .inl e => .inl ⟨sideEdge hG hT Z e, hsideE e⟩
        | .inr _ => .inr ()
      left_inv := by
        rintro (c | u)
        · exact congrArg Sum.inl (Subtype.ext (hcof c.1 c.2.1 c.2.2).choose_spec.symm)
        · rfl
      right_inv := by
        rintro (e | u)
        · exact congrArg Sum.inl (hsideE_inj _ _
            (hcof (sideEdge hG hT Z e) (hsideE e).1 (hsideE e).2).choose_spec).symm
        · rfl }
  have hedge : ∀ c : {c // H.graph.source c ∈ cutSide H.graph fH yH ∧
      H.graph.target c ∈ cutSide H.graph fH yH}, ∃ e, c.1 = sideEdge hG hT Z e ∧
        edge (.inl c) = .inl e := fun c =>
    ⟨_, (hcof c.1 c.2.1 c.2.2).choose_spec, rfl⟩
  refine ⟨{ vert := vert
            edge := edge
            isDirected_iff := fun c => ?_
            joins := fun c => ?_
            directed := fun c hd => ?_
            leaf := fun z => ?_ }⟩
  · rcases c with c | u
    · obtain ⟨e, hce, he⟩ := hedge c
      rw [he]
      change G.IsDirected e.1 ↔ H.IsDirected c.1
      rw [hce]
      exact (sideEdge_spec hG hT Z e).2.1.symm
    · exact Iff.rfl
  · rcases c with c | u
    · obtain ⟨e, hce, he⟩ := hedge c
      rw [he]
      have hJ := (sideEdge_spec hG hT Z e).1
      rw [← hce] at hJ
      have hs : vert ((halfNet H fH yH id).graph.source (.inl c)) =
          (.inl ⟨(H.graph.source c.1).1.1, hxof _ c.2.1⟩ : ↥(cutSide G.graph f y) ⊕ Unit) := rfl
      have ht : vert ((halfNet H fH yH id).graph.target (.inl c)) =
          (.inl ⟨(H.graph.target c.1).1.1, hxof _ c.2.2⟩ : ↥(cutSide G.graph f y) ⊕ Unit) := rfl
      rw [hs, ht]
      rcases hJ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have v₁ : (H.graph.source c.1).1.1 = G.graph.source e.1 := by rw [h₁]; rfl
        have v₂ : (H.graph.target c.1).1.1 = G.graph.target e.1 := by rw [h₂]; rfl
        exact Or.inl ⟨congrArg Sum.inl (Subtype.ext v₁.symm),
          congrArg Sum.inl (Subtype.ext v₂.symm)⟩
      · have v₁ : (H.graph.source c.1).1.1 = G.graph.target e.1 := by rw [h₁]; rfl
        have v₂ : (H.graph.target c.1).1.1 = G.graph.source e.1 := by rw [h₂]; rfl
        exact Or.inr ⟨congrArg Sum.inl (Subtype.ext v₂.symm),
          congrArg Sum.inl (Subtype.ext v₁.symm)⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases c with c | u
    · obtain ⟨e, hce, he⟩ := hedge c
      rw [he]
      have hd' : H.IsDirected (sideEdge hG hT Z e) := hce ▸ hd
      have hS := (sideEdge_spec hG hT Z e).2.2 ((sideEdge_spec hG hT Z e).2.1.mp hd')
      rw [← hce] at hS
      have hs : vert ((halfNet H fH yH id).graph.source (.inl c)) =
          (.inl ⟨(H.graph.source c.1).1.1, hxof _ c.2.1⟩ : ↥(cutSide G.graph f y) ⊕ Unit) := rfl
      have ht : vert ((halfNet H fH yH id).graph.target (.inl c)) =
          (.inl ⟨(H.graph.target c.1).1.1, hxof _ c.2.2⟩ : ↥(cutSide G.graph f y) ⊕ Unit) := rfl
      rw [hs, ht]
      have v₁ : (H.graph.source c.1).1.1 = G.graph.source e.1 := by rw [hS.1]; rfl
      have v₂ : (H.graph.target c.1).1.1 = G.graph.target e.1 := by rw [hS.2]; rfl
      exact ⟨congrArg Sum.inl (Subtype.ext v₁.symm), congrArg Sum.inl (Subtype.ext v₂.symm)⟩
    · exact hd.elim
  · by_cases h : G.leaf z.1 ∈ cutSide G.graph f y
    · have h' : H.leaf (id z) ∈ cutSide H.graph fH yH := (hleafS z).mpr h
      rw [pendantSide_leaf_of_mem h, pendantSide_leaf_of_mem h']
      rfl
    · have h' : H.leaf (id z) ∉ cutSide H.graph fH yH := fun h'' => h ((hleafS z).mp h'')
      rw [pendantSide_leaf_of_notMem h, pendantSide_leaf_of_notMem h']
      rfl

end RestrictSide




end Cut

section RootedPaths

variable {V E X : Type*} {N : RootedNetwork V E X}

/-- A path whose nodes are all other than `x` avoids `x`. -/
theorem reflTransGen_avoid_of_reaches {u v x : V} (h : N.graph.Reaches u v)
    (hx : ∀ w, N.graph.Reaches u w → N.graph.Reaches w v → w ≠ x) :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ x ∧ b ≠ x) u v := by
  induction h with
  | refl => exact .refl
  | @tail a b hua hab ih =>
    refine (ih fun w h₁ h₂ => hx w h₁ (h₂.tail hab)).tail ⟨hab, hx a hua (.single hab), hx b
      (hua.tail hab) .refl⟩

/-- A path avoiding a node, from `u`, either avoids the arc `e` or reaches its source avoiding the
node. -/
theorem reflTransGen_avoid_source_or_avoidingReach {u v x : V} {e : E}
    (h : Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ x ∧ b ≠ x) u v) :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ x ∧ b ≠ x) u (N.graph.source e) ∨
      N.AvoidingReach e u v := by
  induction h with
  | refl => exact Or.inr .refl
  | @tail a b hua hab ih =>
    rcases ih with ih | ih
    · exact Or.inl ih
    · obtain ⟨⟨g, hgs, hgt⟩, -, -⟩ := hab
      by_cases hge : g = e
      · subst hge
        exact Or.inl (hgs ▸ hua)
      · exact Or.inr (ih.tail ⟨g, hge, hgs, hgt⟩)

end RootedPaths

section Induced

variable {V E X : Type*} [Finite V] [Finite E] {N : RootedNetwork V E X}
  (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X)

omit [Finite V] [Finite E] in
/-- **`(N⁻)_Z` is `(N⊕_Z)⁻`**, up to isomorphism: Proposition 1 gives `(N⁻)_Z ≅ (N⁺_Z)⁻`, and
`(N⁺_Z)⁻ ≅ (N⊕_Z)⁻`. -/
theorem nonempty_sdIso_inducedUnrooted_unrooted_inducedLSA {Z : Set X} (hZ : Z.Nontrivial) :
    Nonempty (SDIso (inducedUnrooted (unrooted N hN hX) Z)
      (unrooted (inducedLSA N hN.1 Z hZ) (inducedLSA_isBinaryRootedNetwork hN hZ)
        hZ.coe_sort)) := by
  obtain ⟨p₁⟩ := proposition1 hN hX hZ
  obtain ⟨p₂⟩ := nonempty_sdIso_unrooted_inducedRooted hN hZ
  exact ⟨p₁.trans p₂⟩

include h1 in
/-- `(N⁻)_Z` has the properties of `IsUnrootedLevelOne`, being isomorphic to `(N⊕_Z)⁻`. -/
theorem isUnrootedLevelOne_inducedUnrooted {Z : Set X} (hZ : Z.Nontrivial) :
    IsUnrootedLevelOne (inducedUnrooted (unrooted N hN hX) Z) := by
  obtain ⟨ι⟩ := nonempty_sdIso_inducedUnrooted_unrooted_inducedLSA hN hX hZ
  have h1M : IsLevelOne (inducedLSA N hN.1 Z hZ).graph :=
    isLevelOne_suppress (lsaNetwork_isPhylogenetic hN.1 hZ) (isLevelOne_belowNetwork h1)
  exact (isUnrootedLevelOne_unrooted (inducedLSA_isBinaryRootedNetwork hN hZ) h1M
    hZ.coe_sort).of_sdIso ι.symm

include h1 in
/-- **The edges of `N⁻` at the side of `y` lie on simple treks between taxa of `Z`**, when `Z` is
the set of taxa on the side of `y` of an edge `f` on no cycle, and one taxon `z₀` on the other side.
By Lemma 17 these are the arcs of `N` below `LSA(Z)` above a taxon of `Z`. An edge at the side of
`y` is above a taxon of the side of `y`, or above the arc of `f`, which is above `z₀`. When the side
of `y` is the side of the source of the arc of `f`, `LSA(Z)` is `LSA(X)`: a path from the root to
another taxon passes the arc of `f`, from which it can go on to `z₀`. When it is the side of its
target, `LSA(Z)` is above the arc of `f`, and above the source of every arc at the side of `y`: else
the target of that arc would reach the source of `f`, joining the two sides. -/
theorem mem_trekEdges_of_side {f : SemidirectedArc hN.1 hN.2 hX}
    (hf : ∀ C, IsCycle (unrooted N hN hX).graph C → f ∉ C) {y y' : SemidirectedVertex hN.1 hX}
    (hj : Joins (unrooted N hN hX).graph f y y') {Z : Set X} {z₀ : X}
    (hz₀ : (unrooted N hN hX).leaf z₀ ∉ cutSide (unrooted N hN hX).graph f y)
    (hZ : ∀ x, x ∈ Z ↔ (unrooted N hN hX).leaf x ∈ cutSide (unrooted N hN hX).graph f y ∨ x = z₀)
    (g : SemidirectedArc hN.1 hN.2 hX)
    (hg : (unrooted N hN hX).graph.source g ∈ cutSide (unrooted N hN hX).graph f y ∨
      (unrooted N hN hX).graph.target g ∈ cutSide (unrooted N hN hX).graph f y) :
    g ∈ trekEdges (unrooted N hN hX) Z := by
  classical
  set G := unrooted N hN hX with hG_def
  have hG := isUnrootedLevelOne_unrooted hN h1 hX
  have hconn := unrooted_isConnected hN hX
  have hzZ : z₀ ∈ Z := (hZ z₀).mpr (Or.inr rfl)
  have hZne : Z.Nonempty := ⟨z₀, hzZ⟩
  rw [mem_trekEdges_iff hN hX hZne (fun _ he hd => lemma17 hN hZne he hd) g]
  set e₀ := f.1.1 with he₀
  have hb := not_walks_of_forall_notMem hf
  have hsep := unrooted_separates hN f hb
  -- the taxa on the side of the target of `f` are those below its arc
  have hTS : ∀ x, G.graph.Walks {f}ᶜ (G.graph.target f) (G.leaf x) ↔
      N.graph.Reaches (N.graph.target e₀) (N.leaf x) := fun x =>
    ⟨fun h => Dominates.isBelow hN.1 (hsep.1 x h), fun h => by
      by_contra h'
      exact hsep.2 x h' h⟩
  have hy : y ∈ cutSide G.graph f y := Relation.ReflTransGen.refl
  have hcut := mem_cutSide_iff_notMem hconn hf hj
  have hy'z : G.leaf z₀ ∈ cutSide G.graph f y' := (hcut _).mpr hz₀
  -- a taxon of the side of `y`
  obtain ⟨x₁, hx₁⟩ := hG.exists_leaf_side f hf y hj.incident_left
  have hx₁Z : x₁ ∈ Z := (hZ x₁).mpr (Or.inl hx₁)
  -- the arc of `g` is above a taxon of `Z`
  have hanc : ∃ z ∈ Z, N.graph.Reaches (N.graph.target g.1.1) (N.leaf z) := by
    obtain ⟨x, hx⟩ := Phylogenetics.RootedNetwork.exists_reaches_leaf hN.1 (N.graph.target g.1.1)
    by_cases hav : N.AvoidingReach e₀ (N.graph.target g.1.1) (N.leaf x)
    · obtain ⟨w', hw'x, hw'⟩ := unrooted_walks_of_avoidingReach hN f (G.graph.target g) hav
      have hw'' : w' = G.leaf x := unrooted_node_ext hw'x
      subst hw''
      by_cases hgA : G.graph.target g ∈ cutSide G.graph f y
      · exact ⟨x, (hZ x).mpr (Or.inl (Relation.ReflTransGen.trans hgA hw')), hx⟩
      · have hgf : g = f := by
          by_contra hgf
          exact hgA (Relation.ReflTransGen.tail (hg.resolve_right hgA) ⟨g, hgf, Or.inl ⟨rfl, rfl⟩⟩)
        subst hgf
        have hty' : G.graph.target g = y' :=
          (hj.eq_or_eq (Or.inr rfl)).resolve_left fun h => hgA (h ▸ hy)
        refine ⟨z₀, hzZ, (hTS z₀).mp ?_⟩
        rw [hty']
        exact hy'z
    · have ht₀x := target_reaches_of_not_avoidingReach hx hav
      have hts₀ := reaches_source_of_not_avoidingReach hx hav
      by_cases hz : N.graph.Reaches (N.graph.target e₀) (N.leaf z₀)
      · exact ⟨z₀, hzZ, hts₀.trans ((Relation.ReflTransGen.single ⟨e₀, rfl, rfl⟩).trans hz)⟩
      · refine ⟨x, (hZ x).mpr (Or.inl ?_), hx⟩
        have hyt : G.graph.target f = y := by
          rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exfalso
            apply hz
            apply (hTS z₀).mp
            rw [h₂]
            exact hy'z
          · exact h₂
        have := (hTS x).mpr ht₀x
        rwa [hyt] at this
  refine ⟨?_, hanc⟩
  obtain ⟨hst, hleast⟩ := lsa_spec hN.1 Z hZne
  set mZ := lsa hN.1 Z hZne
  set m := lsa hN.1 Set.univ Set.univ_nonempty
  have hgm : N.graph.Reaches m (N.graph.source g.1.1) := g.1.2.1
  rcases hj with ⟨hsy, hty'⟩ | ⟨hsy', hty⟩
  · -- the side of `y` is that of the source of `f`: `LSA(Z)` is `LSA(X)`
    have hmmZ : N.graph.Reaches m mZ := hleast m fun x _ =>
      (lsa_spec hN.1 Set.univ Set.univ_nonempty).1 x (Set.mem_univ x)
    have hTS' : ∀ x, G.leaf x ∈ cutSide G.graph f y' ↔
        N.graph.Reaches (N.graph.target e₀) (N.leaf x) := fun x => by
      rw [← hty']
      exact hTS x
    have hnot : ∀ w, N.graph.Reaches (N.graph.target e₀) w → w ≠ mZ := by
      rintro w hw rfl
      exact (hcut _).mp ((hTS' x₁).mpr (hw.trans (hst.reaches_leaf hN.1 hx₁Z))) hx₁
    have hstX : N.IsStableAncestor Set.univ mZ := by
      intro x _ hpa
      by_cases hxZ : x ∈ Z
      · exact hst x hxZ hpa
      · have hxT : G.graph.Walks {f}ᶜ (G.graph.target f) (G.leaf x) := by
          rw [hty']
          exact (hcut _).mpr fun h => hxZ ((hZ x).mpr (Or.inl h))
        obtain ⟨hr, -, hp⟩ := hpa
        rcases reflTransGen_avoid_source_or_avoidingReach (e := e₀) hp with hpre | hav
        · have hz₀T := (hTS' z₀).mp hy'z
          have hs₀ : N.graph.source e₀ ≠ mZ := by
            rcases Relation.ReflTransGen.cases_tail hpre with h | ⟨a, -, -, -, h⟩
            · rw [h]
              exact hr
            · exact h
          refine hst z₀ hzZ ⟨hr, hnot _ hz₀T, ?_⟩
          exact (hpre.tail ⟨⟨e₀, rfl, rfl⟩, hs₀, hnot _ .refl⟩).trans
            (reflTransGen_avoid_of_reaches hz₀T fun w h₁ _ => hnot w h₁)
        · exact hsep.1 x hxT hav
    have hmZ : mZ = m := eq_of_reaches_of_reaches hN.1.acyclic
      ((lsa_spec hN.1 Set.univ Set.univ_nonempty).2 mZ hstX) hmmZ
    rw [hmZ]
    exact hgm
  · -- the side of `y` is that of the target of `f`: `LSA(Z)` is above the source of `f`
    have hTSA : ∀ x, G.leaf x ∈ cutSide G.graph f y ↔
        N.graph.Reaches (N.graph.target e₀) (N.leaf x) := fun x => by
      rw [← hty]
      exact hTS x
    have hms₀ : N.graph.Reaches mZ (N.graph.source e₀) := by
      have hdom := hsep.1 x₁ (by rw [hty]; exact hx₁)
      rcases reaches_source_or_target_reaches_of_not_hasPathAvoiding (hN.1.root_reaches _) hdom
        (hst x₁ hx₁Z) with h | h
      · exact h
      · exact absurd ((hTSA z₀).mpr (h.trans (hst.reaches_leaf hN.1 hzZ))) hz₀
    obtain ⟨z, hz, hgz⟩ := hanc
    -- `LSA(Z)` is on every path from the root to `z` through the arc of `g`
    have hor : N.graph.Reaches mZ (N.graph.source g.1.1) ∨
        N.graph.Reaches (N.graph.target g.1.1) mZ := by
      by_contra hn
      push Not at hn
      obtain ⟨h₁, h₂⟩ := hn
      have hroot : N.root ≠ mZ := fun h => h₁ (h ▸ hN.1.root_reaches _)
      refine hst z hz ⟨hroot, fun h => h₂ (by rw [← h]; exact hgz), ?_⟩
      refine ((reflTransGen_avoid_of_reaches (hN.1.root_reaches (N.graph.source g.1.1))
        fun w _ hw h => h₁ (by rw [← h]; exact hw)).tail ⟨⟨g.1.1, rfl, rfl⟩,
          fun h => h₁ (by rw [← h]; exact .refl), fun h => h₂ (by rw [← h]; exact .refl)⟩).trans ?_
      exact reflTransGen_avoid_of_reaches hgz fun w hw _ h => h₂ (by rw [← h]; exact hw)
    rcases hor with h | h
    · exact h
    · -- the target of `g` would reach the source of `f`, joining the two sides
      exfalso
      have hts₀ := h.trans hms₀
      by_cases hs₀m : N.graph.source e₀ = m
      · exact hN.1.acyclic _ (Relation.TransGen.head' ⟨g.1.1, rfl, rfl⟩ (hts₀.trans (hs₀m ▸ hgm)))
      by_cases hgf : g = f
      · subst hgf
        exact hN.1.acyclic _ (Relation.TransGen.head' ⟨e₀, rfl, rfl⟩ hts₀)
      have hav : N.AvoidingReach e₀ (N.graph.target g.1.1) (N.graph.source e₀) :=
        avoidingReach_of_not_reaches_target hts₀ fun h' =>
          hN.1.acyclic _ (Relation.TransGen.head' ⟨e₀, rfl, rfl⟩ h')
      obtain ⟨w', hw's, hw'⟩ := unrooted_walks_of_avoidingReach hN f (G.graph.target g) hav
      have hw'' : w' = G.graph.source f :=
        unrooted_node_ext (hw's.trans (unrooted_source_val_of_ne hN f hs₀m).symm)
      subst hw''
      have hgA : G.graph.target g ∈ cutSide G.graph f y := by
        rcases hg with hA | hA
        · exact Relation.ReflTransGen.tail hA ⟨g, hgf, Or.inl ⟨rfl, rfl⟩⟩
        · exact hA
      rw [← hty] at hgA
      exact hb (G.graph.walks_symm (Relation.ReflTransGen.trans hgA hw'))

include h1 in
/-- **The side of `y` of `N⁻` is a side of `(N⁻)_Z`** when `Z` is the set of taxa on the side of `y`
of an edge `f` on no cycle, and one taxon `z₀` on the other side: the edges of `N⁻` at the nodes on
the side of `y` lie on simple treks between taxa of `Z`, and their nodes are kept by the
suppression. The edge of `(N⁻)_Z` through `f` lies on no cycle, the only taxon on its other side is
`z₀`, and the two sides of `y`, with their pendant edges, are isomorphic. -/
theorem exists_halfNet_inducedUnrooted {f : SemidirectedArc hN.1 hN.2 hX}
    (hf : ∀ C, IsCycle (unrooted N hN hX).graph C → f ∉ C) {y y' : SemidirectedVertex hN.1 hX}
    (hj : Joins (unrooted N hN hX).graph f y y') {Z : Set X} {z₀ : X}
    (hz₀ : (unrooted N hN hX).leaf z₀ ∉ cutSide (unrooted N hN hX).graph f y)
    (hZ : ∀ x, x ∈ Z ↔ (unrooted N hN hX).leaf x ∈ cutSide (unrooted N hN hX).graph f y ∨ x = z₀) :
    ∃ fH yH yH', (∀ C, IsCycle (inducedUnrooted (unrooted N hN hX) Z).graph C → fH ∉ C) ∧
      Joins (inducedUnrooted (unrooted N hN hX) Z).graph fH yH yH' ∧
      (∀ z, (inducedUnrooted (unrooted N hN hX) Z).leaf z ∈
        cutSide (inducedUnrooted (unrooted N hN hX) Z).graph fH yH' ↔ z.1 = z₀) ∧
      Nonempty (SDIso (halfNet (inducedUnrooted (unrooted N hN hX) Z) fH yH id)
        (halfNet (unrooted N hN hX) f y (Subtype.val : Z → X))) := by
  have hG := isUnrootedLevelOne_unrooted hN h1 hX
  have hT := mem_trekEdges_of_side hN h1 hX hf hj hz₀ hZ
  -- `Z` has two taxa: `z₀` and a taxon on the side of `y`
  obtain ⟨x, hx⟩ := hG.exists_leaf_side f hf y hj.incident_left
  have hZn : Z.Nontrivial := ⟨x, (hZ x).mpr (Or.inl hx), z₀, (hZ z₀).mpr (Or.inr rfl), by
    rintro rfl
    exact hz₀ hx⟩
  -- the edge `f` lies on a chain of the edges on simple treks
  have hy : y ∈ cutSide (unrooted N hN hX).graph f y := Relation.ReflTransGen.refl
  have hfT : f ∈ trekEdges (unrooted N hN hX) Z := hT f (by
    rcases hj.incident_left with h | h
    · exact Or.inl (h ▸ hy)
    · exact Or.inr (h ▸ hy))
  have h17 : Lemma17Conclusion hN Z hZn.nonempty := fun _ he hd => lemma17 hN hZn.nonempty he hd
  have hfc : ∃ c, IsChain (restrict (unrooted N hN hX) (trekEdges (unrooted N hN hX) Z) Z) ∅ c ∧
      ∃ g ∈ c, g.1 = f :=
    ⟨_, chainOfR_isChain hN hX hZn h17 (inducedRooted_isBinaryRootedNetwork hN hZn) Subtype.val
      Subtype.val (isContraction_contractRoot _ _) (psiR hN hX hZn h17
        (inducedRooted_isBinaryRootedNetwork hN hZn) Subtype.val Subtype.val
        (isContraction_contractRoot _ _) ⟨f, hfT⟩), ⟨f, hfT⟩,
      mem_chainOfR_psiR hN hX hZn h17 (inducedRooted_isBinaryRootedNetwork hN hZn) Subtype.val
        Subtype.val (isContraction_contractRoot _ _) ⟨f, hfT⟩, rfl⟩
  exact exists_halfNet_restrict hG hT Z hf hj hz₀ hZ hfc
    (isUnrootedLevelOne_inducedUnrooted hN h1 hX hZn).connected

include h1 in
/-- **`Ñ` of `(N⁻)_Z` is the side of `y` of `Ñ`**, with the edge `ε` through `f` as a pendant edge,
when `Z` is the set of taxa on the side of `y` of an edge `f` on no cycle, and one taxon `z₀` on the
other side. -/
theorem tilde_inducedUnrooted_sdIso_pendantSide {f : SemidirectedArc hN.1 hN.2 hX}
    (hf : ∀ C, IsCycle (unrooted N hN hX).graph C → f ∉ C) {y y' : SemidirectedVertex hN.1 hX}
    (hj : Joins (unrooted N hN hX).graph f y y')
    {ε : {c // IsChain (tildeContracted (unrooted N hN hX)) ∅ c}} (hεf : ∃ g ∈ ε.1, g.1 = f)
    {a : {u // IsBranch (tildeContracted (unrooted N hN hX)) ∅ u}}
    (ha : a ∈ tildeCutSide (unrooted N hN hX) f y)
    (haε : (tildeNetwork (unrooted N hN hX)).graph.source ε = a ∨
      (tildeNetwork (unrooted N hN hX)).graph.target ε = a) {Z : Set X} {z₀ : X}
    (hz₀ : (unrooted N hN hX).leaf z₀ ∉ cutSide (unrooted N hN hX).graph f y)
    (hZ : ∀ x, x ∈ Z ↔ (unrooted N hN hX).leaf x ∈ cutSide (unrooted N hN hX).graph f y ∨ x = z₀)
    (hZn : Z.Nontrivial) :
    Nonempty (SDIso (tildeNetwork (inducedUnrooted (unrooted N hN hX) Z))
      (pendantSide (tildeNetwork (unrooted N hN hX)) (tildeCutSide (unrooted N hN hX) f y) ⟨a, ha⟩
        (Subtype.val : Z → X))) := by
  have hG := isUnrootedLevelOne_unrooted hN h1 hX
  have hH := isUnrootedLevelOne_inducedUnrooted hN h1 hX hZn
  obtain ⟨fH, yH, yH', hfH, hjH, hzH, ⟨σ⟩⟩ := exists_halfNet_inducedUnrooted hN h1 hX hf hj hz₀ hZ
  obtain ⟨εH, aH, bH, hεH, haH, -, hεab, -⟩ := tilde_cut hH hfH hjH
  obtain ⟨i₁⟩ := tilde_sdIso_pendantSide_of_side hH hfH hjH (z₀ := ⟨z₀, (hZ z₀).2 (Or.inr rfl)⟩)
    (fun z => (hzH z).trans ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩) hεH haH
    (Joins.incident_left hεab)
  obtain ⟨i₂⟩ := tilde_halfNet hH hfH hjH hεH haH (Joins.incident_left hεab) id
  obtain ⟨i₃⟩ := tilde_halfNet hG hf hj hεf ha haε (Subtype.val : Z → X)
  exact ⟨((i₁.trans i₂.symm).trans σ.tildeNetwork).trans i₃⟩

end Induced

section Decomposition

variable {X : Type} [Fintype X] [DecidableEq X] {V E : Type} [Fintype V] [Fintype E]

/-- The taxa of the gluing at a block `P`: those of `P` go to the second piece, the others to the
first. -/
def blockSide (P : Finset X) (s₁ s₂ : X) (x : X) :
    ↥((insert s₂ Pᶜ : Finset X) : Set X) ⊕ ↥((insert s₁ P : Finset X) : Set X) :=
  if h : x ∈ P then .inr ⟨x, by simp [h]⟩ else .inl ⟨x, by simp [h]⟩

/-- **`Ñ` is the gluing of the networks `Ñ` of two induced networks** (proof of Theorem 4): for a node
`u` of a cycle `C` of `N⁻`, with block `P`, a taxon `s₂ ∈ P` and a taxon `s₁ ∉ P`, the network `Ñ` of
`N` is the gluing of the network `Ñ` of the network induced on `Pᶜ ∪ {s₂}`, at its leaf `s₂`, to the
network `Ñ` of the network induced on `P ∪ {s₁}`, at its leaf `s₁`. -/
theorem tilde_sdIso_glue {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {u} (hu : u ∈ cycleNodes (unrooted N hN hX).graph C)
    {P : Finset X} (hP : ∀ x, x ∈ P ↔ x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u)
    {s₁ s₂ : X} (hs₁ : s₁ ∉ P) (hs₂ : s₂ ∈ P)
    (hZ₁ : ((insert s₂ Pᶜ : Finset X) : Set X).Nontrivial)
    (hZ₂ : ((insert s₁ P : Finset X) : Set X).Nontrivial) :
    ∃ w₁ w₂, IsLeafNeighbour (tildeNetwork (unrooted (inducedLSA N hN.1 _ hZ₁)
        (inducedLSA_isBinaryRootedNetwork hN hZ₁) hZ₁.coe_sort)) ⟨s₂, by simp⟩ w₁ ∧
      IsLeafNeighbour (tildeNetwork (unrooted (inducedLSA N hN.1 _ hZ₂)
        (inducedLSA_isBinaryRootedNetwork hN hZ₂) hZ₂.coe_sort)) ⟨s₁, by simp⟩ w₂ ∧
      ∃ (hw₁ : w₁ ≠ _) (hw₂ : w₂ ≠ _), Nonempty (SDIso (tildeNetwork (unrooted N hN hX))
        (glue (tildeNetwork (unrooted (inducedLSA N hN.1 _ hZ₁)
            (inducedLSA_isBinaryRootedNetwork hN hZ₁) hZ₁.coe_sort))
          (tildeNetwork (unrooted (inducedLSA N hN.1 _ hZ₂)
            (inducedLSA_isBinaryRootedNetwork hN hZ₂) hZ₂.coe_sort))
          ⟨s₂, by simp⟩ ⟨s₁, by simp⟩ ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ (blockSide P s₁ s₂))) := by
  classical
  set G := unrooted N hN hX with hG_def
  have hG : IsUnrootedLevelOne G := isUnrootedLevelOne_unrooted hN h1 hX
  -- the edge `f` of `u` off `C`, from `u` to `v`
  obtain ⟨f, hfu, hfC, hf⟩ := hG.exists_offCycle hC hu
  obtain ⟨v, hj⟩ : ∃ v, Joins G.graph f u v := by
    rcases hfu with h | h
    · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨rfl, h⟩⟩
  -- the block `P` is the side of `v`
  have hPv : ∀ x, x ∈ P ↔ G.leaf x ∈ cutSide G.graph f v := fun x =>
    (hP x).trans (hG.mem_nodeBlock_iff hC hu hfC hj x)
  have hPu : ∀ x, x ∉ P ↔ G.leaf x ∈ cutSide G.graph f u := fun x => by
    rw [hPv, mem_cutSide_iff_notMem hG.connected hf hj.symm]
  -- the cut of `Ñ`
  obtain ⟨ε, a, b, hεf, ha, hb, hεab, hεd, hcross, hS, hleaf⟩ := tilde_cut hG hf hj
  have hleaf' : ∀ x, (tildeNetwork G).leaf x ∈ tildeCutSide G f v ↔ x ∈ P := fun x => by
    rw [hS, hleaf, ← hPu, not_not]
  -- the two sides
  have hZ₁' : ∀ x, x ∈ ((insert s₂ Pᶜ : Finset X) : Set X) ↔
      G.leaf x ∈ cutSide G.graph f u ∨ x = s₂ := fun x => by
    simp only [coe_insert, coe_compl, Set.mem_insert_iff, Set.mem_compl_iff, mem_coe, hPu]
    tauto
  have hZ₂' : ∀ x, x ∈ ((insert s₁ P : Finset X) : Set X) ↔
      G.leaf x ∈ cutSide G.graph f v ∨ x = s₁ := fun x => by
    simp only [coe_insert, Set.mem_insert_iff, mem_coe, hPv]
    tauto
  have hs₂u : G.leaf s₂ ∉ cutSide G.graph f u := (not_congr (hPu s₂)).mp (not_not.mpr hs₂)
  have hs₁v : G.leaf s₁ ∉ cutSide G.graph f v := (not_congr (hPv s₁)).mp hs₁
  obtain ⟨ι₁⟩ := tilde_inducedUnrooted_sdIso_pendantSide hN h1 hX hf hj hεf ha
    (Joins.incident_left hεab) hs₂u hZ₁' hZ₁
  obtain ⟨ι₂⟩ := tilde_inducedUnrooted_sdIso_pendantSide hN h1 hX hf (Or.symm hj) hεf hb
    (Joins.incident_right hεab) hs₁v hZ₂' hZ₂
  obtain ⟨j₁⟩ := nonempty_sdIso_inducedUnrooted_unrooted_inducedLSA hN hX hZ₁
  obtain ⟨j₂⟩ := nonempty_sdIso_inducedUnrooted_unrooted_inducedLSA hN hX hZ₂
  set k₁ := j₁.tildeNetwork.symm.trans ι₁
  set k₂ := j₂.tildeNetwork.symm.trans ι₂
  -- the neighbours of the leaves
  have hz₁ : (tildeNetwork G).leaf (Subtype.val (⟨s₂, by simp⟩ : ↥((insert s₂ Pᶜ : Finset X) :
      Set X))) ∉ tildeCutSide G f u := fun h => hs₂u ((hleaf s₂).mp h)
  have hz₂ : (tildeNetwork G).leaf (Subtype.val (⟨s₁, by simp⟩ : ↥((insert s₁ P : Finset X) :
      Set X))) ∉ tildeCutSide G f v := fun h => hs₁ ((hleaf' s₁).mp h)
  have hn₁ := isLeafNeighbour_pendantSide ⟨a, ha⟩ hz₁
  have hn₂ := isLeafNeighbour_pendantSide ⟨b, hb⟩ hz₂
  have hw₁ := hn₁.of_sdIso k₁.symm
  have hw₂ := hn₂.of_sdIso k₂.symm
  refine ⟨_, _, hw₁, hw₂, hw₁.1, hw₂.1, ?_⟩
  obtain ⟨g⟩ := glue_congr hw₁ hw₂ hn₁ hn₂ (blockSide P s₁ s₂) k₁ k₂
  have hτ₁ : ∀ x y, blockSide P s₁ s₂ x = .inl y → y.1 = x ∧
      (tildeNetwork G).leaf x ∈ tildeCutSide G f u := fun x y hxy => by
    unfold blockSide at hxy
    split_ifs at hxy with h
    cases hxy
    exact ⟨rfl, (hleaf x).mpr ((hPu x).mp h)⟩
  have hτ₂ : ∀ x y, blockSide P s₁ s₂ x = .inr y → y.1 = x ∧
      (tildeNetwork G).leaf x ∈ tildeCutSide G f v := fun x y hxy => by
    unfold blockSide at hxy
    split_ifs at hxy with h
    cases hxy
    exact ⟨rfl, (hleaf' x).mpr h⟩
  obtain ⟨A⟩ := nonempty_sdIso_glue_pendantSide (tildeNetwork G) hS ha hb hεab hεd hcross hz₁ hz₂
    hτ₁ hτ₂
  exact ⟨A.trans g.symm⟩

end Decomposition

end Banos2019
