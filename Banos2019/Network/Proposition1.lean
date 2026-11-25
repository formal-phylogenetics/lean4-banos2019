module

public import Banos2019.Network.TrekEdges
public import Banos2019.Network.AncestralSuppress

/-!
# Proposition 1: `(N⁻)_Z` and `(N⁺_Z)⁻` are isomorphic

The proof of Proposition 1 (Appendix): `K`, the network of the edges of `N⁻` on simple treks between
taxa of `Z`, has the edges of the LSA network of `Z` (`mem_trekEdges_iff`, by Lemma 17); suppressing
its nodes of degree two gives the network obtained from `N⁺_Z` by suppressing `LSA(Z)` and its other
nodes of degree two. The edges of both are the chains of the ancestral network on `Z` below `LSA(Z)`,
the two chains out of `LSA(Z)` merged into one.

* `trekNet`: `K` with its nodes; `valH`, `valK`: its nodes and edges in `N`.
* `isBranch_trekNet_iff`: the nodes of `K` kept by suppression are the nodes below `LSA(Z)` other than
  `LSA(Z)` that are not chain nodes of the ancestral network.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-- The conclusion of Lemma 17 for `N` and `Z`. -/
def Lemma17Conclusion {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (Z : Set X)
    (hZ : Z.Nonempty) : Prop :=
  ∀ e : E, N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source e) →
    (∃ z ∈ Z, N.graph.Reaches (N.graph.target e) (N.leaf z)) →
    ∃ x ∈ Z, ∃ y ∈ Z, ∃ t P₁ P₂, IsSimpleTrek (⟨N.graph, fun _ => True, N.leaf⟩ :
      SemidirectedNetwork V E X) (N.leaf x) (N.leaf y) t P₁ P₂ ∧ e ∈ P₁ ∪ P₂ ∧
      ∀ f ∈ P₁ ∪ P₂, N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source f)

section Restricted

variable {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X)

/-- `K`: the edges of `N⁻` on simple treks between taxa of `Z`, with their nodes. -/
abbrev trekNet (Z : Set X) :=
  restrict (semidirected hN.1 hN.2 hX) (trekEdges (semidirected hN.1 hN.2 hX) Z) Z

/-- The node of `N` of a node of `K`. -/
def valH {Z : Set X}
    (u : keptNodes (semidirected hN.1 hN.2 hX) (trekEdges (semidirected hN.1 hN.2 hX) Z) Z) : V :=
  sdVert hN.1 hX u.1

/-- The arc of `N` of an edge of `K`. -/
def valK {Z : Set X} (g : trekEdges (semidirected hN.1 hN.2 hX) Z) : E := sdArc hN.1 hN.2 hX g.1

variable {Z : Set X}

theorem valH_injective : Function.Injective (valH hN hX (Z := Z)) := fun _ _ h =>
  Subtype.ext (sdVert_injective hN.1 hX h)

theorem valK_injective : Function.Injective (valK hN hX (Z := Z)) := fun _ _ h =>
  Subtype.ext (sdArc_injective hN.1 hN.2 hX h)

theorem valH_target (g : trekEdges (semidirected hN.1 hN.2 hX) Z) :
    valH hN hX ((trekNet hN hX Z).graph.target g) = N.graph.target (valK hN hX g) := rfl

theorem valH_source (g : trekEdges (semidirected hN.1 hN.2 hX) Z) :
    valH hN hX ((trekNet hN hX Z).graph.source g) =
      sdVert hN.1 hX ((semidirected hN.1 hN.2 hX).graph.source g.1) := rfl

theorem valH_leaf (z : Z) : valH hN hX ((trekNet hN hX Z).leaf z) = N.leaf z := rfl

theorem trekNet_isDirected_iff (g : trekEdges (semidirected hN.1 hN.2 hX) Z) :
    (trekNet hN hX Z).IsDirected g ↔ 2 ≤ N.graph.indegree (N.graph.target (valK hN hX g)) :=
  semidirected_isDirected_iff hN.1 hN.2 hX g.1

theorem trekNet_isAcyclic : (trekNet hN hX Z).graph.IsAcyclic := by
  intro a h
  refine semidirected_isAcyclic hN hX a.1 (Relation.TransGen.lift Subtype.val ?_ a a h)
  rintro x y ⟨g, rfl, rfl⟩
  exact ⟨g.1, rfl, rfl⟩

/-- The arcs of the LSA of `Z`: two arcs leave it, both above taxa of `Z`. -/
theorem arcs_lsa (hZ : Z.Nontrivial) :
    {e | N.graph.source e = lsa hN.1 Z hZ.nonempty} =
      {e | N.graph.source e = lsa hN.1 Z hZ.nonempty ∧ e ∈ N.ancestralArcs Z} := by
  have := hN.1.finite_arcs
  have h2 := lsa_outdegree_ancestral hN.1 hN.2 hZ
  have hle : N.graph.outdegree (lsa hN.1 Z hZ.nonempty) ≤ 2 := by
    by_cases hr : lsa hN.1 Z hZ.nonempty = N.root
    · rw [hr, hN.2.1]
    · have h₁ := hN.1.nonroot_indegree _ hr
      by_cases h0 : N.graph.outdegree (lsa hN.1 Z hZ.nonempty) = 0
      · omega
      · have := hN.2.2 _ hr h0
        omega
  symm
  refine Set.eq_of_subset_of_ncard_le (fun e he => he.1) ?_ (Set.toFinite _)
  unfold DirectedMultigraph.outdegree at hle
  omega

/-- The other arc out of `LSA(Z)`. -/
theorem exists_other_arc_lsa (hZ : Z.Nontrivial) {a : E}
    (ha : N.graph.source a = lsa hN.1 Z hZ.nonempty) :
    ∃ b, N.graph.source b = lsa hN.1 Z hZ.nonempty ∧ b ≠ a ∧ b ∈ N.ancestralArcs Z ∧
      ∀ e, N.graph.source e = lsa hN.1 Z hZ.nonempty → e ≠ a → e = b := by
  have := hN.1.finite_arcs
  set A : Set E := {e | N.graph.source e = lsa hN.1 Z hZ.nonempty ∧ e ∈ N.ancestralArcs Z}
  have h2 : A.ncard = 2 := lsa_outdegree_ancestral hN.1 hN.2 hZ
  have hout : N.graph.outdegree (lsa hN.1 Z hZ.nonempty) = 2 := by
    unfold DirectedMultigraph.outdegree
    rw [arcs_lsa hN hZ]
    exact h2
  have hne : (A \ {a}).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    intro h0
    have := Set.ncard_le_ncard_sdiff_add_ncard A {a}
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨b, ⟨hbs, hba⟩, hb⟩ := hne
  refine ⟨b, hbs, fun h => hb (Set.mem_singleton_iff.mpr h), hba, fun e hes hea => ?_⟩
  by_contra heb
  exact not_three_of_outdegree_eq_two hout hes hbs ha heb hea
    (fun h => hb (Set.mem_singleton_iff.mpr h))

/-- A node of the ancestral network is a chain node when it has one parent in `N` and one arc above a
taxon of `Z`. -/
theorem chainZ_iff (hZ : Z.Nonempty) {v : V} (hv : v ∈ N.ancestralVertices Z) :
    ChainZ hN.1 hZ v ↔
      N.graph.indegree v = 1 ∧ {e | N.graph.source e = v ∧ e ∈ N.ancestralArcs Z}.ncard = 1 := by
  constructor
  · rintro ⟨h, h₁, h₂⟩
    rw [ancestral_outdegree hN.1 hZ] at h₂
    exact ⟨(N.ancestralGraph_indegree Z ⟨v, h⟩).symm.trans h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨hv, (N.ancestralGraph_indegree Z ⟨v, hv⟩).trans h₁, ?_⟩
    rw [ancestral_outdegree hN.1 hZ]
    exact h₂

section Kept

variable (hZ : Z.Nontrivial) (h17 : Lemma17Conclusion hN Z hZ.nonempty)
include h17

theorem valK_mem_belowArcs (g : trekEdges (semidirected hN.1 hN.2 hX) Z) :
    valK hN hX g ∈ N.belowArcs (lsa hN.1 Z hZ.nonempty) Z :=
  (mem_trekEdges_iff hN hX hZ.nonempty h17 g.1).mp g.2

omit h17 in
/-- An arc out of `LSA(X)` other than `rootTreeArc` is below `LSA(Z)` only when the two are equal. -/
theorem lsa_eq_of_source_eq {e : E} (he : e ∈ N.belowArcs (lsa hN.1 Z hZ.nonempty) Z)
    (hs : N.graph.source e = lsa hN.1 Set.univ Set.univ_nonempty) :
    lsa hN.1 Z hZ.nonempty = lsa hN.1 Set.univ Set.univ_nonempty :=
  eq_of_reaches_of_reaches hN.1.acyclic (hs ▸ he.1) (lsa_univ_reaches hN.1 hZ.nonempty)

theorem exists_valK {e : E} (he : e ∈ N.belowArcs (lsa hN.1 Z hZ.nonempty) Z)
    (hne : e ≠ sdRootArc hN.1 hN.2 hX) : ∃ g, valK hN hX (Z := Z) g = e := by
  obtain ⟨g, rfl⟩ := (mem_range_sdArc hN.1 hN.2 hX e).mpr
    ⟨(lsa_univ_reaches hN.1 hZ.nonempty).trans he.1, hne⟩
  exact ⟨⟨g, (mem_trekEdges_iff hN hX hZ.nonempty h17 g).mpr he⟩, rfl⟩

/-- The nodes of `K`: those strictly below `LSA(X)`, below `LSA(Z)` and above a taxon of `Z`. -/
theorem mem_keptNodes_iff (u : SemidirectedVertex hN.1 hX) :
    u ∈ keptNodes (semidirected hN.1 hN.2 hX) (trekEdges (semidirected hN.1 hN.2 hX) Z) Z ↔
      N.graph.Reaches (lsa hN.1 Z hZ.nonempty) (sdVert hN.1 hX u) ∧
        sdVert hN.1 hX u ∈ N.ancestralVertices Z := by
  have := hN.1.finite_arcs
  have hlsa := lsa_spec hN.1 Z hZ.nonempty
  set m := lsa hN.1 Z hZ.nonempty
  set ρ := lsa hN.1 Set.univ Set.univ_nonempty
  have hsf₁ := (sdRootArc_spec hN.1 hN.2 hX).1
  constructor
  · rintro (⟨g, hg, hu | hu⟩ | ⟨z, hz, rfl⟩)
    · have hb := (mem_trekEdges_iff hN hX hZ.nonempty h17 g).mp hg
      rw [← hu]
      by_cases hs : N.graph.source (sdArc hN.1 hN.2 hX g) = ρ
      · have hmρ := lsa_eq_of_source_eq hN hX hZ hb hs
        rw [sdVert_source_of_eq hN hX g hs]
        have hf₁ : sdRootArc hN.1 hN.2 hX ∈ N.ancestralArcs Z := by
          have : sdRootArc hN.1 hN.2 hX ∈ {e | N.graph.source e = m} :=
            hsf₁.trans hmρ.symm
          rw [arcs_lsa hN hZ] at this
          exact this.2
        exact ⟨.single ⟨_, hsf₁.trans hmρ.symm, rfl⟩, hf₁⟩
      · rw [sdVert_source_of_ne hN hX g hs]
        exact ⟨hb.1, N.source_mem_ancestralVertices hb.2⟩
    · rw [← hu]
      have hb := (mem_trekEdges_iff hN hX hZ.nonempty h17 g).mp hg
      exact ⟨hb.1.tail ⟨_, rfl, rfl⟩, hb.2⟩
    · exact ⟨hlsa.1.reaches_leaf hN.1 hz, N.leaf_mem_ancestralVertices hz⟩
  · rintro ⟨hmv, hv⟩
    have hvρ : sdVert hN.1 hX u ≠ ρ := ((mem_range_sdVert hN.1 hX _).mp ⟨u, rfl⟩).2
    by_cases hvm : sdVert hN.1 hX u = m
    · -- an arc out of `LSA(Z)`
      have hne : ({e | N.graph.source e = m ∧ e ∈ N.ancestralArcs Z} : Set E).Nonempty := by
        have := hN.1.finite_arcs
        apply Set.nonempty_of_ncard_ne_zero
        rw [lsa_outdegree_ancestral hN.1 hN.2 hZ]
        norm_num
      obtain ⟨e, hes, hea⟩ := hne
      have hb : e ∈ N.belowArcs m Z := ⟨hes ▸ .refl, hea⟩
      have hesρ : N.graph.source e ≠ ρ := fun h => hvρ (hvm.trans (hes.symm.trans h))
      obtain ⟨g, hg⟩ := exists_valK hN hX hZ h17 hb fun h => hesρ (h ▸ hsf₁)
      refine Or.inl ⟨g.1, g.2, Or.inl (sdVert_injective hN.1 hX ?_)⟩
      rw [sdVert_source_of_ne hN hX g.1 (by rw [← hg] at hesρ; exact hesρ)]
      change N.graph.source (valK hN hX g) = _
      rw [hg, hes, hvm]
    · -- an arc into it
      have hvr : sdVert hN.1 hX u ≠ N.root := fun h => hvm
        (eq_of_reaches_of_reaches hN.1.acyclic (h ▸ hN.1.root_reaches m) hmv)
      obtain ⟨e, he⟩ := (N.graph.one_le_indegree_iff _).mp (hN.1.nonroot_indegree _ hvr)
      obtain ⟨z, hz, hvz⟩ := hv
      have hb : e ∈ N.belowArcs m Z := by
        refine ⟨hlsa.1.reaches_source hN.1 hz (he ▸ hvz) fun h => hvm ?_, by
          show N.graph.target e ∈ N.ancestralVertices Z
          rw [he]
          exact ⟨z, hz, hvz⟩⟩
        exact eq_of_reaches_of_reaches hN.1.acyclic (he ▸ h) hmv
      by_cases hef : e = sdRootArc hN.1 hN.2 hX
      · -- the child of `rootTreeArc`: the other arc out of `LSA(X) = LSA(Z)` leaves it in `N⁻`
        have hmρ := lsa_eq_of_source_eq hN hX hZ hb (hef ▸ hsf₁)
        set A : Set E := {e | N.graph.source e = m ∧ e ∈ N.ancestralArcs Z} with hA
        have hne : (A \ {sdRootArc hN.1 hN.2 hX}).Nonempty := by
          have := hN.1.finite_arcs
          apply Set.nonempty_of_ncard_ne_zero
          intro h0
          have h2 : A.ncard = 2 := lsa_outdegree_ancestral hN.1 hN.2 hZ
          have := Set.ncard_le_ncard_sdiff_add_ncard A {sdRootArc hN.1 hN.2 hX}
          rw [Set.ncard_singleton] at this
          omega
        obtain ⟨f₂, ⟨hf₂s, hf₂a⟩, hf₂⟩ := hne
        obtain ⟨g, hg⟩ := exists_valK hN hX hZ h17 (e := f₂) ⟨hf₂s ▸ .refl, hf₂a⟩ hf₂
        refine Or.inl ⟨g.1, g.2, Or.inl (sdVert_injective hN.1 hX ?_)⟩
        rw [sdVert_source_of_eq hN hX g.1 (by
          change N.graph.source (valK hN hX g) = _
          rw [hg, hf₂s]
          exact hmρ), ← hef, he]
      · obtain ⟨g, hg⟩ := exists_valK hN hX hZ h17 hb hef
        refine Or.inl ⟨g.1, g.2, Or.inr (sdVert_injective hN.1 hX ?_)⟩
        change N.graph.target (valK hN hX g) = _
        rw [hg, he]

theorem exists_valH {v : V} (hmv : N.graph.Reaches (lsa hN.1 Z hZ.nonempty) v)
    (hv : v ∈ N.ancestralVertices Z) (hvρ : v ≠ lsa hN.1 Set.univ Set.univ_nonempty) :
    ∃ u, valH hN hX (Z := Z) u = v := by
  obtain ⟨u, rfl⟩ := (mem_range_sdVert hN.1 hX v).mpr
    ⟨(lsa_univ_reaches hN.1 hZ.nonempty).trans hmv, hvρ⟩
  exact ⟨⟨u, (mem_keptNodes_iff hN hX hZ h17 u).mpr ⟨hmv, hv⟩⟩, rfl⟩

theorem valH_mem (u : keptNodes (semidirected hN.1 hN.2 hX) (trekEdges (semidirected hN.1 hN.2 hX)
    Z) Z) : N.graph.Reaches (lsa hN.1 Z hZ.nonempty) (valH hN hX u) ∧
      valH hN hX u ∈ N.ancestralVertices Z :=
  (mem_keptNodes_iff hN hX hZ h17 u.1).mp u.2

/-- **The degree of a node of `K` other than `LSA(Z)`** is its indegree in `N` plus its outdegree in
the ancestral network on `Z`. At the child of `rootTreeArc`, when `LSA(Z) = LSA(X)`, `rootTreeArc` is
replaced by the other arc out of `LSA(X)`. -/
theorem degree_trekNet (u : keptNodes (semidirected hN.1 hN.2 hX)
    (trekEdges (semidirected hN.1 hN.2 hX) Z) Z) (hu : valH hN hX u ≠ lsa hN.1 Z hZ.nonempty) :
    degree (trekNet hN hX Z).graph u = N.graph.indegree (valH hN hX u) +
      {e | N.graph.source e = valH hN hX u ∧ e ∈ N.ancestralArcs Z}.ncard := by
  have := hN.1.finite_arcs
  obtain ⟨hmv, hv⟩ := valH_mem hN hX hZ h17 u
  have hlsa := lsa_spec hN.1 Z hZ.nonempty
  set v := valH hN hX u with hv_def
  set m := lsa hN.1 Z hZ.nonempty
  set ρ := lsa hN.1 Set.univ Set.univ_nonempty
  set f₁ := sdRootArc hN.1 hN.2 hX
  have hsf₁ : N.graph.source f₁ = ρ := (sdRootArc_spec hN.1 hN.2 hX).1
  have hvρ : v ≠ ρ := ((mem_range_sdVert hN.1 hX _).mp ⟨u.1, rfl⟩).2
  have hin_below : ∀ e, N.graph.target e = v → e ∈ N.belowArcs m Z := by
    intro e he
    obtain ⟨z, hz, hvz⟩ := hv
    refine ⟨hlsa.1.reaches_source hN.1 hz (he ▸ hvz) fun h => hu ?_, by
      show N.graph.target e ∈ N.ancestralVertices Z
      rw [he]
      exact ⟨z, hz, hvz⟩⟩
    exact eq_of_reaches_of_reaches hN.1.acyclic (he ▸ h) hmv
  have htgt : ∀ g, (trekNet hN hX Z).graph.target g = u ↔ N.graph.target (valK hN hX g) = v :=
    fun g => ⟨fun h => congrArg (valH hN hX) h, fun h => valH_injective hN hX h⟩
  have hsrc : ∀ g, (trekNet hN hX Z).graph.source g = u ↔
      sdVert hN.1 hX ((semidirected hN.1 hN.2 hX).graph.source g.1) = v :=
    fun g => ⟨fun h => congrArg (valH hN hX) h, fun h => valH_injective hN hX h⟩
  unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree
  rw [← Set.ncard_image_of_injective _ (valK_injective hN hX),
    ← Set.ncard_image_of_injective {g | (trekNet hN hX Z).graph.source g = u}
      (valK_injective hN hX)]
  by_cases hvf : v = N.graph.target f₁
  · -- the child of `rootTreeArc`
    have hmρ : m = ρ := lsa_eq_of_source_eq hN hX hZ (hin_below f₁ hvf.symm) hsf₁
    have hind : N.graph.indegree v = 1 := hvf ▸ (sdRootArc_spec hN.1 hN.2 hX).2
    obtain ⟨f₂, hf₂s, hf₂, hf₂a, hf₂u⟩ := exists_other_arc_lsa hN hZ (hsf₁.trans hmρ.symm)
    have h1 : valK hN hX '' {g | (trekNet hN hX Z).graph.target g = u} = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro e ⟨g, hg, rfl⟩
      obtain ⟨e₀, he₀⟩ := (N.graph.indegree_eq_one_iff _).mp (sdRootArc_spec hN.1 hN.2 hX).2
      have h₁ := (he₀ (valK hN hX g)).mp (((htgt g).mp hg).trans hvf)
      have h₂ := (he₀ f₁).mp rfl
      exact ((mem_range_sdArc hN.1 hN.2 hX _).mp ⟨g.1, rfl⟩).2 (h₁.trans h₂.symm)
    have h2 : valK hN hX '' {g | (trekNet hN hX Z).graph.source g = u} =
        insert f₂ {e | N.graph.source e = v ∧ e ∈ N.ancestralArcs Z} := by
      ext e
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hg' := (hsrc g).mp hg
        by_cases hs : N.graph.source (valK hN hX g) = ρ
        · exact Or.inl (hf₂u _ (hs.trans hmρ.symm) ((mem_range_sdArc hN.1 hN.2 hX _).mp
            ⟨g.1, rfl⟩).2)
        · rw [sdVert_source_of_ne hN hX g.1 hs] at hg'
          exact Or.inr ⟨hg', (valK_mem_belowArcs hN hX hZ h17 g).2⟩
      · rintro (he | ⟨hes, hea⟩)
        · obtain ⟨g, hg⟩ := exists_valK hN hX hZ h17 (e := f₂) ⟨hf₂s ▸ .refl, hf₂a⟩ hf₂
          refine ⟨g, (hsrc g).mpr ?_, hg.trans he.symm⟩
          have hgs : N.graph.source (valK hN hX g) = ρ := by
            rw [hg, hf₂s]
            exact hmρ
          rw [sdVert_source_of_eq hN hX g.1 hgs, ← hvf]
        · have hesρ : N.graph.source e ≠ ρ := fun h => hvρ (hes.symm.trans h)
          obtain ⟨g, hg⟩ := exists_valK hN hX hZ h17 (e := e) ⟨hes ▸ hmv, hea⟩
            fun h => hesρ (h ▸ hsf₁)
          refine ⟨g, (hsrc g).mpr ?_, hg⟩
          have hgs : N.graph.source (valK hN hX g) ≠ ρ := by
            rw [hg]
            exact hesρ
          rw [sdVert_source_of_ne hN hX g.1 hgs]
          change N.graph.source (valK hN hX g) = _
          rw [hg, hes]
    have hind' : ({e | N.graph.target e = v} : Set E).ncard = 1 := hind
    rw [h1, h2, Set.ncard_empty, Set.ncard_insert_of_notMem (fun h => hvρ (h.1.symm.trans hf₂s
      |>.trans hmρ)) (Set.toFinite _), hind']
    omega
  · have h1 : valK hN hX '' {g | (trekNet hN hX Z).graph.target g = u} =
        {e | N.graph.target e = v} := by
      ext e
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact (htgt g).mp hg
      · intro he
        obtain ⟨g, hg⟩ := exists_valK hN hX hZ h17 (hin_below e he)
          fun h => hvf (h ▸ he).symm
        exact ⟨g, (htgt g).mpr (hg ▸ he), hg⟩
    have h2 : valK hN hX '' {g | (trekNet hN hX Z).graph.source g = u} =
        {e | N.graph.source e = v ∧ e ∈ N.ancestralArcs Z} := by
      ext e
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hg' := (hsrc g).mp hg
        by_cases hs : N.graph.source (valK hN hX g) = ρ
        · rw [sdVert_source_of_eq hN hX g.1 hs] at hg'
          exact absurd hg'.symm hvf
        · rw [sdVert_source_of_ne hN hX g.1 hs] at hg'
          exact ⟨hg', (valK_mem_belowArcs hN hX hZ h17 g).2⟩
      · rintro ⟨hes, hea⟩
        have hesρ : N.graph.source e ≠ ρ := fun h => hvρ (hes.symm.trans h)
        obtain ⟨g, hg⟩ := exists_valK hN hX hZ h17 (e := e) ⟨hes ▸ hmv, hea⟩
          fun h => hesρ (h ▸ hsf₁)
        refine ⟨g, (hsrc g).mpr ?_, hg⟩
        have hgs : N.graph.source (valK hN hX g) ≠ ρ := by
          rw [hg]
          exact hesρ
        rw [sdVert_source_of_ne hN hX g.1 hgs]
        change N.graph.source (valK hN hX g) = _
        rw [hg, hes]
    rw [h1, h2]

/-- The nodes of `K` that are taxa are the taxa of `Z`. -/
theorem trekNet_leaf_iff (u : keptNodes (semidirected hN.1 hN.2 hX)
    (trekEdges (semidirected hN.1 hN.2 hX) Z) Z) :
    (∃ x, (trekNet hN hX Z).leaf x = u) ↔ ∃ x, N.leaf x = valH hN hX u := by
  have := hN.1.finite_arcs
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz, hvz⟩ := (valH_mem hN hX hZ h17 u).2
    have hxz : N.leaf z = N.leaf x := N.graph.eq_of_reaches_of_outdegree_eq_zero (hx ▸ hvz)
      ((hN.1.leaves _).mpr ⟨x, rfl⟩)
    have hxz' := hN.1.leaf_injective hxz
    subst hxz'
    exact ⟨⟨z, hz⟩, valH_injective hN hX hx⟩

/-- **The nodes of `K` kept by suppression**, other than `LSA(Z)`, are those that are not chain nodes
of the ancestral network on `Z`. -/
theorem isBranch_trekNet_iff (u : keptNodes (semidirected hN.1 hN.2 hX)
    (trekEdges (semidirected hN.1 hN.2 hX) Z) Z) (hu : valH hN hX u ≠ lsa hN.1 Z hZ.nonempty) :
    IsBranch (trekNet hN hX Z) ∅ u ↔ ¬ ChainZ hN.1 hZ.nonempty (valH hN hX u) := by
  have := hN.1.finite_arcs
  obtain ⟨hmv, hv⟩ := valH_mem hN hX hZ h17 u
  have hdeg := degree_trekNet hN hX hZ h17 u hu
  rw [chainZ_iff hN hZ.nonempty hv]
  have hvr : valH hN hX u ≠ N.root := fun h => hu
    (eq_of_reaches_of_reaches hN.1.acyclic (h ▸ hN.1.root_reaches _) hmv)
  have hin : 1 ≤ N.graph.indegree (valH hN hX u) := hN.1.nonroot_indegree _ hvr
  constructor
  · rintro (hd | hl | he) ⟨h₁, h₂⟩
    · exact hd (by omega)
    · obtain ⟨x, hx⟩ := (trekNet_leaf_iff hN hX hZ h17 u).mp hl
      have h0 := (N.graph.outdegree_eq_zero_iff _).mp ((hN.1.leaves _).mpr ⟨x, hx⟩)
      have : ({e | N.graph.source e = valH hN hX u ∧ e ∈ N.ancestralArcs Z} : Set E) = ∅ :=
        Set.eq_empty_of_forall_notMem fun e he => h0 e he.1
      rw [this, Set.ncard_empty] at h₂
      exact absurd h₂ (by norm_num)
    · exact he
  · intro hnc
    by_cases hl : ∃ x, N.leaf x = valH hN hX u
    · exact Or.inr (Or.inl ((trekNet_leaf_iff hN hX hZ h17 u).mpr hl))
    · refine Or.inl fun h2 => hnc ⟨?_, ?_⟩ <;> rw [hdeg] at h2
      · have : 1 ≤ ({e | N.graph.source e = valH hN hX u ∧ e ∈ N.ancestralArcs Z} : Set E).ncard := by
          obtain ⟨z, hz, hvz⟩ := hv
          rcases Relation.ReflTransGen.cases_head hvz with h | ⟨c, ⟨e, hes, het⟩, hcz⟩
          · exact absurd ⟨z, h.symm⟩ hl
          · exact Nat.one_le_iff_ne_zero.mpr (Set.ncard_ne_zero_of_mem (a := e)
              ⟨hes, ⟨z, hz, het ▸ hcz⟩⟩ (Set.toFinite _))
        omega
      · have : 1 ≤ ({e | N.graph.source e = valH hN hX u ∧ e ∈ N.ancestralArcs Z} : Set E).ncard := by
          obtain ⟨z, hz, hvz⟩ := hv
          rcases Relation.ReflTransGen.cases_head hvz with h | ⟨c, ⟨e, hes, het⟩, hcz⟩
          · exact absurd ⟨z, h.symm⟩ hl
          · exact Nat.one_le_iff_ne_zero.mpr (Set.ncard_ne_zero_of_mem (a := e)
              ⟨hes, ⟨z, hz, het ▸ hcz⟩⟩ (Set.toFinite _))
        omega

/-- **`LSA(Z)`, when it is a node of `K`, is removed by suppression**: it has degree two. -/
theorem not_isBranch_trekNet_lsa (u : keptNodes (semidirected hN.1 hN.2 hX)
    (trekEdges (semidirected hN.1 hN.2 hX) Z) Z) (hu : valH hN hX u = lsa hN.1 Z hZ.nonempty) :
    ¬ IsBranch (trekNet hN hX Z) ∅ u := by
  have := hN.1.finite_arcs
  set m := lsa hN.1 Z hZ.nonempty
  set ρ := lsa hN.1 Set.univ Set.univ_nonempty
  have hsf₁ : N.graph.source (sdRootArc hN.1 hN.2 hX) = ρ := (sdRootArc_spec hN.1 hN.2 hX).1
  have hmρ : m ≠ ρ := fun h => ((mem_range_sdVert hN.1 hX _).mp ⟨u.1, rfl⟩).2 (hu.trans h)
  have htgt : ∀ g, (trekNet hN hX Z).graph.target g = u ↔ N.graph.target (valK hN hX g) = m :=
    fun g => ⟨fun h => (congrArg (valH hN hX) h).trans hu, fun h => valH_injective hN hX
      (h.trans hu.symm)⟩
  have hsrc : ∀ g, (trekNet hN hX Z).graph.source g = u ↔
      sdVert hN.1 hX ((semidirected hN.1 hN.2 hX).graph.source g.1) = m :=
    fun g => ⟨fun h => (congrArg (valH hN hX) h).trans hu, fun h => valH_injective hN hX
      (h.trans hu.symm)⟩
  rintro (hd | hl | he)
  · apply hd
    unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree
    rw [← Set.ncard_image_of_injective _ (valK_injective hN hX),
      ← Set.ncard_image_of_injective {g | (trekNet hN hX Z).graph.source g = u}
        (valK_injective hN hX)]
    have h1 : valK hN hX '' {g | (trekNet hN hX Z).graph.target g = u} = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro e ⟨g, hg, rfl⟩
      have hb := valK_mem_belowArcs hN hX hZ h17 g
      exact not_reaches_target_source' hN.1.acyclic _ (by rw [(htgt g).mp hg]; exact hb.1)
    have h2 : valK hN hX '' {g | (trekNet hN hX Z).graph.source g = u} =
        {e | N.graph.source e = m ∧ e ∈ N.ancestralArcs Z} := by
      ext e
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hg' := (hsrc g).mp hg
        have hb := valK_mem_belowArcs hN hX hZ h17 g
        by_cases hs : N.graph.source (valK hN hX g) = ρ
        · exact absurd (lsa_eq_of_source_eq hN hX hZ hb hs) hmρ
        · rw [sdVert_source_of_ne hN hX g.1 hs] at hg'
          exact ⟨hg', hb.2⟩
      · rintro ⟨hes, hea⟩
        have hesρ : N.graph.source e ≠ ρ := fun h => hmρ (hes.symm.trans h)
        obtain ⟨g, hg⟩ := exists_valK hN hX hZ h17 (e := e) ⟨hes ▸ .refl, hea⟩
          fun h => hesρ (h ▸ hsf₁)
        refine ⟨g, (hsrc g).mpr ?_, hg⟩
        have hgs : N.graph.source (valK hN hX g) ≠ ρ := by
          rw [hg]
          exact hesρ
        rw [sdVert_source_of_ne hN hX g.1 hgs]
        change N.graph.source (valK hN hX g) = _
        rw [hg, hes]
    rw [h1, h2, Set.ncard_empty, lsa_outdegree_ancestral hN.1 hN.2 hZ]
  · obtain ⟨x, hx⟩ := (trekNet_leaf_iff hN hX hZ h17 u).mp hl
    exact IsStableAncestor.leaf_ne hN.1 hZ (lsa_spec hN.1 Z hZ.nonempty).1 x (hx.trans hu)
  · exact he

/-- **The nodes of `(N⁻)_Z`**: the nodes strictly below `LSA(Z)`, above a taxon of `Z`, that are not
chain nodes of the ancestral network on `Z`. -/
def lVertEquiv : {u // IsBranch (trekNet hN hX Z) ∅ u} ≃
    {v : V // v ∈ N.ancestralVertices Z ∧ ¬ ChainZ hN.1 hZ.nonempty v ∧
      N.graph.Reaches (lsa hN.1 Z hZ.nonempty) v ∧ v ≠ lsa hN.1 Z hZ.nonempty} :=
  equivOfInjective (fun u => valH hN hX u.1) (fun _ _ h => Subtype.ext (valH_injective hN hX h)) _
    fun v => by
      constructor
      · rintro ⟨hv, hnc, hmv, hvm⟩
        have hvρ : v ≠ lsa hN.1 Set.univ Set.univ_nonempty := fun h => hvm
          (eq_of_reaches_of_reaches hN.1.acyclic (h ▸ lsa_univ_reaches hN.1 hZ.nonempty) hmv)
        obtain ⟨u, rfl⟩ := exists_valH hN hX hZ h17 hmv hv hvρ
        exact ⟨⟨u, (isBranch_trekNet_iff hN hX hZ h17 u hvm).mpr hnc⟩, rfl⟩
      · rintro ⟨u, rfl⟩
        obtain ⟨hmv, hv⟩ := valH_mem hN hX hZ h17 u.1
        have hvm : valH hN hX u.1 ≠ lsa hN.1 Z hZ.nonempty := fun h =>
          not_isBranch_trekNet_lsa hN hX hZ h17 u.1 h u.2
        exact ⟨hv, (isBranch_trekNet_iff hN hX hZ h17 u.1 hvm).mp u.2, hmv, hvm⟩

end Kept

end Restricted

end Banos2019
