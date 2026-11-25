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

omit h17 in
/-- A node below `LSA(Z)` is not `LSA(X)`, unless both are `LSA(Z)`. -/
theorem ne_lsa_univ {s : V} (hms : N.graph.Reaches (lsa hN.1 Z hZ.nonempty) s)
    (h : s ≠ lsa hN.1 Z hZ.nonempty ∨ lsa hN.1 Z hZ.nonempty ≠ lsa hN.1 Set.univ Set.univ_nonempty) :
    s ≠ lsa hN.1 Set.univ Set.univ_nonempty := by
  rintro rfl
  have := eq_of_reaches_of_reaches hN.1.acyclic hms (lsa_univ_reaches hN.1 hZ.nonempty)
  rcases h with h | h
  · exact h this.symm
  · exact h this

/-- **A path of `N` below `LSA(Z)` is a path of `K`**, when it avoids `LSA(X)`. -/
theorem isDPath_trekNet {a b : V} {S : Set V} {P : Set E} (h : IsDPath N.graph a b S P)
    (hS : ∀ s ∈ S, N.graph.Reaches (lsa hN.1 Z hZ.nonempty) s ∧ s ∈ N.ancestralVertices Z ∧
      s ≠ lsa hN.1 Set.univ Set.univ_nonempty)
    {ua ub : keptNodes (semidirected hN.1 hN.2 hX) (trekEdges (semidirected hN.1 hN.2 hX) Z) Z}
    (hua : valH hN hX ua = a) (hub : valH hN hX ub = b) :
    IsDPath (trekNet hN hX Z).graph ua ub (valH hN hX ⁻¹' S) (valK hN hX ⁻¹' P) := by
  refine h.pullback (valH hN hX) (valK hN hX) (valH_injective hN hX) (valK_injective hN hX)
    (fun e he => ?_) hua hub
  obtain ⟨hs₁, -, hs₃⟩ := hS _ (h.ends_mem he).1
  obtain ⟨-, ht₂, -⟩ := hS _ (h.ends_mem he).2
  obtain ⟨g, rfl⟩ := exists_valK hN hX hZ h17 (e := e) ⟨hs₁, ht₂⟩
    fun h' => hs₃ (h' ▸ (sdRootArc_spec hN.1 hN.2 hX).1)
  exact ⟨g, rfl, (sdVert_source_of_ne hN hX g.1 hs₃).symm, rfl⟩

/-- A node of `K` that is not a chain node and is not `LSA(Z)` is kept. -/
theorem isBranch_of_not_chainZ (u : keptNodes (semidirected hN.1 hN.2 hX)
    (trekEdges (semidirected hN.1 hN.2 hX) Z) Z) (hm : valH hN hX u ≠ lsa hN.1 Z hZ.nonempty)
    (hc : ¬ ChainZ hN.1 hZ.nonempty (valH hN hX u)) : IsBranch (trekNet hN hX Z) ∅ u :=
  (isBranch_trekNet_iff hN hX hZ h17 u hm).mpr hc

/-- A chain node is removed by suppression. -/
theorem not_isBranch_of_chainZ (u : keptNodes (semidirected hN.1 hN.2 hX)
    (trekEdges (semidirected hN.1 hN.2 hX) Z) Z)
    (hc : ChainZ hN.1 hZ.nonempty (valH hN hX u)) : ¬ IsBranch (trekNet hN hX Z) ∅ u := by
  have hm : valH hN hX u ≠ lsa hN.1 Z hZ.nonempty := fun h =>
    not_chainZ_lsa hN.1 hN.2 hZ (h ▸ hc)
  exact fun h => (isBranch_trekNet_iff hN hX hZ h17 u hm).mp h hc

end Kept

end Restricted

section RSide

variable {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {Z : Set X} (hZ : Z.Nontrivial)
  {VC EC : Type*} {C : RootedNetwork VC EC Z} (hC : IsBinaryRootedNetwork C)
  (ι : VC → {v : N.AncestralVertex Z //
    ¬ (N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).IsChainVertex v})
  (κ : EC → {e : N.AncestralArc Z // ¬ (N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).IsChainVertex
    ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).graph.source e)})
  (hK : IsContraction ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).suppress
    (N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty)) C ι κ)

/-- The node of `N` of a node of `C`. -/
def valC (c : VC) : V := valS hN.1 hZ.nonempty (ι c)

/-- The arc of `N` of an arc of `C`. -/
def valCE (e : EC) : E := valSE hN.1 hZ.nonempty (κ e)

include hK

theorem valC_injective : Function.Injective (valC hN hZ ι) := fun _ _ h =>
  hK.inj_v (valS_injective hN.1 hZ.nonempty h)

theorem valCE_injective : Function.Injective (valCE hN hZ κ) := fun _ _ h =>
  hK.inj_e (valSE_injective hN.1 hZ.nonempty h)

theorem valC_source (e : EC) : valC hN hZ ι (C.graph.source e) = N.graph.source (valCE hN hZ κ e) := by
  unfold valC valCE
  rw [hK.source]
  rfl

theorem valC_target (e : EC) :
    valC hN hZ ι (C.graph.target e) = chainEndZ hN.1 hZ.nonempty (N.graph.target (valCE hN hZ κ e)) := by
  unfold valC valCE
  rw [hK.target, valS_target]

theorem valC_leaf (z : Z) : valC hN hZ ι (C.leaf z) = N.leaf z := by
  unfold valC
  rw [hK.leaf]
  rfl

theorem valC_reaches_iff (c c' : VC) :
    C.graph.Reaches c c' ↔ N.graph.Reaches (valC hN hZ ι c) (valC hN hZ ι c') :=
  hK.reaches_iff.trans (suppressAnc_reaches_iff hN.1 hZ.nonempty _ _)

theorem valC_lsa :
    valC hN hZ ι (lsa hC.1 Set.univ (@Set.univ_nonempty _ hZ.coe_sort.to_nonempty)) =
      lsa hN.1 Z hZ.nonempty := by
  have hS := suppress_isPhylogenetic (N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty)
  unfold valC
  rw [hK.lsa_eq hS hC.1, IsLeastStableAncestor.unique hS (lsa_spec hS _ _)
    (suppressAnc_isLeastStableAncestor hN.1 hN.2 hZ)]
  rfl

include hC in
theorem isHybridArc_iff_valC (e : EC) :
    C.IsHybridArc e ↔ 2 ≤ N.graph.indegree (chainEndZ hN.1 hZ.nonempty
      (N.graph.target (valCE hN hZ κ e))) :=
  (hK.isHybridArc_iff hC.1 e).trans (suppressAnc_isHybridArc_iff hN.1 hZ.nonempty _)

include hC in
theorem isTreeArc_iff_valC (e : EC) :
    C.IsTreeArc e ↔ N.graph.indegree (chainEndZ hN.1 hZ.nonempty
      (N.graph.target (valCE hN hZ κ e))) = 1 :=
  (hK.isTreeArc_iff hC.1 e).trans (suppressAnc_isTreeArc_iff hN.1 hZ.nonempty _)

omit hK in
/-- The node of `N` of a node of `(N⁺_Z)⁻`. -/
def valR (r : SemidirectedVertex hC.1 hZ.coe_sort) : V :=
  valC hN hZ ι (sdVert hC.1 hZ.coe_sort r)

omit hK in
/-- The arc of `N` of an edge of `(N⁺_Z)⁻`. -/
def valRE (g : SemidirectedArc hC.1 hC.2 hZ.coe_sort) : E :=
  valCE hN hZ κ (sdArc hC.1 hC.2 hZ.coe_sort g)

omit hK in
/-- The arc out of `LSA(Z)` that `(N⁺_Z)⁻` merges into the other. -/
def rootArcR : E := valCE hN hZ κ (sdRootArc hC.1 hC.2 hZ.coe_sort)

theorem mem_range_valC (v : V) :
    (∃ c, valC hN hZ ι c = v) ↔ v ∈ N.ancestralVertices Z ∧ ¬ ChainZ hN.1 hZ.nonempty v ∧
      ¬ (v = N.root ∧ ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).suppress
        (N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty)).graph.outdegree
          ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).suppress
            (N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty)).root = 1) := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨hv, hnc⟩ := (mem_range_valS hN.1 hZ.nonempty _).mp ⟨ι c, rfl⟩
    refine ⟨hv, hnc, fun ⟨hr, h1⟩ => (hK.range_v (ι c)).mp ⟨c, rfl⟩ ⟨?_, h1⟩⟩
    exact valS_injective hN.1 hZ.nonempty (hr.trans (valS_root hN.1 hZ.nonempty).symm)
  · rintro ⟨hv, hnc, hr⟩
    obtain ⟨s, rfl⟩ := (mem_range_valS hN.1 hZ.nonempty v).mpr ⟨hv, hnc⟩
    obtain ⟨c, rfl⟩ := (hK.range_v s).mpr fun ⟨h, h1⟩ => hr ⟨h ▸ valS_root hN.1 hZ.nonempty, h1⟩
    exact ⟨c, rfl⟩

/-- **The nodes of `(N⁺_Z)⁻`**: the nodes strictly below `LSA(Z)`, above a taxon of `Z`, that are not
chain nodes of the ancestral network on `Z`. -/
theorem mem_range_valR (v : V) :
    (∃ r, valR hN hZ hC ι r = v) ↔ v ∈ N.ancestralVertices Z ∧ ¬ ChainZ hN.1 hZ.nonempty v ∧
      N.graph.Reaches (lsa hN.1 Z hZ.nonempty) v ∧ v ≠ lsa hN.1 Z hZ.nonempty := by
  have hl := valC_lsa hN hZ hC ι κ hK
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨h₁, h₂⟩ := (mem_range_sdVert hC.1 hZ.coe_sort _).mp ⟨r, rfl⟩
    obtain ⟨hv, hnc, -⟩ := (mem_range_valC hN hZ ι κ hK _).mp ⟨_, rfl⟩
    refine ⟨hv, hnc, ?_, fun h => h₂ (valC_injective hN hZ ι κ hK (h.trans hl.symm))⟩
    rw [← hl]
    exact (valC_reaches_iff hN hZ ι κ hK _ _).mp h₁
  · rintro ⟨hv, hnc, hmv, hvm⟩
    have hr : ¬ v = N.root := fun h => hvm (eq_of_reaches_of_reaches hN.1.acyclic
      (h ▸ hN.1.root_reaches _) hmv)
    obtain ⟨c, rfl⟩ := (mem_range_valC hN hZ ι κ hK v).mpr ⟨hv, hnc, fun h => hr h.1⟩
    obtain ⟨r, rfl⟩ := (mem_range_sdVert hC.1 hZ.coe_sort c).mpr
      ⟨(valC_reaches_iff hN hZ ι κ hK _ _).mpr (hl ▸ hmv), fun h => hvm (h ▸ hl)⟩
    exact ⟨r, rfl⟩

/-- **The edges of `(N⁺_Z)⁻`**: the arcs below `LSA(Z)`, above a taxon of `Z`, out of nodes that are
not chain nodes, other than the arc out of `LSA(Z)` merged into the other. -/
theorem mem_range_valRE (f : E) :
    (∃ g, valRE hN hZ hC κ g = f) ↔ f ∈ N.ancestralArcs Z ∧
      ¬ ChainZ hN.1 hZ.nonempty (N.graph.source f) ∧
      N.graph.Reaches (lsa hN.1 Z hZ.nonempty) (N.graph.source f) ∧ f ≠ rootArcR hN hZ hC κ := by
  have hl := valC_lsa hN hZ hC ι κ hK
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨h₁, h₂⟩ := (mem_range_sdArc hC.1 hC.2 hZ.coe_sort _).mp ⟨g, rfl⟩
    obtain ⟨hf, hnc⟩ := (mem_range_valSE hN.1 hZ.nonempty _).mp ⟨_, rfl⟩
    refine ⟨hf, hnc, ?_, fun h => h₂ (valCE_injective hN hZ ι κ hK h)⟩
    rw [← hl]
    unfold valRE
    rw [← valC_source hN hZ ι κ hK]
    exact (valC_reaches_iff hN hZ ι κ hK _ _).mp h₁
  · rintro ⟨hf, hnc, hmf, hfr⟩
    obtain ⟨a, rfl⟩ := (mem_range_valSE hN.1 hZ.nonempty f).mpr ⟨hf, hnc⟩
    obtain ⟨e, rfl⟩ := (hK.range_e a).mpr fun ⟨hs, h1⟩ => by
      -- the root of `N` is then `LSA(Z)`, of outdegree two in the ancestral network
      have hsr : N.graph.source (valSE hN.1 hZ.nonempty a) = N.root :=
        (valS_source hN.1 hZ.nonempty a).symm.trans (hs ▸ valS_root hN.1 hZ.nonempty)
      have hmr : lsa hN.1 Z hZ.nonempty = N.root :=
        eq_of_reaches_of_reaches hN.1.acyclic (hsr ▸ hmf) (hN.1.root_reaches _)
      rw [suppress_outdegree, ancestral_outdegree hN.1 hZ.nonempty] at h1
      change ({e | N.graph.source e = N.root ∧ e ∈ N.ancestralArcs Z} : Set E).ncard = 1 at h1
      rw [← hmr, lsa_outdegree_ancestral hN.1 hN.2 hZ] at h1
      exact absurd h1 (by norm_num)
    have : Nonempty Z := hZ.coe_sort.to_nonempty
    have hreach : C.graph.Reaches (lsa hC.1 Set.univ Set.univ_nonempty) (C.graph.source e) := by
      refine (valC_reaches_iff hN hZ ι κ hK _ _).mpr ?_
      rw [hl, valC_source hN hZ ι κ hK]
      exact hmf
    obtain ⟨g, hg⟩ := (mem_range_sdArc hC.1 hC.2 hZ.coe_sort e).mpr ⟨hreach, fun h =>
      hfr (by rw [h]; rfl)⟩
    exact ⟨g, by rw [valRE, hg]; rfl⟩

open Classical in
theorem valR_source (g : SemidirectedArc hC.1 hC.2 hZ.coe_sort) :
    valR hN hZ hC ι ((semidirected hC.1 hC.2 hZ.coe_sort).graph.source g) =
      if N.graph.source (valRE hN hZ hC κ g) = lsa hN.1 Z hZ.nonempty then
        chainEndZ hN.1 hZ.nonempty (N.graph.target (rootArcR hN hZ hC κ))
      else N.graph.source (valRE hN hZ hC κ g) := by
  have hl := valC_lsa hN hZ hC ι κ hK
  have : Nonempty Z := hZ.coe_sort.to_nonempty
  unfold valR
  rw [sdVert_source]
  have key : C.graph.source (sdArc hC.1 hC.2 hZ.coe_sort g) =
      lsa hC.1 Set.univ Set.univ_nonempty ↔
        N.graph.source (valRE hN hZ hC κ g) = lsa hN.1 Z hZ.nonempty := by
    unfold valRE
    rw [← valC_source hN hZ ι κ hK, ← hl]
    exact (valC_injective hN hZ ι κ hK).eq_iff.symm
  split_ifs with h₁ h₂ h₂
  · rw [valC_target hN hZ ι κ hK]
    rfl
  · exact absurd (key.mp h₁) h₂
  · exact absurd (key.mpr h₂) h₁
  · rw [valC_source hN hZ ι κ hK]
    rfl

theorem valR_target (g : SemidirectedArc hC.1 hC.2 hZ.coe_sort) :
    valR hN hZ hC ι ((semidirected hC.1 hC.2 hZ.coe_sort).graph.target g) =
      chainEndZ hN.1 hZ.nonempty (N.graph.target (valRE hN hZ hC κ g)) := by
  unfold valR
  rw [sdVert_target, valC_target hN hZ ι κ hK]
  rfl

theorem valR_leaf (z : Z) :
    valR hN hZ hC ι ((semidirected hC.1 hC.2 hZ.coe_sort).leaf z) = N.leaf z := by
  unfold valR
  rw [sdVert_leaf, valC_leaf hN hZ ι κ hK]

theorem semidirectedR_isDirected_iff (g : SemidirectedArc hC.1 hC.2 hZ.coe_sort) :
    (semidirected hC.1 hC.2 hZ.coe_sort).IsDirected g ↔
      2 ≤ N.graph.indegree (chainEndZ hN.1 hZ.nonempty (N.graph.target (valRE hN hZ hC κ g))) :=
  (semidirected_isDirected_iff hC.1 hC.2 hZ.coe_sort g).trans
    (isHybridArc_iff_valC hN hZ hC ι κ hK _)

theorem rootArcR_spec :
    N.graph.source (rootArcR hN hZ hC κ) = lsa hN.1 Z hZ.nonempty ∧
      N.graph.indegree (chainEndZ hN.1 hZ.nonempty (N.graph.target (rootArcR hN hZ hC κ))) = 1 ∧
      rootArcR hN hZ hC κ ∈ N.ancestralArcs Z := by
  obtain ⟨h₁, h₂⟩ := sdRootArc_spec hC.1 hC.2 hZ.coe_sort
  refine ⟨?_, (isTreeArc_iff_valC hN hZ hC ι κ hK _).mp h₂,
    ((mem_range_valSE hN.1 hZ.nonempty _).mp ⟨_, rfl⟩).1⟩
  unfold rootArcR
  rw [← valC_source hN hZ ι κ hK, h₁, valC_lsa hN hZ hC ι κ hK]

end RSide

section Chains

variable {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X) {Z : Set X}
  (hZ : Z.Nontrivial) (h17 : Lemma17Conclusion hN Z hZ.nonempty)
  {VC EC : Type*} {C : RootedNetwork VC EC Z} (hC : IsBinaryRootedNetwork C)
  (ι : VC → {v : N.AncestralVertex Z //
    ¬ (N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).IsChainVertex v})
  (κ : EC → {e : N.AncestralArc Z // ¬ (N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).IsChainVertex
    ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).graph.source e)})
  (hK : IsContraction ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).suppress
    (N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty)) C ι κ)

/-- The arcs of `N` of an edge of `(N⁺_Z)⁻`: the chain of the ancestral network starting with its arc,
and, for the edge out of `LSA(Z)`, the chain starting with the other arc out of `LSA(Z)`. -/
def edgeArcsR (g : SemidirectedArc hC.1 hC.2 hZ.coe_sort) : Set E :=
  {e | e ∈ chainArcs hN.1 hZ.nonempty (valRE hN hZ hC κ g) ∨
    (N.graph.source (valRE hN hZ hC κ g) = lsa hN.1 Z hZ.nonempty ∧
      e ∈ chainArcs hN.1 hZ.nonempty (rootArcR hN hZ hC κ))}

/-- The chain of `K` of an edge of `(N⁺_Z)⁻`. -/
def chainOfR (g : SemidirectedArc hC.1 hC.2 hZ.coe_sort) :
    Set (trekEdges (semidirected hN.1 hN.2 hX) Z) :=
  valK hN hX ⁻¹' edgeArcsR hN hZ hC κ g

/-- The properties of a path of `K` that make it the chain of an edge of `(N⁺_Z)⁻`. -/
def IsChainTrail (g : SemidirectedArc hC.1 hC.2 hZ.coe_sort)
    (u w : keptNodes (semidirected hN.1 hN.2 hX) (trekEdges (semidirected hN.1 hN.2 hX) Z) Z)
    (S : Set (keptNodes (semidirected hN.1 hN.2 hX) (trekEdges (semidirected hN.1 hN.2 hX) Z) Z)) :
    Prop :=
  IsUTrail (trekNet hN hX Z).graph u w S (chainOfR hN hX hZ hC κ g) ∧
    valH hN hX u = valR hN hZ hC ι ((semidirected hC.1 hC.2 hZ.coe_sort).graph.source g) ∧
    valH hN hX w = valR hN hZ hC ι ((semidirected hC.1 hC.2 hZ.coe_sort).graph.target g) ∧
    (chainOfR hN hX hZ hC κ g).Nonempty ∧ IsBranch (trekNet hN hX Z) ∅ u ∧
    IsBranch (trekNet hN hX Z) ∅ w ∧ ∀ s ∈ S, s ≠ u → s ≠ w → ¬ IsBranch (trekNet hN hX Z) ∅ s

include h17 hK in
/-- **The chain of an edge of `(N⁺_Z)⁻` below `LSA(Z)`**: its arc, then the chain from its child. -/
theorem exists_chainTrail_of_ne (g : SemidirectedArc hC.1 hC.2 hZ.coe_sort)
    (hg : N.graph.source (valRE hN hZ hC κ g) ≠ lsa hN.1 Z hZ.nonempty) :
    ∃ u w S, IsChainTrail hN hX hZ hC ι κ g u w S := by
  have := hN.1.finite_vertices
  set m := lsa hN.1 Z hZ.nonempty
  set f := valRE hN hZ hC κ g
  obtain ⟨hf, hnc, hmf, hfr⟩ := (mem_range_valRE hN hZ hC ι κ hK f).mp ⟨g, rfl⟩
  have htf : N.graph.target f ∈ N.ancestralVertices Z := hf
  have hsf : N.graph.source f ∈ N.ancestralVertices Z := N.source_mem_ancestralVertices hf
  have hpath := IsDPath.cons f (isDPath_chainTail hN.1 hZ.nonempty htf)
  have hgood : ∀ s ∈ insert (N.graph.source f) (chainNodes hN.1 hZ.nonempty (N.graph.target f)),
      N.graph.Reaches m s ∧ s ∈ N.ancestralVertices Z ∧ s ≠ lsa hN.1 Set.univ Set.univ_nonempty := by
    rintro s (rfl | hs)
    · exact ⟨hmf, hsf, ne_lsa_univ hN hX hZ hmf (Or.inl hg)⟩
    · have hms : N.graph.Reaches m s := (hmf.tail ⟨f, rfl, rfl⟩).trans
        (reaches_of_mem_chainNodes hN.1 hZ.nonempty hs)
      have hsm : s ≠ m := by
        rintro rfl
        exact not_reaches_target_source' hN.1.acyclic f
          ((reaches_of_mem_chainNodes hN.1 hZ.nonempty hs).trans hmf)
      exact ⟨hms, hs.2.1, ne_lsa_univ hN hX hZ hms (Or.inl hsm)⟩
  obtain ⟨u, hu⟩ := exists_valH hN hX hZ h17 hmf hsf ((hgood _ (Set.mem_insert _ _)).2.2)
  have hend := Set.mem_insert_of_mem (N.graph.source f) (chainEndZ_mem_chainNodes hN.1 hZ.nonempty htf)
  obtain ⟨w, hw⟩ := exists_valH hN hX hZ h17 (hgood _ hend).1 (hgood _ hend).2.1 (hgood _ hend).2.2
  have hK' := isDPath_trekNet hN hX hZ h17 hpath hgood hu hw
  have hedges : valK hN hX ⁻¹' insert f (chainTailArcs hN.1 hZ.nonempty (N.graph.target f)) =
      chainOfR hN hX hZ hC κ g := by
    unfold chainOfR edgeArcsR
    congr 1
    ext e
    rw [← chainArcs_eq hN.1 hZ.nonempty hf]
    exact ⟨fun h => Or.inl h, fun h => h.elim id fun h' => absurd h'.1 hg⟩
  rw [hedges] at hK'
  have hwm : chainEndZ hN.1 hZ.nonempty (N.graph.target f) ≠ m := by
    intro h
    have h1 := reaches_of_mem_chainNodes hN.1 hZ.nonempty
      (chainEndZ_mem_chainNodes hN.1 hZ.nonempty htf)
    rw [h] at h1
    exact not_reaches_target_source' hN.1.acyclic f (h1.trans hmf)
  refine ⟨u, w, _, hK'.isUTrail (trekNet_isAcyclic hN hX), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · classical
    rw [valR_source hN hZ hC ι κ hK]
    split_ifs with h'
    · exact absurd h' hg
    · exact hu
  · rw [valR_target hN hZ hC ι κ hK, hw]
  · obtain ⟨e, he⟩ := exists_valK hN hX hZ h17 (e := f) ⟨hmf, hf⟩ fun h =>
      (hgood _ (Set.mem_insert _ _)).2.2 (h ▸ (sdRootArc_spec hN.1 hN.2 hX).1)
    exact ⟨e, by rw [← hedges]; exact Set.mem_preimage.mpr (he ▸ Set.mem_insert _ _)⟩
  · exact isBranch_of_not_chainZ hN hX hZ h17 u (by rw [hu]; exact hg) (by rw [hu]; exact hnc)
  · refine isBranch_of_not_chainZ hN hX hZ h17 w (by rw [hw]; exact hwm) ?_
    rw [hw]
    exact not_chainZ_chainEndZ hN.1 hZ.nonempty htf
  · intro s hs hsu hsw
    rcases hs with hs | hs
    · exact absurd (valH_injective hN hX (hs.trans hu.symm)) hsu
    · by_cases hse : valH hN hX s = chainEndZ hN.1 hZ.nonempty (N.graph.target f)
      · exact absurd (valH_injective hN hX (hse.trans hw.symm)) hsw
      · exact not_isBranch_of_chainZ hN hX hZ h17 s
          (chainZ_of_mem_chainNodes hN.1 hZ.nonempty hs hse)

end Chains

end Banos2019
