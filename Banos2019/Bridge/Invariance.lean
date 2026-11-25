module

public import Banos2019.Bridge.Suppress

/-!
# The constructions on semidirected networks are invariant under isomorphism

An isomorphism of semidirected networks keeps cycles and their sizes (`SDIso.isCycle_image_iff`),
semidirected paths and simple treks (`SDIso.isSimpleTrek`), so the edges on simple treks between
taxa (`SDIso.mem_trekEdges_iff`). It gives isomorphisms of the networks built from them: `restrict`,
`inducedUnrooted` (Definition 10), `contractCycles`, `undirectEdges` and `tildeNetwork` (Theorem 4).

The Challenge's copies of these definitions are the library's, up to isomorphism
(`Model.SDNetwork.inducedIso`, `Model.SDNetwork.tildeIso`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

section Invariance

variable {V' E' : Type*} {G : SemidirectedNetwork V E X} {G' : SemidirectedNetwork V' E' X}
  (ι : SDIso G G')

/-! ### Cycles -/

theorem SDIso.isCycle_image {C : Set E} (h : IsCycle G.graph C) : IsCycle G'.graph
    (ι.edge '' C) := by
  obtain ⟨k, v, e, ⟨hk, hj, hv, he⟩, rfl⟩ := h
  exact ⟨k, ι.vert ∘ v, ι.edge ∘ e,
    ⟨hk, fun i => ι.joins_of_joins (hj i), ι.vert.injective.comp hv, ι.edge.injective.comp he⟩,
    Set.range_comp _ _⟩

theorem SDIso.isCycle_image_iff (C : Set E) : IsCycle G'.graph (ι.edge '' C) ↔
    IsCycle G.graph C := by
  refine ⟨fun h => ?_, ι.isCycle_image⟩
  have := ι.symm.isCycle_image h
  rwa [show ι.symm.edge '' (ι.edge '' C) = C from ι.edge.symm_image_image C] at this

theorem SDIso.isCycle_iff_symm_image (C' : Set E') :
    IsCycle G'.graph C' ↔ IsCycle G.graph (ι.edge.symm '' C') := by
  rw [← ι.isCycle_image_iff, ι.edge.image_symm_image]

theorem SDIso.ncard_image (C : Set E) : (ι.edge '' C).ncard = C.ncard :=
  Set.ncard_image_of_injective _ ι.edge.injective

theorem SDIso.cycleNodes_image (C : Set E) :
    cycleNodes G'.graph (ι.edge '' C) = ι.vert '' cycleNodes G.graph C := by
  ext u'
  obtain ⟨u, rfl⟩ := ι.vert.surjective u'
  simp only [cycleNodes, Set.mem_ofPred_eq, Set.mem_image, ι.vert.apply_eq_iff_eq,
    exists_eq_right]
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, h⟩
    exact ⟨f, hf, (ι.incident_iff f u).mp h⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨_, ⟨f, hf, rfl⟩, (ι.incident_iff f u).mpr h⟩

include ι in
/-- **An isomorphism keeps the cycles of each size.** -/
theorem SDIso.exists_isCycle_ncard_iff (n : ℕ) :
    (∃ C, IsCycle G.graph C ∧ C.ncard = n) ↔ ∃ C', IsCycle G'.graph C' ∧ C'.ncard = n := by
  constructor
  · rintro ⟨C, hC, hn⟩
    exact ⟨_, ι.isCycle_image hC, (ι.ncard_image C).trans hn⟩
  · rintro ⟨C', hC', hn⟩
    refine ⟨ι.edge.symm '' C', (ι.isCycle_iff_symm_image C').mp hC', ?_⟩
    rw [← ι.ncard_image, ι.edge.image_symm_image, hn]

/-! ### Paths and treks -/

theorem SDIso.sdStep {f : E} {u w : V} (h : SDStep G f u w) :
    SDStep G' (ι.edge f) (ι.vert u) (ι.vert w) := by
  rcases h with ⟨h₁, h₂⟩ | ⟨hd, h₁, h₂⟩
  · by_cases hd : G.IsDirected f
    · have := ι.directed f hd
      exact Or.inl ⟨this.1.trans (congrArg _ h₁), this.2.trans (congrArg _ h₂)⟩
    · rcases ι.joins f with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
      · exact Or.inl ⟨k₁.trans (congrArg _ h₁), k₂.trans (congrArg _ h₂)⟩
      · exact Or.inr ⟨fun h => hd ((ι.isDirected_iff f).mp h), k₂.trans (congrArg _ h₁),
          k₁.trans (congrArg _ h₂)⟩
  · rcases ι.joins f with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
    · exact Or.inr ⟨fun h => hd ((ι.isDirected_iff f).mp h), k₂.trans (congrArg _ h₁),
        k₁.trans (congrArg _ h₂)⟩
    · exact Or.inl ⟨k₁.trans (congrArg _ h₁), k₂.trans (congrArg _ h₂)⟩

theorem SDIso.isSDPath {u w : V} {P : Set E} {S : Set V} (h : IsSDPath G u w P S) :
    IsSDPath G' (ι.vert u) (ι.vert w) (ι.edge '' P) (ι.vert '' S) := by
  obtain ⟨k, v, e, ⟨hs, hv⟩, h0, hl, rfl, rfl⟩ := h
  exact ⟨k, ι.vert ∘ v, ι.edge ∘ e, ⟨fun i => ι.sdStep (hs i), ι.vert.injective.comp hv⟩,
    by simp [h0], by simp [hl], Set.range_comp _ _, Set.range_comp _ _⟩

theorem SDIso.isSimpleTrek {x y t : V} {P₁ P₂ : Set E} (h : IsSimpleTrek G x y t P₁ P₂) :
    IsSimpleTrek G' (ι.vert x) (ι.vert y) (ι.vert t) (ι.edge '' P₁) (ι.edge '' P₂) := by
  obtain ⟨S₁, S₂, ⟨h₁, h₂⟩, hS⟩ := h
  refine ⟨_, _, ⟨ι.isSDPath h₁, ι.isSDPath h₂⟩, ?_⟩
  rw [← Set.image_inter ι.vert.injective, hS, Set.image_singleton]

theorem SDIso.mem_trekEdges_of_mem {Z : Set X} {f : E} (h : f ∈ trekEdges G Z) :
    ι.edge f ∈ trekEdges G' Z := by
  obtain ⟨x, hx, y, hy, t, P₁, P₂, ht, hf⟩ := h
  refine ⟨x, hx, y, hy, ι.vert t, ι.edge '' P₁, ι.edge '' P₂, ?_, ?_⟩
  · rw [ι.leaf, ι.leaf]
    exact ι.isSimpleTrek ht
  · rw [← Set.image_union]
    exact Set.mem_image_of_mem _ hf

/-- **An isomorphism keeps the edges on simple treks between taxa.** -/
theorem SDIso.mem_trekEdges_iff (Z : Set X) (f : E) :
    ι.edge f ∈ trekEdges G' Z ↔ f ∈ trekEdges G Z := by
  refine ⟨fun h => ?_, ι.mem_trekEdges_of_mem⟩
  have := ι.symm.mem_trekEdges_of_mem h
  rwa [show ι.symm.edge (ι.edge f) = f from ι.edge.symm_apply_apply f] at this

/-! ### Restriction and Definition 10 -/

/-- An isomorphism of the networks retaining corresponding sets of edges. -/
def SDIso.restrict {K : Set E} {K' : Set E'} (hK : ∀ f, ι.edge f ∈ K' ↔ f ∈ K) (Z : Set X) :
    SDIso (Banos2019.restrict G K Z) (Banos2019.restrict G' K' Z) where
  vert := ι.vert.subtypeEquiv fun u => by
    simp only [keptNodes, Set.mem_ofPred_eq]
    refine or_congr ⟨?_, ?_⟩ ?_
    · rintro ⟨f, hf, h⟩
      exact ⟨ι.edge f, (hK f).mpr hf, (ι.incident_iff f u).mpr h⟩
    · rintro ⟨f', hf', h⟩
      obtain ⟨f, rfl⟩ := ι.edge.surjective f'
      exact ⟨f, (hK f).mp hf', (ι.incident_iff f u).mp h⟩
    · simp only [ι.leaf, ι.vert.apply_eq_iff_eq]
  edge := ι.edge.subtypeEquiv fun f => (hK f).symm
  isDirected_iff f := ι.isDirected_iff f.1
  joins f := by
    unfold Joins
    simp only [Subtype.ext_iff, Equiv.subtypeEquiv_apply]
    exact ι.joins f.1
  directed f hf := by
    simp only [Subtype.ext_iff, Equiv.subtypeEquiv_apply]
    exact ι.directed f.1 hf
  leaf z := Subtype.ext (ι.leaf z.1)

/-- **An isomorphism of semidirected networks gives isomorphic induced unrooted networks**
(Definition 10). -/
def SDIso.inducedUnrooted [Finite E] (Z : Set X) :
    SDIso (Banos2019.inducedUnrooted G Z) (Banos2019.inducedUnrooted G' Z) :=
  (ι.restrict (ι.mem_trekEdges_iff Z) Z).suppressExcept fun _ => Iff.rfl

/-! ### Contraction and `Ñ` -/

variable {Q : Set E → Prop} {Q' : Set E' → Prop}
  (hQ : ∀ C, IsCycle G.graph C → (Q' (ι.edge '' C) ↔ Q C))
include hQ

theorem SDIso.contractRel_iff (u w : V) :
    ContractRel G'.graph Q' (ι.vert u) (ι.vert w) ↔ ContractRel G.graph Q u w := by
  constructor
  · rintro ⟨C', hC', hQC', hu, hw⟩
    have hC := (ι.isCycle_iff_symm_image C').mp hC'
    refine ⟨_, hC, (hQ _ hC).mp (by rwa [ι.edge.image_symm_image]), ?_, ?_⟩
    · rw [← ι.edge.image_symm_image C', ι.cycleNodes_image] at hu
      exact ι.vert.injective.mem_set_image.mp hu
    · rw [← ι.edge.image_symm_image C', ι.cycleNodes_image] at hw
      exact ι.vert.injective.mem_set_image.mp hw
  · rintro ⟨C, hC, hQC, hu, hw⟩
    refine ⟨_, ι.isCycle_image hC, (hQ C hC).mpr hQC, ?_, ?_⟩
    · rw [ι.cycleNodes_image]
      exact Set.mem_image_of_mem _ hu
    · rw [ι.cycleNodes_image]
      exact Set.mem_image_of_mem _ hw

theorem SDIso.notMem_contracted_iff (f : E) :
    (∀ C', IsCycle G'.graph C' → Q' C' → ι.edge f ∉ C') ↔ ∀ C, IsCycle G.graph C → Q C → f ∉ C := by
  constructor
  · intro h C hC hQC hf
    exact h _ (ι.isCycle_image hC) ((hQ C hC).mpr hQC) (Set.mem_image_of_mem _ hf)
  · intro h C' hC' hQC' hf
    have hC := (ι.isCycle_iff_symm_image C').mp hC'
    refine h _ hC ((hQ _ hC).mp (by rwa [ι.edge.image_symm_image])) ?_
    exact ⟨ι.edge f, hf, ι.edge.symm_apply_apply f⟩

/-- **An isomorphism gives isomorphic contracted networks**, when it keeps the cycles contracted. -/
def SDIso.contractCycles : SDIso (Banos2019.contractCycles G Q)
    (Banos2019.contractCycles G' Q') where
  vert := Quot.congr ι.vert fun a b => (ι.contractRel_iff hQ a b).symm
  edge := ι.edge.subtypeEquiv fun f => (ι.notMem_contracted_iff hQ f).symm
  isDirected_iff f := ι.isDirected_iff f.1
  joins f := by
    change Joins (Banos2019.contractCycles G' Q').graph _ (Quot.congr ι.vert _ (Quot.mk _ _))
      (Quot.congr ι.vert _ (Quot.mk _ _))
    rw [Quot.congr_mk, Quot.congr_mk]
    rcases ι.joins f.1 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨congrArg (Quot.mk _) h₁, congrArg (Quot.mk _) h₂⟩
    · exact Or.inr ⟨congrArg (Quot.mk _) h₁, congrArg (Quot.mk _) h₂⟩
  directed f hf := by
    change _ = Quot.congr ι.vert _ (Quot.mk _ _) ∧ _ = Quot.congr ι.vert _ (Quot.mk _ _)
    rw [Quot.congr_mk, Quot.congr_mk]
    have := ι.directed f.1 hf
    exact ⟨congrArg (Quot.mk _) this.1, congrArg (Quot.mk _) this.2⟩
  leaf x := by
    change Quot.mk _ _ = Quot.congr ι.vert _ (Quot.mk _ _)
    rw [Quot.congr_mk, ι.leaf]

theorem SDIso.contractCycles_edge_val (f) : ((ι.contractCycles hQ).edge f).1 = ι.edge f.1 := rfl

omit hQ

/-- An isomorphism of the networks forgetting the directions of corresponding edges. -/
def SDIso.undirectEdges {D : Set E} {D' : Set E'} (hD : ∀ f, ι.edge f ∈ D' ↔ f ∈ D) :
    SDIso (Banos2019.undirectEdges G D) (Banos2019.undirectEdges G' D') where
  vert := ι.vert
  edge := ι.edge
  isDirected_iff f := and_congr (ι.isDirected_iff f) (not_congr (hD f))
  joins f := ι.joins f
  directed f hf := ι.directed f hf.1
  leaf x := ι.leaf x

/-- **An isomorphism of semidirected networks gives isomorphic networks `Ñ`** (Theorem 4). -/
def SDIso.tildeNetwork [Finite E] : SDIso (Banos2019.tildeNetwork G) (Banos2019.tildeNetwork G') :=
  have hQ : ∀ C, IsCycle G.graph C → ((ι.edge '' C).ncard ≤ 3 ↔ C.ncard ≤ 3) := fun C _ => by
    rw [ι.ncard_image]
  let ι₁ := ι.contractCycles hQ
  let ι₂ := ι₁.undirectEdges (D := {e | ∃ C, IsCycle G.graph C ∧ C.ncard = 4 ∧ e.1 ∈ C})
    (D' := {e | ∃ C, IsCycle G'.graph C ∧ C.ncard = 4 ∧ e.1 ∈ C}) fun f => by
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨C', hC', h4, hf⟩
        refine ⟨_, (ι.isCycle_iff_symm_image C').mp hC', ?_,
          ⟨ι.edge f.1, hf, ι.edge.symm_apply_apply _⟩⟩
        rw [← ι.ncard_image, ι.edge.image_symm_image, h4]
      · rintro ⟨C, hC, h4, hf⟩
        exact ⟨_, ι.isCycle_image hC, (ι.ncard_image C).trans h4, Set.mem_image_of_mem _ hf⟩
  ι₂.suppressExcept fun _ => Iff.rfl

end Invariance

/-! ### The Challenge's Definition 10 and `Ñ` are the library's -/

namespace Model.SDNetwork

variable (G : Model.SDNetwork V E X)

theorem isPath_iff {u w : V} {P : Set E} {S : Set V} :
    G.IsPath u w P S ↔ IsSDPath G.toSD u w P S := by
  constructor
  · rintro ⟨k, v, e, hs, hv, h0, hl, hP, hS⟩
    exact ⟨k, v, e, ⟨hs, hv⟩, h0, hl, hP, hS⟩
  · rintro ⟨k, v, e, ⟨hs, hv⟩, h0, hl, hP, hS⟩
    exact ⟨k, v, e, hs, hv, h0, hl, hP, hS⟩

theorem isSimpleTrek_iff {x y t : V} {P₁ P₂ : Set E} :
    G.IsSimpleTrek x y t P₁ P₂ ↔ Banos2019.IsSimpleTrek G.toSD x y t P₁ P₂ := by
  simp only [IsSimpleTrek, Banos2019.IsSimpleTrek, IsTrek, isPath_iff, and_assoc]

/-- The network retaining the edges on simple treks, in Definition 10. -/
def inducedRestrict (Z : Set X) :=
  let K : Set E :=
    {e | ∃ x ∈ Z, ∃ y ∈ Z, ∃ t P₁ P₂, G.IsSimpleTrek (G.leaf x) (G.leaf y) t P₁ P₂ ∧ e ∈ P₁ ∪ P₂}
  let R : SDNetwork {u // (∃ e ∈ K, G.graph.source e = u ∨ G.graph.target e = u) ∨
      ∃ z ∈ Z, G.leaf z = u} K Z :=
    { graph :=
        { source := fun e => ⟨G.graph.source e.1, Or.inl ⟨e.1, e.2, Or.inl rfl⟩⟩
          target := fun e => ⟨G.graph.target e.1, Or.inl ⟨e.1, e.2, Or.inr rfl⟩⟩ }
      IsDirected := fun e => G.IsDirected e.1
      leaf := fun z => ⟨G.leaf z.1, Or.inr ⟨z.1, z.2, rfl⟩⟩ }
  R

theorem induced_eq (Z : Set X) : G.induced Z = (G.inducedRestrict Z).suppress := rfl

theorem mem_trekEdges_iff (Z : Set X) (f : E) :
    (∃ x ∈ Z, ∃ y ∈ Z, ∃ t P₁ P₂, G.IsSimpleTrek (G.leaf x) (G.leaf y) t P₁ P₂ ∧ f ∈ P₁ ∪ P₂) ↔
      f ∈ trekEdges G.toSD Z := by
  simp only [trekEdges, Set.mem_ofPred_eq, isSimpleTrek_iff]
  rfl

/-- The retained network of the Challenge is the library's. -/
def inducedRestrictIso (Z : Set X) :
    Banos2019.SDIso (G.inducedRestrict Z).toSD (restrict G.toSD (trekEdges G.toSD Z) Z) where
  vert := Equiv.subtypeEquivRight fun u => by
    simp only [keptNodes, Set.mem_ofPred_eq, ← mem_trekEdges_iff]
    rfl
  edge := Equiv.subtypeEquivRight fun f => G.mem_trekEdges_iff Z f
  isDirected_iff _ := Iff.rfl
  joins f := Or.inl ⟨rfl, rfl⟩
  directed _ _ := ⟨rfl, rfl⟩
  leaf _ := rfl

/-- **Definition 10 of the Challenge is the library's**, up to isomorphism. -/
def inducedIso [Finite E] (Z : Set X) :
    Banos2019.SDIso (G.induced Z).toSD (Banos2019.inducedUnrooted G.toSD Z) :=
  ((G.inducedRestrict Z).suppressIso ∅).trans
    ((G.inducedRestrictIso Z).suppressExcept fun _ => Iff.rfl)

/-- The network contracted and partly undirected, before the suppression of `Ñ`. -/
def tildePre :=
  let H := G.contract fun C => C.ncard ≤ 3
  let H' : SDNetwork _ _ X :=
    ⟨H.graph, fun e => H.IsDirected e ∧ ¬ ∃ C, G.graph.IsCycle C ∧ C.ncard = 4 ∧ e.1 ∈ C, H.leaf⟩
  H'

theorem tilde_eq : G.tilde = G.tildePre.suppress := rfl

theorem contractRel_iff (Q : Set E → Prop) (u w : V) :
    G.ContractRel Q u w ↔ Banos2019.ContractRel G.toSD.graph Q u w := by
  simp only [ContractRel, Banos2019.ContractRel, Digraph.isCycle_iff, Digraph.nodes_eq]
  rfl

/-- The contracted network of the Challenge is the library's. -/
def tildePreIso :
    Banos2019.SDIso G.tildePre.toSD (undirectEdges (contractCycles G.toSD fun C => C.ncard ≤ 3)
      {e | ∃ C, IsCycle G.toSD.graph C ∧ C.ncard = 4 ∧ e.1 ∈ C}) where
  vert := Quot.congr (Equiv.refl V) fun a b => G.contractRel_iff _ a b
  edge := Equiv.subtypeEquivRight fun f => by
    simp only [Digraph.isCycle_iff]
    rfl
  isDirected_iff f := by
    change (G.IsDirected f.1 ∧ ¬ ∃ C, IsCycle G.toSD.graph C ∧ C.ncard = 4 ∧ f.1 ∈ C) ↔
      G.IsDirected f.1 ∧ ¬ ∃ C, G.graph.IsCycle C ∧ C.ncard = 4 ∧ f.1 ∈ C
    simp only [Digraph.isCycle_iff]
    rfl
  joins _ := Or.inl ⟨rfl, rfl⟩
  directed _ _ := ⟨rfl, rfl⟩
  leaf _ := rfl

/-- **The network `Ñ` of the Challenge is the library's**, up to isomorphism. -/
def tildeIso [Finite E] : Banos2019.SDIso G.tilde.toSD (tildeNetwork G.toSD) :=
  (G.tildePre.suppressIso ∅).trans (G.tildePreIso.suppressExcept fun _ => Iff.rfl)

end Model.SDNetwork

end Banos2019
