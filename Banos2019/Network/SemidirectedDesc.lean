module

public import Banos2019.Network.SuppressIso
public import Banos2019.Basic.Logic.EquivOfInjective
public import Phylogenetics.NMSC.InducedParams

/-!
# The semidirected network of a binary network, in the terms of the network

The nodes of `semidirected M` are the nodes of `M` strictly below the LSA `ℓ` of all the taxa, and
its edges are the arcs of `M` below `ℓ` other than `rootTreeArc`. An edge keeps its target; its
source is its source in `M`, or the child of `rootTreeArc` for the other arc out of `ℓ`; it is hybrid
when it is a hybrid arc of `M`.

* `sdVert`, `sdArc`: the node and the arc of `M` of a node and an edge of `semidirected M`, with
  their images (`mem_range_sdVert`, `mem_range_sdArc`) and the ends, hybrid edges and taxa
  (`sdVert_source`, `sdVert_target`, `semidirected_isDirected_iff`, `sdVert_leaf`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

section Desc

variable {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) (hB : M.IsBinary) (hX : Nontrivial X)

/-- The node of `M` of a node of `semidirected M`. -/
def sdVert (v : SemidirectedVertex hM hX) : V := v.1.1

/-- The arc of `M` of an edge of `semidirected M`. -/
def sdArc (e : SemidirectedArc hM hB hX) : E := e.1.1

/-- The arc out of the LSA that is merged into the other. -/
def sdRootArc : E := (rootTreeArc hM hB hX).1

theorem sdVert_injective : Function.Injective (sdVert hM hX) := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

theorem sdArc_injective : Function.Injective (sdArc hM hB hX) := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

theorem lsaPlus_root_val : (lsaPlus hM hX).root.1 = lsa hM Set.univ Set.univ_nonempty := rfl

theorem mem_range_sdVert (v : V) :
    (∃ u, sdVert hM hX u = v) ↔
      M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) v ∧
        v ≠ lsa hM Set.univ Set.univ_nonempty := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.1.2.1, fun h => u.2 (Subtype.ext h)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨⟨v, h₁, mem_ancestralVertices_univ hM v⟩, fun h => h₂ (congrArg Subtype.val h)⟩, rfl⟩

theorem sdRootArc_spec :
    M.graph.source (sdRootArc hM hB hX) = lsa hM Set.univ Set.univ_nonempty ∧
      M.IsTreeArc (sdRootArc hM hB hX) := by
  obtain ⟨h₁, h₂⟩ := rootTreeArc_spec hM hB hX
  refine ⟨congrArg Subtype.val h₁, ?_⟩
  exact (belowNetwork_isTreeArc_iff (hl := lsa_mem_ancestralVertices hM Set.univ_nonempty)
    (hleaf := fun _ hx => (lsa_spec hM Set.univ Set.univ_nonempty).1.reaches_leaf hM hx) hM
    (lsa_spec hM Set.univ Set.univ_nonempty).1 _).mp h₂

theorem mem_range_sdArc (e : E) :
    (∃ g, sdArc hM hB hX g = e) ↔
      M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) (M.graph.source e) ∧
        e ≠ sdRootArc hM hB hX := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1.2.1, fun h => g.2 (Subtype.ext h)⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨⟨e, h₁, mem_ancestralVertices_univ hM _⟩, fun h => h₂ (congrArg Subtype.val h)⟩, rfl⟩

open Classical in
theorem sdVert_source (g : SemidirectedArc hM hB hX) :
    sdVert hM hX ((semidirected hM hB hX).graph.source g) =
      if M.graph.source (sdArc hM hB hX g) = lsa hM Set.univ Set.univ_nonempty then
        M.graph.target (sdRootArc hM hB hX)
      else M.graph.source (sdArc hM hB hX g) := by
  have key : (lsaPlus hM hX).graph.source g.1 = (lsaPlus hM hX).root ↔
      M.graph.source (sdArc hM hB hX g) = lsa hM Set.univ Set.univ_nonempty :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  simp only [semidirected, unrootAt, sdVert]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (key.mp h₁) h₂
  · exact absurd (key.mpr h₂) h₁
  · rfl

theorem sdVert_target (g : SemidirectedArc hM hB hX) :
    sdVert hM hX ((semidirected hM hB hX).graph.target g) = M.graph.target (sdArc hM hB hX g) :=
  rfl

theorem sdVert_leaf (x : X) : sdVert hM hX ((semidirected hM hB hX).leaf x) = M.leaf x := rfl

theorem semidirected_isDirected_iff (g : SemidirectedArc hM hB hX) :
    (semidirected hM hB hX).IsDirected g ↔ M.IsHybridArc (sdArc hM hB hX g) :=
  belowNetwork_isHybridArc_iff (hl := lsa_mem_ancestralVertices hM Set.univ_nonempty)
    (hleaf := fun _ hx => (lsa_spec hM Set.univ Set.univ_nonempty).1.reaches_leaf hM hx) hM
    (lsa_spec hM Set.univ Set.univ_nonempty).1 g.1

open Classical in
/-- The length of an edge of `semidirected M`: that of its arc, plus that of `rootTreeArc` for the
edge out of the LSA. -/
theorem semidirectedMetric_length (θ : MetricData E) (g : SemidirectedArc hM hB hX) :
    (semidirectedMetric hM hB hX θ).length g =
      if M.graph.source (sdArc hM hB hX g) = lsa hM Set.univ Set.univ_nonempty then
        θ.length (sdArc hM hB hX g) + θ.length (sdRootArc hM hB hX)
      else θ.length (sdArc hM hB hX g) := by
  have key : (lsaPlus hM hX).graph.source g.1 = (lsaPlus hM hX).root ↔
      M.graph.source (sdArc hM hB hX g) = lsa hM Set.univ Set.univ_nonempty :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  simp only [semidirectedMetric]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (key.mp h₁) h₂
  · exact absurd (key.mpr h₂) h₁
  · rfl

theorem semidirectedMetric_inheritance (θ : MetricData E) (g : SemidirectedArc hM hB hX) :
    (semidirectedMetric hM hB hX θ).inheritance g = θ.inheritance (sdArc hM hB hX g) := rfl

/-- The nodes of `semidirected M`, as the nodes of `M` strictly below the LSA. -/
def sdVertEquiv : SemidirectedVertex hM hX ≃
    {v : V // M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) v ∧
      v ≠ lsa hM Set.univ Set.univ_nonempty} :=
  Equiv.ofInjectiveSubtype (sdVert hM hX) (sdVert_injective hM hX) _ fun v => (mem_range_sdVert hM hX v).symm

/-- The edges of `semidirected M`, as the arcs of `M` below the LSA other than `sdRootArc`. -/
def sdArcEquiv : SemidirectedArc hM hB hX ≃
    {e : E // M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) (M.graph.source e) ∧
      e ≠ sdRootArc hM hB hX} :=
  Equiv.ofInjectiveSubtype (sdArc hM hB hX) (sdArc_injective hM hB hX) _ fun e =>
    (mem_range_sdArc hM hB hX e).symm

/-- The LSA of all the taxa has outdegree two, and its arcs are below it. -/
theorem lsa_univ_outdegree (hM : M.IsPhylogenetic) (hB : M.IsBinary) [Nontrivial X] :
    M.graph.outdegree (lsa hM Set.univ Set.univ_nonempty) = 2 := by
  have := hM.finite_arcs
  have h := lsaNetwork_outdegree_root hM hB (Set.nontrivial_univ (α := X))
  have hge : 2 ≤ M.graph.outdegree (lsa hM Set.univ Set.univ_nonempty) := by
    have := belowNetwork_outdegree_le (N := M) (l := lsa hM Set.univ Set.univ_nonempty)
      (Y := Set.univ) (hl := lsa_mem_ancestralVertices hM Set.univ_nonempty)
      (hleaf := fun _ hx => (lsa_spec hM Set.univ Set.univ_nonempty).1.reaches_leaf hM hx)
      (lsaNetwork hM Set.univ Set.univ_nonempty).root
    change _ ≤ M.graph.outdegree (lsa hM Set.univ Set.univ_nonempty) at this
    have h' : (M.belowNetwork (lsa hM Set.univ Set.univ_nonempty) Set.univ
        (lsa_mem_ancestralVertices hM Set.univ_nonempty)
        fun _ hx => (lsa_spec hM Set.univ Set.univ_nonempty).1.reaches_leaf hM hx).graph.outdegree
          (lsaNetwork hM Set.univ Set.univ_nonempty).root = 2 := h
    omega
  have hle : M.graph.outdegree (lsa hM Set.univ Set.univ_nonempty) ≤ 2 := by
    by_cases hr : lsa hM Set.univ Set.univ_nonempty = M.root
    · rw [hr, hB.1]
    · have h₁ := hM.nonroot_indegree _ hr
      have h₂ := hB.2 _ hr (by omega)
      omega
  omega

end Desc

end Banos2019
