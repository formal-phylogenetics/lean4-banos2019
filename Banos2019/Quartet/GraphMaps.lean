module

public import Banos2019.Quartet.SemidirectedCycles
public import Banos2019.Network.Suppress

/-!
# Walks and cycles carried along maps of networks

* `IsCycle.image_of_hom`, `IsCycle.preimage_of_hom`, `walks_image_of_hom`: cycles and walks along an
  injective map of graphs.
* `isCycle_suppress_preimage`: the chains of a cycle of a level-1 network are a cycle of the
  suppressed network; `walks_suppress_chainEnd_of_walks`: a walk of the network gives a walk of the
  suppressed network.
* `sdNode`, `walks_semidirected_of_walks`, `isCycle_semidirected_preimage`: the node of `N⁻` of a node
  of `N` below `LSA(X)`; a walk, and a cycle, of `N` below `LSA(X)` give a walk, and a cycle, of `N⁻`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Maps of graphs -/

section Hom

variable {V₁ E₁ V₂ E₂ : Type*} {G₁ : DirectedMultigraph V₁ E₁} {G₂ : DirectedMultigraph V₂ E₂}
  {φ : V₁ → V₂} {ψ : E₁ → E₂} (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
  (hs : ∀ e, G₂.source (ψ e) = φ (G₁.source e)) (ht : ∀ e, G₂.target (ψ e) = φ (G₁.target e))
include hφ hψ hs ht

/-- The image of a cycle under an injective map of graphs is a cycle. -/
theorem IsCycle.image_of_hom {C : Set E₁} (hC : IsCycle G₁ C) : IsCycle G₂ (ψ '' C) := by
  obtain ⟨k, v, e, hc, rfl⟩ := hC
  refine ⟨k, φ ∘ v, ψ ∘ e, ⟨hc.pos, fun i => ?_, hφ.comp hc.injective_node,
    hψ.comp hc.injective_edge⟩, Set.range_comp ..⟩
  rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨by simp [hs, h₁], by simp [ht, h₂]⟩
  · exact Or.inr ⟨by simp [hs, h₁], by simp [ht, h₂]⟩

/-- A cycle of `G₂` whose edges are images of edges of `G₁` under an injective map of graphs is the
image of a cycle of `G₁`. -/
theorem IsCycle.preimage_of_hom {C : Set E₂} (hC : IsCycle G₂ C) (hCψ : C ⊆ Set.range ψ) :
    IsCycle G₁ (ψ ⁻¹' C) := by
  obtain ⟨k, v, e, hc, rfl⟩ := hC
  choose e' he' using fun i => hCψ ⟨i, rfl⟩
  have hv : ∀ i, ∃ u, φ u = v i := fun i => by
    rcases hc.joins i with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact ⟨G₁.source (e' i), by rw [← hs, he' i, h₁]⟩
    · exact ⟨G₁.target (e' i), by rw [← ht, he' i, h₂]⟩
  choose v' hv' using hv
  refine ⟨k, v', e', ⟨hc.pos, fun i => ?_, fun i j h => hc.injective_node (by rw [← hv', ← hv', h]),
    fun i j h => hc.injective_edge (by rw [← he', ← he', h])⟩, ?_⟩
  · rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨hφ (by rw [← hs, he', h₁, hv']), hφ (by rw [← ht, he', h₂, hv'])⟩
    · exact Or.inr ⟨hφ (by rw [← hs, he', h₁, hv']), hφ (by rw [← ht, he', h₂, hv'])⟩
  · ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (he' i).symm⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, hψ (by rw [he', hi])⟩

omit hφ hψ hs ht in
/-- A walk of `G₁` maps to a walk of `G₂`. -/
theorem walks_image_of_hom (hs : ∀ e, G₂.source (ψ e) = φ (G₁.source e))
    (ht : ∀ e, G₂.target (ψ e) = φ (G₁.target e)) {F : Set E₁} {a b : V₁}
    (h : G₁.Walks F a b) : G₂.Walks (ψ '' F) (φ a) (φ b) := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, hf, hj⟩ := hbc
    refine ih.tail ⟨ψ f, ⟨f, hf, rfl⟩, ?_⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by rw [hs, h₁], by rw [ht, h₂]⟩
    · exact Or.inr ⟨by rw [hs, h₁], by rw [ht, h₂]⟩

end Hom

/-! ### Cycles of a suppressed network from cycles of the network -/

section SuppressCycles

variable {M : RootedNetwork V E X} (hM : M.IsPhylogenetic)

/-- **A walk of the network gives a walk of the suppressed network** between the ends of the chains
of its ends, along the arcs of the walk that leave nodes that are not chain nodes. -/
theorem walks_suppress_chainEnd_of_walks {A : Set E}
    {F : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    (hA : ∀ f ∈ A, ∀ hf : ¬ M.IsChainVertex (M.graph.source f), (⟨f, hf⟩ : {e // ¬ M.IsChainVertex (M.graph.source e)}) ∈ F)
    {a b : V} (h : M.graph.Walks A a b) :
    (M.suppress hM).graph.Walks F ⟨chainEnd hM a, not_isChainVertex_chainEnd hM a⟩
      ⟨chainEnd hM b, not_isChainVertex_chainEnd hM b⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨g, hg, hj⟩ := hbc
    have key : (M.suppress hM).graph.Walks F
        ⟨chainEnd hM (M.graph.source g), not_isChainVertex_chainEnd hM _⟩
        ⟨chainEnd hM (M.graph.target g), not_isChainVertex_chainEnd hM _⟩ := by
      by_cases hgs : M.IsChainVertex (M.graph.source g)
      · have : (⟨chainEnd hM (M.graph.source g), not_isChainVertex_chainEnd hM _⟩ :
            {v // ¬ M.IsChainVertex v}) =
            ⟨chainEnd hM (M.graph.target g), not_isChainVertex_chainEnd hM _⟩ :=
          Subtype.ext (chainEnd_eq_of_adj hM hgs ⟨g, rfl, rfl⟩)
        rw [this]
        exact .refl
      · exact .single ⟨⟨g, hgs⟩, hA g hg hgs,
          Or.inl ⟨Subtype.ext (chainEnd_eq_self hM hgs).symm, rfl⟩⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₁ h₂
      exact ih.trans key
    · subst h₁ h₂
      exact ih.trans ((M.suppress hM).graph.walks_symm key)

/-- **A cycle of a level-1 network gives a cycle of the suppressed network**: the arcs of the
suppressed network whose first arc is on the cycle form a cycle, whose chains are the arcs of the
cycle. An arc out of the top of the cycle leaves a node that is not a chain node; the rest of the cycle
is a walk between its ends, which gives a walk of the suppressed network, closing a cycle through
it; the chains of that cycle are a cycle of the network sharing that arc, so they are the cycle. -/
theorem isCycle_suppress_preimage (h1 : IsLevelOne M.graph) {D : Set E} (hD : IsCycle M.graph D) :
    IsCycle (M.suppress hM).graph {g | g.1 ∈ D} ∧ cycleChainArcs M {g | g.1 ∈ D} = D := by
  have := hM.finite_arcs
  have hloop := source_ne_target_of_isPhylogenetic hM
  -- an arc of `D` out of the top of `D`, a node of outdegree at least two
  obtain ⟨t, htD, -, hin, -, -⟩ := h1.exists_top hM hD
  obtain ⟨f₁, hf₁, f₂, hf₂, hne, h₁, h₂⟩ := hD.exists_ne_of_mem (fun f _ => hloop f) htD
  have hs₁ : M.graph.source f₁ = t := h₁.resolve_right (hin f₁ hf₁)
  have hs₂ : M.graph.source f₂ = t := h₂.resolve_right (hin f₂ hf₂)
  have hg₀ : ¬ M.IsChainVertex (M.graph.source f₁) := by
    rintro ⟨-, hout⟩
    have h2 : 2 ≤ M.graph.outdegree (M.graph.source f₁) := by
      unfold DirectedMultigraph.outdegree
      rw [← Set.ncard_pair hne]
      exact Set.ncard_le_ncard (by
        rintro f (rfl | hf)
        · rfl
        · rw [Set.mem_singleton_iff.1 hf]
          exact hs₂.trans hs₁.symm) (Set.toFinite _)
    omega
  set g₀ : {e // ¬ M.IsChainVertex (M.graph.source e)} := ⟨f₁, hg₀⟩
  set F : Set {e // ¬ M.IsChainVertex (M.graph.source e)} := {g | g.1 ∈ D} \ {g₀}
  have hW := walks_suppress_chainEnd_of_walks hM (F := F) (A := D \ {f₁})
    (fun f hf hfc => ⟨hf.1, fun h => hf.2 (congrArg Subtype.val (Set.mem_singleton_iff.1 h))⟩)
    (hD.walks_sdiff_singleton hf₁ (target_mem_cycleNodes hf₁) (source_mem_cycleNodes hf₁))
  have hend : (⟨chainEnd hM (M.graph.source f₁), not_isChainVertex_chainEnd hM _⟩ :
      {v // ¬ M.IsChainVertex v}) = (M.suppress hM).graph.source g₀ :=
    Subtype.ext (chainEnd_eq_self hM hg₀)
  rw [hend] at hW
  obtain ⟨D', hD', hg₀D', hsub⟩ := exists_isCycle_of_walks (G := (M.suppress hM).graph)
    (e := g₀) (F := F) (fun h => h.2 rfl) hW
  have hsub' : D' ⊆ {g | g.1 ∈ D} := fun g hg => by
    rcases hsub hg with rfl | h
    · exact hf₁
    · exact h.1
  -- the chains of `D'` are `D`
  have hE : cycleChainArcs M D' = D :=
    h1 _ _ (isCycle_cycleChainArcs hM hD') hD ⟨f₁, ⟨g₀, hg₀D', Or.inl rfl⟩, hf₁⟩
  have hDD' : {g | g.1 ∈ D} = D' := Set.Subset.antisymm
    (fun g hg => val_mem_cycleChainArcs_iff.1 (hE.symm ▸ hg : g.1 ∈ cycleChainArcs M D')) hsub'
  rw [hDD']
  exact ⟨hD', hE⟩

/-- A node of a cycle of the suppressed network is a node of the cycle of the network formed by its
chains. -/
theorem val_mem_cycleNodes_cycleChainArcs {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    {u : {v // ¬ M.IsChainVertex v}} (hu : u ∈ cycleNodes (M.suppress hM).graph D) :
    u.1 ∈ cycleNodes M.graph (cycleChainArcs M D) := by
  obtain ⟨g, hg, hu | hu⟩ := hu
  · exact ⟨g.1, ⟨g, hg, Or.inl rfl⟩, Or.inl (congrArg Subtype.val hu)⟩
  · obtain ⟨l, hl, hlt⟩ := NMSC.exists_lastArc hM g.1
    exact ⟨l, ⟨g, hg, hl⟩, Or.inr (hlt.trans (congrArg Subtype.val hu))⟩

/-- A node of the network that is not a chain node, on the chains of a set of arcs of the suppressed
network, is a node of that set. -/
theorem mem_cycleNodes_suppress_of_val {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    {u : {v // ¬ M.IsChainVertex v}} (hu : u.1 ∈ cycleNodes M.graph (cycleChainArcs M D)) :
    u ∈ cycleNodes (M.suppress hM).graph D := by
  obtain ⟨f, ⟨g, hg, hon⟩, hfu | hfu⟩ := hu
  · have hfg : f = g.1 := eq_of_isOnChain_of_not_isChainVertex hon (by rw [hfu]; exact u.2)
    subst hfg
    exact ⟨g, hg, Or.inl (Subtype.ext hfu)⟩
  · refine ⟨g, hg, Or.inr (Subtype.ext ?_)⟩
    show chainEnd hM (M.graph.target g.1) = u.1
    rw [chainEnd_eq_of_chainReach_left hM (NMSC.IsOnChain.chainReach_target hon), hfu,
      chainEnd_eq_self hM u.2]

end SuppressCycles

/-! ### Walks and cycles of `N⁻` from those of `N` -/

section Semidirected

variable {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) (hB : M.IsBinary) (hX : Nontrivial X)

/-- The node of `N⁻` of a node of `M` below the LSA of all the taxa: itself, and for the LSA, which
`N⁻` suppresses, the child of the arc `sdRootArc` merged into the other arc out of the LSA. -/
def sdNode (u : V) : SemidirectedVertex hM hX :=
  if h : M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) u ∧
      u ≠ lsa hM Set.univ Set.univ_nonempty then
    ⟨⟨u, h.1, mem_ancestralVertices_univ hM u⟩, fun h' => h.2 (congrArg Subtype.val h')⟩
  else ⟨(lsaPlus hM hX).graph.target (rootTreeArc hM hB hX),
    (lsaPlus_isPhylogenetic hM hX).target_ne_root _⟩

theorem sdVert_sdNode {u : V} (h : M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) u)
    (hne : u ≠ lsa hM Set.univ Set.univ_nonempty) : sdVert hM hX (sdNode hM hB hX u) = u := by
  simp only [sdNode, h, ne_eq, hne, not_false_eq_true, and_self, ↓reduceDIte]
  rfl

theorem sdVert_sdNode_lsa :
    sdVert hM hX (sdNode hM hB hX (lsa hM Set.univ Set.univ_nonempty)) =
      M.graph.target (sdRootArc hM hB hX) := by
  simp only [sdNode, ne_eq, not_true_eq_false, and_false, dite_false]
  rfl

theorem sdNode_sdVert (w : SemidirectedVertex hM hX) : sdNode hM hB hX (sdVert hM hX w) = w :=
  sdVert_injective hM hX (sdVert_sdNode hM hB hX ((mem_range_sdVert hM hX _).1 ⟨w, rfl⟩).1
    ((mem_range_sdVert hM hX _).1 ⟨w, rfl⟩).2)

theorem sdNode_leaf (x : X) : sdNode hM hB hX (M.leaf x) = (semidirected hM hB hX).leaf x :=
  sdNode_sdVert hM hB hX ((semidirected hM hB hX).leaf x)

/-- The ends of an edge of `N⁻` are the nodes of `N⁻` of the ends of its arc. -/
theorem sdNode_source (g : SemidirectedArc hM hB hX) :
    (semidirected hM hB hX).graph.source g = sdNode hM hB hX (M.graph.source (sdArc hM hB hX g)) := by
  apply sdVert_injective hM hX
  rcases sdVert_source_cases hM hB hX g with ⟨hne, h⟩ | ⟨hm, h⟩
  · rw [h, sdVert_sdNode hM hB hX ((mem_range_sdArc hM hB hX _).1 ⟨g, rfl⟩).1 hne]
  · rw [h, hm, sdVert_sdNode_lsa]

theorem sdNode_target (g : SemidirectedArc hM hB hX) :
    (semidirected hM hB hX).graph.target g = sdNode hM hB hX (M.graph.target (sdArc hM hB hX g)) := by
  rw [← sdVert_target]
  exact (sdNode_sdVert hM hB hX _).symm

/-- **A walk of `M` below the LSA gives a walk of `N⁻`** between the nodes of `N⁻` of its ends: an arc
is an edge of `N⁻`, but for `sdRootArc`, whose two ends have the same node of `N⁻`. -/
theorem walks_semidirected_of_walks {A : Set E} {F : Set (SemidirectedArc hM hB hX)}
    (hA : ∀ f ∈ A, M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) (M.graph.source f))
    (hF : ∀ g, sdArc hM hB hX g ∈ A → g ∈ F) {a b : V} (h : M.graph.Walks A a b) :
    (semidirected hM hB hX).graph.Walks F (sdNode hM hB hX a) (sdNode hM hB hX b) := by
  have key : ∀ f ∈ A, (semidirected hM hB hX).graph.Walks F (sdNode hM hB hX (M.graph.source f))
      (sdNode hM hB hX (M.graph.target f)) := by
    intro f hf
    by_cases hf₀ : f = sdRootArc hM hB hX
    · have h₁ : sdNode hM hB hX (M.graph.source f) = sdNode hM hB hX (M.graph.target f) := by
        apply sdVert_injective hM hX
        have hm : M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) (M.graph.target f) :=
          (hA f hf).tail ⟨f, rfl, rfl⟩
        rw [hf₀, (sdRootArc_spec hM hB hX).1, sdVert_sdNode_lsa,
          sdVert_sdNode hM hB hX (hf₀ ▸ hm) (fun h => not_reaches_target_source_of_isAcyclic
            hM.acyclic (sdRootArc hM hB hX) (by rw [h, (sdRootArc_spec hM hB hX).1]; exact .refl))]
      rw [h₁]
      exact .refl
    · obtain ⟨g, rfl⟩ := (mem_range_sdArc hM hB hX f).2 ⟨hA f hf, hf₀⟩
      rw [← sdNode_source, ← sdNode_target]
      exact .single ⟨g, hF g hf, Or.inl ⟨rfl, rfl⟩⟩
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, hf, hj⟩ := hbc
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₁ h₂
      exact ih.trans (key f hf)
    · subst h₁ h₂
      exact ih.trans ((semidirected hM hB hX).graph.walks_symm (key f hf))

/-- **A cycle of a level-1 network below the LSA of all the taxa is the cycle of `M` of a cycle of
`N⁻`**: the edges of `N⁻` whose arcs are on the cycle. An edge `g₀` of it is closed into a cycle of
`N⁻` by the rest of the cycle (`walks_semidirected_of_walks`); the cycle of `M` of that cycle shares
an arc with the cycle, so it is the cycle. -/
theorem isCycle_semidirected_preimage (hbin : IsBinaryRootedNetwork M) (h1 : IsLevelOne M.graph)
    {D : Set E} (hD : IsCycle M.graph D)
    (hbelow : ∀ f ∈ D, M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) (M.graph.source f)) :
    IsCycle (semidirected hM hB hX).graph {g | sdArc hM hB hX g ∈ D} ∧
      liftEdges hM hB hX {g | sdArc hM hB hX g ∈ D} = D := by
  have := hM.finite_arcs
  set G := semidirected hM hB hX
  -- an edge of `N⁻` on the cycle: the cycle has two arcs
  obtain ⟨f₀, hf₀D, hf₀⟩ : ∃ f ∈ D, f ≠ sdRootArc hM hB hX := by
    obtain ⟨k, v, e, hc, rfl⟩ := hD
    have hk := hc.two_le (source_ne_target_of_binary hbin)
    by_cases h0 : e ⟨0, by omega⟩ = sdRootArc hM hB hX
    · refine ⟨e ⟨1, by omega⟩, ⟨_, rfl⟩, fun h => ?_⟩
      have := hc.injective_edge (h.trans h0.symm)
      simp at this
    · exact ⟨_, ⟨_, rfl⟩, h0⟩
  obtain ⟨g₀, rfl⟩ := (mem_range_sdArc hM hB hX f₀).2 ⟨hbelow _ hf₀D, hf₀⟩
  set F : Set (SemidirectedArc hM hB hX) := {g | sdArc hM hB hX g ∈ D} \ {g₀}
  have hW := walks_semidirected_of_walks hM hB hX (F := F) (A := D \ {sdArc hM hB hX g₀})
    (fun f hf => hbelow f hf.1)
    (fun g hg => ⟨hg.1, fun h => hg.2 (by rw [Set.mem_singleton_iff.1 h]; rfl)⟩)
    (hD.walks_sdiff_singleton hf₀D (target_mem_cycleNodes hf₀D) (source_mem_cycleNodes hf₀D))
  rw [← sdNode_source, ← sdNode_target] at hW
  obtain ⟨D', hD', hg₀D', hsub⟩ := exists_isCycle_of_walks (G := G.graph) (e := g₀) (F := F)
    (fun h => h.2 rfl) hW
  have hsub' : D' ⊆ {g | sdArc hM hB hX g ∈ D} := fun g hg => by
    rcases hsub hg with rfl | h
    · exact hf₀D
    · exact h.1
  have hE : liftEdges hM hB hX D' = D :=
    h1 _ _ (isCycle_liftEdges hM hB hX hD') hD ⟨_, (sdArc_mem_liftEdges_iff hM hB hX D' g₀).2 hg₀D',
      hf₀D⟩
  have hDD' : {g | sdArc hM hB hX g ∈ D} = D' := Set.Subset.antisymm
    (fun g hg => (sdArc_mem_liftEdges_iff hM hB hX D' g).1 (hE.symm ▸ hg)) hsub'
  rw [hDD']
  exact ⟨hD', hE⟩

end Semidirected

end Banos2019
