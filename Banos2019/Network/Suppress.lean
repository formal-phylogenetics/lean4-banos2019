module

public import Banos2019.Network.CycleFacts
public import Phylogenetics.NMSC.InducedSuppress

/-!
# The cycles of a suppressed network

Suppressing the nodes of indegree one and outdegree one (`RootedNetwork.suppress`) replaces each
chain of arcs by its first arc. The arcs on the chains of the arcs of a cycle of the suppressed
network form a cycle of the network, so suppression keeps a network level-1; so does taking a part
of a network.

* `IsCycle.walks_sdiff_singleton`: two nodes of a cycle are joined along it, avoiding any one of its
  edges.
* `IsCycle.subset_of_pendant`, `IsCycle.superset_of_ncard_incident_le`: an edge with an end on no
  other edge is on no cycle; a cycle inside a connected set of edges with at most two edges at each
  node is all of it.
* `IsLevelOne.of_injective`: a subgraph of a level-1 graph is level-1.
* `cycleChainArcs`: the arcs of a network on the chains of a set of arcs of its suppressed network;
  `isCycle_cycleChainArcs`: for a cycle, they form a cycle. A cycle `D` of the network through the
  first arc of one chain, on these arcs, exists because a walk around the cycle closes it; it is all
  of them, because at each node there are at most two of them.
* `suppress_isLevelOne`: suppression keeps a network level-1.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-! ### Walks along a cycle, subgraphs -/

section Graph

variable {V' E' : Type*} {G : DirectedMultigraph V' E'}

/-- **Two nodes of a cycle are joined along the cycle without any one of its edges.** -/
theorem IsCycle.walks_sdiff_singleton {C : Set E'} (hC : IsCycle G C) {g : E'} (hg : g ∈ C)
    {a b : V'} (ha : a ∈ cycleNodes G C) (hb : b ∈ cycleNodes G C) : G.Walks (C \ {g}) a b := by
  obtain ⟨k, v, e, hcyc, rfl⟩ := hC
  obtain ⟨i, rfl⟩ := hg
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hcyc.pos; omega⟩
  -- the cycle read from `v (i + 1)`, whose last edge is `e i`, without that edge is a path
  have hrot := hcyc.rotate (i + 1)
  have hP := hrot.isPathOf
  have hlast : Fin.last n + (i + 1) = i := by
    rw [add_comm i 1, ← add_assoc, Fin.last_add_one, zero_add]
  have hP' : IsPathOf G (Set.range e \ {e i}) n (fun j => v (j + (i + 1)))
      (fun l => e (l.castSucc + (i + 1))) := by
    refine ⟨fun l => ⟨⟨_, rfl⟩, fun h => ?_⟩, hP.link, hP.injective⟩
    have h' := (hcyc.injective_edge (Set.mem_singleton_iff.1 h)).trans hlast.symm
    exact (Fin.castSucc_lt_last l).ne (add_right_cancel h')
  -- every node of the cycle is joined to `v (i + 1)`
  have hnode : ∀ w ∈ cycleNodes G (Set.range e),
      G.Walks (Set.range e \ {e i}) (v (0 + (i + 1))) w := by
    intro w hw
    rw [hcyc.cycleNodes_eq] at hw
    obtain ⟨j, rfl⟩ := hw
    have hj : v j = v ((j - (i + 1)) + (i + 1)) := by rw [sub_add_cancel]
    rw [hj]
    exact walks_mono (fun f hf => by obtain ⟨l, -, -, rfl⟩ := hf; exact hP'.mem l)
      (hP'.walks_of_le (Fin.zero_le _))
  exact (G.walks_symm (hnode a ha)).trans (hnode b hb)

/-- **A subgraph of a level-1 graph is level-1**: its cycles are cycles of the graph. -/
theorem IsLevelOne.of_injective {V'' E'' : Type*} {G' : DirectedMultigraph V'' E''}
    (h1 : IsLevelOne G) (φ : V'' → V') (ψ : E'' → E') (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (hs : ∀ e, G.source (ψ e) = φ (G'.source e))
    (ht : ∀ e, G.target (ψ e) = φ (G'.target e)) : IsLevelOne G' := by
  have hcyc : ∀ C, IsCycle G' C → IsCycle G (ψ '' C) := by
    rintro C ⟨k, v, e, hc, rfl⟩
    refine ⟨k, φ ∘ v, ψ ∘ e, ⟨hc.pos, fun i => ?_, hφ.comp hc.injective_node,
      hψ.comp hc.injective_edge⟩, Set.range_comp ..⟩
    rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by simp [hs, h₁], by simp [ht, h₂]⟩
    · exact Or.inr ⟨by simp [hs, h₁], by simp [ht, h₂]⟩
  intro C C' hC hC' ⟨f, hf, hf'⟩
  exact Set.image_injective.2 hψ
    (h1 _ _ (hcyc C hC) (hcyc C' hC') ⟨ψ f, ⟨f, hf, rfl⟩, ⟨f, hf', rfl⟩⟩)

/-- **An edge with an end on no other edge is on no cycle**: a node of a cycle is on two of its
edges. Here the edges are those of a set `K₁` containing the cycle. -/
theorem IsCycle.subset_of_pendant {D K K₁ : Set E'} (hD : IsCycle G D)
    (hloop : ∀ f, G.source f ≠ G.target f) (hDK₁ : D ⊆ K₁)
    (hK : ∀ f ∈ K₁, f ∉ K → ∃ p, (G.source f = p ∨ G.target f = p) ∧
      ∀ g ∈ K₁, (G.source g = p ∨ G.target g = p) → g = f) : D ⊆ K := by
  intro f hf
  by_contra hfK
  obtain ⟨p, hfp, hp⟩ := hK f (hDK₁ hf) hfK
  have hpD : p ∈ cycleNodes G D := by
    rcases hfp with h | h
    · exact h ▸ source_mem_cycleNodes hf
    · exact h ▸ target_mem_cycleNodes hf
  obtain ⟨f₁, hf₁, f₂, hf₂, hne, h₁, h₂⟩ := hD.exists_ne_of_mem (fun g _ => hloop g) hpD
  exact hne ((hp f₁ (hDK₁ hf₁) h₁).trans (hp f₂ (hDK₁ hf₂) h₂).symm)

/-- **A cycle inside a connected set of edges with at most two edges at each node is all of it**: at
a node of the cycle, its two edges are all the edges of the set there, so the walks on the set stay
on the cycle. -/
theorem IsCycle.superset_of_ncard_incident_le [Finite E'] {D K : Set E'} (hD : IsCycle G D)
    (hloop : ∀ f, G.source f ≠ G.target f) (hDK : D ⊆ K)
    (hdeg : ∀ x, {f | f ∈ K ∧ (G.source f = x ∨ G.target f = x)}.ncard ≤ 2) {x₀ : V'}
    (hx₀ : x₀ ∈ cycleNodes G D) (hconn : ∀ f ∈ K, G.Walks K x₀ (G.source f)) : K ⊆ D := by
  -- at a node of `D`, every edge of `K` is an edge of `D`
  have hstep : ∀ x ∈ cycleNodes G D, ∀ f ∈ K, (G.source f = x ∨ G.target f = x) → f ∈ D := by
    intro x hx f hf hfx
    have h₂ := hD.ncard_incident hloop hx
    have hsub : {f | f ∈ D ∧ (G.source f = x ∨ G.target f = x)} ⊆
        {f | f ∈ K ∧ (G.source f = x ∨ G.target f = x)} := fun f hf => ⟨hDK hf.1, hf.2⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (by have := hdeg x; omega) (Set.toFinite _)
    have hmem : f ∈ {f | f ∈ K ∧ (G.source f = x ∨ G.target f = x)} := ⟨hf, hfx⟩
    rw [← heq] at hmem
    exact hmem.1
  -- the walks on `K` from `x₀` stay at nodes of `D`
  have hreach : ∀ y, G.Walks K x₀ y → y ∈ cycleNodes G D := by
    intro y hy
    induction hy with
    | refl => exact hx₀
    | @tail b c _ hbc ih =>
      obtain ⟨f, hf, hl⟩ := hbc
      rcases hl with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact ht ▸ target_mem_cycleNodes (hstep _ ih f hf (Or.inl hs))
      · exact hs ▸ source_mem_cycleNodes (hstep _ ih f hf (Or.inr ht))
  exact fun f hf => hstep _ (hreach _ (hconn f hf)) f hf (Or.inl rfl)

end Graph

/-! ### The chains of a cycle of the suppressed network -/

section Suppress

variable {M : RootedNetwork V E X}

/-- The arcs of `M` on the chains of the arcs `C` of the suppressed network: an arc `g` of the
suppressed network is the first arc of its chain. -/
def cycleChainArcs (M : RootedNetwork V E X) (C : Set {e // ¬ M.IsChainVertex (M.graph.source e)}) :
    Set E :=
  {f | ∃ g ∈ C, M.IsOnChain g.1 f}

/-- An arc leaving a node that is not a chain node is the first arc of its chain. -/
theorem eq_of_isOnChain_of_not_isChainVertex {g f : E} (h : M.IsOnChain g f)
    (hf : ¬ M.IsChainVertex (M.graph.source f)) : f = g := by
  rcases h with h | ⟨hc, -⟩
  · exact h
  · exact absurd hc hf

/-- An arc is on the chain of only one arc of the suppressed network. -/
theorem eq_of_isOnChain_of_isOnChain {g h : {e // ¬ M.IsChainVertex (M.graph.source e)}} {f : E}
    (hg : M.IsOnChain g.1 f) (hh : M.IsOnChain h.1 f) : g = h :=
  Subtype.ext (IsOnChain.unique hg hh g.2 h.2)

/-- The first arc of the chain of `g` is on the chains of the arcs `C` exactly when `g ∈ C`. -/
theorem val_mem_cycleChainArcs_iff {C : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    {g : {e // ¬ M.IsChainVertex (M.graph.source e)}} : g.1 ∈ cycleChainArcs M C ↔ g ∈ C := by
  constructor
  · rintro ⟨h, hh, hon⟩
    rwa [eq_of_isOnChain_of_isOnChain (g := g) (h := h) (Or.inl rfl) hon]
  · exact fun hg => ⟨g, hg, Or.inl rfl⟩

/-- **Along a chain**: from the target of the first arc `g` of a chain to a node the chain reaches,
on the arcs of the chain other than `g`. -/
theorem walks_isOnChain_of_chainReach {g : E} (hg : ¬ M.IsChainVertex (M.graph.source g)) {a : V}
    (h : M.ChainReach (M.graph.target g) a) :
    M.graph.Walks {f | M.IsOnChain g f ∧ f ≠ g} (M.graph.target g) a := by
  induction h with
  | refl => exact .refl
  | @tail b c hb hbc ih =>
    obtain ⟨hcb, f, hfs, hft⟩ := hbc
    have hcf : M.IsChainVertex (M.graph.source f) := by rw [hfs]; exact hcb
    refine ih.tail ⟨f, ⟨Or.inr ⟨hcf, by rw [hfs]; exact hb⟩, ?_⟩, Or.inl ⟨hfs, hft⟩⟩
    rintro rfl
    exact hg hcf

variable (hM : M.IsPhylogenetic)

include hM in
/-- A network satisfying the network laws has no loop. -/
theorem source_ne_target_of_isPhylogenetic (e : E) : M.graph.source e ≠ M.graph.target e :=
  fun h => hM.acyclic _ (Relation.TransGen.single ⟨e, rfl, h.symm⟩)

/-- **A walk of the suppressed network gives a walk of the network**, on the chains of its arcs. -/
theorem walks_cycleChainArcs_of_walks {F : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    {u w : {v // ¬ M.IsChainVertex v}} (h : (M.suppress hM).graph.Walks F u w) :
    M.graph.Walks (cycleChainArcs M F) u.1 w.1 := by
  have key : ∀ g ∈ F, M.graph.Walks (cycleChainArcs M F) (M.graph.source g.1)
      (chainEnd hM (M.graph.target g.1)) := by
    intro g hg
    refine Relation.ReflTransGen.head ⟨g.1, ⟨g, hg, Or.inl rfl⟩, Or.inl ⟨rfl, rfl⟩⟩ ?_
    exact walks_mono (F := {f | M.IsOnChain g.1 f ∧ f ≠ g.1}) (F' := cycleChainArcs M F)
      (fun f hf => ⟨g, hg, hf.1⟩) (walks_isOnChain_of_chainReach g.2 (chainReach_chainEnd hM _))
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨g, hg, hl⟩ := hbc
    rcases hl with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hs' : M.graph.source g.1 = b.1 := congrArg Subtype.val hs
      have ht' : chainEnd hM (M.graph.target g.1) = c.1 := congrArg Subtype.val ht
      exact ih.trans (by rw [← hs', ← ht']; exact key g hg)
    · have hs' : M.graph.source g.1 = c.1 := congrArg Subtype.val hs
      have ht' : chainEnd hM (M.graph.target g.1) = b.1 := congrArg Subtype.val ht
      exact ih.trans (M.graph.walks_symm (by rw [← hs', ← ht']; exact key g hg))

/-- **At each node there are at most two arcs on the chains of a cycle of the suppressed network**:
a chain node has one arc in and one out; at another node `x`, an arc on the chain of `g` leaving `x`
is `g`, and one entering `x` is the last arc of the chain of `g`, which ends at `x`; and the cycle
has two arcs at `x`. -/
theorem ncard_incident_cycleChainArcs_le {C : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    (hC : IsCycle (M.suppress hM).graph C) (x : V) :
    {f | f ∈ cycleChainArcs M C ∧ (M.graph.source f = x ∨ M.graph.target f = x)}.ncard ≤ 2 := by
  classical
  have := hM.finite_arcs
  by_cases hx : M.IsChainVertex x
  · calc _ ≤ ({f | M.graph.source f = x} ∪ {f | M.graph.target f = x}).ncard :=
          Set.ncard_le_ncard (fun f (hf : f ∈ {f | f ∈ cycleChainArcs M C ∧
            (M.graph.source f = x ∨ M.graph.target f = x)}) => hf.2) (Set.toFinite _)
      _ ≤ {f | M.graph.source f = x}.ncard + {f | M.graph.target f = x}.ncard :=
          Set.ncard_union_le _ _
      _ = 2 := by
          have h₁ : M.graph.outdegree x = 1 := hx.2
          have h₂ : M.graph.indegree x = 1 := hx.1
          unfold DirectedMultigraph.outdegree at h₁
          unfold DirectedMultigraph.indegree at h₂
          rw [h₁, h₂]
  · set x' : {v // ¬ M.IsChainVertex v} := ⟨x, hx⟩
    choose last hlast_on hlast_tgt using NMSC.exists_lastArc hM
    let ψ : {e // ¬ M.IsChainVertex (M.graph.source e)} → E := fun g =>
      if M.graph.source g.1 = x then g.1 else last g.1
    have hsub : {f | f ∈ cycleChainArcs M C ∧ (M.graph.source f = x ∨ M.graph.target f = x)} ⊆
        ψ '' {g | g ∈ C ∧ ((M.suppress hM).graph.source g = x' ∨
          (M.suppress hM).graph.target g = x')} := by
      rintro f ⟨⟨h, hhC, hon⟩, hfx | hfx⟩
      · have hfe : f = h.1 := eq_of_isOnChain_of_not_isChainVertex hon (by rw [hfx]; exact hx)
        subst hfe
        refine ⟨h, ⟨hhC, Or.inl (Subtype.ext hfx)⟩, ?_⟩
        simp [ψ, hfx]
      · -- `f` enters `x`: the chain of `h` ends at `x`
        have hend : chainEnd hM (M.graph.target h.1) = x := by
          rw [chainEnd_eq_of_chainReach_left hM (NMSC.IsOnChain.chainReach_target hon), hfx,
            chainEnd_eq_self hM hx]
        have hnot : M.graph.source h.1 ≠ x := by
          intro hsx
          have hr := (NMSC.IsOnChain.chainReach_target hon).reaches
          rw [hfx] at hr
          exact hM.acyclic x (Relation.TransGen.head' ⟨h.1, hsx, rfl⟩ hr)
        refine ⟨h, ⟨hhC, Or.inr (Subtype.ext hend)⟩, ?_⟩
        simp only [ψ, hnot, ↓reduceIte]
        exact (IsOnChain.eq_of_target hon (hlast_on h.1) (by rw [hfx, hlast_tgt, hend])
          (by rw [hfx]; exact hx)).symm
    have hloop : ∀ e, (M.suppress hM).graph.source e ≠ (M.suppress hM).graph.target e :=
      source_ne_target_of_isPhylogenetic (suppress_isPhylogenetic hM)
    calc _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ _ := Set.ncard_image_le (Set.toFinite _)
      _ ≤ 2 := by
          by_cases hx' : x' ∈ cycleNodes (M.suppress hM).graph C
          · exact (hC.ncard_incident hloop hx').le
          · have : {g | g ∈ C ∧ ((M.suppress hM).graph.source g = x' ∨
                (M.suppress hM).graph.target g = x')} = ∅ :=
              Set.eq_empty_of_forall_notMem fun g hg => hx' ⟨g, hg.1, hg.2⟩
            rw [this, Set.ncard_empty]
            omega

/-- **The chains of the arcs of a cycle of the suppressed network form a cycle of the network.** -/
theorem isCycle_cycleChainArcs {C : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    (hC : IsCycle (M.suppress hM).graph C) : IsCycle M.graph (cycleChainArcs M C) := by
  have := hM.finite_arcs
  obtain ⟨g, hg⟩ : C.Nonempty := by
    obtain ⟨k, v, e, hcyc, rfl⟩ := hC
    exact ⟨e ⟨0, hcyc.pos⟩, ⟨_, rfl⟩⟩
  -- the arcs on the chains of `C` other than `g`
  set F := cycleChainArcs M C \ {g.1} with hF
  have hgF : g.1 ∉ F := fun h => h.2 rfl
  -- around the cycle from the end of the chain of `g` back to its start
  have hW : (M.suppress hM).graph.Walks (C \ {g}) ((M.suppress hM).graph.target g)
      ((M.suppress hM).graph.source g) :=
    hC.walks_sdiff_singleton hg (target_mem_cycleNodes hg) (source_mem_cycleNodes hg)
  have hW₁ : M.graph.Walks F (chainEnd hM (M.graph.target g.1)) (M.graph.source g.1) := by
    refine walks_mono (F := cycleChainArcs M (C \ {g})) (F' := F) (fun f hf => ?_)
      (walks_cycleChainArcs_of_walks hM hW)
    obtain ⟨h, ⟨hhC, hhg⟩, hon⟩ := hf
    refine ⟨⟨h, hhC, hon⟩, fun hfg => hhg ?_⟩
    rw [Set.mem_singleton_iff] at hfg ⊢
    subst hfg
    exact eq_of_isOnChain_of_isOnChain hon (Or.inl rfl)
  have hW₂ : M.graph.Walks F (M.graph.target g.1) (chainEnd hM (M.graph.target g.1)) :=
    walks_mono (F := {f | M.IsOnChain g.1 f ∧ f ≠ g.1}) (F' := F)
      (fun f hf => ⟨⟨g, hg, hf.1⟩, hf.2⟩)
      (walks_isOnChain_of_chainReach g.2 (chainReach_chainEnd hM _))
  -- a cycle `D` through `g`, on the chains of `C`
  obtain ⟨D, hD, hgD, hDsub⟩ := exists_isCycle_of_walks hgF (hW₂.trans hW₁)
  have hDsub' : D ⊆ cycleChainArcs M C := fun f hf => by
    rcases hDsub hf with rfl | hf
    · exact ⟨g, hg, Or.inl rfl⟩
    · exact hf.1
  -- every arc on the chains of `C` is reached from the start of `g` along them
  have hconn : ∀ f ∈ cycleChainArcs M C,
      M.graph.Walks (cycleChainArcs M C) (M.graph.source g.1) (M.graph.source f) := by
    rintro f ⟨h, hhC, hon⟩
    have hW₃ : M.graph.Walks (cycleChainArcs M C) (M.graph.source g.1) (M.graph.source h.1) :=
      walks_cycleChainArcs_of_walks hM (u := (M.suppress hM).graph.source g)
        (w := (M.suppress hM).graph.source h) (walks_mono Set.sdiff_subset
          (hC.walks_sdiff_singleton hg (source_mem_cycleNodes hg) (source_mem_cycleNodes hhC)))
    refine hW₃.trans ?_
    rcases hon with rfl | ⟨-, hr⟩
    · exact .refl
    · exact Relation.ReflTransGen.head ⟨h.1, ⟨h, hhC, Or.inl rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
        (walks_mono (F := {f | M.IsOnChain h.1 f ∧ f ≠ h.1}) (F' := cycleChainArcs M C)
          (fun f' hf' => ⟨h, hhC, hf'.1⟩) (walks_isOnChain_of_chainReach h.2 hr))
  have hsup := hD.superset_of_ncard_incident_le (source_ne_target_of_isPhylogenetic hM) hDsub'
    (ncard_incident_cycleChainArcs_le hM hC) (source_mem_cycleNodes hgD) hconn
  rw [hsup.antisymm hDsub']
  exact hD

/-- **Suppression keeps a network level-1**: two cycles of the suppressed network with a common arc
give two cycles of the network with a common arc, the chains of their arcs. -/
theorem suppress_isLevelOne (h1 : IsLevelOne M.graph) : IsLevelOne (M.suppress hM).graph := by
  intro C C' hC hC' ⟨g, hg, hg'⟩
  have hE := h1 _ _ (isCycle_cycleChainArcs hM hC) (isCycle_cycleChainArcs hM hC')
    ⟨g.1, ⟨g, hg, Or.inl rfl⟩, ⟨g, hg', Or.inl rfl⟩⟩
  ext h
  rw [← val_mem_cycleChainArcs_iff (M := M), ← val_mem_cycleChainArcs_iff (M := M), hE]

end Suppress

end Banos2019
