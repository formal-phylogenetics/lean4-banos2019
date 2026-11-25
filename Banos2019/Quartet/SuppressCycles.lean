module

public import Banos2019.Quartet.RootContract

/-!
# The cycles of a suppressed network, with their types

When no node of indegree one and outdegree one of a network `M` is on a cycle, the cycles of the
suppressed network `M.suppress hM` are those of `M`, with the same arcs, the same hybrid nodes, the
same sizes and the same taxa below their hybrid nodes.

* `suppress_isCycle_image`, `exists_suppress_isCycle`: the two directions.
* `suppress_inducesCycleType_iff`, `ncard_setOf_isCycle_suppress`: the types and the number of the
  cycles.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} {M : RootedNetwork V E X} (hM : M.IsPhylogenetic)
  (hchain : ∀ D, IsCycle M.graph D → ∀ w ∈ cycleNodes M.graph D, ¬ M.IsChainVertex w)
include hM hchain

/-- **A cycle of the suppressed network is a cycle of `M`, on the same arcs**: the chains of its arcs
form a cycle of `M` (`isCycle_cycleChainArcs`), which passes through no chain node. -/
theorem suppress_isCycle_image {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    (hD : IsCycle (M.suppress hM).graph D) :
    IsCycle M.graph (Subtype.val '' D) ∧ cycleChainArcs M D = Subtype.val '' D := by
  have hcyc := isCycle_cycleChainArcs hM hD
  have heq : cycleChainArcs M D = Subtype.val '' D := by
    ext f
    constructor
    · rintro ⟨g, hg, hon⟩
      rcases hon with rfl | ⟨hc, hr⟩
      · exact ⟨g, hg, rfl⟩
      · exact absurd hc (hchain _ hcyc _ (source_mem_cycleNodes ⟨g, hg, Or.inr ⟨hc, hr⟩⟩))
    · rintro ⟨g, hg, rfl⟩
      exact val_mem_cycleChainArcs_iff.2 hg
  exact ⟨heq ▸ hcyc, heq⟩

/-- The arcs of a cycle of the suppressed network end at the ends of the same arcs in `M`. -/
theorem suppress_target_of_isCycle {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    (hD : IsCycle (M.suppress hM).graph D) {e : {e // ¬ M.IsChainVertex (M.graph.source e)}}
    (he : e ∈ D) : ((M.suppress hM).graph.target e).1 = M.graph.target e.1 := by
  have hcyc := (suppress_isCycle_image hM hchain hD).1
  exact chainEnd_eq_self hM (hchain _ hcyc _ (target_mem_cycleNodes ⟨e, he, rfl⟩))

/-- **Every cycle of `M` is a cycle of the suppressed network.** -/
theorem exists_suppress_isCycle {D : Set E} (hD : IsCycle M.graph D) :
    ∃ D', IsCycle (M.suppress hM).graph D' ∧ Subtype.val '' D' = D := by
  have hDψ : D ⊆ Set.range (Subtype.val : {e // ¬ M.IsChainVertex (M.graph.source e)} → E) :=
    fun f hf => ⟨⟨f, hchain _ hD _ (source_mem_cycleNodes hf)⟩, rfl⟩
  have hDφ : cycleNodes M.graph D ⊆ Set.range (Subtype.val : {v // ¬ M.IsChainVertex v} → V) :=
    fun w hw => ⟨⟨w, hchain _ hD _ hw⟩, rfl⟩
  refine ⟨_, hD.preimage (G' := (M.suppress hM).graph) Subtype.val Subtype.val
    Subtype.val_injective Subtype.val_injective hDψ hDφ (fun _ _ => rfl) (fun e he => ?_),
    Set.image_preimage_eq_of_subset hDψ⟩
  exact (chainEnd_eq_self hM (hchain _ hD _ (target_mem_cycleNodes he))).symm

/-- The nodes of a cycle of the suppressed network are its nodes in `M`. -/
theorem suppress_cycleNodes_image {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    (hD : IsCycle (M.suppress hM).graph D) :
    cycleNodes M.graph (Subtype.val '' D) = Subtype.val '' cycleNodes (M.suppress hM).graph D :=
  cycleNodes_image Subtype.val Subtype.val (fun _ _ => rfl)
    (fun _ he => (suppress_target_of_isCycle hM hchain hD he).symm)

/-- **The cycles of the suppressed network have the types of the cycles of `M`.** -/
theorem suppress_inducesCycleType_iff [Fintype V] [Fintype E] [Fintype X] {D : Set {e // ¬ M.IsChainVertex (M.graph.source e)}}
    {v : {v // ¬ M.IsChainVertex v}} {n k : ℕ} :
    InducesCycleType (M.suppress hM) D v n k ↔ InducesCycleType M (Subtype.val '' D) v.1 n k := by
  have hcyc : IsCycle (M.suppress hM).graph D ↔ IsCycle M.graph (Subtype.val '' D) := by
    refine ⟨fun hD => (suppress_isCycle_image hM hchain hD).1, fun hD => ?_⟩
    obtain ⟨D', hD', he⟩ := exists_suppress_isCycle hM hchain hD
    rwa [← Set.image_injective.2 Subtype.val_injective he]
  have hnodes : IsCycle (M.suppress hM).graph D → ∀ w : {v // ¬ M.IsChainVertex v},
      (w.1 ∈ cycleNodes M.graph (Subtype.val '' D) ↔ w ∈ cycleNodes (M.suppress hM).graph D) :=
    fun hD w => by
      rw [suppress_cycleNodes_image hM hchain hD]
      exact Subtype.val_injective.mem_set_image
  have hbelow : {x | (M.suppress hM).graph.Reaches v ((M.suppress hM).leaf x)} =
      {x | M.graph.Reaches v.1 (M.leaf x)} := by
    ext x
    exact suppress_reaches_iff hM v _
  unfold InducesCycleType
  rw [hbelow, Set.ncard_image_of_injective _ Subtype.val_injective, suppress_indegree hM]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨hcyc.1 h₁, (hnodes h₁ v).2 h₂, h₃, ?_, h₅⟩
    rw [← h₄]
    congr 2
    exact propext (hnodes h₁ (M.suppress hM).root)
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    have h₁' := hcyc.2 h₁
    refine ⟨h₁', (hnodes h₁' v).1 h₂, h₃, ?_, h₅⟩
    rw [← h₄]
    congr 2
    exact propext (hnodes h₁' (M.suppress hM).root).symm

/-- The cycles of the suppressed network and of `M` are as many. -/
theorem ncard_setOf_isCycle_suppress :
    {D | IsCycle (M.suppress hM).graph D}.ncard = {D | IsCycle M.graph D}.ncard := by
  rw [← Set.ncard_image_of_injective _ (Set.image_injective.2 Subtype.val_injective)]
  congr 1
  ext D
  constructor
  · rintro ⟨D', hD', rfl⟩
    exact (suppress_isCycle_image hM hchain hD').1
  · intro hD
    obtain ⟨D', hD', rfl⟩ := exists_suppress_isCycle hM hchain hD
    exact ⟨D', hD', rfl⟩

end Banos2019
