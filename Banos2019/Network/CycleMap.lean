module

public import Banos2019.Network.Cycle

/-!
# Cycles under maps of graphs

A map of the nodes and a map of the edges of two directed multigraphs that keep the ends of the edges
of a cycle carry the cycle to a cycle (`IsCycle.image`); conversely, a cycle whose edges and nodes are
images comes from a cycle (`IsCycle.preimage`).
-/

@[expose] public noncomputable section

open Phylogenetics

namespace Banos2019

variable {V E V' E' : Type*} {G : DirectedMultigraph V E} {G' : DirectedMultigraph V' E'}

/-- **The image of a cycle** under maps of the nodes and of the edges, injective on the cycle and
keeping the ends of its edges, is a cycle. -/
theorem IsCycle.image (φ : V' → V) (ψ : E' → E) {C : Set E'} (hC : IsCycle G' C)
    (hφ : Set.InjOn φ (cycleNodes G' C)) (hψ : Set.InjOn ψ C)
    (hs : ∀ e ∈ C, G.source (ψ e) = φ (G'.source e))
    (ht : ∀ e ∈ C, G.target (ψ e) = φ (G'.target e)) : IsCycle G (ψ '' C) := by
  obtain ⟨k, v, e, hc, rfl⟩ := hC
  have hv : ∀ i, v i ∈ cycleNodes G' (Set.range e) := fun i => by
    rw [hc.cycleNodes_eq]
    exact ⟨i, rfl⟩
  refine ⟨k, φ ∘ v, ψ ∘ e, ⟨hc.pos, fun i => ?_, fun i j h => ?_, fun i j h => ?_⟩,
    Set.range_comp ..⟩
  · rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by simp [hs _ ⟨i, rfl⟩, h₁], by simp [ht _ ⟨i, rfl⟩, h₂]⟩
    · exact Or.inr ⟨by simp [hs _ ⟨i, rfl⟩, h₁], by simp [ht _ ⟨i, rfl⟩, h₂]⟩
  · exact hc.injective_node (hφ (hv i) (hv j) h)
  · exact hc.injective_edge (hψ ⟨i, rfl⟩ ⟨j, rfl⟩ h)

/-- The nodes of the image of a cycle are the images of its nodes. -/
theorem cycleNodes_image (φ : V' → V) (ψ : E' → E) {C : Set E'}
    (hs : ∀ e ∈ C, G.source (ψ e) = φ (G'.source e))
    (ht : ∀ e ∈ C, G.target (ψ e) = φ (G'.target e)) :
    cycleNodes G (ψ '' C) = φ '' cycleNodes G' C := by
  ext u
  constructor
  · rintro ⟨f, ⟨e, he, rfl⟩, hu | hu⟩
    · exact ⟨_, ⟨e, he, Or.inl rfl⟩, (hs e he).symm.trans hu⟩
    · exact ⟨_, ⟨e, he, Or.inr rfl⟩, (ht e he).symm.trans hu⟩
  · rintro ⟨w, ⟨e, he, hw | hw⟩, rfl⟩
    · exact ⟨ψ e, ⟨e, he, rfl⟩, Or.inl (by rw [hs e he, hw])⟩
    · exact ⟨ψ e, ⟨e, he, rfl⟩, Or.inr (by rw [ht e he, hw])⟩

/-- **The preimage of a cycle** whose edges and nodes are images, under injective maps keeping the
ends of the edges, is a cycle. -/
theorem IsCycle.preimage (φ : V' → V) (ψ : E' → E) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) {D : Set E} (hD : IsCycle G D) (hDψ : D ⊆ Set.range ψ)
    (hDφ : cycleNodes G D ⊆ Set.range φ)
    (hs : ∀ e, ψ e ∈ D → G.source (ψ e) = φ (G'.source e))
    (ht : ∀ e, ψ e ∈ D → G.target (ψ e) = φ (G'.target e)) : IsCycle G' (ψ ⁻¹' D) := by
  obtain ⟨k, v, e, hc, rfl⟩ := hD
  have hv : ∀ i, v i ∈ Set.range φ := fun i => hDφ (by rw [hc.cycleNodes_eq]; exact ⟨i, rfl⟩)
  choose v' hv' using hv
  have he : ∀ i, e i ∈ Set.range ψ := fun i => hDψ ⟨i, rfl⟩
  choose e' he' using he
  have hmem : ∀ i, ψ (e' i) ∈ Set.range e := fun i => ⟨i, (he' i).symm⟩
  refine ⟨k, v', e', ⟨hc.pos, fun i => ?_, fun i j h => ?_, fun i j h => ?_⟩, ?_⟩
  · have hsi := hs (e' i) (hmem i)
    have hti := ht (e' i) (hmem i)
    rw [he' i] at hsi hti
    rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine Or.inl ⟨hφ ?_, hφ ?_⟩
      · rw [← hsi, h₁, hv']
      · rw [← hti, h₂, hv']
    · refine Or.inr ⟨hφ ?_, hφ ?_⟩
      · rw [← hsi, h₁, hv']
      · rw [← hti, h₂, hv']
  · exact hc.injective_node (by rw [← hv' i, ← hv' j, h])
  · exact hc.injective_edge (by rw [← he' i, ← he' j, h])
  · ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (he' i).symm⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, hψ ((he' i).trans hi)⟩

end Banos2019
