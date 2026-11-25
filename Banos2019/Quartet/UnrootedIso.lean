module

public import Banos2019.Bridge.Invariance
public import Banos2019.Quartet.Defs

/-!
# Isomorphisms of semidirected networks keep the types of cycles

An isomorphism of semidirected networks keeps the hybrid node of a cycle and the taxa descending
from a node, so it keeps the type `n_k` of a cycle (`SDIso.isCycleType_image`). Proposition 5
matches the cycles of `Q⁻` and of `Q̃⁻` this way.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X V' E' : Type*} {G : SemidirectedNetwork V E X} {G' : SemidirectedNetwork V' E' X}
  (ι : SDIso G G')

theorem SDIso.isHybridNodeOf_image {D : Set E} {v : V} (h : IsHybridNodeOf G D v) :
    IsHybridNodeOf G' (ι.edge '' D) (ι.vert v) := by
  obtain ⟨h₁, hh₁, h₂, hh₂, hne, hd₁, hd₂, ht₁, ht₂⟩ := h
  exact ⟨ι.edge h₁, Set.mem_image_of_mem _ hh₁, ι.edge h₂, Set.mem_image_of_mem _ hh₂,
    fun h => hne (ι.edge.injective h), (ι.isDirected_iff h₁).2 hd₁, (ι.isDirected_iff h₂).2 hd₂,
    (ι.directed h₁ hd₁).2.trans (congrArg _ ht₁), (ι.directed h₂ hd₂).2.trans (congrArg _ ht₂)⟩

theorem SDIso.descendsFrom_of {v : V} {x : X} (h : DescendsFrom G v x) :
    DescendsFrom G' (ι.vert v) x := by
  obtain ⟨P, S, hP⟩ := h
  have := ι.isSDPath hP
  rw [← ι.leaf] at this
  exact ⟨_, _, this⟩

theorem SDIso.descendsFrom_iff (v : V) (x : X) : DescendsFrom G' (ι.vert v) x ↔
    DescendsFrom G v x := by
  refine ⟨fun h => ?_, ι.descendsFrom_of⟩
  have := ι.symm.descendsFrom_of h
  rwa [show ι.symm.vert (ι.vert v) = v from ι.vert.symm_apply_apply v] at this

/-- **An isomorphism keeps the type of a cycle.** -/
theorem SDIso.isCycleType_image {D : Set E} {n k : ℕ} (h : IsCycleType G D n k) :
    IsCycleType G' (ι.edge '' D) n k := by
  obtain ⟨hD, hn, v, hv, hk⟩ := h
  refine ⟨ι.isCycle_image hD, (ι.ncard_image D).trans hn, ι.vert v, ι.isHybridNodeOf_image hv, ?_⟩
  rw [← hk]
  congr 1
  ext x
  exact ι.descendsFrom_iff v x

end Banos2019
