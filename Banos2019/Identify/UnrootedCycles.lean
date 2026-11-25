module

public import Banos2019.CycleProperty
public import Banos2019.Network.CycleFacts

/-!
# The cycles of `N⁻` (Baños 2019, Sections 3 and 8)

* `unrooted_isLevelOne`: `N⁻` is level-1 (connected: `unrooted_isConnected`, Quartet/Correspondence).
* `exists_isHybridNodeOf`, `IsHybridNodeOf.eq`, `IsHybridNodeOf.cycle_eq`: a cycle of `N⁻` has exactly
  one hybrid node, and a hybrid node lies on one cycle (Lemma 3).
* `exists_walks_compl_cycleNodes`: in a connected graph, every node is joined to a node of a cycle
  by a walk avoiding the cycle.
* `card_four_of_ne`, `injOn_four`: sets of four elements.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Cycles of a directed multigraph -/

section Multigraph

variable {G : DirectedMultigraph V E}

/-- Taxa in the same block of a set of edges are in the same block of a smaller set. -/
theorem SameBlock.mono {ℓ : X → V} {D D' : Set E} (hD : D ⊆ D') {x y : X}
    (h : SameBlock G ℓ D' x y) : SameBlock G ℓ D x y :=
  Relation.ReflTransGen.mono (fun _ _ ⟨f, hf, hl⟩ => ⟨f, fun hfD => hf (hD hfD), hl⟩) _ _ h

/-- A cycle has a node outside a set with fewer elements than the size of the cycle. -/
theorem IsCycle.exists_mem_cycleNodes_notMem {C : Set E} (hC : IsCycle G C) {F : Set V}
    (hF : F.Finite) (h : F.ncard < C.ncard) : ∃ u ∈ cycleNodes G C, u ∉ F :=
  Set.exists_mem_notMem_of_ncard_lt_ncard (by rwa [ncard_cycleNodes hC]) hF

end Multigraph

/-! ### Four distinct elements -/

section Four

variable {α β : Type*} [DecidableEq α]

/-- Four distinct elements make a set of four. -/
theorem card_four_of_ne {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : #({a, b, c, d} : Finset α) = 4 := by
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
    card_pair hcd]

/-- A map taking four elements to four distinct values is injective on them. -/
theorem injOn_four {f : α → β} {a b c d : α} (hab : f a ≠ f b) (hac : f a ≠ f c) (had : f a ≠ f d)
    (hbc : f b ≠ f c) (hbd : f b ≠ f d) (hcd : f c ≠ f d) :
    Set.InjOn f ↑({a, b, c, d} : Finset α) := by
  intro x hx y hy hxy
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first | rfl | exact absurd hxy ‹_› | exact absurd hxy.symm ‹_›

end Four

/-! ### `N⁻` is connected and level-1 -/

section Unrooted

variable {N : RootedNetwork V E X}

variable [Finite E]

/-- **`N⁻` is level-1**: two cycles sharing an edge share its ends, and two cycles with a common node
are the same (Lemma 3). -/
theorem unrooted_isLevelOne (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) : IsLevelOne (unrooted N hN hX).graph := by
  rintro C C' hC hC' ⟨f, hf, hf'⟩
  exact (lemma3_unrooted hN h1 hX hC).2.2 C' hC'
    ⟨_, ⟨f, hf, Or.inl rfl⟩, ⟨f, hf', Or.inl rfl⟩⟩

variable {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}

/-- **A cycle of `N⁻` has a hybrid node** (Lemma 3). -/
theorem exists_isHybridNodeOf (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) :
    ∃ v, IsHybridNodeOf (unrooted N hN hX) C v := by
  obtain ⟨⟨v, ⟨-, h₁, h₂, hne, hd₁, hd₂, ht₁, ht₂⟩, -⟩, h2, -⟩ := lemma3_unrooted hN h1 hX hC
  obtain ⟨v, hv, -⟩ := (lemma3_unrooted hN h1 hX hC).1
  obtain ⟨hvC, g₁, g₂, hne, hd₁, hd₂, ht₁, ht₂⟩ := hv
  exact ⟨v, g₁, h2 v hvC g₁ hd₁ ht₁, g₂, h2 v hvC g₂ hd₂ ht₂, hne, hd₁, hd₂, ht₁, ht₂⟩

/-- The hybrid node of a cycle is a node of the cycle. -/
theorem IsHybridNodeOf.mem_cycleNodes {V' E' X' : Type*} {G : SemidirectedNetwork V' E' X'}
    {C : Set E'} {v : V'} (hv : IsHybridNodeOf G C v) : v ∈ cycleNodes G.graph C := by
  obtain ⟨g, hg, -, -, -, -, -, hgt, -⟩ := hv
  exact ⟨g, hg, Or.inr hgt⟩

/-- **A cycle of `N⁻` has only one hybrid node** (Lemma 3). -/
theorem IsHybridNodeOf.eq (h1 : IsLevelOne N.graph) {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) {v v'}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hv' : IsHybridNodeOf (unrooted N hN hX) C v') :
    v = v' := by
  obtain ⟨v₀, -, huniq⟩ := (lemma3_unrooted hN h1 hX hC).1
  have key : ∀ u, IsHybridNodeOf (unrooted N hN hX) C u → u = v₀ := fun u hu => by
    obtain ⟨g₁, hg₁, g₂, hg₂, hne, hd₁, hd₂, ht₁, ht₂⟩ := hu
    exact huniq u ⟨⟨g₁, hg₁, Or.inr ht₁⟩, g₁, g₂, hne, hd₁, hd₂, ht₁, ht₂⟩
  rw [key v hv, key v' hv']

/-- **A hybrid node of `N⁻` lies on only one cycle** (Lemma 3). -/
theorem IsHybridNodeOf.cycle_eq (h1 : IsLevelOne N.graph) {C C' : Set _} (hC : IsCycle (unrooted N hN hX).graph C)
    (hC' : IsCycle (unrooted N hN hX).graph C') {v} (hv : IsHybridNodeOf (unrooted N hN hX) C v)
    (hv' : IsHybridNodeOf (unrooted N hN hX) C' v) : C = C' :=
  (lemma3_unrooted hN h1 hX hC).2.2 C' hC' ⟨v, hv.mem_cycleNodes, hv'.mem_cycleNodes⟩

end Unrooted

end Banos2019
