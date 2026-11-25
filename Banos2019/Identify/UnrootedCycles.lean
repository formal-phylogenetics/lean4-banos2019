module

public import Banos2019.CycleProperty
public import Banos2019.Network.CycleFacts

/-!
# The cycles of `N⁻` (Baños 2019, Sections 3 and 8)

* `isConnected_unrooted_graph`, `unrooted_isLevelOne`: `N⁻` is connected and level-1.
* `exists_isHybridNodeOf`, `IsHybridNodeOf.eq`, `IsHybridNodeOf.cycle_eq`: a cycle of `N⁻` has exactly
  one hybrid node, and a hybrid node lies on one cycle (Lemma 3).
* `exists_walks_compl_of_isConnected`: in a connected graph, every node is joined to a node of a cycle
  by a walk avoiding the cycle.
* `card_four_of_ne`, `injOn_four`, `distinct4_of_card_eq_four`: sets of four elements.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Cycles of a directed multigraph -/

section Multigraph

variable {G : DirectedMultigraph V E}

/-- The nodes of a cycle form a nonempty set. -/
theorem IsCycle.cycleNodes_nonempty {C : Set E} (hC : IsCycle G C) : (cycleNodes G C).Nonempty := by
  obtain ⟨k, v, e, hC, rfl⟩ := hC
  exact ⟨G.source (e ⟨0, hC.pos⟩), e ⟨0, hC.pos⟩, ⟨_, rfl⟩, Or.inl rfl⟩

/-- Taxa in the same block of a set of edges are in the same block of a smaller set. -/
theorem SameBlock.mono {ℓ : X → V} {D D' : Set E} (hD : D ⊆ D') {x y : X}
    (h : SameBlock G ℓ D' x y) : SameBlock G ℓ D x y :=
  Relation.ReflTransGen.mono (fun _ _ ⟨f, hf, hl⟩ => ⟨f, fun hfD => hf (hD hfD), hl⟩) _ _ h

/-- A cycle has a node outside a set with fewer elements than the size of the cycle. -/
theorem IsCycle.exists_mem_cycleNodes_notMem {C : Set E} (hC : IsCycle G C) {F : Set V}
    (hF : F.Finite) (h : F.ncard < C.ncard) : ∃ u ∈ cycleNodes G C, u ∉ F :=
  Set.exists_mem_notMem_of_ncard_lt_ncard (by rwa [ncard_cycleNodes hC]) hF

/-- **In a connected graph, every node is joined to a node of a cycle `C` by a walk avoiding the edges
of `C`**: along a walk to a node of `C`, stop at the first node of `C`. -/
theorem exists_walks_compl_of_isConnected (hG : G.IsConnected) {C : Set E} (hC : IsCycle G C)
    (a : V) : ∃ u ∈ cycleNodes G C, G.Walks Cᶜ u a := by
  obtain ⟨u₀, hu₀⟩ := hC.cycleNodes_nonempty
  have hw := hG a u₀
  induction hw using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨u₀, hu₀, .refl⟩
  | @head a b hab _ ih =>
    obtain ⟨u, hu, hub⟩ := ih
    obtain ⟨f, -, hf⟩ := hab
    by_cases hfC : f ∈ C
    · refine ⟨a, ?_, .refl⟩
      rcases hf with ⟨h, -⟩ | ⟨-, h⟩
      · exact ⟨f, hfC, Or.inl h⟩
      · exact ⟨f, hfC, Or.inr h⟩
    · exact ⟨u, hu, hub.tail ⟨f, hfC, hf.symm⟩⟩

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

/-- Four elements making a set of four are distinct. -/
theorem distinct4_of_card_eq_four {a b c d : α} (h : #({a, b, c, d} : Finset α) = 4) :
    Distinct4 a b c d := by
  have h3 : ∀ p q r : α, #({p, q, r} : Finset α) ≤ 3 := fun p q r => card_le_three
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · have := h3 a c d
    simp_all
  · have := h3 a b d
    rw [show ({a, b, a, d} : Finset α) = {a, b, d} by ext; simp; tauto] at h
    omega
  · have := h3 a b c
    rw [show ({a, b, c, a} : Finset α) = {a, b, c} by ext; simp; tauto] at h
    omega
  · have := h3 a b d
    rw [show ({a, b, b, d} : Finset α) = {a, b, d} by ext; simp] at h
    omega
  · have := h3 a b c
    rw [show ({a, b, c, b} : Finset α) = {a, b, c} by ext; simp; tauto] at h
    omega
  · have := h3 a b c
    rw [show ({a, b, c, c} : Finset α) = {a, b, c} by ext; simp] at h
    omega

/-- Four distinct elements make a set of four. -/
theorem card_eq_four_of_distinct4 {a b c d : α} (h : Distinct4 a b c d) :
    #({a, b, c, d} : Finset α) = 4 :=
  card_four_of_ne h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

end Four

/-! ### `N⁻` is connected and level-1 -/

section Unrooted

variable {N : RootedNetwork V E X}

/-- **`N⁻` is connected**: a directed path from the LSA to a node gives a walk from the child of the
edge of the LSA that suppression merges, through the merged edge when the path starts with the other
edge. -/
theorem isConnected_unrooted_graph (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X) :
    (unrooted N hN hX).graph.IsConnected := by
  set M := lsaPlus hN.1 hX
  have hM : M.IsPhylogenetic := lsaPlus_isPhylogenetic hN.1 hX
  set e₀ := rootTreeArc hN.1 hN.2 hX
  have he₀ := (rootTreeArc_spec hN.1 hN.2 hX).1
  set t₀ : SemidirectedVertex hN.1 hX := ⟨M.graph.target e₀, hM.target_ne_root e₀⟩
  have key : ∀ w (hw : w ≠ M.root), (unrooted N hN hX).graph.Walks Set.univ t₀ ⟨w, hw⟩ := by
    intro w hw
    induction hM.root_reaches w with
    | refl => exact absurd rfl hw
    | @tail a b _ hab ih =>
      obtain ⟨f, hfs, hft⟩ := hab
      by_cases ha : a = M.root
      · by_cases hf : f = e₀
        · have : (⟨b, hw⟩ : SemidirectedVertex hN.1 hX) = t₀ :=
            Subtype.ext (show b = M.graph.target e₀ by rw [← hft, hf])
          rw [this]
          exact .refl
        · refine .single ⟨⟨f, hf⟩, Set.mem_univ _, Or.inl ⟨?_, Subtype.ext hft⟩⟩
          show (unrootAt M hM e₀).graph.source ⟨f, hf⟩ = t₀
          simp only [unrootAt]
          rw [dite_eq_left (hfs.trans ha)]
      · have hf : f ≠ e₀ := by
          rintro rfl
          exact ha (hfs.symm.trans he₀)
        refine (ih ha).tail ⟨⟨f, hf⟩, Set.mem_univ _, Or.inl ⟨?_, Subtype.ext hft⟩⟩
        show (unrootAt M hM e₀).graph.source ⟨f, hf⟩ = ⟨a, ha⟩
        simp only [unrootAt]
        rw [dite_eq_right (by rw [hfs]; exact ha)]
        exact Subtype.ext hfs
  intro u w
  exact ((unrooted N hN hX).graph.walks_symm (key u.1 u.2)).trans (key w.1 w.2)

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
