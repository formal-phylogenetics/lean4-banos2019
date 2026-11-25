module

public import Banos2019.Quartet.Normal
public import Phylogenetics.Graph.Tree

/-!
# The 4-cycles of `Q⁻_s` and the cycles of `N⁻` (Section 7, Lemmas 12 and 13)

A set `s` of four taxa induces a quartet network `Q⁻_s` with a 4-cycle exactly when `N⁻` has a cycle
`C_v` of size at least four that separates `s`: its four taxa are in distinct `v`-blocks, one in the
hybrid block. The hybrid node of the 4-cycle of `Q⁻_s` is then that of `C_v`.

* `exists_fourCycle_of_separates`, `exists_separates_of_fourCycle`: the two directions, as the proof
  of Lemma 12 states them.
* `unrooted_isConnected`: `N⁻` is connected.
* `walks_of_mem_cycleNodes`: two nodes of a cycle are joined along it.
* `exists_walks_cycleNodes_of_not_walks`: in a connected graph, a node not joined to a node `z₀` of a
  cycle `C'` by a walk avoiding a cycle `C`, disjoint from `C'`, reaches a node of `C` by a walk
  avoiding both (the argument of Lemma 13).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Walks -/

section Walks

variable {V' E' : Type*} (G : DirectedMultigraph V' E')

/-- Two nodes of a cycle are joined by a walk along its edges. -/
theorem walks_of_mem_cycleNodes {C : Set E'} (hC : IsCycle G C) {p q : V'}
    (hp : p ∈ cycleNodes G C) (hq : q ∈ cycleNodes G C) : G.Walks C p q := by
  obtain ⟨k, v, e, hcyc, hrange⟩ := hC
  -- every node of the cycle is joined to `v 0`
  have hpos := hcyc.pos
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have h₀ : ∀ i : Fin (m + 1), G.Walks C (v ⟨0, hpos⟩) (v i) := by
    intro i
    obtain ⟨i, hi⟩ := i
    induction i with
    | zero => exact .refl
    | succ n ih =>
      have hn : n < m + 1 := by omega
      refine (ih hn).tail ⟨e ⟨n, hn⟩, hrange ▸ ⟨_, rfl⟩, ?_⟩
      have hj := hcyc.joins ⟨n, hn⟩
      have hrot : finRotate (m + 1) ⟨n, hn⟩ = ⟨n + 1, hi⟩ := by
        rw [finRotate_of_lt (by omega)]
      rw [hrot] at hj
      rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨h₁, h₂⟩
  have hnode : ∀ r ∈ cycleNodes G C, ∃ i, v i = r := by
    rintro r ⟨f, hf, hr⟩
    rw [← hrange] at hf
    obtain ⟨i, rfl⟩ := hf
    rcases hcyc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hr with hr | hr
    · exact ⟨i, h₁.symm.trans hr⟩
    · exact ⟨finRotate (m + 1) i, h₂.symm.trans hr⟩
    · exact ⟨finRotate (m + 1) i, h₁.symm.trans hr⟩
    · exact ⟨i, h₂.symm.trans hr⟩
  obtain ⟨i, rfl⟩ := hnode p hp
  obtain ⟨j, rfl⟩ := hnode q hq
  exact (G.walks_symm (h₀ i)).trans (h₀ j)

/-- **The first node of a cycle on a walk** (the argument of Lemma 13): in a connected graph, take a
node `z₀` and a set `K` of edges whose ends are joined to `z₀` avoiding `C`. A node `p` that is not
joined to `z₀` by a walk avoiding `C` reaches a node of `C` by a walk avoiding `C` and `K`: follow a
walk from `p` to `z₀` up to its first edge of `C`. -/
theorem exists_walks_cycleNodes_of_not_walks (hG : G.IsConnected) {C K : Set E'} {z₀ : V'}
    (hK : ∀ f ∈ K, G.Walks Cᶜ (G.source f) z₀) {p : V'} (hp : ¬ G.Walks Cᶜ p z₀) :
    ∃ z ∈ cycleNodes G C, G.Walks (Cᶜ ∩ Kᶜ) p z := by
  have hw := hG p z₀
  induction hw using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd .refl hp
  | @head p q hpq _ ih =>
    obtain ⟨f, -, hf⟩ := hpq
    by_cases hfC : f ∈ C
    · refine ⟨p, ⟨f, hfC, ?_⟩, .refl⟩
      rcases hf with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · have hstep : G.AdjOn Cᶜ p q := ⟨f, hfC, hf⟩
      have hq : ¬ G.Walks Cᶜ q z₀ := fun h => hp (Relation.ReflTransGen.head hstep h)
      obtain ⟨z, hz, hqz⟩ := ih hq
      have hfK : f ∉ K := by
        intro hfK
        have hs := hK f hfK
        rcases hf with ⟨h₁, -⟩ | ⟨h₁, -⟩
        · exact hp (h₁ ▸ hs)
        · exact hq (h₁ ▸ hs)
      exact ⟨z, hz, Relation.ReflTransGen.head ⟨f, ⟨hfC, hfK⟩, hf⟩ hqz⟩

end Walks

/-! ### `N⁻` is connected -/

/-- **`N⁻` is connected**: every node is joined to the child of the edge of the root that suppression
merges, along a directed path from the root. -/
theorem unrooted_isConnected {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (hX : Nontrivial X) : (unrooted N hN hX).graph.IsConnected := by
  set M := lsaPlus hN.1 hX
  have hM : M.IsPhylogenetic := lsaPlus_isPhylogenetic hN.1 hX
  set e₀ := rootTreeArc hN.1 hN.2 hX
  have he₀ := (rootTreeArc_spec hN.1 hN.2 hX).1
  set t₀ : SemidirectedVertex hN.1 hX := ⟨M.graph.target e₀, hM.target_ne_root e₀⟩
  have key : ∀ w (hw : w ≠ M.root), (unrooted N hN hX).graph.Walks Set.univ t₀ ⟨w, hw⟩ := by
    intro w hw
    have hr := hM.root_reaches w
    induction hr with
    | refl => exact absurd rfl hw
    | @tail a b hra hab ih =>
      obtain ⟨f, hfs, hft⟩ := hab
      by_cases ha : a = M.root
      · by_cases hf : f = e₀
        · have : (⟨b, hw⟩ : SemidirectedVertex hN.1 hX) = t₀ :=
            Subtype.ext (show b = M.graph.target e₀ by rw [← hft, hf])
          rw [this]
          exact .refl
        · refine Relation.ReflTransGen.single ⟨⟨f, hf⟩, Set.mem_univ _, Or.inl ⟨?_, ?_⟩⟩
          · show (unrootAt M hM e₀).graph.source ⟨f, hf⟩ = t₀
            simp only [unrootAt]
            rw [dite_eq_left (hfs.trans ha)]
          · exact Subtype.ext hft
      · have hf : f ≠ e₀ := by
          rintro rfl
          exact ha (hfs.symm.trans he₀)
        refine (ih ha).tail ⟨⟨f, hf⟩, Set.mem_univ _, Or.inl ⟨?_, ?_⟩⟩
        · show (unrootAt M hM e₀).graph.source ⟨f, hf⟩ = ⟨a, ha⟩
          simp only [unrootAt]
          rw [dite_eq_right (by rw [hfs]; exact ha)]
          exact Subtype.ext hfs
        · exact Subtype.ext hft
  intro u w
  exact ((unrooted N hN hX).graph.walks_symm (key u.1 u.2)).trans (key w.1 w.2)

/-! ### The correspondence -/

/-- **Lemma 12, the cycle of `N⁻` gives the 4-cycle of `Q⁻_s`** (proof of Lemma 12): if `N⁻` has a
cycle `C_v` of size at least four for which the taxa of `s` are in distinct `v`-blocks, one of them in
the hybrid block, then `s` induces a quartet network with a 4-cycle: the edges of `C_v` that lie on
simple treks between taxa of `s` form a cycle of `(N⁻)_s`, through the four blocks of `s`. -/
theorem exists_fourCycle_of_separates {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) {C : Set _} {v : _}
    (hC4 : 4 ≤ C.ncard) (hC : IsCycle (unrooted N hN hX).graph C)
    (hv : IsHybridNodeOf (unrooted N hN hX) C v)
    (hblk : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y)
    (hdesc : ∃ x ∈ s, DescendsFrom (unrooted N hN hX) v x) :
    ∃ C' v' k, InducesCycleType (quartetLSA N hN.1 s hs) C' v' 4 k := by
  sorry

/-- **Lemma 12, the 4-cycle of `Q⁻_s` gives the cycle of `N⁻`** (proof of Lemma 12): if `Q⁻_s` has a
4-cycle with hybrid node `w`, then `N⁻` has a cycle of size at least four with hybrid node `w'`, the
same node of `N`, for which the taxa of `s` are in distinct `w'`-blocks, one of them descending from
`w'`: the cycle of `Q⁻_s` is made of chains of edges of a cycle of `N⁻`, and two taxa in distinct
blocks of `Q⁻_s` are in distinct blocks of `N⁻`. -/
theorem exists_separates_of_fourCycle {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) {C : Set _} {w : _}
    (hC : IsCycle (quartetUnrooted N hN s hs).graph C) (hC4 : C.ncard = 4)
    (hw : IsHybridNodeOf (quartetUnrooted N hN s hs) C w) :
    ∃ C' w', 4 ≤ C'.ncard ∧ IsCycle (unrooted N hN hX).graph C' ∧
      IsHybridNodeOf (unrooted N hN hX) C' w' ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C' x y) ∧
      (∃ x ∈ s, DescendsFrom (unrooted N hN hX) w' x) ∧ w'.1.1 = w.1.1.1.1 := by
  sorry

end Banos2019
