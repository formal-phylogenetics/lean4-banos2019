module

public import Banos2019.Identify.Blocks
public import Banos2019.Basic.Data.Finset.Card

/-!
# The order of the blocks around a cycle of `N⁻` (Baños 2019, Lemma 16)

* `blockNodes`, `JoinedAvoiding`: the blocks of `x` and `y` are joined along `C` avoiding the blocks
  of the taxa `T`.
* `adjacentBlocks_iff_forall_joinedAvoiding`: two blocks of a cycle of size at least four are
  adjacent exactly when they are so joined, avoiding the other two blocks, for every set of four
  taxa separated by the cycle that contains them.
* `IsCycleOf.eq_or_eq_of_joins`, `IsCycleOf.ne_of_joins`, `IsCycle.exists_isCycleOf_apply_zero`,
  `IsCycleOf.mem_image_Ioo_iff_of_reflTransGen`: the ends of the edges of a cycle, reading a cycle
  from a given node, and walks along a cycle that avoid two of its nodes.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### The arcs of a cycle of a directed multigraph -/

section CycleArc

variable {G : DirectedMultigraph V E}

/-- **An edge of a cycle joins exactly its two consecutive nodes**, in one order or the other. -/
theorem IsCycleOf.eq_or_eq_of_joins {k : ℕ} {v : Fin k → V} {e : Fin k → E}
    (hC : IsCycleOf G k v e) {l : Fin k} {u w : V} (h : Joins G (e l) u w) :
    (u = v l ∧ w = v (finRotate k l)) ∨ (u = v (finRotate k l) ∧ w = v l) := by
  rcases hC.joins l with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases h with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
  · exact Or.inl ⟨h₃.symm.trans h₁, h₄.symm.trans h₂⟩
  · exact Or.inr ⟨h₄.symm.trans h₂, h₃.symm.trans h₁⟩
  · exact Or.inr ⟨h₃.symm.trans h₁, h₄.symm.trans h₂⟩
  · exact Or.inl ⟨h₄.symm.trans h₂, h₃.symm.trans h₁⟩

/-- **The two ends of an edge of a cycle of size at least two are distinct.** -/
theorem IsCycleOf.ne_of_joins {k : ℕ} {v : Fin k → V} {e : Fin k → E} (hC : IsCycleOf G k v e)
    (hk : 2 ≤ k) {l : Fin k} {u w : V} (h : Joins G (e l) u w) : u ≠ w := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hrot : finRotate (n + 2) l ≠ l := by
    intro h'
    have h'' := congrArg Fin.val h'
    rw [coe_finRotate] at h''
    split_ifs at h'' with hl
    · rw [hl, Fin.val_last] at h''
      omega
    · omega
  intro huw
  subst huw
  rcases hC.eq_or_eq_of_joins h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hrot (hC.injective_node (h₂.symm.trans h₁))
  · exact hrot (hC.injective_node (h₁.symm.trans h₂))

/-- **A cycle can be read from any of its nodes**: its nodes and edges can be listed starting from a
given node. -/
theorem IsCycle.exists_isCycleOf_apply_zero {C : Set E} (hC : IsCycle G C) {w : V}
    (hw : w ∈ cycleNodes G C) :
    ∃ (n : ℕ) (v : Fin (n + 1) → V) (e : Fin (n + 1) → E), IsCycleOf G (n + 1) v e ∧
      Set.range e = C ∧ v 0 = w := by
  obtain ⟨k, v, e, hcyc, hrange, j, rfl⟩ := hC.exists_of_mem hw
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hcyc.pos; omega⟩
  refine ⟨n, _, _, hcyc.rotate j, ?_, by simp⟩
  rw [← hrange]
  exact (Equiv.addRight j).surjective.range_comp e

/-- **A walk along the edges of a cycle avoiding the nodes `v a` and `v b` stays inside, or stays
outside, the arc of the nodes strictly between them**: an edge of the cycle with one end on the arc
and the other off it has `v a` or `v b` as an end. -/
theorem IsCycleOf.mem_image_Ioo_iff_of_reflTransGen {n : ℕ} {v : Fin (n + 1) → V}
    {e : Fin (n + 1) → E} (hC : IsCycleOf G (n + 1) v e) {a b : Fin (n + 1)} {F : Set V}
    (ha : v a ∈ F) (hb : v b ∈ F) {p q : V}
    (h : Relation.ReflTransGen (fun p q => G.AdjOn (Set.range e) p q ∧ p ∉ F ∧ q ∉ F) p q) :
    p ∈ v '' Set.Ioo a b ↔ q ∈ v '' Set.Ioo a b := by
  -- a step along the edge `e l`, from `v l` to `v (l + 1)`
  have key : ∀ l, v l ∉ F → v (finRotate (n + 1) l) ∉ F →
      (v l ∈ v '' Set.Ioo a b ↔ v (finRotate (n + 1) l) ∈ v '' Set.Ioo a b) := by
    intro l h₁ h₂
    have hne : ∀ {i j : Fin (n + 1)}, v i ∉ F → v j ∈ F → (i : ℕ) ≠ j := fun hi hj hij =>
      hi (by rw [Fin.ext hij]; exact hj)
    have hla := hne h₁ ha
    have hlb := hne h₁ hb
    have hra := hne h₂ ha
    have hrb := hne h₂ hb
    rw [hC.injective_node.mem_set_image, hC.injective_node.mem_set_image]
    simp only [Set.mem_Ioo, Fin.lt_def]
    have hal := a.isLt
    have hbl := b.isLt
    have hll := l.isLt
    by_cases hl : (l : ℕ) = n
    · have hr : (finRotate (n + 1) l : ℕ) = 0 := by
        rw [show l = Fin.last n from Fin.ext hl, finRotate_last, Fin.val_zero]
      omega
    · have hr := coe_finRotate_of_ne_last (n := n) (i := l) fun h => hl (by rw [h, Fin.val_last])
      omega
  induction h with
  | refl => exact Iff.rfl
  | @tail q r _ hqr ih =>
    refine ih.trans ?_
    obtain ⟨⟨f, ⟨l, rfl⟩, hl⟩, hq, hr⟩ := hqr
    rcases hC.eq_or_eq_of_joins hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key l hq hr
    · exact (key l hr hq).symm

end CycleArc

section Order

variable {N : RootedNetwork V E X} [Finite E] {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}

/-- The nodes of the cycle `C` whose blocks contain a taxon of `T`. -/
def blockNodes {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (T : Set X') :
    Set V' :=
  {u | u ∈ cycleNodes G.graph C ∧ ∃ x ∈ T, x ∈ nodeBlock G.graph G.leaf C u}

/-- The blocks of `x` and `y` are *joined along `C` avoiding the blocks of `T`*: in the cycle `C`
with the nodes of the blocks of the taxa of `T` removed, the nodes of the blocks of `x` and `y` are
connected. -/
def JoinedAvoiding {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E') (T : Set X')
    (x y : X') : Prop :=
  ∃ u w, u ∈ cycleNodes G.graph C ∧ w ∈ cycleNodes G.graph C ∧
    x ∈ nodeBlock G.graph G.leaf C u ∧ y ∈ nodeBlock G.graph G.leaf C w ∧
    Relation.ReflTransGen
      (fun a b => G.graph.AdjOn C a b ∧ a ∉ blockNodes G C T ∧ b ∉ blockNodes G C T) u w

/-- **Two blocks of a cycle of size at least four are adjacent exactly when they are joined avoiding
the other two blocks of every set of four taxa that the cycle separates and that contains them.**
Adjacent blocks are joined by their edge. Two blocks that are not adjacent leave a node on each of
the two arcs of the cycle between them, the hybrid node among them when it is not one of the two;
taxa in the blocks of these nodes separate them. -/
theorem adjacentBlocks_iff_forall_joinedAvoiding [DecidableEq X] (h1 : IsLevelOne N.graph)
    {C : Set _} (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : 4 ≤ C.ncard) {v}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (x y : X) :
    AdjacentBlocks (unrooted N hN hX) C x y ↔
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y ∧
        ∀ z z', #({x, y, z, z'} : Finset X) = 4 →
          SeparatesQuartet (unrooted N hN hX) C v {x, y, z, z'} →
          JoinedAvoiding (unrooted N hN hX) C {z, z'} x y := by
  -- membership in the block of a node of `C`
  have hblock : ∀ {u}, u ∈ cycleNodes (unrooted N hN hX).graph C → ∀ t : X,
      (t ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u ↔
        u = blockNode (unrooted N hN hX) C t) := fun hu t =>
    ⟨eq_blockNode h1 hC hu, by rintro rfl; exact (blockNode_spec hC t).2⟩
  have hmemF : ∀ {T : Set X} {t : X}, t ∈ T →
      blockNode (unrooted N hN hX) C t ∈ blockNodes (unrooted N hN hX) C T := fun ht =>
    ⟨blockNode_mem hC _, _, ht, (blockNode_spec hC _).2⟩
  have hβne : ∀ {s t : X}, blockNode (unrooted N hN hX) C s ≠ blockNode (unrooted N hN hX) C t →
      s ≠ t := fun h h' => h (h' ▸ rfl)
  constructor
  · rintro ⟨f, hf, u, w, hj, hxu, hyw⟩
    have hu : u ∈ cycleNodes (unrooted N hN hX).graph C := by
      rcases hj with ⟨h, -⟩ | ⟨-, h⟩
      exacts [⟨f, hf, Or.inl h⟩, ⟨f, hf, Or.inr h⟩]
    have hw : w ∈ cycleNodes (unrooted N hN hX).graph C := by
      rcases hj with ⟨-, h⟩ | ⟨h, -⟩
      exacts [⟨f, hf, Or.inr h⟩, ⟨f, hf, Or.inl h⟩]
    rw [hblock hu] at hxu
    rw [hblock hw] at hyw
    subst hxu hyw
    obtain ⟨k, v', e', hcyc, hrange⟩ := id hC
    have hk : C.ncard = k := by
      rw [← hrange, Set.ncard_range_of_injective hcyc.injective_edge, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    rw [← hrange] at hf
    obtain ⟨l, rfl⟩ := hf
    have hne := hcyc.ne_of_joins (by omega) hj
    refine ⟨fun h => hne ((sameBlock_iff_blockNode_eq h1 hC x y).1 h), fun z z' hcard hsep => ?_⟩
    obtain ⟨hinj, -⟩ := (separatesQuartet_iff h1 hC hv _).1 hsep
    have hd := distinct4_of_card_insert_eq hcard
    have hxz : blockNode (unrooted N hN hX) C x ≠ blockNode (unrooted N hN hX) C z := fun h =>
      hd.2.1 (hinj (by simp) (by simp) h)
    have hxz' : blockNode (unrooted N hN hX) C x ≠ blockNode (unrooted N hN hX) C z' := fun h =>
      hd.2.2.1 (hinj (by simp) (by simp) h)
    have hyz : blockNode (unrooted N hN hX) C y ≠ blockNode (unrooted N hN hX) C z := fun h =>
      hd.2.2.2.1 (hinj (by simp) (by simp) h)
    have hyz' : blockNode (unrooted N hN hX) C y ≠ blockNode (unrooted N hN hX) C z' := fun h =>
      hd.2.2.2.2.1 (hinj (by simp) (by simp) h)
    refine ⟨_, _, blockNode_mem hC x, blockNode_mem hC y, (blockNode_spec hC x).2,
      (blockNode_spec hC y).2, .single ⟨⟨e' l, by rw [← hrange]; exact ⟨l, rfl⟩, hj⟩, ?_, ?_⟩⟩
    · rintro ⟨-, t, ht, htx⟩
      rw [hblock (blockNode_mem hC x)] at htx
      rcases ht with rfl | rfl
      exacts [hxz htx, hxz' htx]
    · rintro ⟨-, t, ht, hty⟩
      rw [hblock (blockNode_mem hC y)] at hty
      rcases ht with rfl | rfl
      exacts [hyz hty, hyz' hty]
  · rintro ⟨hxy, hall⟩
    rw [sameBlock_iff_blockNode_eq h1 hC] at hxy
    by_contra hadj
    have hnj : ∀ f ∈ C, ¬ Joins (unrooted N hN hX).graph f (blockNode (unrooted N hN hX) C x)
        (blockNode (unrooted N hN hX) C y) := fun f hf hj =>
      hadj ⟨f, hf, _, _, hj, (blockNode_spec hC x).2, (blockNode_spec hC y).2⟩
    -- the nodes `v' 0, …, v' n` of `C`, starting from the node of the block of `x`
    obtain ⟨n, v', e', hcyc, hrange, h0⟩ := hC.exists_isCycleOf_apply_zero (blockNode_mem hC x)
    have hk : C.ncard = n + 1 := by
      rw [← hrange, Set.ncard_range_of_injective hcyc.injective_edge, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hnodes : cycleNodes (unrooted N hN hX).graph C = Set.range v' := by
      rw [← hrange]
      exact hcyc.cycleNodes_eq
    have hmemv : ∀ i, v' i ∈ cycleNodes (unrooted N hN hX).graph C := fun i => by
      rw [hnodes]
      exact ⟨i, rfl⟩
    have he' : ∀ i, e' i ∈ C := fun i => by
      rw [← hrange]
      exact ⟨i, rfl⟩
    have hvne : ∀ i j : Fin (n + 1), (i : ℕ) ≠ j → v' i ≠ v' j := fun i j hij h =>
      hij (congrArg Fin.val (hcyc.injective_node h))
    obtain ⟨m, hm⟩ : blockNode (unrooted N hN hX) C y ∈ Set.range v' :=
      hnodes ▸ blockNode_mem hC y
    obtain ⟨h, hh⟩ : v ∈ Set.range v' := hnodes ▸ hv.mem_cycleNodes
    -- the node of the block of `y` is neither `v' 0`, nor next to it
    have hm0 : (m : ℕ) ≠ 0 := fun hm0 => hxy (by
      rw [← h0, ← hm, show m = 0 from Fin.ext (by rw [hm0, Fin.val_zero])])
    have hm1 : (m : ℕ) ≠ 1 := by
      intro hm1
      apply hnj _ (he' 0)
      have hj := hcyc.joins 0
      have hr : finRotate (n + 1) 0 = m := Fin.ext (by
        rw [coe_finRotate_of_ne_last (by rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega),
          Fin.val_zero, hm1])
      rwa [hr, h0, hm] at hj
    have hmn : (m : ℕ) ≠ n := by
      intro hmn
      obtain rfl : m = Fin.last n := Fin.ext hmn
      apply hnj _ (he' (Fin.last n))
      have hj := hcyc.joins (Fin.last n)
      rw [finRotate_last, h0, hm] at hj
      exact Or.symm hj
    -- a node on each arc between them, one of the four being the hybrid node
    obtain ⟨a, b, h0a, ham, hmb, hhyb⟩ : ∃ a b : Fin (n + 1), 0 < (a : ℕ) ∧ (a : ℕ) < m ∧
        (m : ℕ) < b ∧ (v = v' 0 ∨ v = v' a ∨ v = v' m ∨ v = v' b) := by
      have hmlt := m.isLt
      have hhlt := h.isLt
      rcases Nat.lt_trichotomy (h : ℕ) m with hhm | hhm | hhm
      · by_cases hh0 : (h : ℕ) = 0
        · refine ⟨⟨1, by omega⟩,
            ⟨m + 1, by omega⟩, by simp, by simp only; omega, by simp only; omega, Or.inl ?_⟩
          rw [← hh, show h = 0 from Fin.ext (by rw [hh0, Fin.val_zero])]
        · exact ⟨h, ⟨m + 1, by omega⟩, by omega, hhm, by simp only; omega, Or.inr (Or.inl hh.symm)⟩
      · refine ⟨⟨1, by omega⟩, ⟨m + 1, by omega⟩, by simp, by simp only; omega, by simp only; omega,
          Or.inr (Or.inr (Or.inl ?_))⟩
        rw [← hh, Fin.ext hhm]
      · exact
          ⟨⟨1, by omega⟩, h, by simp, by simp only; omega, hhm, Or.inr (Or.inr (Or.inr hh.symm))⟩
    obtain ⟨z, hz⟩ := exists_blockNode_eq h1 hC (hmemv a)
    obtain ⟨z', hz'⟩ := exists_blockNode_eq h1 hC (hmemv b)
    have hxz : blockNode (unrooted N hN hX) C x ≠ blockNode (unrooted N hN hX) C z := by
      rw [← h0, hz]
      exact hvne _ _ (by rw [Fin.val_zero]; omega)
    have hxz' : blockNode (unrooted N hN hX) C x ≠ blockNode (unrooted N hN hX) C z' := by
      rw [← h0, hz']
      exact hvne _ _ (by rw [Fin.val_zero]; omega)
    have hyz : blockNode (unrooted N hN hX) C y ≠ blockNode (unrooted N hN hX) C z := by
      rw [← hm, hz]
      exact hvne _ _ (by omega)
    have hyz' : blockNode (unrooted N hN hX) C y ≠ blockNode (unrooted N hN hX) C z' := by
      rw [← hm, hz']
      exact hvne _ _ (by omega)
    have hzz' : blockNode (unrooted N hN hX) C z ≠ blockNode (unrooted N hN hX) C z' := by
      rw [hz, hz']
      exact hvne _ _ (by omega)
    have hcard := Finset.card_four_of_ne (hβne hxy) (hβne hxz) (hβne hxz') (hβne hyz) (hβne hyz')
      (hβne hzz')
    have hsep : SeparatesQuartet (unrooted N hN hX) C v {x, y, z, z'} := by
      refine (separatesQuartet_iff h1 hC hv _).2 ⟨Finset.injOn_four hxy hxz hxz' hyz hyz' hzz', ?_⟩
      rcases hhyb with hv0 | hva | hvm | hvb
      · exact ⟨x, by simp, h0.symm.trans hv0.symm⟩
      · exact ⟨z, by simp, hz.trans hva.symm⟩
      · exact ⟨y, by simp, hm.symm.trans hvm.symm⟩
      · exact ⟨z', by simp, hz'.trans hvb.symm⟩
    -- a walk from `v' 0` to `v' m` avoiding `v' a` and `v' b` would cross from outside the arc
    -- between them to inside
    obtain ⟨u, w, hu, hw, hxu, hyw, hwalk⟩ := hall z z' hcard hsep
    rw [hblock hu] at hxu
    rw [hblock hw] at hyw
    subst hxu hyw
    have hFa : v' a ∈ blockNodes (unrooted N hN hX) C {z, z'} := by
      rw [← hz]
      exact hmemF (by simp)
    have hFb : v' b ∈ blockNodes (unrooted N hN hX) C {z, z'} := by
      rw [← hz']
      exact hmemF (by simp)
    have key := hcyc.mem_image_Ioo_iff_of_reflTransGen hFa hFb
      (Relation.ReflTransGen.mono (fun p q hpq => ⟨hrange ▸ hpq.1, hpq.2⟩) _ _ hwalk)
    rw [← h0, ← hm, hcyc.injective_node.mem_set_image, hcyc.injective_node.mem_set_image] at key
    simp only [Set.mem_Ioo, Fin.lt_def, Fin.val_zero] at key
    have := key.2 ⟨ham, hmb⟩
    omega

end Order

end Banos2019
