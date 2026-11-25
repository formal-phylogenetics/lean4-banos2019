module

public import Banos2019.Network.SuppressIso
public import Banos2019.Bridge.Model

/-!
# Suppression is invariant under isomorphism

The edges of `suppressExcept G P` are the chains of `G`, each with an order chosen on it
(`chainRep`); its ends and direction are read off that order. Two orders on a chain are the same or
reverse to each other (`ChainRep.eq_or_eq_reverse`), and the rule of `suppressExcept` gives the same
ends and direction for both (`ChainRep.src_tgt`, `ChainRep.src_tgt_of_directed`). So the suppressed
network does not depend on the orders chosen, and an isomorphism of semidirected networks is an
isomorphism of the suppressed networks (`SDIso.suppressExcept`); so is the passage from the
Challenge's copy of the definitions to the library's (`Model.SDNetwork.suppressIso`).

* `ChainRep.reverse`, `ChainRep.src`, `ChainRep.tgt`.
* `IsChainOf.map`, `ChainRep.map`: the image of a chain under an isomorphism.
* `SDIso.degree_eq`, `SDIso.isBranch_iff`: isomorphisms keep degrees and kept nodes.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-! ### Two orders on a chain -/

section ChainRep

variable {G : SemidirectedNetwork V E X} {P : Set V}

/-- An edge joining `a` to `b` and `a` to `b'` has `b = b'`. -/
theorem Joins.eq_right {H : DirectedMultigraph V E} {f : E} {a b b' : V} (h : Joins H f a b)
    (h' : Joins H f a b') : b = b' := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases h' with ⟨h₁', h₂'⟩ | ⟨h₁', h₂'⟩
  · exact h₂.symm.trans h₂'
  · exact h₂.symm.trans (h₂'.trans (h₁.symm.trans h₁'))
  · exact h₁.symm.trans (h₁'.trans (h₂.symm.trans h₂'))
  · exact h₁.symm.trans h₁'

/-- The ends of an edge are on it. -/
theorem Joins.incident_left {H : DirectedMultigraph V E} {f : E} {a b : V} (h : Joins H f a b) :
    H.source f = a ∨ H.target f = a := by
  rcases h with ⟨h₁, -⟩ | ⟨-, h₂⟩
  · exact Or.inl h₁
  · exact Or.inr h₂

theorem Joins.incident_right {H : DirectedMultigraph V E} {f : E} {a b : V} (h : Joins H f a b) :
    H.source f = b ∨ H.target f = b :=
  Joins.incident_left (Or.symm h)

/-- The nodes of a chain that suppression keeps are its two ends. -/
theorem IsChainOf.isBranch_iff {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    (h : IsChainOf G P k p e) (j : Fin (k + 1)) : IsBranch G P (p j) ↔ j = 0 ∨ j = Fin.last k := by
  constructor
  · intro hb
    by_contra hn
    push Not at hn
    exact h.inner j hn.1 hn.2 hb
  · rintro (rfl | rfl)
    exacts [h.ends.1, h.ends.2]

/-- A chain read backwards. -/
theorem IsChainOf.reverse {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    (h : IsChainOf G P k p e) : IsChainOf G P k (p ∘ Fin.rev) (e ∘ Fin.rev) where
  pos := h.pos
  joins i := by
    have := h.joins (Fin.rev i)
    simp only [Function.comp_apply, Fin.rev_castSucc, Fin.rev_succ]
    exact Or.symm this
  inner i hi0 hil := h.inner (Fin.rev i)
    (fun h' => hil (by rw [← Fin.rev_rev i, h', Fin.rev_zero]))
    (fun h' => hi0 (by rw [← Fin.rev_rev i, h', Fin.rev_last]))
  ends := by
    simp only [Function.comp_apply, Fin.rev_zero, Fin.rev_last]
    exact ⟨h.ends.2, h.ends.1⟩
  injective_edge := h.injective_edge.comp Fin.rev_injective

/-- **Two chains with the same first node and the same first edge are the same.** -/
theorem IsChainOf.eq_of_head [Finite E] {k k' : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    {p' : Fin (k' + 1) → V} {e' : Fin k' → E} (h : IsChainOf G P k p e)
    (h' : IsChainOf G P k' p' e') (hp : p 0 = p' 0) (he : e ⟨0, h.pos⟩ = e' ⟨0, h'.pos⟩) :
    k = k' ∧ (∀ i (hi : i ≤ k) (hi' : i ≤ k'), p ⟨i, by omega⟩ = p' ⟨i, by omega⟩) ∧
      ∀ i (hi : i < k) (hi' : i < k'), e ⟨i, hi⟩ = e' ⟨i, hi'⟩ := by
  have key : ∀ i, (∀ (hi : i ≤ k) (hi' : i ≤ k'), p ⟨i, by omega⟩ = p' ⟨i, by omega⟩) ∧
      ∀ (hi : i < k) (hi' : i < k'), e ⟨i, hi⟩ = e' ⟨i, hi'⟩ := by
    intro i
    induction i with
    | zero => exact ⟨fun _ _ => hp, fun _ _ => he⟩
    | succ i ih =>
      have hpi : ∀ (hi : i + 1 ≤ k) (hi' : i + 1 ≤ k'),
          p ⟨i + 1, by omega⟩ = p' ⟨i + 1, by omega⟩ := by
        intro hi hi'
        have h₁ := h.joins ⟨i, hi⟩
        have h₂ := h'.joins ⟨i, hi'⟩
        have hpe : p (Fin.castSucc ⟨i, hi⟩) = p' (Fin.castSucc ⟨i, hi'⟩) :=
          ih.1 (by omega) (by omega)
        rw [hpe, ih.2 hi hi'] at h₁
        exact h₁.eq_right h₂
      refine ⟨hpi, fun hi hi' => ?_⟩
      have hu : ¬ IsBranch G P (p ⟨i + 1, by omega⟩) :=
        h.inner ⟨i + 1, by omega⟩ (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]; omega)
      have hdeg : degree G.graph (p ⟨i + 1, by omega⟩) = 2 := by
        by_contra hd
        exact hu (Or.inl hd)
      have hinc₁ : G.graph.source (e ⟨i, by omega⟩) = p ⟨i + 1, by omega⟩ ∨
          G.graph.target (e ⟨i, by omega⟩) = p ⟨i + 1, by omega⟩ :=
        (h.joins ⟨i, by omega⟩).incident_right
      have hinc₂ : G.graph.source (e ⟨i + 1, hi⟩) = p ⟨i + 1, by omega⟩ ∨
          G.graph.target (e ⟨i + 1, hi⟩) = p ⟨i + 1, by omega⟩ :=
        (h.joins ⟨i + 1, hi⟩).incident_left
      have hinc₃ : G.graph.source (e' ⟨i + 1, hi'⟩) = p ⟨i + 1, by omega⟩ ∨
          G.graph.target (e' ⟨i + 1, hi'⟩) = p ⟨i + 1, by omega⟩ := by
        rw [hpi (by omega) (by omega)]
        exact (h'.joins ⟨i + 1, hi'⟩).incident_left
      have hne : e ⟨i, by omega⟩ ≠ e ⟨i + 1, hi⟩ := fun h'' => by
        have := congrArg Fin.val (h.injective_edge h'')
        simp at this
      rcases eq_or_eq_of_degree_eq_two hdeg hinc₁ hinc₂ hinc₃ hne with h₃ | h₃
      · rw [ih.2 (by omega) (by omega)] at h₃
        have := congrArg Fin.val (h'.injective_edge h₃)
        simp at this
      · exact h₃.symm
  have hk : k = k' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have heq : p (Fin.last k) = p' ⟨k, by omega⟩ := (key k).1 le_rfl hlt.le
      have hb : IsBranch G P (p (Fin.last k)) := h.ends.2
      rw [heq] at hb
      exact h'.inner ⟨k, by omega⟩ (by simp [Fin.ext_iff]; exact h.pos.ne')
        (by simp [Fin.ext_iff]; omega) hb
    · have heq : p ⟨k', by omega⟩ = p' (Fin.last k') := (key k').1 hlt.le le_rfl
      have hb : IsBranch G P (p' (Fin.last k')) := h'.ends.2
      rw [← heq] at hb
      exact h.inner ⟨k', by omega⟩ (by simp [Fin.ext_iff]; exact h'.pos.ne')
        (by simp [Fin.ext_iff]; omega) hb
  exact ⟨hk, fun i hi hi' => (key i).1 hi hi', fun i hi hi' => (key i).2 hi hi'⟩

variable {c : Set E}

/-- The order of a chain read backwards. -/
def ChainRep.reverse (r : ChainRep G P c) : ChainRep G P c :=
  ⟨r.k, r.p ∘ Fin.rev, r.e ∘ Fin.rev, r.isChainOf.reverse,
    (Fin.rev_surjective.range_comp r.e).trans r.range_eq⟩

theorem ChainRep.eq_of_head [Finite E] (r r' : ChainRep G P c) (hp : r.p 0 = r'.p 0)
    (he : r.e ⟨0, r.isChainOf.pos⟩ = r'.e ⟨0, r'.isChainOf.pos⟩) : r = r' := by
  obtain ⟨k, p, e, h, hr⟩ := r
  obtain ⟨k', p', e', h', hr'⟩ := r'
  obtain ⟨rfl, hpp, hee⟩ := h.eq_of_head h' hp he
  have hp' : p = p' := funext fun i => hpp i.1 (by omega) (by omega)
  have he' : e = e' := funext fun i => hee i.1 i.2 i.2
  subst hp' he'
  rfl

/-- **Two orders on a chain are the same or reverse to each other.** -/
theorem ChainRep.eq_or_eq_reverse [Finite E] (r r' : ChainRep G P c) : r' = r ∨ r' = r.reverse := by
  have hk := r.isChainOf.pos
  have hk' := r'.isChainOf.pos
  obtain ⟨j, hj⟩ : r'.e ⟨0, hk'⟩ ∈ Set.range r.e := by
    rw [r.range_eq]
    exact r'.range_eq.subset ⟨_, rfl⟩
  have hinc : r'.p 0 = r.p j.castSucc ∨ r'.p 0 = r.p j.succ :=
    r.isChainOf.eq_of_incident (hj ▸ (r'.isChainOf.joins ⟨0, hk'⟩).incident_left)
  have hb : IsBranch G P (r'.p 0) := r'.isChainOf.ends.1
  rcases hinc with h0 | h0
  · rw [h0, r.isChainOf.isBranch_iff] at hb
    have hj0 : j = ⟨0, hk⟩ := by
      rcases hb with hb | hb
      · exact Fin.ext (by simpa [Fin.ext_iff] using hb)
      · exact absurd hb (Fin.castSucc_ne_last j)
    subst hj0
    exact Or.inl (ChainRep.eq_of_head r r' h0.symm hj).symm
  · rw [h0, r.isChainOf.isBranch_iff] at hb
    have hjl : j = Fin.rev ⟨0, hk⟩ := by
      rcases hb with hb | hb
      · exact absurd hb (Fin.succ_ne_zero j)
      · exact Fin.ext (by simp [Fin.ext_iff] at hb ⊢; omega)
    refine Or.inr (ChainRep.eq_of_head r.reverse r' ?_ ?_).symm
    · change r.p (Fin.rev 0) = r'.p 0
      rw [h0, Fin.rev_zero]
      congr 1
      rcases hb with hb | hb
      · exact absurd hb (Fin.succ_ne_zero j)
      · exact hb.symm
    · change r.e (Fin.rev ⟨0, hk⟩) = r'.e ⟨0, hk'⟩
      rw [← hjl]
      exact hj

theorem ChainRep.reverse_pointsForward (r : ChainRep G P c) :
    r.reverse.PointsForward ↔ r.PointsBackward := by
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩
    refine ⟨⟨Fin.rev i, hi⟩, fun j hj => ?_⟩
    have := h (Fin.rev j) (by change G.IsDirected (r.e (Fin.rev (Fin.rev j))); rwa [Fin.rev_rev])
    change G.graph.target (r.e (Fin.rev (Fin.rev j))) = r.p (Fin.rev (Fin.rev j).succ) at this
    rwa [Fin.rev_succ, Fin.rev_rev] at this
  · rintro ⟨⟨i, hi⟩, h⟩
    refine ⟨⟨Fin.rev i, by change G.IsDirected (r.e (Fin.rev (Fin.rev i))); rwa [Fin.rev_rev]⟩,
      fun (j : Fin r.k) hj => ?_⟩
    have := h (Fin.rev j) hj
    change G.graph.target (r.e (Fin.rev j)) = r.p (Fin.rev j.succ)
    rwa [Fin.rev_succ]

theorem ChainRep.reverse_pointsBackward (r : ChainRep G P c) :
    r.reverse.PointsBackward ↔ r.PointsForward := by
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩
    refine ⟨⟨Fin.rev i, hi⟩, fun j hj => ?_⟩
    have := h (Fin.rev j) (by change G.IsDirected (r.e (Fin.rev (Fin.rev j))); rwa [Fin.rev_rev])
    change G.graph.target (r.e (Fin.rev (Fin.rev j))) = r.p (Fin.rev (Fin.rev j).castSucc) at this
    rwa [Fin.rev_castSucc, Fin.rev_rev] at this
  · rintro ⟨⟨i, hi⟩, h⟩
    refine ⟨⟨Fin.rev i, by change G.IsDirected (r.e (Fin.rev (Fin.rev i))); rwa [Fin.rev_rev]⟩,
      fun (j : Fin r.k) hj => ?_⟩
    have := h (Fin.rev j) hj
    change G.graph.target (r.e (Fin.rev j)) = r.p (Fin.rev j.castSucc)
    rwa [Fin.rev_castSucc]

/-- A chain that points toward both of its ends is a loop: its ends are the same node. -/
theorem ChainRep.first_eq_last [Finite E] (r : ChainRep G P c) (hf : r.PointsForward)
    (hb : r.PointsBackward) : r.p 0 = r.p (Fin.last r.k) := by
  obtain ⟨⟨i, hi⟩, hf⟩ := hf
  have h₁ := hf i hi
  rw [hb.2 i hi] at h₁
  -- `p i = p (i + 1)`
  by_cases hil : i.succ = Fin.last r.k
  · have hbr : IsBranch G P (r.p i.castSucc) := by rw [h₁, hil]; exact r.isChainOf.ends.2
    rcases (r.isChainOf.isBranch_iff _).mp hbr with h0 | h0
    · rw [← h0, h₁, hil]
    · exact absurd h0 (Fin.castSucc_ne_last i)
  · exfalso
    have hin : ¬ IsBranch G P (r.p i.succ) := r.isChainOf.inner _ (Fin.succ_ne_zero i) hil
    by_cases hi0 : i.castSucc = 0
    · rw [← h₁, hi0] at hin
      exact hin r.isChainOf.ends.1
    · -- `p i` is an inner node of degree two, with the loop `e i` and the edge before it
      have hdeg : degree G.graph (r.p i.castSucc) = 2 := by
        by_contra hd
        exact hin (h₁ ▸ Or.inl hd)
      have hi1 : 1 ≤ i.val := by
        rcases Nat.eq_zero_or_pos i.val with h' | h'
        · exact absurd (Fin.ext (by simpa using h')) hi0
        · exact h'
      set j : Fin r.k := ⟨i.val - 1, by omega⟩
      have hjs : j.succ = i.castSucc := Fin.ext (by simp [j]; omega)
      have hloop : G.graph.source (r.e i) = r.p i.castSucc ∧ G.graph.target (r.e i) =
        r.p i.castSucc := by
        rcases r.isChainOf.joins i with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
        · exact ⟨h₂, h₃.trans h₁.symm⟩
        · exact ⟨h₂.trans h₁.symm, h₃⟩
      have hji : r.e j ≠ r.e i := fun h' => by
        have := congrArg Fin.val (r.isChainOf.injective_edge h')
        simp [j] at this
        omega
      have hj : G.graph.source (r.e j) = r.p i.castSucc ∨ G.graph.target (r.e j) = r.p i.castSucc :=
        hjs ▸ (r.isChainOf.joins j).incident_right
      have hfin₁ := Set.toFinite {f | G.graph.target f = r.p i.castSucc}
      have hfin₂ := Set.toFinite {f | G.graph.source f = r.p i.castSucc}
      unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree at hdeg
      rcases hj with hj | hj
      · have h₂ : ({r.e j, r.e i} : Set E).ncard ≤ {f | G.graph.source f = r.p i.castSucc}.ncard :=
          Set.ncard_le_ncard (by rintro f (rfl | rfl); exacts [hj, hloop.1]) hfin₂
        have h₃ : ({r.e i} : Set E).ncard ≤ {f | G.graph.target f = r.p i.castSucc}.ncard :=
          Set.ncard_le_ncard (by rintro f rfl; exact hloop.2) hfin₁
        rw [Set.ncard_pair hji, Set.ncard_singleton] at *
        omega
      · have h₂ : ({r.e j, r.e i} : Set E).ncard ≤ {f | G.graph.target f = r.p i.castSucc}.ncard :=
          Set.ncard_le_ncard (by rintro f (rfl | rfl); exacts [hj, hloop.2]) hfin₁
        have h₃ : ({r.e i} : Set E).ncard ≤ {f | G.graph.source f = r.p i.castSucc}.ncard :=
          Set.ncard_le_ncard (by rintro f rfl; exact hloop.1) hfin₂
        rw [Set.ncard_pair hji, Set.ncard_singleton] at *
        omega

open Classical in
/-- The source that `suppressExcept` gives a chain read in the order `r`. -/
def ChainRep.src (r : ChainRep G P c) : V := if r.PointsBackward then r.p (Fin.last r.k) else r.p 0

open Classical in
/-- The target that `suppressExcept` gives a chain read in the order `r`. -/
def ChainRep.tgt (r : ChainRep G P c) : V := if r.PointsBackward then r.p 0 else r.p (Fin.last r.k)

theorem ChainRep.isBranch_src (r : ChainRep G P c) : IsBranch G P r.src := by
  unfold ChainRep.src
  split_ifs
  exacts [r.isChainOf.ends.2, r.isChainOf.ends.1]

theorem ChainRep.isBranch_tgt (r : ChainRep G P c) : IsBranch G P r.tgt := by
  unfold ChainRep.tgt
  split_ifs
  exacts [r.isChainOf.ends.1, r.isChainOf.ends.2]

/-- Two orders on a chain are both directed or both not. -/
theorem ChainRep.directed_iff [Finite E] (r r' : ChainRep G P c) :
    (r'.PointsForward ∨ r'.PointsBackward) ↔ (r.PointsForward ∨ r.PointsBackward) := by
  rcases r.eq_or_eq_reverse r' with rfl | rfl
  · exact Iff.rfl
  · rw [r.reverse_pointsForward, r.reverse_pointsBackward, or_comm]

open Classical in
theorem ChainRep.reverse_src (r : ChainRep G P c) :
    r.reverse.src = if r.PointsForward then r.p 0 else r.p (Fin.last r.k) := by
  unfold ChainRep.src
  by_cases h : r.PointsForward
  · simp only [r.reverse_pointsBackward.mpr h, h, ↓reduceIte]
    change r.p (Fin.rev (Fin.last r.k)) = _
    rw [Fin.rev_last]
  · simp only [mt r.reverse_pointsBackward.mp h, h, ↓reduceIte]
    change r.p (Fin.rev 0) = _
    rw [Fin.rev_zero]

open Classical in
theorem ChainRep.reverse_tgt (r : ChainRep G P c) :
    r.reverse.tgt = if r.PointsForward then r.p (Fin.last r.k) else r.p 0 := by
  unfold ChainRep.tgt
  by_cases h : r.PointsForward
  · simp only [r.reverse_pointsBackward.mpr h, h, ↓reduceIte]
    change r.p (Fin.rev 0) = _
    rw [Fin.rev_zero]
  · simp only [mt r.reverse_pointsBackward.mp h, h, ↓reduceIte]
    change r.p (Fin.rev (Fin.last r.k)) = _
    rw [Fin.rev_last]

/-- Two orders on a chain give it the same ends, in the same order or the other. -/
theorem ChainRep.src_tgt [Finite E] (r r' : ChainRep G P c) :
    (r'.src = r.src ∧ r'.tgt = r.tgt) ∨ (r'.src = r.tgt ∧ r'.tgt = r.src) := by
  rcases r.eq_or_eq_reverse r' with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · rw [r.reverse_src, r.reverse_tgt]
    unfold ChainRep.src ChainRep.tgt
    by_cases hf : r.PointsForward <;> by_cases hb : r.PointsBackward <;>
      simp only [hf, hb, ↓reduceIte, and_self, true_or, or_true]

/-- Two orders on a directed chain give it the same source and target. -/
theorem ChainRep.src_tgt_of_directed [Finite E] (r r' : ChainRep G P c)
    (hd : r.PointsForward ∨ r.PointsBackward) : r'.src = r.src ∧ r'.tgt = r.tgt := by
  rcases r.eq_or_eq_reverse r' with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [r.reverse_src, r.reverse_tgt]
    unfold ChainRep.src ChainRep.tgt
    by_cases hf : r.PointsForward <;> by_cases hb : r.PointsBackward <;>
      simp only [hf, hb, ↓reduceIte, and_self]
    · have := r.first_eq_last hf hb
      exact ⟨this, this.symm⟩
    · exact absurd hd (by tauto)

/-! ### The suppressed network, read from any order on its chains -/

theorem suppressExcept_source_val (hc : IsChain G P c) :
    ((suppressExcept G P).graph.source ⟨c, hc⟩).1 = (chainRep G P hc).src := by
  unfold ChainRep.src
  simp only [suppressExcept]
  split_ifs <;> rfl

theorem suppressExcept_target_val (hc : IsChain G P c) :
    ((suppressExcept G P).graph.target ⟨c, hc⟩).1 = (chainRep G P hc).tgt := by
  unfold ChainRep.tgt
  simp only [suppressExcept]
  split_ifs <;> rfl

theorem suppressExcept_isDirected_iff [Finite E] (hc : IsChain G P c) (r : ChainRep G P c) :
    (suppressExcept G P).IsDirected ⟨c, hc⟩ ↔ r.PointsForward ∨ r.PointsBackward :=
  ChainRep.directed_iff r (chainRep G P hc)

theorem suppressExcept_ends [Finite E] (hc : IsChain G P c) (r : ChainRep G P c) :
    (((suppressExcept G P).graph.source ⟨c, hc⟩).1 = r.src ∧
        ((suppressExcept G P).graph.target ⟨c, hc⟩).1 = r.tgt) ∨
      (((suppressExcept G P).graph.source ⟨c, hc⟩).1 = r.tgt ∧
        ((suppressExcept G P).graph.target ⟨c, hc⟩).1 = r.src) := by
  rw [suppressExcept_source_val, suppressExcept_target_val]
  exact ChainRep.src_tgt r (chainRep G P hc)

theorem suppressExcept_ends_of_directed [Finite E] (hc : IsChain G P c) (r : ChainRep G P c)
    (hd : r.PointsForward ∨ r.PointsBackward) :
    ((suppressExcept G P).graph.source ⟨c, hc⟩).1 = r.src ∧
      ((suppressExcept G P).graph.target ⟨c, hc⟩).1 = r.tgt := by
  rw [suppressExcept_source_val, suppressExcept_target_val]
  exact ChainRep.src_tgt_of_directed r (chainRep G P hc) hd

end ChainRep

/-! ### Isomorphisms keep chains -/

section Transport

variable {V' E' : Type*} {G : SemidirectedNetwork V E X} {G' : SemidirectedNetwork V' E' X}
  (ι : SDIso G G')

theorem SDIso.joins_of_joins {f : E} {a b : V} (h : Joins G.graph f a b) :
    Joins G'.graph (ι.edge f) (ι.vert a) (ι.vert b) := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [← h₁, ← h₂]
    exact ι.joins f
  · rw [← h₁, ← h₂]
    exact Or.symm (ι.joins f)

theorem SDIso.incident_iff (f : E) (u : V) :
    (G'.graph.source (ι.edge f) = ι.vert u ∨ G'.graph.target (ι.edge f) = ι.vert u) ↔
      (G.graph.source f = u ∨ G.graph.target f = u) := by
  rcases ι.joins f with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> simp only [ι.vert.apply_eq_iff_eq]
  exact or_comm

theorem SDIso.loop_iff (f : E) (u : V) :
    (G'.graph.source (ι.edge f) = ι.vert u ∧ G'.graph.target (ι.edge f) = ι.vert u) ↔
      (G.graph.source f = u ∧ G.graph.target f = u) := by
  rcases ι.joins f with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> simp only [ι.vert.apply_eq_iff_eq]
  exact and_comm

theorem SDIso.image_setOf {p : E → Prop} {q : E' → Prop} (h : ∀ f, q (ι.edge f) ↔ p f) :
    ι.edge '' {f | p f} = {f' | q f'} := by
  ext f'
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (h f).mpr hf
  · intro hf
    exact ⟨ι.edge.symm f', (h _).mp (by rwa [Equiv.apply_symm_apply]), Equiv.apply_symm_apply _ _⟩

/-- **An isomorphism keeps degrees.** -/
theorem SDIso.degree_eq [Finite E] (u : V) : degree G'.graph (ι.vert u) = degree G.graph u := by
  have : Finite E' := Finite.of_equiv _ ι.edge
  unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree
  have hA := Set.ncard_union_add_ncard_inter {f' | G'.graph.target f' = ι.vert u}
    {f' | G'.graph.source f' = ι.vert u} (Set.toFinite _) (Set.toFinite _)
  have hB := Set.ncard_union_add_ncard_inter {f | G.graph.target f = u}
    {f | G.graph.source f = u} (Set.toFinite _) (Set.toFinite _)
  have h₁ : {f' | G'.graph.target f' = ι.vert u} ∪ {f' | G'.graph.source f' = ι.vert u} =
      ι.edge '' ({f | G.graph.target f = u} ∪ {f | G.graph.source f = u}) := by
    rw [← Set.ofPred_or, ← Set.ofPred_or]
    exact (ι.image_setOf fun f => by rw [or_comm, ι.incident_iff, or_comm]).symm
  have h₂ : {f' | G'.graph.target f' = ι.vert u} ∩ {f' | G'.graph.source f' = ι.vert u} =
      ι.edge '' ({f | G.graph.target f = u} ∩ {f | G.graph.source f = u}) := by
    rw [← Set.ofPred_and, ← Set.ofPred_and]
    exact (ι.image_setOf fun f => by rw [and_comm, ι.loop_iff, and_comm]).symm
  rw [h₁, h₂, Set.ncard_image_of_injective _ ι.edge.injective,
    Set.ncard_image_of_injective _ ι.edge.injective] at hA
  omega

theorem SDIso.isLeaf_iff (u : V) : (∃ x, G'.leaf x = ι.vert u) ↔ ∃ x, G.leaf x = u := by
  simp only [ι.leaf, ι.vert.apply_eq_iff_eq]

/-- **An isomorphism keeps the nodes that suppression keeps.** -/
theorem SDIso.isBranch_iff [Finite E] {P : Set V} {P' : Set V'} (hP : ∀ u, ι.vert u ∈ P' ↔ u ∈ P)
    (u : V) : IsBranch G' P' (ι.vert u) ↔ IsBranch G P u := by
  unfold IsBranch
  rw [ι.degree_eq, ι.isLeaf_iff, hP]

variable [Finite E] {P : Set V} {P' : Set V'} (hP : ∀ u, ι.vert u ∈ P' ↔ u ∈ P)
include hP

/-- **The image of a chain is a chain.** -/
theorem IsChainOf.map {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E} (h : IsChainOf G P k p e) :
    IsChainOf G' P' k (ι.vert ∘ p) (ι.edge ∘ e) where
  pos := h.pos
  joins i := ι.joins_of_joins (h.joins i)
  inner i hi0 hil := by
    simp only [Function.comp_apply, ι.isBranch_iff hP]
    exact h.inner i hi0 hil
  ends := by
    simp only [Function.comp_apply, ι.isBranch_iff hP]
    exact h.ends
  injective_edge := ι.edge.injective.comp h.injective_edge

theorem IsChain.map {c : Set E} (h : IsChain G P c) : IsChain G' P' (ι.edge '' c) := by
  obtain ⟨k, p, e, hc, rfl⟩ := h
  exact ⟨k, _, _, hc.map ι hP, Set.range_comp _ _⟩

/-- The image of an order on a chain. -/
def ChainRep.map {c : Set E} (r : ChainRep G P c) : ChainRep G' P' (ι.edge '' c) :=
  ⟨r.k, ι.vert ∘ r.p, ι.edge ∘ r.e, r.isChainOf.map ι hP, by rw [Set.range_comp, r.range_eq]⟩

theorem ChainRep.map_pointsForward {c : Set E} (r : ChainRep G P c) :
    (r.map ι hP).PointsForward ↔ r.PointsForward := by
  unfold ChainRep.PointsForward
  refine and_congr (exists_congr fun i => ι.isDirected_iff _) (forall_congr' fun i => ?_)
  change G'.IsDirected (ι.edge (r.e i)) → G'.graph.target (ι.edge (r.e i)) = ι.vert (r.p i.succ) ↔ _
  rw [ι.isDirected_iff]
  refine imp_congr_right fun hd => ?_
  rw [(ι.directed _ hd).2, ι.vert.apply_eq_iff_eq]
  exact Iff.rfl

theorem ChainRep.map_pointsBackward {c : Set E} (r : ChainRep G P c) :
    (r.map ι hP).PointsBackward ↔ r.PointsBackward := by
  unfold ChainRep.PointsBackward
  refine and_congr (exists_congr fun i => ι.isDirected_iff _) (forall_congr' fun i => ?_)
  change G'.IsDirected (ι.edge (r.e i)) →
    G'.graph.target (ι.edge (r.e i)) = ι.vert (r.p i.castSucc) ↔ _
  rw [ι.isDirected_iff]
  refine imp_congr_right fun hd => ?_
  rw [(ι.directed _ hd).2, ι.vert.apply_eq_iff_eq]
  exact Iff.rfl

theorem ChainRep.map_src {c : Set E} (r : ChainRep G P c) : (r.map ι hP).src = ι.vert r.src := by
  unfold ChainRep.src
  by_cases h : r.PointsBackward
  · simp only [(r.map_pointsBackward ι hP).mpr h, h, ↓reduceIte]
    rfl
  · simp only [mt (r.map_pointsBackward ι hP).mp h, h, ↓reduceIte]
    rfl

theorem ChainRep.map_tgt {c : Set E} (r : ChainRep G P c) : (r.map ι hP).tgt = ι.vert r.tgt := by
  unfold ChainRep.tgt
  by_cases h : r.PointsBackward
  · simp only [(r.map_pointsBackward ι hP).mpr h, h, ↓reduceIte]
    rfl
  · simp only [mt (r.map_pointsBackward ι hP).mp h, h, ↓reduceIte]
    rfl

omit [Finite E] in
theorem SDIso.symm_hP : ∀ u', ι.symm.vert u' ∈ P ↔ u' ∈ P' := fun u' => by
  rw [← hP, show ι.vert (ι.symm.vert u') = u' from ι.vert.apply_symm_apply u']

/-- The chains of `G'` are the images of those of `G`. -/
def SDIso.chainEquiv : {c : Set E // IsChain G P c} ≃ {c' : Set E' // IsChain G' P' c'} where
  toFun c := ⟨ι.edge '' c.1, c.2.map ι hP⟩
  invFun c' := ⟨ι.edge.symm '' c'.1, by
    have : Finite E' := Finite.of_equiv _ ι.edge
    exact c'.2.map ι.symm (ι.symm_hP hP)⟩
  left_inv c := Subtype.ext (ι.edge.symm_image_image c.1)
  right_inv c' := Subtype.ext (ι.edge.image_symm_image c'.1)

/-- **An isomorphism of semidirected networks is an isomorphism of the suppressed networks.** -/
def SDIso.suppressExcept : SDIso (suppressExcept G P) (suppressExcept G' P') where
  vert := ι.vert.subtypeEquiv fun u => (ι.isBranch_iff hP u).symm
  edge := ι.chainEquiv hP
  isDirected_iff c := by
    have : Finite E' := Finite.of_equiv _ ι.edge
    change (Banos2019.suppressExcept G' P').IsDirected ⟨ι.edge '' c.1, _⟩ ↔
      (Banos2019.suppressExcept G P).IsDirected ⟨c.1, c.2⟩
    rw [suppressExcept_isDirected_iff _ ((chainRep G P c.2).map ι hP),
      suppressExcept_isDirected_iff _ (chainRep G P c.2), ChainRep.map_pointsForward,
      ChainRep.map_pointsBackward]
  joins c := by
    have : Finite E' := Finite.of_equiv _ ι.edge
    have h := suppressExcept_ends (c.2.map ι hP) ((chainRep G P c.2).map ι hP)
    rw [ChainRep.map_src, ChainRep.map_tgt, ← suppressExcept_source_val c.2,
      ← suppressExcept_target_val c.2] at h
    unfold Joins
    simp only [Subtype.ext_iff, Equiv.subtypeEquiv_apply]
    exact h
  directed c hc := by
    have : Finite E' := Finite.of_equiv _ ι.edge
    have hd : ((chainRep G P c.2).map ι hP).PointsForward ∨
        ((chainRep G P c.2).map ι hP).PointsBackward := by
      rw [ChainRep.map_pointsForward, ChainRep.map_pointsBackward]
      exact hc
    have h := suppressExcept_ends_of_directed (c.2.map ι hP) _ hd
    rw [ChainRep.map_src, ChainRep.map_tgt, ← suppressExcept_source_val c.2,
      ← suppressExcept_target_val c.2] at h
    simp only [Subtype.ext_iff, Equiv.subtypeEquiv_apply]
    exact h
  leaf x := Subtype.ext (ι.leaf x)

end Transport

/-! ### The Challenge's suppression is the library's -/

namespace Model.SDNetwork

variable (G : Model.SDNetwork V E X) (P : Set V)

theorem isBranch_iff (u : V) : G.IsBranch P u ↔ Banos2019.IsBranch G.toSD P u := Iff.rfl

theorem isChainOf_iff {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E} :
    G.IsChainOf P k p e ↔ Banos2019.IsChainOf G.toSD P k p e :=
  ⟨fun h => ⟨h.pos, h.joins, h.inner, h.ends, h.injective_edge⟩,
    fun h => ⟨h.pos, h.joins, h.inner, h.ends, h.injective_edge⟩⟩

theorem isChain_iff (c : Set E) : G.IsChain P c ↔ Banos2019.IsChain G.toSD P c := by
  simp only [IsChain, Banos2019.IsChain, isChainOf_iff]

variable {G P} in
/-- An order on a chain, for the library. -/
def ChainRep.toLib {c : Set E} (r : G.ChainRep P c) : Banos2019.ChainRep G.toSD P c :=
  ⟨r.k, r.p, r.e, (G.isChainOf_iff P).mp r.isChainOf, r.range_eq⟩

theorem suppressExcept_source_val (c : {c : Set E // G.IsChain P c}) :
    ((G.suppressExcept P).graph.source c).1 = (G.chainRep P c.2).toLib.src := by
  unfold Banos2019.ChainRep.src
  simp only [suppressExcept]
  split_ifs with h₁ h₂ h₂ <;> first | rfl | exact absurd h₁ h₂ | exact absurd h₂ h₁

theorem suppressExcept_target_val (c : {c : Set E // G.IsChain P c}) :
    ((G.suppressExcept P).graph.target c).1 = (G.chainRep P c.2).toLib.tgt := by
  unfold Banos2019.ChainRep.tgt
  simp only [suppressExcept]
  split_ifs with h₁ h₂ h₂ <;> first | rfl | exact absurd h₁ h₂ | exact absurd h₂ h₁

/-- **The Challenge's suppression is the library's.** -/
def suppressIso [Finite E] :
    Banos2019.SDIso (G.suppressExcept P).toSD (Banos2019.suppressExcept G.toSD P) where
  vert := Equiv.subtypeEquivRight fun u => G.isBranch_iff P u
  edge := Equiv.subtypeEquivRight fun c => G.isChain_iff P c
  isDirected_iff c :=
    Banos2019.suppressExcept_isDirected_iff ((G.isChain_iff P c.1).mp c.2) (G.chainRep P c.2).toLib
  joins c := by
    have h := Banos2019.suppressExcept_ends ((G.isChain_iff P c.1).mp c.2) (G.chainRep P c.2).toLib
    rw [← suppressExcept_source_val, ← suppressExcept_target_val] at h
    unfold Joins
    simp only [Subtype.ext_iff, Equiv.subtypeEquivRight_apply_coe]
    exact h
  directed c hc := by
    have h := Banos2019.suppressExcept_ends_of_directed ((G.isChain_iff P c.1).mp c.2)
      (G.chainRep P c.2).toLib hc
    rw [← suppressExcept_source_val, ← suppressExcept_target_val] at h
    simp only [Subtype.ext_iff, Equiv.subtypeEquivRight_apply_coe]
    exact h
  leaf _ := rfl

theorem suppressIso_edge_val [Finite E] (c : {c : Set E // G.IsChain P c}) :
    ((G.suppressIso P).edge c).1 = c.1 := rfl

/-- The Challenge's parameters of a suppressed network are the library's. -/
def suppressMetricIso [Finite E] (θ : Params E) :
    Banos2019.SDMetricIso (G.suppressExcept ∅).toSD (G.suppressParams θ).toMetric
      (Banos2019.suppress G.toSD) (Banos2019.suppressMetric G.toSD θ.toMetric) where
  toSDIso := G.suppressIso ∅
  length _ := rfl
  inheritance _ _ := rfl

end Model.SDNetwork

end Banos2019
