module

public import Banos2019.Network.DirectedPath
public import Banos2019.Basic.Logic.RelationSymm

/-!
# The chains of a suppressed network and its isomorphisms

The edges of `suppressExcept G P` are the chains of `G`: maximal paths through nodes of degree two
that are neither taxa nor in `P`. This module shows that a chain is determined by any one of its
edges (`IsChain.eq_of_mem`), and gives the ends of a chain (`IsChainOf.chainEnds_eq`). From these,
an isomorphism of `suppressExcept G P` with a network `R` is given by a bijection of the kept nodes
with the nodes of `R` and, for each edge of `R`, a chain of `G` with the same ends and the same
hybrid edges (`exists_sdIso_suppressExcept`, `nonempty_sdMetricIso_suppress`).

* `IsUTrail`: a path of the undirected graph through distinct nodes, given edge by edge, and
  `IsUTrail.isChain`: such a path whose inner nodes are suppressed and whose ends are not is a
  chain.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-! ### Paths of the undirected graph -/

section Trail

variable (G : DirectedMultigraph V E)

/-- A path of the undirected graph from `u` to `w` through distinct nodes `S`, with edges `P`. -/
inductive IsUTrail : V → V → Set V → Set E → Prop
  | nil (u : V) : IsUTrail u u {u} ∅
  | cons {e : E} {a b w : V} {S : Set V} {P : Set E} :
      Joins G e a b → a ∉ S → IsUTrail b w S P → IsUTrail a w (insert a S) (insert e P)

variable {G}

namespace IsUTrail

variable {u w : V} {S : Set V} {P : Set E}

theorem start_mem (h : IsUTrail G u w S P) : u ∈ S := by
  cases h with
  | nil => exact rfl
  | cons => exact Set.mem_insert _ _

theorem end_mem (h : IsUTrail G u w S P) : w ∈ S := by
  induction h with
  | nil u => exact rfl
  | cons _ _ _ ih => exact Set.mem_insert_of_mem _ ih

theorem ends_mem (h : IsUTrail G u w S P) {e : E} (he : e ∈ P) :
    G.source e ∈ S ∧ G.target e ∈ S := by
  induction h with
  | nil u => exact absurd he (Set.notMem_empty e)
  | cons hj _ h ih =>
    rcases Set.mem_insert_iff.mp he with rfl | he
    · rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨h₁ ▸ Set.mem_insert _ _, h₂ ▸ Set.mem_insert_of_mem _ h.start_mem⟩
      · exact ⟨h₁ ▸ Set.mem_insert_of_mem _ h.start_mem, h₂ ▸ Set.mem_insert _ _⟩
    · obtain ⟨h₁, h₂⟩ := ih he
      exact ⟨Set.mem_insert_of_mem _ h₁, Set.mem_insert_of_mem _ h₂⟩

theorem append {v : V} {S₁ S₂ : Set V} {P₁ P₂ : Set E} (h₁ : IsUTrail G u v S₁ P₁)
    (h₂ : IsUTrail G v w S₂ P₂) (hS : S₁ ∩ S₂ ⊆ {v}) :
    IsUTrail G u w (S₁ ∪ S₂) (P₁ ∪ P₂) := by
  induction h₁ with
  | nil u =>
    rw [Set.singleton_union, Set.insert_eq_of_mem h₂.start_mem, Set.empty_union]
    exact h₂
  | @cons e a b v S P hj ha h ih =>
    rw [Set.insert_union, Set.insert_union]
    refine .cons hj ?_ (ih h₂ fun x hx => hS ⟨Set.mem_insert_of_mem _ hx.1, hx.2⟩)
    rintro (h' | h')
    · exact ha h'
    · have := hS ⟨Set.mem_insert _ _, h'⟩
      rw [Set.mem_singleton_iff.mp this] at ha
      exact ha h.end_mem

/-- A single edge. -/
theorem single {e : E} {a b : V} (hj : Joins G e a b) (hab : a ≠ b) :
    IsUTrail G a b {a, b} {e} := by
  have := IsUTrail.cons hj (fun h => hab (Set.mem_singleton_iff.mp h)) (.nil b)
  simpa using this

theorem reverse (h : IsUTrail G u w S P) : IsUTrail G w u S P := by
  induction h with
  | nil u => exact .nil u
  | @cons e a b w S P hj ha h ih =>
    have hab : a ≠ b := fun h' => ha (h' ▸ h.start_mem)
    have := ih.append (single (Or.symm hj) hab.symm) (by
      rintro x ⟨hx, hx' | hx'⟩
      · exact hx'
      · rw [Set.mem_singleton_iff.mp hx'] at hx
        exact absurd hx ha)
    rwa [Set.union_insert, Set.union_singleton,
      Set.insert_eq_of_mem (Set.mem_insert_of_mem _ h.start_mem), Set.union_singleton] at this

/-- A trail from a node to itself has no edge. -/
theorem edges_eq_empty_of_self {P : Set E} {S : Set V} (h : IsUTrail G u u S P) : P = ∅ := by
  cases h with
  | nil => rfl
  | cons _ ha h' => exact absurd h'.end_mem ha

/-- A trail as nodes and edges in order. -/
theorem exists_fin (h : IsUTrail G u w S P) :
    ∃ (k : ℕ) (p : Fin (k + 1) → V) (e : Fin k → E),
      (∀ i : Fin k, Joins G (e i) (p i.castSucc) (p i.succ)) ∧ Function.Injective p ∧
        Function.Injective e ∧ p 0 = u ∧ p (Fin.last k) = w ∧ Set.range p = S ∧
          Set.range e = P := by
  induction h with
  | nil u =>
    exact ⟨0, fun _ => u, Fin.elim0, fun i => i.elim0, fun i j _ => Fin.ext (by omega),
      fun i => i.elim0, rfl, rfl, Set.range_const, Set.range_eq_empty _⟩
  | @cons e a b w S P hj ha h ih =>
    obtain ⟨k, p, f, hjoin, hp, hf, h0, hlast, hS, hP⟩ := ih
    refine ⟨k + 1, (Fin.cons a p : Fin (k + 2) → V), (Fin.cons e f : Fin (k + 1) → E),
      fun i => ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_zero, Fin.cons_succ, h0]
        exact hj
      · rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hjoin i
    · refine Fin.cons_injective_iff.mpr ⟨fun hm => ?_, hp⟩
      rw [hS] at hm
      exact ha hm
    · refine Fin.cons_injective_iff.mpr ⟨fun hm => ?_, hf⟩
      rw [hP] at hm
      have := (h.ends_mem hm)
      rcases hj with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact ha (h₁ ▸ this.1)
      · exact ha (h₂ ▸ this.2)
    · rw [← Fin.succ_last, Fin.cons_succ, hlast]
    · rw [Fin.range_cons, hS]
    · rw [Fin.range_cons, hP]

end IsUTrail

/-- A directed path of an acyclic graph is a path of its undirected graph. -/
theorem IsDPath.isUTrail (hA : G.IsAcyclic) {u w : V} {S : Set V} {P : Set E}
    (h : IsDPath G u w S P) : IsUTrail G u w S P := by
  induction h with
  | nil u => exact .nil u
  | cons e h ih =>
    exact .cons (Or.inl ⟨rfl, rfl⟩) (fun hm => not_reaches_target_source_of_isAcyclic hA e
      (h.reaches_of_mem hm).1) ih

end Trail

/-! ### Chains -/

section Chains

variable (G : SemidirectedNetwork V E X) (P : Set V)

/-- Two edges meet at a node that suppression removes. -/
def ChainLink (g g' : E) : Prop :=
  ∃ u, ¬ IsBranch G P u ∧ (G.graph.source g = u ∨ G.graph.target g = u) ∧
    (G.graph.source g' = u ∨ G.graph.target g' = u)

/-- The ends of a set of edges: the kept nodes at which they meet. -/
def chainEnds (c : Set E) : Set V :=
  {u | IsBranch G P u ∧ ∃ g ∈ c, G.graph.source g = u ∨ G.graph.target g = u}

variable {G P}

theorem chainLink_symm {g g' : E} (h : ChainLink G P g g') : ChainLink G P g' g := by
  obtain ⟨u, hu, h₁, h₂⟩ := h
  exact ⟨u, hu, h₂, h₁⟩

/-- At a node of degree two, two distinct edges are all the edges. -/
theorem eq_or_eq_of_degree_eq_two [Finite E] {u : V} (hu : degree G.graph u = 2) {g₁ g₂ g₃ : E}
    (h₁ : G.graph.source g₁ = u ∨ G.graph.target g₁ = u)
    (h₂ : G.graph.source g₂ = u ∨ G.graph.target g₂ = u)
    (h₃ : G.graph.source g₃ = u ∨ G.graph.target g₃ = u) (h₁₂ : g₁ ≠ g₂) :
    g₃ = g₁ ∨ g₃ = g₂ := by
  by_contra hne
  push Not at hne
  have h3 : ({g₁, g₂, g₃} : Set E).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨g₁, g₂, g₃, h₁₂, hne.1.symm, hne.2.symm, rfl⟩
  have hsub : ({g₁, g₂, g₃} : Set E) ⊆ {g | G.graph.target g = u} ∪ {g | G.graph.source g = u} := by
    rintro g (rfl | rfl | rfl)
    · exact h₁.symm.imp id id
    · exact h₂.symm.imp id id
    · exact h₃.symm.imp id id
  have := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree at hu
  omega

/-- The node `p j` of a chain is an inner node when it is not kept. -/
theorem IsChainOf.inner_of_not_isBranch {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    (h : IsChainOf G P k p e) {j : Fin (k + 1)} (hj : ¬ IsBranch G P (p j)) :
    j ≠ 0 ∧ j ≠ Fin.last k := by
  refine ⟨fun h0 => hj (h0 ▸ h.ends.1), fun hl => hj (hl ▸ h.ends.2)⟩

/-- The ends of the edge `e i` of a chain are `p i` and `p (i + 1)`. -/
theorem IsChainOf.eq_of_incident {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    (h : IsChainOf G P k p e) {i : Fin k} {u : V}
    (hu : G.graph.source (e i) = u ∨ G.graph.target (e i) = u) :
    u = p i.castSucc ∨ u = p i.succ := by
  rcases h.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hu with hu | hu
  · exact Or.inl (hu.symm.trans h₁)
  · exact Or.inr (hu.symm.trans h₂)
  · exact Or.inr (hu.symm.trans h₁)
  · exact Or.inl (hu.symm.trans h₂)

/-- **A chain is closed under meeting at removed nodes.** -/
theorem IsChainOf.mem_of_chainLink [Finite E] {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    (h : IsChainOf G P k p e) {i : Fin k} {g : E} (hl : ChainLink G P (e i) g) :
    g ∈ Set.range e := by
  obtain ⟨u, hu, h₁, h₂⟩ := hl
  have hdeg : degree G.graph u = 2 := by
    by_contra hd
    exact hu (Or.inl hd)
  -- `u` is an inner node `p j`
  obtain ⟨j, rfl⟩ : ∃ j, u = p j := (h.eq_of_incident h₁).elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  obtain ⟨hj0, hjl⟩ := h.inner_of_not_isBranch hu
  have hj1 : 1 ≤ j.val := by
    rcases Nat.eq_zero_or_pos j.val with h' | h'
    · exact absurd (Fin.ext h') hj0
    · exact h'
  have hjk : j.val < k := by
    have := j.isLt
    have : j.val ≠ k := fun h' => hjl (Fin.ext h')
    omega
  set a : Fin k := ⟨j.val - 1, by omega⟩
  set b : Fin k := ⟨j.val, hjk⟩
  have ha : a.succ = j := Fin.ext (by simp [a]; omega)
  have hb : b.castSucc = j := Fin.ext rfl
  have hinc : ∀ c : Fin k, (c.succ = j ∨ c.castSucc = j) →
      G.graph.source (e c) = p j ∨ G.graph.target (e c) = p j := by
    intro c hc
    rcases h.joins c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hc with hc | hc <;> rw [← hc]
    · exact Or.inr h₂
    · exact Or.inl h₁
    · exact Or.inl h₁
    · exact Or.inr h₂
  have hab : e a ≠ e b := fun h' => by
    have := congrArg Fin.val (h.injective_edge h')
    simp [a, b] at this
    omega
  rcases eq_or_eq_of_degree_eq_two hdeg (hinc a (Or.inl ha)) (hinc b (Or.inr hb)) h₂ hab with
    h' | h'
  · exact ⟨a, h'.symm⟩
  · exact ⟨b, h'.symm⟩

/-- **The edges of a chain are linked through its inner nodes.** -/
theorem IsChainOf.linked {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    (h : IsChainOf G P k p e) (i j : Fin k) :
    Relation.ReflTransGen (ChainLink G P) (e i) (e j) := by
  have h0 : ∀ (t : ℕ) (ht : t < k), Relation.ReflTransGen (ChainLink G P) (e ⟨0, by omega⟩)
      (e ⟨t, ht⟩) := by
    intro t
    induction t with
    | zero => exact fun _ => .refl
    | succ t ih =>
      intro ht
      refine (ih (by omega)).tail ⟨p ⟨t + 1, by omega⟩, h.inner _ ?_ ?_, ?_, ?_⟩
      · exact fun h' => by simpa using congrArg Fin.val h'
      · exact fun h' => by simp [Fin.ext_iff] at h'; omega
      · rcases h.joins ⟨t, by omega⟩ with ⟨-, h₂⟩ | ⟨h₁, -⟩
        · exact Or.inr h₂
        · exact Or.inl h₁
      · rcases h.joins ⟨t + 1, ht⟩ with ⟨h₁, -⟩ | ⟨-, h₂⟩
        · exact Or.inl h₁
        · exact Or.inr h₂
  have hk : 0 < k := h.pos
  exact (Relation.ReflTransGen.symm_of_symm (fun _ _ => chainLink_symm) (h0 i.val i.isLt)).trans
    (h0 j.val j.isLt)

/-- **A chain is the set of edges linked to any one of its edges.** -/
theorem IsChain.eq_setOf [Finite E] {c : Set E} (hc : IsChain G P c) {g : E} (hg : g ∈ c) :
    c = {g' | Relation.ReflTransGen (ChainLink G P) g g'} := by
  obtain ⟨k, p, e, h, rfl⟩ := hc
  obtain ⟨i, rfl⟩ := hg
  ext g'
  constructor
  · rintro ⟨j, rfl⟩
    exact h.linked i j
  · intro hl
    induction hl with
    | refl => exact ⟨i, rfl⟩
    | tail _ hab ih =>
      obtain ⟨i', rfl⟩ := ih
      exact h.mem_of_chainLink hab

/-- **Two chains with a common edge are the same.** -/
theorem IsChain.eq_of_mem [Finite E] {c c' : Set E} (hc : IsChain G P c) (hc' : IsChain G P c')
    {g : E} (hg : g ∈ c) (hg' : g ∈ c') : c = c' :=
  (hc.eq_setOf hg).trans (hc'.eq_setOf hg').symm

/-- **The ends of a chain** are its first and last nodes. -/
theorem IsChainOf.chainEnds_eq {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    (h : IsChainOf G P k p e) : chainEnds G P (Set.range e) = {p 0, p (Fin.last k)} := by
  have hk := h.pos
  ext u
  constructor
  · rintro ⟨hu, _, ⟨i, rfl⟩, hi⟩
    rcases h.eq_of_incident hi with rfl | rfl
    · by_cases h0 : i.castSucc = 0
      · exact Or.inl (by rw [h0])
      · by_cases hl : i.castSucc = Fin.last k
        · exact Or.inr (by rw [hl]; exact Set.mem_singleton _)
        · exact absurd hu (h.inner _ h0 hl)
    · by_cases h0 : i.succ = 0
      · exact Or.inl (by rw [h0])
      · by_cases hl : i.succ = Fin.last k
        · exact Or.inr (by rw [hl]; exact Set.mem_singleton _)
        · exact absurd hu (h.inner _ h0 hl)
  · rintro (rfl | rfl)
    · refine ⟨h.ends.1, _, ⟨⟨0, hk⟩, rfl⟩, ?_⟩
      rcases h.joins ⟨0, hk⟩ with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact Or.inl h₁
      · exact Or.inr h₂
    · refine ⟨h.ends.2, _, ⟨⟨k - 1, by omega⟩, rfl⟩, ?_⟩
      have : (⟨k - 1, by omega⟩ : Fin k).succ = Fin.last k := Fin.ext (by simp; omega)
      rcases h.joins ⟨k - 1, by omega⟩ with ⟨-, h₂⟩ | ⟨h₁, -⟩
      · exact Or.inr (this ▸ h₂)
      · exact Or.inl (this ▸ h₁)

/-- A path of the undirected graph whose inner nodes are removed by suppression and whose ends are
kept is a chain. -/
theorem IsUTrail.isChainOf {u w : V} {S : Set V} {Q : Set E} (h : IsUTrail G.graph u w S Q)
    (hQ : Q.Nonempty) (hu : IsBranch G P u) (hw : IsBranch G P w)
    (hin : ∀ s ∈ S, s ≠ u → s ≠ w → ¬ IsBranch G P s) :
    ∃ (k : ℕ) (p : Fin (k + 1) → V) (e : Fin k → E), IsChainOf G P k p e ∧ Set.range e = Q ∧
      p 0 = u ∧ p (Fin.last k) = w := by
  obtain ⟨k, p, e, hjoin, hp, he, h0, hlast, hS, hQe⟩ := h.exists_fin
  refine ⟨k, p, e, ⟨?_, hjoin, fun i hi0 hil => ?_, ⟨h0 ▸ hu, hlast ▸ hw⟩, he⟩, hQe, h0, hlast⟩
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [← hQe] at hQ
      obtain ⟨_, ⟨i, -⟩⟩ := hQ
      exact i.elim0
    · exact hk
  · refine hin _ (hS ▸ ⟨i, rfl⟩) (fun h' => hi0 (hp (h'.trans h0.symm))) fun h' =>
      hil (hp (h'.trans hlast.symm))

theorem IsUTrail.isChain {u w : V} {S : Set V} {Q : Set E} (h : IsUTrail G.graph u w S Q)
    (hQ : Q.Nonempty) (hu : IsBranch G P u) (hw : IsBranch G P w)
    (hin : ∀ s ∈ S, s ≠ u → s ≠ w → ¬ IsBranch G P s) : IsChain G P Q := by
  obtain ⟨k, p, e, hc, hQe, -, -⟩ := h.isChainOf hQ hu hw hin
  exact ⟨k, p, e, hc, hQe⟩

/-- The ends of a chain given by a path of the undirected graph are the ends of the path. -/
theorem IsUTrail.chainEnds_eq {u w : V} {S : Set V} {Q : Set E} (h : IsUTrail G.graph u w S Q)
    (hQ : Q.Nonempty) (hu : IsBranch G P u) (hw : IsBranch G P w)
    (hin : ∀ s ∈ S, s ≠ u → s ≠ w → ¬ IsBranch G P s) : chainEnds G P Q = {u, w} := by
  obtain ⟨k, p, e, hc, hQe, h0, hlast⟩ := h.isChainOf hQ hu hw hin
  rw [← hQe, hc.chainEnds_eq, h0, hlast]

end Chains

/-! ### Isomorphisms of a suppressed network -/

section Iso

variable {V' E' : Type*}

/-- In a chain whose hybrid edges all enter its end `t`, they point toward `t`. -/
theorem IsChainOf.pointsTo {G : SemidirectedNetwork V E X} {P : Set V} {k : ℕ}
    {p : Fin (k + 1) → V} {e : Fin k → E} (h : IsChainOf G P k p e) (hne : p 0 ≠ p (Fin.last k))
    {t : V} (hdir : ∀ i, G.IsDirected (e i) → G.graph.target (e i) = t) :
    (t = p (Fin.last k) → ∀ i, G.IsDirected (e i) → G.graph.target (e i) = p i.succ) ∧
      (t = p 0 → ∀ i, G.IsDirected (e i) → G.graph.target (e i) = p i.castSucc) := by
  have hk := h.pos
  constructor
  · rintro rfl i hi
    have ht := hdir i hi
    rcases h.joins i with ⟨-, h₂⟩ | ⟨-, h₂⟩
    · exact h₂
    · -- the edge enters `p i`, which is then the last node, so `i = 0` and `p 0` is the last node
      rw [h₂] at ht
      have hb : IsBranch G P (p i.castSucc) := ht ▸ h.ends.2
      by_cases h0 : i.castSucc = 0
      · exact absurd (h0 ▸ ht) hne
      · by_cases hl : i.castSucc = Fin.last k
        · exact absurd hl (Fin.castSucc_ne_last i)
        · exact absurd hb (h.inner _ h0 hl)
  · rintro rfl i hi
    have ht := hdir i hi
    rcases h.joins i with ⟨-, h₂⟩ | ⟨-, h₂⟩
    · rw [h₂] at ht
      have hb : IsBranch G P (p i.succ) := ht ▸ h.ends.1
      by_cases h0 : i.succ = 0
      · exact absurd h0 (Fin.succ_ne_zero i)
      · by_cases hl : i.succ = Fin.last k
        · exact absurd (hl ▸ ht).symm hne
        · exact absurd hb (h.inner _ h0 hl)
    · exact h₂

/-- **An isomorphism of a suppressed network**, from a bijection `φ` of the kept nodes with the
nodes of `R` and, for each edge `f` of `R`, a chain `chainOf f` of `G`, such that every edge of `G`
is on the chain of exactly one edge `ψ g` of `R`; the ends of the chain of `f` are the ends of `f`;
`f` is hybrid exactly when its chain has a hybrid edge, and the hybrid edges of the chain enter the
target of `f`. -/
theorem exists_sdIso_suppressExcept [Finite E] {G : SemidirectedNetwork V E X} {P : Set V}
    {R : SemidirectedNetwork V' E' X} (φ : {u // IsBranch G P u} ≃ V') (chainOf : E' → Set E)
    (hchain : ∀ f, IsChain G P (chainOf f)) (ψ : E → E') (hψ : ∀ g, g ∈ chainOf (ψ g))
    (hψ' : ∀ f, ∀ g ∈ chainOf f, ψ g = f)
    (hends : ∀ f, chainEnds G P (chainOf f) =
      {(φ.symm (R.graph.source f)).1, (φ.symm (R.graph.target f)).1})
    (hne : ∀ f, R.graph.source f ≠ R.graph.target f)
    (hdir : ∀ f, R.IsDirected f ↔ ∃ g ∈ chainOf f, G.IsDirected g)
    (hdir_tgt : ∀ f, ∀ g ∈ chainOf f, G.IsDirected g →
      G.graph.target g = (φ.symm (R.graph.target f)).1)
    (hleaf : ∀ x, R.leaf x = φ ⟨G.leaf x, Or.inr (Or.inl ⟨x, rfl⟩)⟩) :
    ∃ ι : SDIso (suppressExcept G P) R, ∀ c, c.1 = chainOf (ι.edge c) := by
  classical
  -- an edge of the suppressed network is the chain of one edge of `R`
  have hmem : ∀ c : {c : Set E // IsChain G P c}, ∃ g, g ∈ c.1 := fun c => by
    obtain ⟨k, p, e, h, hc⟩ := c.2
    exact ⟨e ⟨0, h.pos⟩, hc ▸ ⟨_, rfl⟩⟩
  let edge : {c : Set E // IsChain G P c} ≃ E' :=
    { toFun := fun c => ψ (hmem c).choose
      invFun := fun f => ⟨chainOf f, hchain f⟩
      left_inv := fun c => Subtype.ext ((hchain _).eq_of_mem c.2 (hψ _) (hmem c).choose_spec)
      right_inv := fun f => hψ' f _ (hmem ⟨chainOf f, hchain f⟩).choose_spec }
  have hedge : ∀ c, c.1 = chainOf (edge c) := fun c => by
    have := edge.left_inv c
    exact (congrArg Subtype.val this).symm
  refine ⟨⟨φ, edge, fun c => ?_, fun c => ?_, fun c hc => ?_, hleaf⟩, hedge⟩
  all_goals
    set f := edge c with hf
    set r := chainRep G P c.2
    have hr : Set.range r.e = chainOf f := r.range_eq.trans (hedge c)
    have hends' : ({r.p 0, r.p (Fin.last r.k)} : Set V) =
        {(φ.symm (R.graph.source f)).1, (φ.symm (R.graph.target f)).1} := by
      rw [← r.isChainOf.chainEnds_eq, hr, hends]
    have hne' : r.p 0 ≠ r.p (Fin.last r.k) := by
      intro h0
      rw [h0, Set.pair_eq_singleton] at hends'
      have h₁ : (φ.symm (R.graph.source f)).1 ∈ ({r.p (Fin.last r.k)} : Set V) :=
        hends' ▸ Or.inl rfl
      have h₂ : (φ.symm (R.graph.target f)).1 ∈ ({r.p (Fin.last r.k)} : Set V) :=
        hends' ▸ Or.inr rfl
      exact hne f (φ.symm.injective (Subtype.ext ((Set.mem_singleton_iff.mp h₁).trans
        (Set.mem_singleton_iff.mp h₂).symm)))
    have hdir' : ∀ i, G.IsDirected (r.e i) → G.graph.target (r.e i) =
        (φ.symm (R.graph.target f)).1 := fun i hi =>
      hdir_tgt f (r.e i) (hr ▸ ⟨i, rfl⟩) hi
    have ht_end : (φ.symm (R.graph.target f)).1 = r.p 0 ∨
        (φ.symm (R.graph.target f)).1 = r.p (Fin.last r.k) := by
      have : (φ.symm (R.graph.target f)).1 ∈ ({r.p 0, r.p (Fin.last r.k)} : Set V) :=
        hends'.symm ▸ Or.inr rfl
      exact this
    have hs_end : (φ.symm (R.graph.source f)).1 = r.p 0 ∨
        (φ.symm (R.graph.source f)).1 = r.p (Fin.last r.k) := by
      have : (φ.symm (R.graph.source f)).1 ∈ ({r.p 0, r.p (Fin.last r.k)} : Set V) :=
        hends'.symm ▸ Or.inl rfl
      exact this
    have hst : (φ.symm (R.graph.source f)).1 ≠ (φ.symm (R.graph.target f)).1 := fun h =>
      hne f (φ.symm.injective (Subtype.ext h))
    have hpts := r.isChainOf.pointsTo hne' hdir'
    have hφs : ∀ (u : V) (hu : IsBranch G P u), u = (φ.symm (R.graph.source f)).1 →
        φ ⟨u, hu⟩ = R.graph.source f := fun u hu h => by
      rw [show (⟨u, hu⟩ : {u // IsBranch G P u}) = φ.symm (R.graph.source f) from Subtype.ext h,
        Equiv.apply_symm_apply]
    have hφt : ∀ (u : V) (hu : IsBranch G P u), u = (φ.symm (R.graph.target f)).1 →
        φ ⟨u, hu⟩ = R.graph.target f := fun u hu h => by
      rw [show (⟨u, hu⟩ : {u // IsBranch G P u}) = φ.symm (R.graph.target f) from Subtype.ext h,
        Equiv.apply_symm_apply]
  · -- hybrid edges
    rw [hdir f]
    change _ ↔ r.PointsForward ∨ r.PointsBackward
    constructor
    · rintro ⟨g, hg, hgd⟩
      rw [← hr] at hg
      obtain ⟨i, rfl⟩ := hg
      rcases ht_end with h | h
      · exact Or.inr ⟨⟨i, hgd⟩, hpts.2 h⟩
      · exact Or.inl ⟨⟨i, hgd⟩, hpts.1 h⟩
    · rintro (⟨⟨i, hi⟩, -⟩ | ⟨⟨i, hi⟩, -⟩) <;> exact ⟨r.e i, hr ▸ ⟨i, rfl⟩, hi⟩
  · -- the ends
    change Joins R.graph f (φ (if r.PointsBackward then _ else _))
      (φ (if r.PointsBackward then _ else _))
    split_ifs
    · rcases hs_end with h | h
      · have h' := ht_end.resolve_left (fun h'' => hst (h.trans h''.symm))
        exact Or.inr ⟨(hφs _ _ h.symm).symm, (hφt _ _ h'.symm).symm⟩
      · have h' := ht_end.resolve_right (fun h'' => hst (h.trans h''.symm))
        exact Or.inl ⟨(hφs _ _ h.symm).symm, (hφt _ _ h'.symm).symm⟩
    · rcases hs_end with h | h
      · have h' := ht_end.resolve_left (fun h'' => hst (h.trans h''.symm))
        exact Or.inl ⟨(hφs _ _ h.symm).symm, (hφt _ _ h'.symm).symm⟩
      · have h' := ht_end.resolve_right (fun h'' => hst (h.trans h''.symm))
        exact Or.inr ⟨(hφs _ _ h.symm).symm, (hφt _ _ h'.symm).symm⟩
  · -- the direction of a hybrid edge
    change r.PointsForward ∨ r.PointsBackward at hc
    have hback : r.PointsBackward ↔ (φ.symm (R.graph.target f)).1 = r.p 0 := by
      constructor
      · rintro ⟨⟨i, hi⟩, hb⟩
        rcases ht_end with h | h
        · exact h
        · have h₁ := hpts.1 h i hi
          have h₂ := hb i hi
          rw [h₂] at h₁
          -- `p i = p (i + 1)` would make `p 0 = p last`
          have hb' : IsBranch G P (r.p i.castSucc) := by
            rw [← h₂, hdir' i hi, h]
            exact r.isChainOf.ends.2
          by_cases h0 : i.castSucc = 0
          · rw [h0] at hb'
            exfalso
            have : r.p 0 = r.p (Fin.last r.k) := by
              rw [← h0, ← h₂, hdir' i hi, h]
            exact hne' this
          · by_cases hl : i.castSucc = Fin.last r.k
            · exact absurd hl (Fin.castSucc_ne_last i)
            · exact absurd hb' (r.isChainOf.inner _ h0 hl)
      · intro h
        rcases hc with ⟨⟨i, hi⟩, -⟩ | hb
        · exact ⟨⟨i, hi⟩, hpts.2 h⟩
        · exact hb
    change R.graph.source f = φ (if r.PointsBackward then _ else _) ∧
      R.graph.target f = φ (if r.PointsBackward then _ else _)
    split_ifs with hb
    · have h := hback.mp hb
      have h' := hs_end.resolve_left (fun h'' => hst (h''.trans h.symm))
      exact ⟨(hφs _ _ h'.symm).symm, (hφt _ _ h.symm).symm⟩
    · have h : (φ.symm (R.graph.target f)).1 = r.p (Fin.last r.k) :=
        ht_end.resolve_left fun h => hb (hback.mpr h)
      have h' := hs_end.resolve_right (fun h'' => hst (h''.trans h.symm))
      exact ⟨(hφs _ _ h'.symm).symm, (hφt _ _ h.symm).symm⟩

/-- **A metric isomorphism of a suppressed network**: as `exists_sdIso_suppressExcept`, when the
length of each edge of `R` is the sum of the lengths of its chain, and the inheritance probability
of a hybrid edge of `R` is the product of those of the hybrid edges of its chain. -/
theorem nonempty_sdMetricIso_suppress [Finite E] {G : SemidirectedNetwork V E X}
    {R : SemidirectedNetwork V' E' X} (θ : MetricData E) (θ' : MetricData E')
    (φ : {u // IsBranch G ∅ u} ≃ V') (chainOf : E' → Set E)
    (hchain : ∀ f, IsChain G ∅ (chainOf f)) (ψ : E → E') (hψ : ∀ g, g ∈ chainOf (ψ g))
    (hψ' : ∀ f, ∀ g ∈ chainOf f, ψ g = f)
    (hends : ∀ f, chainEnds G ∅ (chainOf f) =
      {(φ.symm (R.graph.source f)).1, (φ.symm (R.graph.target f)).1})
    (hne : ∀ f, R.graph.source f ≠ R.graph.target f)
    (hdir : ∀ f, R.IsDirected f ↔ ∃ g ∈ chainOf f, G.IsDirected g)
    (hdir_tgt : ∀ f, ∀ g ∈ chainOf f, G.IsDirected g →
      G.graph.target g = (φ.symm (R.graph.target f)).1)
    (hleaf : ∀ x, R.leaf x = φ ⟨G.leaf x, Or.inr (Or.inl ⟨x, rfl⟩)⟩)
    (hlen : ∀ f, θ'.length f = ∑ᶠ g ∈ chainOf f, θ.length g)
    (hinh : ∀ f, R.IsDirected f →
      θ'.inheritance f = ∏ᶠ g ∈ {g | g ∈ chainOf f ∧ G.IsDirected g}, θ.inheritance g) :
    Nonempty (SDMetricIso (suppress G) (suppressMetric G θ) R θ') := by
  obtain ⟨ι, hι⟩ := exists_sdIso_suppressExcept φ chainOf hchain ψ hψ hψ' hends hne hdir hdir_tgt
    hleaf
  refine ⟨⟨ι, fun c => ?_, fun c hc => ?_⟩⟩
  · rw [hlen, ← hι c]
    rfl
  · rw [hinh _ ((ι.isDirected_iff c).mpr hc), ← hι c]
    rfl

end Iso

end Banos2019
