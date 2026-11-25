module

public import Banos2019.Network.Semidirected
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.Order

/-!
# Directed paths in an acyclic graph

A directed walk `IsDPath G u w S P` from `u` to `w`, with node set `S` and arc set `P`, given by
its arcs one after the other. In an acyclic graph it is a path, and its nodes are ordered by
reachability, so that a part of it is determined by its two ends (`IsDPath.segment`). These are the
paths of the rooted network in the proof of Lemma 17 and of Proposition 1.

* `IsDPath`, `IsDPath.append`, `IsDPath.exists_split`, `IsDPath.segment`.
* `IsDPath.isSDPath`: a directed path is a semidirected path of any semidirected network on the
  same graph.
* `reachOrder`: the reachability order of an acyclic graph.
-/

@[expose] public noncomputable section

open Phylogenetics

namespace Banos2019

variable {V E X : Type*}

section DPath

variable (G : DirectedMultigraph V E)

/-- A directed walk from `u` to `w`, with nodes `S` and arcs `P`. In an acyclic graph its nodes are
distinct. -/
inductive IsDPath : V → V → Set V → Set E → Prop
  | nil (u : V) : IsDPath u u {u} ∅
  | cons (e : E) {w : V} {S : Set V} {P : Set E} :
      IsDPath (G.target e) w S P → IsDPath (G.source e) w (insert (G.source e) S) (insert e P)

/-- The reachability order of an acyclic graph: `u ≤ w` when a directed path leads from `u` to `w`. -/
@[reducible] def reachOrder (hA : G.IsAcyclic) : PartialOrder V where
  le := G.Reaches
  le_refl _ := .refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm a b h h' := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with h | ht
    · exact h.symm
    · exact absurd (ht.trans_left h') (hA a)

variable {G}

/-- In an acyclic graph, mutual reachability is equality. -/
theorem reaches_antisymm (hA : G.IsAcyclic) {a b : V} (h : G.Reaches a b) (h' : G.Reaches b a) :
    a = b :=
  (reachOrder G hA).le_antisymm a b h h'

/-- In an acyclic graph, the target of an arc does not reach its source. -/
theorem not_reaches_target_source' (hA : G.IsAcyclic) (e : E) :
    ¬ G.Reaches (G.target e) (G.source e) := fun h =>
  hA _ (Relation.TransGen.head' ⟨e, rfl, rfl⟩ h)

namespace IsDPath

variable {u w : V} {S : Set V} {P : Set E}

theorem reaches (h : IsDPath G u w S P) : G.Reaches u w := by
  induction h with
  | nil u => exact .refl
  | cons e _ ih => exact ih.head ⟨e, rfl, rfl⟩

theorem start_mem (h : IsDPath G u w S P) : u ∈ S := by
  cases h with
  | nil => exact rfl
  | cons => exact Set.mem_insert _ _

theorem end_mem (h : IsDPath G u w S P) : w ∈ S := by
  induction h with
  | nil u => exact rfl
  | cons e _ ih => exact Set.mem_insert_of_mem _ ih

theorem reaches_of_mem (h : IsDPath G u w S P) {s : V} (hs : s ∈ S) :
    G.Reaches u s ∧ G.Reaches s w := by
  induction h with
  | nil u =>
    rw [Set.mem_singleton_iff.mp hs]
    exact ⟨.refl, .refl⟩
  | cons e h ih =>
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact ⟨.refl, h.reaches.head ⟨e, rfl, rfl⟩⟩
    · obtain ⟨h₁, h₂⟩ := ih hs
      exact ⟨h₁.head ⟨e, rfl, rfl⟩, h₂⟩

theorem ends_mem (h : IsDPath G u w S P) {e : E} (he : e ∈ P) :
    G.source e ∈ S ∧ G.target e ∈ S := by
  induction h with
  | nil u => exact absurd he (Set.notMem_empty e)
  | cons f h ih =>
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ h.start_mem⟩
    · obtain ⟨h₁, h₂⟩ := ih he
      exact ⟨Set.mem_insert_of_mem _ h₁, Set.mem_insert_of_mem _ h₂⟩

/-- The nodes of a walk are ordered by reachability. -/
theorem total (h : IsDPath G u w S P) {s t : V} (hs : s ∈ S) (ht : t ∈ S) :
    G.Reaches s t ∨ G.Reaches t s := by
  induction h with
  | nil u =>
    rw [Set.mem_singleton_iff.mp hs, Set.mem_singleton_iff.mp ht]
    exact Or.inl .refl
  | cons e h ih =>
    rcases Set.mem_insert_iff.mp hs with rfl | hs <;> rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact Or.inl .refl
    · exact Or.inl ((h.reaches_of_mem ht).1.head ⟨e, rfl, rfl⟩)
    · exact Or.inr ((h.reaches_of_mem hs).1.head ⟨e, rfl, rfl⟩)
    · exact ih hs ht

/-- A node of a walk through an arc is above the arc or below it. -/
theorem mem_or (h : IsDPath G u w S P) {e : E} (he : e ∈ P) {s : V} (hs : s ∈ S) :
    G.Reaches s (G.source e) ∨ G.Reaches (G.target e) s := by
  induction h with
  | nil u => exact absurd he (Set.notMem_empty e)
  | cons f h ih =>
    rcases Set.mem_insert_iff.mp he with rfl | he
    · rcases Set.mem_insert_iff.mp hs with rfl | hs
      · exact Or.inl .refl
      · exact Or.inr (h.reaches_of_mem hs).1
    · rcases Set.mem_insert_iff.mp hs with rfl | hs
      · exact Or.inl (((h.reaches_of_mem (h.ends_mem he).1).1).head ⟨f, rfl, rfl⟩)
      · exact ih he hs

theorem append {v : V} {S₁ S₂ : Set V} {P₁ P₂ : Set E} (h₁ : IsDPath G u v S₁ P₁)
    (h₂ : IsDPath G v w S₂ P₂) : IsDPath G u w (S₁ ∪ S₂) (P₁ ∪ P₂) := by
  induction h₁ with
  | nil u =>
    rw [Set.singleton_union, Set.insert_eq_of_mem h₂.start_mem, Set.empty_union]
    exact h₂
  | cons e _ ih =>
    rw [Set.insert_union, Set.insert_union]
    exact .cons e (ih h₂)

theorem exists_split (h : IsDPath G u w S P) {v : V} (hv : v ∈ S) :
    ∃ S₁ P₁ S₂ P₂, IsDPath G u v S₁ P₁ ∧ IsDPath G v w S₂ P₂ ∧ S = S₁ ∪ S₂ ∧ P = P₁ ∪ P₂ := by
  induction h with
  | nil u =>
    rw [Set.mem_singleton_iff.mp hv]
    exact ⟨{u}, ∅, {u}, ∅, .nil u, .nil u, by simp, by simp⟩
  | cons e h ih =>
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · refine ⟨{G.source e}, ∅, _, _, .nil _, .cons e h, ?_, by simp⟩
      rw [Set.singleton_union, Set.insert_eq_of_mem (Set.mem_insert _ _)]
    · obtain ⟨S₁, P₁, S₂, P₂, h₁, h₂, rfl, rfl⟩ := ih hv
      exact ⟨_, _, S₂, P₂, .cons e h₁, h₂, by rw [Set.insert_union], by rw [Set.insert_union]⟩

/-- **A part of a path in an acyclic graph**, between two of its nodes: its nodes are those of the
path between them, and its arcs are those of the path between them. -/
theorem segment (hA : G.IsAcyclic) (h : IsDPath G u w S P) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (hab : G.Reaches a b) :
    ∃ P', IsDPath G a b {s | s ∈ S ∧ G.Reaches a s ∧ G.Reaches s b} P' ∧ P' ⊆ P ∧
      ∀ e ∈ P, G.Reaches a (G.source e) → G.Reaches (G.target e) b → e ∈ P' := by
  obtain ⟨S₁, P₁, S₂, P₂, h₁, h₂, rfl, rfl⟩ := h.exists_split ha
  have hb₂ : b ∈ S₂ := by
    rcases hb with hb | hb
    · rw [reaches_antisymm hA (h₁.reaches_of_mem hb).2 hab]
      exact h₂.start_mem
    · exact hb
  obtain ⟨S₃, P₃, S₄, P₄, h₃, h₄, rfl, rfl⟩ := h₂.exists_split hb₂
  have hS : {s | s ∈ S₁ ∪ (S₃ ∪ S₄) ∧ G.Reaches a s ∧ G.Reaches s b} = S₃ := by
    ext s
    constructor
    · rintro ⟨hs | hs | hs, has, hsb⟩
      · rw [reaches_antisymm hA (h₁.reaches_of_mem hs).2 has]
        exact h₃.start_mem
      · exact hs
      · rw [reaches_antisymm hA hsb (h₄.reaches_of_mem hs).1]
        exact h₃.end_mem
    · intro hs
      exact ⟨Or.inr (Or.inl hs), h₃.reaches_of_mem hs⟩
  rw [hS]
  refine ⟨P₃, h₃, fun e he => Or.inr (Or.inl he), fun e he hae heb => ?_⟩
  rcases he with he | he | he
  · exact absurd (((h₁.reaches_of_mem (h₁.ends_mem he).2).2).trans hae)
      (not_reaches_target_source' hA e)
  · exact he
  · exact absurd (heb.trans (h₄.reaches_of_mem (h₄.ends_mem he).1).1)
      (not_reaches_target_source' hA e)

/-- A walk avoiding a node, from a path avoiding it. -/
theorem of_reflTransGen_avoiding {b : V}
    (h : Relation.ReflTransGen (fun a c => G.Adj a c ∧ a ≠ b ∧ c ≠ b) u w) (hu : u ≠ b) :
    ∃ S P, IsDPath G u w S P ∧ b ∉ S := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨_, ∅, .nil _, fun h => hu (Set.mem_singleton_iff.mp h).symm⟩
  | @head a c hac _ ih =>
    obtain ⟨⟨e, hs, ht⟩, ha, hc⟩ := hac
    obtain ⟨S, P, hp, hbS⟩ := ih hc
    subst hs ht
    refine ⟨_, _, .cons e hp, fun h => ?_⟩
    rcases Set.mem_insert_iff.mp h with h | h
    · exact ha h.symm
    · exact hbS h

theorem of_reaches (h : G.Reaches u w) : ∃ S P, IsDPath G u w S P := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨_, _, .nil _⟩
  | @head a c hac _ ih =>
    obtain ⟨e, hs, ht⟩ := hac
    obtain ⟨S, P, hp⟩ := ih
    subst hs ht
    exact ⟨_, _, .cons e hp⟩

/-- A walk avoiding a node is a path avoiding it. -/
theorem reflTransGen_avoiding {b : V} (h : IsDPath G u w S P) (hb : b ∉ S) :
    Relation.ReflTransGen (fun a c => G.Adj a c ∧ a ≠ b ∧ c ≠ b) u w := by
  induction h with
  | nil u => exact .refl
  | cons e h ih =>
    refine (ih fun h' => hb (Set.mem_insert_of_mem _ h')).head ⟨⟨e, rfl, rfl⟩, ?_, ?_⟩
    · exact fun h' => hb (h' ▸ Set.mem_insert _ _)
    · exact fun h' => hb (Set.mem_insert_of_mem _ (h' ▸ h.start_mem))

/-- **A directed path is a semidirected path** of a semidirected network on the same graph. -/
theorem isSDPath (hA : G.IsAcyclic) {G' : SemidirectedNetwork V E X} (hG : G'.graph = G)
    (h : IsDPath G u w S P) : IsSDPath G' u w P S := by
  subst hG
  induction h with
  | nil u =>
    refine ⟨0, fun _ => u, Fin.elim0, ⟨fun i => i.elim0, fun i j _ => Fin.ext (by omega)⟩,
      rfl, rfl, Set.range_eq_empty _, Set.range_const⟩
  | cons e h ih =>
    obtain ⟨k, v, f, hpath, h0, hlast, hP, hS⟩ := ih
    refine ⟨k + 1, (Fin.cons (G'.graph.source e) v : Fin (k + 2) → V), (Fin.cons e f : Fin (k + 1) → E),
      ⟨fun i => ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · refine Or.inl ⟨rfl, ?_⟩
        rw [Fin.cons_zero]
        rw [Fin.cons_succ, h0]
      · rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hpath.step i
    · refine Fin.cons_injective_iff.mpr ⟨fun hm => ?_, hpath.injective⟩
      rw [hS] at hm
      exact not_reaches_target_source' hA e (h.reaches_of_mem hm).1
    · rw [← Fin.succ_last, Fin.cons_succ, hlast]
    · rw [Fin.range_cons, hP]
    · rw [Fin.range_cons, hS]

end IsDPath

/-- A nonempty finite set of a partial order on which the order is total has a greatest element. -/
theorem exists_greatest_of_total [PartialOrder V] {T : Set V} (hT : T.Finite) (hne : T.Nonempty)
    (htot : ∀ s ∈ T, ∀ t ∈ T, s ≤ t ∨ t ≤ s) : ∃ g ∈ T, ∀ s ∈ T, s ≤ g := by
  obtain ⟨g, hg⟩ := hT.exists_maximal hne
  refine ⟨g, hg.1, fun s hs => ?_⟩
  rcases htot s hs g hg.1 with h | h
  · exact h
  · exact hg.2 hs h

/-- A nonempty finite set of a partial order on which the order is total has a least element. -/
theorem exists_least_of_total [PartialOrder V] {T : Set V} (hT : T.Finite) (hne : T.Nonempty)
    (htot : ∀ s ∈ T, ∀ t ∈ T, s ≤ t ∨ t ≤ s) : ∃ g ∈ T, ∀ s ∈ T, g ≤ s := by
  obtain ⟨g, hg⟩ := hT.exists_minimal hne
  refine ⟨g, hg.1, fun s hs => ?_⟩
  rcases htot s hs g hg.1 with h | h
  · exact hg.2 hs h
  · exact h

end DPath

end Banos2019
