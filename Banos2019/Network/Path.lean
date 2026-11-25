module

public import Phylogenetics.Graph.Connectivity
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Paths in the undirected graph of a directed multigraph

Walks of `Phylogenetics.DirectedMultigraph` (`Walks F`) ignore the directions of the edges and use
edges of `F`. A walk contains a path with the same ends: a walk through distinct nodes, given by its
nodes and edges in order.

* `IsPathOf G F n p q`: a path `p 0, q 0, p 1, …, q (n - 1), p n` through distinct nodes, with its
  edges in `F`.
* `exists_isPathOf_of_walks`: a walk contains a path with the same ends.
* `IsPathOf.snoc`: a path extended by a new node.
* `IsPathOf.walks_of_le`: the part of a path between two of its nodes is a walk on its edges there.
* `IsPathOf.injective_edge`: the edges of a path are distinct.
-/

@[expose] public noncomputable section

open Phylogenetics

namespace Banos2019

variable {V E : Type*}

/-- A *path* `p 0, q 0, p 1, …, q (n - 1), p n` of the undirected graph of `G` with edges in `F`:
the edge `q i` joins `p i` and `p (i + 1)`, in either direction, and the nodes are distinct. -/
structure IsPathOf (G : DirectedMultigraph V E) (F : Set E) (n : ℕ) (p : Fin (n + 1) → V)
    (q : Fin n → E) : Prop where
  mem : ∀ i, q i ∈ F
  link : ∀ i : Fin n, (G.source (q i) = p i.castSucc ∧ G.target (q i) = p i.succ) ∨
    (G.source (q i) = p i.succ ∧ G.target (q i) = p i.castSucc)
  injective : Function.Injective p

/-- **A walk contains a path with the same ends.** Along the walk, a node already on the path cuts
the path back to it, and a new node extends it. -/
theorem exists_isPathOf_of_walks {G : DirectedMultigraph V E} {F : Set E} {u w : V}
    (h : G.Walks F u w) : ∃ n p q, IsPathOf G F n p q ∧ p 0 = u ∧ p (Fin.last n) = w := by
  induction h with
  | refl =>
    exact ⟨0, fun _ => u, Fin.elim0,
      ⟨fun i => i.elim0, fun i => i.elim0,
        fun i j _ => Fin.ext (by have := i.isLt; have := j.isLt; omega)⟩, rfl, rfl⟩
  | @tail y z _ hyz ih =>
    obtain ⟨n, p, q, hP, hp0, hpn⟩ := ih
    obtain ⟨f, hf, hlink⟩ := hyz
    by_cases hz : ∃ i, p i = z
    · -- cut the path back to `z`
      obtain ⟨i, hi⟩ := hz
      have h₁ : (i : ℕ) + 1 ≤ n + 1 := i.isLt
      have h₂ : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
      refine ⟨i, fun j => p (Fin.castLE h₁ j), fun j => q (Fin.castLE h₂ j),
        ⟨fun j => hP.mem _, fun j => ?_, hP.injective.comp (Fin.castLE_injective h₁)⟩, ?_, ?_⟩
      · have hc : (Fin.castLE h₁ j.castSucc : Fin (n + 1)) = (Fin.castLE h₂ j).castSucc :=
          Fin.ext rfl
        have hs : (Fin.castLE h₁ j.succ : Fin (n + 1)) = (Fin.castLE h₂ j).succ := Fin.ext rfl
        simp only [hc, hs]
        exact hP.link _
      · rw [← hp0]
        exact congrArg p (Fin.ext rfl)
      · rw [← hi]
        exact congrArg p (Fin.ext rfl)
    · -- extend the path by `z`
      push Not at hz
      refine ⟨n + 1, Fin.snoc (α := fun _ => V) p z, Fin.snoc (α := fun _ => E) q f,
        ⟨fun i => ?_, fun i => ?_, Fin.snoc_injective_of_injective hP.injective ?_⟩, ?_, ?_⟩
      · induction i using Fin.lastCases with
        | cast j => rw [Fin.snoc_castSucc]; exact hP.mem j
        | last => rw [Fin.snoc_last]; exact hf
      · induction i using Fin.lastCases with
        | cast j =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
          exact hP.link j
        | last =>
          rw [Fin.snoc_last, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hpn]
          exact hlink
      · rintro ⟨i, hi⟩
        exact hz i hi
      · rw [← hp0]
        exact Fin.snoc_castSucc (α := fun _ => V) (i := 0) ..
      · exact Fin.snoc_last (α := fun _ => V) ..

/-- Walks on fewer edges are walks on more. -/
theorem walks_mono {G : DirectedMultigraph V E} {F F' : Set E} (hF : F ⊆ F') {u w : V}
    (h : G.Walks F u w) : G.Walks F' u w :=
  Relation.ReflTransGen.mono (fun _ _ ⟨f, hf, hl⟩ => ⟨f, hF hf, hl⟩) _ _ h

variable {G : DirectedMultigraph V E} {F : Set E} {n : ℕ} {p : Fin (n + 1) → V} {q : Fin n → E}

/-- **A path extended by a new node** `z` and an edge from its last node to `z` is a path. -/
theorem IsPathOf.snoc (hP : IsPathOf G F n p q) {z : V} (hz : z ∉ Set.range p) {f : E} (hf : f ∈ F)
    (hj : (G.source f = p (Fin.last n) ∧ G.target f = z) ∨
      (G.source f = z ∧ G.target f = p (Fin.last n))) :
    IsPathOf G F (n + 1) (Fin.snoc (α := fun _ => V) p z) (Fin.snoc (α := fun _ => E) q f) where
  mem i := by
    induction i using Fin.lastCases with
    | cast j => rw [Fin.snoc_castSucc]; exact hP.mem j
    | last => rw [Fin.snoc_last]; exact hf
  link i := by
    induction i using Fin.lastCases with
    | cast j =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
      exact hP.link j
    | last =>
      rw [Fin.snoc_last, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
      exact hj
  injective := Fin.snoc_injective_of_injective hP.injective fun ⟨i, hi⟩ => hz ⟨i, hi⟩

/-- The edge `q i` of a path joins `p i` and `p (i + 1)` as an edge of the walks. -/
theorem IsPathOf.adjOn (hP : IsPathOf G F n p q) (i : Fin n) {F' : Set E} (hi : q i ∈ F') :
    G.AdjOn F' (p i.castSucc) (p i.succ) :=
  ⟨q i, hi, hP.link i⟩

/-- **The part of a path between two of its nodes** is a walk on the edges of the path there. -/
theorem IsPathOf.walks_of_le (hP : IsPathOf G F n p q) {i j : Fin (n + 1)} (hij : i ≤ j) :
    G.Walks {f | ∃ l : Fin n, (i : ℕ) ≤ l ∧ (l : ℕ) < j ∧ q l = f} (p i) (p j) := by
  suffices ∀ d : ℕ, ∀ j : Fin (n + 1), (j : ℕ) = i + d →
      G.Walks {f | ∃ l : Fin n, (i : ℕ) ≤ l ∧ (l : ℕ) < j ∧ q l = f} (p i) (p j) from
    this _ j (Nat.add_sub_cancel' hij).symm
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [show j = i from Fin.ext (by simpa using hj)]
    exact .refl
  | succ d ih =>
    intro j hj
    have hjn : (j : ℕ) - 1 < n := by have := j.isLt; omega
    obtain ⟨l, hl⟩ : ∃ l : Fin n, (l : ℕ) = j - 1 := ⟨⟨j - 1, hjn⟩, rfl⟩
    have hl₁ : l.castSucc = ⟨i + d, by have := j.isLt; omega⟩ := Fin.ext (by simp; omega)
    have hl₂ : l.succ = j := Fin.ext (by simp; omega)
    have hw := ih ⟨i + d, by have := j.isLt; omega⟩ rfl
    refine Relation.ReflTransGen.tail (walks_mono (fun f hf => ?_) hw) ?_
    · obtain ⟨l', h₁, h₂, h₃⟩ := hf
      exact ⟨l', h₁, by simp only at h₂; omega, h₃⟩
    · have hadj := hP.adjOn l (F' := {f | ∃ l' : Fin n, (i : ℕ) ≤ l' ∧ (l' : ℕ) < j ∧ q l' = f})
        ⟨l, by omega, by omega, rfl⟩
      rw [hl₁, hl₂] at hadj
      exact hadj

/-- A path is a walk on its edges. -/
theorem IsPathOf.walks (hP : IsPathOf G F n p q) : G.Walks F (p 0) (p (Fin.last n)) :=
  walks_mono (fun _ h => by obtain ⟨l, -, -, hl⟩ := h; exact hl ▸ hP.mem l)
    (hP.walks_of_le (Fin.zero_le _))

/-- The two ends of the edge `q i` of a path are `p i` and `p (i + 1)`: a node at an end of `q i` is
one of them. -/
theorem IsPathOf.eq_or_eq_of_end (hP : IsPathOf G F n p q) (i : Fin n) {u : V}
    (hu : G.source (q i) = u ∨ G.target (q i) = u) : u = p i.castSucc ∨ u = p i.succ := by
  rcases hP.link i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hu with rfl | rfl <;> simp_all

/-- **The edges of a path are distinct**: the ends of `q i` are `p i` and `p (i + 1)`, and the
nodes are distinct. -/
theorem IsPathOf.injective_edge (hP : IsPathOf G F n p q) : Function.Injective q := by
  intro i j hij
  have h₁ := hP.eq_or_eq_of_end j (u := p i.castSucc) (by
    rcases hP.link i with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl (hij ▸ h)
    · exact Or.inr (hij ▸ h))
  have h₂ := hP.eq_or_eq_of_end j (u := p i.succ) (by
    rcases hP.link i with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr (hij ▸ h)
    · exact Or.inl (hij ▸ h))
  rcases h₁ with h₁ | h₁ <;> have h₁ := congrArg Fin.val (hP.injective h₁) <;>
    rcases h₂ with h₂ | h₂ <;> have h₂ := congrArg Fin.val (hP.injective h₂) <;>
    simp at h₁ h₂ <;> exact Fin.ext (by omega)

end Banos2019
