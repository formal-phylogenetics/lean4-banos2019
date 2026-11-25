module

public import Banos2019.Network.Rooted
public import Banos2019.Network.Path
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cycles and level-1 networks (Baños 2019, Section 2.5 and Definition 12)

A cycle is a closed path of the undirected graph `U(N)`: the directions of the edges are ignored. The
definitions are on `Phylogenetics.DirectedMultigraph`, the graph of a rooted network and of a
semidirected network alike, so they apply to both.

* `Joins`: an edge joins two nodes, in either direction.
* `IsCycleOf` (Definition 11): a cycle `v₀ e₀ v₁ e₁ ⋯ e_{k-1} v₀` of size `k`, given by its nodes and
  edges in order, with distinct nodes and distinct edges. `IsCycle C`: `C` is the edge set of a
  cycle; its size is `C.ncard`.
* `IsLevelOne` (Definition 12): no two cycles share an edge.
* `exists_isCycle_of_walks`: a walk between the ends of an edge `e` avoiding `e` closes a cycle
  through `e`; `IsLevelOne.eq_of_walks_compl`: in a level-1 graph, two nodes of a cycle joined by a
  walk avoiding its edges are equal; `IsPathOf.not_subset_of_isCycle`: the edges of a cycle are not
  all on a path; `IsCycle.exists_ne_of_mem`: a node of a cycle is on two of its edges.
* `lemma3`: a cycle of a binary level-1 rooted network has exactly one hybrid node and contains its two
  hybrid edges, and two cycles with a common node are the same (Rosselló, Valiente 2009).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-- The edge `e` joins the nodes `u` and `w`, in one direction or the other. -/
def Joins (G : DirectedMultigraph V E) (e : E) (u w : V) : Prop :=
  (G.source e = u ∧ G.target e = w) ∨ (G.source e = w ∧ G.target e = u)

/-- **Definition 11** (`cycle`): a *cycle* of size `k`: a non-empty path `v₀ e₀ v₁ ⋯ v_{k-1} e_{k-1} v₀`
from a node to itself in the undirected graph, the edge `e i` joining `v i` and `v (i + 1)` (indices
mod `k`), with distinct nodes and distinct edges. -/
structure IsCycleOf (G : DirectedMultigraph V E) (k : ℕ) (v : Fin k → V) (e : Fin k → E) : Prop where
  pos : 0 < k
  joins : ∀ i : Fin k, Joins G (e i) (v i) (v (finRotate k i))
  injective_node : Function.Injective v
  injective_edge : Function.Injective e

/-- `C` is the set of edges of a cycle. A cycle traversed from another node or in the other direction
has the same edges, so cycles are identified with their edge sets; the *size* of the cycle is
`C.ncard`, and its nodes are `cycleNodes G C`. -/
def IsCycle (G : DirectedMultigraph V E) (C : Set E) : Prop :=
  ∃ (k : ℕ) (v : Fin k → V) (e : Fin k → E), IsCycleOf G k v e ∧ Set.range e = C

/-- The nodes of a set of edges: their ends. -/
def cycleNodes (G : DirectedMultigraph V E) (C : Set E) : Set V :=
  {u | ∃ e ∈ C, G.source e = u ∨ G.target e = u}

/-- **Definition 12** (`level1`): a network is *level-1* if no two cycles share an edge. -/
def IsLevelOne (G : DirectedMultigraph V E) : Prop :=
  ∀ C C', IsCycle G C → IsCycle G C' → (C ∩ C').Nonempty → C = C'

/-! ### Cycles of a directed multigraph -/

section CycleFacts

/-- The nodes of a cycle are the nodes of its edges. -/
theorem IsCycleOf.cycleNodes_eq {G : DirectedMultigraph V E} {k : ℕ} {v : Fin k → V}
    {e : Fin k → E}    (hC : IsCycleOf G k v e) : cycleNodes G (Set.range e) = Set.range v := by
  ext u
  constructor
  · rintro ⟨f, ⟨i, rfl⟩, hu⟩
    rcases hC.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hu with hu | hu
    · exact ⟨i, h₁.symm.trans hu⟩
    · exact ⟨_, h₂.symm.trans hu⟩
    · exact ⟨_, h₁.symm.trans hu⟩
    · exact ⟨i, h₂.symm.trans hu⟩
  · rintro ⟨i, rfl⟩
    rcases hC.joins i with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact ⟨e i, ⟨i, rfl⟩, Or.inl h₁⟩
    · exact ⟨e i, ⟨i, rfl⟩, Or.inr h₂⟩

/-- The ends of an edge of `C` are nodes of `C`. -/
theorem source_mem_cycleNodes {G : DirectedMultigraph V E} {C : Set E} {f : E} (hf : f ∈ C) :
    G.source f ∈ cycleNodes G C :=
  ⟨f, hf, Or.inl rfl⟩

theorem target_mem_cycleNodes {G : DirectedMultigraph V E} {C : Set E} {f : E} (hf : f ∈ C) :
    G.target f ∈ cycleNodes G C :=
  ⟨f, hf, Or.inr rfl⟩

/-- **A node of a cycle is on two distinct edges of it**, when the cycle is not a loop. -/
theorem IsCycle.exists_ne_of_mem {G : DirectedMultigraph V E} {C : Set E} (hC : IsCycle G C)
    (hloop : ∀ f ∈ C, G.source f ≠ G.target f) {u : V} (hu : u ∈ cycleNodes G C) :
    ∃ f₁ ∈ C, ∃ f₂ ∈ C, f₁ ≠ f₂ ∧ (G.source f₁ = u ∨ G.target f₁ = u) ∧
      (G.source f₂ = u ∨ G.target f₂ = u) := by
  obtain ⟨k, v, e, hC, rfl⟩ := hC
  rw [hC.cycleNodes_eq] at hu
  obtain ⟨i, rfl⟩ := hu
  have hj := hC.joins ((finRotate k).symm i)
  rw [Equiv.apply_symm_apply] at hj
  refine ⟨e i, ⟨i, rfl⟩, e ((finRotate k).symm i), ⟨_, rfl⟩, fun h => ?_, ?_, ?_⟩
  · have hi : (finRotate k).symm i = i := (hC.injective_edge h).symm
    have hfix : finRotate k i = i := by
      conv_lhs => rw [← hi]
      exact Equiv.apply_symm_apply _ _
    have := hloop (e i) ⟨i, rfl⟩
    have hj' := hC.joins i
    rw [hfix] at hj'
    rcases hj' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> exact this (h₁.trans h₂.symm)
  · rcases hC.joins i with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact Or.inl h₁
    · exact Or.inr h₂
  · rcases hj with ⟨-, h₂⟩ | ⟨h₁, -⟩
    · exact Or.inr h₂
    · exact Or.inl h₁

/-- **A walk avoiding an edge `e` between its ends closes a cycle through `e`**, whose other edges
are those of the walk. A shortest such walk is a path (`exists_isPathOf_of_walks`), and `e` closes
it. -/
theorem exists_isCycle_of_walks {G : DirectedMultigraph V E} {e : E} {F : Set E} (he : e ∉ F)
    (h : G.Walks F (G.target e) (G.source e)) : ∃ C, IsCycle G C ∧ e ∈ C ∧ C ⊆ insert e F := by
  obtain ⟨n, p, q, hP, hp0, hpn⟩ := exists_isPathOf_of_walks h
  refine ⟨Set.range (Fin.snoc (α := fun _ => E) q e),
    ⟨n + 1, p, Fin.snoc (α := fun _ => E) q e, ⟨Nat.succ_pos n, fun i => ?_, hP.injective,
      Fin.snoc_injective_of_injective hP.injective_edge ?_⟩, rfl⟩,
    ⟨Fin.last n, Fin.snoc_last (α := fun _ => E) ..⟩, ?_⟩
  · induction i using Fin.lastCases with
    | cast j =>
      have hr : finRotate (n + 1) j.castSucc = j.succ := by
        ext
        rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last j).ne]
        simp
      rw [Fin.snoc_castSucc, hr]
      exact hP.link j
    | last =>
      rw [Fin.snoc_last, finRotate_last]
      exact Or.inl ⟨hpn.symm, hp0.symm⟩
  · rintro ⟨i, hi⟩
    exact he (hi ▸ hP.mem i)
  · rintro _ ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | cast j =>
      rw [Fin.snoc_castSucc]
      exact Or.inr (hP.mem j)
    | last =>
      rw [Fin.snoc_last]
      exact Or.inl rfl

/-- A cycle with its last edge removed is a path, through the nodes in order. -/
theorem IsCycleOf.isPathOf {G : DirectedMultigraph V E} {n : ℕ} {v : Fin (n + 1) → V}
    {e : Fin (n + 1) → E} (hC : IsCycleOf G (n + 1) v e) :
    IsPathOf G (Set.range e) n v fun l => e l.castSucc where
  mem l := ⟨_, rfl⟩
  link l := by
    have hr : finRotate (n + 1) l.castSucc = l.succ := by
      ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last l).ne]
      simp
    have := hC.joins l.castSucc
    rwa [hr] at this
  injective := hC.injective_node

/-- **In a level-1 graph, two nodes of a cycle `C` joined by a walk avoiding the edges of `C` are
equal.** Otherwise the walk and an arc of `C` would close a cycle through an edge of `C` that misses
another edge of `C`. -/
theorem IsLevelOne.eq_of_walks_compl {G : DirectedMultigraph V E} (h1 : IsLevelOne G) {C : Set E}
    (hC : IsCycle G C) {u w : V} (hu : u ∈ cycleNodes G C) (hw : w ∈ cycleNodes G C)
    (huw : G.Walks Cᶜ u w) : u = w := by
  obtain ⟨k, v, e, hC', rfl⟩ := hC
  rw [hC'.cycleNodes_eq] at hu hw
  obtain ⟨i, rfl⟩ := hu
  obtain ⟨j, rfl⟩ := hw
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hC'.pos; omega⟩
  -- for `i < j`, the arc `v i, …, v j` of the cycle and the walk close a cycle through `e i`
  have key : ∀ i j : Fin (n + 1), i < j → G.Walks (Set.range e)ᶜ (v i) (v j) → False := by
    intro i j hij hW
    have hP := hC'.isPathOf
    have hin : (i : ℕ) < n := by have := j.isLt; omega
    let l₀ : Fin n := ⟨i, hin⟩
    have hl₀ : l₀.castSucc = i := Fin.ext rfl
    let F : Set E := (Set.range e)ᶜ ∪
      {f | ∃ l : Fin n, (l₀.succ : ℕ) ≤ l ∧ (l : ℕ) < j ∧ e l.castSucc = f}
    have hle : l₀.succ ≤ j := by
      rw [Fin.le_def]
      simp only [Fin.val_succ, l₀]
      omega
    have hW₁ : G.Walks F (v l₀.succ) (v j) :=
      walks_mono Set.subset_union_right (hP.walks_of_le hle)
    have hW₂ : G.Walks F (v j) (v l₀.castSucc) :=
      walks_mono Set.subset_union_left (hl₀ ▸ G.walks_symm hW)
    have hei : e i ∉ F := by
      rintro (h | ⟨l, h₁, -, h₃⟩)
      · exact h ⟨i, rfl⟩
      · have := congrArg Fin.val (hC'.injective_edge h₃)
        simp only [Fin.val_succ, Fin.val_castSucc, l₀] at h₁ this
        omega
    have hwalk : G.Walks F (G.target (e i)) (G.source (e i)) := by
      rcases hP.link l₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [← hl₀, h₁, h₂]
        exact hW₁.trans hW₂
      · rw [← hl₀, h₁, h₂]
        exact G.walks_symm (hW₁.trans hW₂)
    obtain ⟨C'', hC'', heC, hsub⟩ := exists_isCycle_of_walks hei hwalk
    have hEq := h1 C'' _ hC'' ⟨_, v, e, hC', rfl⟩ ⟨e i, heC, i, rfl⟩
    have hej : e j ∈ C'' := hEq ▸ ⟨j, rfl⟩
    rcases hsub hej with h | h | ⟨l, -, h₂, h₃⟩
    · exact hij.ne (hC'.injective_edge h).symm
    · exact h ⟨j, rfl⟩
    · have := congrArg Fin.val (hC'.injective_edge h₃)
      simp only [Fin.val_castSucc] at this
      omega
  by_contra hne
  rcases lt_or_gt_of_ne (fun h : i = j => hne (h ▸ rfl)) with h | h
  · exact key i j h huw
  · exact key j i h (G.walks_symm huw)

/-- **The edges of a cycle are not all on a path.** The first node of the path on the cycle is on
two edges of the cycle, but only on one edge of the path that goes to a node of the cycle. -/
theorem IsPathOf.not_subset_of_isCycle {G : DirectedMultigraph V E} {F : Set E} {n : ℕ}
    {p : Fin (n + 1) → V} {q : Fin n → E} (hP : IsPathOf G F n p q) {C : Set E} (hC : IsCycle G C)
    (hsub : C ⊆ Set.range q) : False := by
  classical
  have hends : ∀ l : Fin n, q l ∈ C → p l.castSucc ∈ cycleNodes G C ∧ p l.succ ∈ cycleNodes G C :=
    fun l hl => by
      rcases hP.link l with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨h₁ ▸ source_mem_cycleNodes hl, h₂ ▸ target_mem_cycleNodes hl⟩
      · exact ⟨h₂ ▸ target_mem_cycleNodes hl, h₁ ▸ source_mem_cycleNodes hl⟩
  have hloop : ∀ f ∈ C, G.source f ≠ G.target f := fun f hf h => by
    obtain ⟨l, rfl⟩ := hsub hf
    rcases hP.link l with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] at h
    · exact Fin.castSucc_lt_succ.ne (hP.injective h)
    · exact Fin.castSucc_lt_succ.ne (hP.injective h).symm
  obtain ⟨k, v, e, hC', rfl⟩ := hC
  -- the first node of the path on the cycle
  have hex : ∃ m, ∃ h : m < n + 1, p ⟨m, h⟩ ∈ cycleNodes G (Set.range e) := by
    obtain ⟨l, hl⟩ := hsub ⟨⟨0, hC'.pos⟩, rfl⟩
    exact ⟨l, l.isLt.trans (Nat.lt_succ_self n), (hends l (hl ▸ ⟨_, rfl⟩)).1⟩
  obtain ⟨hm, hmC⟩ := Nat.find_spec hex
  have hmin : ∀ (m : ℕ) (h : m < n + 1), p ⟨m, h⟩ ∈ cycleNodes G (Set.range e) → Nat.find hex ≤ m :=
    fun m h hm' => Nat.find_min' hex ⟨h, hm'⟩
  obtain ⟨f₁, hf₁, f₂, hf₂, hne, hu₁, hu₂⟩ := IsCycle.exists_ne_of_mem ⟨k, v, e, hC', rfl⟩ hloop hmC
  -- an edge of the cycle on that node is the edge of the path leaving it
  have hfirst : ∀ f ∈ Set.range e, (G.source f = p ⟨Nat.find hex, hm⟩ ∨
      G.target f = p ⟨Nat.find hex, hm⟩) → ∃ l : Fin n, q l = f ∧ (l : ℕ) = Nat.find hex := by
    intro f hf hu
    obtain ⟨l, rfl⟩ := hsub hf
    refine ⟨l, rfl, ?_⟩
    rcases hP.eq_or_eq_of_end l hu with h | h
    · have h' := congrArg Fin.val (hP.injective h)
      simp only [Fin.val_castSucc] at h'
      omega
    · have h' := congrArg Fin.val (hP.injective h)
      simp only [Fin.val_succ] at h'
      have := hmin l (l.isLt.trans (Nat.lt_succ_self n)) (hends l hf).1
      omega
  obtain ⟨l₁, rfl, hl₁⟩ := hfirst f₁ hf₁ hu₁
  obtain ⟨l₂, rfl, hl₂⟩ := hfirst f₂ hf₂ hu₂
  exact hne (congrArg q (Fin.ext (hl₁.trans hl₂.symm)))

end CycleFacts

/-! ### Directed paths and the edges of a cycle -/

section Hits

/-- A step along an arc that is not an edge of `C`. -/
def AdjOff (G : DirectedMultigraph V E) (C : Set E) (a b : V) : Prop :=
  ∃ f, f ∉ C ∧ G.source f = a ∧ G.target f = b

/-- A directed path whose arcs are not in `C` is a walk avoiding `C`. -/
theorem walks_of_adjOff {G : DirectedMultigraph V E} {C : Set E} {a b : V}
    (h : Relation.ReflTransGen (AdjOff G C) a b) :
    G.Walks Cᶜ a b :=
  Relation.ReflTransGen.mono (fun _ _ ⟨f, hf, hs, ht⟩ => ⟨f, hf, Or.inl ⟨hs, ht⟩⟩) _ _ h

theorem reaches_of_adjOff {G : DirectedMultigraph V E} {C : Set E} {a b : V}
    (h : Relation.ReflTransGen (AdjOff G C) a b) :
    G.Reaches a b :=
  Relation.ReflTransGen.mono (fun _ _ ⟨f, _, hs, ht⟩ => ⟨f, hs, ht⟩) _ _ h

/-- **The first node of `C` on a directed path**: a directed path from `s` either avoids the edges
of `C` or reaches a node of `C` before using any. -/
theorem first_hit {G : DirectedMultigraph V E} {C : Set E} {s z : V} (h : G.Reaches s z) :
    Relation.ReflTransGen (AdjOff G C) s z ∨
      ∃ c ∈ cycleNodes G C, Relation.ReflTransGen (AdjOff G C) s c := by
  induction h with
  | refl => exact Or.inl .refl
  | @tail y z _ hyz ih =>
    obtain ⟨f, hfs, hft⟩ := hyz
    rcases ih with h | h
    · by_cases hf : f ∈ C
      · exact Or.inr ⟨y, hfs ▸ source_mem_cycleNodes hf, h⟩
      · exact Or.inl (h.tail ⟨f, hf, hfs, hft⟩)
    · exact Or.inr h

/-- **The last node of `C` on a directed path**: a directed path to `z` either avoids the edges of
`C` or leaves a node of `C` for the last time and then avoids them. -/
theorem last_hit {G : DirectedMultigraph V E} {C : Set E} {s z : V} (h : G.Reaches s z) :
    Relation.ReflTransGen (AdjOff G C) s z ∨
      ∃ c ∈ cycleNodes G C, Relation.ReflTransGen (AdjOff G C) c z := by
  induction h with
  | refl => exact Or.inl .refl
  | @tail y z _ hyz ih =>
    obtain ⟨f, hfs, hft⟩ := hyz
    by_cases hf : f ∈ C
    · exact Or.inr ⟨z, hft ▸ target_mem_cycleNodes hf, .refl⟩
    · rcases ih with h | ⟨c, hc, h⟩
      · exact Or.inl (h.tail ⟨f, hf, hfs, hft⟩)
      · exact Or.inr ⟨c, hc, h.tail ⟨f, hf, hfs, hft⟩⟩

end Hits

/-- **Lemma 3** (`lem:assos`), for rooted networks: in a binary level-1 rooted network, a cycle `C`
contains exactly one hybrid node `v`, and both hybrid edges of `v` are edges of `C`; and two cycles
with a common node are the same, so `v` and its hybrid edges lie on exactly one cycle. The paper takes
the lemma from Rosselló and Valiente (2009) and gives no proof.

Proved here directly. Two nodes of `C` are not joined by a walk avoiding the edges of `C`
(`IsLevelOne.eq_of_walks_compl`), so the root reaches exactly one node `a` of `C` by a directed path
avoiding them; every arc entering another node of `C` is an edge of `C`, `a` is above every node
of `C`, and no edge of `C` enters `a`. A lowest node of `C` is entered by its two edges of `C`, so
it is a hybrid node; counting the edges of `C` by the node they enter (none enters `a`, at least one
enters every other node, two enter a hybrid node) leaves room for only one. A node on two cycles without a
common edge would be on four edges, and a node of a binary network is on at most three. -/
theorem lemma3 [Finite E] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {C : Set E} (hC : IsCycle N.graph C) :
    (∃! v, v ∈ cycleNodes N.graph C ∧ N.graph.indegree v = 2) ∧
      (∀ v ∈ cycleNodes N.graph C, N.graph.indegree v = 2 → ∀ h, N.graph.target h = v → h ∈ C) ∧
      ∀ C', IsCycle N.graph C' → (cycleNodes N.graph C ∩ cycleNodes N.graph C').Nonempty → C = C' := by
  classical
  have hloop : ∀ f, N.graph.source f ≠ N.graph.target f := fun f h =>
    hN.1.acyclic _ (.single ⟨f, rfl, h.symm⟩)
  have hcyc : ∀ {a b}, N.graph.Reaches a b → N.graph.Adj b a → False := fun h hab =>
    hN.1.acyclic _ (Relation.TransGen.tail' h hab)
  have htwo := fun {u} (hu : u ∈ cycleNodes N.graph C) =>
    hC.exists_ne_of_mem (fun f _ => hloop f) hu
  -- the entry node `a`: the only node of `C` that the root reaches avoiding the edges of `C`
  obtain ⟨k, v, e, hC', rfl⟩ := id hC
  have hv0 : v ⟨0, hC'.pos⟩ ∈ cycleNodes N.graph (Set.range e) := by
    rw [hC'.cycleNodes_eq]; exact ⟨_, rfl⟩
  obtain ⟨a, haT, ha⟩ : ∃ a ∈ cycleNodes N.graph (Set.range e),
      Relation.ReflTransGen (AdjOff N.graph (Set.range e)) N.root a := by
    rcases first_hit (C := Set.range e) (hN.1.root_reaches (v ⟨0, hC'.pos⟩)) with h | h
    · exact ⟨_, hv0, h⟩
    · exact h
  have huniq : ∀ c ∈ cycleNodes N.graph (Set.range e),
      Relation.ReflTransGen (AdjOff N.graph (Set.range e)) N.root c → c = a :=
    fun c hc h => h1.eq_of_walks_compl hC hc haT
      ((N.graph.walks_symm (walks_of_adjOff h)).trans (walks_of_adjOff ha))
  -- every arc entering a node of `C` other than `a` is an edge of `C`
  have hE : ∀ c ∈ cycleNodes N.graph (Set.range e), c ≠ a →
      ∀ g, N.graph.target g = c → g ∈ Set.range e := by
    intro c hcT hca g hg
    by_contra hgC
    rcases last_hit (C := Set.range e) (hN.1.root_reaches (N.graph.source g)) with h | ⟨c₂, hc₂, h⟩
    · exact hca (huniq c hcT (h.tail ⟨g, hgC, rfl, hg⟩))
    · have hc₂c := h1.eq_of_walks_compl hC hc₂ hcT (walks_of_adjOff (h.tail ⟨g, hgC, rfl, hg⟩))
      subst hc₂c
      exact hcyc (reaches_of_adjOff h) ⟨g, rfl, hg⟩
  have hroot : N.root ∈ cycleNodes N.graph (Set.range e) → N.root = a := fun h => huniq _ h .refl
  -- `a` reaches every node of `C`
  have : Finite V := hN.1.finite_vertices
  let r : V → V → Prop := fun x y => Relation.TransGen N.graph.Adj x y
  have : IsTrans V r := ⟨fun _ _ _ h h' => h.trans h'⟩
  have : Std.Irrefl r := ⟨fun x h => hN.1.acyclic x h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  have hF : ∀ c ∈ cycleNodes N.graph (Set.range e), N.graph.Reaches a c := by
    intro c
    induction c using hwf.induction with
    | _ c ih =>
      intro hcT
      by_cases hca : c = a
      · rw [hca]
        exact .refl
      have hcr : c ≠ N.root := fun h => hca (h ▸ hroot (h ▸ hcT))
      obtain ⟨g, hg⟩ := (N.graph.one_le_indegree_iff c).mp (hN.1.nonroot_indegree c hcr)
      have hgC := hE c hcT hca g hg
      exact (ih _ (.single ⟨g, rfl, hg⟩) (source_mem_cycleNodes hgC)).tail ⟨g, rfl, hg⟩
  -- no edge of `C` enters `a`
  have hG : ∀ g ∈ Set.range e, N.graph.target g ≠ a := fun g hg h =>
    hcyc (hF _ (source_mem_cycleNodes hg)) ⟨g, rfl, h⟩
  -- so both edges of `C` at `a` leave it, and `a` is not a hybrid node
  have hA : N.graph.indegree a ≠ 2 := by
    intro h2
    obtain ⟨f₁, hf₁, f₂, hf₂, hne, hu₁, hu₂⟩ := htwo haT
    have hs₁ : N.graph.source f₁ = a := hu₁.resolve_right (hG f₁ hf₁)
    have hs₂ : N.graph.source f₂ = a := hu₂.resolve_right (hG f₂ hf₂)
    have : 2 ≤ N.graph.outdegree a := by
      rw [← Set.ncard_pair hne]
      exact Set.ncard_le_ncard (by rintro f (rfl | rfl) <;> assumption) (Set.toFinite _)
    have := hN.indegree_add_outdegree_le a
    omega
  -- the arcs entering a node of `C` of indegree two are edges of `C`
  have h2 : ∀ u ∈ cycleNodes N.graph (Set.range e), N.graph.indegree u = 2 →
      ∀ h, N.graph.target h = u → h ∈ Set.range e := fun u hu hu2 =>
    hE u hu fun h => hA (h ▸ hu2)
  refine ⟨?_, h2, fun C' hC'' hmeet => ?_⟩
  · -- a lowest node of `C` has its two edges of `C` entering it
    let r' : V → V → Prop := fun x y => Relation.TransGen N.graph.Adj y x
    have : IsTrans V r' := ⟨fun _ _ _ h h' => h'.trans h⟩
    have : Std.Irrefl r' := ⟨fun x h => hN.1.acyclic x h⟩
    obtain ⟨s, hsT, hmax⟩ := WellFounded.has_min (Finite.wellFounded_of_trans_of_irrefl r') _
      ⟨a, haT⟩
    have hsink : 2 ≤ N.graph.indegree s := by
      obtain ⟨f₁, hf₁, f₂, hf₂, hne, hu₁, hu₂⟩ := htwo hsT
      have hin : ∀ f ∈ Set.range e, (N.graph.source f = s ∨ N.graph.target f = s) →
          N.graph.target f = s := fun f hf hu => hu.resolve_left fun h =>
        hmax _ (target_mem_cycleNodes hf) (.single ⟨f, h, rfl⟩)
      rw [← Set.ncard_pair hne]
      exact Set.ncard_le_ncard
        (by rintro f (rfl | rfl) <;> [exact hin _ hf₁ hu₁; exact hin _ hf₂ hu₂])
        (Set.toFinite _)
    refine ⟨s, ⟨hsT, le_antisymm (hN.indegree_le_two s) hsink⟩, ?_⟩
    rintro s' ⟨hs'T, hs'2⟩
    -- two such nodes: count the edges of `C` by the node they enter
    by_contra hne
    have hs2 : N.graph.indegree s = 2 := le_antisymm (hN.indegree_le_two s) hsink
    have hsa : s ≠ a := fun h => hA (h ▸ hs2)
    have hs'a : s' ≠ a := fun h => hA (h ▸ hs'2)
    let S : Finset E := Finset.univ.image e
    let T : Finset V := Finset.univ.image v
    have hScard : S.card = k := by
      simp [S, Finset.card_image_of_injective _ hC'.injective_edge]
    have hTcard : T.card = k := by
      simp [T, Finset.card_image_of_injective _ hC'.injective_node]
    have hmemT : ∀ u, u ∈ T ↔ u ∈ cycleNodes N.graph (Set.range e) := by
      intro u
      rw [hC'.cycleNodes_eq]
      simp [T]
    have hmemS : ∀ f, f ∈ S ↔ f ∈ Set.range e := by simp [S]
    have hmaps : (S : Set E).MapsTo N.graph.target T := fun f hf =>
      (hmemT _).mpr (target_mem_cycleNodes ((hmemS f).mp hf))
    have hsum := Finset.card_eq_sum_card_fiberwise hmaps
    -- each node of `C` other than `a` is entered by an edge of `C`, a hybrid one by two
    have hlow : ∀ u ∈ T, u ≠ a → 1 ≤ (S.filter fun f => N.graph.target f = u).card := by
      intro u hu hua
      have huT := (hmemT u).mp hu
      have hur : u ≠ N.root := fun h => hua (h ▸ hroot (h ▸ huT))
      obtain ⟨g, hg⟩ := (N.graph.one_le_indegree_iff u).mp (hN.1.nonroot_indegree u hur)
      exact Finset.card_pos.mpr ⟨g, Finset.mem_filter.mpr ⟨(hmemS g).mpr (hE u huT hua g hg), hg⟩⟩
    have hlow2 : ∀ u ∈ T, N.graph.indegree u = 2 →
        2 ≤ (S.filter fun f => N.graph.target f = u).card := by
      intro u hu hu2
      obtain ⟨h₁, h₂, hne, hs⟩ := Set.ncard_eq_two.mp hu2
      have hmem : ∀ h ∈ ({h₁, h₂} : Set E), N.graph.target h = u := fun h hh => by
        rw [← hs] at hh
        exact hh
      rw [← Finset.card_pair hne]
      refine Finset.card_le_card fun h hh => ?_
      have hh' : h ∈ ({h₁, h₂} : Set E) := by simpa using hh
      exact Finset.mem_filter.mpr ⟨(hmemS h).mpr (h2 u ((hmemT u).mp hu) hu2 h (hmem h hh')),
        hmem h hh'⟩
    have haT' : a ∈ T := (hmemT a).mpr haT
    have hsT' : s ∈ T.erase a := Finset.mem_erase.mpr ⟨hsa, (hmemT s).mpr hsT⟩
    have hs'T' : s' ∈ (T.erase a).erase s :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_erase.mpr ⟨hs'a, (hmemT s').mpr hs'T⟩⟩
    rw [← Finset.add_sum_erase T _ haT', ← Finset.add_sum_erase _ _ hsT',
      ← Finset.add_sum_erase _ _ hs'T'] at hsum
    have hrest := Finset.card_nsmul_le_sum (((T.erase a).erase s).erase s')
      (fun u => (S.filter fun f => N.graph.target f = u).card) 1 fun u hu => by
        simp only [Finset.mem_erase] at hu
        exact hlow u hu.2.2.2 hu.2.2.1
    rw [smul_eq_mul, mul_one, Finset.card_erase_of_mem hs'T', Finset.card_erase_of_mem hsT',
      Finset.card_erase_of_mem haT', hTcard] at hrest
    have := hlow2 s ((hmemT s).mpr hsT) hs2
    have := hlow2 s' ((hmemT s').mpr hs'T) hs'2
    have : 3 ≤ k := by
      rw [← hTcard]
      have := Finset.card_le_card (Finset.erase_subset s' ((T.erase a).erase s))
      have := Finset.card_pos.mpr ⟨s', hs'T'⟩
      rw [Finset.card_erase_of_mem hsT', Finset.card_erase_of_mem haT'] at *
      omega
    omega
  · -- a node on two cycles with no common edge would be on four edges
    obtain ⟨u, huC, huC'⟩ := hmeet
    by_cases hshare : (Set.range e ∩ C').Nonempty
    · exact h1 _ _ hC hC'' hshare
    exfalso
    obtain ⟨f₁, hf₁, f₂, hf₂, hne₁₂, hu₁, hu₂⟩ := htwo huC
    obtain ⟨f₃, hf₃, f₄, hf₄, hne₃₄, hu₃, hu₄⟩ := hC''.exists_ne_of_mem (fun f _ => hloop f) huC'
    have hdisj : ∀ f ∈ Set.range e, ∀ f' ∈ C', f ≠ f' := fun f hf f' hf' h =>
      hshare ⟨f, hf, h ▸ hf'⟩
    have hsub : ({f₁, f₂, f₃, f₄} : Set E) ⊆
        {f | N.graph.target f = u} ∪ {f | N.graph.source f = u} := by
      rintro f (rfl | rfl | rfl | rfl)
      · exact hu₁.symm
      · exact hu₂.symm
      · exact hu₃.symm
      · exact hu₄.symm
    have h4 : ({f₁, f₂, f₃, f₄} : Set E).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hne₃₄]
      · rintro (h | h)
        · exact hdisj _ hf₂ _ hf₃ h
        · exact hdisj _ hf₂ _ hf₄ h
      · rintro (h | h | h)
        · exact hne₁₂ h
        · exact hdisj _ hf₁ _ hf₃ h
        · exact hdisj _ hf₁ _ hf₄ h
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have := Set.ncard_union_le {f | N.graph.target f = u} {f | N.graph.source f = u}
    have := hN.indegree_add_outdegree_le u
    unfold DirectedMultigraph.indegree DirectedMultigraph.outdegree at *
    omega

end Banos2019
