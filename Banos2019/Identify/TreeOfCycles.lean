module

public import Banos2019.Identify.Glue

/-!
# The tree of cycles (Baños 2019, Definition 13, proof of Theorem 4)

The induction step of Theorem 4 takes `T`, the tree of cycles of `Ñ` (Definition 13,
`treeOfCycles`), and a leaf of it, which arises from a cycle `C_v` of `N⁻` all of whose `v`-blocks
but one are 4-network blocks. The paper proves neither that `T` is a tree nor this description of
its leaves; the results below prove both, for `T` the tree of cycles of
`tildeNetwork (unrooted N hN hX)`.

* `isConnected_treeOfCycles_unrooted`, `not_isCycle_treeOfCycles_unrooted`: `T` is connected and
  has no cycle.
* `ArisesFrom w C`: the node `w` of `T` is the class of the nodes of `Ñ` coming from the cycle `C`
  of `N⁻`. `exists_arisesFrom_of_isLeafNode_unrooted`: every leaf of `T` (`IsLeafNode`, a node with
  at most one edge) arises from a cycle of `N⁻` of size at least four; a node of `T` arises from each
  such cycle (`exists_arisesFrom_unrooted`).
* `IsFourNetworkBlock`: a `v`-block whose taxa are in one 4-network block.
  `isLeafNode_iff_fourNetworkBlocks_unrooted`: a node of `T` arising from a cycle `C_v` of size at
  least four is a leaf exactly when all the `v`-blocks but one are 4-network blocks. The proof of
  Theorem 4 uses both directions: a leaf of the tree of cycles of `Ñ₁` gives such a cycle of `N₁⁻`
  (`fourNetworkBlocks_of_isLeafNode_unrooted`), and the cycle of `N₂⁻` with the same blocks gives a
  leaf of the tree of cycles of `Ñ₂`.
* `exists_isLeafNode_treeOfCycles_unrooted`: when `N⁻` has a cycle of size at least four, `T` has
  a leaf.

The first part concerns any semidirected network `H` without loops and `T = treeOfCycles H`: `H`
restricted to its pendant core (`coreNet`), with the nodes of degree two on no cycle suppressed
(`coreSuppressed`), and every cycle contracted.

* The pendant core contains the edges of a path between two of its nodes
  (`mem_pendantCore_of_isPathOf`) and the edges with a node of a cycle on each side
  (`mem_pendantCore_of_sides`); an edge of the core on no cycle has a node of a cycle on each side
  (`exists_cycle_side_of_mem_pendantCore`).
* Walks pass through suppression both ways (`suppressExcept_walks_val`,
  `suppressExcept_walks_of_walks`); an edge of a chain on a cycle lies on a cycle of the network
  (`exists_isCycle_of_suppressExcept_walks`); a cycle whose nodes are kept is a cycle of the
  suppressed network (`isCycleOf_suppressExcept`).
* For `H` connected, `T` is a tree (`treeOfCycles_isTree`), and a node of the core on no cycle of
  `H` has two edges of `T` (`not_isLeafNode_mk_of_notMem`).

The second part concerns `Ñ`, for a network `G` with the properties of `N⁻` (`IsUnrootedLevelOne`).

* The cycles of `Ñ` come from the cycles of `G` of size at least four
  (`exists_isCycle_big_of_mem_cycleNodes_tilde`). Such a cycle gives a cycle of `Ñ` and one of the
  suppressed core through the nodes coming from its nodes (`exists_isCycle_tilde_of_big`), all in
  one class of `T` (`treeOfCycles_mk_eq_of_big`), which holds no other node
  (`exists_mem_of_mk_eq_of_big`).
* At a node `u` of such a cycle, the edge of `Ñ` through the edge `f` off the cycle is in the
  pendant core exactly when the block of `u` is not a 4-network block (`exists_tilde_offCycle`,
  `not_fourNetworkBlock_of_mem_pendantCore`), that is, when a cycle of size at least four lies on
  the far side of `f` (`exists_big_notMem_side`, `not_fourNetworkBlock_of_side`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace Banos2019

/-! ### Leaves, walks and the pendant core of a multigraph -/

section Graph

variable {V E : Type*}

/-- The node `w` is a *leaf*: at most one edge has `w` as an end. -/
def IsLeafNode (G : DirectedMultigraph V E) (w : V) : Prop :=
  {e | G.source e = w ∨ G.target e = w}.Subsingleton

variable {G : DirectedMultigraph V E}

/-- A walk on `F` is a walk on `F'` when every edge of `F` at a node that the walk can reach is in
`F'`. -/
theorem walks_mono_of_reach {F F' : Set E} {a b : V} (h : G.Walks F a b)
    (hF : ∀ y, G.Walks F a y → ∀ f ∈ F, (G.source f = y ∨ G.target f = y) → f ∈ F') :
    G.Walks F' a b := by
  induction h with
  | refl => exact .refl
  | @tail c d hac hcd ih =>
    obtain ⟨f, hf, hj⟩ := hcd
    refine ih.tail ⟨f, hF c hac f hf ?_, hj⟩
    rcases hj with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h

/-- An edge on a cycle has its ends joined without it. -/
theorem walks_compl_of_mem_isCycle {C : Set E} (hC : IsCycle G C) {e : E} (he : e ∈ C) :
    G.Walks {e}ᶜ (G.source e) (G.target e) :=
  walks_mono (fun f (hf : f ∈ C \ {e}) => hf.2)
    (hC.walks_sdiff_singleton he (source_mem_cycleNodes he) (target_mem_cycleNodes he))

/-- An edge whose ends are joined without it lies on a cycle. -/
theorem exists_isCycle_of_walks_compl {e : E} (h : G.Walks {e}ᶜ (G.source e) (G.target e)) :
    ∃ C, IsCycle G C ∧ e ∈ C := by
  obtain ⟨C, hC, heC, -⟩ := exists_isCycle_of_walks (F := {e}ᶜ) (fun h => h rfl) (G.walks_symm h)
  exact ⟨C, hC, heC⟩

/-- The number of ends at `u` of edges of `K`, as `pendantCore` counts them, grows with `K`. -/
theorem pendantCount_mono [Finite E] {K K' : Set E} (h : K ⊆ K') (u : V) :
    {f | f ∈ K ∧ G.source f = u}.ncard + {f | f ∈ K ∧ G.target f = u}.ncard ≤
      {f | f ∈ K' ∧ G.source f = u}.ncard + {f | f ∈ K' ∧ G.target f = u}.ncard :=
  add_le_add (Set.ncard_le_ncard (fun _ hf => ⟨h hf.1, hf.2⟩) (Set.toFinite _))
    (Set.ncard_le_ncard (fun _ hf => ⟨h hf.1, hf.2⟩) (Set.toFinite _))

/-- Two distinct edges of `K` at `u` give two ends at `u`. -/
theorem two_le_pendantCount [Finite E] {K : Set E} {f₁ f₂ : E} (hf₁ : f₁ ∈ K) (hf₂ : f₂ ∈ K)
    (hne : f₁ ≠ f₂) {u : V} (h₁ : G.source f₁ = u ∨ G.target f₁ = u)
    (h₂ : G.source f₂ = u ∨ G.target f₂ = u) :
    2 ≤ {f | f ∈ K ∧ G.source f = u}.ncard + {f | f ∈ K ∧ G.target f = u}.ncard := by
  have hpos : ∀ {f} (P : E → Prop), f ∈ K → P f → 0 < {f | f ∈ K ∧ P f}.ncard :=
    fun P hf hP => (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hf, hP⟩
  have hpair : ∀ P : E → Prop, P f₁ → P f₂ → 2 ≤ {f | f ∈ K ∧ P f}.ncard := fun P hP₁ hP₂ => by
    have := Set.ncard_le_ncard (show ({f₁, f₂} : Set E) ⊆ {f | f ∈ K ∧ P f} by
      rintro f (rfl | rfl)
      exacts [⟨hf₁, hP₁⟩, ⟨hf₂, hP₂⟩]) (Set.toFinite _)
    rwa [Set.ncard_pair hne] at this
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · have := hpair (fun f => G.source f = u) h₁ h₂; omega
  · have := hpos (fun f => G.source f = u) hf₁ h₁
    have := hpos (fun f => G.target f = u) hf₂ h₂
    omega
  · have := hpos (fun f => G.target f = u) hf₁ h₁
    have := hpos (fun f => G.source f = u) hf₂ h₂
    omega
  · have := hpair (fun f => G.target f = u) h₁ h₂; omega

/-- Two ends at `u` of edges of `K` come from two distinct edges, when no edge is a loop. -/
theorem exists_ne_of_two_le_pendantCount [Finite E] (hloop : ∀ e, G.source e ≠ G.target e)
    {K : Set E} {u : V}
    (h : 2 ≤ {f | f ∈ K ∧ G.source f = u}.ncard + {f | f ∈ K ∧ G.target f = u}.ncard) :
    ∃ f₁ ∈ K, ∃ f₂ ∈ K, f₁ ≠ f₂ ∧ (G.source f₁ = u ∨ G.target f₁ = u) ∧
      (G.source f₂ = u ∨ G.target f₂ = u) := by
  by_cases hA : 1 < {f | f ∈ K ∧ G.source f = u}.ncard
  · obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 hA
    exact ⟨a, ha.1, b, hb.1, hab, Or.inl ha.2, Or.inl hb.2⟩
  by_cases hB : 1 < {f | f ∈ K ∧ G.target f = u}.ncard
  · obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 hB
    exact ⟨a, ha.1, b, hb.1, hab, Or.inr ha.2, Or.inr hb.2⟩
  obtain ⟨a, ha⟩ := (Set.ncard_pos (Set.toFinite {f | f ∈ K ∧ G.source f = u})).1 (by omega)
  obtain ⟨b, hb⟩ := (Set.ncard_pos (Set.toFinite {f | f ∈ K ∧ G.target f = u})).1 (by omega)
  exact ⟨a, ha.1, b, hb.1, fun hab => hloop a (ha.2.trans (hab ▸ hb.2).symm), Or.inl ha.2,
    Or.inr hb.2⟩

/-- A set of edges in which every end of an edge has two edges of the set is in the pendant
core. -/
theorem subset_pendantCore {K : Set E}
    (hK : ∀ e ∈ K, ∀ u, (G.source e = u ∨ G.target e = u) →
      2 ≤ {f | f ∈ K ∧ G.source f = u}.ncard + {f | f ∈ K ∧ G.target f = u}.ncard) :
    K ⊆ pendantCore G :=
  Set.subset_sUnion_of_mem (show K ∈ {K | ∀ e ∈ K, ∀ u, (G.source e = u ∨ G.target e = u) →
    2 ≤ {f | f ∈ K ∧ G.source f = u}.ncard + {f | f ∈ K ∧ G.target f = u}.ncard} from hK)

/-- **Every end of an edge of the pendant core has two edges of the core.** -/
theorem two_le_pendantCount_pendantCore [Finite E] {e : E} (he : e ∈ pendantCore G) {u : V}
    (hu : G.source e = u ∨ G.target e = u) :
    2 ≤ {f | f ∈ pendantCore G ∧ G.source f = u}.ncard +
      {f | f ∈ pendantCore G ∧ G.target f = u}.ncard := by
  obtain ⟨K, hK, heK⟩ := he
  exact (hK e heK u hu).trans (pendantCount_mono (Set.subset_sUnion_of_mem hK) u)

/-- **A path between two nodes of edges of the pendant core lies in the core**: with it, every end
of an edge still has two edges, the ends of the path having two edges of the core. -/
theorem mem_pendantCore_of_isPathOf [Finite E] {n : ℕ} {p : Fin (n + 1) → V} {q : Fin n → E}
    (hP : IsPathOf G Set.univ n p q)
    (h0 : ∃ e ∈ pendantCore G, G.source e = p 0 ∨ G.target e = p 0)
    (hn : ∃ e ∈ pendantCore G, G.source e = p (Fin.last n) ∨ G.target e = p (Fin.last n))
    (i : Fin n) : q i ∈ pendantCore G := by
  refine subset_pendantCore (K := pendantCore G ∪ Set.range q) ?_ (Or.inr ⟨i, rfl⟩)
  have hcore : ∀ u, (∃ e ∈ pendantCore G, G.source e = u ∨ G.target e = u) →
      2 ≤ {f | f ∈ pendantCore G ∪ Set.range q ∧ G.source f = u}.ncard +
        {f | f ∈ pendantCore G ∪ Set.range q ∧ G.target f = u}.ncard := fun u ⟨e, he, hu⟩ =>
    (two_le_pendantCount_pendantCore he hu).trans (pendantCount_mono Set.subset_union_left u)
  have hinc₁ : ∀ j : Fin n, G.source (q j) = p j.castSucc ∨ G.target (q j) = p j.castSucc :=
    fun j => (hP.link j).elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
  have hinc₂ : ∀ j : Fin n, G.source (q j) = p j.succ ∨ G.target (q j) = p j.succ :=
    fun j => (hP.link j).elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)
  rintro e (he | ⟨j, rfl⟩) u hu
  · exact hcore u ⟨e, he, hu⟩
  · rcases hP.eq_or_eq_of_end j hu with rfl | rfl
    · by_cases hj0 : (j : ℕ) = 0
      · have : j.castSucc = 0 := Fin.ext hj0
        rw [this]
        exact hcore _ h0
      · set j' : Fin n := ⟨j - 1, by omega⟩
        have hj' : j'.succ = j.castSucc := Fin.ext (by simp [j']; omega)
        refine two_le_pendantCount (Or.inr ⟨j', rfl⟩) (Or.inr ⟨j, rfl⟩) (fun h => ?_)
          (hj' ▸ hinc₂ j') (hinc₁ j)
        have := congrArg Fin.val (hP.injective_edge h)
        simp [j'] at this
        omega
    · by_cases hjn : (j : ℕ) + 1 = n
      · have : j.succ = Fin.last n := Fin.ext (by simp; omega)
        rw [this]
        exact hcore _ hn
      · set j' : Fin n := ⟨j + 1, by omega⟩
        have hj' : j'.castSucc = j.succ := Fin.ext (by simp [j'])
        refine two_le_pendantCount (Or.inr ⟨j', rfl⟩) (Or.inr ⟨j, rfl⟩) (fun h => ?_)
          (hj' ▸ hinc₁ j') (hinc₂ j)
        have := congrArg Fin.val (hP.injective_edge h)
        simp [j'] at this

/-- **An edge between cycles is in the pendant core**: an edge on a cycle, or one each of whose ends
is joined to a node of a cycle without the edge. These edges form a set in which every end of an
edge has two edges of the set: at a node of a cycle, the two edges of the cycle; at a node on no
cycle, the first edge of a path toward a cycle on the side of the node also has a cycle on each
side. -/
theorem mem_pendantCore_of_sides [Finite E] (hloop : ∀ e, G.source e ≠ G.target e) {e : E}
    (he : (∃ C, IsCycle G C ∧ e ∈ C) ∨ ∀ a, (G.source e = a ∨ G.target e = a) →
      ∃ C z, IsCycle G C ∧ z ∈ cycleNodes G C ∧ G.Walks {e}ᶜ a z) :
    e ∈ pendantCore G := by
  set K : Set E := {e | (∃ C, IsCycle G C ∧ e ∈ C) ∨ ∀ a, (G.source e = a ∨ G.target e = a) →
      ∃ C z, IsCycle G C ∧ z ∈ cycleNodes G C ∧ G.Walks {e}ᶜ a z}
  refine subset_pendantCore (K := K) ?_ he
  intro e he u hu
  by_cases hcu : ∃ C, IsCycle G C ∧ u ∈ cycleNodes G C
  · obtain ⟨C, hC, huC⟩ := hcu
    obtain ⟨f₁, hf₁, f₂, hf₂, hne, h₁, h₂⟩ := hC.exists_ne_of_mem (fun f _ => hloop f) huC
    exact two_le_pendantCount (Or.inl ⟨C, hC, hf₁⟩) (Or.inl ⟨C, hC, hf₂⟩) hne h₁ h₂
  push Not at hcu
  have hecyc : ∀ C, IsCycle G C → e ∉ C := fun C hC heC => hcu C hC ⟨e, heC, hu⟩
  have he' : ∀ a, (G.source e = a ∨ G.target e = a) →
      ∃ C z, IsCycle G C ∧ z ∈ cycleNodes G C ∧ G.Walks {e}ᶜ a z :=
    he.resolve_left fun ⟨C, hC, heC⟩ => hecyc C hC heC
  obtain ⟨C, z, hC, hz, huz⟩ := he' u hu
  obtain ⟨n, p, q, hP, hp0, hpn⟩ := exists_isPathOf_of_walks huz
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (hp0.symm.trans hpn ▸ hz) (hcu C hC)
    · exact h
  set g := q ⟨0, hn⟩
  have h0 : (⟨0, hn⟩ : Fin n).castSucc = 0 := rfl
  have hgu : G.source g = u ∨ G.target g = u := by
    rcases hP.link ⟨0, hn⟩ with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact Or.inl (h₁.trans (by rw [h0, hp0]))
    · exact Or.inr (h₂.trans (by rw [h0, hp0]))
  have hge : g ≠ e := hP.mem ⟨0, hn⟩
  -- the other end `v` of `e`
  obtain ⟨v, hj⟩ := exists_joins_of_incident hu
  have hnv : ¬ G.Walks {e}ᶜ u v := not_walks_of_joins hecyc hj
  refine two_le_pendantCount (Or.inr fun a ha => ?_) he hge hgu hu
  rcases hP.eq_or_eq_of_end ⟨0, hn⟩ ha with rfl | rfl
  · -- the end `u`: through `e` to `v`, then to a cycle on the side of `v`
    obtain ⟨C', z', hC', hz', hvz⟩ := he' v (hj.incident_right)
    refine ⟨C', z', hC', hz', ?_⟩
    have hvz' : G.Walks {g}ᶜ v z' := by
      refine walks_mono_of_reach hvz fun y hy f hf hfy hfg => ?_
      rw [Set.mem_singleton_iff] at hfg
      subst hfg
      rcases hP.eq_or_eq_of_end ⟨0, hn⟩ hfy with rfl | rfl
      · rw [h0, hp0] at hy
        exact hnv (G.walks_symm hy)
      · refine hnv (G.walks_symm (hy.tail ⟨q ⟨0, hn⟩, hf, ?_⟩))
        rcases hP.link ⟨0, hn⟩ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inr ⟨h₁.trans (by rw [h0, hp0]), h₂⟩
        · exact Or.inl ⟨h₁, h₂.trans (by rw [h0, hp0])⟩
    rw [h0, hp0]
    exact (Relation.ReflTransGen.single
      ⟨e, fun h => hge (Set.mem_singleton_iff.1 h).symm, hj⟩).trans hvz'
  · -- the end `p 1`: along the path to `z`
    refine ⟨C, z, hC, hz, ?_⟩
    rw [← hpn]
    refine walks_mono (fun f hf => ?_) (hP.walks_of_le (Fin.le_last _))
    obtain ⟨l, hl, -, rfl⟩ := hf
    intro h
    have := congrArg Fin.val (hP.injective_edge (Set.mem_singleton_iff.1 h))
    simp at hl
    simp at this
    omega

/-- **An edge of the pendant core on no cycle has a node of a cycle on each side**: on the side of
`y`, a longest path of the core from `a` through the edge ends at a node whose second edge of the
core leads to a new node on that side, or closes a cycle there. -/
theorem exists_cycle_side_of_mem_pendantCore [Finite V] [Finite E]
    (hloop : ∀ e, G.source e ≠ G.target e) {c : E} (hc : c ∈ pendantCore G)
    (hcC : ∀ C, IsCycle G C → c ∉ C) {a y : V} (hj : Joins G c a y) :
    ∃ C z, IsCycle G C ∧ z ∈ cycleNodes G C ∧ G.Walks {c}ᶜ y z := by
  by_contra hno
  push Not at hno
  have hay : ¬ G.Walks {c}ᶜ y a := fun h => not_walks_of_joins hcC hj (G.walks_symm h)
  have hext : ∀ (n k : ℕ) (p : Fin (k + 1) → V) (q : Fin k → E), Nat.card V - k = n → 0 < k →
      IsPathOf G (pendantCore G) k p q → p 0 = a →
      (∀ i : Fin (k + 1), i ≠ 0 → G.Walks {c}ᶜ y (p i)) → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro k p q hn hk hP hp0 hside
    have hz : G.Walks {c}ᶜ y (p (Fin.last k)) :=
      hside _ (fun h => by have := congrArg Fin.val h; simp at this; omega)
    obtain ⟨j, hj'⟩ : ∃ j : Fin k, j.succ = Fin.last k :=
      ⟨⟨k - 1, by omega⟩, Fin.ext (by simp; omega)⟩
    have hqz : G.source (q j) = p (Fin.last k) ∨ G.target (q j) = p (Fin.last k) := by
      rcases hP.link j with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr (hj' ▸ h)
      · exact Or.inl (hj' ▸ h)
    obtain ⟨f₁, hf₁, f₂, hf₂, hne, h₁, h₂⟩ :=
      exists_ne_of_two_le_pendantCount hloop (two_le_pendantCount_pendantCore (hP.mem j) hqz)
    obtain ⟨g, hg, hgq, hgz⟩ : ∃ g ∈ pendantCore G, g ≠ q j ∧
        (G.source g = p (Fin.last k) ∨ G.target g = p (Fin.last k)) := by
      by_cases h : f₁ = q j
      · exact ⟨f₂, hf₂, fun h' => hne (h.trans h'.symm), h₂⟩
      · exact ⟨f₁, hf₁, h, h₁⟩
    obtain ⟨z', hjz⟩ := exists_joins_of_incident hgz
    have hgP : g ∉ Set.range q := by
      rintro ⟨l, rfl⟩
      rcases hP.eq_or_eq_of_end l hgz with h | h
      · have := congrArg Fin.val (hP.injective h)
        simp at this
        omega
      · exact hgq (congrArg q (Fin.succ_injective _ ((hP.injective h).symm.trans hj'.symm)))
    by_cases hz' : z' ∈ Set.range p
    · -- `g` closes a cycle through the last node
      obtain ⟨i, hi⟩ := hz'
      have hw : G.Walks {g}ᶜ (p i) (p (Fin.last k)) := by
        refine walks_mono (fun f hf => ?_) (hP.walks_of_le (Fin.le_last i))
        obtain ⟨l, -, -, rfl⟩ := hf
        exact fun h => hgP ⟨l, Set.mem_singleton_iff.1 h⟩
      obtain ⟨C, hC, hgC⟩ := exists_isCycle_of_walks_compl (G := G) (e := g) (by
        rcases hjz with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · rw [h₁, h₂, ← hi]
          exact G.walks_symm hw
        · rw [h₁, h₂, ← hi]
          exact hw)
      exact hno C _ hC ⟨g, hgC, hgz⟩ hz
    · -- `g` leads to a new node on the side of `y`
      have hgc : g ≠ c := by
        rintro rfl
        rcases Joins.eq_or_eq hj hgz with h | h
        · exact hay (h ▸ hz)
        · rcases Joins.eq_or_eq hj hjz.incident_right with h' | h'
          · exact hz' ⟨0, hp0.trans h'.symm⟩
          · rcases hjz with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · exact hloop g (h₁.trans (h.trans (h'.symm.trans h₂.symm)))
            · exact hloop g (h₁.trans (h'.trans (h.symm.trans h₂.symm)))
      have hP' := hP.snoc hz' hg hjz
      have hcard : k + 2 ≤ Nat.card V := by
        have := Nat.card_le_card_of_injective _ hP'.injective
        simp at this
        omega
      refine ih (Nat.card V - (k + 1)) (by omega) (k + 1) _ _ rfl (by omega) hP' ?_ ?_
      · rw [← hp0]
        exact Fin.snoc_castSucc (α := fun _ => V) (i := 0) ..
      · intro i hi
        induction i using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last]
          exact hz.tail ⟨g, hgc, hjz⟩
        | cast i =>
          rw [Fin.snoc_castSucc]
          exact hside i (fun h => hi (by rw [h]; rfl))
  have hay' : a ≠ y := fun h => by
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hloop c (h₁.trans (h.trans h₂.symm))
    · exact hloop c (h₁.trans (h.symm.trans h₂.symm))
  refine hext _ 1 ![a, y] ![c] rfl one_pos ⟨fun i => ?_, fun i => ?_, fun i j h => ?_⟩ rfl
    (fun i hi => ?_)
  · fin_cases i
    exact hc
  · fin_cases i
    exact hj
  · fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h hay'
    · exact absurd h.symm hay'
    · rfl
  · fin_cases i
    · exact absurd rfl hi
    · exact .refl

/-- **In a network whose cycles share no node, a walk on edges of cycles from a node of a cycle
stays on that cycle.** -/
theorem mem_cycleNodes_of_walks_cycleEdges
    (hnd : ∀ C C', IsCycle G C → IsCycle G C' → (cycleNodes G C ∩ cycleNodes G C').Nonempty →
      C = C') {C : Set E} (hC : IsCycle G C) {a b : V} (ha : a ∈ cycleNodes G C)
    (h : G.Walks {e | ∃ C', IsCycle G C' ∧ e ∈ C'} a b) : b ∈ cycleNodes G C := by
  induction h with
  | refl => exact ha
  | @tail y z _ hst ih =>
    obtain ⟨f, ⟨C', hC', hfC'⟩, hj⟩ := hst
    have hy : y ∈ cycleNodes G C' := hj.elim (fun h => ⟨f, hfC', Or.inl h.1⟩)
      (fun h => ⟨f, hfC', Or.inr h.2⟩)
    obtain rfl := hnd C C' hC hC' ⟨y, ih, hy⟩
    exact hj.elim (fun h => ⟨f, hfC', Or.inr h.2⟩) (fun h => ⟨f, hfC', Or.inl h.1⟩)

end Graph

/-! ### Restriction and suppression -/

section Restrict

variable {W F X : Type*} {H : SemidirectedNetwork W F X} {K : Set F} {Z : Set X}

/-- A walk of the restricted network is a walk of the network. -/
theorem restrict_walks_val {F' : Set K} {a b : keptNodes H K Z}
    (h : (restrict H K Z).graph.Walks F' a b) : H.graph.Walks (Subtype.val '' F') a.1 b.1 := by
  induction h with
  | refl => exact .refl
  | @tail c d _ hst ih =>
    obtain ⟨f, hf, hj⟩ := hst
    refine ih.tail ⟨f.1, ⟨f, hf, rfl⟩, ?_⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
    · exact Or.inr ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩

/-- A walk of the network on kept edges between kept nodes is a walk of the restricted network. -/
theorem restrict_walks_of_walks {F' : Set F} (hF' : F' ⊆ K) {a b : W} (h : H.graph.Walks F' a b)
    (ha : a ∈ keptNodes H K Z) (hb : b ∈ keptNodes H K Z) :
    (restrict H K Z).graph.Walks {f | f.1 ∈ F'} ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact .refl
  | @tail c d _ hcd ih =>
    obtain ⟨f, hf, hj⟩ := hcd
    have hc : c ∈ keptNodes H K Z := by
      rcases hj with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact Or.inl ⟨f, hF' hf, Or.inl h₁⟩
      · exact Or.inl ⟨f, hF' hf, Or.inr h₂⟩
    refine (ih hc).tail ⟨⟨f, hF' hf⟩, hf, ?_⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨Subtype.ext h₁, Subtype.ext h₂⟩
    · exact Or.inr ⟨Subtype.ext h₁, Subtype.ext h₂⟩

/-- The restricted network has no loops when the network has none. -/
theorem restrict_source_ne_target (hloop : ∀ e, H.graph.source e ≠ H.graph.target e) (e : K) :
    (restrict H K Z).graph.source e ≠ (restrict H K Z).graph.target e := fun h =>
  hloop e.1 (congrArg Subtype.val h)

/-- An edge of the restricted network whose ends are joined without it lies on a cycle of the
network. -/
theorem exists_isCycle_of_restrict_walks {e : K}
    (h : (restrict H K Z).graph.Walks {e}ᶜ ((restrict H K Z).graph.source e)
      ((restrict H K Z).graph.target e)) : ∃ C, IsCycle H.graph C ∧ e.1 ∈ C :=
  exists_isCycle_of_walks_compl (walks_mono (by
    rintro _ ⟨f, hf, rfl⟩ h
    exact hf (Subtype.ext (Set.mem_singleton_iff.1 h))) (restrict_walks_val h))

/-- A walk of the restricted network on edges of its cycles is a walk of the network on edges of its
cycles. -/
theorem restrict_walks_cycleEdges {a b : keptNodes H K Z}
    (h : (restrict H K Z).graph.Walks {e | ∃ C, IsCycle (restrict H K Z).graph C ∧ e ∈ C} a b) :
    H.graph.Walks {e | ∃ C, IsCycle H.graph C ∧ e ∈ C} a.1 b.1 := by
  refine walks_mono ?_ (restrict_walks_val h)
  rintro _ ⟨e, ⟨C, hC, heC⟩, rfl⟩
  exact exists_isCycle_of_restrict_walks (walks_compl_of_mem_isCycle hC heC)

/-- **A cycle with kept edges is a cycle of the restricted network.** -/
theorem isCycleOf_restrict {k : ℕ} {v : Fin k → W} {e : Fin k → F}
    (hc : IsCycleOf H.graph k v e) (he : ∀ i, e i ∈ K) :
    IsCycleOf (restrict H K Z).graph k
      (fun i => ⟨v i, Or.inl ⟨e i, he i, (hc.joins i).incident_left⟩⟩) (fun i => ⟨e i, he i⟩) where
  pos := hc.pos
  joins i := by
    rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨Subtype.ext h₁, Subtype.ext h₂⟩
    · exact Or.inr ⟨Subtype.ext h₁, Subtype.ext h₂⟩
  injective_node i j h := hc.injective_node (congrArg Subtype.val h)
  injective_edge i j h := hc.injective_edge (congrArg Subtype.val h)

end Restrict

section SuppressExcept

variable {W F X : Type*} {K : SemidirectedNetwork W F X} {P : Set W}

/-- The ends of an edge of the suppressed network are the first and last nodes of its chain. -/
theorem suppressExcept_ends_val (c : {c // IsChain K P c}) :
    (((suppressExcept K P).graph.source c).1 = (chainRep K P c.2).p 0 ∧
        ((suppressExcept K P).graph.target c).1 = (chainRep K P c.2).p (Fin.last _)) ∨
      (((suppressExcept K P).graph.source c).1 = (chainRep K P c.2).p (Fin.last _) ∧
        ((suppressExcept K P).graph.target c).1 = (chainRep K P c.2).p 0) := by
  obtain ⟨c, hc⟩ := c
  rw [suppressExcept_source_val hc, suppressExcept_target_val hc]
  unfold ChainRep.src ChainRep.tgt
  split_ifs
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- A chain at a kept node of one of its edges has that node as an end. -/
theorem suppressExcept_incident_of_mem (c : {c // IsChain K P c}) {g : F} (hg : g ∈ c.1) {w : W}
    (hw : IsBranch K P w) (hinc : K.graph.source g = w ∨ K.graph.target g = w) :
    (suppressExcept K P).graph.source c = ⟨w, hw⟩ ∨
      (suppressExcept K P).graph.target c = ⟨w, hw⟩ := by
  have hmem : w ∈ chainEnds K P c.1 := ⟨hw, g, hg, hinc⟩
  rw [← (chainRep K P c.2).range_eq, (chainRep K P c.2).isChainOf.chainEnds_eq] at hmem
  rcases suppressExcept_ends_val c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hmem with h | h
  · exact Or.inl (Subtype.ext (h₁.trans h.symm))
  · exact Or.inr (Subtype.ext (h₂.trans (Set.mem_singleton_iff.1 h).symm))
  · exact Or.inr (Subtype.ext (h₂.trans h.symm))
  · exact Or.inl (Subtype.ext (h₁.trans (Set.mem_singleton_iff.1 h).symm))

/-- A walk of the suppressed network is a walk of the network on the edges of its chains. -/
theorem suppressExcept_walks_val {F' : Set {c // IsChain K P c}} {S : Set F}
    (hFS : ∀ c ∈ F', c.1 ⊆ S) {u w : {u // IsBranch K P u}}
    (h : (suppressExcept K P).graph.Walks F' u w) : K.graph.Walks S u.1 w.1 := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hst ih =>
    obtain ⟨c, hc, hj⟩ := hst
    refine ih.trans ?_
    have hw := walks_mono (hFS c hc) (chainRep K P c.2).walks_ends
    rcases suppressExcept_ends_val c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      rcases hj with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩ <;> rw [k₁] at h₁ <;> rw [k₂] at h₂
    · rw [h₁, h₂]; exact hw
    · rw [h₁, h₂]; exact K.graph.walks_symm hw
    · rw [h₁, h₂]; exact K.graph.walks_symm hw
    · rw [h₁, h₂]; exact hw

/-- **A walk of the network between kept nodes is a walk of the suppressed network**, on the chains
of its edges, when every edge lies on a chain. -/
theorem suppressExcept_walks_of_walks [Finite F] (hch : ∀ g, ∃ c, IsChain K P c ∧ g ∈ c)
    {F' : Set F} {u w : {u // IsBranch K P u}} (h : K.graph.Walks F' u.1 w.1) :
    (suppressExcept K P).graph.Walks {c | ∃ g ∈ c.1, g ∈ F'} u w := by
  set S := suppressExcept K P
  set FS : Set {c // IsChain K P c} := {c | ∃ g ∈ c.1, g ∈ F'}
  set Rch := {x | S.graph.Walks FS u x}
  have hRc : ∀ c ∈ FS, S.graph.source c ∈ Rch ↔ S.graph.target c ∈ Rch := fun c hc =>
    ⟨fun h => h.tail ⟨c, hc, Or.inl ⟨rfl, rfl⟩⟩, fun h => h.tail ⟨c, hc, Or.inr ⟨rfl, rfl⟩⟩⟩
  set A : Set W := {y | (∀ hy : IsBranch K P y, (⟨y, hy⟩ : {u // IsBranch K P u}) ∈ Rch) ∧
    ∀ g ∈ F', (K.graph.source g = y ∨ K.graph.target g = y) → ∀ c : {c // IsChain K P c},
      g ∈ c.1 → S.graph.source c ∈ Rch}
  have key : ∀ g ∈ F', ∀ c : {c // IsChain K P c}, g ∈ c.1 → ∀ y,
      (K.graph.source g = y ∨ K.graph.target g = y) → (y ∈ A ↔ S.graph.source c ∈ Rch) := by
    intro g hgF c hgc y hinc
    have hcF : c ∈ FS := ⟨g, hgc, hgF⟩
    refine ⟨fun h => h.2 g hgF hinc c hgc, fun hc => ?_⟩
    by_cases hy : IsBranch K P y
    · have hyR : (⟨y, hy⟩ : {u // IsBranch K P u}) ∈ Rch := by
        rcases suppressExcept_incident_of_mem c hgc hy hinc with h | h
        · exact h ▸ hc
        · exact h ▸ (hRc c hcF).1 hc
      refine ⟨fun _ => hyR, fun g' hg'F hinc' c' hg'c' => ?_⟩
      rcases suppressExcept_incident_of_mem c' hg'c' hy hinc' with h | h
      · exact h ▸ hyR
      · exact (hRc c' ⟨g', hg'c', hg'F⟩).2 (h ▸ hyR)
    · refine ⟨fun h => absurd h hy, fun g' _ hinc' c' hg'c' => ?_⟩
      have hl : ChainLink K P g g' := ⟨y, hy, hinc, hinc'⟩
      set r := chainRep K P c.2
      obtain ⟨i, hi⟩ : g ∈ Set.range r.e := by rw [r.range_eq]; exact hgc
      have hg'c : g' ∈ c.1 := by
        rw [← r.range_eq]
        exact r.isChainOf.mem_of_chainLink (hi ▸ hl)
      have : c = c' := Subtype.ext (c.2.eq_of_mem c'.2 hg'c hg'c')
      rw [← this]
      exact hc
  have hS : ∀ g ∈ F', ¬ K.graph.Crosses g A := by
    intro g hg hcr
    obtain ⟨c, hc, hgc⟩ := hch g
    have h₁ := key g hg ⟨c, hc⟩ hgc _ (Or.inl rfl)
    have h₂ := key g hg ⟨c, hc⟩ hgc _ (Or.inr rfl)
    rcases hcr with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact ht (h₂.2 (h₁.1 hs))
    · exact hs (h₁.2 (h₂.1 ht))
  have hu : u.1 ∈ A := by
    refine ⟨fun _ => .refl, fun g hg hinc c hgc => ?_⟩
    rcases suppressExcept_incident_of_mem c hgc u.2 hinc with h | h
    · rw [h]
      exact .refl
    · exact (hRc c ⟨g, hgc, hg⟩).2 (by rw [h]; exact .refl)
  exact ((K.graph.mem_iff_mem_of_walks hS h).1 hu).1 w.2

/-- **The edges of a chain whose ends are joined without it lie on cycles of the network**: the rest
of the chain and that walk join the ends of each edge without it. -/
theorem exists_isCycle_of_suppressExcept_walks [Finite F] (d : {c // IsChain K P c})
    (h : (suppressExcept K P).graph.Walks {d}ᶜ ((suppressExcept K P).graph.source d)
      ((suppressExcept K P).graph.target d)) {g : F} (hg : g ∈ d.1) :
    ∃ C, IsCycle K.graph C ∧ g ∈ C := by
  set r := chainRep K P d.2
  have hw : K.graph.Walks d.1ᶜ ((suppressExcept K P).graph.source d).1
      ((suppressExcept K P).graph.target d).1 :=
    suppressExcept_walks_val (S := d.1ᶜ) (fun c (hc : c ∈ ({d}ᶜ : Set _)) f hf hfd =>
      hc (Set.mem_singleton_iff.2 (Subtype.ext (c.2.eq_of_mem d.2 hf hfd)))) h
  have hw' : K.graph.Walks d.1ᶜ (r.p (Fin.last r.k)) (r.p 0) := by
    rcases suppressExcept_ends_val d with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at hw
      exact K.graph.walks_symm hw
    · rw [h₁, h₂] at hw
      exact hw
  obtain ⟨i, rfl⟩ : g ∈ Set.range r.e := by rw [r.range_eq]; exact hg
  have hA : K.graph.Walks {r.e i}ᶜ (r.p i.succ) (r.p (Fin.last r.k)) := by
    refine walks_mono (fun f hf => ?_) (walks_of_joins_le r.isChainOf.joins (Fin.le_last _))
    obtain ⟨l, hl, -, rfl⟩ := hf
    intro h'
    have := congrArg Fin.val (r.isChainOf.injective_edge (Set.mem_singleton_iff.1 h'))
    simp at hl
    omega
  have hB : K.graph.Walks {r.e i}ᶜ (r.p 0) (r.p i.castSucc) := by
    refine walks_mono (fun f hf => ?_) (walks_of_joins_le r.isChainOf.joins (Fin.zero_le _))
    obtain ⟨l, -, hl, rfl⟩ := hf
    intro h'
    have := congrArg Fin.val (r.isChainOf.injective_edge (Set.mem_singleton_iff.1 h'))
    simp at hl
    omega
  have hmid : K.graph.Walks {r.e i}ᶜ (r.p (Fin.last r.k)) (r.p 0) :=
    walks_mono (F' := {r.e i}ᶜ) (fun f (hf : f ∈ d.1ᶜ) hfe => hf (by
      rw [Set.mem_singleton_iff.1 hfe]
      exact hg)) hw'
  have hall := (hA.trans hmid).trans hB
  refine exists_isCycle_of_walks_compl ?_
  rcases r.isChainOf.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
    exact K.graph.walks_symm hall
  · rw [h₁, h₂]
    exact hall

/-- An edge of the suppressed network at a kept node has an edge of its chain at that node: the
first or the last edge. -/
theorem suppressExcept_exists_mem_incident {d : {c // IsChain K P c}} {s : {u // IsBranch K P u}}
    (h : (suppressExcept K P).graph.source d = s ∨ (suppressExcept K P).graph.target d = s) :
    ∃ g ∈ d.1, K.graph.source g = s.1 ∨ K.graph.target g = s.1 := by
  set r := chainRep K P d.2
  have hk := r.isChainOf.pos
  have hmem : ∀ i, r.e i ∈ d.1 := fun i => (Set.ext_iff.1 r.range_eq _).1 ⟨i, rfl⟩
  have h0 : ∃ g ∈ d.1, K.graph.source g = r.p 0 ∨ K.graph.target g = r.p 0 :=
    ⟨r.e ⟨0, hk⟩, hmem _, (r.isChainOf.joins ⟨0, hk⟩).incident_left⟩
  have hl : ∃ g ∈ d.1, K.graph.source g = r.p (Fin.last r.k) ∨
      K.graph.target g = r.p (Fin.last r.k) := by
    have hlast : (⟨r.k - 1, by omega⟩ : Fin r.k).succ = Fin.last r.k := Fin.ext (by simp; omega)
    have := (r.isChainOf.joins ⟨r.k - 1, by omega⟩).incident_right
    rw [hlast] at this
    exact ⟨_, hmem _, this⟩
  have hs : s.1 = r.p 0 ∨ s.1 = r.p (Fin.last r.k) := by
    rcases suppressExcept_ends_val d with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases h with rfl | rfl
    · exact Or.inl h₁
    · exact Or.inr h₂
    · exact Or.inr h₁
    · exact Or.inl h₂
  rcases hs with hs | hs <;> rw [hs]
  exacts [h0, hl]

/-- A walk of the suppressed network on edges of its cycles is a walk of the network on edges of its
cycles. -/
theorem suppressExcept_walks_cycleEdges [Finite F] {a b : {u // IsBranch K P u}}
    (h : (suppressExcept K P).graph.Walks
      {d | ∃ C, IsCycle (suppressExcept K P).graph C ∧ d ∈ C} a b) :
    K.graph.Walks {e | ∃ C, IsCycle K.graph C ∧ e ∈ C} a.1 b.1 :=
  suppressExcept_walks_val (F' := {d | ∃ C, IsCycle (suppressExcept K P).graph C ∧ d ∈ C})
    (fun _ ⟨_, hC, hdC⟩ _ hg =>
      exists_isCycle_of_suppressExcept_walks _ (walks_compl_of_mem_isCycle hC hdC) hg) h

/-- An edge between two distinct kept nodes is a chain by itself. -/
theorem isChain_singleton {g : F} {a b : W} (hj : Joins K.graph g a b) (ha : IsBranch K P a)
    (hb : IsBranch K P b) : IsChain K P {g} := by
  refine ⟨1, ![a, b], ![g], ⟨one_pos, fun i => ?_, fun i h0 hl => ?_, ⟨ha, hb⟩,
    fun i j _ => Subsingleton.elim i j⟩, ?_⟩
  · fin_cases i
    exact hj
  · fin_cases i
    · exact absurd rfl h0
    · exact absurd rfl hl
  · ext f
    simp [eq_comm]

/-- **The chain of one edge joins its ends** in the suppressed network. -/
theorem joins_suppressExcept_singleton {g : F} {a b : W} (hj : Joins K.graph g a b) (hab : a ≠ b)
    (ha : IsBranch K P a) (hb : IsBranch K P b) (hc : IsChain K P {g}) :
    Joins (suppressExcept K P).graph ⟨{g}, hc⟩ ⟨a, ha⟩ ⟨b, hb⟩ := by
  have h₁ := suppressExcept_incident_of_mem ⟨{g}, hc⟩ (Set.mem_singleton g) ha hj.incident_left
  have h₂ := suppressExcept_incident_of_mem ⟨{g}, hc⟩ (Set.mem_singleton g) hb hj.incident_right
  have hab' : (⟨a, ha⟩ : {u // IsBranch K P u}) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact absurd (h₁.symm.trans h₂) hab'
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₂, h₁⟩
  · exact absurd (h₁.symm.trans h₂) hab'

/-- **Two distinct edges of a chain at the same kept node make its ends equal**: each is its first
or its last edge, with that node as the first or last node of the chain. -/
theorem suppressExcept_source_eq_target_of_ne (c : {c // IsChain K P c}) {g₁ g₂ : F}
    (hg₁ : g₁ ∈ c.1) (hg₂ : g₂ ∈ c.1) (hne : g₁ ≠ g₂) {w : W} (hw : IsBranch K P w)
    (h₁ : K.graph.source g₁ = w ∨ K.graph.target g₁ = w)
    (h₂ : K.graph.source g₂ = w ∨ K.graph.target g₂ = w) :
    (suppressExcept K P).graph.source c = (suppressExcept K P).graph.target c := by
  set r := chainRep K P c.2
  obtain ⟨i₁, rfl⟩ : g₁ ∈ Set.range r.e := by rw [r.range_eq]; exact hg₁
  obtain ⟨i₂, rfl⟩ : g₂ ∈ Set.range r.e := by rw [r.range_eq]; exact hg₂
  have hv₁ := r.isChainOf.val_of_incident hw h₁
  have hv₂ := r.isChainOf.val_of_incident hw h₂
  have heq : r.p 0 = r.p (Fin.last r.k) := by
    rcases hv₁ with ⟨k₁, l₁⟩ | ⟨k₁, l₁⟩ <;> rcases hv₂ with ⟨k₂, l₂⟩ | ⟨k₂, l₂⟩
    · exact absurd (congrArg r.e (Fin.ext (l₁.trans l₂.symm))) hne
    · exact k₁.symm.trans k₂
    · exact k₂.symm.trans k₁
    · exact absurd (congrArg r.e (Fin.ext (l₁.trans l₂.symm))) hne
  apply Subtype.ext
  rcases suppressExcept_ends_val c with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
  · rw [k₁, k₂, heq]
  · rw [k₁, k₂, heq]

/-- **A cycle whose nodes are kept is a cycle of the suppressed network**, through the chains of
its single edges. -/
theorem isCycleOf_suppressExcept {k : ℕ} {v : Fin k → W} {e : Fin k → F}
    (hc : IsCycleOf K.graph k v e) (hloop : ∀ i, K.graph.source (e i) ≠ K.graph.target (e i))
    (hb : ∀ i, IsBranch K P (v i)) :
    IsCycleOf (suppressExcept K P).graph k (fun i => ⟨v i, hb i⟩)
      (fun i => ⟨{e i}, isChain_singleton (hc.joins i) (hb i) (hb _)⟩) where
  pos := hc.pos
  joins i := by
    refine joins_suppressExcept_singleton (hc.joins i) (fun h => hloop i ?_) _ _ _
    rcases hc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂, h]
    · rw [h₁, h₂, h]
  injective_node i j h := hc.injective_node (congrArg Subtype.val h)
  injective_edge i j h := hc.injective_edge (Set.singleton_injective (congrArg Subtype.val h))

end SuppressExcept

/-! ### The tree of cycles of a network -/

section Tree

/-- **A finite multigraph tree with a node has a leaf**: with one node it has no edge, a loop being
impossible; with more, its simple graph is a tree with a node of degree one. -/
theorem exists_isLeafNode_of_isTree {V E : Type*} [Finite V] [Finite E]
    {G : DirectedMultigraph V E} (hG : G.IsTree) [Nonempty V] : ∃ w, IsLeafNode G w := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · obtain ⟨w⟩ := ‹Nonempty V›
    exact ⟨w, fun e _ _ _ => absurd (Subsingleton.elim _ _) (isTree_source_ne_target hG e)⟩
  · have := Fintype.ofFinite V
    obtain ⟨w, hw⟩ := hG.toSimpleGraph_isTree.exists_vert_degree_one_of_nontrivial
    refine ⟨w, ?_⟩
    have h1 : degree G w = 1 := by
      rw [← isTree_ncard_neighborSet hG w, SimpleGraph.ncard_neighborSet, hw]
    rw [degree_eq_ncard_incident (isTree_source_ne_target hG)] at h1
    obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 h1
    rw [IsLeafNode, he₀]
    exact Set.subsingleton_singleton

variable {W F X : Type*} (H : SemidirectedNetwork W F X)

/-- **Step 1 of Definition 13**: the edges of the pendant core of `H`, with their ends. -/
abbrev coreNet := restrict H (pendantCore H.graph) ∅

/-- The nodes of `coreNet H` on cycles of `H`, which step 2 of Definition 13 keeps. -/
abbrev coreCycleNodes : Set (keptNodes H (pendantCore H.graph) ∅) :=
  {u | ∃ C, IsCycle H.graph C ∧ u.1 ∈ cycleNodes H.graph C}

/-- **Step 2 of Definition 13**: `coreNet H` with its nodes of degree two on no cycle suppressed.
Contracting its cycles (step 3) gives the tree of cycles. -/
abbrev coreSuppressed := suppressExcept (coreNet H) (coreCycleNodes H)

/-- The tree of cycles contracts the cycles of `coreSuppressed H`. -/
theorem treeOfCycles_eq : treeOfCycles H = contractCycles (coreSuppressed H) fun _ => True := rfl

variable {H}

/-- A node of `coreNet H` is an end of an edge of the core. -/
theorem exists_mem_pendantCore_of_keptNodes (u : keptNodes H (pendantCore H.graph) ∅) :
    ∃ e ∈ pendantCore H.graph, H.graph.source e = u.1 ∨ H.graph.target e = u.1 := by
  rcases u.2 with h | ⟨z, hz, -⟩
  · exact h
  · exact absurd hz (Set.notMem_empty z)

/-- **The edges at the nodes that step 2 removes are bridges**: an edge of `coreNet H` whose ends
are joined without it lies on a cycle of `H`, whose nodes are kept. -/
theorem coreNet_bridge (e : pendantCore H.graph) (u : keptNodes H (pendantCore H.graph) ∅)
    (hu : ¬ IsBranch (coreNet H) (coreCycleNodes H) u)
    (he : (coreNet H).graph.source e = u ∨ (coreNet H).graph.target e = u) :
    ¬ (coreNet H).graph.Walks {e}ᶜ ((coreNet H).graph.source e) ((coreNet H).graph.target e) := by
  intro hw
  obtain ⟨C, hC, heC⟩ := exists_isCycle_of_restrict_walks hw
  refine hu (Or.inr (Or.inr ⟨C, hC, ?_⟩))
  rcases he with h | h
  · exact ⟨e.1, heC, Or.inl (congrArg Subtype.val h)⟩
  · exact ⟨e.1, heC, Or.inr (congrArg Subtype.val h)⟩

variable [Finite F]

/-- **The edges of a chain of the suppressed core whose ends are joined without it lie on cycles
of `H`.** -/
theorem exists_isCycle_of_coreSuppressed_walks
    (d : {c // IsChain (coreNet H) (coreCycleNodes H) c})
    (h : (coreSuppressed H).graph.Walks {d}ᶜ ((coreSuppressed H).graph.source d)
      ((coreSuppressed H).graph.target d)) {g : pendantCore H.graph} (hg : g ∈ d.1) :
    ∃ C, IsCycle H.graph C ∧ g.1 ∈ C := by
  obtain ⟨C, hC, hgC⟩ := exists_isCycle_of_suppressExcept_walks d h hg
  exact exists_isCycle_of_restrict_walks (walks_compl_of_mem_isCycle hC hgC)

/-- A chain of the suppressed core with an edge on no cycle of `H` is an edge of the tree of cycles:
it lies on no cycle. -/
theorem forall_notMem_of_coreSuppressed (d : {c // IsChain (coreNet H) (coreCycleNodes H) c})
    {g : pendantCore H.graph} (hg : g ∈ d.1) (hgC : ∀ C, IsCycle H.graph C → g.1 ∉ C) :
    ∀ C, IsCycle (coreSuppressed H).graph C → True → d ∉ C := by
  intro C hC _ hdC
  obtain ⟨D, hD, hgD⟩ := exists_isCycle_of_coreSuppressed_walks d
    (walks_compl_of_mem_isCycle hC hdC) hg
  exact hgC D hD hgD

variable [Finite W] (hloop : ∀ e, H.graph.source e ≠ H.graph.target e)
include hloop

/-- **Every edge of `coreNet H` lies on a chain.** -/
theorem exists_isChain_coreNet (g : pendantCore H.graph) :
    ∃ c, IsChain (coreNet H) (coreCycleNodes H) c ∧ g ∈ c :=
  exists_isChain_mem_of_bridge (restrict_source_ne_target hloop) coreNet_bridge g

variable (hconn : H.graph.IsConnected)
include hconn

/-- **The suppressed core is connected**: a path of `H` between two nodes of the core lies in the
core (`mem_pendantCore_of_isPathOf`), and passes through suppression. -/
theorem coreSuppressed_isConnected : (coreSuppressed H).graph.IsConnected := by
  intro s₁ s₂
  obtain ⟨n, p, q, hP, hp0, hpn⟩ := exists_isPathOf_of_walks (hconn s₁.1.1 s₂.1.1)
  have hq : ∀ i, q i ∈ pendantCore H.graph := mem_pendantCore_of_isPathOf hP
    (hp0 ▸ exists_mem_pendantCore_of_keptNodes s₁.1)
    (hpn ▸ exists_mem_pendantCore_of_keptNodes s₂.1)
  have hw : H.graph.Walks (pendantCore H.graph) s₁.1.1 s₂.1.1 := by
    rw [← hp0, ← hpn]
    refine walks_mono (fun f hf => ?_) (hP.walks_of_le (Fin.zero_le _))
    obtain ⟨l, -, -, rfl⟩ := hf
    exact hq l
  have hR := restrict_walks_of_walks (Z := ∅) le_rfl hw s₁.1.2 s₂.1.2
  exact walks_mono (Set.subset_univ _)
    (suppressExcept_walks_of_walks (exists_isChain_coreNet hloop) (u := s₁) (w := s₂) hR)

/-- **Definition 13 gives a tree**: the tree of cycles is connected, and contracting all the cycles
leaves no edge whose ends are joined without it. -/
theorem treeOfCycles_isTree : (treeOfCycles H).graph.IsTree :=
  contract_isTree (P := fun _ => True) (fun _ _ => trivial) (coreSuppressed_isConnected hloop hconn)

/-- **Two nodes of the suppressed core in one class of the tree of cycles, each the end of an edge
of the tree, give two edges at that class**: one edge at both would be a loop of the tree. -/
theorem not_isLeafNode_mk_of_two {s₁ s₂ : {u // IsBranch (coreNet H) (coreCycleNodes H) u}}
    (hs : s₁ ≠ s₂)
    (hcl : (Quot.mk _ s₁ : Quot (ContractRel (coreSuppressed H).graph fun _ => True)) =
      Quot.mk _ s₂)
    {d₁ d₂ : {c // IsChain (coreNet H) (coreCycleNodes H) c}}
    (hn₁ : ∀ C, IsCycle (coreSuppressed H).graph C → True → d₁ ∉ C)
    (hn₂ : ∀ C, IsCycle (coreSuppressed H).graph C → True → d₂ ∉ C)
    (hi₁ : (coreSuppressed H).graph.source d₁ = s₁ ∨ (coreSuppressed H).graph.target d₁ = s₁)
    (hi₂ : (coreSuppressed H).graph.source d₂ = s₂ ∨ (coreSuppressed H).graph.target d₂ = s₂) :
    ¬ IsLeafNode (treeOfCycles H).graph (Quot.mk _ s₁) := by
  intro hleaf
  have hT := treeOfCycles_isTree hloop hconn
  have hT₁ : (treeOfCycles H).graph.source ⟨d₁, hn₁⟩ = Quot.mk _ s₁ ∨
      (treeOfCycles H).graph.target ⟨d₁, hn₁⟩ = Quot.mk _ s₁ :=
    hi₁.imp (congrArg (Quot.mk _)) (congrArg (Quot.mk _))
  have hT₂ : (treeOfCycles H).graph.source ⟨d₂, hn₂⟩ = Quot.mk _ s₁ ∨
      (treeOfCycles H).graph.target ⟨d₂, hn₂⟩ = Quot.mk _ s₁ := by
    rw [hcl]
    exact hi₂.imp (congrArg (Quot.mk _)) (congrArg (Quot.mk _))
  have hd : d₁ = d₂ := congrArg Subtype.val (hleaf hT₁ hT₂)
  subst hd
  have hloopT := isTree_source_ne_target hT ⟨d₁, hn₁⟩
  rcases hi₁ with h₁ | h₁ <;> rcases hi₂ with h₂ | h₂
  · exact hs (h₁.symm.trans h₂)
  · exact hloopT ((congrArg (Quot.mk _) h₁).trans (hcl.trans (congrArg (Quot.mk _) h₂).symm))
  · exact hloopT ((congrArg (Quot.mk _) h₂).trans (hcl.symm.trans (congrArg (Quot.mk _) h₁).symm))
  · exact hs (h₁.symm.trans h₂)

/-- **A node of the core on no cycle of `H` is not a leaf of the tree of cycles**: it has two edges
of the core (`two_le_pendantCount_pendantCore`), on two chains, which are distinct (else the chain
would be a loop of the tree) and lie on no cycle. -/
theorem not_isLeafNode_mk_of_notMem (s : {u // IsBranch (coreNet H) (coreCycleNodes H) u})
    (hs : s.1 ∉ coreCycleNodes H) :
    ¬ IsLeafNode (treeOfCycles H).graph (Quot.mk _ s) := by
  intro hleaf
  have hT := treeOfCycles_isTree hloop hconn
  have hu : ∀ C, IsCycle H.graph C → s.1.1 ∉ cycleNodes H.graph C := fun C hC h => hs ⟨C, hC, h⟩
  obtain ⟨k, hk, hks⟩ := exists_mem_pendantCore_of_keptNodes s.1
  obtain ⟨g₁, hg₁, g₂, hg₂, hne, h₁, h₂⟩ :=
    exists_ne_of_two_le_pendantCount hloop (two_le_pendantCount_pendantCore hk hks)
  have hinc : ∀ (g : F) (hg : g ∈ pendantCore H.graph) (_ : H.graph.source g = s.1.1 ∨
      H.graph.target g = s.1.1),
      (coreNet H).graph.source ⟨g, hg⟩ = s.1 ∨ (coreNet H).graph.target ⟨g, hg⟩ = s.1 := by
    intro g hg h
    rcases h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  obtain ⟨d₁, hd₁, hgd₁⟩ := exists_isChain_coreNet hloop ⟨g₁, hg₁⟩
  obtain ⟨d₂, hd₂, hgd₂⟩ := exists_isChain_coreNet hloop ⟨g₂, hg₂⟩
  have hn₁ := forall_notMem_of_coreSuppressed ⟨d₁, hd₁⟩ hgd₁
    fun C hC hgC => hu C hC ⟨g₁, hgC, h₁⟩
  have hn₂ := forall_notMem_of_coreSuppressed ⟨d₂, hd₂⟩ hgd₂
    fun C hC hgC => hu C hC ⟨g₂, hgC, h₂⟩
  have hT₁ : (treeOfCycles H).graph.source ⟨⟨d₁, hd₁⟩, hn₁⟩ = Quot.mk _ s ∨
      (treeOfCycles H).graph.target ⟨⟨d₁, hd₁⟩, hn₁⟩ = Quot.mk _ s := by
    rcases suppressExcept_incident_of_mem ⟨d₁, hd₁⟩ hgd₁ s.2 (hinc g₁ hg₁ h₁) with h | h
    · exact Or.inl (congrArg (Quot.mk _) h)
    · exact Or.inr (congrArg (Quot.mk _) h)
  have hT₂ : (treeOfCycles H).graph.source ⟨⟨d₂, hd₂⟩, hn₂⟩ = Quot.mk _ s ∨
      (treeOfCycles H).graph.target ⟨⟨d₂, hd₂⟩, hn₂⟩ = Quot.mk _ s := by
    rcases suppressExcept_incident_of_mem ⟨d₂, hd₂⟩ hgd₂ s.2 (hinc g₂ hg₂ h₂) with h | h
    · exact Or.inl (congrArg (Quot.mk _) h)
    · exact Or.inr (congrArg (Quot.mk _) h)
  have hd : d₁ = d₂ := congrArg (fun t => t.1.1) (hleaf hT₁ hT₂)
  subst hd
  have := suppressExcept_source_eq_target_of_ne ⟨d₁, hd₁⟩ hgd₁ hgd₂
    (fun h => hne (congrArg Subtype.val h)) s.2 (hinc g₁ hg₁ h₁) (hinc g₂ hg₂ h₂)
  exact isTree_source_ne_target hT ⟨⟨d₁, hd₁⟩, hn₁⟩ (congrArg (Quot.mk _) this)

end Tree

/-! ### The network `Ñ` -/

section Tilde

variable {V E X : Type*} {G : SemidirectedNetwork V E X}

/-- The node `w` of the tree of cycles of `Ñ` *arises from* the cycle `C` of the network: `w` is the
class of a node of the suppressed core of `Ñ` coming from a node of `C`. For `C` of size at least
four, the nodes coming from the nodes of `C` are all in that class (`treeOfCycles_mk_eq_of_big`),
and are its only nodes (`exists_mem_of_mk_eq_of_big`). -/
def ArisesFrom (G : SemidirectedNetwork V E X)
    (w : Quot (ContractRel (coreSuppressed (tildeNetwork G)).graph fun _ => True)) (C : Set E) :
    Prop :=
  ∃ u ∈ cycleNodes G.graph C, ∃ s : {x // IsBranch (coreNet (tildeNetwork G))
    (coreCycleNodes (tildeNetwork G)) x}, s.1.1.1 = Quot.mk _ u ∧ w = Quot.mk _ s

/-- The block of the node `u` of the cycle `C` is a *4-network block*: its taxa are in one block of
the family of the cycles of size at least four. -/
def IsFourNetworkBlock (G : SemidirectedNetwork V E X) (C : Set E) (u : V) : Prop :=
  ∀ x ∈ nodeBlock G.graph G.leaf C u, ∀ y ∈ nodeBlock G.graph G.leaf C u,
    SameBlock G.graph G.leaf (familyEdges (cyclesOfSizeAtLeast G.graph 4)) x y

/-- A node of a cycle is on the cycle of its edges. -/
theorem IsCycleOf.mem_cycleNodes {V' E' : Type*} {H : DirectedMultigraph V' E'} {k : ℕ}
    {v : Fin k → V'} {e : Fin k → E'} (hc : IsCycleOf H k v e) (i : Fin k) :
    v i ∈ cycleNodes H (Set.range e) :=
  ⟨e i, ⟨i, rfl⟩, (hc.joins i).incident_left⟩

/-- **A multigraph tree has no cycle**: the ends of an edge of a cycle are joined without it. -/
theorem not_isCycle_of_isTree {V' E' : Type*} {H : DirectedMultigraph V' E'} (hH : H.IsTree)
    (C : Set E') : ¬ IsCycle H C := by
  rintro ⟨k, v, e, hc, rfl⟩
  exact hH.2 (e ⟨0, hc.pos⟩) (walks_compl_of_mem_isCycle ⟨k, v, e, hc, rfl⟩ ⟨_, rfl⟩)

/-- A walk of the network is a walk of the network with its 2- and 3-cycles contracted, on its
edges off those cycles. -/
theorem tildeContracted_walks_of_walks {F : Set E} {a b : V} (h : G.graph.Walks F a b) :
    (tildeContracted G).graph.Walks {e | e.1 ∈ F} (Quot.mk _ a) (Quot.mk _ b) := by
  induction h with
  | refl => exact .refl
  | @tail c d _ hst ih =>
    obtain ⟨f, hf, hj⟩ := hst
    by_cases hc : ∃ C, IsCycle G.graph C ∧ C.ncard ≤ 3 ∧ f ∈ C
    · obtain ⟨C, hC, h3, hfC⟩ := hc
      have : (Quot.mk _ c : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) = Quot.mk _ d := by
        apply Quot.sound
        refine ⟨C, hC, h3, ?_, ?_⟩
        · rcases hj with ⟨h₁, -⟩ | ⟨-, h₂⟩
          exacts [⟨f, hfC, Or.inl h₁⟩, ⟨f, hfC, Or.inr h₂⟩]
        · rcases hj with ⟨-, h₂⟩ | ⟨h₁, -⟩
          exacts [⟨f, hfC, Or.inr h₂⟩, ⟨f, hfC, Or.inl h₁⟩]
      rw [← this]
      exact ih
    · push Not at hc
      refine ih.tail ⟨⟨f, fun C hC h3 => hc C hC h3⟩, hf, ?_⟩
      rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg _ h₁, congrArg _ h₂⟩
      · exact Or.inr ⟨congrArg _ h₁, congrArg _ h₂⟩

/-- **A walk of `Ñ` avoiding an edge is a walk of the network avoiding an edge of its chain** that
lies on no cycle. -/
theorem walks_compl_of_tildeNetwork_walks [Finite E]
    {c : {c // IsChain (tildeContracted G) ∅ c}} {g} (hg : g ∈ c.1)
    (hgc : ∀ C, IsCycle G.graph C → g.1 ∉ C)
    {x y : {q // IsBranch (tildeContracted G) ∅ q}} {a b : V} (hx : x.1 = Quot.mk _ a)
    (hy : y.1 = Quot.mk _ b) (h : (tildeNetwork G).graph.Walks {c}ᶜ x y) :
    G.graph.Walks {g.1}ᶜ a b := by
  have hK : (tildeContracted G).graph.Walks c.1ᶜ x.1 y.1 :=
    suppressExcept_walks_val (K := tildeContracted G) (P := ∅) (S := c.1ᶜ)
      (fun c' (hc' : c' ∈ ({c}ᶜ : Set _)) f hf hfc =>
        hc' (Set.mem_singleton_iff.2 (Subtype.ext (c'.2.eq_of_mem c.2 hf hfc)))) h
  rw [hx, hy] at hK
  refine walks_mono ?_ (walks_of_contract_walks (P := fun C => C.ncard ≤ 3) hK)
  rintro _ (⟨g', hg', rfl⟩ | ⟨C, hC, hgC⟩) h'
  · exact hg' (by rw [Subtype.ext (Set.mem_singleton_iff.1 h')]; exact hg)
  · exact hgc C hC (Set.mem_singleton_iff.1 h' ▸ hgC)

/-- An edge of `Ñ` whose chain has an edge on no cycle of the network lies on no cycle of `Ñ`. -/
theorem forall_notMem_tilde_of_mem [Finite E] {c : {c // IsChain (tildeContracted G) ∅ c}} {g}
    (hg : g ∈ c.1) (hgc : ∀ C, IsCycle G.graph C → g.1 ∉ C) :
    ∀ C', IsCycle (tildeNetwork G).graph C' → c ∉ C' := by
  intro C' hC' hcC'
  obtain ⟨C₀, hC₀, hgC₀⟩ := exists_isCycle_of_suppressExcept_walks (K := tildeContracted G)
    (P := ∅) c (walks_compl_of_mem_isCycle hC' hcC') hg
  obtain ⟨D, hD, hgD⟩ :=
    exists_mem_cycle_of_tildeContracted_walks (walks_compl_of_mem_isCycle hC₀ hgC₀)
  exact hgc D hD hgD

variable [Finite V] [Finite E] (hG : IsUnrootedLevelOne G)
include hG

omit [Finite V] in
/-- `Ñ` has no loops. -/
theorem tildeNetwork_loopless (c : {c // IsChain (tildeContracted G) ∅ c}) :
    (tildeNetwork G).graph.source c ≠ (tildeNetwork G).graph.target c :=
  suppress_source_ne_target (tildeContracted_loopless hG) (tildeContracted_bridge hG) c

/-- **`Ñ` is connected.** -/
theorem tildeNetwork_isConnected : (tildeNetwork G).graph.IsConnected := by
  intro x y
  obtain ⟨a, ha⟩ := Quot.exists_rep x.1
  obtain ⟨b, hb⟩ := Quot.exists_rep y.1
  have h := tildeContracted_walks_of_walks (G := G) (hG.connected a b)
  rw [ha, hb] at h
  exact walks_mono (Set.subset_univ _) (suppressExcept_walks_of_walks (K := tildeContracted G)
    (P := ∅) (exists_isChain_tildeContracted hG) (u := x) (w := y) h)

omit [Finite V] hG in
/-- **The cycles of `Ñ` come from the cycles of size at least four**: a node of `Ñ` on a cycle is
the class of a node of a cycle of size at least four. An edge of the chain of an edge of the cycle
at the node lies on a cycle of the contracted network, so on a cycle of the network, which is not
contracted. -/
theorem exists_isCycle_big_of_mem_cycleNodes_tilde
    {C : Set {c // IsChain (tildeContracted G) ∅ c}} (hC : IsCycle (tildeNetwork G).graph C) {w}
    (hw : w ∈ cycleNodes (tildeNetwork G).graph C) :
    ∃ D u, IsCycle G.graph D ∧ 4 ≤ D.ncard ∧ u ∈ cycleNodes G.graph D ∧ w.1 = Quot.mk _ u := by
  obtain ⟨c, hc, hcw⟩ := hw
  obtain ⟨g, hg, hgw⟩ := exists_mem_incident_of_tildeNetwork hcw
  obtain ⟨C₀, hC₀, hgC₀⟩ := exists_isCycle_of_suppressExcept_walks (K := tildeContracted G)
    (P := ∅) c (walks_compl_of_mem_isCycle hC hc) hg
  obtain ⟨D, hD, hgD⟩ :=
    exists_mem_cycle_of_tildeContracted_walks (walks_compl_of_mem_isCycle hC₀ hgC₀)
  have h4 : 4 ≤ D.ncard := by
    by_contra h
    exact g.2 D hD (by omega) hgD
  rcases hgw with h | h
  · exact ⟨D, G.graph.source g.1, hD, h4, ⟨g.1, hgD, Or.inl rfl⟩, h.symm⟩
  · exact ⟨D, G.graph.target g.1, hD, h4, ⟨g.1, hgD, Or.inr rfl⟩, h.symm⟩

omit [Finite V] in
/-- **At a node of a cycle, the edge off the cycle is unique**: the node has degree three, two of
its edges being on the cycle. -/
theorem IsUnrootedLevelOne.eq_of_notMem_of_incident {C : Set E} (hC : IsCycle G.graph C) {u : V}
    (hu : u ∈ cycleNodes G.graph C) {f f' : E} (hf : G.graph.source f = u ∨ G.graph.target f = u)
    (hfC : f ∉ C) (hf' : G.graph.source f' = u ∨ G.graph.target f' = u) (hf'C : f' ∉ C) :
    f = f' := by
  have h2 := hC.ncard_incident hG.loopless hu
  have hd := degree_eq_ncard_incident hG.loopless u
  rw [hG.degree_of_mem hC hu] at hd
  by_contra hne
  obtain ⟨c₁, c₂, hc, hcs⟩ := Set.ncard_eq_two.1 h2
  have hc₁ : c₁ ∈ {e | e ∈ C ∧ (G.graph.source e = u ∨ G.graph.target e = u)} := by
    rw [hcs]; exact Or.inl rfl
  have hc₂ : c₂ ∈ {e | e ∈ C ∧ (G.graph.source e = u ∨ G.graph.target e = u)} := by
    rw [hcs]; exact Or.inr rfl
  have h4 : ({f, f', c₁, c₂} : Set E).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hc]
    · rintro (h | h)
      · exact hf'C (h ▸ hc₁.1)
      · exact hf'C (h ▸ hc₂.1)
    · rintro (h | h | h)
      · exact hne h
      · exact hfC (h ▸ hc₁.1)
      · exact hfC (h ▸ hc₂.1)
  have hsub : ({f, f', c₁, c₂} : Set E) ⊆ {e | G.graph.source e = u ∨ G.graph.target e = u} := by
    rintro e (rfl | rfl | rfl | rfl)
    exacts [hf, hf', hc₁.2, hc₂.2]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

omit [Finite V] in
/-- The block of a node of a cycle holds a taxon: the far side of the edge off the cycle does. -/
theorem IsUnrootedLevelOne.nodeBlock_nonempty_of_mem {D : Set E} (hD : IsCycle G.graph D) {d : V}
    (hd : d ∈ cycleNodes G.graph D) : (nodeBlock G.graph G.leaf D d).Nonempty := by
  obtain ⟨f, hfd, hfD, hf⟩ := hG.exists_offCycle hD hd
  obtain ⟨v, hj⟩ := exists_joins_of_incident hfd
  obtain ⟨x, hx⟩ := hG.exists_leaf_side f hf v hj.incident_right
  exact ⟨x, (hG.mem_nodeBlock_iff hD hd hfD hj x).2 hx⟩

/-- **The tree of cycles of `Ñ` is a tree.** -/
theorem treeOfCycles_tilde_isTree : (treeOfCycles (tildeNetwork G)).graph.IsTree :=
  treeOfCycles_isTree (tildeNetwork_loopless hG) (tildeNetwork_isConnected hG)

/-- **Every leaf of the tree of cycles of `Ñ` arises from a cycle of size at least four**: a node of
the suppressed core on no cycle of `Ñ` is not a leaf (`not_isLeafNode_mk_of_notMem`), and the cycles
of `Ñ` come from the cycles of size at least four (`exists_isCycle_big_of_mem_cycleNodes_tilde`). -/
theorem exists_arisesFrom_of_isLeafNode
    {w : Quot (ContractRel (coreSuppressed (tildeNetwork G)).graph fun _ => True)}
    (hw : IsLeafNode (treeOfCycles (tildeNetwork G)).graph w) :
    ∃ C, IsCycle G.graph C ∧ 4 ≤ C.ncard ∧ ArisesFrom G w C := by
  induction w using Quot.ind with
  | mk s =>
  by_cases hs : s.1 ∈ coreCycleNodes (tildeNetwork G)
  · obtain ⟨C₁, hC₁, hsC₁⟩ := hs
    obtain ⟨D, u, hD, h4, hu, hsu⟩ := exists_isCycle_big_of_mem_cycleNodes_tilde hC₁ hsC₁
    exact ⟨D, hD, h4, u, hu, s, hsu, rfl⟩
  · exact absurd hw (not_isLeafNode_mk_of_notMem (tildeNetwork_loopless hG)
      (tildeNetwork_isConnected hG) s hs)

variable {C : Set E} (hC : IsCycle G.graph C) (h4 : 4 ≤ C.ncard)
include hC h4

omit [Finite V] [Finite E] in
/-- A node of a cycle of size at least four is on no 2- or 3-cycle. -/
theorem notMem_small_of_big {u : V} (hu : u ∈ cycleNodes G.graph C) :
    ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → u ∉ cycleNodes G.graph C' := fun C' hC' h3 hu' => by
  have := hG.cycle_eq C C' hC hC' ⟨u, hu, hu'⟩
  subst this
  omega

omit [Finite V] in
/-- The class of a node of a cycle of size at least four is kept by suppression: it has degree
three. -/
theorem isBranch_mk_of_big {u : V} (hu : u ∈ cycleNodes G.graph C) :
    IsBranch (tildeContracted G) ∅ (Quot.mk _ u) := by
  rw [isBranch_tildeContracted_iff hG, degree_tildeContracted_of_notMem hG
    (notMem_small_of_big hG hC h4 hu), hG.degree_of_mem hC hu]
  omega

omit [Finite V] [Finite E] in
/-- The nodes of a cycle of size at least four have distinct classes. -/
theorem eq_of_mk_eq_of_big {u u' : V} (hu : u ∈ cycleNodes G.graph C)
    (h : (Quot.mk _ u : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) = Quot.mk _ u') :
    u = u' := by
  rcases (tildeContracted_mk_eq_iff hG).1 h with h | ⟨C', hC', h3, hu₁, -⟩
  · exact h
  · exact absurd hu₁ (notMem_small_of_big hG hC h4 hu C' hC' h3)

omit [Finite V] in
/-- **A cycle of size at least four gives a cycle of `Ñ` and a cycle of the suppressed core of `Ñ`**
through the nodes coming from its nodes, each of its edges being in the chain of an edge of the
latter: its edges are edges of the contracted network between nodes of degree three, so chains of
one edge of `Ñ`, which are in the pendant core, and chains of one edge of the suppressed core. -/
theorem exists_isCycle_tilde_of_big :
    ∃ C₁, IsCycle (tildeNetwork G).graph C₁ ∧
      ∃ C₂, IsCycle (coreSuppressed (tildeNetwork G)).graph C₂ ∧
      (∀ u ∈ cycleNodes G.graph C,
        (∃ w ∈ cycleNodes (tildeNetwork G).graph C₁, w.1 = Quot.mk _ u) ∧
        ∃ s ∈ cycleNodes (coreSuppressed (tildeNetwork G)).graph C₂, s.1.1.1 = Quot.mk _ u) ∧
      ∀ e ∈ C, ∃ d ∈ C₂, ∃ ρ ∈ d.1, ∃ g ∈ ρ.1.1, g.1 = e := by
  have hC' := hC
  obtain ⟨k, v, e, hc, rfl⟩ := hC'
  have hv : ∀ i, v i ∈ cycleNodes G.graph (Set.range e) := fun i => by
    rw [hc.cycleNodes_eq]
    exact ⟨i, rfl⟩
  have he : ∀ i, ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e i ∉ C' := fun i C' hC' h3 hei =>
    notMem_small_of_big hG hC h4 (source_mem_cycleNodes ⟨i, rfl⟩) C' hC' h3
      (source_mem_cycleNodes hei)
  have hc₀ : IsCycleOf (tildeContracted G).graph k (fun i => Quot.mk _ (v i))
      (fun i => ⟨e i, he i⟩) :=
    ⟨hc.pos, fun i => (hc.joins i).imp (fun h => ⟨congrArg _ h.1, congrArg _ h.2⟩)
      (fun h => ⟨congrArg _ h.1, congrArg _ h.2⟩),
      fun i j h => hc.injective_node (eq_of_mk_eq_of_big hG hC h4 (hv i) h),
      fun i j h => hc.injective_edge (congrArg Subtype.val h)⟩
  obtain ⟨nT, eT, hc₁, hnT, heT⟩ : ∃ (nT : Fin k → {q // IsBranch (tildeContracted G) ∅ q})
      (eT : Fin k → {c // IsChain (tildeContracted G) ∅ c}),
      IsCycleOf (tildeNetwork G).graph k nT eT ∧ (∀ i, (nT i).1 = Quot.mk _ (v i)) ∧
        ∀ i, ∃ g ∈ (eT i).1, g.1 = e i :=
    ⟨_, _, isCycleOf_suppressExcept hc₀ (fun i => tildeContracted_loopless hG _)
      (fun i => isBranch_mk_of_big hG hC h4 (hv i)), fun i => rfl,
      fun i => ⟨⟨e i, he i⟩, Set.mem_singleton _, rfl⟩⟩
  have hC₁ : IsCycle (tildeNetwork G).graph (Set.range eT) := ⟨k, nT, eT, hc₁, rfl⟩
  have hcore : ∀ i, eT i ∈ pendantCore (tildeNetwork G).graph := fun i =>
    mem_pendantCore_of_sides (tildeNetwork_loopless hG) (Or.inl ⟨_, hC₁, ⟨i, rfl⟩⟩)
  have hc₂ := isCycleOf_restrict (Z := ∅) hc₁ hcore
  obtain ⟨sT, dT, hc₃, hsT, hdT⟩ : ∃ (sT : Fin k → {u // IsBranch (coreNet (tildeNetwork G))
      (coreCycleNodes (tildeNetwork G)) u})
      (dT : Fin k → {c // IsChain (coreNet (tildeNetwork G)) (coreCycleNodes (tildeNetwork G)) c}),
      IsCycleOf (coreSuppressed (tildeNetwork G)).graph k sT dT ∧ (∀ i, (sT i).1.1 = nT i) ∧
        ∀ i, ∃ ρ ∈ (dT i).1, ρ.1 = eT i :=
    ⟨_, _, isCycleOf_suppressExcept (K := coreNet (tildeNetwork G))
      (P := coreCycleNodes (tildeNetwork G)) hc₂ (fun i => restrict_source_ne_target
      (tildeNetwork_loopless hG) _) (fun i => Or.inr (Or.inr ⟨_, hC₁, hc₁.mem_cycleNodes i⟩)),
      fun i => rfl, fun i => ⟨⟨eT i, hcore i⟩, Set.mem_singleton _, rfl⟩⟩
  refine ⟨_, hC₁, _, ⟨k, sT, dT, hc₃, rfl⟩, fun u hu => ?_, fun e' he' => ?_⟩
  · rw [hc.cycleNodes_eq] at hu
    obtain ⟨i, rfl⟩ := hu
    exact ⟨⟨nT i, hc₁.mem_cycleNodes i, hnT i⟩, ⟨sT i, hc₃.mem_cycleNodes i, by rw [hsT i, hnT i]⟩⟩
  · obtain ⟨i, rfl⟩ := he'
    obtain ⟨ρ, hρ, hρe⟩ := hdT i
    obtain ⟨g, hg, hge⟩ := heT i
    exact ⟨dT i, ⟨i, rfl⟩, ρ, hρ, g, hρe ▸ hg, hge⟩

omit [Finite V] in
/-- **The nodes coming from a cycle of size at least four are in one class of the tree of cycles**:
they lie on one cycle of the suppressed core of `Ñ` (`exists_isCycle_tilde_of_big`). -/
theorem treeOfCycles_mk_eq_of_big {u u' : V} (hu : u ∈ cycleNodes G.graph C)
    (hu' : u' ∈ cycleNodes G.graph C)
    {s s' : {x // IsBranch (coreNet (tildeNetwork G)) (coreCycleNodes (tildeNetwork G)) x}}
    (hs : s.1.1.1 = Quot.mk _ u) (hs' : s'.1.1.1 = Quot.mk _ u') :
    (Quot.mk _ s : Quot (ContractRel (coreSuppressed (tildeNetwork G)).graph fun _ => True)) =
      Quot.mk _ s' := by
  obtain ⟨_, _, C₂, hC₂, hall, -⟩ := exists_isCycle_tilde_of_big hG hC h4
  obtain ⟨-, s₀, hs₀, hs₀u⟩ := hall u hu
  obtain ⟨-, s₀', hs₀', hs₀u'⟩ := hall u' hu'
  have e₁ : s = s₀ := Subtype.ext (Subtype.ext (Subtype.ext (hs.trans hs₀u.symm)))
  have e₂ : s' = s₀' := Subtype.ext (Subtype.ext (Subtype.ext (hs'.trans hs₀u'.symm)))
  subst e₁ e₂
  exact Quot.sound ⟨C₂, hC₂, trivial, hs₀, hs₀'⟩

omit [Finite V] h4 in
/-- **A block that is not a 4-network block holds a cycle of size at least four** on the far side of
the edge `f` off `C` at `u`: two of its taxa are in different blocks of such a cycle `C'` (Lemma 4);
they are on the far side of `f`, and if a node of `C'` were on the side of `u`, all of `C'` would
be, and the far side would join the two taxa avoiding `C'`. -/
theorem exists_big_notMem_side {u : V} (hu : u ∈ cycleNodes G.graph C) {f : E}
    (hfu : G.graph.source f = u ∨ G.graph.target f = u) (hfC : f ∉ C)
    (hf : ∀ C', IsCycle G.graph C' → f ∉ C') (hnb : ¬ IsFourNetworkBlock G C u) :
    ∃ C', IsCycle G.graph C' ∧ 4 ≤ C'.ncard ∧
      ∃ z ∈ cycleNodes G.graph C', ¬ G.graph.Walks {f}ᶜ u z := by
  have h1 : IsLevelOne G.graph := fun C₁ C₂ h₁ h₂ ⟨g, hg₁, hg₂⟩ =>
    hG.cycle_eq C₁ C₂ h₁ h₂ ⟨_, ⟨g, hg₁, Or.inl rfl⟩, ⟨g, hg₂, Or.inl rfl⟩⟩
  unfold IsFourNetworkBlock at hnb
  push Not at hnb
  obtain ⟨x, hx, y, hy, hxy⟩ := hnb
  obtain ⟨C', ⟨hC', h4'⟩, hnC'⟩ := lemma4 G.leaf hG.connected h1
    (fun C (hC : C ∈ cyclesOfSizeAtLeast G.graph 4) => hC.1) hxy
  refine ⟨C', hC', h4', ?_⟩
  by_contra hall
  push Not at hall
  obtain ⟨v, hj⟩ := exists_joins_of_incident hfu
  have hnv := not_walks_of_joins hf hj
  have hside : ∀ t ∈ nodeBlock G.graph G.leaf C u, G.graph.Walks C'ᶜ v (G.leaf t) := by
    intro t ht
    refine walks_mono_of_reach ((hG.mem_nodeBlock_iff hC hu hfC hj t).1 ht)
      fun y' hy' g _ hgy' hgC' => ?_
    exact hnv ((hall y' ⟨g, hgC', hgy'⟩).trans (G.graph.walks_symm hy'))
  exact hnC' ((G.graph.walks_symm (hside x hx)).trans (hside y hy))

/-- **The edge of `Ñ` off a cycle of size at least four at the node `nu` of `u`**: the chain of the
edge `f` at `u` off the cycle. It is an edge of `Ñ` at `nu`, on no cycle of `Ñ`, and in the pendant
core when the block of `u` is not a 4-network block: then its side of `nu` holds `nu`, a node of a
cycle of `Ñ`, and its other side a node of a cycle of `Ñ` coming from a cycle of size at least four
on the far side of `f` (`exists_big_notMem_side`). -/
theorem exists_tilde_offCycle {u : V} (hu : u ∈ cycleNodes G.graph C)
    {nu : {q // IsBranch (tildeContracted G) ∅ q}} (hnu : nu.1 = Quot.mk _ u) :
    ∃ c : {c // IsChain (tildeContracted G) ∅ c},
      ((tildeNetwork G).graph.source c = nu ∨ (tildeNetwork G).graph.target c = nu) ∧
      (∀ C', IsCycle (tildeNetwork G).graph C' → c ∉ C') ∧
      (¬ IsFourNetworkBlock G C u → c ∈ pendantCore (tildeNetwork G).graph) := by
  obtain ⟨f, hfu, hfC, hf⟩ := hG.exists_offCycle hC hu
  have hfs : ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → f ∉ C' := fun C' hC' _ => hf C' hC'
  obtain ⟨c, hc, hfc⟩ := exists_isChain_tildeContracted hG ⟨f, hfs⟩
  have hinc : (tildeNetwork G).graph.source ⟨c, hc⟩ = nu ∨
      (tildeNetwork G).graph.target ⟨c, hc⟩ = nu :=
    suppressExcept_incident_of_mem (K := tildeContracted G) (P := ∅) ⟨c, hc⟩ hfc nu.2
      (hfu.imp (fun h => (congrArg (Quot.mk _) h).trans hnu.symm)
        (fun h => (congrArg (Quot.mk _) h).trans hnu.symm))
  have hnc : ∀ C', IsCycle (tildeNetwork G).graph C' → ⟨c, hc⟩ ∉ C' :=
    forall_notMem_tilde_of_mem (c := ⟨c, hc⟩) hfc hf
  refine ⟨⟨c, hc⟩, hinc, hnc, fun hnb => ?_⟩
  obtain ⟨C', hC', h4', z, hz, hnz⟩ := exists_big_notMem_side hG hC hu hfu hfC hf hnb
  obtain ⟨C₁, hC₁, _, _, hall, -⟩ := exists_isCycle_tilde_of_big hG hC h4
  obtain ⟨C₁', hC₁', _, _, hall', -⟩ := exists_isCycle_tilde_of_big hG hC' h4'
  obtain ⟨⟨wu, hwu, hwuu⟩, -⟩ := hall u hu
  obtain ⟨⟨wz, hwz, hwzz⟩, -⟩ := hall' z hz
  have hnuC : nu ∈ cycleNodes (tildeNetwork G).graph C₁ := by
    rwa [show wu = nu from Subtype.ext (hwuu.trans hnu.symm)] at hwu
  have hlift : ¬ (tildeNetwork G).graph.Walks {⟨c, hc⟩}ᶜ nu wz := fun h =>
    hnz (walks_compl_of_tildeNetwork_walks hfc hf hnu hwzz h)
  refine mem_pendantCore_of_sides (tildeNetwork_loopless hG) (Or.inr fun a ha => ?_)
  rcases walks_compl_or_of_isConnected (tildeNetwork_isConnected hG) ⟨c, hc⟩ wz with hs | ht
  · have htgt := hinc.resolve_left fun h => hlift (h ▸ hs)
    rcases ha with rfl | rfl
    · exact ⟨C₁', wz, hC₁', hwz, hs⟩
    · exact ⟨C₁, nu, hC₁, hnuC, htgt ▸ .refl⟩
  · have hsrc := hinc.resolve_right fun h => hlift (h ▸ ht)
    rcases ha with rfl | rfl
    · exact ⟨C₁, nu, hC₁, hnuC, hsrc ▸ .refl⟩
    · exact ⟨C₁', wz, hC₁', hwz, ht⟩

omit [Finite V] h4 in
/-- **The class in the tree of cycles of the nodes coming from a cycle of size at least four holds
no other node**: nodes in one class are joined along cycles of the suppressed core, whose edges
come from edges of cycles of the network, and a walk along cycles from a node of the cycle stays on
it. -/
theorem exists_mem_of_mk_eq_of_big {u₀ : V} (hu₀ : u₀ ∈ cycleNodes G.graph C)
    {s₀ s : {x // IsBranch (coreNet (tildeNetwork G)) (coreCycleNodes (tildeNetwork G)) x}}
    (hs₀ : s₀.1.1.1 = Quot.mk _ u₀)
    (h : (Quot.mk _ s : Quot (ContractRel (coreSuppressed (tildeNetwork G)).graph fun _ => True)) =
      Quot.mk _ s₀) :
    ∃ u ∈ cycleNodes G.graph C, s.1.1.1 = Quot.mk _ u := by
  have h₁ :=
    walks_of_contract_eq (G := coreSuppressed (tildeNetwork G)) (P := fun _ => True) h.symm
  have h₂ := restrict_walks_cycleEdges (suppressExcept_walks_cycleEdges h₁)
  have h₃ := suppressExcept_walks_cycleEdges (K := tildeContracted G) (P := ∅) h₂
  obtain ⟨a, ha⟩ := Quot.exists_rep s.1.1.1
  rw [hs₀, ← ha] at h₃
  have h₄ := walks_of_contract_walks (P := fun C => C.ncard ≤ 3) h₃
  refine ⟨a, mem_cycleNodes_of_walks_cycleEdges hG.cycle_eq hC hu₀ (walks_mono ?_ h₄), ha.symm⟩
  rintro _ (⟨g, ⟨C', hC', hgC'⟩, rfl⟩ | hcyc)
  · exact exists_mem_cycle_of_tildeContracted_walks (walks_compl_of_mem_isCycle hC' hgC')
  · exact hcyc

omit [Finite V] h4 in
/-- **A block with a cycle of size at least four on the far side is not a 4-network block**: the
nodes of that cycle `D` but the one toward `u` have their blocks of `D` on the far side of the edge
`f` off `C` at `u`, so in the block of `u`, and two of them give taxa of the block of `u` in
different blocks of `D`. -/
theorem not_fourNetworkBlock_of_side {u : V} (hu : u ∈ cycleNodes G.graph C) {f : E} {v : V}
    (hj : Joins G.graph f u v) (hfC : f ∉ C) (hf : ∀ C', IsCycle G.graph C' → f ∉ C')
    {D : Set E} (hD : IsCycle G.graph D) (h4D : 4 ≤ D.ncard) {z : V}
    (hz : z ∈ cycleNodes G.graph D) (hvz : G.graph.Walks {f}ᶜ v z) :
    ¬ IsFourNetworkBlock G C u := by
  intro hblock
  have h1 : IsLevelOne G.graph := fun C₁ C₂ h₁ h₂ ⟨g, hg₁, hg₂⟩ =>
    hG.cycle_eq C₁ C₂ h₁ h₂ ⟨_, ⟨g, hg₁, Or.inl rfl⟩, ⟨g, hg₂, Or.inl rfl⟩⟩
  -- the nodes of `D` are on the far side of `f`
  have hfar : ∀ d ∈ cycleNodes G.graph D, G.graph.Walks {f}ᶜ v d := fun d hd =>
    hvz.trans (walks_mono (F' := ({f}ᶜ : Set E))
      (fun g (hg : g ∈ D) (hgf : g ∈ ({f} : Set E)) => hf D hD (Set.mem_singleton_iff.1 hgf ▸ hg))
      (walks_cycle_of_mem_cycleNodes G.graph hD hz hd))
  obtain ⟨d₀, hd₀, hd₀u⟩ := exists_walks_compl_of_isConnected hG.connected hD u
  -- the blocks of `D` of its nodes other than `d₀` are in the block of `u`
  have hin : ∀ d ∈ cycleNodes G.graph D, d ≠ d₀ → ∀ t ∈ nodeBlock G.graph G.leaf D d,
      t ∈ nodeBlock G.graph G.leaf C u := by
    intro d hd hne t ht
    refine (hG.mem_nodeBlock_iff hC hu hfC hj t).2 ?_
    have hdu : ¬ G.graph.Walks Dᶜ d u := fun h =>
      hne (h1.eq_of_walks_compl hD hd hd₀ (h.trans (G.graph.walks_symm hd₀u)))
    rcases walks_inter_compl_or_exists_cycleNodes (C := {f}) ht with h | ⟨c, ⟨g, hg, hgc⟩, hdc⟩
    · exact (hfar d hd).trans (walks_mono (fun g (hg : g ∈ Dᶜ ∩ {f}ᶜ) => hg.2) h)
    · rw [Set.mem_singleton_iff] at hg
      rw [hg] at hgc
      rcases Joins.eq_or_eq hj hgc with rfl | rfl
      · exact absurd (walks_mono (fun g (hg : g ∈ Dᶜ ∩ {f}ᶜ) => hg.1) hdc) hdu
      · exact absurd ((walks_mono (fun g (hg : g ∈ Dᶜ ∩ {f}ᶜ) => hg.1) hdc).tail
          ⟨f, hf D hD, Or.symm hj⟩) hdu
  obtain ⟨d₁, hd₁, hd₁'⟩ := hD.exists_mem_cycleNodes_notMem (Set.toFinite {d₀})
    (by rw [Set.ncard_singleton]; omega)
  obtain ⟨d₂, hd₂, hd₂'⟩ := hD.exists_mem_cycleNodes_notMem (Set.toFinite {d₀, d₁})
    (lt_of_le_of_lt ((Set.ncard_insert_le d₀ {d₁}).trans (by rw [Set.ncard_singleton]))
      (by omega))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hd₁' hd₂'
  obtain ⟨t₁, ht₁⟩ := hG.nodeBlock_nonempty_of_mem hD hd₁
  obtain ⟨t₂, ht₂⟩ := hG.nodeBlock_nonempty_of_mem hD hd₂
  have hab : G.graph.Walks Dᶜ (G.leaf t₁) (G.leaf t₂) :=
    walks_mono (Set.compl_subset_compl.2 (Set.subset_sUnion_of_mem
      (show D ∈ cyclesOfSizeAtLeast G.graph 4 from ⟨hD, h4D⟩)))
      (hblock t₁ (hin d₁ hd₁ hd₁' t₁ ht₁) t₂ (hin d₂ hd₂ hd₂'.1 t₂ ht₂))
  exact hd₂'.2 (h1.eq_of_walks_compl hD hd₂ hd₁
    (ht₂.trans ((G.graph.walks_symm hab).trans (G.graph.walks_symm ht₁))))

omit h4 in
/-- **An edge of `Ñ` in the pendant core through the edge `f` off a cycle at `u` makes the block of
`u` not a 4-network block**: the far side of the edge in `Ñ` holds a node of a cycle of `Ñ`
(`exists_cycle_side_of_mem_pendantCore`), which comes from a cycle of size at least four
(`exists_isCycle_big_of_mem_cycleNodes_tilde`) on the far side of `f` (`tilde_cut`). -/
theorem not_fourNetworkBlock_of_mem_pendantCore {u : V} (hu : u ∈ cycleNodes G.graph C) {f : E}
    (hfu : G.graph.source f = u ∨ G.graph.target f = u) (hfC : f ∉ C)
    (hf : ∀ C', IsCycle G.graph C' → f ∉ C') {c : {c // IsChain (tildeContracted G) ∅ c}} {g}
    (hg : g ∈ c.1) (hgf : g.1 = f) (hc : c ∈ pendantCore (tildeNetwork G).graph) :
    ¬ IsFourNetworkBlock G C u := by
  obtain ⟨v, hj⟩ := exists_joins_of_incident hfu
  obtain ⟨ε, a, b, ⟨g₀, hg₀, hg₀f⟩, -, hb, hjε, -, hcross, hcompl, -⟩ := tilde_cut hG hf hj
  have hεc : ε = c := Subtype.ext (ε.2.eq_of_mem c.2 hg₀
    (by rwa [show g₀ = g from Subtype.ext (hg₀f.trans hgf.symm)]))
  subst hεc
  obtain ⟨C₁, z₁, hC₁, hz₁, hbz⟩ := exists_cycle_side_of_mem_pendantCore
    (tildeNetwork_loopless hG) hc (forall_notMem_tilde_of_mem hg (hgf ▸ hf)) hjε
  have hz₁v : z₁ ∈ tildeCutSide G f v := by
    refine (hcompl z₁).2 fun hz₁u => (hcompl b).1 hb ?_
    refine ((tildeNetwork G).graph.mem_iff_mem_of_walks (fun e he hcr => ?_) hbz).2 hz₁u
    rcases hcr with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact h₂ ((hcross e he).1 h₁)
    · exact h₂ ((hcross e he).2 h₁)
  obtain ⟨x, hx, hxz⟩ := hz₁v
  obtain ⟨D, z, hD, h4D, hz, hz₁z⟩ := exists_isCycle_big_of_mem_cycleNodes_tilde hC₁ hz₁
  obtain rfl : z = x := eq_of_mk_eq_of_big hG hD h4D hz (hz₁z.symm.trans hxz)
  exact not_fourNetworkBlock_of_side hG hC hu hj hfC hf hD h4D hz hx

/-- **A leaf arising from a cycle of size at least four has all its blocks but one 4-network
blocks** (proof of Theorem 4): two blocks that are not 4-network blocks give, at two nodes of the
cycle, two edges of `Ñ` off the cycle in the pendant core (`exists_tilde_offCycle`), so two
distinct edges of the tree of cycles at the class of the cycle (`not_isLeafNode_mk_of_two`). -/
theorem fourNetworkBlocks_of_isLeafNode
    {w : Quot (ContractRel (coreSuppressed (tildeNetwork G)).graph fun _ => True)}
    (hw : ArisesFrom G w C) (hleaf : IsLeafNode (treeOfCycles (tildeNetwork G)).graph w) :
    ∃ u ∈ cycleNodes G.graph C, ∀ u' ∈ cycleNodes G.graph C, u' ≠ u →
      IsFourNetworkBlock G C u' := by
  by_cases hex : ∃ u₁ ∈ cycleNodes G.graph C, ¬ IsFourNetworkBlock G C u₁
  · obtain ⟨u₁, hu₁, hb₁⟩ := hex
    refine ⟨u₁, hu₁, fun u₂ hu₂ hne => by_contra fun hb₂ => ?_⟩
    obtain ⟨u₀, hu₀, s₀, hs₀, rfl⟩ := hw
    obtain ⟨_, _, C₂, -, hall, -⟩ := exists_isCycle_tilde_of_big hG hC h4
    obtain ⟨-, s₁, -, hs₁⟩ := hall u₁ hu₁
    obtain ⟨-, s₂, -, hs₂⟩ := hall u₂ hu₂
    have hloop := tildeNetwork_loopless hG
    have key : ∀ (u : V) (s : {x // IsBranch (coreNet (tildeNetwork G))
        (coreCycleNodes (tildeNetwork G)) x}), u ∈ cycleNodes G.graph C →
        s.1.1.1 = Quot.mk _ u → ¬ IsFourNetworkBlock G C u →
        ∃ d : {c // IsChain (coreNet (tildeNetwork G)) (coreCycleNodes (tildeNetwork G)) c},
          (∀ C', IsCycle (coreSuppressed (tildeNetwork G)).graph C' → True → d ∉ C') ∧
          ((coreSuppressed (tildeNetwork G)).graph.source d = s ∨
            (coreSuppressed (tildeNetwork G)).graph.target d = s) := by
      intro u s hu hs hb
      obtain ⟨c, hinc, hnc, hcore⟩ := exists_tilde_offCycle hG hC h4 hu hs
      obtain ⟨d, hd, hcd⟩ := exists_isChain_coreNet hloop ⟨c, hcore hb⟩
      exact ⟨⟨d, hd⟩, forall_notMem_of_coreSuppressed ⟨d, hd⟩ hcd hnc,
        suppressExcept_incident_of_mem ⟨d, hd⟩ hcd s.2
          (hinc.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h))⟩
    obtain ⟨d₁, hn₁, hi₁⟩ := key u₁ s₁ hu₁ hs₁ hb₁
    obtain ⟨d₂, hn₂, hi₂⟩ := key u₂ s₂ hu₂ hs₂ hb₂
    have hs₁₂ : s₁ ≠ s₂ := fun h =>
      hne (eq_of_mk_eq_of_big hG hC h4 hu₁ (hs₁.symm.trans (h ▸ hs₂))).symm
    refine not_isLeafNode_mk_of_two hloop (tildeNetwork_isConnected hG) hs₁₂
      (treeOfCycles_mk_eq_of_big hG hC h4 hu₁ hu₂ hs₁ hs₂) hn₁ hn₂ hi₁ hi₂ ?_
    rwa [treeOfCycles_mk_eq_of_big hG hC h4 hu₀ hu₁ hs₀ hs₁] at hleaf
  · push Not at hex
    obtain ⟨u₀, hu₀⟩ := hC.cycleNodes_nonempty
    exact ⟨u₀, hu₀, fun u' hu' _ => hex u' hu'⟩

/-- **A node arising from a cycle of size at least four all of whose blocks but one are 4-network
blocks is a leaf of the tree of cycles**: an edge of the tree at the class of the cycle is a chain
of the suppressed core with an edge of `Ñ` at a node coming from the cycle
(`exists_mem_of_mk_eq_of_big`, `suppressExcept_exists_mem_incident`). That edge of `Ñ` is not an
edge of the cycle, whose chain lies on a cycle of the suppressed core, so it is the edge through
the edge `f` off the cycle there, in the pendant core; the block of that node is then not a
4-network block (`not_fourNetworkBlock_of_mem_pendantCore`), so the node is the excepted one, and
every edge of the tree at the class is the chain of the same edge of `Ñ`. -/
theorem isLeafNode_of_fourNetworkBlocks
    {w : Quot (ContractRel (coreSuppressed (tildeNetwork G)).graph fun _ => True)}
    (hw : ArisesFrom G w C)
    (hb : ∃ u ∈ cycleNodes G.graph C, ∀ u' ∈ cycleNodes G.graph C, u' ≠ u →
      IsFourNetworkBlock G C u') :
    IsLeafNode (treeOfCycles (tildeNetwork G)).graph w := by
  obtain ⟨u₀, hu₀, s₀, hs₀, rfl⟩ := hw
  obtain ⟨u, hu, hblk⟩ := hb
  obtain ⟨_, _, C₂, hC₂, -, hedge⟩ := exists_isCycle_tilde_of_big hG hC h4
  obtain ⟨f, hfu, hfC, -⟩ := hG.exists_offCycle hC hu
  -- every edge of the tree at the class has an edge of `Ñ` through `f`
  have key : ∀ t, ((treeOfCycles (tildeNetwork G)).graph.source t = Quot.mk _ s₀ ∨
      (treeOfCycles (tildeNetwork G)).graph.target t = Quot.mk _ s₀) →
      ∃ ρ ∈ t.1.1, ∃ g ∈ ρ.1.1, g.1 = f := by
    intro t ht
    obtain ⟨s, hs, hst⟩ : ∃ s, (Quot.mk _ s : Quot (ContractRel
        (coreSuppressed (tildeNetwork G)).graph fun _ => True)) = Quot.mk _ s₀ ∧
        ((coreSuppressed (tildeNetwork G)).graph.source t.1 = s ∨
          (coreSuppressed (tildeNetwork G)).graph.target t.1 = s) := by
      rcases ht with h | h
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr rfl⟩
    obtain ⟨u', hu', hsu'⟩ := exists_mem_of_mk_eq_of_big hG hC hu₀ hs₀ hs
    obtain ⟨ρ, hρ, hρs⟩ := suppressExcept_exists_mem_incident hst
    obtain ⟨g, hg, hgs⟩ := exists_mem_incident_of_tildeNetwork (c' := ρ.1) (w := s.1.1)
      (hρs.imp (congrArg Subtype.val) (congrArg Subtype.val))
    have hgu' : G.graph.source g.1 = u' ∨ G.graph.target g.1 = u' := hgs.imp
      (fun h => (eq_of_mk_eq_of_big hG hC h4 hu' (hsu'.symm.trans h.symm)).symm)
      (fun h => (eq_of_mk_eq_of_big hG hC h4 hu' (hsu'.symm.trans h.symm)).symm)
    by_cases hgC : g.1 ∈ C
    · -- an edge of the cycle: its chain is an edge of a cycle of the suppressed core
      exfalso
      obtain ⟨d, hd, ρ', hρ', g', hg', hg'g⟩ := hedge g.1 hgC
      obtain rfl : g' = g := Subtype.ext hg'g
      obtain rfl : ρ' = ρ := Subtype.ext (Subtype.ext (ρ'.1.2.eq_of_mem ρ.1.2 hg' hg))
      obtain rfl : d = t.1 := Subtype.ext (d.2.eq_of_mem t.1.2 hρ' hρ)
      exact t.2 C₂ hC₂ trivial hd
    · -- the edge off the cycle: its block is not a 4-network block
      have hgcyc : ∀ C', IsCycle G.graph C' → g.1 ∉ C' := fun C' hC' hgC' => by
        have hu'C' : u' ∈ cycleNodes G.graph C' := ⟨g.1, hgC', hgu'⟩
        exact hgC (hG.cycle_eq C' C hC' hC ⟨u', hu'C', hu'⟩ ▸ hgC')
      have hnb := not_fourNetworkBlock_of_mem_pendantCore hG hC hu' hgu' hgC hgcyc hg rfl ρ.2
      obtain rfl : u' = u := by_contra fun hne => hnb (hblk u' hu' hne)
      exact ⟨ρ, hρ, g, hg, hG.eq_of_notMem_of_incident hC hu' hgu' hgC hfu hfC⟩
  intro t₁ ht₁ t₂ ht₂
  obtain ⟨ρ₁, hρ₁, g₁, hg₁, hg₁f⟩ := key t₁ ht₁
  obtain ⟨ρ₂, hρ₂, g₂, hg₂, hg₂f⟩ := key t₂ ht₂
  obtain rfl : g₁ = g₂ := Subtype.ext (hg₁f.trans hg₂f.symm)
  obtain rfl : ρ₁ = ρ₂ := Subtype.ext (Subtype.ext (ρ₁.1.2.eq_of_mem ρ₂.1.2 hg₁ hg₂))
  exact Subtype.ext (Subtype.ext (t₁.1.2.eq_of_mem t₂.1.2 hρ₁ hρ₂))

/-- **The leaves of the tree of cycles** (proof of Theorem 4): a node arising from a cycle `C_v` of
size at least four is a leaf exactly when all the `v`-blocks but one are 4-network blocks. -/
theorem isLeafNode_iff_fourNetworkBlocks
    {w : Quot (ContractRel (coreSuppressed (tildeNetwork G)).graph fun _ => True)}
    (hw : ArisesFrom G w C) :
    IsLeafNode (treeOfCycles (tildeNetwork G)).graph w ↔
      ∃ u ∈ cycleNodes G.graph C, ∀ u' ∈ cycleNodes G.graph C, u' ≠ u →
        IsFourNetworkBlock G C u' :=
  ⟨fourNetworkBlocks_of_isLeafNode hG hC h4 hw, isLeafNode_of_fourNetworkBlocks hG hC h4 hw⟩

/-- **The tree of cycles has a leaf** when the network has a cycle of size at least four: it is a
finite tree (`treeOfCycles_isTree`) with a node, the class of the nodes of the cycle. -/
theorem exists_isLeafNode_treeOfCycles_of_big :
    ∃ w, IsLeafNode (treeOfCycles (tildeNetwork G)).graph w := by
  obtain ⟨_, _, _, _, hall, -⟩ := exists_isCycle_tilde_of_big hG hC h4
  obtain ⟨u, hu⟩ := hC.cycleNodes_nonempty
  obtain ⟨-, s, -, -⟩ := hall u hu
  have : Nonempty (Quot (ContractRel (coreSuppressed (tildeNetwork G)).graph fun _ => True)) :=
    ⟨Quot.mk _ s⟩
  exact exists_isLeafNode_of_isTree
    (treeOfCycles_isTree (tildeNetwork_loopless hG) (tildeNetwork_isConnected hG))

end Tilde

/-! ### The tree of cycles of `Ñ`, for `N⁻` -/

section Unrooted

variable {V E X : Type*} [Finite V] [Finite E] {N : RootedNetwork V E X}
  (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X)
include h1

/-- **The tree of cycles `T` of `Ñ` is connected** (Definition 13, proof of Theorem 4). -/
theorem isConnected_treeOfCycles_unrooted :
    (treeOfCycles (tildeNetwork (unrooted N hN hX))).graph.IsConnected :=
  (treeOfCycles_tilde_isTree (isUnrootedLevelOne_unrooted hN h1 hX)).1

/-- **The tree of cycles `T` of `Ñ` has no cycle** (Definition 13, proof of Theorem 4). -/
theorem not_isCycle_treeOfCycles_unrooted (C) :
    ¬ IsCycle (treeOfCycles (tildeNetwork (unrooted N hN hX))).graph C :=
  not_isCycle_of_isTree (treeOfCycles_tilde_isTree (isUnrootedLevelOne_unrooted hN h1 hX)) C

/-- **Every leaf of `T` arises from a cycle of `N⁻` of size at least four** (proof of Theorem 4). -/
theorem exists_arisesFrom_of_isLeafNode_unrooted
    {w : Quot (ContractRel (coreSuppressed (tildeNetwork (unrooted N hN hX))).graph fun _ => True)}
    (hw : IsLeafNode (treeOfCycles (tildeNetwork (unrooted N hN hX))).graph w) :
    ∃ C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4, ArisesFrom (unrooted N hN hX) w C := by
  obtain ⟨C, hC, h4, hwC⟩ :=
    exists_arisesFrom_of_isLeafNode (isUnrootedLevelOne_unrooted hN h1 hX) hw
  exact ⟨C, ⟨hC, h4⟩, hwC⟩

omit [Finite V] in
/-- **A node of `T` arises from each cycle of `N⁻` of size at least four**: the class of a node of
the suppressed core of `Ñ` coming from a node of the cycle (`exists_isCycle_tilde_of_big`). -/
theorem exists_arisesFrom_unrooted {C : Set _}
    (hC : C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4) :
    ∃ w, ArisesFrom (unrooted N hN hX) w C := by
  obtain ⟨_, _, _, _, hall, -⟩ :=
    exists_isCycle_tilde_of_big (isUnrootedLevelOne_unrooted hN h1 hX) hC.1 hC.2
  obtain ⟨u, hu⟩ := hC.1.cycleNodes_nonempty
  obtain ⟨-, s, -, hs⟩ := hall u hu
  exact ⟨_, u, hu, s, hs, rfl⟩

/-- **A leaf of `T` arising from a cycle `C_v` of size at least four has all its `v`-blocks but one
4-network blocks** (proof of Theorem 4). -/
theorem fourNetworkBlocks_of_isLeafNode_unrooted {C : Set _}
    (hC : C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4)
    {w : Quot (ContractRel (coreSuppressed (tildeNetwork (unrooted N hN hX))).graph fun _ => True)}
    (hw : ArisesFrom (unrooted N hN hX) w C)
    (hleaf : IsLeafNode (treeOfCycles (tildeNetwork (unrooted N hN hX))).graph w) :
    ∃ u ∈ cycleNodes (unrooted N hN hX).graph C, ∀ u' ∈ cycleNodes (unrooted N hN hX).graph C,
      u' ≠ u → IsFourNetworkBlock (unrooted N hN hX) C u' :=
  fourNetworkBlocks_of_isLeafNode (isUnrootedLevelOne_unrooted hN h1 hX) hC.1 hC.2 hw hleaf

/-- **The leaves of `T`** (proof of Theorem 4): a node of `T` arising from a cycle `C_v` of `N⁻` of
size at least four is a leaf exactly when all the `v`-blocks but one are 4-network blocks. -/
theorem isLeafNode_iff_fourNetworkBlocks_unrooted {C : Set _}
    (hC : C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4)
    {w : Quot (ContractRel (coreSuppressed (tildeNetwork (unrooted N hN hX))).graph fun _ => True)}
    (hw : ArisesFrom (unrooted N hN hX) w C) :
    IsLeafNode (treeOfCycles (tildeNetwork (unrooted N hN hX))).graph w ↔
      ∃ u ∈ cycleNodes (unrooted N hN hX).graph C, ∀ u' ∈ cycleNodes (unrooted N hN hX).graph C,
        u' ≠ u → IsFourNetworkBlock (unrooted N hN hX) C u' :=
  isLeafNode_iff_fourNetworkBlocks (isUnrootedLevelOne_unrooted hN h1 hX) hC.1 hC.2 hw

/-- **`T` has a leaf** when `N⁻` has a cycle of size at least four (proof of Theorem 4): it is a
finite tree with a node. -/
theorem exists_isLeafNode_treeOfCycles_unrooted
    (h : (cyclesOfSizeAtLeast (unrooted N hN hX).graph 4).Nonempty) :
    ∃ w, IsLeafNode (treeOfCycles (tildeNetwork (unrooted N hN hX))).graph w := by
  obtain ⟨C, hC, h4⟩ := h
  exact exists_isLeafNode_treeOfCycles_of_big (isUnrootedLevelOne_unrooted hN h1 hX) hC h4

end Unrooted

end Banos2019
