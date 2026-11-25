module

public import Banos2019.Network.Cycle

/-!
# The orientation of a cycle of a binary level-1 network

A cycle `C` of a binary level-1 rooted network has one hybrid node `v` (Lemma 3), and its edges are
directed along two paths from a *top* node `t` down to `v`:

* `IsCycle.ncard_incident`: every node of a cycle lies on exactly two of its edges.
* `ncard_cycleNodes`: a cycle has as many nodes as edges.
* `reaches_hybrid`: every node of `C` is above `v`.
* `exists_top`: exactly one node `t` of `C` is entered by no edge of `C`; it is above every node of
  `C` (`top_reaches`), and every other node of `C` is entered by edges of `C` only (`target_eq_top`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Graph

variable {G : DirectedMultigraph V E}

theorem IsCycle.exists_of_mem {C : Set E} (hC : IsCycle G C) {w : V} (hw : w ∈ cycleNodes G C) :
    ∃ (k : ℕ) (v : Fin k → V) (e : Fin k → E), IsCycleOf G k v e ∧ Set.range e = C ∧
      ∃ j, v j = w := by
  obtain ⟨k, v, e, hcyc, rfl⟩ := hC
  obtain ⟨f, ⟨i, rfl⟩, hf⟩ := hw
  refine ⟨k, v, e, hcyc, rfl, ?_⟩
  rcases hcyc.joins i with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> rcases hf with hf | hf
  · exact ⟨i, hs.symm.trans hf⟩
  · exact ⟨finRotate k i, ht.symm.trans hf⟩
  · exact ⟨finRotate k i, hs.symm.trans hf⟩
  · exact ⟨i, ht.symm.trans hf⟩

theorem IsCycleOf.two_le (hloop : ∀ e, G.source e ≠ G.target e) {k : ℕ} {v : Fin k → V}
    {e : Fin k → E} (hcyc : IsCycleOf G k v e) : 2 ≤ k := by
  have hk := hcyc.pos
  by_contra hlt
  have hk1 : k = 1 := by omega
  subst hk1
  have hrot : finRotate 1 0 = 0 := Subsingleton.elim _ _
  rcases hcyc.joins 0 with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hrot] at ht
    exact hloop (e 0) (hs.trans ht.symm)
  · rw [hrot] at hs
    exact hloop (e 0) (hs.trans ht.symm)

/-- **Every node of a cycle lies on exactly two of its edges.** -/
theorem IsCycle.ncard_incident (hloop : ∀ e, G.source e ≠ G.target e) {C : Set E}
    (hC : IsCycle G C) {w : V} (hw : w ∈ cycleNodes G C) :
    {e | e ∈ C ∧ (G.source e = w ∨ G.target e = w)}.ncard = 2 := by
  obtain ⟨k, v, e, hcyc, rfl, j, rfl⟩ := hC.exists_of_mem hw
  have hk := hcyc.two_le hloop
  have hrot : finRotate k j ≠ j := by
    have : NeZero k := ⟨by omega⟩
    rw [finRotate_apply]
    intro h
    have h1 : (1 : Fin k) = 0 := by
      have := congrArg (· - j) h
      simpa using this
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    exact absurd h1 (by simp)
  have hj : (finRotate k).symm j ≠ j := fun h => hrot (by
    have := congrArg (finRotate k) h
    rwa [Equiv.apply_symm_apply, eq_comm] at this)
  have hset : {f | f ∈ Set.range e ∧ (G.source f = v j ∨ G.target f = v j)} =
      {e j, e ((finRotate k).symm j)} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      have hendp : v i = v j ∨ v (finRotate k i) = v j := by
        rcases hcyc.joins i with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> rcases hi with hi | hi
        · exact Or.inl (hs.symm.trans hi)
        · exact Or.inr (ht.symm.trans hi)
        · exact Or.inr (hs.symm.trans hi)
        · exact Or.inl (ht.symm.trans hi)
      rcases hendp with h | h
      · exact Or.inl (congrArg e (hcyc.injective_node h))
      · refine Or.inr (congrArg e ?_)
        rw [← hcyc.injective_node h, Equiv.symm_apply_apply]
    · rintro (rfl | rfl)
      · refine ⟨⟨j, rfl⟩, ?_⟩
        rcases hcyc.joins j with ⟨hs, -⟩ | ⟨-, ht⟩
        · exact Or.inl hs
        · exact Or.inr ht
      · refine ⟨⟨_, rfl⟩, ?_⟩
        rcases hcyc.joins ((finRotate k).symm j) with ⟨-, ht⟩ | ⟨hs, -⟩
        · rw [Equiv.apply_symm_apply] at ht
          exact Or.inr ht
        · rw [Equiv.apply_symm_apply] at hs
          exact Or.inl hs
  rw [hset, Set.ncard_pair fun h => hj (hcyc.injective_edge h).symm]

/-- **A cycle has as many nodes as edges.** -/
theorem ncard_cycleNodes {C : Set E} (hC : IsCycle G C) : (cycleNodes G C).ncard = C.ncard := by
  obtain ⟨k, v, e, hcyc, rfl⟩ := hC
  have hn : cycleNodes G (Set.range e) = Set.range v := by
    ext w
    constructor
    · rintro ⟨f, ⟨i, rfl⟩, hf⟩
      rcases hcyc.joins i with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> rcases hf with hf | hf
      · exact ⟨i, hs.symm.trans hf⟩
      · exact ⟨finRotate k i, ht.symm.trans hf⟩
      · exact ⟨finRotate k i, hs.symm.trans hf⟩
      · exact ⟨i, ht.symm.trans hf⟩
    · rintro ⟨i, rfl⟩
      refine ⟨e i, ⟨i, rfl⟩, ?_⟩
      rcases hcyc.joins i with ⟨hs, -⟩ | ⟨-, ht⟩
      · exact Or.inl hs
      · exact Or.inr ht
  rw [hn, Set.ncard_range_of_injective hcyc.injective_node,
    Set.ncard_range_of_injective hcyc.injective_edge]

theorem IsCycle.finite [Finite E] {C : Set E} (_ : IsCycle G C) : C.Finite := Set.toFinite C

end Graph

section Rooted

variable {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
  {C : Set E} (hC : IsCycle N.graph C) {v : V} (hv : v ∈ cycleNodes N.graph C)
  (h2 : N.graph.indegree v = 2)
include hN h1 hC hv h2

omit h1 hC hv h2 in
theorem source_ne_target_of_binary (e : E) : N.graph.source e ≠ N.graph.target e := fun h =>
  hN.1.acyclic _ (.single ⟨e, rfl, h.symm⟩)

/-- The nodes of `C` other than its hybrid node have at most one parent. -/
theorem indegree_le_one_of_mem {w : V} (hw : w ∈ cycleNodes N.graph C) (hwv : w ≠ v) :
    N.graph.indegree w ≤ 1 := by
  have := hN.1.finite_arcs
  have hdeg := (isBinaryRootedNetwork_iff N).1 hN
  obtain ⟨-, -, -, -, -, hr0, -, hleaf, -, hother⟩ := hdeg
  have huniq := (lemma3 hN h1 hC).1
  by_cases hr : w = N.root
  · rw [hr, hr0]
    exact zero_le_one
  by_cases hl : w ∈ Set.range N.leaf
  · obtain ⟨x, rfl⟩ := hl
    exact (hleaf x).1.le
  rcases hother w hr hl with h | h
  · exact h.1.le
  · exact absurd (huniq.unique ⟨hw, h.1⟩ ⟨hv, h2⟩) hwv

omit h1 hC hv h2 in
theorem two_le_indegree_of_two_targets {w : V} {e e' : E} (hne : e ≠ e')
    (he : N.graph.target e = w) (he' : N.graph.target e' = w) : 2 ≤ N.graph.indegree w := by
  have := hN.1.finite_arcs
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_pair hne]
  exact Set.ncard_le_ncard (by
    intro f hf
    rcases hf with rfl | hf
    · exact he
    · rw [Set.mem_singleton_iff.1 hf]; exact he') (Set.toFinite _)

/-- A node of `C` other than its hybrid node leaves an edge of `C`. -/
theorem exists_source_of_mem {w : V} (hw : w ∈ cycleNodes N.graph C) (hwv : w ≠ v) :
    ∃ e ∈ C, N.graph.source e = w := by
  have := hN.1.finite_arcs
  by_contra hno
  push Not at hno
  have hinc := hC.ncard_incident (source_ne_target_of_binary hN) hw
  have hsub : {e | e ∈ C ∧ (N.graph.source e = w ∨ N.graph.target e = w)} ⊆
      {e | N.graph.target e = w} := fun e he => he.2.resolve_left (hno e he.1)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hle := indegree_le_one_of_mem hN h1 hC hv h2 hw hwv
  unfold DirectedMultigraph.indegree at hle
  omega

/-- **Every node of a cycle is above its hybrid node.** -/
theorem reaches_hybrid (w : V) (hw : w ∈ cycleNodes N.graph C) : N.graph.Reaches w v := by
  have := hN.1.finite_vertices
  let rel : V → V → Prop := fun a c => Relation.TransGen N.graph.Adj c a
  have : IsTrans V rel := ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
  have : Std.Irrefl rel := ⟨fun a ha => hN.1.acyclic a ha⟩
  have hwf : WellFounded rel := Finite.wellFounded_of_trans_of_irrefl rel
  induction w using hwf.induction with
  | _ w ih =>
    by_cases hwv : w = v
    · subst hwv
      exact .refl
    · obtain ⟨e, he, hs⟩ := exists_source_of_mem hN h1 hC hv h2 hw hwv
      exact Relation.ReflTransGen.head ⟨e, hs, rfl⟩
        (ih _ (.single ⟨e, hs, rfl⟩) ⟨e, he, Or.inr rfl⟩)

omit hN h1 hC hv h2 in
theorem target_mem_cycleNodes' {e : E} (he : e ∈ C) : N.graph.target e ∈ cycleNodes N.graph C :=
  ⟨e, he, Or.inr rfl⟩

omit hN h1 hC hv h2 in
theorem source_mem_cycleNodes' {e : E} (he : e ∈ C) : N.graph.source e ∈ cycleNodes N.graph C :=
  ⟨e, he, Or.inl rfl⟩

/-- The hybrid edges of `v` are its two edges in `C`. -/
theorem mem_of_target_eq_hybrid {e : E} (he : N.graph.target e = v) : e ∈ C :=
  have := hN.1.finite_arcs
  (lemma3 hN h1 hC).2.1 v hv h2 e he

/-- An arc leaving the hybrid node is not an edge of `C`. -/
theorem notMem_of_source_eq_hybrid {c : E} (hc : N.graph.source c = v) : c ∉ C := by
  have := hN.1.finite_arcs
  intro hcC
  obtain ⟨h₁, h₂, hne, hh₁, hh₂⟩ : ∃ h₁ h₂, h₁ ≠ h₂ ∧ N.graph.target h₁ = v ∧
      N.graph.target h₂ = v := by
    obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 h2
    have hx : x ∈ {e | N.graph.target e = v} := hs ▸ Set.mem_insert x {y}
    have hy : y ∈ {e | N.graph.target e = v} := hs ▸ Set.mem_insert_of_mem x rfl
    exact ⟨x, y, hxy, hx, hy⟩
  have hloop := source_ne_target_of_binary hN
  have h1c : c ≠ h₁ := fun h => hloop c (hc.trans (h ▸ hh₁).symm)
  have h2c : c ≠ h₂ := fun h => hloop c (hc.trans (h ▸ hh₂).symm)
  have hinc := hC.ncard_incident hloop hv
  have hsub : ({c, h₁, h₂} : Set E) ⊆ {e | e ∈ C ∧ (N.graph.source e = v ∨ N.graph.target e = v)} := by
    intro f hf
    rcases hf with rfl | rfl | hf
    · exact ⟨hcC, Or.inl hc⟩
    · exact ⟨mem_of_target_eq_hybrid hN h1 hC hv h2 hh₁, Or.inr hh₁⟩
    · rw [Set.mem_singleton_iff.1 hf]
      exact ⟨mem_of_target_eq_hybrid hN h1 hC hv h2 hh₂, Or.inr hh₂⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem (by simp [h1c, h2c]) (Set.toFinite _), Set.ncard_pair hne] at this
  omega

/-- The number of edges of `C` entering `w`. -/
def inCycle (C : Set E) (w : V) [Fintype E] : ℕ :=
  #(univ.filter fun e => e ∈ C ∧ N.graph.target e = w)

omit hN h1 hC hv h2 in
theorem inCycle_le_indegree [Fintype E] (w : V) : inCycle (N := N) C w ≤ N.graph.indegree w := by
  unfold inCycle DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun e he => (mem_filter.1 (mem_coe.1 he)).2.2) (Set.toFinite _)

/-- **The top of a cycle**: exactly one node of `C` is entered by no edge of `C`. -/
theorem existsUnique_top [Fintype V] [Fintype E] :
    ∃! t, t ∈ cycleNodes N.graph C ∧ inCycle (N := N) C t = 0 := by
  let S : Finset V := univ.filter (· ∈ cycleNodes N.graph C)
  have hSv : v ∈ S := mem_filter.2 ⟨mem_univ _, hv⟩
  have hcount : ∑ w ∈ S, inCycle (N := N) C w = #S := by
    have h := card_eq_sum_card_fiberwise (f := N.graph.target)
      (s := univ.filter fun e => e ∈ C) (t := S) fun e he =>
        mem_filter.2 ⟨mem_univ _, target_mem_cycleNodes' (mem_filter.1 he).2⟩
    have hC' : #(univ.filter fun e => e ∈ C) = #S := by
      rw [← Set.ncard_coe_finset, ← Set.ncard_coe_finset]
      simp only [coe_filter, mem_univ, true_and, S]
      exact (ncard_cycleNodes hC).symm
    rw [← hC', h]
    refine sum_congr rfl fun w _ => ?_
    unfold inCycle
    rw [filter_filter]
  have hv2 : inCycle (N := N) C v = 2 := by
    rw [← h2]
    unfold inCycle DirectedMultigraph.indegree
    rw [← Set.ncard_coe_finset]
    congr 1
    ext e
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨mem_of_target_eq_hybrid hN h1 hC hv h2 h, h⟩⟩
  have hle : ∀ w ∈ S.erase v, inCycle (N := N) C w ≤ 1 := fun w hw =>
    (inCycle_le_indegree w).trans (indegree_le_one_of_mem hN h1 hC hv h2
      (mem_filter.1 (mem_of_mem_erase hw)).2 (ne_of_mem_erase hw))
  have hsum : ∑ w ∈ S.erase v, inCycle (N := N) C w = #S - 2 := by
    have := hcount
    rw [← add_sum_erase S _ hSv, hv2] at this
    omega
  have hsum' : ∑ w ∈ S.erase v, inCycle (N := N) C w =
      #((S.erase v).filter fun w => inCycle (N := N) C w ≠ 0) := by
    rw [card_eq_sum_ones, sum_filter]
    refine sum_congr rfl fun w hw => ?_
    have := hle w hw
    split_ifs with h0 <;> omega
  have hZ : #((S.erase v).filter fun w => inCycle (N := N) C w = 0) = 1 := by
    have h := card_filter_add_card_filter_not (s := S.erase v)
      (fun w => inCycle (N := N) C w = 0)
    rw [card_erase_of_mem hSv] at h
    have hS2 : 2 ≤ #S := by
      have := hcount
      rw [← add_sum_erase S _ hSv, hv2] at this
      omega
    simp only [ne_eq] at hsum'
    omega
  obtain ⟨t, ht⟩ := card_eq_one.1 hZ
  have htm : t ∈ (S.erase v).filter fun w => inCycle (N := N) C w = 0 := ht ▸ mem_singleton_self t
  refine ⟨t, ⟨(mem_filter.1 (mem_of_mem_erase (mem_filter.1 htm).1)).2, (mem_filter.1 htm).2⟩,
    fun w ⟨hw, hw0⟩ => ?_⟩
  have hwv : w ≠ v := fun h => by rw [h, hv2] at hw0; exact absurd hw0 (by norm_num)
  have : w ∈ (S.erase v).filter fun w => inCycle (N := N) C w = 0 :=
    mem_filter.2 ⟨mem_erase.2 ⟨hwv, mem_filter.2 ⟨mem_univ _, hw⟩⟩, hw0⟩
  rw [ht] at this
  exact mem_singleton.1 this

omit h1 hC hv in
/-- A hybrid node of a binary network has exactly one child arc. -/
theorem existsUnique_child_of_hybrid : ∃ c, N.graph.source c = v ∧ ∀ g, N.graph.source g = v → g = c := by
  have := hN.1.finite_arcs
  have hvr : v ≠ N.root := fun h => by
    have := hN.1.root_indegree
    rw [← h, h2] at this
    exact absurd this (by norm_num)
  have hout : N.graph.outdegree v ≠ 0 := fun h0 => by
    obtain ⟨x, hx⟩ := (hN.1.leaves v).1 h0
    have := hN.1.leaf_indegree x
    rw [hx, h2] at this
    exact absurd this (by norm_num)
  have h3 := hN.2.2 v hvr hout
  have h1' : N.graph.outdegree v = 1 := by omega
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 h1'
  refine ⟨c, (Set.ext_iff.1 hc c).2 rfl, fun g hg => ?_⟩
  have : g ∈ ({c} : Set E) := hc ▸ hg
  exact this

omit hC hv in
/-- **Below a hybrid node, the vertices are entered only at it**: an arc into a vertex below the
hybrid node `v` of a binary level-1 network, other than `v`, leaves a vertex below `v`. Otherwise the
vertex entered would be a hybrid node whose cycle passes through `v`, a second cycle at `v`. -/
theorem reaches_source_of_below_hybrid {e : E} (he : N.graph.Reaches v (N.graph.target e))
    (hne : N.graph.target e ≠ v) : N.graph.Reaches v (N.graph.source e) := by
  sorry

omit hN h1 hC hv h2 in
/-- The vertices below a vertex whose only child arc is `c`: the vertex itself, or below `c`. -/
theorem eq_or_reaches_of_unique_child {c : E} (huniq : ∀ g, N.graph.source g = v → g = c) {w : V}
    (hw : N.graph.Reaches v w) : w = v ∨ N.graph.Reaches (N.graph.target c) w := by
  rcases Relation.ReflTransGen.cases_head hw with h | ⟨a, ⟨g, hg, rfl⟩, ha⟩
  · exact Or.inl h.symm
  · rw [huniq g hg] at ha
    exact Or.inr ha

end Rooted

end Banos2019
