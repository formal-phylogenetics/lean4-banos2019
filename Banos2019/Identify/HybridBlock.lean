module

public import Banos2019.Identify.UnrootedCycles

/-!
# The blocks of the nodes of a cycle of `N⁻` (Baños 2019, Sections 3 and 7)

Removing the edges of a cycle `C` of `N⁻` leaves one component through each node of `C`.

* `nodeBlock_nonempty_unrooted`: the component of every node of `C` holds a taxon.
* `mem_nodeBlock_iff_descendsFrom`: the taxa of the component of the hybrid node are those
  descending from it.

The proofs pass between `N⁻` and `N`: the nodes of `N⁻` are the vertices of `N` strictly below
`LSA(X)`, and its edges the arcs of `N` below `LSA(X)` other than `rootTreeArc`, the edge leaving
`LSA(X)` having the child of `rootTreeArc` as source.

* `reaches_source_of_below_hybrid`: in `N`, the vertices below a hybrid node `v` other than `v`
  are entered only from below `v`.
* `descendsFrom_of_reaches`: a directed path of `N` from a node of `N⁻` to a taxon is a semidirected
  path of `N⁻`.
* `walks_compl_of_isSDPathOf`: a semidirected path from a node of `C` that no step leaves along `C`
  avoids `C`.
* `nodeBlock_nonempty_of_child`, `nodeBlock_nonempty_of_parents`: the block of a node of the cycle
  holds a taxon below a child off the cycle, or else a taxon reached from `LSA(X)` avoiding the
  node.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Walks avoiding a cycle -/

section Walks

variable {G : DirectedMultigraph V E}

/-- A walk avoiding `C` continues along an edge outside `C` at its end: both ends of the edge are
reached. -/
theorem walks_compl_ends_of_notMem {C : Set E} {u w : V} (hw : G.Walks Cᶜ u w) {f : E}
    (hf : G.source f = w ∨ G.target f = w) (hfC : f ∉ C) :
    G.Walks Cᶜ u (G.source f) ∧ G.Walks Cᶜ u (G.target f) := by
  have hadj : G.AdjOn Cᶜ (G.source f) (G.target f) := ⟨f, hfC, Or.inl ⟨rfl, rfl⟩⟩
  rcases hf with h | h
  · rw [h] at hadj ⊢
    exact ⟨hw, hw.tail hadj⟩
  · rw [h] at hadj ⊢
    exact ⟨hw.tail (G.adjOn_symm hadj), hw⟩

/-- **Off the cycle, the edges are outside the cycle**: in a level-1 graph, a node `w ≠ u` joined to
the node `u` of a cycle `C` by a walk avoiding `C` is not on `C`, so no edge at `w` is in `C`. -/
theorem IsLevelOne.notMem_of_walks_compl (h1 : IsLevelOne G) {C : Set E} (hC : IsCycle G C)
    {u w : V} (hu : u ∈ cycleNodes G C) (hw : G.Walks Cᶜ u w) (hne : w ≠ u) {f : E}
    (hf : G.source f = w ∨ G.target f = w) : f ∉ C := fun hfC =>
  hne (h1.eq_of_walks_compl hC hu ⟨f, hfC, hf⟩ hw).symm

/-- In a level-1 graph, a walk avoiding a cycle `C` from a node `u` of `C`, ending at `w ≠ u`,
continues along every edge at `w`. -/
theorem IsLevelOne.walks_compl_ends (h1 : IsLevelOne G) {C : Set E} (hC : IsCycle G C) {u w : V}
    (hu : u ∈ cycleNodes G C) (hw : G.Walks Cᶜ u w) (hne : w ≠ u) {f : E}
    (hf : G.source f = w ∨ G.target f = w) :
    G.Walks Cᶜ u (G.source f) ∧ G.Walks Cᶜ u (G.target f) :=
  walks_compl_ends_of_notMem hw hf (h1.notMem_of_walks_compl hC hu hw hne hf)

/-- Two distinct arcs entering a vertex give it indegree at least two. -/
theorem two_le_indegree_of_ne_targets [Finite E] {w : V} {e e' : E} (hne : e ≠ e')
    (he : G.target e = w) (he' : G.target e' = w) : 2 ≤ G.indegree w := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_pair hne]
  exact Set.ncard_le_ncard (by rintro f (rfl | rfl) <;> assumption) (Set.toFinite _)

end Walks

/-- **A semidirected path that can neither start along `C` nor come back to `C` avoids `C`**:
when no step along an edge of `C` leaves `v`, and no node of `C` other than `v` is joined to `v` by
a walk avoiding `C`, every node of a semidirected path from `v` is joined to `v` by a walk avoiding
`C`. At the first edge of `C` on the path, the path would be at a node of `C` reached from `v`
avoiding `C`, so at `v`, and would leave `v` along `C`. -/
theorem walks_compl_of_isSDPathOf {V' E' X' : Type*} {G : SemidirectedNetwork V' E' X'}
    {C : Set E'} {v : V'} (hfirst : ∀ e ∈ C, ∀ w, ¬ SDStep G e v w)
    (hback : ∀ u ∈ cycleNodes G.graph C, G.graph.Walks Cᶜ v u → u = v)
    {k : ℕ} {p : Fin (k + 1) → V'} {q : Fin k → E'} (hP : IsSDPathOf G k p q) (h0 : p 0 = v)
    (i : Fin (k + 1)) : G.graph.Walks Cᶜ v (p i) := by
  induction i using Fin.induction with
  | zero => exact h0 ▸ .refl
  | succ i ih =>
    have hstep := hP.step i
    by_cases hqC : q i ∈ C
    · exfalso
      have hmem : p i.castSucc ∈ cycleNodes G.graph C := by
        rcases hstep with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact ⟨q i, hqC, Or.inl h⟩
        · exact ⟨q i, hqC, Or.inr h⟩
      rw [hback _ hmem ih] at hstep
      exact hfirst _ hqC _ hstep
    · refine ih.tail ⟨q i, hqC, ?_⟩
      rcases hstep with ⟨h₁, h₂⟩ | ⟨-, h₁, h₂⟩
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨h₂, h₁⟩

/-! ### Below a hybrid node of a rooted network -/

section Rooted

variable {N : RootedNetwork V E X}

end Rooted

/-! ### The nodes and edges of `N⁻` in `N` -/

section Transfer

variable {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {hX : Nontrivial X}

/-- A node of `N⁻` is determined by its vertex of `N`. -/
theorem unrooted_node_ext {hP : N.IsPhylogenetic} {u w : SemidirectedVertex hP hX}
    (h : u.1.1 = w.1.1) : u = w :=
  Subtype.ext (Subtype.ext h)

/-- An edge of `N⁻` is determined by its arc of `N`. -/
theorem unrooted_edge_ext {hP : N.IsPhylogenetic} {hB : N.IsBinary}
    {c c' : SemidirectedArc hP hB hX} (h : c.1.1 = c'.1.1) : c = c' :=
  Subtype.ext (Subtype.ext h)

/-- A node of `N⁻` is not the LSA. -/
theorem unrooted_node_ne_lsa {hP : N.IsPhylogenetic} (u : SemidirectedVertex hP hX) :
    u.1.1 ≠ lsa hP Set.univ Set.univ_nonempty := fun h => u.2 (Subtype.ext h)

/-- An edge of `N⁻` keeps its target. -/
theorem unrooted_target_val (c : SemidirectedArc hN.1 hN.2 hX) :
    ((unrooted N hN hX).graph.target c).1.1 = N.graph.target c.1.1 := rfl

/-- An edge of `N⁻` not leaving the LSA keeps its source. -/
theorem unrooted_source_val_of_ne (c : SemidirectedArc hN.1 hN.2 hX)
    (h : N.graph.source c.1.1 ≠ lsa hN.1 Set.univ Set.univ_nonempty) :
    ((unrooted N hN hX).graph.source c).1.1 = N.graph.source c.1.1 := by
  have h' : (lsaPlus hN.1 hX).graph.source c.1 ≠ (lsaPlus hN.1 hX).root :=
    fun h' => h (congrArg Subtype.val h')
  simp only [unrooted, semidirected, unrootAt, dite_eq_right h']
  rfl

/-- The edge of `N⁻` leaving the LSA, merged with `rootTreeArc`, leaves the child of
`rootTreeArc`. -/
theorem unrooted_source_val_of_eq (c : SemidirectedArc hN.1 hN.2 hX)
    (h : N.graph.source c.1.1 = lsa hN.1 Set.univ Set.univ_nonempty) :
    ((unrooted N hN hX).graph.source c).1.1 = N.graph.target (rootTreeArc hN.1 hN.2 hX).1 := by
  have h' : (lsaPlus hN.1 hX).graph.source c.1 = (lsaPlus hN.1 hX).root := Subtype.ext h
  simp only [unrooted, semidirected, unrootAt, dite_eq_left h']
  rfl

/-- A vertex of `N` strictly below the LSA is a node of `N⁻`. -/
theorem exists_unrooted_node (hP : N.IsPhylogenetic) {a : V}
    (hma : N.graph.Reaches (lsa hP Set.univ Set.univ_nonempty) a)
    (ham : a ≠ lsa hP Set.univ Set.univ_nonempty) :
    ∃ w : SemidirectedVertex hP hX, w.1.1 = a :=
  ⟨⟨⟨a, hma, mem_ancestralVertices_univ hP a⟩, fun h => ham (congrArg Subtype.val h)⟩, rfl⟩

/-- An arc of `N` leaving a node `w` of `N⁻` is an edge of `N⁻` leaving `w`. -/
theorem exists_unrooted_edge (w : SemidirectedVertex hN.1 hX) {f : E}
    (hf : N.graph.source f = w.1.1) :
    ∃ c : SemidirectedArc hN.1 hN.2 hX, c.1.1 = f ∧ (unrooted N hN hX).graph.source c = w ∧
      ((unrooted N hN hX).graph.target c).1.1 = N.graph.target f := by
  have hfm : N.graph.source f ≠ lsa hN.1 Set.univ Set.univ_nonempty := hf ▸ unrooted_node_ne_lsa w
  have hmem : f ∈ N.belowArcs (lsa hN.1 Set.univ Set.univ_nonempty) Set.univ :=
    ⟨hf ▸ w.1.2.1, mem_ancestralVertices_univ hN.1 _⟩
  have hne : (⟨f, hmem⟩ : N.belowArcs _ _) ≠ rootTreeArc hN.1 hN.2 hX := fun h => hfm (by
    rw [show f = (rootTreeArc hN.1 hN.2 hX).1 from congrArg Subtype.val h]
    exact congrArg Subtype.val (rootTreeArc_spec hN.1 hN.2 hX).1)
  refine ⟨⟨⟨f, hmem⟩, hne⟩, rfl, unrooted_node_ext ?_, rfl⟩
  rw [unrooted_source_val_of_ne hN _ hfm]
  exact hf

/-- **`N⁻` has no loops**: an edge not leaving the LSA is an arc of the acyclic `N`, and the merged
edge joins the two distinct children of the LSA, `rootTreeArc` being a tree arc. -/
theorem unrooted_source_ne_target [Finite E] (c : SemidirectedArc hN.1 hN.2 hX) :
    (unrooted N hN hX).graph.source c ≠ (unrooted N hN hX).graph.target c := by
  intro h
  have h' : ((unrooted N hN hX).graph.source c).1.1 = ((unrooted N hN hX).graph.target c).1.1 :=
    congrArg (fun w => w.1.1) h
  by_cases hm : N.graph.source c.1.1 = lsa hN.1 Set.univ Set.univ_nonempty
  · rw [unrooted_source_val_of_eq hN c hm, unrooted_target_val] at h'
    have htree := (rootTreeArc_spec hN.1 hN.2 hX).2
    unfold IsTreeArc at htree
    have hne : rootTreeArc hN.1 hN.2 hX ≠ c.1 := fun h => c.2 h.symm
    have := two_le_indegree_of_ne_targets (G := (lsaPlus hN.1 hX).graph) hne rfl
      (Subtype.ext h'.symm)
    omega
  · rw [unrooted_source_val_of_ne hN c hm, unrooted_target_val] at h'
    exact hN.1.acyclic _ (.single ⟨c.1.1, rfl, h'.symm⟩)

/-- **A directed path of `N` from a node of `N⁻` is a semidirected path of `N⁻`**: below a node of
`N⁻` no vertex is the LSA, so the arcs are edges of `N⁻`, followed in their direction, and the
vertices of a directed path of the acyclic `N` are distinct. -/
theorem descendsFrom_of_reaches (w : SemidirectedVertex hN.1 hX) {x : X}
    (h : N.graph.Reaches w.1.1 (N.leaf x)) : DescendsFrom (unrooted N hN hX) w x := by
  suffices key : ∀ a, N.graph.Reaches a (N.leaf x) → ∀ w : SemidirectedVertex hN.1 hX, w.1.1 = a →
      ∃ P S, IsSDPath (unrooted N hN hX) w ((unrooted N hN hX).leaf x) P S ∧
        ∀ s ∈ S, N.graph.Reaches a s.1.1 by
    obtain ⟨P, S, hP, -⟩ := key _ h w rfl
    exact ⟨P, S, hP⟩
  intro a ha
  induction ha using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro w hw
    obtain rfl : w = (unrooted N hN hX).leaf x := unrooted_node_ext hw
    refine ⟨∅, {(unrooted N hN hX).leaf x}, ⟨0, fun _ => (unrooted N hN hX).leaf x, Fin.elim0,
      ⟨fun i => i.elim0, fun i j _ => Fin.ext (by omega)⟩, rfl, rfl, Set.range_eq_empty _,
      Set.range_const⟩, ?_⟩
    rintro s rfl
    exact .refl
  | @head a b hab hbx ih =>
    intro w hw
    obtain ⟨f, hfs, hft⟩ := hab
    obtain ⟨c, rfl, hcs, hct⟩ := exists_unrooted_edge hN w (hfs.trans hw.symm)
    obtain ⟨P, S, ⟨k, p, q, hpath, h0, hlast, hP, hS⟩, hSb⟩ := ih _ (hct.trans hft)
    refine ⟨insert c P, insert w S, ⟨k + 1, Fin.cons w p, Fin.cons c q, ⟨fun i => ?_, ?_⟩, rfl,
      ?_, ?_, ?_⟩, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, h0]
        exact Or.inl ⟨hcs, rfl⟩
      · rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hpath.step i
    · refine Fin.cons_injective_iff.mpr ⟨fun ⟨i, hi⟩ => ?_, hpath.injective⟩
      have hbw := hSb w (hS ▸ ⟨i, hi⟩)
      rw [hw] at hbw
      exact hN.1.acyclic _ (Relation.TransGen.head' ⟨c.1.1, hfs, hft⟩ hbw)
    · rw [← Fin.succ_last, Fin.cons_succ, hlast]
    · rw [Fin.range_cons, hP]
    · rw [Fin.range_cons, hS]
    · rintro s (rfl | hs)
      · rw [hw]
        exact .refl
      · exact (hSb s hs).head ⟨c.1.1, hfs, hft⟩

end Transfer

/-! ### The hybrid node of a cycle of `N⁻` -/

section CycleNodes

variable {N : RootedNetwork V E X} {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X} [Finite E]

/-- An arc of `N` entering the hybrid node `v` of a cycle `C` of `N⁻` is one of the two hybrid edges
of `v`, which are in `C`. -/
theorem IsHybridNodeOf.exists_mem_of_target {C : Set (SemidirectedArc hN.1 hN.2 hX)}
    {v : SemidirectedVertex hN.1 hX} (hv : IsHybridNodeOf (unrooted N hN hX) C v) {f : E}
    (hf : N.graph.target f = v.1.1) : ∃ h ∈ C, (unrooted N hN hX).IsDirected h ∧ h.1.1 = f := by
  obtain ⟨h₁, hh₁, h₂, hh₂, hne, hd₁, hd₂, ht₁, ht₂⟩ := hv
  have hne' : h₁.1.1 ≠ h₂.1.1 := fun h => hne (unrooted_edge_ext h)
  have ht₁' : N.graph.target h₁.1.1 = v.1.1 := congrArg (fun w => w.1.1) ht₁
  have ht₂' : N.graph.target h₂.1.1 = v.1.1 := congrArg (fun w => w.1.1) ht₂
  have h2 : N.graph.indegree v.1.1 = 2 :=
    le_antisymm (hN.indegree_le_two _) (two_le_indegree_of_two_targets hN hne' ht₁' ht₂')
  have hmem : f ∈ ({h₁.1.1, h₂.1.1} : Set E) := by
    rw [← eq_or_eq_of_indegree_eq_two h2 hne' ht₁' ht₂']
    exact hf
  rcases hmem with rfl | rfl
  · exact ⟨h₁, hh₁, hd₁, rfl⟩
  · exact ⟨h₂, hh₂, hd₂, rfl⟩

omit [Finite E] in
/-- The hybrid node of a cycle of `N⁻` is a hybrid node of `N`. -/
theorem IsHybridNodeOf.unrooted_indegree {C : Set (SemidirectedArc hN.1 hN.2 hX)}
    {v : SemidirectedVertex hN.1 hX} (hv : IsHybridNodeOf (unrooted N hN hX) C v) :
    N.graph.indegree v.1.1 = 2 := by
  obtain ⟨h₁, -, h₂, -, hne, -, -, ht₁, ht₂⟩ := hv
  exact le_antisymm (hN.indegree_le_two _) (two_le_indegree_of_two_targets hN
    (fun h => hne (unrooted_edge_ext h)) (congrArg (fun w => w.1.1) ht₁)
    (congrArg (fun w => w.1.1) ht₂))

/-- **No semidirected step leaves the hybrid node along its cycle**: the two edges of the cycle at
the hybrid node are its hybrid edges, which enter it. -/
theorem IsHybridNodeOf.not_sdStep {C : Set (SemidirectedArc hN.1 hN.2 hX)}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) :
    ∀ e ∈ C, ∀ w, ¬ SDStep (unrooted N hN hX) e v w := by
  intro e he w hstep
  rcases hstep with ⟨hs, -⟩ | ⟨hnd, ht, -⟩
  · -- `e` leaves `v`: with the two hybrid edges, `C` would have three edges at `v`
    have hinc := hC.ncard_incident (unrooted_source_ne_target hN) hv.mem_cycleNodes
    obtain ⟨h₁, hh₁, h₂, hh₂, hne, -, -, ht₁, ht₂⟩ := hv
    have he₁ : e ≠ h₁ := by
      rintro rfl
      exact unrooted_source_ne_target hN e (hs.trans ht₁.symm)
    have he₂ : e ≠ h₂ := by
      rintro rfl
      exact unrooted_source_ne_target hN e (hs.trans ht₂.symm)
    have hsub : ({e, h₁, h₂} : Set _) ⊆ {f | f ∈ C ∧ ((unrooted N hN hX).graph.source f = v ∨
        (unrooted N hN hX).graph.target f = v)} := by
      rintro f (rfl | rfl | rfl)
      · exact ⟨he, Or.inl hs⟩
      · exact ⟨hh₁, Or.inr ht₁⟩
      · exact ⟨hh₂, Or.inr ht₂⟩
    have h3 : ({e, h₁, h₂} : Set (SemidirectedArc hN.1 hN.2 hX)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by rintro (h | h) <;> [exact he₁ h; exact he₂ h]),
        Set.ncard_pair hne]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  · -- `e` enters `v`: it is a hybrid edge of `v`, which is directed
    obtain ⟨h, -, hd, hh⟩ := hv.exists_mem_of_target (f := e.1.1) (congrArg (fun w => w.1.1) ht)
    exact hnd (unrooted_edge_ext hh ▸ hd)

/-- **A taxon descending from the hybrid node of a cycle is in its block** (the inclusion `⊇` of
`mem_nodeBlock_iff_descendsFrom`): a semidirected path from the hybrid node cannot leave it along
the cycle, and cannot come back to the cycle (`walks_compl_of_isSDPathOf`). -/
theorem mem_nodeBlock_of_descendsFrom (h1 : IsLevelOne N.graph)
    {C : Set (SemidirectedArc hN.1 hN.2 hX)} (hC : IsCycle (unrooted N hN hX).graph C)
    {v : SemidirectedVertex hN.1 hX} (hv : IsHybridNodeOf (unrooted N hN hX) C v) {x : X}
    (hx : DescendsFrom (unrooted N hN hX) v x) :
    x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C v := by
  obtain ⟨-, -, k, p, q, hP, h0, hlast, -, -⟩ := hx
  have := walks_compl_of_isSDPathOf (hv.not_sdStep hC) (fun u hu huw =>
    ((unrooted_isLevelOne hN h1 hX).eq_of_walks_compl hC hv.mem_cycleNodes hu huw).symm) hP h0
    (Fin.last k)
  rw [hlast] at this
  exact this

/-- **A taxon in the block of the hybrid node `v` of a cycle `C` is below `v` in `N`**: the vertices
of `N⁻` below `v` in `N` are entered from outside only at `v`
(`reaches_source_of_below_hybrid`), by the hybrid edges of `v`, which are in `C`; so no edge
outside `C` crosses the cut they make. -/
theorem reaches_of_mem_nodeBlock_hybrid (h1 : IsLevelOne N.graph)
    {C : Set (SemidirectedArc hN.1 hN.2 hX)} {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) {x : X}
    (hx : x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C v) :
    N.graph.Reaches v.1.1 (N.leaf x) := by
  have h2 := hv.unrooted_indegree
  have hvm : ¬ N.graph.Reaches v.1.1 (lsa hN.1 Set.univ Set.univ_nonempty) := fun h =>
    unrooted_node_ne_lsa v (eq_of_reaches_of_reaches hN.1.acyclic h v.1.2.1)
  -- an arc entering a vertex below `v` from a vertex not below `v` enters `v`
  have hin : ∀ f : E, N.graph.Reaches v.1.1 (N.graph.target f) →
      ¬ N.graph.Reaches v.1.1 (N.graph.source f) → N.graph.target f = v.1.1 := fun f ht hs => by
    by_contra hne
    exact hs (reaches_source_of_below_hybrid hN h1 h2 ht hne)
  let S : Set (SemidirectedVertex hN.1 hX) := {w | N.graph.Reaches v.1.1 w.1.1}
  have hcut : ∀ c ∈ Cᶜ, ¬ (unrooted N hN hX).graph.Crosses c S := by
    intro c hc hcross
    -- an edge of `N⁻` entering `v` in `N` is in `C`
    have hcv : N.graph.target c.1.1 ≠ v.1.1 := fun hf => by
      obtain ⟨h, hhC, -, hh⟩ := hv.exists_mem_of_target hf
      exact hc (unrooted_edge_ext hh ▸ hhC)
    by_cases hm : N.graph.source c.1.1 = lsa hN.1 Set.univ Set.univ_nonempty
    · have hs := unrooted_source_val_of_eq hN c hm
      rcases hcross with ⟨h₁, -⟩ | ⟨h₁, -⟩
      · -- the child of `rootTreeArc` is below `v`, so it is `v`, which has no tree arc
        have h₁' : N.graph.Reaches v.1.1 ((unrooted N hN hX).graph.source c).1.1 := h₁
        rw [hs] at h₁'
        have he₀ : N.graph.source (rootTreeArc hN.1 hN.2 hX).1 =
            lsa hN.1 Set.univ Set.univ_nonempty :=
          congrArg Subtype.val (rootTreeArc_spec hN.1 hN.2 hX).1
        obtain ⟨h, -, -, hh⟩ := hv.exists_mem_of_target (hin _ h₁' (by rw [he₀]; exact hvm))
        exact h.2 (Subtype.ext hh)
      · exact hcv (hin _ h₁ (by rw [hm]; exact hvm))
    · have hs := unrooted_source_val_of_ne hN c hm
      rcases hcross with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have h₁' : N.graph.Reaches v.1.1 ((unrooted N hN hX).graph.source c).1.1 := h₁
        rw [hs] at h₁'
        exact h₂ (h₁'.tail ⟨c.1.1, rfl, rfl⟩)
      · have h₂' : ¬ N.graph.Reaches v.1.1 ((unrooted N hN hX).graph.source c).1.1 := h₂
        rw [hs] at h₂'
        exact hcv (hin _ h₁ h₂')
  exact ((unrooted N hN hX).graph.mem_iff_mem_of_walks hcut hx).mp
    (Relation.ReflTransGen.refl : N.graph.Reaches v.1.1 v.1.1)


/-! ### The other nodes of a cycle of `N⁻` -/

/-- **A node of a cycle of `N⁻` entered by two arcs of `N` is the hybrid node of the cycle**: both
arcs are below the LSA, they are hybrid edges of `N⁻` (neither is the tree arc `rootTreeArc`), and
the hybrid edges entering a node of the cycle are in the cycle (Lemma 3). -/
theorem isHybridNodeOf_of_indegree (h1 : IsLevelOne N.graph)
    {C : Set (SemidirectedArc hN.1 hN.2 hX)} (hC : IsCycle (unrooted N hN hX).graph C)
    {u : SemidirectedVertex hN.1 hX} (hu : u ∈ cycleNodes (unrooted N hN hX).graph C)
    (h2 : N.graph.indegree u.1.1 = 2) : IsHybridNodeOf (unrooted N hN hX) C u := by
  obtain ⟨p₁, p₂, hne, hs⟩ := Set.ncard_eq_two.mp h2
  have hp₁ : N.graph.target p₁ = u.1.1 := by
    have : p₁ ∈ {f | N.graph.target f = u.1.1} := by rw [hs]; exact Or.inl rfl
    exact this
  have hp₂ : N.graph.target p₂ = u.1.1 := by
    have : p₂ ∈ {f | N.graph.target f = u.1.1} := by rw [hs]; exact Or.inr rfl
    exact this
  have hst := (lsa_spec hN.1 Set.univ Set.univ_nonempty).1
  have hmem₁ := mem_belowArcs_of_target hN.1 hst u.1 (unrooted_node_ne_lsa u) hp₁
  have hmem₂ := mem_belowArcs_of_target hN.1 hst u.1 (unrooted_node_ne_lsa u) hp₂
  -- in `𝒩⊕`, both arcs enter `u`
  have hM2 : 2 ≤ (lsaPlus hN.1 hX).graph.indegree u.1 :=
    two_le_indegree_of_ne_targets (G := (lsaPlus hN.1 hX).graph) (e := ⟨p₁, hmem₁⟩)
      (e' := ⟨p₂, hmem₂⟩) (fun h => hne (congrArg Subtype.val h)) (Subtype.ext hp₁)
      (Subtype.ext hp₂)
  have htree := (rootTreeArc_spec hN.1 hN.2 hX).2
  unfold IsTreeArc at htree
  have hq : ∀ (p : E) (hp : p ∈ N.belowArcs (lsa hN.1 Set.univ Set.univ_nonempty) Set.univ),
      N.graph.target p = u.1.1 → (⟨p, hp⟩ : N.belowArcs _ _) ≠ rootTreeArc hN.1 hN.2 hX := by
    intro p hp hpt h
    have : (lsaPlus hN.1 hX).graph.target (rootTreeArc hN.1 hN.2 hX) = u.1 := by
      rw [← h]
      exact Subtype.ext hpt
    rw [this] at htree
    omega
  let q₁ : SemidirectedArc hN.1 hN.2 hX := ⟨⟨p₁, hmem₁⟩, hq p₁ hmem₁ hp₁⟩
  let q₂ : SemidirectedArc hN.1 hN.2 hX := ⟨⟨p₂, hmem₂⟩, hq p₂ hmem₂ hp₂⟩
  have hqt₁ : (unrooted N hN hX).graph.target q₁ = u := unrooted_node_ext hp₁
  have hqt₂ : (unrooted N hN hX).graph.target q₂ = u := unrooted_node_ext hp₂
  have hd : ∀ q : SemidirectedArc hN.1 hN.2 hX, (unrooted N hN hX).graph.target q = u →
      (unrooted N hN hX).IsDirected q := fun q hq => by
    show 2 ≤ (lsaPlus hN.1 hX).graph.indegree ((lsaPlus hN.1 hX).graph.target q.1)
    rw [show (lsaPlus hN.1 hX).graph.target q.1 = u.1 from congrArg Subtype.val hq]
    exact hM2
  have hC2 := (lemma3_unrooted hN h1 hX hC).2.1 u hu
  exact ⟨q₁, hC2 q₁ (hd q₁ hqt₁) hqt₁, q₂, hC2 q₂ (hd q₂ hqt₂) hqt₂,
    fun h => hne (congrArg (fun c => c.1.1) h), hd q₁ hqt₁, hd q₂ hqt₂, hqt₁, hqt₂⟩

/-- **A node of a cycle with a child off the cycle has a taxon in its block**: below the child, a
directed path of `N` reaches a taxon; it does not come back to `u`, so it never meets the cycle. -/
theorem nodeBlock_nonempty_of_child (h1 : IsLevelOne N.graph)
    {C : Set (SemidirectedArc hN.1 hN.2 hX)} (hC : IsCycle (unrooted N hN hX).graph C)
    {u : SemidirectedVertex hN.1 hX} (hu : u ∈ cycleNodes (unrooted N hN hX).graph C)
    {c : SemidirectedArc hN.1 hN.2 hX} (hcs : N.graph.source c.1.1 = u.1.1) (hc : c ∉ C) :
    (nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u).Nonempty := by
  have h1G := unrooted_isLevelOne hN h1 hX
  have hsrc : (unrooted N hN hX).graph.source c = u := unrooted_node_ext
    ((unrooted_source_val_of_ne hN c (hcs ▸ unrooted_node_ne_lsa u)).trans hcs)
  have key : ∀ b, N.graph.Reaches (N.graph.target c.1.1) b →
      ∃ w, (unrooted N hN hX).graph.Walks Cᶜ u w ∧ w.1.1 = b := by
    intro b hb
    induction hb with
    | refl => exact ⟨_, Relation.ReflTransGen.single ⟨c, hc, Or.inl ⟨hsrc, rfl⟩⟩, rfl⟩
    | @tail a b hca hab ih =>
      obtain ⟨w, hw, rfl⟩ := ih
      obtain ⟨f, hfs, hft⟩ := hab
      obtain ⟨d, rfl, hds, hdt⟩ := exists_unrooted_edge hN w hfs
      have hwu : w ≠ u := by
        rintro rfl
        exact hN.1.acyclic _ (Relation.TransGen.head' ⟨c.1.1, hcs, rfl⟩ hca)
      exact ⟨_, (h1G.walks_compl_ends hC hu hw hwu (Or.inl hds)).2, hdt.trans hft⟩
  obtain ⟨x, hx⟩ := exists_reaches_leaf hN.1 (N.graph.target c.1.1)
  obtain ⟨w, hw, hwx⟩ := key _ hx
  obtain rfl : w = (unrooted N hN hX).leaf x := unrooted_node_ext hwx
  exact ⟨x, hw⟩

/-- **A node of a cycle whose edges in the cycle leave it has a taxon in its block**: here every
edge of `C` at `u` is an arc of `N` leaving `u`. The node `u` is not the LSA, so it is not a stable
ancestor of the taxa, and a path of `N` from the LSA avoids `u` down to a taxon. The vertices of a
path from the LSA down to `u`, the two children of the LSA (joined by the merged edge), and then the
vertices of the path avoiding `u` are all joined to `u` by walks avoiding `C`: away from `u` no edge
of `C` is met, and at `u` these walks use only edges not leaving `u` in `N`. -/
theorem nodeBlock_nonempty_of_parents (h1 : IsLevelOne N.graph)
    {C : Set (SemidirectedArc hN.1 hN.2 hX)} (hC : IsCycle (unrooted N hN hX).graph C)
    {u : SemidirectedVertex hN.1 hX} (hu : u ∈ cycleNodes (unrooted N hN hX).graph C)
    (hup : ∀ f : SemidirectedArc hN.1 hN.2 hX,
      ((unrooted N hN hX).graph.source f = u ∨ (unrooted N hN hX).graph.target f = u) →
        N.graph.source f.1.1 ≠ u.1.1 → f ∉ C) :
    (nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u).Nonempty := by
  have h1G := unrooted_isLevelOne hN h1 hX
  have := hX
  set m := lsa hN.1 Set.univ Set.univ_nonempty with hm
  have hst := lsa_spec hN.1 Set.univ Set.univ_nonempty
  have he₀s : N.graph.source (rootTreeArc hN.1 hN.2 hX).1 = m :=
    congrArg Subtype.val (rootTreeArc_spec hN.1 hN.2 hX).1
  -- the vertices on a path from the LSA to `u`, below the LSA, are joined to `u` avoiding `C`
  have hupw : ∀ a, N.graph.Reaches a u.1.1 → N.graph.Reaches m a → a ≠ m →
      ∃ w, (unrooted N hN hX).graph.Walks Cᶜ u w ∧ w.1.1 = a := by
    intro a ha
    induction ha using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ _ => ⟨u, .refl, rfl⟩
    | @head a c hac hcu ih =>
      intro hma ham
      obtain ⟨f, hfs, hft⟩ := hac
      have hmc : N.graph.Reaches m c := hma.tail ⟨f, hfs, hft⟩
      have hcm : c ≠ m := by
        rintro rfl
        exact hN.1.acyclic _ (Relation.TransGen.tail' hma ⟨f, hfs, hft⟩)
      obtain ⟨wc, hwc, hwcc⟩ := ih hmc hcm
      obtain ⟨wa, rfl⟩ := exists_unrooted_node (hX := hX) hN.1 hma ham
      obtain ⟨d, rfl, hds, hdt⟩ := exists_unrooted_edge hN wa hfs
      have hdt' : (unrooted N hN hX).graph.target d = wc :=
        unrooted_node_ext (hdt.trans (hft.trans hwcc.symm))
      have hdC : d ∉ C := by
        by_cases hwcu : wc = u
        · have hdu : (unrooted N hN hX).graph.target d = u := hdt'.trans hwcu
          refine hup d (Or.inr hdu) fun h => ?_
          have hdt'' : N.graph.target d.1.1 = u.1.1 := congrArg (fun w => w.1.1) hdu
          exact hN.1.acyclic _ (.single ⟨d.1.1, rfl, hdt''.trans h.symm⟩)
        · exact h1G.notMem_of_walks_compl hC hu hwc hwcu (Or.inr hdt')
      exact ⟨wa, hds ▸ (walks_compl_ends_of_notMem hwc (Or.inr hdt') hdC).1, rfl⟩
  -- the first arc of a path from the LSA to `u`
  obtain ⟨b₁, f₁, hf₁s, hf₁t, hb₁u⟩ : ∃ b f, N.graph.source f = m ∧ N.graph.target f = b ∧
      N.graph.Reaches b u.1.1 := by
    rcases Relation.ReflTransGen.cases_head u.1.2.1 with h | ⟨b, ⟨f, hfs, hft⟩, hb⟩
    · exact absurd h.symm (unrooted_node_ne_lsa u)
    · exact ⟨b, f, hfs, hft, hb⟩
  have hb₁m : b₁ ≠ m := by
    rintro rfl
    exact hN.1.acyclic _ (.single ⟨f₁, hf₁s, hf₁t⟩)
  obtain ⟨w₁, hw₁, hw₁b⟩ := hupw b₁ hb₁u (.single ⟨f₁, hf₁s, hf₁t⟩) hb₁m
  -- the edge of `N⁻` merging the two arcs leaving the LSA
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : SemidirectedArc hN.1 hN.2 hX, N.graph.source c₀.1.1 = m := by
    obtain ⟨g₁, g₂, hne, hs⟩ := Set.ncard_eq_two.mp (lsaPlus_outdegree_root hN.1 hN.2 hX)
    have hg₁ : (lsaPlus hN.1 hX).graph.source g₁ = (lsaPlus hN.1 hX).root := by
      have : g₁ ∈ {f | (lsaPlus hN.1 hX).graph.source f = (lsaPlus hN.1 hX).root} := by
        rw [hs]; exact Or.inl rfl
      exact this
    have hg₂ : (lsaPlus hN.1 hX).graph.source g₂ = (lsaPlus hN.1 hX).root := by
      have : g₂ ∈ {f | (lsaPlus hN.1 hX).graph.source f = (lsaPlus hN.1 hX).root} := by
        rw [hs]; exact Or.inr rfl
      exact this
    by_cases h : g₁ = rootTreeArc hN.1 hN.2 hX
    · exact ⟨⟨g₂, fun h' => hne (h.trans h'.symm)⟩, congrArg Subtype.val hg₂⟩
    · exact ⟨⟨g₁, h⟩, congrArg Subtype.val hg₁⟩
  have hm_arcs : ∀ g : E, N.graph.source g = m → g = (rootTreeArc hN.1 hN.2 hX).1 ∨ g = c₀.1.1 := by
    intro g hg
    by_contra hcon
    push Not at hcon
    have hne : (rootTreeArc hN.1 hN.2 hX).1 ≠ c₀.1.1 := fun h => c₀.2 (Subtype.ext h).symm
    have hsub : ({(rootTreeArc hN.1 hN.2 hX).1, c₀.1.1, g} : Set E) ⊆
        {f | N.graph.source f = m} := by
      rintro f (rfl | rfl | rfl)
      · exact he₀s
      · exact hc₀
      · exact hg
    have h3 : ({(rootTreeArc hN.1 hN.2 hX).1, c₀.1.1, g} : Set E).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hcon.2)]
      rintro (h | h)
      · exact hne h
      · exact hcon.1 h.symm
    have := h3 ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
    have := hN.outdegree_le_two m
    unfold DirectedMultigraph.outdegree at *
    omega
  -- both children of the LSA are joined to `u` avoiding `C`
  have hends : (unrooted N hN hX).graph.Walks Cᶜ u ((unrooted N hN hX).graph.source c₀) ∧
      (unrooted N hN hX).graph.Walks Cᶜ u ((unrooted N hN hX).graph.target c₀) := by
    have hinc : (unrooted N hN hX).graph.source c₀ = w₁ ∨
        (unrooted N hN hX).graph.target c₀ = w₁ := by
      rcases hm_arcs f₁ hf₁s with rfl | rfl
      · exact Or.inl (unrooted_node_ext
          ((unrooted_source_val_of_eq hN c₀ hc₀).trans (hf₁t.trans hw₁b.symm)))
      · exact Or.inr (unrooted_node_ext (hf₁t.trans hw₁b.symm))
    have hc₀C : c₀ ∉ C := by
      by_cases hwu : w₁ = u
      · exact hup c₀ (hwu ▸ hinc) (by rw [hc₀]; exact (unrooted_node_ne_lsa u).symm)
      · exact h1G.notMem_of_walks_compl hC hu hw₁ hwu hinc
    exact walks_compl_ends_of_notMem hw₁ hinc hc₀C
  -- a taxon reached from the LSA by a path avoiding `u`
  have hnst : ¬ N.IsStableAncestor Set.univ u.1.1 := fun h =>
    unrooted_node_ne_lsa u (eq_of_reaches_of_reaches hN.1.acyclic (hst.2 _ h) u.1.2.1)
  obtain ⟨x, hx⟩ : ∃ x, N.HasPathAvoiding N.root (N.leaf x) u.1.1 := by
    by_contra hcon
    push Not at hcon
    exact hnst fun x _ => hcon x
  obtain ⟨-, -, hpath⟩ := hx.suffix_of_not_hasPathAvoiding (hst.1 x (Set.mem_univ x))
  have key : ∀ b, Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ u.1.1 ∧ b ≠ u.1.1) m b →
      b = m ∨ ∃ w, (unrooted N hN hX).graph.Walks Cᶜ u w ∧ w.1.1 = b := by
    intro b hb
    induction hb with
    | refl => exact Or.inl rfl
    | @tail a b _ hab ih =>
      obtain ⟨⟨f, hfs, hft⟩, hau, -⟩ := hab
      right
      rcases ih with rfl | ⟨wa, hwa, rfl⟩
      · rcases hm_arcs f hfs with rfl | rfl
        · exact ⟨_, hends.1, (unrooted_source_val_of_eq hN c₀ hc₀).trans hft⟩
        · exact ⟨_, hends.2, hft⟩
      · obtain ⟨d, rfl, hds, hdt⟩ := exists_unrooted_edge hN wa hfs
        have hwau : wa ≠ u := fun h => hau (congrArg (fun w => w.1.1) h)
        exact ⟨_, (h1G.walks_compl_ends hC hu hwa hwau (Or.inl hds)).2, hdt.trans hft⟩
  rcases key _ hpath with h | ⟨w, hw, hwx⟩
  · exact absurd h (hst.1.leaf_ne hN.1 Set.nontrivial_univ x)
  · obtain rfl : w = (unrooted N hN hX).leaf x := unrooted_node_ext hwx
    exact ⟨x, hw⟩

end CycleNodes

section HybridBlock

variable {N : RootedNetwork V E X} [Finite E] {hN : IsBinaryRootedNetwork N} {hX : Nontrivial X}

/-- **Every node of a cycle of `N⁻` has a taxon in its block**: what hangs from the node, off the
cycle, ends at taxa. -/
theorem nodeBlock_nonempty_unrooted (h1 : IsLevelOne N.graph) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {u} (hu : u ∈ cycleNodes (unrooted N hN hX).graph C) :
    (nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u).Nonempty := by
  obtain ⟨v, hv⟩ := exists_isHybridNodeOf h1 hC
  -- the hybrid node: a taxon below it descends from it
  by_cases huv : u = v
  · subst huv
    obtain ⟨x, hx⟩ := exists_reaches_leaf hN.1 u.1.1
    exact ⟨x, mem_nodeBlock_of_descendsFrom h1 hC hv (descendsFrom_of_reaches hN u hx)⟩
  -- a taxon
  by_cases hleaf : ∃ y, N.leaf y = u.1.1
  · obtain ⟨y, hy⟩ := hleaf
    obtain rfl : u = (unrooted N hN hX).leaf y := unrooted_node_ext hy.symm
    exact ⟨y, .refl⟩
  push Not at hleaf
  -- otherwise a tree node of `N`, with two children
  have hur : u.1.1 ≠ N.root := fun h => unrooted_node_ne_lsa u
    (eq_of_reaches_of_reaches hN.1.acyclic (by rw [h]; exact hN.1.root_reaches _) u.1.2.1)
  have hout : N.graph.outdegree u.1.1 ≠ 0 := fun h => by
    obtain ⟨y, hy⟩ := (hN.1.leaves _).mp h
    exact hleaf y hy
  have hin : N.graph.indegree u.1.1 ≠ 2 := fun h2 =>
    huv ((isHybridNodeOf_of_indegree h1 hC hu h2).eq h1 hC hv)
  have hout2 : N.graph.outdegree u.1.1 = 2 := by
    have := hN.2.2 _ hur hout
    have := hN.1.nonroot_indegree _ hur
    have := hN.indegree_le_two u.1.1
    omega
  by_cases hdown : ∃ c : SemidirectedArc hN.1 hN.2 hX, N.graph.source c.1.1 = u.1.1 ∧ c ∉ C
  · obtain ⟨c, hcs, hc⟩ := hdown
    exact nodeBlock_nonempty_of_child h1 hC hu hcs hc
  push Not at hdown
  -- both children are on the cycle, so the edges of `C` at `u` are the two leaving it
  refine nodeBlock_nonempty_of_parents h1 hC hu fun f hf hfs hfC => ?_
  have hinc := hC.ncard_incident (unrooted_source_ne_target hN) hu
  obtain ⟨g₁, g₂, hne, hs⟩ := Set.ncard_eq_two.mp hout2
  have hg₁ : N.graph.source g₁ = u.1.1 := by
    have : g₁ ∈ {f | N.graph.source f = u.1.1} := by rw [hs]; exact Or.inl rfl
    exact this
  have hg₂ : N.graph.source g₂ = u.1.1 := by
    have : g₂ ∈ {f | N.graph.source f = u.1.1} := by rw [hs]; exact Or.inr rfl
    exact this
  obtain ⟨c₁, rfl, hc₁s, -⟩ := exists_unrooted_edge hN u hg₁
  obtain ⟨c₂, rfl, hc₂s, -⟩ := exists_unrooted_edge hN u hg₂
  have hsub : ({f, c₁, c₂} : Set _) ⊆ {e | e ∈ C ∧ ((unrooted N hN hX).graph.source e = u ∨
      (unrooted N hN hX).graph.target e = u)} := by
    rintro e (rfl | rfl | rfl)
    · exact ⟨hfC, hf⟩
    · exact ⟨hdown _ hg₁, Or.inl hc₁s⟩
    · exact ⟨hdown _ hg₂, Or.inl hc₂s⟩
  have h3 : ({f, c₁, c₂} : Set (SemidirectedArc hN.1 hN.2 hX)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair fun h => hne (congrArg (fun c => c.1.1) h)]
    rintro (rfl | rfl)
    · exact hfs hg₁
    · exact hfs hg₂
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- **The block of the hybrid node is the set of taxa descending from it**: a semidirected path from
the hybrid node leaves it by its child edge and does not come back to the cycle. -/
theorem mem_nodeBlock_iff_descendsFrom (h1 : IsLevelOne N.graph) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (x : X) :
    x ∈ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C v ↔
      DescendsFrom (unrooted N hN hX) v x :=
  ⟨fun hx => descendsFrom_of_reaches hN v (reaches_of_mem_nodeBlock_hybrid h1 hv hx),
    mem_nodeBlock_of_descendsFrom h1 hC hv⟩

end HybridBlock

end Banos2019
