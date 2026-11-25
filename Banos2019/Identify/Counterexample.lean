module

public import Banos2019.Identify.QuartetCycles
public import Banos2019.Quartet.Examples
public import Banos2019.Quartet.Transfer

/-!
# Proposition 13 as printed fails (Baños 2019, Section 9)

A binary level-1 network with a 4-cycle `C_v` and a 3-cycle above it: for the taxa `a, b, c, d` in
the four blocks of `C_v` and a fifth taxon `e` in the block of `a`, the quartet network on
`{a, b, c, e}` has no 4-cycle and a `3₂`-cycle from the 3-cycle, so on an open set of parameters
`{a, b, c, e}` satisfies the Cycle property but not the Big Cycle property, while `e` is not in the
hybrid block of `C_v`.

* `cexNet`: the network, with `cexNet_isBinaryRootedNetwork` and `cexNet_isLevelOne` (its cycles are
  the 3-cycle `t, p, u` and the 4-cycle `w, x, v, y`, `cexNet_cycle_eq`).
* `cexCv`, `cexV`: the 4-cycle `C_v` of `N⁻` and its hybrid node; `cex_blocks`: `a, b, c, d` are in
  its four blocks; `cex_not_descendsFrom`: `e` does not descend from `v`.
* `cex_inducesNetwork`: `Q⁻_{abce}` is Figure 18, with taxa `b, c, e, a`; `cex_cf`: the concordance
  factors of Example 5 on `{a, b, c, e}`.
* `cex_not_forGenericParams`, `proposition13AsPrinted_counterexample`: the parameters near those of
  Example 6 form an open set on which the conclusion of Proposition 13 as printed fails.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-! ### The network

The taxa `a, b, c, d, e` are `0, 1, 2, 3, 4` of `Fin 5`, at the vertices `0, …, 4`; the other
vertices are `r = 5`, `t = 6`, `p = 7`, `u = 8`, `w = 9`, `x = 10`, `y = 11`, `v = 12`. The arcs are
`0: r → a`, `1: r → t`, `2: t → p`, `3: t → u`, `4: p → e`, `5: p → u`, `6: u → w`, `7: w → x`,
`8: w → y`, `9: x → b`, `10: x → v`, `11: y → c`, `12: y → v`, `13: v → d`. -/

/-- The tails of the arcs of the counterexample. -/
def cexSrc : Fin 14 → Fin 13 := ![5, 5, 6, 6, 7, 7, 8, 9, 9, 10, 10, 11, 11, 12]

/-- The heads of the arcs of the counterexample. -/
def cexTgt : Fin 14 → Fin 13 := ![0, 6, 7, 8, 4, 8, 9, 10, 11, 1, 12, 2, 12, 3]

/-- **The counterexample network**, with hybrid nodes `u` (parents `t`, `p`) and `v` (parents `x`,
`y`). -/
def cexNet : RootedNetwork (Fin 13) (Fin 14) (Fin 5) :=
  ⟨⟨cexSrc, cexTgt⟩, 5, ![0, 1, 2, 3, 4]⟩

theorem cexNet_indegree (v : Fin 13) :
    cexNet.graph.indegree v = (univ.filter fun e => cexTgt e = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [cexNet]

theorem cexNet_outdegree (v : Fin 13) :
    cexNet.graph.outdegree v = (univ.filter fun e => cexSrc e = v).card := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [cexNet]

theorem cexNet_adj {i : Fin 14} : cexNet.graph.Adj (cexSrc i) (cexTgt i) := ⟨i, rfl, rfl⟩

/-- A path from the head of an arc extends to its tail. -/
theorem cexNet_reaches_of_arc (i : Fin 14) {w : Fin 13} (h : cexNet.graph.Reaches (cexTgt i) w) :
    cexNet.graph.Reaches (cexSrc i) w :=
  Relation.ReflTransGen.head cexNet_adj h

/-- The vertices below `u ∈ D` stay in `D` when `D` is closed under children. -/
theorem cexNet_reaches_mem {D : Finset (Fin 13)} (hD : ∀ e, cexSrc e ∈ D → cexTgt e ∈ D)
    {u w : Fin 13} (hu : u ∈ D) (h : cexNet.graph.Reaches u w) : w ∈ D := by
  induction h with
  | refl => exact hu
  | @tail p q _ hpq ih =>
    obtain ⟨e, rfl, rfl⟩ := hpq
    exact hD e ih

theorem cexNet_root_reaches (v : Fin 13) : cexNet.graph.Reaches 5 v := by
  have r0 : cexNet.graph.Reaches 5 0 := cexNet_reaches_of_arc 0 .refl
  have r6 : cexNet.graph.Reaches 5 6 := cexNet_reaches_of_arc 1 .refl
  have r7 : cexNet.graph.Reaches 5 7 := r6.tail (cexNet_adj (i := 2))
  have r8 : cexNet.graph.Reaches 5 8 := r6.tail (cexNet_adj (i := 3))
  have r4 : cexNet.graph.Reaches 5 4 := r7.tail (cexNet_adj (i := 4))
  have r9 : cexNet.graph.Reaches 5 9 := r8.tail (cexNet_adj (i := 6))
  have r10 : cexNet.graph.Reaches 5 10 := r9.tail (cexNet_adj (i := 7))
  have r11 : cexNet.graph.Reaches 5 11 := r9.tail (cexNet_adj (i := 8))
  have r1 : cexNet.graph.Reaches 5 1 := r10.tail (cexNet_adj (i := 9))
  have r12 : cexNet.graph.Reaches 5 12 := r10.tail (cexNet_adj (i := 10))
  have r2 : cexNet.graph.Reaches 5 2 := r11.tail (cexNet_adj (i := 11))
  have r3 : cexNet.graph.Reaches 5 3 := r12.tail (cexNet_adj (i := 13))
  fin_cases v
  exacts [r0, r1, r2, r3, r4, .refl, r6, r7, r8, r9, r10, r11, r12]

theorem cexNet_isPhylogenetic : cexNet.IsPhylogenetic where
  finite_vertices := inferInstance
  finite_arcs := inferInstance
  finite_taxa := inferInstance
  acyclic := DirectedMultigraph.isAcyclic_of_rank _
    (fun v : Fin 13 => ![7, 7, 7, 7, 7, 0, 1, 2, 3, 4, 5, 5, 6] v)
    (by show ∀ e, ![7, 7, 7, 7, 7, 0, 1, 2, 3, 4, 5, 5, 6] (cexSrc e) <
          ![7, 7, 7, 7, 7, 0, 1, 2, 3, 4, 5, 5, 6] (cexTgt e)
        decide)
  root_reaches := cexNet_root_reaches
  root_indegree := by
    rw [cexNet_indegree]
    decide
  nonroot_indegree v hv := by
    rw [cexNet_indegree]
    revert v
    decide
  leaf_injective := by
    show Function.Injective (![0, 1, 2, 3, 4] : Fin 5 → Fin 13)
    decide
  leaf_indegree x := by
    rw [cexNet_indegree]
    revert x
    decide
  leaves v := by
    rw [cexNet_outdegree]
    show _ ↔ ∃ x, (![0, 1, 2, 3, 4] : Fin 5 → Fin 13) x = v
    revert v
    decide

theorem cexNet_isBinary : cexNet.IsBinary := by
  refine ⟨by rw [cexNet_outdegree]; decide, fun v hv h0 => ?_⟩
  rw [cexNet_indegree, cexNet_outdegree]
  rw [cexNet_outdegree] at h0
  revert v
  decide

theorem cexNet_isBinaryRootedNetwork : IsBinaryRootedNetwork cexNet :=
  ⟨cexNet_isPhylogenetic, cexNet_isBinary⟩

theorem cexNet_isHybridArc_iff (e : Fin 14) :
    cexNet.IsHybridArc e ↔ e ∈ ({3, 5, 10, 12} : Finset (Fin 14)) := by
  unfold IsHybridArc
  rw [cexNet_indegree]
  show 2 ≤ #(univ.filter fun f => cexTgt f = cexTgt e) ↔ _
  revert e
  decide

theorem cexNet_isTreeArc_iff (e : Fin 14) :
    cexNet.IsTreeArc e ↔ e ∉ ({3, 5, 10, 12} : Finset (Fin 14)) := by
  unfold IsTreeArc
  rw [cexNet_indegree]
  show #(univ.filter fun f => cexTgt f = cexTgt e) = 1 ↔ _
  revert e
  decide

/-- The root `r` is the LSA of every set of taxa containing `a` and `e`: the path `r → a` avoids
every vertex but `r, a`, and the path `r → t → p → e` avoids `a`. -/
theorem cexNet_isLeastStableAncestor {Y : Set (Fin 5)} (ha : 0 ∈ Y) (he : 4 ∈ Y) :
    cexNet.IsLeastStableAncestor Y 5 := by
  refine ⟨root_isStableAncestor _ _, fun w hw => ?_⟩
  suffices hw5 : w = 5 by rw [hw5]; exact .refl
  by_contra hne
  by_cases hw0 : w = 0
  · subst hw0
    refine hw 4 he ⟨by decide, by decide, ?_⟩
    refine ((Relation.ReflTransGen.single ⟨cexNet_adj (i := 1), by decide, by decide⟩).tail
      ⟨cexNet_adj (i := 2), by decide, by decide⟩).tail ⟨cexNet_adj (i := 4), by decide, by decide⟩
  · exact hw 0 ha ⟨Ne.symm hne, Ne.symm hw0, Relation.ReflTransGen.single
      ⟨cexNet_adj (i := 0), Ne.symm hne, Ne.symm hw0⟩⟩

theorem cexNet_lsa_univ :
    lsa cexNet_isPhylogenetic Set.univ Set.univ_nonempty = 5 :=
  IsLeastStableAncestor.unique cexNet_isPhylogenetic (lsa_spec _ _ _)
    (cexNet_isLeastStableAncestor (Set.mem_univ _) (Set.mem_univ _))

/-! ### Level-1

The arcs `0, 1, 4, 6, 9, 11, 13` are cut edges, so they are on no cycle; a cut around `t, p, u`
separates the arcs `2, 3, 5` of the 3-cycle from the arcs `7, 8, 10, 12` of the 4-cycle, and each
node of a cycle is on exactly two of its edges. -/

section LevelOne

variable {V E : Type*} {G : DirectedMultigraph V E}

/-- An edge that is the only edge crossing a cut is on no cycle. -/
theorem IsCycle.notMem_of_crosses {C : Set E} (hC : IsCycle G C) {f : E} {S : Set V}
    (hS : ∀ g, g ≠ f → ¬ G.Crosses g S) (hf : G.Crosses f S) : f ∉ C := fun h => by
  have := G.mem_iff_mem_of_walks (fun g hg => hS g hg) (hC.walks_compl_singleton h)
  unfold DirectedMultigraph.Crosses at hf
  tauto

end LevelOne

theorem cexNet_crosses_iff (g : Fin 14) (S : Finset (Fin 13)) :
    cexNet.graph.Crosses g ↑S ↔
      (cexSrc g ∈ S ∧ cexTgt g ∉ S) ∨ (cexTgt g ∈ S ∧ cexSrc g ∉ S) :=
  Iff.rfl

/-- The side of the cut edge `f` below it. -/
def cexCut (f : Fin 14) : Finset (Fin 13) :=
  if f = 0 then {0} else if f = 1 then {1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12}
  else if f = 4 then {4} else if f = 6 then {1, 2, 3, 9, 10, 11, 12}
  else if f = 9 then {1} else if f = 11 then {2} else {3}

/-- The edges of the 3-cycle `t, p, u`. -/
def cexTri : Finset (Fin 14) := {2, 3, 5}

/-- The edges of the 4-cycle `w, x, v, y`. -/
def cexSq : Finset (Fin 14) := {7, 8, 10, 12}

theorem cexNet_cycle_subset {C : Set (Fin 14)} (hC : IsCycle cexNet.graph C) :
    C ⊆ ↑(cexTri ∪ cexSq) := by
  intro f hf
  by_contra hfC
  have key : ∀ f : Fin 14, f ∉ cexTri ∪ cexSq →
      (∀ g, g ≠ f → ¬ ((cexSrc g ∈ cexCut f ∧ cexTgt g ∉ cexCut f) ∨
        (cexTgt g ∈ cexCut f ∧ cexSrc g ∉ cexCut f))) ∧
      ((cexSrc f ∈ cexCut f ∧ cexTgt f ∉ cexCut f) ∨
        (cexTgt f ∈ cexCut f ∧ cexSrc f ∉ cexCut f)) := by decide
  obtain ⟨h₁, h₂⟩ := key f hfC
  exact hC.notMem_of_crosses (S := ↑(cexCut f))
    (fun g hg => (cexNet_crosses_iff g _).not.2 (h₁ g hg)) ((cexNet_crosses_iff f _).2 h₂) hf

/-- The edges of a cycle that meet a node of it: exactly two. -/
theorem cexNet_card_incident {C : Set (Fin 14)} (hC : IsCycle cexNet.graph C) {f : Fin 14}
    (hf : f ∈ C) {z : Fin 13} (hz : cexSrc f = z ∨ cexTgt f = z) :
    ((univ.filter (· ∈ C)).filter fun e => cexSrc e = z ∨ cexTgt e = z).card = 2 := by
  have hloop : ∀ e, cexNet.graph.source e ≠ cexNet.graph.target e := by
    show ∀ e, cexSrc e ≠ cexTgt e
    decide
  have h := hC.ncard_incident hloop ⟨f, hf, hz⟩
  rw [← h, ← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [cexNet]

/-- **The cycles of the counterexample** are the 3-cycle `t, p, u` and the 4-cycle `w, x, v, y`. -/
theorem cexNet_cycle_eq {C : Set (Fin 14)} (hC : IsCycle cexNet.graph C) :
    C = ↑cexTri ∨ C = ↑cexSq := by
  have hsub := cexNet_cycle_subset hC
  set Cf := univ.filter (· ∈ C) with hCf
  have hCeq : C = ↑Cf := by
    ext f
    simp [Cf]
  have hCf_sub : Cf ⊆ cexTri ∪ cexSq := fun f hf => hsub (by simpa [Cf] using hf)
  have hinc : ∀ f ∈ Cf, ∀ z : Fin 13, (cexSrc f = z ∨ cexTgt f = z) →
      (Cf.filter fun e => cexSrc e = z ∨ cexTgt e = z).card = 2 := fun f hf z hz =>
    cexNet_card_incident hC (by simpa [Cf] using hf) hz
  have hne : Cf.Nonempty := by
    obtain ⟨k, v, e, hc, hr⟩ := hC
    exact ⟨e ⟨0, hc.pos⟩, by simp [Cf, ← hr]⟩
  -- the cycle does not cross the cut around `t, p, u`
  have hsplit : Cf ⊆ cexTri ∨ Cf ⊆ cexSq := by
    by_contra hcon
    simp only [not_or, Finset.not_subset] at hcon
    obtain ⟨⟨f, hf, hfT⟩, ⟨g, hg, hgS⟩⟩ := hcon
    have hfS : f ∈ cexSq := by
      have := hCf_sub hf
      simp only [mem_union] at this
      tauto
    have hgT : g ∈ cexTri := by
      have := hCf_sub hg
      simp only [mem_union] at this
      tauto
    have hW := walks_cycle_of_mem_cycleNodes cexNet.graph hC
      (source_mem_cycleNodes (G := cexNet.graph) (by simpa [Cf] using hf))
      (source_mem_cycleNodes (G := cexNet.graph) (by simpa [Cf] using hg))
    have hcut : ∀ e ∈ C, ¬ cexNet.graph.Crosses e ↑({6, 7, 8} : Finset (Fin 13)) := by
      intro e he
      rw [cexNet_crosses_iff]
      have key : ∀ e ∈ cexTri ∪ cexSq, ¬ ((cexSrc e ∈ ({6, 7, 8} : Finset (Fin 13)) ∧
          cexTgt e ∉ ({6, 7, 8} : Finset (Fin 13))) ∨ (cexTgt e ∈ ({6, 7, 8} : Finset (Fin 13)) ∧
          cexSrc e ∉ ({6, 7, 8} : Finset (Fin 13)))) := by decide
      exact key e (hsub he)
    have hm := cexNet.graph.mem_iff_mem_of_walks hcut hW
    have k₁ : ∀ f ∈ cexSq, cexSrc f ∉ ({6, 7, 8} : Finset (Fin 13)) := by decide
    have k₂ : ∀ g ∈ cexTri, cexSrc g ∈ ({6, 7, 8} : Finset (Fin 13)) := by decide
    exact k₁ f hfS (Finset.mem_coe.1 (hm.2 (Finset.mem_coe.2 (k₂ g hgT))))
  -- a set of edges of one of the cycles, each of whose nodes is on two of them, is the cycle
  have hT : ∀ D ∈ cexTri.powerset, D.Nonempty → (∀ f ∈ D, ∀ z : Fin 13,
      (cexSrc f = z ∨ cexTgt f = z) → (D.filter fun e => cexSrc e = z ∨ cexTgt e = z).card = 2) →
      D = cexTri := by decide
  have hS : ∀ D ∈ cexSq.powerset, D.Nonempty → (∀ f ∈ D, ∀ z : Fin 13,
      (cexSrc f = z ∨ cexTgt f = z) → (D.filter fun e => cexSrc e = z ∨ cexTgt e = z).card = 2) →
      D = cexSq := by decide
  rcases hsplit with h | h
  · exact Or.inl (by rw [hCeq, hT Cf (Finset.mem_powerset.2 h) hne hinc])
  · exact Or.inr (by rw [hCeq, hS Cf (Finset.mem_powerset.2 h) hne hinc])

theorem cexNet_isLevelOne : IsLevelOne cexNet.graph := by
  intro C C' hC hC' ⟨f, hf, hf'⟩
  have hdisj : ∀ f, f ∈ cexTri → f ∉ cexSq := by decide
  rcases cexNet_cycle_eq hC with rfl | rfl <;> rcases cexNet_cycle_eq hC' with rfl | rfl
  · rfl
  · exact absurd (Finset.mem_coe.1 hf') (hdisj f (Finset.mem_coe.1 hf))
  · exact absurd (Finset.mem_coe.1 hf) (hdisj f (Finset.mem_coe.1 hf'))
  · rfl

/-! ### `N⁻` and the 4-cycle `C_v`

`N⁻` removes the root `r` and merges its two arcs `r → a`, `r → t`, one of which is
`rootTreeArc`. -/

/-- `Fin 5` has at least two taxa. -/
theorem cexHX : Nontrivial (Fin 5) := inferInstance

/-- `N⁻` of the counterexample. -/
abbrev cexUnrooted := unrooted cexNet cexNet_isBinaryRootedNetwork cexHX

/-- The arc of `N` removed in `N⁻`. -/
abbrev cexRho : Fin 14 :=
  (rootTreeArc cexNet_isPhylogenetic cexNet_isBinary cexHX).1

theorem cexRho_mem : cexRho ∈ ({0, 1} : Finset (Fin 14)) := by
  have h := congrArg Subtype.val (rootTreeArc_spec cexNet_isPhylogenetic cexNet_isBinary cexHX).1
  have h' : cexSrc cexRho = 5 := h.trans cexNet_lsa_univ
  have key : ∀ f : Fin 14, cexSrc f = 5 → f ∈ ({0, 1} : Finset (Fin 14)) := by decide
  exact key _ h'

/-- The tail in `N⁻` of an edge, as a vertex of `N`. -/
def cexSrcU (ρ f : Fin 14) : Fin 13 := if cexSrc f = 5 then cexTgt ρ else cexSrc f

theorem cexUnrooted_source_val (c : SemidirectedArc cexNet_isPhylogenetic cexNet_isBinary cexHX) :
    (cexUnrooted.graph.source c).1.1 = cexSrcU cexRho c.1.1 := by
  unfold cexSrcU
  split_ifs with h
  · exact unrooted_source_val_of_eq cexNet_isBinaryRootedNetwork c (h.trans cexNet_lsa_univ.symm)
  · exact unrooted_source_val_of_ne cexNet_isBinaryRootedNetwork c
      fun h' => h (h'.trans cexNet_lsa_univ)

theorem cexUnrooted_target_val (c : SemidirectedArc cexNet_isPhylogenetic cexNet_isBinary cexHX) :
    (cexUnrooted.graph.target c).1.1 = cexTgt c.1.1 := rfl

theorem cexUnrooted_isDirected_iff
    (c : SemidirectedArc cexNet_isPhylogenetic cexNet_isBinary cexHX) :
    cexUnrooted.IsDirected c ↔ c.1.1 ∈ ({3, 5, 10, 12} : Finset (Fin 14)) :=
  (belowNetwork_isHybridArc_iff
    (hl := lsa_mem_ancestralVertices cexNet_isPhylogenetic Set.univ_nonempty)
    (hleaf := fun _ hx => (lsa_spec cexNet_isPhylogenetic Set.univ Set.univ_nonempty).1.reaches_leaf
      cexNet_isPhylogenetic hx)
    cexNet_isPhylogenetic (lsa_spec cexNet_isPhylogenetic _ _).1 c.1).trans
    (cexNet_isHybridArc_iff c.1.1)

theorem cexUnrooted_leaf_val (x : Fin 5) :
    (cexUnrooted.leaf x).1.1 = (![0, 1, 2, 3, 4] : Fin 5 → Fin 13) x := rfl

/-- The node of `N⁻` at the vertex `i ≠ r` of `N`. -/
def cexNode (i : Fin 13) (hi : i ≠ 5) : SemidirectedVertex cexNet_isPhylogenetic cexHX :=
  ⟨⟨i, by rw [cexNet_lsa_univ]; exact cexNet_root_reaches i,
    mem_ancestralVertices_univ cexNet_isPhylogenetic i⟩,
    fun h => hi ((congrArg Subtype.val h).trans cexNet_lsa_univ)⟩

/-- The edge of `N⁻` at the arc `f` of `N` not leaving `r`. -/
def cexEdge (f : Fin 14) (hf : cexSrc f ≠ 5) :
    SemidirectedArc cexNet_isPhylogenetic cexNet_isBinary cexHX :=
  ⟨⟨f, by rw [cexNet_lsa_univ]; exact cexNet_root_reaches _,
    mem_ancestralVertices_univ cexNet_isPhylogenetic _⟩, fun h => hf (by
      have h' := congrArg Subtype.val h
      have hs := congrArg Subtype.val
        (rootTreeArc_spec cexNet_isPhylogenetic cexNet_isBinary cexHX).1
      exact (congrArg cexSrc h').trans (hs.trans cexNet_lsa_univ))⟩

theorem cexEdge_source (f : Fin 14) (hf : cexSrc f ≠ 5) (i : Fin 13) (hi : i ≠ 5)
    (h : cexSrc f = i) : cexUnrooted.graph.source (cexEdge f hf) = cexNode i hi :=
  unrooted_node_ext (by rw [cexUnrooted_source_val]; simp [cexSrcU, cexEdge, cexNode, h, hi])

theorem cexEdge_target (f : Fin 14) (hf : cexSrc f ≠ 5) (i : Fin 13) (hi : i ≠ 5)
    (h : cexTgt f = i) : cexUnrooted.graph.target (cexEdge f hf) = cexNode i hi :=
  unrooted_node_ext h

/-- The edges `w x`, `x v`, `y v`, `w y` of the 4-cycle `C_v`. -/
def cexCvEdges : Fin 4 → SemidirectedArc cexNet_isPhylogenetic cexNet_isBinary cexHX :=
  ![cexEdge 7 (by decide), cexEdge 10 (by decide), cexEdge 12 (by decide), cexEdge 8 (by decide)]

/-- **The 4-cycle `C_v` of `N⁻`.** -/
def cexCv : Set (SemidirectedArc cexNet_isPhylogenetic cexNet_isBinary cexHX) :=
  Set.range cexCvEdges

/-- The hybrid node `v` of `C_v`. -/
def cexV : SemidirectedVertex cexNet_isPhylogenetic cexHX := cexNode 12 (by decide)

theorem cexCvEdges_val (i : Fin 4) : (cexCvEdges i).1.1 = (![7, 10, 12, 8] : Fin 4 → Fin 14) i := by
  fin_cases i <;> rfl

theorem mem_cexCv_iff (c : SemidirectedArc cexNet_isPhylogenetic cexNet_isBinary cexHX) :
    c ∈ cexCv ↔ c.1.1 ∈ ({7, 10, 12, 8} : Finset (Fin 14)) := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [cexCvEdges_val]
    fin_cases i <;> decide
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with h | h | h | h
    · exact ⟨0, unrooted_edge_ext h.symm⟩
    · exact ⟨1, unrooted_edge_ext h.symm⟩
    · exact ⟨2, unrooted_edge_ext h.symm⟩
    · exact ⟨3, unrooted_edge_ext h.symm⟩

theorem cexCvEdges_injective : Function.Injective cexCvEdges := by
  intro i j h
  have h' := congrArg (fun c => c.1.1) h
  simp only [cexCvEdges_val] at h'
  revert i j
  decide

theorem cexCv_isCycle : IsCycle cexUnrooted.graph cexCv := by
  refine ⟨4, ![cexNode 9 (by decide), cexNode 10 (by decide), cexNode 12 (by decide),
    cexNode 11 (by decide)], cexCvEdges, ⟨by norm_num, fun i => ?_, ?_, cexCvEdges_injective⟩, rfl⟩
  · fin_cases i
    · exact Or.inl ⟨cexEdge_source 7 (by decide) 9 (by decide) rfl,
        cexEdge_target 7 (by decide) 10 (by decide) rfl⟩
    · exact Or.inl ⟨cexEdge_source 10 (by decide) 10 (by decide) rfl,
        cexEdge_target 10 (by decide) 12 (by decide) rfl⟩
    · exact Or.inr ⟨cexEdge_source 12 (by decide) 11 (by decide) rfl,
        cexEdge_target 12 (by decide) 12 (by decide) rfl⟩
    · exact Or.inr ⟨cexEdge_source 8 (by decide) 9 (by decide) rfl,
        cexEdge_target 8 (by decide) 11 (by decide) rfl⟩
  · intro i j h
    have h' := congrArg (fun z => z.1.1) h
    revert i j
    decide

theorem cexCv_ncard : cexCv.ncard = 4 := by
  rw [cexCv, Set.ncard_range_of_injective cexCvEdges_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem cexV_isHybridNodeOf : IsHybridNodeOf cexUnrooted cexCv cexV :=
  ⟨cexEdge 10 (by decide), ⟨1, rfl⟩, cexEdge 12 (by decide), ⟨2, rfl⟩,
    fun h => absurd (congrArg (fun c => c.1.1) h) (by decide),
    (cexUnrooted_isDirected_iff _).2 (by decide), (cexUnrooted_isDirected_iff _).2 (by decide),
    cexEdge_target _ _ _ _ rfl, cexEdge_target _ _ _ _ rfl⟩

/-- Two taxa on different sides of a cut that no edge of `N⁻` outside `C_v` crosses are in different
blocks of `C_v`. -/
theorem cex_not_sameBlock_of_cut (S : Finset (Fin 13))
    (hS : ∀ ρ ∈ ({0, 1} : Finset (Fin 14)), ∀ f : Fin 14, f ∉ ({7, 10, 12, 8} : Finset (Fin 14)) →
      ¬ ((cexSrcU ρ f ∈ S ∧ cexTgt f ∉ S) ∨ (cexTgt f ∈ S ∧ cexSrcU ρ f ∉ S)))
    (x y : Fin 5)
    (hxy : ¬ ((![0, 1, 2, 3, 4] : Fin 5 → Fin 13) x ∈ S ↔
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 13) y ∈ S)) :
    ¬ SameBlock cexUnrooted.graph cexUnrooted.leaf cexCv x y := by
  intro h
  refine hxy ?_
  have := cexUnrooted.graph.mem_iff_mem_of_walks (S := {z | z.1.1 ∈ S}) (fun c hc hcr => ?_) h
  · exact this
  · refine hS _ cexRho_mem c.1.1 (fun hm => hc ((mem_cexCv_iff c).2 hm)) ?_
    simpa only [DirectedMultigraph.Crosses, Set.mem_ofPred_eq, cexUnrooted_source_val,
      cexUnrooted_target_val] using hcr

/-- **The taxa `a, b, c, d` are in the four distinct blocks of `C_v`**, separated by the cuts
`{x, b}`, `{y, c}`, `{v, d}`. -/
theorem cex_blocks : ∀ x ∈ ({0, 1, 2, 3} : Finset (Fin 5)), ∀ y ∈ ({0, 1, 2, 3} : Finset (Fin 5)),
    x ≠ y → ¬ SameBlock cexUnrooted.graph cexUnrooted.leaf cexCv x y := by
  have hb := cex_not_sameBlock_of_cut {10, 1} (by decide)
  have hc := cex_not_sameBlock_of_cut {11, 2} (by decide)
  have hd := cex_not_sameBlock_of_cut {12, 3} (by decide)
  intro x hx y hy hxy
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | exact hb _ _ (by decide)
      | exact hc _ _ (by decide)
      | exact hd _ _ (by decide)

/-- **`e` does not descend from `v`**: a semidirected path from `v` stays in `{v, d}`. -/
theorem cex_not_descendsFrom : ¬ DescendsFrom cexUnrooted cexV 4 := by
  rintro ⟨P, S, k, p, q, hp, h0, hk, -, -⟩
  have key : ∀ ρ ∈ ({0, 1} : Finset (Fin 14)), ∀ f : Fin 14, ∀ a b : Fin 13,
      a ∈ ({12, 3} : Finset (Fin 13)) →
      ((cexSrcU ρ f = a ∧ cexTgt f = b) ∨
        (f ∉ ({3, 5, 10, 12} : Finset (Fin 14)) ∧ cexTgt f = a ∧ cexSrcU ρ f = b)) →
      b ∈ ({12, 3} : Finset (Fin 13)) := by decide
  have hall : ∀ i : Fin (k + 1), (p i).1.1 ∈ ({12, 3} : Finset (Fin 13)) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [h0]; decide
    | succ i ih =>
      refine key _ cexRho_mem (q i).1.1 _ _ ih ?_
      rcases hp.step i with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩
      · left
        rw [← cexUnrooted_source_val, ← cexUnrooted_target_val, h₁, h₂]
        exact ⟨rfl, rfl⟩
      · right
        refine ⟨fun h => h₁ ((cexUnrooted_isDirected_iff _).2 h), ?_, ?_⟩
        · rw [← cexUnrooted_target_val, h₂]
        · rw [← cexUnrooted_source_val, h₃]
  have := hall (Fin.last k)
  rw [hk, cexUnrooted_leaf_val] at this
  exact absurd this (by decide)

/-! ### The quartet network `Q⊕` on `{a, b, c, e}`

Its LSA is `r`. The arcs ancestral to `a, b, c, e` are all but `x → v`, `y → v`, `v → d`; in that
part of `N` the vertices `x` and `y` have one parent and one child, and are suppressed: `Q⊕` has the
vertices `r, a, t, p, e, u, w, b, c` and the arcs `0, …, 8`, the arcs `7`, `8` ending at `b`,
`c`. -/

/-- The taxa `a, b, c, e`. -/
def cexS : Finset (Fin 5) := {0, 1, 2, 4}

theorem cexS_card : #cexS = 4 := by decide

theorem cexS_nontrivial : (cexS : Set (Fin 5)).Nontrivial :=
  ⟨0, by simp [cexS], 1, by simp [cexS], by decide⟩

theorem cexNet_lsa_s (h : (cexS : Set (Fin 5)).Nonempty) :
    lsa cexNet_isPhylogenetic (cexS : Set (Fin 5)) h = 5 :=
  IsLeastStableAncestor.unique cexNet_isPhylogenetic (lsa_spec _ _ _)
    (cexNet_isLeastStableAncestor (by simp [cexS]) (by simp [cexS]))

theorem cex_mem_ancestralVertices_iff (v : Fin 13) :
    v ∈ cexNet.ancestralVertices (cexS : Set (Fin 5)) ↔ v ∉ ({3, 12} : Finset (Fin 13)) := by
  constructor
  · rintro ⟨x, hx, hr⟩ hv
    have h := cexNet_reaches_mem (D := {3, 12}) (by decide) hv hr
    have key : ∀ x : Fin 5, x ∈ cexS →
        (![0, 1, 2, 3, 4] : Fin 5 → Fin 13) x ∉ ({3, 12} : Finset (Fin 13)) := by decide
    exact key x hx h
  · intro hv
    have h0 : (0 : Fin 5) ∈ (cexS : Set (Fin 5)) := by simp [cexS]
    have h1 : (1 : Fin 5) ∈ (cexS : Set (Fin 5)) := by simp [cexS]
    have h2 : (2 : Fin 5) ∈ (cexS : Set (Fin 5)) := by simp [cexS]
    have h4 : (4 : Fin 5) ∈ (cexS : Set (Fin 5)) := by simp [cexS]
    fin_cases v
    · exact ⟨0, h0, .refl⟩
    · exact ⟨1, h1, .refl⟩
    · exact ⟨2, h2, .refl⟩
    · exact absurd (by decide) hv
    · exact ⟨4, h4, .refl⟩
    · exact ⟨0, h0, cexNet_reaches_of_arc 0 .refl⟩
    · exact ⟨4, h4, cexNet_reaches_of_arc 2 (cexNet_reaches_of_arc 4 .refl)⟩
    · exact ⟨4, h4, cexNet_reaches_of_arc 4 .refl⟩
    · exact ⟨1, h1,
        cexNet_reaches_of_arc 6 (cexNet_reaches_of_arc 7 (cexNet_reaches_of_arc 9 .refl))⟩
    · exact ⟨1, h1, cexNet_reaches_of_arc 7 (cexNet_reaches_of_arc 9 .refl)⟩
    · exact ⟨1, h1, cexNet_reaches_of_arc 9 .refl⟩
    · exact ⟨2, h2, cexNet_reaches_of_arc 11 .refl⟩
    · exact absurd (by decide) hv

theorem cex_mem_belowVertices_iff (h : (cexS : Set (Fin 5)).Nonempty) (v : Fin 13) :
    v ∈ cexNet.belowVertices (lsa cexNet_isPhylogenetic (cexS : Set (Fin 5)) h) cexS ↔
      v ∉ ({3, 12} : Finset (Fin 13)) := by
  rw [← cex_mem_ancestralVertices_iff]
  refine ⟨fun hv => hv.2, fun hv => ⟨?_, hv⟩⟩
  rw [cexNet_lsa_s]
  exact cexNet_root_reaches v

theorem cex_mem_belowArcs_iff (h : (cexS : Set (Fin 5)).Nonempty) (f : Fin 14) :
    f ∈ cexNet.belowArcs (lsa cexNet_isPhylogenetic (cexS : Set (Fin 5)) h) cexS ↔
      cexTgt f ∉ ({3, 12} : Finset (Fin 13)) := by
  rw [← cex_mem_ancestralVertices_iff]
  refine ⟨fun hf => hf.2, fun hf => ⟨?_, hf⟩⟩
  rw [cexNet_lsa_s]
  exact cexNet_root_reaches _

/-- The part `N⊕_{abce}` of `N` below the LSA of `a, b, c, e` and ancestral to them, before
suppression. -/
abbrev cexL := lsaNetwork cexNet_isPhylogenetic (cexS : Set (Fin 5)) cexS_nontrivial.nonempty

theorem cexL_isPhylogenetic : cexL.IsPhylogenetic :=
  lsaNetwork_isPhylogenetic cexNet_isPhylogenetic cexS_nontrivial

theorem cexL_indegree
    (z : cexNet.belowVertices (lsa cexNet_isPhylogenetic (cexS : Set (Fin 5))
      cexS_nontrivial.nonempty) cexS) (hz : z.1 ≠ 5) :
    cexL.graph.indegree z = cexNet.graph.indegree z.1 :=
  belowNetwork_indegree cexNet_isPhylogenetic (lsa_spec _ _ _).1 z
    fun h => hz (h.trans (cexNet_lsa_s _))

theorem cexL_outdegree
    (z : cexNet.belowVertices (lsa cexNet_isPhylogenetic (cexS : Set (Fin 5))
      cexS_nontrivial.nonempty) cexS) :
    cexL.graph.outdegree z =
      #(univ.filter fun f => cexSrc f = z.1 ∧ cexTgt f ∉ ({3, 12} : Finset (Fin 13))) := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun e _ => e.1) (fun e he => ?_) (fun e e' _ _ h => Subtype.ext h)
    (fun f hf => ?_)
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨congrArg Subtype.val he, (cex_mem_belowArcs_iff _ e.1).1 e.2⟩
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf
    exact ⟨⟨f, (cex_mem_belowArcs_iff _ f).2 hf.2⟩, Subtype.ext hf.1, rfl⟩

theorem cexL_isChainVertex_iff
    (z : cexNet.belowVertices (lsa cexNet_isPhylogenetic (cexS : Set (Fin 5))
      cexS_nontrivial.nonempty) cexS) :
    cexL.IsChainVertex z ↔ z.1 ∈ ({10, 11} : Finset (Fin 13)) := by
  by_cases hz : z.1 = 5
  · have hroot : z = cexL.root :=
      Subtype.ext (hz.trans (cexNet_lsa_s cexS_nontrivial.nonempty).symm)
    subst hroot
    refine iff_of_false (not_isChainVertex_root cexL_isPhylogenetic) ?_
    rw [hz]
    decide
  · unfold IsChainVertex
    rw [cexL_indegree z hz, cexNet_indegree, cexL_outdegree]
    have hz' := (cex_mem_belowVertices_iff _ z.1).1 z.2
    generalize z.1 = v at hz hz' ⊢
    revert v
    decide

/-- The heads in `Q⊕` of its arcs: the arcs `7`, `8` end at `b`, `c`. -/
def cexTgtQ (f : Fin 14) : Fin 13 := if f = 7 then 1 else if f = 8 then 2 else cexTgt f

theorem cexL_chainEnd_target
    (f : cexNet.belowArcs (lsa cexNet_isPhylogenetic (cexS : Set (Fin 5))
      cexS_nontrivial.nonempty) cexS) :
    (chainEnd cexL_isPhylogenetic (cexL.graph.target f)).1 = cexTgtQ f.1 := by
  have hf := (cex_mem_belowArcs_iff _ f.1).1 f.2
  by_cases h7 : f.1 = 7
  · have hb := (cex_mem_belowVertices_iff cexS_nontrivial.nonempty 1).2 (by decide)
    have h9 := (cex_mem_belowArcs_iff cexS_nontrivial.nonempty 9).2 (by decide)
    have hchain : cexL.IsChainVertex (cexL.graph.target f) :=
      (cexL_isChainVertex_iff _).2 (by show cexTgt f.1 ∈ _; rw [h7]; decide)
    rw [chainEnd_eq_of_chainReach cexL_isPhylogenetic (w := ⟨1, hb⟩)
      (Relation.ReflTransGen.single ⟨hchain, ⟨⟨9, h9⟩, Subtype.ext (by
        show cexSrc 9 = cexTgt f.1
        rw [h7]
        rfl), rfl⟩⟩) ((cexL_isChainVertex_iff _).not.2 (by show (1 : Fin 13) ∉ _; decide))]
    simp [cexTgtQ, h7]
  · by_cases h8 : f.1 = 8
    · have hc := (cex_mem_belowVertices_iff cexS_nontrivial.nonempty 2).2 (by decide)
      have h11 := (cex_mem_belowArcs_iff cexS_nontrivial.nonempty 11).2 (by decide)
      have hchain : cexL.IsChainVertex (cexL.graph.target f) :=
        (cexL_isChainVertex_iff _).2 (by show cexTgt f.1 ∈ _; rw [h8]; decide)
      rw [chainEnd_eq_of_chainReach cexL_isPhylogenetic (w := ⟨2, hc⟩)
        (Relation.ReflTransGen.single ⟨hchain, ⟨⟨11, h11⟩, Subtype.ext (by
          show cexSrc 11 = cexTgt f.1
          rw [h8]
          rfl), rfl⟩⟩) ((cexL_isChainVertex_iff _).not.2 (by show (2 : Fin 13) ∉ _; decide))]
      simp [cexTgtQ, h8]
    · rw [chainEnd_eq_self cexL_isPhylogenetic ((cexL_isChainVertex_iff _).not.2 ?_)]
      · simp only [cexTgtQ, h7, h8, ite_false]
        rfl
      · show cexTgt f.1 ∉ _
        generalize f.1 = g at h7 h8 hf
        revert g
        decide

/-- `Q⊕`, the quartet network on `a, b, c, e`. -/
abbrev cexQ := quartetLSA cexNet cexNet_isPhylogenetic cexS cexS_card

theorem cexQ_isBinary : IsBinaryRootedNetwork cexQ :=
  quartetLSA_isBinaryRootedNetwork cexNet_isBinaryRootedNetwork cexS_card

theorem cexQX : Nontrivial (cexS : Set (Fin 5)) := cexS_nontrivial.coe_sort

instance cexS_nonempty : Nonempty (cexS : Set (Fin 5)) := ⟨⟨0, by simp [cexS]⟩⟩

theorem cexQ_lsa : lsa cexQ_isBinary.1 Set.univ Set.univ_nonempty = cexQ.root :=
  IsLeastStableAncestor.unique cexQ_isBinary.1 (lsa_spec _ _ _)
    (quartetLSA_isLSANetwork cexNet_isBinaryRootedNetwork cexS_card)

theorem cexQ_root_val : cexQ.root.1.1 = 5 := cexNet_lsa_s cexS_nontrivial.nonempty

/-- `Q⁻`, the unrooted network of `Q⊕`. -/
abbrev cexQU := unrooted cexQ cexQ_isBinary cexQX

/-- The nodes of `Q⁻`. -/
abbrev cexQV := SemidirectedVertex cexQ_isBinary.1 cexQX

/-- The edges of `Q⁻`. -/
abbrev cexQE := SemidirectedArc cexQ_isBinary.1 cexQ_isBinary.2 cexQX

/-- The arc of `N` removed in `Q⁻`. -/
abbrev cexRhoQ : Fin 14 := (rootTreeArc cexQ_isBinary.1 cexQ_isBinary.2 cexQX).1.1.1

/-- The vertices of `N` that are nodes of `Q⁻`. -/
def cexKeptV : Finset (Fin 13) := {0, 1, 2, 4, 6, 7, 8, 9}

/-- The arcs of `N` that are arcs of `Q⊕`. -/
def cexKeptE : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}

theorem cexRhoQ_mem : cexRhoQ ∈ ({0, 1} : Finset (Fin 14)) := by
  have h := congrArg (fun z => z.1.1.1)
    (rootTreeArc_spec cexQ_isBinary.1 cexQ_isBinary.2 cexQX).1
  have h' : cexSrc cexRhoQ = 5 := by
    refine h.trans ?_
    show (lsa cexQ_isBinary.1 Set.univ Set.univ_nonempty).1.1 = 5
    exact (congrArg (fun z => z.1.1) cexQ_lsa).trans cexQ_root_val
  have key : ∀ f : Fin 14, cexSrc f = 5 → f ∈ ({0, 1} : Finset (Fin 14)) := by decide
  exact key _ h'

theorem cexQE_val_mem (e : cexQE) : e.1.1.1.1 ∈ cexKeptE ∧ e.1.1.1.1 ≠ cexRhoQ := by
  have ht := (cex_mem_belowArcs_iff _ e.1.1.1.1).1 e.1.1.1.2
  have hs := (cexL_isChainVertex_iff _).not.1 e.1.1.2
  refine ⟨?_, fun h => e.2 (Subtype.ext (Subtype.ext (Subtype.ext h)))⟩
  change cexSrc e.1.1.1.1 ∉ _ at hs
  generalize e.1.1.1.1 = f at ht hs
  revert f
  decide

theorem cexQV_val_mem (v : cexQV) : v.1.1.1.1 ∈ cexKeptV := by
  have ha := (cex_mem_belowVertices_iff _ v.1.1.1.1).1 v.1.1.1.2
  have hc := (cexL_isChainVertex_iff _).not.1 v.1.1.2
  have hr : v.1.1.1.1 ≠ 5 := fun h => v.2 (Subtype.ext (by
    show v.1.1 = lsa cexQ_isBinary.1 Set.univ Set.univ_nonempty
    exact (Subtype.ext (Subtype.ext (h.trans cexQ_root_val.symm))).trans cexQ_lsa.symm))
  generalize v.1.1.1.1 = z at ha hc hr
  revert z
  decide

theorem cexQ_lsaPlus_source_eq_root_iff (e : cexQE) :
    (lsaPlus cexQ_isBinary.1 cexQX).graph.source e.1 = (lsaPlus cexQ_isBinary.1 cexQX).root ↔
      cexSrc e.1.1.1.1 = 5 := by
  constructor
  · intro h
    have h' := congrArg (fun z => z.1.1.1) h
    refine h'.trans ?_
    show (lsa cexQ_isBinary.1 Set.univ Set.univ_nonempty).1.1 = 5
    exact (congrArg (fun z => z.1.1) cexQ_lsa).trans cexQ_root_val
  · intro h
    refine Subtype.ext ?_
    show cexQ.graph.source e.1.1 = lsa cexQ_isBinary.1 Set.univ Set.univ_nonempty
    exact (Subtype.ext (Subtype.ext (h.trans cexQ_root_val.symm))).trans cexQ_lsa.symm

/-- The tail in `Q⁻` of an edge, as a vertex of `N`. -/
def cexSrcQU (ρ f : Fin 14) : Fin 13 := if cexSrc f = 5 then cexTgtQ ρ else cexSrc f

theorem cexQU_source_val (e : cexQE) :
    (cexQU.graph.source e).1.1.1.1 = cexSrcQU cexRhoQ e.1.1.1.1 := by
  unfold cexSrcQU
  show ((unrootAt (lsaPlus cexQ_isBinary.1 cexQX) (lsaPlus_isPhylogenetic cexQ_isBinary.1 cexQX)
    (rootTreeArc cexQ_isBinary.1 cexQ_isBinary.2 cexQX)).graph.source e).1.1.1.1 = _
  simp only [unrootAt]
  by_cases h :
      (lsaPlus cexQ_isBinary.1 cexQX).graph.source e.1 = (lsaPlus cexQ_isBinary.1 cexQX).root
  · rw [dite_eq_left h, ite_eq_left ((cexQ_lsaPlus_source_eq_root_iff e).1 h)]
    exact cexL_chainEnd_target _
  · rw [dite_eq_right h, ite_eq_right (mt (cexQ_lsaPlus_source_eq_root_iff e).2 h)]
    rfl

theorem cexQU_target_val (e : cexQE) : (cexQU.graph.target e).1.1.1.1 = cexTgtQ e.1.1.1.1 :=
  cexL_chainEnd_target _

theorem cexQU_leaf_val (x : (cexS : Set (Fin 5))) :
    (cexQU.leaf x).1.1.1.1 = (![0, 1, 2, 3, 4] : Fin 5 → Fin 13) x.1 := rfl

theorem cexQU_isDirected_iff (e : cexQE) :
    cexQU.IsDirected e ↔ e.1.1.1.1 ∈ ({3, 5} : Finset (Fin 14)) := by
  have h₁ : cexQU.IsDirected e ↔ cexQ.IsHybridArc e.1.1 :=
    belowNetwork_isHybridArc_iff
      (hl := lsa_mem_ancestralVertices cexQ_isBinary.1 Set.univ_nonempty)
      (hleaf := fun _ hx => (lsa_spec cexQ_isBinary.1 Set.univ Set.univ_nonempty).1.reaches_leaf
        cexQ_isBinary.1 hx)
      cexQ_isBinary.1 (lsa_spec cexQ_isBinary.1 _ _).1 e.1
  rw [h₁]
  unfold IsHybridArc
  have h₂ : cexQ.graph.indegree (cexQ.graph.target e.1.1) =
      cexL.graph.indegree (cexQ.graph.target e.1.1).1 :=
    suppress_indegree cexL_isPhylogenetic (cexQ.graph.target e.1.1)
  have hne : (cexQ.graph.target e.1.1).1.1 ≠ 5 := by
    have ht : (cexQ.graph.target e.1.1).1.1 = cexTgtQ e.1.1.1.1 := cexL_chainEnd_target _
    rw [ht]
    have := (cexQE_val_mem e).1
    generalize e.1.1.1.1 = f at this
    revert f
    decide
  rw [h₂, cexL_indegree _ hne, cexNet_indegree]
  have ht : (cexQ.graph.target e.1.1).1.1 = cexTgtQ e.1.1.1.1 := cexL_chainEnd_target _
  rw [ht]
  have := (cexQE_val_mem e).1
  generalize e.1.1.1.1 = f at this
  revert f
  decide

/-! ### `Q⁻` is Figure 18

The nodes `b, c, e, a, w, u, p, t` of `Q⁻` are the nodes `0, …, 7` of Figure 18; its edges `w b`,
`w c`, `p e`, the edge `t a` merged at the root, `u w`, `t p`, `t u`, `p u` are the edges `0, …, 7`.
The taxa `A, B, C, D` of the figure are `b, c, e, a`. -/

/-- The node of Figure 18 of a vertex of `N`. -/
def cexLookV (v : Fin 13) : Fin 8 := ![3, 0, 1, 0, 2, 0, 7, 6, 5, 4, 0, 0, 0] v

/-- The vertex of `N` of a node of Figure 18. -/
def cexNodeOf (i : Fin 8) : Fin 13 := ![1, 2, 4, 0, 9, 8, 7, 6] i

/-- The edge of Figure 18 of an arc of `N`. -/
def cexLookE (f : Fin 14) : Fin 8 := ![3, 3, 5, 6, 2, 7, 4, 0, 1, 0, 0, 0, 0, 0] f

/-- The arc of `N` of an edge of Figure 18, when `ρ` is the arc removed at the root. -/
def cexArcOf (ρ : Fin 14) (j : Fin 8) : Fin 14 :=
  if j = 3 then (if ρ = 0 then 1 else 0) else ![7, 8, 4, 0, 6, 2, 3, 5] j

theorem cexNodeOf_mem : ∀ i, cexNodeOf i ∈ cexKeptV := by decide

theorem cexArcOf_mem : ∀ ρ ∈ ({0, 1} : Finset (Fin 14)), ∀ j, cexArcOf ρ j ∈ cexKeptE ∧
    cexArcOf ρ j ≠ ρ := by decide

theorem cexKeptV_spec : ∀ i ∈ cexKeptV, i ∉ ({3, 12} : Finset (Fin 13)) ∧
    i ∉ ({10, 11} : Finset (Fin 13)) ∧ i ≠ 5 := by decide

theorem cexKeptE_spec : ∀ f ∈ cexKeptE, cexTgt f ∉ ({3, 12} : Finset (Fin 13)) ∧
    cexSrc f ∉ ({10, 11} : Finset (Fin 13)) := by decide

theorem cexQ_lsa_reaches (z) :
    cexQ.graph.Reaches (lsa cexQ_isBinary.1 Set.univ Set.univ_nonempty) z := by
  rw [cexQ_lsa]
  exact cexQ_isBinary.1.root_reaches z

/-- The node of `Q⁻` at a vertex of `N`. -/
def cexQNode (i : Fin 13) (hi : i ∈ cexKeptV) : cexQV :=
  ⟨⟨⟨⟨i, (cex_mem_belowVertices_iff _ i).2 (cexKeptV_spec i hi).1⟩,
    (cexL_isChainVertex_iff _).not.2 (cexKeptV_spec i hi).2.1⟩,
    ⟨cexQ_lsa_reaches _, mem_ancestralVertices_univ cexQ_isBinary.1 _⟩⟩, fun h =>
    (cexKeptV_spec i hi).2.2 ((congrArg (fun z => z.1.1.1) h).trans
      ((congrArg (fun z => z.1.1) cexQ_lsa).trans cexQ_root_val))⟩

/-- The edge of `Q⁻` at an arc of `N`. -/
def cexQEdge (f : Fin 14) (hf : f ∈ cexKeptE) (hρ : f ≠ cexRhoQ) : cexQE :=
  ⟨⟨⟨⟨f, (cex_mem_belowArcs_iff _ f).2 (cexKeptE_spec f hf).1⟩,
    (cexL_isChainVertex_iff _).not.2 (cexKeptE_spec f hf).2⟩,
    ⟨cexQ_lsa_reaches _, mem_ancestralVertices_univ cexQ_isBinary.1 _⟩⟩,
    fun h => hρ (congrArg (fun z => z.1.1.1) h)⟩

/-- The nodes of `Q⁻` and of Figure 18. -/
def cexVert : cexQV ≃ Fin 8 where
  toFun v := cexLookV v.1.1.1.1
  invFun i := cexQNode (cexNodeOf i) (cexNodeOf_mem i)
  left_inv v := by
    have key : ∀ z ∈ cexKeptV, cexNodeOf (cexLookV z) = z := by decide
    exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext (key _ (cexQV_val_mem v)))))
  right_inv i := by
    show cexLookV (cexNodeOf i) = i
    revert i
    decide

/-- The edges of `Q⁻` and of Figure 18. -/
def cexEdgeEquiv : cexQE ≃ Fin 8 where
  toFun e := cexLookE e.1.1.1.1
  invFun j := cexQEdge (cexArcOf cexRhoQ j) (cexArcOf_mem _ cexRhoQ_mem j).1
    (cexArcOf_mem _ cexRhoQ_mem j).2
  left_inv e := by
    have key : ∀ ρ ∈ ({0, 1} : Finset (Fin 14)), ∀ f ∈ cexKeptE, f ≠ ρ →
        cexArcOf ρ (cexLookE f) = f := by decide
    exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext
      (key _ cexRhoQ_mem _ (cexQE_val_mem e).1 (cexQE_val_mem e).2))))
  right_inv j := by
    show cexLookE (cexArcOf cexRhoQ j) = j
    have key : ∀ ρ ∈ ({0, 1} : Finset (Fin 14)), ∀ j, cexLookE (cexArcOf ρ j) = j := by decide
    exact key _ cexRhoQ_mem j

theorem cexEdgeEquiv_symm_val (j : Fin 8) :
    (cexEdgeEquiv.symm j).1.1.1.1 = cexArcOf cexRhoQ j := rfl

/-- The taxa `A, B, C` of Figure 18: `b, c, e`. -/
def cexA : (cexS : Set (Fin 5)) := ⟨1, by simp [cexS]⟩
def cexB : (cexS : Set (Fin 5)) := ⟨2, by simp [cexS]⟩
def cexC : (cexS : Set (Fin 5)) := ⟨4, by simp [cexS]⟩
def cexD : (cexS : Set (Fin 5)) := ⟨0, by simp [cexS]⟩

/-- **`Q⁻` is isomorphic to Figure 18.** -/
def cexSDIso : SDIso cexQU (fig18 cexA cexB cexC) where
  vert := cexVert
  edge := cexEdgeEquiv
  isDirected_iff e := by
    rw [cexQU_isDirected_iff]
    show cexLookE e.1.1.1.1 = 6 ∨ cexLookE e.1.1.1.1 = 7 ↔ _
    have := (cexQE_val_mem e).1
    generalize e.1.1.1.1 = f at this
    revert f
    decide
  joins e := by
    show (_ = cexLookV (cexQU.graph.source e).1.1.1.1 ∧
        _ = cexLookV (cexQU.graph.target e).1.1.1.1) ∨
      (_ = cexLookV (cexQU.graph.target e).1.1.1.1 ∧ _ = cexLookV (cexQU.graph.source e).1.1.1.1)
    rw [cexQU_source_val, cexQU_target_val]
    show ((![4, 4, 6, 7, 5, 7, 7, 6] : Fin 8 → Fin 8) (cexLookE e.1.1.1.1) = _ ∧
        (![0, 1, 2, 3, 4, 6, 5, 5] : Fin 8 → Fin 8) (cexLookE e.1.1.1.1) = _) ∨
      ((![4, 4, 6, 7, 5, 7, 7, 6] : Fin 8 → Fin 8) (cexLookE e.1.1.1.1) = _ ∧
        (![0, 1, 2, 3, 4, 6, 5, 5] : Fin 8 → Fin 8) (cexLookE e.1.1.1.1) = _)
    have key : ∀ ρ ∈ ({0, 1} : Finset (Fin 14)), ∀ f ∈ cexKeptE, f ≠ ρ →
        ((![4, 4, 6, 7, 5, 7, 7, 6] : Fin 8 → Fin 8) (cexLookE f) = cexLookV (cexSrcQU ρ f) ∧
          (![0, 1, 2, 3, 4, 6, 5, 5] : Fin 8 → Fin 8) (cexLookE f) = cexLookV (cexTgtQ f)) ∨
        ((![4, 4, 6, 7, 5, 7, 7, 6] : Fin 8 → Fin 8) (cexLookE f) = cexLookV (cexTgtQ f) ∧
          (![0, 1, 2, 3, 4, 6, 5, 5] : Fin 8 → Fin 8) (cexLookE f) = cexLookV (cexSrcQU ρ f)) := by
      decide
    exact key _ cexRhoQ_mem _ (cexQE_val_mem e).1 (cexQE_val_mem e).2
  directed e he := by
    rw [cexQU_isDirected_iff] at he
    show (_ = cexLookV (cexQU.graph.source e).1.1.1.1) ∧
      (_ = cexLookV (cexQU.graph.target e).1.1.1.1)
    rw [cexQU_source_val, cexQU_target_val]
    show (![4, 4, 6, 7, 5, 7, 7, 6] : Fin 8 → Fin 8) (cexLookE e.1.1.1.1) = _ ∧
        (![0, 1, 2, 3, 4, 6, 5, 5] : Fin 8 → Fin 8) (cexLookE e.1.1.1.1) = _
    have key : ∀ ρ ∈ ({0, 1} : Finset (Fin 14)), ∀ f ∈ ({3, 5} : Finset (Fin 14)),
        (![4, 4, 6, 7, 5, 7, 7, 6] : Fin 8 → Fin 8) (cexLookE f) = cexLookV (cexSrcQU ρ f) ∧
          (![0, 1, 2, 3, 4, 6, 5, 5] : Fin 8 → Fin 8) (cexLookE f) = cexLookV (cexTgtQ f) := by
      decide
    exact key _ cexRhoQ_mem _ he
  leaf x := by
    show figLeaf cexA cexB cexC x = cexLookV (cexQU.leaf x).1.1.1.1
    rw [cexQU_leaf_val]
    obtain ⟨x, hx⟩ := x
    have hx' : x ∈ cexS := hx
    simp only [cexS, mem_insert, mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl | rfl <;> simp [figLeaf, cexA, cexB, cexC, cexLookV]

/-! ### The metric of `Q⁻` -/

section SuppressMetric

variable {V E X : Type*} {M : RootedNetwork V E X}

/-- The chain starting with an arc that enters a vertex that is not a chain vertex is that arc. -/
theorem isOnChain_iff_of_not_isChainVertex {f g : E} (h : ¬ M.IsChainVertex (M.graph.target f)) :
    M.IsOnChain f g ↔ g = f := by
  refine ⟨fun hg => ?_, fun hg => Or.inl hg⟩
  rcases hg with hg | ⟨hc, hr⟩
  · exact hg
  · rcases Relation.ReflTransGen.cases_head hr with h' | ⟨a, ha, -⟩
    · rw [← h'] at hc
      exact absurd hc h
    · exact absurd ha.1 h

/-- An arc of the suppressed network that is an arc of the network keeps its length. -/
theorem suppressMetric_length_of_not_isChainVertex {hE : Fintype E} (θ : MetricData E)
    (e : {e // ¬ M.IsChainVertex (M.graph.source e)}) (h : ¬ M.IsChainVertex (M.graph.target e.1)) :
    (M.suppressMetric θ).length e = θ.length e.1 := by
  simp only [RootedNetwork.suppressMetric]
  refine Finset.sum_eq_single_of_mem e.1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩)
    fun g hg hne => ?_
  exact absurd ((isOnChain_iff_of_not_isChainVertex h).1 (Finset.mem_filter.1 hg).2) hne

/-- An arc of the suppressed network that is an arc of the network keeps its inheritance. -/
theorem suppressMetric_inheritance_of_not_isChainVertex {hE : Fintype E} (θ : MetricData E)
    (e : {e // ¬ M.IsChainVertex (M.graph.source e)}) (h : ¬ M.IsChainVertex (M.graph.target e.1)) :
    (M.suppressMetric θ).inheritance e = θ.inheritance e.1 := by
  simp only [RootedNetwork.suppressMetric]
  refine Finset.prod_eq_single_of_mem e.1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩)
    fun g hg hne => ?_
  exact absurd ((isOnChain_iff_of_not_isChainVertex h).1 (Finset.mem_filter.1 hg).2) hne

end SuppressMetric

/-- The metric of `Q⁻` from parameters of `N`. -/
abbrev cexQUMetric (θ : MetricData (Fin 14)) :=
  unrootedMetric cexQ cexQ_isBinary cexQX
    (quartetLSAMetric cexNet cexNet_isBinaryRootedNetwork cexS cexS_card θ)

theorem cexQU_length (θ : MetricData (Fin 14)) (e : cexQE) (hs : cexSrc e.1.1.1.1 ≠ 5)
    (ht : cexTgt e.1.1.1.1 ∉ ({10, 11} : Finset (Fin 13))) :
    (cexQUMetric θ).length e = θ.length e.1.1.1.1 := by
  simp only [semidirectedMetric]
  rw [ite_eq_right (mt (cexQ_lsaPlus_source_eq_root_iff e).1 hs)]
  exact suppressMetric_length_of_not_isChainVertex (M := cexL) _ e.1.1
    ((cexL_isChainVertex_iff _).not.2 ht)

theorem cexQU_inheritance (θ : MetricData (Fin 14)) (e : cexQE)
    (ht : cexTgt e.1.1.1.1 ∉ ({10, 11} : Finset (Fin 13))) :
    (cexQUMetric θ).inheritance e = θ.inheritance e.1.1.1.1 :=
  suppressMetric_inheritance_of_not_isChainVertex (M := cexL) _ e.1.1
    ((cexL_isChainVertex_iff _).not.2 ht)

/-- The inheritance probabilities of the two hybrid edges of `u` sum to one. -/
theorem cexNet_inheritance_u {θ : MetricData (Fin 14)} (hθ : cexNet.IsMetric θ) :
    θ.inheritance 3 + θ.inheritance 5 = 1 := by
  have h := hθ.2.2.2.2 8 (by rw [cexNet_indegree]; decide)
  have h' : (∑ e : Fin 14, if cexTgt e = 8 then θ.inheritance e else 0) = 1 := by
    convert h using 3
    exact Iff.rfl
  rw [Finset.sum_eq_add (f := fun e : Fin 14 => if cexTgt e = 8 then θ.inheritance e else 0) 3 5
    (by decide) (fun c _ hc => ite_eq_right (by revert c; decide))
    (fun h => absurd (mem_univ _) h) (fun h => absurd (mem_univ _) h)] at h'
  rwa [ite_eq_left (show cexTgt 3 = 8 from rfl), ite_eq_left (show cexTgt 5 = 8 from rfl)] at h'

theorem cexArcOf_val (ρ : Fin 14) :
    cexArcOf ρ 4 = 6 ∧ cexArcOf ρ 5 = 2 ∧ cexArcOf ρ 6 = 3 ∧ cexArcOf ρ 7 = 5 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The metric `Q⁻` of `N` on `a, b, c, e` is Figure 18**, with the lengths of `u → w`, `t → p`,
`t → u`, `p → u` as `t₁`, `t₃`, `t₄`, `t₂`, and the inheritance probability of `t → u` as `γ`. -/
theorem cex_inducesNetwork {θ : MetricData (Fin 14)} (hθ : IsMetricNetwork cexNet θ)
    (hQ : IsLSAQuartet cexQ
      (quartetLSAMetric cexNet cexNet_isBinaryRootedNetwork cexS cexS_card θ)) :
    ∃ len : Fin 8 → ℝ, len 4 = θ.length 6 ∧ len 7 = θ.length 5 ∧ len 5 = θ.length 2 ∧
      len 6 = θ.length 3 ∧
      InducesNetwork hQ (fig18 cexA cexB cexC) (figMetric len (θ.inheritance 3)) := by
  have hlen : ∀ j : Fin 8, ∀ f : Fin 14, cexArcOf cexRhoQ j = f → cexSrc f ≠ 5 →
      cexTgt f ∉ ({10, 11} : Finset (Fin 13)) →
      (cexQUMetric θ).length (cexEdgeEquiv.symm j) = θ.length f := by
    intro j f hj hs ht
    rw [cexQU_length θ _ (by rw [cexEdgeEquiv_symm_val, hj]; exact hs)
      (by rw [cexEdgeEquiv_symm_val, hj]; exact ht), cexEdgeEquiv_symm_val, hj]
  obtain ⟨h4, h5, h6, h7⟩ := cexArcOf_val cexRhoQ
  refine ⟨fun j => (cexQUMetric θ).length (cexEdgeEquiv.symm j),
    hlen 4 6 h4 (by decide) (by decide), hlen 7 5 h7 (by decide) (by decide),
    hlen 5 2 h5 (by decide) (by decide), hlen 6 3 h6 (by decide) (by decide),
    ⟨⟨cexSDIso, fun e => ?_, fun e he => ?_⟩⟩⟩
  · show (cexQUMetric θ).length (cexEdgeEquiv.symm (cexEdgeEquiv e)) = _
    rw [Equiv.symm_apply_apply]
  · have he' := (cexQU_isDirected_iff e).1 he
    rw [cexQU_inheritance θ e (by
      have : ∀ f ∈ ({3, 5} : Finset (Fin 14)), cexTgt f ∉ ({10, 11} : Finset (Fin 13)) := by decide
      exact this _ he')]
    show (if cexLookE e.1.1.1.1 = 6 then θ.inheritance 3 else
      if cexLookE e.1.1.1.1 = 7 then 1 - θ.inheritance 3 else 1) = _
    simp only [mem_insert, mem_singleton] at he'
    rcases he' with h | h <;> rw [h]
    · rfl
    · simp only [show cexLookE 5 = 7 from rfl, show (7 : Fin 8) ≠ 6 from by decide, ite_false,
        ite_true]
      linarith [cexNet_inheritance_u hθ.1]

/-! ### The concordance factors on `{a, b, c, e}` -/

/-- `CF_{bc|ae}` (Example 5, `CF_{AB|CD}`), with `t₁, t₂, t₃, t₄` the lengths of `u → w`, `p → u`,
`t → p`, `t → u` and `γ` the inheritance probability of `t → u`. -/
def cexCF₁ (t₁ t₂ t₃ t₄ γ : ℝ) : ℝ :=
  (1 - γ) ^ 2 * (1 - 2 / 3 * (Real.exp (-t₁) * Real.exp (-t₂))) +
    2 * γ * (1 - γ) * (1 - Real.exp (-t₁) + 1 / 3 * (Real.exp (-t₁) * Real.exp (-t₃))) +
    γ ^ 2 * (1 - 2 / 3 * (Real.exp (-t₁) * Real.exp (-t₄)))

/-- `CF_{be|ac} = CF_{ab|ce}` (Example 5, `CF_{AC|BD} = CF_{AD|BC}`). -/
def cexCF₂ (t₁ t₂ t₃ t₄ γ : ℝ) : ℝ :=
  (1 - γ) ^ 2 * (1 / 3 * (Real.exp (-t₁) * Real.exp (-t₂))) +
    γ * (1 - γ) * Real.exp (-t₁) * (1 - 1 / 3 * Real.exp (-t₃)) +
    γ ^ 2 * (1 / 3 * (Real.exp (-t₁) * Real.exp (-t₄)))

theorem cex_map_quartetTree {a b c d : (cexS : Set (Fin 5))} (h : Distinct4 a b c d)
    (h' : Distinct4 a.1 b.1 c.1 d.1) :
    (quartetTree a b c d h).map Subtype.val_injective = quartetTree a.1 b.1 c.1 d.1 h' := by
  apply Subtype.ext
  simp [QuartetTree.map_val, quartetTree_val_eq_pair]

theorem cex_distinct4 : Distinct4 (1 : Fin 5) 2 4 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The concordance factors of the counterexample on `a, b, c, e`** (Theorem 2 and Example 5). -/
theorem cex_cf {θ : MetricData (Fin 14)} (hθ : IsMetricNetwork cexNet θ) :
    cf cexNet θ (quartetTree 1 2 4 0 cex_distinct4) =
        cexCF₁ (θ.length 6) (θ.length 5) (θ.length 2) (θ.length 3) (θ.inheritance 3) ∧
      cf cexNet θ (quartetTree 1 4 2 0 (distinct4_acbd cex_distinct4)) =
        cexCF₂ (θ.length 6) (θ.length 5) (θ.length 2) (θ.length 3) (θ.inheritance 3) ∧
      cf cexNet θ (quartetTree 1 0 2 4 (distinct4_adbc cex_distinct4)) =
        cexCF₂ (θ.length 6) (θ.length 5) (θ.length 2) (θ.length 3) (θ.inheritance 3) := by
  have hQ : IsLSAQuartet (quartetLSA cexNet cexNet_isBinaryRootedNetwork.1 _ cexS_card)
      (quartetLSAMetric cexNet cexNet_isBinaryRootedNetwork _ cexS_card θ) :=
    { binary := quartetLSA_isBinaryRootedNetwork cexNet_isBinaryRootedNetwork cexS_card
      levelOne := quartetLSA_isLevelOne cexNet_isBinaryRootedNetwork cexNet_isLevelOne cexS_card
      isLSA := quartetLSA_isLSANetwork cexNet_isBinaryRootedNetwork cexS_card
      card_taxa := by simp [cexS_card]
      metric := quartetLSA_isMetricNetwork cexNet_isBinaryRootedNetwork hθ cexS_card }
  obtain ⟨len, h4, h7, h5, h6, hiso⟩ := cex_inducesNetwork hθ hQ
  have hd : Distinct4 cexA cexB cexC cexD := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  have hex := example5 hd hQ len _ hiso
  simp only [CF, Prod.mk.injEq] at hex
  rw [h4, h5, h6, h7] at hex
  obtain ⟨e₁, e₂, e₃⟩ := hex
  have hcf := cf_quartetLSA cexNet_isBinaryRootedNetwork cexNet_isLevelOne hθ cexS_card
  have hinst : (fun a b => Classical.propDecidable (a = b) : DecidableEq (Fin 5)) =
      instDecidableEqFin 5 := Subsingleton.elim _ _
  have t₁ := (congrFun hcf (quartetTree cexA cexB cexC cexD hd)).symm.trans e₁
  have t₂ := (congrFun hcf (quartetTree cexA cexC cexB cexD (distinct4_acbd hd))).symm.trans e₂
  have t₃ := (congrFun hcf (quartetTree cexA cexD cexB cexC (distinct4_adbc hd))).symm.trans e₃
  rw [hinst] at t₁ t₂ t₃
  rw [cex_map_quartetTree hd cex_distinct4] at t₁
  rw [cex_map_quartetTree (distinct4_acbd hd) (distinct4_acbd cex_distinct4)] at t₂
  rw [cex_map_quartetTree (distinct4_adbc hd) (distinct4_adbc cex_distinct4)] at t₃
  exact ⟨t₁, t₂, t₃⟩

/-! ### An open set of parameters -/

/-- The parameters of `N` at the coordinates `x`: the lengths `x.1`, the inheritance probabilities
`x.2 3`, `1 - x.2 3` of `t → u`, `p → u`, and `x.2 10`, `1 - x.2 10` of `x → v`, `y → v`. -/
def cexParams (x : (Fin 14 → ℝ) × (Fin 14 → ℝ)) : MetricData (Fin 14) :=
  ⟨x.1, fun e => if e = 3 then x.2 3 else if e = 5 then 1 - x.2 3 else if e = 10 then x.2 10
    else if e = 12 then 1 - x.2 10 else 1⟩

/-- The parents left out of the coordinates: `p → u` at `u`, `y → v` at `v`. -/
def cexLeftOut (v : Fin 13) : Fin 14 := if v = 8 then 5 else 12

theorem cexLeftOut_spec :
    ∀ v, 2 ≤ cexNet.graph.indegree v → cexNet.graph.target (cexLeftOut v) = v := by
  intro v hv
  rw [cexNet_indegree] at hv
  revert v
  decide

/-- The coordinates of valid parameters at which `CF_{bc|ae} < CF_{be|ac}`. -/
def cexOpen : Set ((Fin 14 → ℝ) × (Fin 14 → ℝ)) :=
  {x | (∀ e, 0 < x.1 e) ∧ 0 < x.2 3 ∧ x.2 3 < 1 ∧ 0 < x.2 10 ∧ x.2 10 < 1 ∧
    cexCF₁ (x.1 6) (x.1 5) (x.1 2) (x.1 3) (x.2 3) < cexCF₂ (x.1 6) (x.1 5) (x.1 2) (x.1 3) (x.2 3)}

theorem isOpen_cexOpen : IsOpen cexOpen := by
  have hfst : ∀ e : Fin 14, Continuous fun x : (Fin 14 → ℝ) × (Fin 14 → ℝ) => x.1 e :=
    fun e => (continuous_apply e).comp continuous_fst
  have hsnd : ∀ e : Fin 14, Continuous fun x : (Fin 14 → ℝ) × (Fin 14 → ℝ) => x.2 e :=
    fun e => (continuous_apply e).comp continuous_snd
  have h₁ : Continuous fun x : (Fin 14 → ℝ) × (Fin 14 → ℝ) =>
      cexCF₁ (x.1 6) (x.1 5) (x.1 2) (x.1 3) (x.2 3) := by
    unfold cexCF₁
    fun_prop
  have h₂ : Continuous fun x : (Fin 14 → ℝ) × (Fin 14 → ℝ) =>
      cexCF₂ (x.1 6) (x.1 5) (x.1 2) (x.1 3) (x.2 3) := by
    unfold cexCF₂
    fun_prop
  simp only [cexOpen, Set.ofPred_and, Set.ofPred_forall]
  exact (isOpen_iInter_of_finite fun e => isOpen_lt continuous_const (hfst e)).inter
    ((isOpen_lt continuous_const (hsnd 3)).inter ((isOpen_lt (hsnd 3) continuous_const).inter
      ((isOpen_lt continuous_const (hsnd 10)).inter ((isOpen_lt (hsnd 10) continuous_const).inter
        (isOpen_lt h₁ h₂)))))

/-- The parameters of Example 6: `γ = 1/2`, `t₁ = t₂ = -log(6/7)`, `t₃ = -log(1/14)`,
`t₄ = -log(13/14)`, all other lengths `1`. -/
def cexPoint : (Fin 14 → ℝ) × (Fin 14 → ℝ) :=
  (fun e => if e = 6 then -Real.log (6 / 7) else if e = 5 then -Real.log (6 / 7)
    else if e = 2 then -Real.log (1 / 14) else if e = 3 then -Real.log (13 / 14) else 1,
    fun _ => 1 / 2)

/-- At the parameters of Example 6, `CF = (32/98, 33/98, 33/98)`. -/
theorem cexPoint_mem : cexPoint ∈ cexOpen := by
  have hlog : ∀ q : ℝ, 0 < q → q < 1 → 0 < -Real.log q := fun q h₀ h₁ =>
    neg_pos.2 (Real.log_neg h₀ h₁)
  have hexp : ∀ q : ℝ, 0 < q → Real.exp (-(-Real.log q)) = q := fun q h => by
    rw [neg_neg, Real.exp_log h]
  refine ⟨fun e => ?_, by norm_num [cexPoint], by norm_num [cexPoint], by norm_num [cexPoint],
    by norm_num [cexPoint], ?_⟩
  · simp only [cexPoint]
    split_ifs
    · exact hlog _ (by norm_num) (by norm_num)
    · exact hlog _ (by norm_num) (by norm_num)
    · exact hlog _ (by norm_num) (by norm_num)
    · exact hlog _ (by norm_num) (by norm_num)
    · norm_num
  · simp only [cexPoint, cexCF₁, cexCF₂, show (6 : Fin 14) ≠ 5 from by decide,
      show (6 : Fin 14) ≠ 2 from by decide, show (6 : Fin 14) ≠ 3 from by decide,
      show (5 : Fin 14) ≠ 6 from by decide, show (5 : Fin 14) ≠ 2 from by decide,
      show (2 : Fin 14) ≠ 6 from by decide, show (2 : Fin 14) ≠ 5 from by decide,
      show (3 : Fin 14) ≠ 6 from by decide, show (3 : Fin 14) ≠ 5 from by decide,
      show (3 : Fin 14) ≠ 2 from by decide, ite_true, ite_false]
    rw [hexp _ (by norm_num), hexp _ (by norm_num), hexp _ (by norm_num)]
    norm_num

theorem cexParams_isMetricNetwork {x : (Fin 14 → ℝ) × (Fin 14 → ℝ)} (hx : x ∈ cexOpen) :
    IsMetricNetwork cexNet (cexParams x) := by
  obtain ⟨hl, h₃, h₃', h₁₀, h₁₀', -⟩ := hx
  refine ⟨⟨fun e _ => hl e, fun e _ => (hl e).le, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩,
    hl⟩
  · rw [cexNet_isTreeArc_iff] at he
    simp only [mem_insert, mem_singleton, not_or] at he
    obtain ⟨n₃, n₅, n₁₀, n₁₂⟩ := he
    simp [cexParams, n₃, n₅, n₁₀, n₁₂]
  · rw [cexNet_isHybridArc_iff] at he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp [cexParams] <;> linarith
  · rw [cexNet_indegree] at hv
    have hv' : v = 8 ∨ v = 12 := by revert v; decide
    rcases hv' with rfl | rfl
    · rw [Finset.sum_eq_add 3 5 (by decide)]
      · rw [ite_eq_left (show cexNet.graph.target 3 = 8 from rfl),
          ite_eq_left (show cexNet.graph.target 5 = 8 from rfl)]
        simp [cexParams]
      · intro c _ hc
        exact ite_eq_right (by revert c; decide)
      · exact fun h => absurd (mem_univ _) h
      · exact fun h => absurd (mem_univ _) h
    · rw [Finset.sum_eq_add 10 12 (by decide)]
      · rw [ite_eq_left (show cexNet.graph.target 10 = 12 from rfl),
          ite_eq_left (show cexNet.graph.target 12 = 12 from rfl)]
        simp [cexParams]
      · intro c _ hc
        exact ite_eq_right (by revert c; decide)
      · exact fun h => absurd (mem_univ _) h
      · exact fun h => absurd (mem_univ _) h

theorem cexParams_inheritance (x : (Fin 14 → ℝ) × (Fin 14 → ℝ)) :
    ∀ e, cexNet.IsHybridArc e → e ≠ cexLeftOut (cexNet.graph.target e) →
      (cexParams x).inheritance e = x.2 e := by
  intro e he hd
  rw [cexNet_isHybridArc_iff] at he
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd rfl hd
  · rfl
  · exact absurd rfl hd

/-- **When `CF_{bc|ae} < CF_{be|ac}`, `{a, b, c, e}` satisfies the Cycle property but not the Big
Cycle property**: `CF_{be|ac} = CF_{ab|ce}`, and the smallest concordance factor is unique. -/
theorem cex_cycleProperty {θ : MetricData (Fin 14)} (hθ : IsMetricNetwork cexNet θ)
    (hlt : cexCF₁ (θ.length 6) (θ.length 5) (θ.length 2) (θ.length 3) (θ.inheritance 3) <
      cexCF₂ (θ.length 6) (θ.length 5) (θ.length 2) (θ.length 3) (θ.inheritance 3)) :
    CyclePropertyOn (cf cexNet θ) {0, 1, 2, 4} ∧ ¬ BigCycleOn (cf cexNet θ) {0, 1, 2, 4} := by
  have hset : ({0, 1, 2, 4} : Finset (Fin 5)) = {1, 2, 4, 0} := by decide
  obtain ⟨c₁, c₂, c₃⟩ := cex_cf hθ
  rw [hset]
  refine ⟨?_, ?_⟩
  · unfold CyclePropertyOn
    rw [isTreelikeOn_iff_triple _ cex_distinct4]
    simp only [c₁, c₂, c₃]
    rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> linarith
  · rw [bigCycleOn_iff_triple _ cex_distinct4, c₂, c₃]
    rintro ⟨-, -, h⟩
    exact h rfl

/-- **Proposition 13 as printed fails for the counterexample**: the parameters at which
`{a, b, c, e}` satisfies the Cycle property but not the Big Cycle property, while `e` is not in the
hybrid block of `C_v`, contain an open set. -/
theorem cex_not_forGenericParams : ¬ ForGenericParams cexNet fun θ => IsMetricNetwork cexNet θ →
    ∀ i ∈ ({0, 1, 2, 3} : Finset (Fin 5)), ∀ j ∈ ({0, 1, 2, 3} : Finset (Fin 5)),
      ∀ k ∈ ({0, 1, 2, 3} : Finset (Fin 5)), i ≠ j → i ≠ k → j ≠ k → ∀ e,
        #({i, j, k, e} : Finset (Fin 5)) = 4 → CyclePropertyOn (cf cexNet θ) {i, j, k, e} →
        ¬ BigCycleOn (cf cexNet θ) {i, j, k, e} → DescendsFrom cexUnrooted cexV e := by
  intro hgen
  have h0 := hgen cexLeftOut cexLeftOut_spec
  refine isOpen_cexOpen.measure_ne_zero _ ⟨_, cexPoint_mem⟩ (MeasureTheory.measure_mono_null ?_ h0)
  intro x hx
  have hθ := cexParams_isMetricNetwork hx
  obtain ⟨hcp, hbc⟩ := cex_cycleProperty hθ hx.2.2.2.2.2
  refine ⟨cexParams x, fun hP => cex_not_descendsFrom ?_, hθ.1, rfl, cexParams_inheritance x⟩
  exact hP hθ 0 (by decide) 1 (by decide) 2 (by decide) (by decide) (by decide) (by decide) 4
    (by decide) hcp hbc

/-- **The counterexample to Proposition 13 as printed.** -/
theorem proposition13AsPrinted_counterexample :
    ¬ ∀ (V E X : Type) [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
    (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph → ∀ (hX : Nontrivial X) (C : Set _)
    (v : SemidirectedVertex hN.1 hX), IsCycle (unrooted N hN hX).graph C → C.ncard = 4 →
    IsHybridNodeOf (unrooted N hN hX) C v → ∀ a b c d : X,
    (∀ x ∈ ({a, b, c, d} : Finset X), ∀ y ∈ ({a, b, c, d} : Finset X), x ≠ y →
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) →
    ForGenericParams N fun θ => IsMetricNetwork N θ →
      ∀ i ∈ ({a, b, c, d} : Finset X), ∀ j ∈ ({a, b, c, d} : Finset X),
        ∀ k ∈ ({a, b, c, d} : Finset X), i ≠ j → i ≠ k → j ≠ k → ∀ e,
          #({i, j, k, e} : Finset X) = 4 → CyclePropertyOn (cf N θ) {i, j, k, e} →
          ¬ BigCycleOn (cf N θ) {i, j, k, e} → DescendsFrom (unrooted N hN hX) v e := by
  intro H
  exact cex_not_forGenericParams (H (Fin 13) (Fin 14) (Fin 5) cexNet cexNet_isBinaryRootedNetwork
    cexNet_isLevelOne cexHX cexCv cexV cexCv_isCycle cexCv_ncard cexV_isHybridNodeOf 0 1 2 3
    cex_blocks)

end Banos2019
