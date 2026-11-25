module

public import Banos2019.Quartet.Concrete

/-!
# Figure 15 as an LSA quartet network (Example 2)

The `2₂`-cycle of Figure 15 is the unrooted network of the LSA quartet network `q15 a b c`: the nodes
`0, 1, 2, 3` are the leaves `a, b, c, d`; `4` is the parent of `a` and `b`, `7` that of `c` and `d`; `5`
and the hybrid node `6` above `7` are the nodes of the cycle; the root `8` has the hybrid edge `8 → 6`
and the tree edge `8 → 5`, which the unrooted network merges into the hybrid edge `5 → 6` of Figure 15.
`inducesNetwork_q15`, with the figures in `Banos2019.Quartet.Examples`, shows that the unrooted network
of `q15 a b c` is Figure 15.

* `isLSAQuartet_q15`, `inducesCycleType_q15`: `q15 a b c` with the parameters `q15Metric len γ` is an
  LSA quartet network with a `2₂`-cycle, whose hybrid edges are `6` (inheritance `γ`) and `7`.
* `cf_deleteArc_q15_seven`, `cf_deleteArc_q15_six`, `cf_contractRooted_q15`: the networks `Q₁⊕`, `Q₂⊕`,
  `Q₀⊕` of Lemma 9 are trees, with the internal edges `ab|cd` of lengths `t₁ + t₂ + t₄`,
  `t₁ + t₂ + t₃` and `t₁ + t₂` (equation (1)).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace Banos2019

/-- The tails of the edges of `q15`. -/
def q15Src : Fin 9 → Fin 9 := ![4, 4, 7, 7, 5, 6, 5, 8, 8]

/-- The heads of the edges of `q15`. -/
def q15Tgt : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 7, 6, 6, 5]

variable {X : Type*} [DecidableEq X]

/-- **Figure 15 as a rooted network**, with the root on the hybrid edge `7` from the node `5`. -/
def q15 (a b c : X) : RootedNetwork (Fin 9) (Fin 9) X :=
  ⟨⟨q15Src, q15Tgt⟩, 8, quartetLeaf9 a b c⟩

/-- The parameters of `q15`: those of Figure 15, the length `len 7` of the merged hybrid edge shared by
the two edges at the root. -/
def q15Metric (len : Fin 8 → ℝ) (γ : ℝ) : MetricData (Fin 9) :=
  ⟨![len 0, len 1, len 2, len 3, len 4, len 5, len 6, len 7 / 2, len 7 / 2],
    ![1, 1, 1, 1, 1, 1, γ, 1 - γ, 1]⟩

variable {a b c d : X}

section Network

theorem q15_indegree (v : Fin 9) :
    (q15 a b c).graph.indegree v = (univ.filter fun e => q15Tgt e = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [q15]

theorem q15_outdegree (v : Fin 9) :
    (q15 a b c).graph.outdegree v = (univ.filter fun e => q15Src e = v).card := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [q15]

/-- The indegrees of `q15` without the edge `h`. -/
theorem deleteArc_q15_indegree (h v : Fin 9) :
    (deleteArc (q15 a b c) h).graph.indegree v =
      (univ.filter fun e : {e : Fin 9 // e ≠ h} => q15Tgt e.1 = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [deleteArc, q15]

variable [Fintype X]

theorem q15_isPhylogenetic (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    (q15 a b c).IsPhylogenetic where
  finite_vertices := inferInstance
  finite_arcs := inferInstance
  finite_taxa := inferInstance
  acyclic := DirectedMultigraph.isAcyclic_of_rank _ (fun v : Fin 9 => ![4, 4, 4, 4, 2, 1, 2, 3, 0] v)
    (by show ∀ e, ![4, 4, 4, 4, 2, 1, 2, 3, 0] (q15Src e) < ![4, 4, 4, 4, 2, 1, 2, 3, 0] (q15Tgt e)
        decide)
  root_reaches v := by
    have h85 : (q15 a b c).graph.Adj 8 5 := ⟨8, rfl, rfl⟩
    have h86 : (q15 a b c).graph.Adj 8 6 := ⟨7, rfl, rfl⟩
    have h54 : (q15 a b c).graph.Adj 5 4 := ⟨4, rfl, rfl⟩
    have h67 : (q15 a b c).graph.Adj 6 7 := ⟨5, rfl, rfl⟩
    have h40 : (q15 a b c).graph.Adj 4 0 := ⟨0, rfl, rfl⟩
    have h41 : (q15 a b c).graph.Adj 4 1 := ⟨1, rfl, rfl⟩
    have h72 : (q15 a b c).graph.Adj 7 2 := ⟨2, rfl, rfl⟩
    have h73 : (q15 a b c).graph.Adj 7 3 := ⟨3, rfl, rfl⟩
    show Relation.ReflTransGen _ 8 v
    fin_cases v
    · exact ((Relation.ReflTransGen.single h85).tail h54).tail h40
    · exact ((Relation.ReflTransGen.single h85).tail h54).tail h41
    · exact ((Relation.ReflTransGen.single h86).tail h67).tail h72
    · exact ((Relation.ReflTransGen.single h86).tail h67).tail h73
    · exact (Relation.ReflTransGen.single h85).tail h54
    · exact Relation.ReflTransGen.single h85
    · exact Relation.ReflTransGen.single h86
    · exact (Relation.ReflTransGen.single h86).tail h67
    · exact .refl
  root_indegree := by
    rw [q15_indegree]
    show #(univ.filter fun e => q15Tgt e = 8) = 0
    decide
  nonroot_indegree v hv := by
    rw [q15_indegree]
    fin_cases v <;> first | decide | exact absurd rfl hv
  leaf_injective := quartetLeaf9_injective hX h
  leaf_indegree x := by
    rw [q15_indegree]
    have := quartetLeaf9_mem (a := a) (b := b) (c := c) x
    simp only [mem_insert, mem_singleton] at this
    show #(univ.filter fun e => q15Tgt e = quartetLeaf9 a b c x) = 1
    rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide
  leaves v := by
    rw [q15_outdegree]
    constructor
    · intro h0
      fin_cases v
      · exact ⟨a, quartetLeaf9_a⟩
      · exact ⟨b, quartetLeaf9_b h⟩
      · exact ⟨c, quartetLeaf9_c h⟩
      · exact ⟨d, quartetLeaf9_d h⟩
      all_goals exact absurd h0 (by decide)
    · rintro ⟨x, rfl⟩
      have := quartetLeaf9_mem (a := a) (b := b) (c := c) x
      simp only [mem_insert, mem_singleton] at this
      show #(univ.filter fun e => q15Src e = quartetLeaf9 a b c x) = 0
      rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide

omit [Fintype X] in
theorem q15_isBinary (a b c : X) : (q15 a b c).IsBinary := by
  refine ⟨by rw [q15_outdegree]; show #(univ.filter fun e => q15Src e = 8) = 2; decide,
    fun v hv h0 => ?_⟩
  rw [q15_indegree, q15_outdegree]
  rw [q15_outdegree] at h0
  fin_cases v <;> first | decide | exact absurd rfl hv | exact absurd (by decide) h0

theorem q15_isBinaryRootedNetwork (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    IsBinaryRootedNetwork (q15 a b c) :=
  ⟨q15_isPhylogenetic hX h, q15_isBinary a b c⟩

end Network

/-! ### The cycle -/

/-- The edges `8 → 5`, `5 → 6`, `8 → 6` of the cycle of `q15`. -/
def q15Cycle : Finset (Fin 9) := {6, 7, 8}

/-- The cycle `8, 5, 6` of `q15`. -/
theorem q15_isCycle : IsCycle (q15 a b c).graph ↑q15Cycle := by
  refine ⟨3, ![8, 5, 6], ![8, 6, 7], ⟨by decide, ?_, by decide, by decide⟩, ?_⟩
  · show ∀ i : Fin 3, (q15Src (![8, 6, 7] i) = ![8, 5, 6] i ∧
        q15Tgt (![8, 6, 7] i) = ![8, 5, 6] (finRotate 3 i)) ∨
      (q15Src (![8, 6, 7] i) = ![8, 5, 6] (finRotate 3 i) ∧
        q15Tgt (![8, 6, 7] i) = ![8, 5, 6] i)
    decide
  · ext f
    simp only [Set.mem_range, q15Cycle, coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨1, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩]

/-- **The only cycle of `q15`**: the edges to the leaves are on no cycle, then neither are the edges to
the nodes `4` and `7` above two leaves, and the three edges left, with at most two at each node, form
one. -/
theorem q15_cycle_eq {C : Set (Fin 9)} (hC : IsCycle (q15 a b c).graph C) : C = ↑q15Cycle := by
  have hloop : ∀ f, (q15 a b c).graph.source f ≠ (q15 a b c).graph.target f := by
    show ∀ f, q15Src f ≠ q15Tgt f
    decide
  -- the edges to the leaves, then the edges `5 → 4` and `6 → 7`
  have hpend₁ : ∀ f : Fin 9, f ∉ ({4, 5, 6, 7, 8} : Finset (Fin 9)) → ∃ p : Fin 9,
      (q15Src f = p ∨ q15Tgt f = p) ∧ ∀ g, (q15Src g = p ∨ q15Tgt g = p) → g = f := by decide
  have hsub₁ : C ⊆ ↑({4, 5, 6, 7, 8} : Finset (Fin 9)) := hC.subset_of_pendant hloop
    (Set.subset_univ _) fun f _ hf =>
      (hpend₁ f (by simpa using hf)).imp fun _ h => ⟨h.1, fun g _ => h.2 g⟩
  have hpend₂ : ∀ f ∈ ({4, 5, 6, 7, 8} : Finset (Fin 9)), f ∉ q15Cycle → ∃ p : Fin 9,
      (q15Src f = p ∨ q15Tgt f = p) ∧ ∀ g ∈ ({4, 5, 6, 7, 8} : Finset (Fin 9)),
        (q15Src g = p ∨ q15Tgt g = p) → g = f := by decide
  have hsub : C ⊆ ↑q15Cycle := hC.subset_of_pendant hloop hsub₁ fun f hf hf' =>
    hpend₂ f (by simpa using hf) (by simpa using hf')
  obtain ⟨f₀, hf₀⟩ : C.Nonempty := by
    obtain ⟨k, v, e, hcyc, rfl⟩ := hC
    exact ⟨e ⟨0, hcyc.pos⟩, ⟨_, rfl⟩⟩
  have hdeg : ∀ x, {f | f ∈ (↑q15Cycle : Set (Fin 9)) ∧ ((q15 a b c).graph.source f = x ∨
      (q15 a b c).graph.target f = x)}.ncard ≤ 2 := by
    intro x
    have e : {f | f ∈ (↑q15Cycle : Set (Fin 9)) ∧ ((q15 a b c).graph.source f = x ∨
        (q15 a b c).graph.target f = x)} =
        ↑(q15Cycle.filter fun f => q15Src f = x ∨ q15Tgt f = x) := by
      ext f
      simp only [Set.mem_ofPred_eq, coe_filter, mem_coe]
      rfl
    have key : ∀ x : Fin 9, #(q15Cycle.filter fun f => q15Src f = x ∨ q15Tgt f = x) ≤ 2 := by
      decide
    rw [e, Set.ncard_coe_finset]
    exact key x
  -- the nodes of the cycle are joined to `8` along its edges
  have h85 : (q15 a b c).graph.AdjOn ↑q15Cycle 8 5 := ⟨8, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have hw : ∀ y : Fin 9, y = 5 ∨ y = 8 → (q15 a b c).graph.Walks ↑q15Cycle 8 y := by
    rintro y (rfl | rfl)
    · exact Relation.ReflTransGen.single h85
    · exact .refl
  have hsrc : ∀ f ∈ q15Cycle, q15Src f = 5 ∨ q15Src f = 8 := by decide
  have hconn : ∀ f ∈ (↑q15Cycle : Set (Fin 9)),
      (q15 a b c).graph.Walks ↑q15Cycle ((q15 a b c).graph.source f₀) ((q15 a b c).graph.source f) :=
    fun f hf => ((q15 a b c).graph.walks_symm (hw _ (hsrc f₀ (hsub hf₀)))).trans
      (hw _ (hsrc f (by simpa using hf)))
  exact hsub.antisymm (hC.superset_of_ncard_incident_le hloop hsub hdeg (source_mem_cycleNodes hf₀)
    hconn)

theorem q15_isLevelOne : IsLevelOne (q15 a b c).graph := fun _ _ hC hC' _ =>
  (q15_cycle_eq hC).trans (q15_cycle_eq hC').symm

/-- The nodes of the cycle of `q15`. -/
theorem q15_cycleNodes : cycleNodes (q15 a b c).graph ↑q15Cycle = ↑({5, 6, 8} : Finset (Fin 9)) := by
  ext y
  have key : ∀ y : Fin 9, (∃ e ∈ q15Cycle, q15Src e = y ∨ q15Tgt e = y) ↔
      y ∈ ({5, 6, 8} : Finset (Fin 9)) := by decide
  simp only [cycleNodes, Set.mem_ofPred_eq, mem_coe]
  exact key y

/-! ### The root is the LSA -/

theorem q15_isLSANetwork (h : Distinct4 a b c d) : (q15 a b c).IsLSANetwork := by
  refine ⟨root_isStableAncestor _ _, fun w hw => ?_⟩
  suffices hw8 : w = 8 by rw [hw8]; exact .refl
  by_contra hne
  have hla : (q15 a b c).leaf a = 0 := quartetLeaf9_a
  have hlc : (q15 a b c).leaf c = 2 := quartetLeaf9_c h
  by_cases h672 : w = 6 ∨ w = 7 ∨ w = 2
  · -- the path `8 → 5 → 4 → 0` to `a` avoids `w`
    have hw5 : w ≠ 5 := by rcases h672 with rfl | rfl | rfl <;> decide
    have hw4 : w ≠ 4 := by rcases h672 with rfl | rfl | rfl <;> decide
    have hw0 : w ≠ 0 := by rcases h672 with rfl | rfl | rfl <;> decide
    refine hw a (Set.mem_univ _) ?_
    rw [hla]
    exact ⟨Ne.symm hne, Ne.symm hw0, ((Relation.ReflTransGen.single
      ⟨⟨8, rfl, rfl⟩, Ne.symm hne, Ne.symm hw5⟩).tail ⟨⟨4, rfl, rfl⟩, Ne.symm hw5, Ne.symm hw4⟩).tail
        ⟨⟨0, rfl, rfl⟩, Ne.symm hw4, Ne.symm hw0⟩⟩
  · -- the path `8 → 6 → 7 → 2` to `c` avoids `w`
    have hw6 : w ≠ 6 := fun e => h672 (Or.inl e)
    have hw7 : w ≠ 7 := fun e => h672 (Or.inr (Or.inl e))
    have hw2 : w ≠ 2 := fun e => h672 (Or.inr (Or.inr e))
    refine hw c (Set.mem_univ _) ?_
    rw [hlc]
    exact ⟨Ne.symm hne, Ne.symm hw2, ((Relation.ReflTransGen.single
      ⟨⟨7, rfl, rfl⟩, Ne.symm hne, Ne.symm hw6⟩).tail ⟨⟨5, rfl, rfl⟩, Ne.symm hw6, Ne.symm hw7⟩).tail
        ⟨⟨2, rfl, rfl⟩, Ne.symm hw7, Ne.symm hw2⟩⟩

/-! ### The parameters -/

theorem q15_isHybridArc_iff (e : Fin 9) : (q15 a b c).IsHybridArc e ↔ e = 6 ∨ e = 7 := by
  unfold IsHybridArc
  rw [q15_indegree]
  show 2 ≤ #(univ.filter fun f => q15Tgt f = q15Tgt e) ↔ e = 6 ∨ e = 7
  revert e
  decide

theorem q15_isTreeArc_iff (e : Fin 9) : (q15 a b c).IsTreeArc e ↔ ¬ (e = 6 ∨ e = 7) := by
  unfold IsTreeArc
  rw [q15_indegree]
  show #(univ.filter fun f => q15Tgt f = q15Tgt e) = 1 ↔ ¬ (e = 6 ∨ e = 7)
  revert e
  decide

theorem q15Metric_isMetricNetwork {len : Fin 8 → ℝ} (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ)
    (hγ₁ : γ < 1) : IsMetricNetwork (q15 a b c) (q15Metric len γ) := by
  have hpos : ∀ e, 0 < (q15Metric len γ).length e := by
    intro e
    fin_cases e <;> simp [q15Metric, hlen]
  refine ⟨⟨fun e _ => hpos e, fun e _ => (hpos e).le, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩,
    hpos⟩
  · rw [q15_isTreeArc_iff] at he
    fin_cases e <;> simp_all [q15Metric]
  · rw [q15_isHybridArc_iff] at he
    rcases he with rfl | rfl
    · simpa [q15Metric] using hγ₀
    · simpa [q15Metric] using hγ₁
  · rw [q15_indegree] at hv
    have hv6 : v = 6 := by revert v; decide
    subst hv6
    simp [Fin.sum_univ_succ, q15Metric, q15, q15Tgt]

theorem isLSAQuartet_q15 [Fintype X] (hX : Fintype.card X = 4) (h : Distinct4 a b c d)
    {len : Fin 8 → ℝ} (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    IsLSAQuartet (q15 a b c) (q15Metric len γ) :=
  ⟨q15_isBinaryRootedNetwork hX h, q15_isLevelOne, q15_isLSANetwork h, hX,
    q15Metric_isMetricNetwork hlen hγ₀ hγ₁⟩

/-- The descendants of the nodes of `q15`. -/
def q15Desc : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {4, 0, 1}, {5, 4, 0, 1, 6, 7, 2, 3}, {6, 7, 2, 3}, {7, 2, 3}, univ]

theorem q15_reaches_iff (u w : Fin 9) : (q15 a b c).graph.Reaches u w ↔ w ∈ q15Desc u :=
  reaches_iff_mem_of_desc q15Desc (by decide)
    (by show ∀ u e, q15Src e ∈ q15Desc u → q15Tgt e ∈ q15Desc u
        decide)
    (by show ∀ u, ∀ w ∈ q15Desc u, w ≠ u → ∃ e, q15Src e = u ∧
          w ∈ q15Desc (q15Tgt e) ∧ #(q15Desc (q15Tgt e)) < #(q15Desc u)
        decide) u w

/-- **The cycle of `q15` induces a `2₂`-cycle**, with hybrid node `6` above `c` and `d`. -/
theorem inducesCycleType_q15 [Fintype X] (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    InducesCycleType (q15 a b c) ↑q15Cycle 6 2 2 := by
  refine ⟨q15_isCycle, ⟨6, by decide, Or.inr rfl⟩, by rw [q15_indegree]; decide, ?_, ?_⟩
  · have h8 : (q15 a b c).root ∈ cycleNodes (q15 a b c).graph ↑q15Cycle :=
      ⟨8, by decide, Or.inl rfl⟩
    rw [ite_eq_left h8, Set.ncard_coe_finset]
    decide
  · have hset : {x | (q15 a b c).graph.Reaches 6 ((q15 a b c).leaf x)} = {c, d} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, q15_reaches_iff]
      obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
      rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl
      · rw [show (q15 x b c).leaf x = 0 from quartetLeaf9_a]
        simp only [hac, had, or_self, iff_false]
        decide
      · rw [show (q15 a x c).leaf x = 1 from quartetLeaf9_b h]
        simp only [hbc, hbd, or_self, iff_false]
        decide
      · rw [show (q15 a b x).leaf x = 2 from quartetLeaf9_c h]
        simp only [true_or, iff_true]
        decide
      · rw [show (q15 a b c).leaf x = 3 from quartetLeaf9_d h]
        simp only [or_true, iff_true]
        decide
    rw [hset, Set.ncard_pair h.2.2.2.2.2]

/-! ### The trees of Lemma 9 -/

section Trees

variable [Fintype X]

/-- The descendants of the nodes of `q15` without the hybrid edge `6`. -/
def q15DescSix : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {4, 0, 1}, {5, 4, 0, 1}, {6, 7, 2, 3}, {7, 2, 3}, univ]

/-- The edges `5 → 4`, `6 → 7`, `5 → 6` of `q15` without the hybrid edge `7`. -/
def q15ArcsSeven : Finset {e : Fin 9 // e ≠ 7} := {⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩}

/-- The edges `5 → 4`, `6 → 7`, `8 → 6`, `8 → 5` of `q15` without the hybrid edge `6`. -/
def q15ArcsSix : Finset {e : Fin 9 // e ≠ 6} :=
  {⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩}

theorem leafSet_ab (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    leafSet (quartetLeaf9 a b c) {0, 1} = {a, b} := by
  ext x
  rw [leafSet_quartetLeaf9 hX h]
  simp only [mem_insert, mem_singleton]
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]

theorem leafSet_cd (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    leafSet (quartetLeaf9 a b c) {2, 3} = {a, b}ᶜ := by
  ext x
  rw [leafSet_quartetLeaf9 hX h]
  simp only [mem_compl, mem_insert, mem_singleton]
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]

/-- **`q15` without the hybrid edge `7` is a tree with the split `ab|cd`**, of length `t₁ + t₂ + t₄`
(equation (1)). -/
theorem cf_deleteArc_q15_seven (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    let x := Real.exp (-len 4) * Real.exp (-len 5) * Real.exp (-len 6)
    cf (deleteArc (q15 a b c) 7) (deleteArcMetric (q15 a b c) 7 (q15Metric len γ))
        (quartetTree a b c d h) = 1 - 2 / 3 * x ∧
      cf (deleteArc (q15 a b c) 7) (deleteArcMetric (q15 a b c) 7 (q15Metric len γ))
        (quartetTree a c b d (distinct4_acbd h)) = 1 / 3 * x ∧
      cf (deleteArc (q15 a b c) 7) (deleteArcMetric (q15 a b c) 7 (q15Metric len γ))
        (quartetTree a d b c (distinct4_adbc h)) = 1 / 3 * x := by
  intro x
  have hQ := isLSAQuartet_q15 hX h hlen hγ₀ hγ₁
  have hN : (deleteArc (q15 a b c) 7).IsPhylogenetic :=
    isPhylogenetic_deleteArc hQ.binary.1 (h' := 6) (g := 8) (by decide) rfl (by decide) rfl
  have ht : ∀ e, ¬ (deleteArc (q15 a b c) 7).IsHybridArc e := by
    intro e
    unfold IsHybridArc
    rw [deleteArc_q15_indegree]
    show ¬ 2 ≤ #(univ.filter fun f : {e : Fin 9 // e ≠ 7} => q15Tgt f.1 = q15Tgt e.1)
    revert e
    decide
  have hθ : (deleteArc (q15 a b c) 7).IsMetric (deleteArcMetric (q15 a b c) 7 (q15Metric len γ)) := by
    convert isMetric_deleteArc hQ.binary.1 hQ.metric.1 hQ.metric.2 (h := 7) (h' := 6) (by decide)
      rfl (by rw [q15_indegree]; show #(univ.filter fun e => q15Tgt e = 6) = 2; decide)
  have hD : ∀ u w, (deleteArc (q15 a b c) 7).graph.Reaches u w ↔ w ∈ q15Desc u :=
    reaches_iff_mem_of_desc q15Desc (by decide)
      (by show ∀ u (e : {e : Fin 9 // e ≠ 7}), q15Src e.1 ∈ q15Desc u → q15Tgt e.1 ∈ q15Desc u
          decide)
      (by show ∀ u, ∀ w ∈ q15Desc u, w ≠ u → ∃ e : {e : Fin 9 // e ≠ 7}, q15Src e.1 = u ∧
            w ∈ q15Desc (q15Tgt e.1) ∧ #(q15Desc (q15Tgt e.1)) < #(q15Desc u)
          decide)
  obtain ⟨e₁, e₂, e₃⟩ := cf_eq_of_desc hN ht hθ hX h q15Desc hD
    (L := {0, 1, 2, 3}) quartetLeaf9_mem (quartetLeaf9_surj h) (leafSet_ab hX h) (leafSet_cd hX h)
    (v := 4) (by decide) q15ArcsSeven (by
      show ∀ e : {e : Fin 9 // e ≠ 7}, e ∈ q15ArcsSeven ↔
        (q15Desc (q15Tgt e.1) ∩ {0, 1, 2, 3} ≠ {0, 1, 2, 3} ∧
          (q15Desc (q15Tgt e.1) ∩ {0, 1, 2, 3} = {0, 1} ∩ {0, 1, 2, 3} ∨
            q15Desc (q15Tgt e.1) ∩ {0, 1, 2, 3} = {2, 3} ∩ {0, 1, 2, 3}))
      decide)
  have hx : Real.exp (-∑ e ∈ q15ArcsSeven,
      (deleteArcMetric (q15 a b c) 7 (q15Metric len γ)).length e) = x := by
    rw [q15ArcsSeven, sum_insert (by decide), sum_pair (by decide), neg_add, neg_add,
      Real.exp_add, Real.exp_add, ← mul_assoc]
    rfl
  rw [hx] at e₁ e₂ e₃
  exact ⟨e₁, e₂, e₃⟩

/-- **`q15` without the hybrid edge `6` is a tree with the split `ab|cd`**, of length `t₁ + t₂ + t₃`
(equation (1)). -/
theorem cf_deleteArc_q15_six (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    let x := Real.exp (-len 4) * Real.exp (-len 5) * Real.exp (-len 7)
    cf (deleteArc (q15 a b c) 6) (deleteArcMetric (q15 a b c) 6 (q15Metric len γ))
        (quartetTree a b c d h) = 1 - 2 / 3 * x ∧
      cf (deleteArc (q15 a b c) 6) (deleteArcMetric (q15 a b c) 6 (q15Metric len γ))
        (quartetTree a c b d (distinct4_acbd h)) = 1 / 3 * x ∧
      cf (deleteArc (q15 a b c) 6) (deleteArcMetric (q15 a b c) 6 (q15Metric len γ))
        (quartetTree a d b c (distinct4_adbc h)) = 1 / 3 * x := by
  intro x
  have hQ := isLSAQuartet_q15 hX h hlen hγ₀ hγ₁
  have hN : (deleteArc (q15 a b c) 6).IsPhylogenetic :=
    isPhylogenetic_deleteArc hQ.binary.1 (h' := 7) (g := 4) (by decide) rfl (by decide) rfl
  have ht : ∀ e, ¬ (deleteArc (q15 a b c) 6).IsHybridArc e := by
    intro e
    unfold IsHybridArc
    rw [deleteArc_q15_indegree]
    show ¬ 2 ≤ #(univ.filter fun f : {e : Fin 9 // e ≠ 6} => q15Tgt f.1 = q15Tgt e.1)
    revert e
    decide
  have hθ : (deleteArc (q15 a b c) 6).IsMetric (deleteArcMetric (q15 a b c) 6 (q15Metric len γ)) := by
    convert isMetric_deleteArc hQ.binary.1 hQ.metric.1 hQ.metric.2 (h := 6) (h' := 7) (by decide)
      rfl (by rw [q15_indegree]; show #(univ.filter fun e => q15Tgt e = 6) = 2; decide)
  have hD : ∀ u w, (deleteArc (q15 a b c) 6).graph.Reaches u w ↔ w ∈ q15DescSix u :=
    reaches_iff_mem_of_desc q15DescSix (by decide)
      (by show ∀ u (e : {e : Fin 9 // e ≠ 6}), q15Src e.1 ∈ q15DescSix u →
            q15Tgt e.1 ∈ q15DescSix u
          decide)
      (by show ∀ u, ∀ w ∈ q15DescSix u, w ≠ u → ∃ e : {e : Fin 9 // e ≠ 6}, q15Src e.1 = u ∧
            w ∈ q15DescSix (q15Tgt e.1) ∧ #(q15DescSix (q15Tgt e.1)) < #(q15DescSix u)
          decide)
  obtain ⟨e₁, e₂, e₃⟩ := cf_eq_of_desc hN ht hθ hX h q15DescSix hD
    (L := {0, 1, 2, 3}) quartetLeaf9_mem (quartetLeaf9_surj h) (leafSet_ab hX h) (leafSet_cd hX h)
    (v := 4) (by decide) q15ArcsSix (by
      show ∀ e : {e : Fin 9 // e ≠ 6}, e ∈ q15ArcsSix ↔
        (q15DescSix (q15Tgt e.1) ∩ {0, 1, 2, 3} ≠ {0, 1, 2, 3} ∧
          (q15DescSix (q15Tgt e.1) ∩ {0, 1, 2, 3} = {0, 1} ∩ {0, 1, 2, 3} ∨
            q15DescSix (q15Tgt e.1) ∩ {0, 1, 2, 3} = {2, 3} ∩ {0, 1, 2, 3}))
      decide)
  have hx : Real.exp (-∑ e ∈ q15ArcsSix,
      (deleteArcMetric (q15 a b c) 6 (q15Metric len γ)).length e) = x := by
    rw [q15ArcsSix, sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    have : (deleteArcMetric (q15 a b c) 6 (q15Metric len γ)).length ⟨4, by decide⟩ +
        ((deleteArcMetric (q15 a b c) 6 (q15Metric len γ)).length ⟨5, by decide⟩ +
          ((deleteArcMetric (q15 a b c) 6 (q15Metric len γ)).length ⟨7, by decide⟩ +
            (deleteArcMetric (q15 a b c) 6 (q15Metric len γ)).length ⟨8, by decide⟩)) =
        len 4 + len 5 + len 7 := by
      show len 4 + (len 5 + (len 7 / 2 + len 7 / 2)) = _
      ring
    rw [this, neg_add, neg_add, Real.exp_add, Real.exp_add]
  rw [hx] at e₁ e₂ e₃
  exact ⟨e₁, e₂, e₃⟩

end Trees

/-! ### The contracted network of Lemma 9 -/

section Contract

open scoped Classical

variable [Fintype X]

/-- The edges `5 → 4` and `6 → 7` of `q15` with its cycle contracted. -/
def q15ContractArcs :
    Finset {e : Fin 9 // ∀ C', IsCycle (q15 a b c).graph C' → C' = ↑q15Cycle → e ∉ C'} :=
  {⟨4, fun _ _ h => h ▸ by decide⟩, ⟨5, fun _ _ h => h ▸ by decide⟩}

/-- **`q15` with its cycle contracted is a tree with the split `ab|cd`**, of length `t₁ + t₂`
(equation (1)). -/
theorem cf_contractRooted_q15 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    let x := Real.exp (-len 4) * Real.exp (-len 5)
    cf (contractRooted (q15 a b c) (· = ↑q15Cycle))
        (contractMetric (q15 a b c) (· = ↑q15Cycle) (q15Metric len γ)) (quartetTree a b c d h) =
        1 - 2 / 3 * x ∧
      cf (contractRooted (q15 a b c) (· = ↑q15Cycle))
        (contractMetric (q15 a b c) (· = ↑q15Cycle) (q15Metric len γ))
        (quartetTree a c b d (distinct4_acbd h)) = 1 / 3 * x ∧
      cf (contractRooted (q15 a b c) (· = ↑q15Cycle))
        (contractMetric (q15 a b c) (· = ↑q15Cycle) (q15Metric len γ))
        (quartetTree a d b c (distinct4_adbc h)) = 1 / 3 * x := by
  intro x
  have hQ := isLSAQuartet_q15 hX h hlen hγ₀ hγ₁
  have hC : IsCycle (q15 a b c).graph ↑q15Cycle := q15_isCycle
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ.binary hQ.levelOne hC (v := 6) ⟨6, by decide, Or.inr rfl⟩
    (by rw [q15_indegree]; decide)
  have hN := hK.isPhylogenetic hQ.binary.1
  have hθ := hK.isMetric hQ.metric.1
  -- the edges left are those off the cycle, which are tree edges of `q15`
  have hoff : ∀ e : {e : Fin 9 // ∀ C', IsCycle (q15 a b c).graph C' → C' = ↑q15Cycle → e ∉ C'},
      e.1 ∉ q15Cycle := fun e he => e.2 _ hC rfl (by simpa using he)
  have ht : ∀ e, ¬ (contractRooted (q15 a b c) (· = ↑q15Cycle)).IsHybridArc e := by
    intro e he
    unfold IsHybridArc at he
    rw [hK.indegree_contract, hK.rep_target] at he
    have h67 := (q15_isHybridArc_iff (a := a) (b := b) (c := c) e.1).1 he
    exact hoff e (by rcases h67 with h' | h' <;> rw [h'] <;> decide)
  -- below the target of an edge off the cycle, the contracted network is `q15`
  have hcl : ∀ e : {e : Fin 9 // ∀ C', IsCycle (q15 a b c).graph C' → C' = ↑q15Cycle → e ∉ C'},
      treeCluster (contractRooted (q15 a b c) (· = ↑q15Cycle))
        ((contractRooted (q15 a b c) (· = ↑q15Cycle)).graph.target e) =
        leafSet (quartetLeaf9 a b c) (q15Desc (q15Tgt e.1)) := by
    intro e
    have hS : ∀ w, (q15 a b c).graph.Reaches (q15Tgt e.1) w →
        w ∉ cycleNodes (q15 a b c).graph ↑q15Cycle := by
      intro w hw
      rw [q15_reaches_iff] at hw
      rw [q15_cycleNodes, mem_coe]
      have key : ∀ j : Fin 9, j ∉ q15Cycle → ∀ w ∈ q15Desc (q15Tgt j),
          w ∉ ({5, 6, 8} : Finset (Fin 9)) := by decide
      exact key _ (hoff e) w hw
    ext y
    rw [mem_treeCluster]
    show (contractRooted (q15 a b c) (· = ↑q15Cycle)).graph.Reaches (Quot.mk _ (q15Tgt e.1))
      (Quot.mk _ ((q15 a b c).leaf y)) ↔ _
    rw [reaches_contract_iff hC hS, q15_reaches_iff]
    simp [leafSet]
    rfl
  obtain ⟨s₁, s₂, s₃⟩ := cf_eq_of_treeCluster_eq_leafSet hN ht hθ hX h (L := {0, 1, 2, 3})
    quartetLeaf9_mem (quartetLeaf9_surj h) (leafSet_ab hX h) (leafSet_cd hX h)
    (fun e => q15Desc (q15Tgt e.1)) hcl (v := Quot.mk _ 4)
    (Or.inl (by
      rw [show (Quot.mk _ 4 : Quot (RootedContractRel (q15 a b c) (· = ↑q15Cycle))) =
        (contractRooted (q15 a b c) (· = ↑q15Cycle)).graph.target ⟨4, fun _ _ h => h ▸ by decide⟩
        from rfl, hcl, ← leafSet_ab hX h]
      exact (leafSet_eq_leafSet_iff quartetLeaf9_mem (quartetLeaf9_surj h) _ _).2
        (show q15Desc 4 ∩ {0, 1, 2, 3} = {0, 1} ∩ {0, 1, 2, 3} by decide)))
    q15ContractArcs (by
      intro e
      have key : ∀ j : Fin 9, j ∉ q15Cycle → ((j = 4 ∨ j = 5) ↔
          (q15Desc (q15Tgt j) ∩ {0, 1, 2, 3} ≠ {0, 1, 2, 3} ∧
            (q15Desc (q15Tgt j) ∩ {0, 1, 2, 3} = {0, 1} ∩ {0, 1, 2, 3} ∨
              q15Desc (q15Tgt j) ∩ {0, 1, 2, 3} = {2, 3} ∩ {0, 1, 2, 3}))) := by decide
      rw [← key _ (hoff e)]
      simp only [q15ContractArcs, mem_insert, mem_singleton, Subtype.ext_iff])
  have hx : Real.exp (-∑ e ∈ q15ContractArcs (a := a) (b := b) (c := c),
      (contractMetric (q15 a b c) (· = ↑q15Cycle) (q15Metric len γ)).length e) = x := by
    rw [q15ContractArcs, sum_pair (by simp [Subtype.ext_iff]), neg_add, Real.exp_add]
    rfl
  rw [hx] at s₁ s₂ s₃
  exact ⟨s₁, s₂, s₃⟩

end Contract

end Banos2019
