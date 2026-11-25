module

public import Banos2019.Quartet.Concrete

/-!
# Figure 17 as an LSA quartet network (Example 4)

The 4-cycle of Figure 17 is the unrooted network of the LSA quartet network `q17 a b c`: the nodes
`0, 1, 2, 3` are the leaves `a, b, c, d`; `4, 5, 6, 7` the nodes of the cycle with `a, b, c, d`, `6`
the hybrid node; the root `8` has the hybrid edge `8 → 6` and the tree edge `8 → 7`, which the
unrooted network merges into the hybrid edge `7 → 6` of Figure 17. `inducesNetwork_q17`, with the
figures in `Banos2019.Quartet.Examples`, shows that the unrooted network of `q17 a b c` is Figure
17.

* `isLSAQuartet_q17`, `inducesCycleType_q17`: `q17 a b c` with the parameters `q17Metric len γ` is
  an LSA quartet network with a 4-cycle, whose hybrid edges are `6` (inheritance `γ`) and `7`.
* `cf_deleteArc_q17_seven`, `cf_deleteArc_q17_six`: the networks `Q₁⊕`, `Q₂⊕` of Lemma 10 are trees,
  with the internal edges `bc|ad` of length `t₂` and `ab|cd` of length `t₁` (equation (1)).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace Banos2019

/-- The tails of the edges of `q17`. -/
def q17Src : Fin 9 → Fin 9 := ![4, 5, 6, 7, 7, 4, 5, 8, 8]

/-- The heads of the edges of `q17`. -/
def q17Tgt : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 6, 7]

variable {X : Type*} [DecidableEq X]

/-- **Figure 17 as a rooted network**, with the root on the hybrid edge from the node of `d`. -/
def q17 (a b c : X) : RootedNetwork (Fin 9) (Fin 9) X :=
  ⟨⟨q17Src, q17Tgt⟩, 8, quartetLeaf9 a b c⟩

/-- The parameters of `q17`: those of Figure 17, the length `len 7` of the merged hybrid edge shared
by the two edges at the root. -/
def q17Metric (len : Fin 8 → ℝ) (γ : ℝ) : MetricData (Fin 9) :=
  ⟨![len 0, len 1, len 2, len 3, len 4, len 5, len 6, len 7 / 2, len 7 / 2],
    ![1, 1, 1, 1, 1, 1, γ, 1 - γ, 1]⟩

variable {a b c d : X}

section Network

theorem q17_indegree (v : Fin 9) :
    (q17 a b c).graph.indegree v = (univ.filter fun e => q17Tgt e = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [q17]

theorem q17_outdegree (v : Fin 9) :
    (q17 a b c).graph.outdegree v = (univ.filter fun e => q17Src e = v).card := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [q17]

/-- The indegrees of `q17` without the edge `h`. -/
theorem deleteArc_q17_indegree (h v : Fin 9) :
    (deleteArc (q17 a b c) h).graph.indegree v =
      (univ.filter fun e : {e : Fin 9 // e ≠ h} => q17Tgt e.1 = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [deleteArc, q17]

variable [Fintype X]

theorem q17_isPhylogenetic (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    (q17 a b c).IsPhylogenetic where
  finite_vertices := inferInstance
  finite_arcs := inferInstance
  finite_taxa := inferInstance
  acyclic := DirectedMultigraph.isAcyclic_of_rank _
    (fun v : Fin 9 => ![5, 5, 5, 5, 2, 3, 4, 1, 0] v)
    (by show ∀ e, ![5, 5, 5, 5, 2, 3, 4, 1, 0] (q17Src e) < ![5, 5, 5, 5, 2, 3, 4, 1, 0] (q17Tgt e)
        decide)
  root_reaches v := by
    have h86 : (q17 a b c).graph.Adj 8 6 := ⟨7, rfl, rfl⟩
    have h87 : (q17 a b c).graph.Adj 8 7 := ⟨8, rfl, rfl⟩
    have h74 : (q17 a b c).graph.Adj 7 4 := ⟨4, rfl, rfl⟩
    have h45 : (q17 a b c).graph.Adj 4 5 := ⟨5, rfl, rfl⟩
    have h40 : (q17 a b c).graph.Adj 4 0 := ⟨0, rfl, rfl⟩
    have h51 : (q17 a b c).graph.Adj 5 1 := ⟨1, rfl, rfl⟩
    have h62 : (q17 a b c).graph.Adj 6 2 := ⟨2, rfl, rfl⟩
    have h73 : (q17 a b c).graph.Adj 7 3 := ⟨3, rfl, rfl⟩
    show Relation.ReflTransGen _ 8 v
    fin_cases v
    · exact ((Relation.ReflTransGen.single h87).tail h74).tail h40
    · exact (((Relation.ReflTransGen.single h87).tail h74).tail h45).tail h51
    · exact (Relation.ReflTransGen.single h86).tail h62
    · exact (Relation.ReflTransGen.single h87).tail h73
    · exact (Relation.ReflTransGen.single h87).tail h74
    · exact ((Relation.ReflTransGen.single h87).tail h74).tail h45
    · exact Relation.ReflTransGen.single h86
    · exact Relation.ReflTransGen.single h87
    · exact .refl
  root_indegree := by
    rw [q17_indegree]
    show #(univ.filter fun e => q17Tgt e = 8) = 0
    decide
  nonroot_indegree v hv := by
    rw [q17_indegree]
    fin_cases v <;> first | decide | exact absurd rfl hv
  leaf_injective := quartetLeaf9_injective hX h
  leaf_indegree x := by
    rw [q17_indegree]
    have := quartetLeaf9_mem (a := a) (b := b) (c := c) x
    simp only [mem_insert, mem_singleton] at this
    show #(univ.filter fun e => q17Tgt e = quartetLeaf9 a b c x) = 1
    rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide
  leaves v := by
    rw [q17_outdegree]
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
      show #(univ.filter fun e => q17Src e = quartetLeaf9 a b c x) = 0
      rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide

omit [Fintype X] in
theorem q17_isBinary (a b c : X) : (q17 a b c).IsBinary := by
  refine ⟨by rw [q17_outdegree]; show #(univ.filter fun e => q17Src e = 8) = 2; decide,
    fun v hv h0 => ?_⟩
  rw [q17_indegree, q17_outdegree]
  rw [q17_outdegree] at h0
  fin_cases v <;> first | decide | exact absurd rfl hv | exact absurd (by decide) h0

theorem q17_isBinaryRootedNetwork (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    IsBinaryRootedNetwork (q17 a b c) :=
  ⟨q17_isPhylogenetic hX h, q17_isBinary a b c⟩

end Network

/-! ### The cycle -/

/-- The edges `8 → 7`, `7 → 4`, `4 → 5`, `5 → 6`, `8 → 6` of the cycle of `q17`. -/
def q17Cycle : Finset (Fin 9) := {4, 5, 6, 7, 8}

/-- The cycle `8, 7, 4, 5, 6` of `q17`. -/
theorem q17_isCycle : IsCycle (q17 a b c).graph ↑q17Cycle := by
  refine ⟨5, ![8, 7, 4, 5, 6], ![8, 4, 5, 6, 7], ⟨by decide, ?_, by decide, by decide⟩, ?_⟩
  · show ∀ i : Fin 5, (q17Src (![8, 4, 5, 6, 7] i) = ![8, 7, 4, 5, 6] i ∧
        q17Tgt (![8, 4, 5, 6, 7] i) = ![8, 7, 4, 5, 6] (finRotate 5 i)) ∨
      (q17Src (![8, 4, 5, 6, 7] i) = ![8, 7, 4, 5, 6] (finRotate 5 i) ∧
        q17Tgt (![8, 4, 5, 6, 7] i) = ![8, 7, 4, 5, 6] i)
    decide
  · ext f
    simp only [Set.mem_range, q17Cycle, coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨0, rfl⟩]

/-- **The only cycle of `q17`**: the edges to the leaves are on no cycle, and the five edges left,
with at most two at each node, form one. -/
theorem q17_cycle_eq {C : Set (Fin 9)} (hC : IsCycle (q17 a b c).graph C) : C = ↑q17Cycle := by
  have hloop : ∀ f, (q17 a b c).graph.source f ≠ (q17 a b c).graph.target f := by
    show ∀ f, q17Src f ≠ q17Tgt f
    decide
  have hpend : ∀ f : Fin 9, f ∉ q17Cycle → ∃ p : Fin 9, (q17Src f = p ∨ q17Tgt f = p) ∧
      ∀ g, (q17Src g = p ∨ q17Tgt g = p) → g = f := by decide
  have hsub : C ⊆ ↑q17Cycle := hC.subset_of_pendant hloop (Set.subset_univ _)
    fun f _ hf => (hpend f (by simpa using hf)).imp fun _ h => ⟨h.1, fun g _ => h.2 g⟩
  obtain ⟨f₀, hf₀⟩ : C.Nonempty := by
    obtain ⟨k, v, e, hcyc, rfl⟩ := hC
    exact ⟨e ⟨0, hcyc.pos⟩, ⟨_, rfl⟩⟩
  have hdeg : ∀ x, {f | f ∈ (↑q17Cycle : Set (Fin 9)) ∧ ((q17 a b c).graph.source f = x ∨
      (q17 a b c).graph.target f = x)}.ncard ≤ 2 := by
    intro x
    have e : {f | f ∈ (↑q17Cycle : Set (Fin 9)) ∧ ((q17 a b c).graph.source f = x ∨
        (q17 a b c).graph.target f = x)} =
        ↑(q17Cycle.filter fun f => q17Src f = x ∨ q17Tgt f = x) := by
      ext f
      simp only [Set.mem_ofPred_eq, coe_filter, mem_coe]
      rfl
    have key : ∀ x : Fin 9, #(q17Cycle.filter fun f => q17Src f = x ∨ q17Tgt f = x) ≤ 2 := by
      decide
    rw [e, Set.ncard_coe_finset]
    exact key x
  -- the nodes of the cycle are joined to `8` along its edges
  have h87 : (q17 a b c).graph.AdjOn ↑q17Cycle 8 7 := ⟨8, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have h74 : (q17 a b c).graph.AdjOn ↑q17Cycle 7 4 := ⟨4, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have h45 : (q17 a b c).graph.AdjOn ↑q17Cycle 4 5 := ⟨5, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have hw : ∀ y : Fin 9, y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 →
      (q17 a b c).graph.Walks ↑q17Cycle 8 y := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact (Relation.ReflTransGen.single h87).tail h74
    · exact ((Relation.ReflTransGen.single h87).tail h74).tail h45
    · exact Relation.ReflTransGen.single h87
    · exact .refl
  have hsrc : ∀ f ∈ q17Cycle, q17Src f = 4 ∨ q17Src f = 5 ∨ q17Src f = 7 ∨ q17Src f = 8 := by
    decide
  have hconn : ∀ f ∈ (↑q17Cycle : Set (Fin 9)),
      (q17 a b c).graph.Walks ↑q17Cycle ((q17 a b c).graph.source f₀)
      ((q17 a b c).graph.source f) :=
    fun f hf => ((q17 a b c).graph.walks_symm (hw _ (hsrc f₀ (hsub hf₀)))).trans
      (hw _ (hsrc f (by simpa using hf)))
  exact hsub.antisymm (hC.superset_of_ncard_incident_le hloop hsub hdeg (source_mem_cycleNodes hf₀)
    hconn)

theorem q17_isLevelOne : IsLevelOne (q17 a b c).graph := fun _ _ hC hC' _ =>
  (q17_cycle_eq hC).trans (q17_cycle_eq hC').symm

/-! ### The root is the LSA -/

theorem q17_isLSANetwork (h : Distinct4 a b c d) : (q17 a b c).IsLSANetwork := by
  refine ⟨root_isStableAncestor _ _, fun w hw => ?_⟩
  suffices hw8 : w = 8 by rw [hw8]; exact .refl
  by_contra hne
  have hlc : (q17 a b c).leaf c = 2 := quartetLeaf9_c h
  have hld : (q17 a b c).leaf d = 3 := quartetLeaf9_d h
  by_cases h62 : w = 6 ∨ w = 2
  · -- the path `8 → 7 → 3` to `d` avoids `w`
    have hw7 : w ≠ 7 := by rcases h62 with rfl | rfl <;> decide
    have hw3 : w ≠ 3 := by rcases h62 with rfl | rfl <;> decide
    refine hw d (Set.mem_univ _) ?_
    rw [hld]
    exact ⟨Ne.symm hne, Ne.symm hw3, (Relation.ReflTransGen.single
      ⟨⟨8, rfl, rfl⟩, Ne.symm hne, Ne.symm hw7⟩).tail ⟨⟨3, rfl, rfl⟩, Ne.symm hw7, Ne.symm hw3⟩⟩
  · -- the path `8 → 6 → 2` to `c` avoids `w`
    have hw6 : w ≠ 6 := fun e => h62 (Or.inl e)
    have hw2 : w ≠ 2 := fun e => h62 (Or.inr e)
    refine hw c (Set.mem_univ _) ?_
    rw [hlc]
    exact ⟨Ne.symm hne, Ne.symm hw2, (Relation.ReflTransGen.single
      ⟨⟨7, rfl, rfl⟩, Ne.symm hne, Ne.symm hw6⟩).tail ⟨⟨2, rfl, rfl⟩, Ne.symm hw6, Ne.symm hw2⟩⟩

/-! ### The parameters -/

theorem q17_isHybridArc_iff (e : Fin 9) : (q17 a b c).IsHybridArc e ↔ e = 6 ∨ e = 7 := by
  unfold IsHybridArc
  rw [q17_indegree]
  show 2 ≤ #(univ.filter fun f => q17Tgt f = q17Tgt e) ↔ e = 6 ∨ e = 7
  revert e
  decide

theorem q17_isTreeArc_iff (e : Fin 9) : (q17 a b c).IsTreeArc e ↔ ¬ (e = 6 ∨ e = 7) := by
  unfold IsTreeArc
  rw [q17_indegree]
  show #(univ.filter fun f => q17Tgt f = q17Tgt e) = 1 ↔ ¬ (e = 6 ∨ e = 7)
  revert e
  decide

theorem q17Metric_isMetricNetwork {len : Fin 8 → ℝ} (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ)
    (hγ₁ : γ < 1) : IsMetricNetwork (q17 a b c) (q17Metric len γ) := by
  have hpos : ∀ e, 0 < (q17Metric len γ).length e := by
    intro e
    fin_cases e <;> simp [q17Metric, hlen]
  refine ⟨⟨fun e _ => hpos e, fun e _ => (hpos e).le, fun e he => ?_, fun e he => ?_,
    fun v hv => ?_⟩,
    hpos⟩
  · rw [q17_isTreeArc_iff] at he
    fin_cases e <;> simp_all [q17Metric]
  · rw [q17_isHybridArc_iff] at he
    rcases he with rfl | rfl
    · simpa [q17Metric] using hγ₀
    · simpa [q17Metric] using hγ₁
  · rw [q17_indegree] at hv
    have hv6 : v = 6 := by revert v; decide
    subst hv6
    simp [Fin.sum_univ_succ, q17Metric, q17, q17Tgt]

theorem isLSAQuartet_q17 [Fintype X] (hX : Fintype.card X = 4) (h : Distinct4 a b c d)
    {len : Fin 8 → ℝ} (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    IsLSAQuartet (q17 a b c) (q17Metric len γ) :=
  ⟨q17_isBinaryRootedNetwork hX h, q17_isLevelOne, q17_isLSANetwork h, hX,
    q17Metric_isMetricNetwork hlen hγ₀ hγ₁⟩

/-- **The cycle of `q17` induces a 4-cycle**, with hybrid node `6`. -/
theorem inducesCycleType_q17 : ∃ k, InducesCycleType (q17 a b c) ↑q17Cycle 6 4 k := by
  refine ⟨_, q17_isCycle, ⟨6, by decide, Or.inr rfl⟩, by rw [q17_indegree]; decide, ?_, rfl⟩
  have h8 : (q17 a b c).root ∈ cycleNodes (q17 a b c).graph ↑q17Cycle := ⟨8, by decide, Or.inl rfl⟩
  rw [ite_eq_left h8, Set.ncard_coe_finset]
  decide

/-! ### The trees of Lemma 10 -/

section Trees

variable [Fintype X]

/-- The descendants of the nodes of `q17` without the hybrid edge `7`. -/
def q17DescSeven : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {4, 0, 5, 1, 6, 2}, {5, 1, 6, 2}, {6, 2}, {7, 3, 4, 0, 5, 1, 6, 2}, univ]

/-- The descendants of the nodes of `q17` without the hybrid edge `6`. -/
def q17DescSix : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {4, 0, 5, 1}, {5, 1}, {6, 2}, {7, 3, 4, 0, 5, 1}, univ]

/-- The edge `4 → 5` of `q17` without the hybrid edge `7`. -/
def q17ArcFive : {e : Fin 9 // e ≠ 7} := ⟨5, by decide⟩

/-- The edge `7 → 4` of `q17` without the hybrid edge `6`. -/
def q17ArcFour : {e : Fin 9 // e ≠ 6} := ⟨4, by decide⟩

/-- **`q17` without the hybrid edge `7` is a tree with the split `bc|ad`**, of length `t₂`: the
concordance factor of `ad|bc` is `1 - ⅔x₂`, those of `ab|cd` and `ac|bd` are `⅓x₂` (equation (1)).
-/
theorem cf_deleteArc_q17_seven (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    cf (deleteArc (q17 a b c) 7) (deleteArcMetric (q17 a b c) 7 (q17Metric len γ))
        (quartetTree a d b c (distinct4_adbc h)) = 1 - 2 / 3 * Real.exp (-len 5) ∧
      cf (deleteArc (q17 a b c) 7) (deleteArcMetric (q17 a b c) 7 (q17Metric len γ))
        (quartetTree a b c d h) = 1 / 3 * Real.exp (-len 5) ∧
      cf (deleteArc (q17 a b c) 7) (deleteArcMetric (q17 a b c) 7 (q17Metric len γ))
        (quartetTree a c b d (distinct4_acbd h)) = 1 / 3 * Real.exp (-len 5) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  have h' : Distinct4 b c a d := ⟨hbc, Ne.symm hab, hbd, Ne.symm hac, hcd, had⟩
  have hQ := isLSAQuartet_q17 hX h hlen hγ₀ hγ₁
  have hN : (deleteArc (q17 a b c) 7).IsPhylogenetic :=
    isPhylogenetic_deleteArc hQ.binary.1 (h' := 6) (g := 8) (by decide) rfl (by decide) rfl
  have ht : ∀ e, ¬ (deleteArc (q17 a b c) 7).IsHybridArc e := by
    intro e
    unfold IsHybridArc
    rw [deleteArc_q17_indegree]
    show ¬ 2 ≤ #(univ.filter fun f : {e : Fin 9 // e ≠ 7} => q17Tgt f.1 = q17Tgt e.1)
    revert e
    decide
  have hθ : (deleteArc (q17 a b c) 7).IsMetric
    (deleteArcMetric (q17 a b c) 7 (q17Metric len γ)) := by
    convert isMetric_deleteArc hQ.binary.1 hQ.metric.1 hQ.metric.2 (h := 7) (h' := 6) (by decide)
      rfl (by rw [q17_indegree]; show #(univ.filter fun e => q17Tgt e = 6) = 2; decide)
  have hD : ∀ u w, (deleteArc (q17 a b c) 7).graph.Reaches u w ↔ w ∈ q17DescSeven u :=
    reaches_iff_mem_of_desc q17DescSeven (by decide)
      (by show ∀ u (e : {e : Fin 9 // e ≠ 7}), q17Src e.1 ∈ q17DescSeven u →
            q17Tgt e.1 ∈ q17DescSeven u
          decide)
      (by show ∀ u, ∀ w ∈ q17DescSeven u, w ≠ u → ∃ e : {e : Fin 9 // e ≠ 7}, q17Src e.1 = u ∧
            w ∈ q17DescSeven (q17Tgt e.1) ∧ #(q17DescSeven (q17Tgt e.1)) < #(q17DescSeven u)
          decide)
  have hS : leafSet (deleteArc (q17 a b c) 7).leaf {1, 2} = {b, c} := by
    ext x
    rw [show (deleteArc (q17 a b c) 7).leaf = quartetLeaf9 a b c from rfl,
      leafSet_quartetLeaf9 hX h]
    simp only [mem_insert, mem_singleton]
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]
  have hSc : leafSet (deleteArc (q17 a b c) 7).leaf {0, 3} = {b, c}ᶜ := by
    ext x
    rw [show (deleteArc (q17 a b c) 7).leaf = quartetLeaf9 a b c from rfl,
      leafSet_quartetLeaf9 hX h]
    simp only [mem_compl, mem_insert, mem_singleton]
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]
  obtain ⟨e₁, e₂, e₃⟩ := cf_eq_of_desc hN ht hθ hX h' q17DescSeven hD
    (L := {0, 1, 2, 3}) quartetLeaf9_mem (quartetLeaf9_surj h) hS hSc (v := 5) (by decide)
    {q17ArcFive} (by
      show ∀ e : {e : Fin 9 // e ≠ 7}, e ∈ ({q17ArcFive} : Finset _) ↔
        (q17DescSeven (q17Tgt e.1) ∩ {0, 1, 2, 3} ≠ {0, 1, 2, 3} ∧
          (q17DescSeven (q17Tgt e.1) ∩ {0, 1, 2, 3} = {1, 2} ∩ {0, 1, 2, 3} ∨
            q17DescSeven (q17Tgt e.1) ∩ {0, 1, 2, 3} = {0, 3} ∩ {0, 1, 2, 3}))
      decide)
  have hlen5 : ∑ e ∈ ({q17ArcFive} : Finset {e : Fin 9 // e ≠ 7}),
      (deleteArcMetric (q17 a b c) 7 (q17Metric len γ)).length e = len 5 := by
    rw [sum_singleton]
    rfl
  rw [hlen5] at e₁ e₂ e₃
  have q₁ : quartetTree b c a d h' = quartetTree a d b c (distinct4_adbc h) :=
    Subtype.ext (by simp only [quartetTree]; rw [Finset.pair_comm])
  have q₂ : quartetTree b a c d (distinct4_acbd h') = quartetTree a b c d h :=
    Subtype.ext (by simp only [quartetTree]; rw [Finset.pair_comm b a])
  have q₃ : quartetTree b d c a (distinct4_adbc h') = quartetTree a c b d (distinct4_acbd h) :=
    Subtype.ext (by simp only [quartetTree]; rw [Finset.pair_comm b d, Finset.pair_comm c a,
      Finset.pair_comm])
  rw [q₁] at e₁
  rw [q₂] at e₂
  rw [q₃] at e₃
  exact ⟨e₁, e₂, e₃⟩

/-- **`q17` without the hybrid edge `6` is a tree with the split `ab|cd`**, of length `t₁`: the
concordance factor of `ab|cd` is `1 - ⅔x₁`, those of `ac|bd` and `ad|bc` are `⅓x₁` (equation (1)).
-/
theorem cf_deleteArc_q17_six (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    cf (deleteArc (q17 a b c) 6) (deleteArcMetric (q17 a b c) 6 (q17Metric len γ))
        (quartetTree a b c d h) = 1 - 2 / 3 * Real.exp (-len 4) ∧
      cf (deleteArc (q17 a b c) 6) (deleteArcMetric (q17 a b c) 6 (q17Metric len γ))
        (quartetTree a c b d (distinct4_acbd h)) = 1 / 3 * Real.exp (-len 4) ∧
      cf (deleteArc (q17 a b c) 6) (deleteArcMetric (q17 a b c) 6 (q17Metric len γ))
        (quartetTree a d b c (distinct4_adbc h)) = 1 / 3 * Real.exp (-len 4) := by
  have hQ := isLSAQuartet_q17 hX h hlen hγ₀ hγ₁
  have hN : (deleteArc (q17 a b c) 6).IsPhylogenetic :=
    isPhylogenetic_deleteArc hQ.binary.1 (h' := 7) (g := 1) (by decide) rfl (by decide) rfl
  have ht : ∀ e, ¬ (deleteArc (q17 a b c) 6).IsHybridArc e := by
    intro e
    unfold IsHybridArc
    rw [deleteArc_q17_indegree]
    show ¬ 2 ≤ #(univ.filter fun f : {e : Fin 9 // e ≠ 6} => q17Tgt f.1 = q17Tgt e.1)
    revert e
    decide
  have hθ : (deleteArc (q17 a b c) 6).IsMetric
    (deleteArcMetric (q17 a b c) 6 (q17Metric len γ)) := by
    convert isMetric_deleteArc hQ.binary.1 hQ.metric.1 hQ.metric.2 (h := 6) (h' := 7) (by decide)
      rfl (by rw [q17_indegree]; show #(univ.filter fun e => q17Tgt e = 6) = 2; decide)
  have hD : ∀ u w, (deleteArc (q17 a b c) 6).graph.Reaches u w ↔ w ∈ q17DescSix u :=
    reaches_iff_mem_of_desc q17DescSix (by decide)
      (by show ∀ u (e : {e : Fin 9 // e ≠ 6}), q17Src e.1 ∈ q17DescSix u →
            q17Tgt e.1 ∈ q17DescSix u
          decide)
      (by show ∀ u, ∀ w ∈ q17DescSix u, w ≠ u → ∃ e : {e : Fin 9 // e ≠ 6}, q17Src e.1 = u ∧
            w ∈ q17DescSix (q17Tgt e.1) ∧ #(q17DescSix (q17Tgt e.1)) < #(q17DescSix u)
          decide)
  have hS : leafSet (deleteArc (q17 a b c) 6).leaf {0, 1} = {a, b} := by
    ext x
    rw [show (deleteArc (q17 a b c) 6).leaf = quartetLeaf9 a b c from rfl,
      leafSet_quartetLeaf9 hX h]
    simp only [mem_insert, mem_singleton]
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]
  have hSc : leafSet (deleteArc (q17 a b c) 6).leaf {2, 3} = {a, b}ᶜ := by
    ext x
    rw [show (deleteArc (q17 a b c) 6).leaf = quartetLeaf9 a b c from rfl,
      leafSet_quartetLeaf9 hX h]
    simp only [mem_compl, mem_insert, mem_singleton]
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]
  obtain ⟨e₁, e₂, e₃⟩ := cf_eq_of_desc hN ht hθ hX h q17DescSix hD
    (L := {0, 1, 2, 3}) quartetLeaf9_mem (quartetLeaf9_surj h) hS hSc (v := 4) (by decide)
    {q17ArcFour} (by
      show ∀ e : {e : Fin 9 // e ≠ 6}, e ∈ ({q17ArcFour} : Finset _) ↔
        (q17DescSix (q17Tgt e.1) ∩ {0, 1, 2, 3} ≠ {0, 1, 2, 3} ∧
          (q17DescSix (q17Tgt e.1) ∩ {0, 1, 2, 3} = {0, 1} ∩ {0, 1, 2, 3} ∨
            q17DescSix (q17Tgt e.1) ∩ {0, 1, 2, 3} = {2, 3} ∩ {0, 1, 2, 3}))
      decide)
  have hlen4 : ∑ e ∈ ({q17ArcFour} : Finset {e : Fin 9 // e ≠ 6}),
      (deleteArcMetric (q17 a b c) 6 (q17Metric len γ)).length e = len 4 := by
    rw [sum_singleton]
    rfl
  rw [hlen4] at e₁ e₂ e₃
  exact ⟨e₁, e₂, e₃⟩

end Trees

end Banos2019
