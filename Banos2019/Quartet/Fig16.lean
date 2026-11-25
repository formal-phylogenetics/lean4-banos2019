module

public import Banos2019.Quartet.Concrete

/-!
# Figure 16 as an LSA quartet network (Example 3)

The `3₁`-cycle of Figure 16 is the unrooted network of the LSA quartet network `q16 a b c`: the nodes
`0, 1, 2, 3` are the leaves `a, b, c, d`; `4` is the parent of `a` and `b`; `5`, `6` and the hybrid node
`7` above `d` are the nodes of the cycle, `c` at `6`; the root `8` has the hybrid edge `8 → 7` and the
tree edge `8 → 5`, which the unrooted network merges into the hybrid edge `5 → 7` of Figure 16.
`inducesNetwork_q16`, with the figures in `Banos2019.Quartet.Examples`, shows that the unrooted network
of `q16 a b c` is Figure 16.

* `isLSAQuartet_q16`, `inducesCycleType_q16`: `q16 a b c` with the parameters `q16Metric len γ` is an
  LSA quartet network with a `3₁`-cycle, whose hybrid edges are `6` (inheritance `γ`) and `7`.
* `cf_deleteArc_q16_seven`, `cf_deleteArc_q16_six`: the networks `Q₁⊕`, `Q₂⊕` of Lemma 10 are trees,
  with the internal edges `ab|cd` of lengths `t₁ + t₂` and `t₁` (equation (1)).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace Banos2019

/-- The tails of the edges of `q16`. -/
def q16Src : Fin 9 → Fin 9 := ![4, 4, 6, 7, 5, 5, 6, 8, 8]

/-- The heads of the edges of `q16`. -/
def q16Tgt : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 6, 7, 7, 5]

variable {X : Type*} [DecidableEq X]

/-- **Figure 16 as a rooted network**, with the root on the hybrid edge from the node `5`. -/
def q16 (a b c : X) : RootedNetwork (Fin 9) (Fin 9) X :=
  ⟨⟨q16Src, q16Tgt⟩, 8, quartetLeaf9 a b c⟩

/-- The parameters of `q16`: those of Figure 16, the length `len 7` of the merged hybrid edge shared by
the two edges at the root. -/
def q16Metric (len : Fin 8 → ℝ) (γ : ℝ) : MetricData (Fin 9) :=
  ⟨![len 0, len 1, len 2, len 3, len 4, len 5, len 6, len 7 / 2, len 7 / 2],
    ![1, 1, 1, 1, 1, 1, γ, 1 - γ, 1]⟩

variable {a b c d : X}

section Network

theorem q16_indegree (v : Fin 9) :
    (q16 a b c).graph.indegree v = (univ.filter fun e => q16Tgt e = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [q16]

theorem q16_outdegree (v : Fin 9) :
    (q16 a b c).graph.outdegree v = (univ.filter fun e => q16Src e = v).card := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [q16]

/-- The indegrees of `q16` without the edge `h`. -/
theorem deleteArc_q16_indegree (h v : Fin 9) :
    (deleteArc (q16 a b c) h).graph.indegree v =
      (univ.filter fun e : {e : Fin 9 // e ≠ h} => q16Tgt e.1 = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [deleteArc, q16]

variable [Fintype X]

theorem q16_leaf_injective (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    Function.Injective (quartetLeaf9 a b c) := by
  intro x y hxy
  rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;>
    rcases eq_or_of_distinct4_of_card_eq hX h y with rfl | rfl | rfl | rfl <;>
    simp only [quartetLeaf9_a, quartetLeaf9_b h, quartetLeaf9_c h, quartetLeaf9_d h] at hxy <;>
    first | rfl | exact absurd hxy (by decide)

theorem q16_isPhylogenetic (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    (q16 a b c).IsPhylogenetic where
  finite_vertices := inferInstance
  finite_arcs := inferInstance
  finite_taxa := inferInstance
  acyclic := DirectedMultigraph.isAcyclic_of_rank _ (fun v : Fin 9 => ![4, 4, 4, 4, 2, 1, 2, 3, 0] v)
    (by show ∀ e, ![4, 4, 4, 4, 2, 1, 2, 3, 0] (q16Src e) < ![4, 4, 4, 4, 2, 1, 2, 3, 0] (q16Tgt e)
        decide)
  root_reaches v := by
    have h85 : (q16 a b c).graph.Adj 8 5 := ⟨8, rfl, rfl⟩
    have h87 : (q16 a b c).graph.Adj 8 7 := ⟨7, rfl, rfl⟩
    have h54 : (q16 a b c).graph.Adj 5 4 := ⟨4, rfl, rfl⟩
    have h56 : (q16 a b c).graph.Adj 5 6 := ⟨5, rfl, rfl⟩
    have h40 : (q16 a b c).graph.Adj 4 0 := ⟨0, rfl, rfl⟩
    have h41 : (q16 a b c).graph.Adj 4 1 := ⟨1, rfl, rfl⟩
    have h62 : (q16 a b c).graph.Adj 6 2 := ⟨2, rfl, rfl⟩
    have h73 : (q16 a b c).graph.Adj 7 3 := ⟨3, rfl, rfl⟩
    show Relation.ReflTransGen _ 8 v
    fin_cases v
    · exact ((Relation.ReflTransGen.single h85).tail h54).tail h40
    · exact ((Relation.ReflTransGen.single h85).tail h54).tail h41
    · exact ((Relation.ReflTransGen.single h85).tail h56).tail h62
    · exact (Relation.ReflTransGen.single h87).tail h73
    · exact (Relation.ReflTransGen.single h85).tail h54
    · exact Relation.ReflTransGen.single h85
    · exact (Relation.ReflTransGen.single h85).tail h56
    · exact Relation.ReflTransGen.single h87
    · exact .refl
  root_indegree := by
    rw [q16_indegree]
    show #(univ.filter fun e => q16Tgt e = 8) = 0
    decide
  nonroot_indegree v hv := by
    rw [q16_indegree]
    fin_cases v <;> first | decide | exact absurd rfl hv
  leaf_injective := q16_leaf_injective hX h
  leaf_indegree x := by
    rw [q16_indegree]
    have := quartetLeaf9_mem (a := a) (b := b) (c := c) x
    simp only [mem_insert, mem_singleton] at this
    show #(univ.filter fun e => q16Tgt e = quartetLeaf9 a b c x) = 1
    rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide
  leaves v := by
    rw [q16_outdegree]
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
      show #(univ.filter fun e => q16Src e = quartetLeaf9 a b c x) = 0
      rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide

omit [Fintype X] in
theorem q16_isBinary (a b c : X) : (q16 a b c).IsBinary := by
  refine ⟨by rw [q16_outdegree]; show #(univ.filter fun e => q16Src e = 8) = 2; decide,
    fun v hv h0 => ?_⟩
  rw [q16_indegree, q16_outdegree]
  rw [q16_outdegree] at h0
  fin_cases v <;> first | decide | exact absurd rfl hv | exact absurd (by decide) h0

theorem q16_isBinaryRootedNetwork (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    IsBinaryRootedNetwork (q16 a b c) :=
  ⟨q16_isPhylogenetic hX h, q16_isBinary a b c⟩

end Network

/-! ### The cycle -/

/-- The edges `8 → 5`, `5 → 6`, `6 → 7`, `8 → 7` of the cycle of `q16`. -/
def q16Cycle : Finset (Fin 9) := {5, 6, 7, 8}

/-- The cycle `8, 5, 6, 7` of `q16`. -/
theorem q16_isCycle : IsCycle (q16 a b c).graph ↑q16Cycle := by
  refine ⟨4, ![8, 5, 6, 7], ![8, 5, 6, 7], ⟨by decide, ?_, by decide, by decide⟩, ?_⟩
  · show ∀ i : Fin 4, (q16Src (![8, 5, 6, 7] i) = ![8, 5, 6, 7] i ∧
        q16Tgt (![8, 5, 6, 7] i) = ![8, 5, 6, 7] (finRotate 4 i)) ∨
      (q16Src (![8, 5, 6, 7] i) = ![8, 5, 6, 7] (finRotate 4 i) ∧
        q16Tgt (![8, 5, 6, 7] i) = ![8, 5, 6, 7] i)
    decide
  · ext f
    simp only [Set.mem_range, q16Cycle, coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨0, rfl⟩]

/-- **The only cycle of `q16`**: the edges to the leaves are on no cycle, then neither is the edge to
the node `4` above `a` and `b`, and the four edges left, with at most two at each node, form one. -/
theorem q16_cycle_eq {C : Set (Fin 9)} (hC : IsCycle (q16 a b c).graph C) : C = ↑q16Cycle := by
  have hloop : ∀ f, (q16 a b c).graph.source f ≠ (q16 a b c).graph.target f := by
    show ∀ f, q16Src f ≠ q16Tgt f
    decide
  -- the edges to the leaves, then the edge `5 → 4`
  have hpend₁ : ∀ f : Fin 9, f ∉ ({4, 5, 6, 7, 8} : Finset (Fin 9)) → ∃ p : Fin 9,
      (q16Src f = p ∨ q16Tgt f = p) ∧ ∀ g, (q16Src g = p ∨ q16Tgt g = p) → g = f := by decide
  have hsub₁ : C ⊆ ↑({4, 5, 6, 7, 8} : Finset (Fin 9)) := hC.subset_of_pendant hloop
    (Set.subset_univ _) fun f _ hf =>
      (hpend₁ f (by simpa using hf)).imp fun _ h => ⟨h.1, fun g _ => h.2 g⟩
  have hpend₂ : ∀ f ∈ ({4, 5, 6, 7, 8} : Finset (Fin 9)), f ∉ q16Cycle → ∃ p : Fin 9,
      (q16Src f = p ∨ q16Tgt f = p) ∧ ∀ g ∈ ({4, 5, 6, 7, 8} : Finset (Fin 9)),
        (q16Src g = p ∨ q16Tgt g = p) → g = f := by decide
  have hsub : C ⊆ ↑q16Cycle := hC.subset_of_pendant hloop hsub₁ fun f hf hf' =>
    hpend₂ f (by simpa using hf) (by simpa using hf')
  obtain ⟨f₀, hf₀⟩ : C.Nonempty := by
    obtain ⟨k, v, e, hcyc, rfl⟩ := hC
    exact ⟨e ⟨0, hcyc.pos⟩, ⟨_, rfl⟩⟩
  have hdeg : ∀ x, {f | f ∈ (↑q16Cycle : Set (Fin 9)) ∧ ((q16 a b c).graph.source f = x ∨
      (q16 a b c).graph.target f = x)}.ncard ≤ 2 := by
    intro x
    have e : {f | f ∈ (↑q16Cycle : Set (Fin 9)) ∧ ((q16 a b c).graph.source f = x ∨
        (q16 a b c).graph.target f = x)} =
        ↑(q16Cycle.filter fun f => q16Src f = x ∨ q16Tgt f = x) := by
      ext f
      simp only [Set.mem_ofPred_eq, coe_filter, mem_coe]
      rfl
    have key : ∀ x : Fin 9, #(q16Cycle.filter fun f => q16Src f = x ∨ q16Tgt f = x) ≤ 2 := by
      decide
    rw [e, Set.ncard_coe_finset]
    exact key x
  -- the nodes of the cycle are joined to `8` along its edges
  have h85 : (q16 a b c).graph.AdjOn ↑q16Cycle 8 5 := ⟨8, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have h56 : (q16 a b c).graph.AdjOn ↑q16Cycle 5 6 := ⟨5, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have hw : ∀ y : Fin 9, y = 5 ∨ y = 6 ∨ y = 8 → (q16 a b c).graph.Walks ↑q16Cycle 8 y := by
    rintro y (rfl | rfl | rfl)
    · exact Relation.ReflTransGen.single h85
    · exact (Relation.ReflTransGen.single h85).tail h56
    · exact .refl
  have hsrc : ∀ f ∈ q16Cycle, q16Src f = 5 ∨ q16Src f = 6 ∨ q16Src f = 8 := by decide
  have hconn : ∀ f ∈ (↑q16Cycle : Set (Fin 9)),
      (q16 a b c).graph.Walks ↑q16Cycle ((q16 a b c).graph.source f₀) ((q16 a b c).graph.source f) :=
    fun f hf => ((q16 a b c).graph.walks_symm (hw _ (hsrc f₀ (hsub hf₀)))).trans
      (hw _ (hsrc f (by simpa using hf)))
  exact hsub.antisymm (hC.superset_of_ncard_incident_le hloop hsub hdeg (source_mem_cycleNodes hf₀)
    hconn)

theorem q16_isLevelOne : IsLevelOne (q16 a b c).graph := fun _ _ hC hC' _ =>
  (q16_cycle_eq hC).trans (q16_cycle_eq hC').symm

/-! ### The root is the LSA -/

theorem q16_isLSANetwork (h : Distinct4 a b c d) : (q16 a b c).IsLSANetwork := by
  refine ⟨root_isStableAncestor _ _, fun w hw => ?_⟩
  suffices hw8 : w = 8 by rw [hw8]; exact .refl
  by_contra hne
  have hlc : (q16 a b c).leaf c = 2 := quartetLeaf9_c h
  have hld : (q16 a b c).leaf d = 3 := quartetLeaf9_d h
  by_cases h73 : w = 7 ∨ w = 3
  · -- the path `8 → 5 → 6 → 2` to `c` avoids `w`
    have hw5 : w ≠ 5 := by rcases h73 with rfl | rfl <;> decide
    have hw6 : w ≠ 6 := by rcases h73 with rfl | rfl <;> decide
    have hw2 : w ≠ 2 := by rcases h73 with rfl | rfl <;> decide
    refine hw c (Set.mem_univ _) ?_
    rw [hlc]
    exact ⟨Ne.symm hne, Ne.symm hw2, ((Relation.ReflTransGen.single
      ⟨⟨8, rfl, rfl⟩, Ne.symm hne, Ne.symm hw5⟩).tail ⟨⟨5, rfl, rfl⟩, Ne.symm hw5, Ne.symm hw6⟩).tail
        ⟨⟨2, rfl, rfl⟩, Ne.symm hw6, Ne.symm hw2⟩⟩
  · -- the path `8 → 7 → 3` to `d` avoids `w`
    have hw7 : w ≠ 7 := fun e => h73 (Or.inl e)
    have hw3 : w ≠ 3 := fun e => h73 (Or.inr e)
    refine hw d (Set.mem_univ _) ?_
    rw [hld]
    exact ⟨Ne.symm hne, Ne.symm hw3, (Relation.ReflTransGen.single
      ⟨⟨7, rfl, rfl⟩, Ne.symm hne, Ne.symm hw7⟩).tail ⟨⟨3, rfl, rfl⟩, Ne.symm hw7, Ne.symm hw3⟩⟩

/-! ### The parameters -/

theorem q16_isHybridArc_iff (e : Fin 9) : (q16 a b c).IsHybridArc e ↔ e = 6 ∨ e = 7 := by
  unfold IsHybridArc
  rw [q16_indegree]
  show 2 ≤ #(univ.filter fun f => q16Tgt f = q16Tgt e) ↔ e = 6 ∨ e = 7
  revert e
  decide

theorem q16_isTreeArc_iff (e : Fin 9) : (q16 a b c).IsTreeArc e ↔ ¬ (e = 6 ∨ e = 7) := by
  unfold IsTreeArc
  rw [q16_indegree]
  show #(univ.filter fun f => q16Tgt f = q16Tgt e) = 1 ↔ ¬ (e = 6 ∨ e = 7)
  revert e
  decide

theorem q16Metric_isMetricNetwork {len : Fin 8 → ℝ} (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ)
    (hγ₁ : γ < 1) : IsMetricNetwork (q16 a b c) (q16Metric len γ) := by
  have hpos : ∀ e, 0 < (q16Metric len γ).length e := by
    intro e
    fin_cases e <;> simp [q16Metric, hlen]
  refine ⟨⟨fun e _ => hpos e, fun e _ => (hpos e).le, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩,
    hpos⟩
  · rw [q16_isTreeArc_iff] at he
    fin_cases e <;> simp_all [q16Metric]
  · rw [q16_isHybridArc_iff] at he
    rcases he with rfl | rfl
    · simpa [q16Metric] using hγ₀
    · simpa [q16Metric] using hγ₁
  · rw [q16_indegree] at hv
    have hv7 : v = 7 := by revert v; decide
    subst hv7
    simp [Fin.sum_univ_succ, q16Metric, q16, q16Tgt]

theorem isLSAQuartet_q16 [Fintype X] (hX : Fintype.card X = 4) (h : Distinct4 a b c d)
    {len : Fin 8 → ℝ} (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    IsLSAQuartet (q16 a b c) (q16Metric len γ) :=
  ⟨q16_isBinaryRootedNetwork hX h, q16_isLevelOne, q16_isLSANetwork h, hX,
    q16Metric_isMetricNetwork hlen hγ₀ hγ₁⟩

theorem q16_reaches_seven {w : Fin 9} (hw : (q16 a b c).graph.Reaches 7 w) :
    w ∈ ({7, 3} : Finset (Fin 9)) := by
  induction hw with
  | refl => decide
  | @tail p q _ hpq ih =>
    obtain ⟨e, rfl, rfl⟩ := hpq
    have key : ∀ e, q16Src e ∈ ({7, 3} : Finset (Fin 9)) → q16Tgt e ∈ ({7, 3} : Finset (Fin 9)) := by
      decide
    exact key e ih

/-- **The cycle of `q16` induces a `3₁`-cycle**, with hybrid node `7` above `d`. -/
theorem inducesCycleType_q16 [Fintype X] (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    InducesCycleType (q16 a b c) ↑q16Cycle 7 3 1 := by
  refine ⟨q16_isCycle, ⟨6, by decide, Or.inr rfl⟩, by rw [q16_indegree]; decide, ?_, ?_⟩
  · have h8 : (q16 a b c).root ∈ cycleNodes (q16 a b c).graph ↑q16Cycle :=
      ⟨8, by decide, Or.inl rfl⟩
    rw [ite_eq_left h8, Set.ncard_coe_finset]
    decide
  · have hset : {x | (q16 a b c).graph.Reaches 7 ((q16 a b c).leaf x)} = {d} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hx
        have := q16_reaches_seven hx
        rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl
        · rw [show (q16 x b c).leaf x = 0 from quartetLeaf9_a] at this
          exact absurd this (by decide)
        · rw [show (q16 a x c).leaf x = 1 from quartetLeaf9_b h] at this
          exact absurd this (by decide)
        · rw [show (q16 a b x).leaf x = 2 from quartetLeaf9_c h] at this
          exact absurd this (by decide)
        · rfl
      · rintro rfl
        rw [show (q16 a b c).leaf x = 3 from quartetLeaf9_d h]
        exact Relation.ReflTransGen.single ⟨3, rfl, rfl⟩
    rw [hset, Set.ncard_singleton]

/-! ### The trees of Lemma 10 -/

section Trees

variable [Fintype X]

/-- The descendants of the nodes of `q16` without the hybrid edge `7`. -/
def q16DescSeven : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {4, 0, 1}, {5, 4, 0, 1, 6, 2, 7, 3}, {6, 2, 7, 3}, {7, 3}, univ]

/-- The descendants of the nodes of `q16` without the hybrid edge `6`. -/
def q16DescSix : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {4, 0, 1}, {5, 4, 0, 1, 6, 2}, {6, 2}, {7, 3}, univ]

/-- The edges `5 → 4` and `5 → 6` of `q16` without the hybrid edge `7`. -/
def q16ArcsSeven : Finset {e : Fin 9 // e ≠ 7} := {⟨4, by decide⟩, ⟨5, by decide⟩}

/-- The edge `5 → 4` of `q16` without the hybrid edge `6`. -/
def q16ArcSix : {e : Fin 9 // e ≠ 6} := ⟨4, by decide⟩

/-- **`q16` without the hybrid edge `7` is a tree with the split `ab|cd`**, of length `t₁ + t₂`: the
concordance factor of `ab|cd` is `1 - ⅔x₁x₂`, those of `ac|bd` and `ad|bc` are `⅓x₁x₂`
(equation (1)). -/
theorem cf_deleteArc_q16_seven (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    cf (deleteArc (q16 a b c) 7) (deleteArcMetric (q16 a b c) 7 (q16Metric len γ))
        (quartetTree a b c d h) = 1 - 2 / 3 * (Real.exp (-len 4) * Real.exp (-len 5)) ∧
      cf (deleteArc (q16 a b c) 7) (deleteArcMetric (q16 a b c) 7 (q16Metric len γ))
        (quartetTree a c b d (distinct4_acbd h)) = 1 / 3 * (Real.exp (-len 4) * Real.exp (-len 5)) ∧
      cf (deleteArc (q16 a b c) 7) (deleteArcMetric (q16 a b c) 7 (q16Metric len γ))
        (quartetTree a d b c (distinct4_adbc h)) = 1 / 3 * (Real.exp (-len 4) * Real.exp (-len 5)) := by
  have hQ := isLSAQuartet_q16 hX h hlen hγ₀ hγ₁
  have hN : (deleteArc (q16 a b c) 7).IsPhylogenetic :=
    isPhylogenetic_deleteArc hQ.binary.1 (h' := 6) (g := 8) (by decide) rfl (by decide) rfl
  have ht : ∀ e, ¬ (deleteArc (q16 a b c) 7).IsHybridArc e := by
    intro e
    unfold IsHybridArc
    rw [deleteArc_q16_indegree]
    show ¬ 2 ≤ #(univ.filter fun f : {e : Fin 9 // e ≠ 7} => q16Tgt f.1 = q16Tgt e.1)
    revert e
    decide
  have hθ : (deleteArc (q16 a b c) 7).IsMetric (deleteArcMetric (q16 a b c) 7 (q16Metric len γ)) := by
    convert isMetric_deleteArc hQ.binary.1 hQ.metric.1 hQ.metric.2 (h := 7) (h' := 6) (by decide)
      rfl (by rw [q16_indegree]; show #(univ.filter fun e => q16Tgt e = 7) = 2; decide)
  have hD : ∀ u w, (deleteArc (q16 a b c) 7).graph.Reaches u w ↔ w ∈ q16DescSeven u :=
    reaches_iff_mem_of_desc q16DescSeven (by decide)
      (by show ∀ u (e : {e : Fin 9 // e ≠ 7}), q16Src e.1 ∈ q16DescSeven u →
            q16Tgt e.1 ∈ q16DescSeven u
          decide)
      (by show ∀ u, ∀ w ∈ q16DescSeven u, w ≠ u → ∃ e : {e : Fin 9 // e ≠ 7}, q16Src e.1 = u ∧
            w ∈ q16DescSeven (q16Tgt e.1) ∧ #(q16DescSeven (q16Tgt e.1)) < #(q16DescSeven u)
          decide)
  have hS : leafSet (deleteArc (q16 a b c) 7).leaf {0, 1} = {a, b} := by
    ext x
    rw [show (deleteArc (q16 a b c) 7).leaf = quartetLeaf9 a b c from rfl,
      leafSet_quartetLeaf9 hX h]
    simp only [mem_insert, mem_singleton]
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]
  have hSc : leafSet (deleteArc (q16 a b c) 7).leaf {2, 3} = {a, b}ᶜ := by
    ext x
    rw [show (deleteArc (q16 a b c) 7).leaf = quartetLeaf9 a b c from rfl,
      leafSet_quartetLeaf9 hX h]
    simp only [mem_compl, mem_insert, mem_singleton]
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]
  obtain ⟨e₁, e₂, e₃⟩ := cf_eq_of_desc hN ht hθ hX h q16DescSeven hD
    (L := {0, 1, 2, 3}) quartetLeaf9_mem (quartetLeaf9_surj h) hS hSc (v := 4) (by decide)
    q16ArcsSeven (by
      show ∀ e : {e : Fin 9 // e ≠ 7}, e ∈ q16ArcsSeven ↔
        (q16DescSeven (q16Tgt e.1) ∩ {0, 1, 2, 3} ≠ {0, 1, 2, 3} ∧
          (q16DescSeven (q16Tgt e.1) ∩ {0, 1, 2, 3} = {0, 1} ∩ {0, 1, 2, 3} ∨
            q16DescSeven (q16Tgt e.1) ∩ {0, 1, 2, 3} = {2, 3} ∩ {0, 1, 2, 3}))
      decide)
  have hlen : Real.exp (-∑ e ∈ q16ArcsSeven,
      (deleteArcMetric (q16 a b c) 7 (q16Metric len γ)).length e) =
        Real.exp (-len 4) * Real.exp (-len 5) := by
    rw [← Real.exp_add, q16ArcsSeven, sum_pair (by decide), neg_add]
    rfl
  rw [hlen] at e₁ e₂ e₃
  exact ⟨e₁, e₂, e₃⟩

/-- **`q16` without the hybrid edge `6` is a tree with the split `ab|cd`**, of length `t₁`: the
concordance factor of `ab|cd` is `1 - ⅔x₁`, those of `ac|bd` and `ad|bc` are `⅓x₁` (equation (1)). -/
theorem cf_deleteArc_q16_six (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    cf (deleteArc (q16 a b c) 6) (deleteArcMetric (q16 a b c) 6 (q16Metric len γ))
        (quartetTree a b c d h) = 1 - 2 / 3 * Real.exp (-len 4) ∧
      cf (deleteArc (q16 a b c) 6) (deleteArcMetric (q16 a b c) 6 (q16Metric len γ))
        (quartetTree a c b d (distinct4_acbd h)) = 1 / 3 * Real.exp (-len 4) ∧
      cf (deleteArc (q16 a b c) 6) (deleteArcMetric (q16 a b c) 6 (q16Metric len γ))
        (quartetTree a d b c (distinct4_adbc h)) = 1 / 3 * Real.exp (-len 4) := by
  have hQ := isLSAQuartet_q16 hX h hlen hγ₀ hγ₁
  have hN : (deleteArc (q16 a b c) 6).IsPhylogenetic :=
    isPhylogenetic_deleteArc hQ.binary.1 (h' := 7) (g := 2) (by decide) rfl (by decide) rfl
  have ht : ∀ e, ¬ (deleteArc (q16 a b c) 6).IsHybridArc e := by
    intro e
    unfold IsHybridArc
    rw [deleteArc_q16_indegree]
    show ¬ 2 ≤ #(univ.filter fun f : {e : Fin 9 // e ≠ 6} => q16Tgt f.1 = q16Tgt e.1)
    revert e
    decide
  have hθ : (deleteArc (q16 a b c) 6).IsMetric (deleteArcMetric (q16 a b c) 6 (q16Metric len γ)) := by
    convert isMetric_deleteArc hQ.binary.1 hQ.metric.1 hQ.metric.2 (h := 6) (h' := 7) (by decide)
      rfl (by rw [q16_indegree]; show #(univ.filter fun e => q16Tgt e = 7) = 2; decide)
  have hD : ∀ u w, (deleteArc (q16 a b c) 6).graph.Reaches u w ↔ w ∈ q16DescSix u :=
    reaches_iff_mem_of_desc q16DescSix (by decide)
      (by show ∀ u (e : {e : Fin 9 // e ≠ 6}), q16Src e.1 ∈ q16DescSix u →
            q16Tgt e.1 ∈ q16DescSix u
          decide)
      (by show ∀ u, ∀ w ∈ q16DescSix u, w ≠ u → ∃ e : {e : Fin 9 // e ≠ 6}, q16Src e.1 = u ∧
            w ∈ q16DescSix (q16Tgt e.1) ∧ #(q16DescSix (q16Tgt e.1)) < #(q16DescSix u)
          decide)
  have hS : leafSet (deleteArc (q16 a b c) 6).leaf {0, 1} = {a, b} := by
    ext x
    rw [show (deleteArc (q16 a b c) 6).leaf = quartetLeaf9 a b c from rfl,
      leafSet_quartetLeaf9 hX h]
    simp only [mem_insert, mem_singleton]
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]
  have hSc : leafSet (deleteArc (q16 a b c) 6).leaf {2, 3} = {a, b}ᶜ := by
    ext x
    rw [show (deleteArc (q16 a b c) 6).leaf = quartetLeaf9 a b c from rfl,
      leafSet_quartetLeaf9 hX h]
    simp only [mem_compl, mem_insert, mem_singleton]
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]
  obtain ⟨e₁, e₂, e₃⟩ := cf_eq_of_desc hN ht hθ hX h q16DescSix hD
    (L := {0, 1, 2, 3}) quartetLeaf9_mem (quartetLeaf9_surj h) hS hSc (v := 4) (by decide)
    {q16ArcSix} (by
      show ∀ e : {e : Fin 9 // e ≠ 6}, e ∈ ({q16ArcSix} : Finset _) ↔
        (q16DescSix (q16Tgt e.1) ∩ {0, 1, 2, 3} ≠ {0, 1, 2, 3} ∧
          (q16DescSix (q16Tgt e.1) ∩ {0, 1, 2, 3} = {0, 1} ∩ {0, 1, 2, 3} ∨
            q16DescSix (q16Tgt e.1) ∩ {0, 1, 2, 3} = {2, 3} ∩ {0, 1, 2, 3}))
      decide)
  have hlen4 : ∑ e ∈ ({q16ArcSix} : Finset {e : Fin 9 // e ≠ 6}),
      (deleteArcMetric (q16 a b c) 6 (q16Metric len γ)).length e = len 4 := by
    rw [sum_singleton]
    rfl
  rw [hlen4] at e₁ e₂ e₃
  exact ⟨e₁, e₂, e₃⟩

end Trees

end Banos2019
