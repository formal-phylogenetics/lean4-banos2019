module

public import Banos2019.Bridge.Model
public import Banos2019.Quartet.Trees
public import Banos2019.Quartet.Examples
public import Banos2019.Quartet.Fig18
public import Banos2019.Basic.Data.Set.Card

/-!
# Equation (1) on an explicit quartet tree, on the Challenge's definitions

The balanced rooted quartet tree `((0,1),(2,3))`: the root `0` has the children `1` and `2`, the
node `1` the leaves `3, 4` of the taxa `0, 1`, the node `2` the leaves `5, 6` of the taxa `2, 3`.
Its root edges have lengths `t₁` and `t₂`, so its unrooted internal edge has length `t₁ + t₂`, and
its pendant edges have length one. It is a binary metric network of the Challenge
(`balanced_isBinaryNetwork`, `balanced_isMetric`), and its concordance factors are those of equation
(1) (`equation1_balanced`), by the library's identification of the coalescent on a network without
hybrid edges with the multispecies coalescent on its species tree (`nmscCF_eq_quartetProb`) and
equation (1) of Allman, Degnan and Rhodes 2011 (`External.AllmanDegnanRhodes2011.equation1`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace Banos2019.Model

/-- The balanced rooted quartet tree `((0,1),(2,3))`. -/
abbrev balancedTree : Network (Fin 7) (Fin 6) (Fin 4) :=
  ⟨⟨![0, 0, 1, 1, 2, 2], ![1, 2, 3, 4, 5, 6]⟩, 0, ![3, 4, 5, 6]⟩

/-- Its parameters: root edges of lengths `t₁` and `t₂`, pendant edges of length one, tree edges of
inheritance probability one. -/
abbrev balancedParams (t₁ t₂ : ℝ) : Params (Fin 6) := ⟨![t₁, t₂, 1, 1, 1, 1], fun _ => 1⟩

theorem balanced_indegree (v : Fin 7) :
    balancedTree.graph.indegree v = if v = 0 then 0 else 1 := by
  unfold Digraph.indegree
  rw [Set.ncard_setOf_eq_card_filter]
  revert v
  decide

theorem balanced_outdegree (v : Fin 7) :
    balancedTree.graph.outdegree v = if v.1 < 3 then 2 else 0 := by
  unfold Digraph.outdegree
  rw [Set.ncard_setOf_eq_card_filter]
  revert v
  decide

theorem balanced_source_lt (e : Fin 6) :
    balancedTree.graph.source e < balancedTree.graph.target e := by
  revert e
  decide

theorem balanced_isBinaryNetwork : balancedTree.IsBinaryNetwork := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun v h => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have key : ∀ u w, Relation.TransGen balancedTree.graph.Adj u w → u < w := by
      intro u w h
      induction h with
      | single h =>
        obtain ⟨e, rfl, rfl⟩ := h
        exact balanced_source_lt e
      | tail _ h ih =>
        obtain ⟨e, he, rfl⟩ := h
        exact ih.trans (he ▸ balanced_source_lt e)
    exact lt_irrefl v (key v v h)
  · rw [balanced_indegree]
    rfl
  · rw [balanced_outdegree]
    rfl
  · intro x
    rw [balanced_indegree, balanced_outdegree]
    revert x
    decide
  · decide
  · intro v hv hl
    rw [balanced_indegree, balanced_outdegree]
    have hl' : ∀ x, balancedTree.leaf x ≠ v := fun x h => hl ⟨x, h⟩
    revert v
    decide

/-- The nodes below each node. -/
theorem balanced_reaches_iff (u v : Fin 7) :
    balancedTree.graph.Reaches u v ↔
      u = v ∨ u = 0 ∨ (u = 1 ∧ (v = 3 ∨ v = 4)) ∨ (u = 2 ∧ (v = 5 ∨ v = 6)) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ h ih =>
      obtain ⟨e, he, rfl⟩ := h
      have key : ∀ (u a : Fin 7) (e : Fin 6),
          (u = a ∨ u = 0 ∨ (u = 1 ∧ (a = 3 ∨ a = 4)) ∨ (u = 2 ∧ (a = 5 ∨ a = 6))) →
          balancedTree.graph.source e = a →
          (u = balancedTree.graph.target e ∨ u = 0 ∨
            (u = 1 ∧ (balancedTree.graph.target e = 3 ∨ balancedTree.graph.target e = 4)) ∨
            (u = 2 ∧ (balancedTree.graph.target e = 5 ∨ balancedTree.graph.target e = 6))) := by
        decide
      exact key _ _ e ih he
  · rintro (rfl | rfl | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩)
    · exact .refl
    · exact ((Network.isBinaryNetwork_iff _).mp balanced_isBinaryNetwork).1.root_reaches v
    · exact .single ⟨2, rfl, rfl⟩
    · exact .single ⟨3, rfl, rfl⟩
    · exact .single ⟨4, rfl, rfl⟩
    · exact .single ⟨5, rfl, rfl⟩

/-- The taxa below the target of each edge. -/
theorem balanced_treeCluster (e : Fin 6) :
    treeCluster balancedTree.toRooted (balancedTree.graph.target e) =
      ![{0, 1}, {2, 3}, {0}, {1}, {2}, {3}] e := by
  ext x
  rw [mem_treeCluster]
  change balancedTree.graph.Reaches _ (balancedTree.leaf x) ↔ _
  rw [balanced_reaches_iff]
  revert e x
  decide

theorem balanced_treeCluster_one : treeCluster balancedTree.toRooted 1 = {0, 1} :=
  balanced_treeCluster 0

theorem balanced_isMetric {t₁ t₂ : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂) :
    balancedTree.IsMetric (balancedParams t₁ t₂) := by
  have hh : ∀ e, ¬ balancedTree.IsHybridEdge e := fun e => by
    unfold Network.IsHybridEdge
    rw [balanced_indegree]
    revert e
    decide
  refine ⟨fun e => ?_, fun _ _ => rfl, fun e he => absurd he (hh e), fun e _ _ he =>
    absurd he (hh e)⟩
  fin_cases e <;> simp [h₁, h₂]

/-- **Equation (1)** on the balanced quartet tree. -/
theorem equation1_balanced (t₁ t₂ : ℝ) (h₁ : 0 < t₁) (h₂ : 0 < t₂) :
    let N : Network (Fin 7) (Fin 6) (Fin 4) :=
        ⟨⟨![0, 0, 1, 1, 2, 2], ![1, 2, 3, 4, 5, 6]⟩, 0, ![3, 4, 5, 6]⟩
    let θ : Params (Fin 6) := ⟨![t₁, t₂, 1, 1, 1, 1], fun _ => 1⟩
    N.IsBinaryNetwork ∧ N.IsMetric θ ∧
      ∀ q : QuartetTree (Fin 4),
        (q.1 = {{0, 1}, {2, 3}} → N.cf θ q = 1 - 2 / 3 * Real.exp (-(t₁ + t₂))) ∧
        (q.1 = {{0, 2}, {1, 3}} → N.cf θ q = 1 / 3 * Real.exp (-(t₁ + t₂))) ∧
        (q.1 = {{0, 3}, {1, 2}} → N.cf θ q = 1 / 3 * Real.exp (-(t₁ + t₂))) := by
  intro N θ
  change balancedTree.IsBinaryNetwork ∧ balancedTree.IsMetric (balancedParams t₁ t₂) ∧
    ∀ q : QuartetTree (Fin 4),
      (q.1 = {{0, 1}, {2, 3}} → balancedTree.cf (balancedParams t₁ t₂) q =
        1 - 2 / 3 * Real.exp (-(t₁ + t₂))) ∧
      (q.1 = {{0, 2}, {1, 3}} → balancedTree.cf (balancedParams t₁ t₂) q =
        1 / 3 * Real.exp (-(t₁ + t₂))) ∧
      (q.1 = {{0, 3}, {1, 2}} → balancedTree.cf (balancedParams t₁ t₂) q =
        1 / 3 * Real.exp (-(t₁ + t₂)))
  have hN := balanced_isBinaryNetwork
  have hθ := balanced_isMetric h₁ h₂
  refine ⟨hN, hθ, ?_⟩
  have hb := (Network.isBinaryNetwork_iff _).mp hN
  have hθ' := ((balancedTree.isMetric_iff hN _).mp hθ).1
  have ht : ∀ e, ¬ balancedTree.toRooted.IsHybridArc e := fun e => by
    unfold IsHybridArc
    change ¬ 2 ≤ balancedTree.graph.indegree _
    rw [balanced_indegree]
    revert e
    decide
  set σ := treeSpeciesTree balancedTree.toRooted hb.1 ht hθ'
  have hcf : ∀ q, balancedTree.cf (balancedParams t₁ t₂) q =
      External.AllmanDegnanRhodes2011.quartetProb σ (quartetTreeEquiv q) := fun q => by
    rw [balancedTree.cf_eq]
    exact nmscCF_eq_quartetProb hb.1 ht hθ' (by simp) le_rfl _
  have hsplit : {0, 1} ∈ unroot σ.clusters := by
    simp only [unroot, mem_union, mem_erase, σ, treeSpeciesTree_clusters]
    refine Or.inl ⟨by decide, mem_treeClusters.2 ⟨1, balanced_treeCluster_one⟩⟩
  have hlen : σ.unrootedLength {0, 1} = t₁ + t₂ := by
    rw [treeSpeciesTree_unrootedLength]
    have hf : (univ.filter fun e : Fin 6 =>
        treeCluster balancedTree.toRooted (balancedTree.toRooted.graph.target e) ≠ univ ∧
          (treeCluster balancedTree.toRooted (balancedTree.toRooted.graph.target e) = {0, 1} ∨
            treeCluster balancedTree.toRooted (balancedTree.toRooted.graph.target e) = {0, 1}ᶜ)) =
        {0, 1} := by
      ext e
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      change treeCluster balancedTree.toRooted (balancedTree.graph.target e) ≠ univ ∧ _ ↔ _
      change _ ∧ (treeCluster balancedTree.toRooted (balancedTree.graph.target e) = {0, 1} ∨
        treeCluster balancedTree.toRooted (balancedTree.graph.target e) = {0, 1}ᶜ) ↔ _
      rw [balanced_treeCluster]
      revert e
      decide
    rw [hf, sum_pair (by decide)]
    rfl
  have hq₀ : Phylogenetics.IsQuartetTree ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))) := by
    unfold Phylogenetics.IsQuartetTree
    decide
  obtain ⟨e₁, e₂⟩ := External.AllmanDegnanRhodes2011.equation1 (X := Fin 4) (by simp) σ
    (q := ⟨_, hq₀⟩) (a := 0) (b := 1) (c := 2) (d := 3) rfl hsplit
  rw [hlen] at e₁ e₂
  have halt : ∀ q : QuartetTree (Fin 4), (q.1 = {{0, 2}, {1, 3}} ∨ q.1 = {{0, 3}, {1, 2}}) →
      quartetTreeEquiv q ∈ Phylogenetics.QuartetTree.alternatives ⟨_, hq₀⟩ := by
    intro q hq
    unfold Phylogenetics.QuartetTree.alternatives
    rw [mem_filter]
    refine ⟨mem_univ _, ?_, fun h => ?_⟩
    · unfold Phylogenetics.QuartetTree.taxa
      rw [quartetTreeEquiv_val]
      rcases hq with hq | hq <;> rw [hq] <;> dsimp only <;> decide
    · have := congrArg Subtype.val h
      rw [quartetTreeEquiv_val] at this
      rcases hq with hq | hq <;> rw [hq] at this <;> dsimp only at this <;>
        exact absurd this (by decide)
  intro q
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_⟩
  · rw [hcf]
    have : quartetTreeEquiv q = ⟨_, hq₀⟩ := Subtype.ext hq
    rw [this, e₁]
  · rw [hcf, e₂ _ (halt q (Or.inl hq))]
  · rw [hcf, e₂ _ (halt q (Or.inr hq))]

/-! ### Examples 6 and 7 -/

theorem distinct4_fin4 : Distinct4 (0 : Fin 4) 1 2 3 := by
  unfold Distinct4
  decide

/-- **Example 6**, on the Challenge's definitions: the rooting `q18` of Figure 18, with `γ = 1/2`,
`t₁ = t₂ = -log(6/7)`, `t₃ = -log(1/14)`, `t₄ = -log(13/14)`, the root halving `t₄`. -/
theorem example6_explicit :
    let N : Network (Fin 9) (Fin 9) (Fin 4) :=
      ⟨⟨![4, 4, 6, 7, 5, 7, 8, 6, 8], ![0, 1, 2, 3, 4, 6, 5, 5, 7]⟩, 8, ![0, 1, 2, 3]⟩
    let θ : Params (Fin 9) :=
      ⟨![1, 1, 1, 1, -Real.log (6 / 7), -Real.log (1 / 14), -Real.log (13 / 14) / 2,
          -Real.log (6 / 7), -Real.log (13 / 14) / 2], ![1, 1, 1, 1, 1, 1, 1 / 2, 1 / 2, 1]⟩
    N.IsBinaryNetwork ∧ N.graph.IsLevelOne ∧ N.IsLSA Set.univ N.root ∧ N.IsMetric θ ∧
      ∀ q : QuartetTree (Fin 4),
        (q.1 = {{0, 1}, {2, 3}} → N.cf θ q = 32 / 98) ∧
        (q.1 = {{0, 2}, {1, 3}} → N.cf θ q = 33 / 98) ∧
        (q.1 = {{0, 3}, {1, 2}} → N.cf θ q = 33 / 98) := by
  intro N θ
  have hd := distinct4_fin4
  let len : Fin 8 → ℝ := ![1, 1, 1, 1, -Real.log (6 / 7), -Real.log (1 / 14), -Real.log (13 / 14),
    -Real.log (6 / 7)]
  have a₁ : Real.log (6 / 7) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have a₂ : 0 < Real.log 14 := Real.log_pos (by norm_num)
  have a₃ : Real.log (13 / 14) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hlen : ∀ i, 0 < len i := by
    intro i
    fin_cases i <;> simp [len, a₁, a₂, a₃]
  have hQ := isLSAQuartet_q18 (by simp) hd hlen (γ := 1 / 2) (by norm_num) (by norm_num)
  have hN' : N.toRooted = q18 0 1 2 := by
    change (⟨⟨_, _⟩, 8, ![0, 1, 2, 3]⟩ : RootedNetwork (Fin 9) (Fin 9) (Fin 4)) =
      ⟨⟨q18Src, q18Tgt⟩, 8, fun x => (figLeaf 0 1 2 x).castSucc⟩
    congr 1
    funext x
    fin_cases x <;> rfl
  have hθ' : θ.toMetric = q18Metric len (1 / 2) := by
    change (⟨_, _⟩ : MetricData (Fin 9)) = ⟨_, _⟩
    congr 1
    funext i
    fin_cases i <;> norm_num [θ, q18Metric]
  have hNb : N.IsBinaryNetwork := (Network.isBinaryNetwork_iff N).mpr (hN' ▸ hQ.binary)
  have h1 : N.graph.IsLevelOne := by
    rw [Digraph.isLevelOne_iff, ← Network.graph_toRooted, hN']
    exact hQ.levelOne
  have hl : N.IsLSA Set.univ N.root := by
    have := hQ.isLSA
    rw [← hN'] at this
    exact this
  have hm : N.IsMetric θ := by
    rw [N.isMetric_iff hNb, hN', hθ']
    exact hQ.metric
  refine ⟨hNb, h1, hl, hm, fun q => ?_⟩
  have e := example6 hd hQ len rfl rfl rfl rfl (inducesNetwork_q18 hd hQ)
  simp only [CF, Prod.mk.injEq] at e
  have hcf : ∀ q, N.cf θ q = Banos2019.cf (q18 0 1 2) (q18Metric len (1 / 2))
    (quartetTreeEquiv q) :=
    fun q => by rw [N.cf_eq, Function.comp_apply, hN', hθ']
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_⟩
  · rw [hcf, ← e.1]
    exact congrArg _ (Subtype.ext hq)
  · rw [hcf, ← e.2.1]
    exact congrArg _ (Subtype.ext hq)
  · rw [hcf, ← e.2.2]
    exact congrArg _ (Subtype.ext hq)

/-- **Example 7**, on the Challenge's definitions: the rooting `q17` of Figure 17, with `γ = 1/2`,
`t₁ = t₂ = -log(48/49)`, the root halving the hybrid edge from the node of `3`. -/
theorem example7_explicit :
    let N : Network (Fin 9) (Fin 9) (Fin 4) :=
      ⟨⟨![4, 5, 6, 7, 7, 4, 5, 8, 8], ![0, 1, 2, 3, 4, 5, 6, 6, 7]⟩, 8, ![0, 1, 2, 3]⟩
    let θ : Params (Fin 9) :=
      ⟨![1, 1, 1, 1, -Real.log (48 / 49), -Real.log (48 / 49), 1, 1 / 2, 1 / 2],
        ![1, 1, 1, 1, 1, 1, 1 / 2, 1 / 2, 1]⟩
    N.IsBinaryNetwork ∧ N.graph.IsLevelOne ∧ N.IsLSA Set.univ N.root ∧ N.IsMetric θ ∧
      ∀ q : QuartetTree (Fin 4),
        (q.1 = {{0, 1}, {2, 3}} → N.cf θ q = 33 / 98) ∧
        (q.1 = {{0, 2}, {1, 3}} → N.cf θ q = 32 / 98) ∧
        (q.1 = {{0, 3}, {1, 2}} → N.cf θ q = 33 / 98) := by
  intro N θ
  have hd := distinct4_fin4
  let len : Fin 8 → ℝ := ![1, 1, 1, 1, -Real.log (48 / 49), -Real.log (48 / 49), 1, 1]
  have a₁ : Real.log (48 / 49) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hlen : ∀ i, 0 < len i := by
    intro i
    fin_cases i <;> simp [len, a₁]
  have hQ := isLSAQuartet_q17 (by simp) hd hlen (γ := 1 / 2) (by norm_num) (by norm_num)
  have hN' : N.toRooted = q17 0 1 2 := by
    change (⟨⟨_, _⟩, 8, ![0, 1, 2, 3]⟩ : RootedNetwork (Fin 9) (Fin 9) (Fin 4)) =
      ⟨⟨q17Src, q17Tgt⟩, 8, quartetLeaf9 0 1 2⟩
    congr 1
    funext x
    fin_cases x <;> rfl
  have hθ' : θ.toMetric = q17Metric len (1 / 2) := by
    change (⟨_, _⟩ : MetricData (Fin 9)) = ⟨_, _⟩
    congr 1
    funext i
    fin_cases i <;> norm_num [θ, q17Metric]
  have hNb : N.IsBinaryNetwork := (Network.isBinaryNetwork_iff N).mpr (hN' ▸ hQ.binary)
  have h1 : N.graph.IsLevelOne := by
    rw [Digraph.isLevelOne_iff, ← Network.graph_toRooted, hN']
    exact hQ.levelOne
  have hl : N.IsLSA Set.univ N.root := by
    have := hQ.isLSA
    rw [← hN'] at this
    exact this
  have hm : N.IsMetric θ := by
    rw [N.isMetric_iff hNb, hN', hθ']
    exact hQ.metric
  refine ⟨hNb, h1, hl, hm, fun q => ?_⟩
  have e := (example7 hd hQ len rfl rfl (inducesNetwork_q17 hQ)).1
  simp only [CF, Prod.mk.injEq] at e
  have hcf : ∀ q, N.cf θ q = Banos2019.cf (q17 0 1 2) (q17Metric len (1 / 2))
    (quartetTreeEquiv q) :=
    fun q => by rw [N.cf_eq, Function.comp_apply, hN', hθ']
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_⟩
  · rw [hcf, ← e.1]
    exact congrArg _ (Subtype.ext hq)
  · rw [hcf, ← e.2.1]
    exact congrArg _ (Subtype.ext hq)
  · rw [hcf, ← e.2.2]
    exact congrArg _ (Subtype.ext hq)

end Banos2019.Model
