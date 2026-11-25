module

public import Banos2019.Identify.TildeDefs
public import Banos2019.Identify.Generic
public import Phylogenetics.NMSC.DisplayedTreeModel

/-!
# The generic conditions of Theorem 4

* `forGenericParams_nonDegenerateCF`: for generic parameters, the three concordance factors on a set
  of four taxa are not all equal.
* `forGenericParams_goodParams`: the conditions `GoodParams` hold for generic parameters.

The paper reads quartet trees from the orderings of concordance factors without stating the first
condition. Its proof is the analytic argument of lean4-phylogenetics
(`RootedNetwork.isGenericNull_of_analyticOnNhd`), from normalized parameters, at a point on the
boundary of the parameters: those of a parent choice (`RootedNetwork.choiceMetric`), where every
hybrid node keeps one parent with inheritance `1`. There the network behaves as the tree of the
choice, which in a binary network resolves every set of four taxa
(`exists_displays_displayedSides_of_isBinary`), so that with positive lengths the quartet tree it
displays is strictly the most probable (`nmscCF_choiceMetric_alternative_lt`).

* `exists_card_displayedCluster_inter_eq_two`, `exists_displays_displayedSides_of_isBinary`: in a
  binary network the tree of a parent choice displays a quartet tree on every set of four taxa.
* `nmscCF_choiceMetric_alternative_lt`: in the parameters of a parent choice, with positive lengths,
  a quartet tree displayed by the tree of the choice has a larger concordance factor than its
  alternatives.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

/-! ### The analytic argument from normalized parameters -/

/-! ### The tree of a parent choice in a binary network -/

/-- **In a binary network, the tree of a parent choice resolves every set of four taxa**: some
vertex has exactly two of the four taxa below it along the arcs that the choice keeps. Otherwise
every vertex would have at most one of them below it, by induction from the leaves, since a vertex
has at most two children; but the root has all four below it. -/
theorem exists_card_displayedCluster_inter_eq_two {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (c : N.ParentChoice) {s : Finset X} (hs : #s = 4) :
    ∃ u, #(N.displayedCluster c u ∩ s) = 2 := by
  obtain ⟨hP, hroot, hbin⟩ := hN
  by_contra! hne
  -- a vertex has at most two children
  have hout : ∀ u, #(univ.filter fun e => N.graph.source e = u) ≤ 2 := by
    intro u
    have hdeg : N.graph.outdegree u = #(univ.filter fun e => N.graph.source e = u) := by
      rw [DirectedMultigraph.outdegree, ← Set.ncard_coe_finset, coe_filter_univ]
    rw [← hdeg]
    by_cases hu : u = N.root
    · rw [hu, hroot]
    · by_cases h0 : N.graph.outdegree u = 0
      · omega
      · have := hbin u hu h0
        have := hP.nonroot_indegree u hu
        omega
  -- every vertex has at most one of the taxa below it, by induction on the vertices it reaches
  have key : ∀ n u, #(univ.filter fun w => N.graph.Reaches u w) = n →
      #(N.displayedCluster c u ∩ s) ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro u hn
      by_cases hleaf : ∃ x, N.leaf x = u
      · obtain ⟨x, rfl⟩ := hleaf
        refine (card_le_card fun y hy => ?_).trans (card_singleton x).le
        exact mem_singleton.2
          (eq_of_leaf_reachesOff_leaf hP (mem_displayedCluster.1 (mem_inter.1 hy).1))
      · have hsub : N.displayedCluster c u ∩ s ⊆ (univ.filter fun e => N.graph.source e = u).biUnion
            fun e => N.displayedCluster c (N.graph.target e) ∩ s := by
          intro y hy
          obtain ⟨hyu, hys⟩ := mem_inter.1 hy
          rcases Relation.ReflTransGen.cases_head (mem_displayedCluster.1 hyu) with
            h | ⟨b, ⟨f, -, hfs, hft⟩, hb⟩
          · exact absurd ⟨y, h.symm⟩ hleaf
          · exact mem_biUnion.2 ⟨f, mem_filter.2 ⟨mem_univ _, hfs⟩,
              mem_inter.2 ⟨mem_displayedCluster.2 (hft ▸ hb), hys⟩⟩
        have hchild : ∀ e ∈ univ.filter (fun e => N.graph.source e = u),
            #(N.displayedCluster c (N.graph.target e) ∩ s) ≤ 1 := by
          intro e he
          have hes : N.graph.source e = u := (mem_filter.1 he).2
          refine ih _ ?_ _ rfl
          rw [← hn]
          refine card_lt_card ⟨fun w hw => ?_, fun h => ?_⟩
          · exact mem_filter.2 ⟨mem_univ _,
              Relation.ReflTransGen.head ⟨e, hes, rfl⟩ (mem_filter.1 hw).2⟩
          · exact hP.acyclic u (Relation.TransGen.head' ⟨e, hes, rfl⟩
              (mem_filter.1 (h (mem_filter.2 ⟨mem_univ _, Relation.ReflTransGen.refl⟩))).2)
        have h2 : #(N.displayedCluster c u ∩ s) ≤ 2 :=
          calc #(N.displayedCluster c u ∩ s)
              ≤ #((univ.filter fun e => N.graph.source e = u).biUnion
                  fun e => N.displayedCluster c (N.graph.target e) ∩ s) := card_le_card hsub
            _ ≤ ∑ e ∈ univ.filter (fun e => N.graph.source e = u),
                  #(N.displayedCluster c (N.graph.target e) ∩ s) := card_biUnion_le
            _ ≤ #(univ.filter fun e => N.graph.source e = u) • 1 := sum_le_card_nsmul _ _ _ hchild
            _ ≤ 2 := by simpa using hout u
        have := hne u
        omega
  have h4 : #(N.displayedCluster c N.root ∩ s) = 4 := by
    rw [show N.displayedCluster c N.root = univ from eq_univ_of_forall fun x =>
      mem_displayedCluster.2 ((isDeletion_deletedArcs hP c).root_reachesOff hP _), univ_inter, hs]
  have := key _ N.root rfl
  omega

/-- **In a binary network, the tree of a parent choice displays a quartet tree on every set of four
taxa.** -/
theorem exists_displays_displayedSides_of_isBinary {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (c : N.ParentChoice) {s : Finset X} (hs : #s = 4) :
    ∃ r ∈ treesOn s, Displays (N.displayedSides c) r := by
  obtain ⟨u, h2⟩ := exists_card_displayedCluster_inter_eq_two hN c hs
  have hAne : N.displayedCluster c u ≠ ∅ := by
    intro h
    rw [h, empty_inter] at h2
    simp at h2
  have hAu : N.displayedCluster c u ≠ univ := by
    intro h
    rw [h, univ_inter, hs] at h2
    norm_num at h2
  have hA : N.displayedCluster c u ∈ N.displayedSides c :=
    mem_unroot.2 (Or.inl ⟨mem_displayedClusters.2 ⟨hAne, _, rfl⟩, hAu⟩)
  exact ⟨_, mem_treesOn.2 (quartetOfCherry_taxa _ _ hs inter_subset_right h2),
    displays_quartetOfCherry hA hs h2⟩

/-- **In the parameters of a parent choice, with positive lengths, a quartet tree displayed by the
tree of the choice has a larger concordance factor than its alternatives** (with independent
inheritance, `ρ = 0`): the network then behaves as the tree of the choice, in which an arc of positive
length separates the two cherries of the quartet tree. -/
theorem nmscCF_choiceMetric_alternative_lt {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (c : N.ParentChoice) {θ : MetricData E} (hℓ : ∀ f, 0 < θ.length f) {r : QuartetTree X}
    (hd : Displays (N.displayedSides c) r) {r' : QuartetTree X} (hr' : r' ∈ r.alternatives) :
    nmscCF N (N.choiceMetric θ c) 0 r' < nmscCF N (N.choiceMetric θ c) 0 r := by
  obtain ⟨P, hP, e, he, hb, hn⟩ := exists_isKeptArc_of_displays hN hd
  obtain ⟨a, -⟩ : P.Nonempty := card_pos.1 (by rw [r.card_of_mem hP]; omega)
  have hM := isPhylogenetic_choiceNetwork hN c a
  rw [← nmscCF_choiceNetwork hN c a le_rfl θ r, ← nmscCF_choiceNetwork hN c a le_rfl θ r']
  have h := one_sub_exp_le_sub_nmscCF_of_tree hM
    (isMetric_choiceNetworkMetric hN c a fun f _ => hℓ f) ⟨le_rfl, zero_le_one⟩
    (fun f g h => eq_of_target_choiceNetwork hN c a h) r hP (e := ⟨e, he⟩)
    (fun x hx => reaches_choiceNetwork hN c a _ _ (hb x hx))
    (fun x hx hxP hb' => hn x hx hxP (reachesOff_of_reaches_choiceNetwork hN c a hb')) hr'
  have hexp : Real.exp (-(N.choiceNetworkMetric θ c).length ⟨e, he⟩) < 1 :=
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (hℓ e))
  linarith

/-! ### The generic conditions -/

/-- **For generic parameters, the concordance factors on a set of four taxa are not all equal**, on
every binary network. For each set `s` of four taxa, the tree of a parent choice displays a quartet
tree `r` on `s`; in the parameters of the choice with lengths `1`, the concordance factor of `r`
exceeds that of an alternative `r'`, so that the analytic function `CF(r) - CF(r')` of the
coordinates vanishes only on a null set. -/
theorem forGenericParams_nonDegenerateCF {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) :
    ForGenericParams N fun θ => IsMetricNetwork N θ → NonDegenerateCF (cf N θ) := by
  -- a parent choice, and lengths `1`
  have hpar : ∀ v : {v : V // v ≠ N.root}, Nonempty {e : E // N.graph.target e = v.val} := by
    intro v
    have h := hN.1.nonroot_indegree v.1 v.2
    obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (s := {e | N.graph.target e = v.1})
      (by unfold DirectedMultigraph.indegree at h; omega)
    exact ⟨⟨e, he⟩⟩
  let c₀ : N.ParentChoice := fun v => (hpar v).some
  let θ₁ : MetricData E := ⟨fun _ => 1, fun _ => 0⟩
  refine (forGenericParams_iInter (ι := {s : Finset X // #s = 4})
    (P := fun s θ => IsMetricNetwork N θ → ∃ q ∈ treesOn s.1, ∃ r ∈ treesOn s.1, cf N θ q ≠ cf N θ r)
    fun s => ?_).mono fun θ h hθ s hs => h ⟨s, hs⟩ hθ
  -- the quartet tree on `s` displayed by the tree of `c₀`, and an alternative
  obtain ⟨r, hr, hd⟩ := exists_displays_displayedSides_of_isBinary hN c₀ s.2
  obtain ⟨r', hr'⟩ : r.alternatives.Nonempty := card_pos.1 (by rw [r.card_alternatives]; omega)
  have hr'' : r' ∈ treesOn s.1 :=
    mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr').1.trans (mem_treesOn.1 hr))
  have hlt := nmscCF_choiceMetric_alternative_lt hN.1 c₀ (θ := θ₁) (fun _ => one_pos) hd hr'
  refine (isGenericNull_of_analyticOnNhd (F := fun θ => nmscCF N θ 0 r - nmscCF N θ 0 r')
    (fun d => (analyticOnNhd_nmscCF_coordMetric N d 0 r).sub
      (analyticOnNhd_nmscCF_coordMetric N d 0 r'))
    (isNormalized_choiceMetric hN.1 θ₁ c₀) (sub_ne_zero.2 hlt.ne')).mono fun θ hθ => ?_
  have hm : IsMetricNetwork N θ := by
    by_contra hm
    exact hθ fun h => absurd h hm
  refine ⟨hm.1, sub_eq_zero.2 ?_⟩
  by_contra hne
  exact hθ fun _ => ⟨r, hr, r', hr'', hne⟩

/-- **The conditions of Theorem 4 hold for generic parameters** (Lemma 12 and
`forGenericParams_nonDegenerateCF`). -/
theorem forGenericParams_goodParams {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) : ForGenericParams N (GoodParams hX N) := by
  obtain rfl : ‹DecidableEq X› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  exact ((lemma12 hN h1 hX).and (forGenericParams_nonDegenerateCF hN)).mono
    fun θ h hθ _ => ⟨h.1 hθ, h.2 hθ⟩

end Banos2019
