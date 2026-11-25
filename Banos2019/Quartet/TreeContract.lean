module

public import Banos2019.Quartet.ContractSet

/-!
# Contracting every cycle: a tree (proof of Proposition 6)

When every cycle of a binary level-1 network `Q` is contracted, no node has two parents, so the
contracted network is a tree in the sense of `Banos2019.Quartet.Trees`: its concordance factors are
those of its species tree `treeSpeciesTree`.

* `contractSet_not_isHybridArc`: with every cycle contracted, there is no hybrid arc.
* `hasCutSplit_iff_mem_unroot_treeClusters`: the cut edges of a network without hybrid arcs between
  two nonempty sets of taxa are the splits of its unrooted tree of clusters.
* `exists_card_two_mem_treeClusters`: a network without hybrid arcs on four taxa whose nodes have at
  most two children, but the root, which may have three, has a cluster of two taxa: a lowest node
  with at least two taxa below has a child per taxon.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Tree

variable [Fintype V] [Fintype E] [Fintype X] {N : RootedNetwork V E X}

/-- **The cut edges of a network without hybrid arcs are the splits of its clusters**: the arc into
a node `v` separates the taxa below `v` from the others. -/
theorem hasCutSplit_iff_mem_unroot_treeClusters (hN : N.IsPhylogenetic)
    (ht : ∀ e, ¬ N.IsHybridArc e) {A : Finset X} (hA : A.Nonempty) (hA' : Aᶜ.Nonempty) :
    N.HasCutSplit ↑A ↔ A ∈ unroot (treeClusters N) := by
  have hA'' : A ≠ univ := fun h => by
    rw [h, compl_univ] at hA'
    exact not_nonempty_empty hA'
  have hAc : Aᶜ ≠ univ := fun h => by
    rw [compl_eq_univ_iff] at h
    rw [h] at hA
    exact not_nonempty_empty hA
  -- the cluster of a node other than the root is the side of the arc into it
  have hcut : ∀ v, v ≠ N.root → N.HasCutSplit ↑(treeCluster N v) := by
    intro v hv
    obtain ⟨c, hc⟩ := (N.graph.indegree_eq_one_iff _).1
      (le_antisymm (indegree_le_one ht v) (hN.nonroot_indegree v hv))
    have hcv : N.graph.target c = v := (hc c).2 rfl
    have hC : IsCut N v := ⟨fun h => hv (eq_of_reaches_of_reaches hN.acyclic h (hN.root_reaches v)),
      fun e he hne => reaches_source_of_reaches_target ht he (Ne.symm hne)⟩
    have := hasCutSplit_of_isCut hN hC hcv fun g hg => (hc g).1 hg
    convert this using 2
    ext x
    simp [mem_treeCluster]
  constructor
  · rintro ⟨e, T, hT, hAT⟩
    set v := N.graph.target e
    have hnot : ∀ f, N.graph.Reaches v (N.graph.source f) → f ≠ e := fun f hf hfe =>
      hN.acyclic _ (Relation.TransGen.head' ⟨e, rfl, rfl⟩ (by rw [hfe] at hf; exact hf))
    -- the taxa below `v` are on the side of `v`, the others on the side of the root
    have hbelow : ∀ x, N.graph.Reaches v (N.leaf x) → (N.leaf x ∈ T ↔ v ∈ T) := fun x hx =>
      (N.graph.mem_iff_mem_of_walks (F := {e}ᶜ) (fun f hf hc => hf ((hT f).1 hc))
        (walks_of_reaches_of_forall hx fun f hf _ => hnot f hf)).symm
    have hroot : ∀ w, ¬ N.graph.Reaches v w → (w ∈ T ↔ N.root ∈ T) := fun w hw =>
      (N.graph.mem_iff_mem_of_walks (F := {e}ᶜ) (fun f hf hc => hf ((hT f).1 hc))
        (walks_of_reaches_of_forall (hN.root_reaches w) fun f _ hf hfe => hw (by
          rw [Set.mem_singleton_iff] at hfe
          subst hfe
          exact hf))).symm
    have hsv : N.graph.source e ∈ T ↔ ¬ v ∈ T := by
      have hc := (hT e).2 rfl
      unfold DirectedMultigraph.Crosses at hc
      tauto
    have hrs : N.root ∈ T ↔ N.graph.source e ∈ T := (hroot _ fun h =>
      hN.acyclic _ (Relation.TransGen.head' ⟨e, rfl, rfl⟩ h)).symm
    have hA_eq : ∀ x, x ∈ A ↔ (x ∈ treeCluster N v ↔ v ∈ T) := by
      intro x
      have hx : x ∈ A ↔ N.leaf x ∈ T := by
        rw [← Finset.mem_coe, ← hAT]
        rfl
      rw [hx, mem_treeCluster]
      by_cases hxv : N.graph.Reaches v (N.leaf x)
      · rw [hbelow x hxv]
        tauto
      · rw [hroot _ hxv, hrs, hsv]
        tauto
    rw [mem_unroot]
    by_cases hvT : v ∈ T
    · have : A = treeCluster N v := by
        ext x
        rw [hA_eq]
        tauto
      exact Or.inl ⟨this ▸ mem_treeClusters.2 ⟨v, rfl⟩, hA''⟩
    · have : Aᶜ = treeCluster N v := by
        ext x
        rw [mem_compl, hA_eq]
        tauto
      exact Or.inr ⟨this ▸ mem_treeClusters.2 ⟨v, rfl⟩, hAc⟩
  · intro hmem
    rcases mem_unroot.1 hmem with ⟨hB, hBu⟩ | ⟨hB, hBu⟩
    · obtain ⟨v, rfl⟩ := mem_treeClusters.1 hB
      exact hcut v fun h => hBu (h ▸ treeCluster_root hN)
    · obtain ⟨v, hv⟩ := mem_treeClusters.1 hB
      have := hcut v fun h => hBu (by rw [← hv, h, treeCluster_root hN])
      rw [hv, coe_compl, hasCutSplit_compl] at this
      exact this

/-- **A network without hybrid arcs on four taxa, whose nodes have at most two children but the
root, which has at most three, has a cluster of two taxa**: a lowest node `u` with at least two taxa
below it has one child per taxon below it. -/
theorem exists_card_two_mem_treeClusters (hN : N.IsPhylogenetic) (ht : ∀ e, ¬ N.IsHybridArc e)
    (hX : Fintype.card X = 4) (hdeg : ∀ v, v ≠ N.root → N.graph.outdegree v ≤ 2)
    (hroot : N.graph.outdegree N.root ≤ 3) : ∃ A ∈ treeClusters N, #A = 2 := by
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨u, hu, hmin⟩ := hwf.has_min {u | 2 ≤ #(treeCluster N u)} ⟨N.root, by
    show 2 ≤ #(treeCluster N N.root)
    rw [treeCluster_root hN, card_univ, hX]
    omega⟩
  have hu2 : 2 ≤ #(treeCluster N u) := hu
  -- the children of `u` have one taxon each below them
  have hchild : ∀ f, N.graph.source f = u → #(treeCluster N (N.graph.target f)) = 1 := by
    intro f hf
    have h1 := card_pos.2 (treeCluster_nonempty hN (N.graph.target f))
    by_contra hne
    exact hmin _ (show 2 ≤ #(treeCluster N (N.graph.target f)) by omega) (.single ⟨f, hf, rfl⟩)
  -- the taxa below `u` are those below its children
  have hunion : treeCluster N u =
      (univ.filter fun f => N.graph.source f = u).biUnion
      fun f => treeCluster N (N.graph.target f) := by
    ext x
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, mem_treeCluster]
    constructor
    · intro hx
      rcases Relation.ReflTransGen.cases_head hx with h | ⟨c, ⟨f, hf, rfl⟩, hc⟩
      · exfalso
        rw [h, treeCluster_leaf hN] at hu2
        simp at hu2
      · exact ⟨f, hf, hc⟩
    · rintro ⟨f, hf, hx⟩
      exact Relation.ReflTransGen.head ⟨f, hf, rfl⟩ hx
  have hcard : #(treeCluster N u) = N.graph.outdegree u := by
    rw [hunion, card_biUnion (fun f hf g hg hfg => disjoint_treeCluster hN ht
      ((mem_filter.1 hf).2.trans (mem_filter.1 hg).2.symm) hfg)]
    rw [sum_congr rfl fun f hf => hchild f (mem_filter.1 hf).2, sum_const, smul_eq_mul, mul_one]
    unfold DirectedMultigraph.outdegree
    rw [← Set.ncard_coe_finset]
    congr 1
    ext f
    simp
  by_cases hur : u = N.root
  · have : #(treeCluster N u) = 4 := by rw [hur, treeCluster_root hN, card_univ, hX]
    have := hroot
    rw [← hur] at this
    omega
  · have := hdeg u hur
    exact ⟨_, mem_treeClusters.2 ⟨u, rfl⟩, by omega⟩

end Tree

section Contract

variable [Fintype V] [Fintype E] {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q)
  (h1 : IsLevelOne Q.graph) {P : Set E → Prop}
include hQ h1

omit [Fintype V] [Fintype E] in
/-- A node of `Q` on no cycle has at most one parent: two parents would close a cycle. -/
theorem indegree_le_one_of_forall_notMem {w : V}
    (hw : ∀ C, IsCycle Q.graph C → w ∉ cycleNodes Q.graph C) : Q.graph.indegree w ≤ 1 := by
  have := hQ.1.finite_arcs
  by_contra h
  have h2 : Q.graph.indegree w = 2 := le_antisymm (hQ.indegree_le_two w) (by omega)
  obtain ⟨f₁, f₂, hne, hs⟩ := Set.ncard_eq_two.1 h2
  have h₁ : Q.graph.target f₁ = w := (Set.ext_iff.1 hs f₁).2 (Or.inl rfl)
  have h₂ : Q.graph.target f₂ = w := (Set.ext_iff.1 hs f₂).2 (Or.inr rfl)
  obtain ⟨C, hC, hf₁, -⟩ := exists_isCycle_of_target_eq hQ h1 hne (h₁.trans h₂.symm)
  exact hw C hC (h₁ ▸ target_mem_cycleNodes hf₁)

/-- The top of a cycle has at most one parent: its parents are off the cycle. -/
theorem indegree_cycleTop_le_one {C : Set E} (hC : IsCycle Q.graph C) :
    Q.graph.indegree (cycleTop Q C) ≤ 1 := by
  have := hQ.1.finite_arcs
  have hK := isContractible_cycleTop hQ h1 hC
  by_contra h
  have h2 : Q.graph.indegree (cycleTop Q C) = 2 := le_antisymm (hQ.indegree_le_two _) (by omega)
  obtain ⟨f₁, f₂, hne, hs⟩ := Set.ncard_eq_two.1 h2
  have h₁ : Q.graph.target f₁ = cycleTop Q C := (Set.ext_iff.1 hs f₁).2 (Or.inl rfl)
  have h₂ : Q.graph.target f₂ = cycleTop Q C := (Set.ext_iff.1 hs f₂).2 (Or.inr rfl)
  obtain ⟨D, hD, hf₁, -⟩ := exists_isCycle_of_target_eq hQ h1 hne (h₁.trans h₂.symm)
  have hDC := eq_of_mem_cycleNodes hQ h1 hD hC (h₁ ▸ target_mem_cycleNodes hf₁) hK.top_mem
  exact hK.top_entry f₁ h₁ (hDC ▸ hf₁)

/-- **With every cycle contracted, there is no hybrid arc.** -/
theorem contractSet_not_isHybridArc (hall : ∀ C, IsCycle Q.graph C → P C)
    (e : {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C}) : ¬ (contractRooted Q P).IsHybridArc e := by
  unfold IsHybridArc
  rw [contractSet_indegree hQ h1]
  induction (contractRooted Q P).graph.target e using Quot.ind with
  | mk w =>
    by_cases hw : InPCycle Q P w
    · obtain ⟨C, hC, hP, hwC⟩ := hw
      rw [contractSetRep_mk_of_mem hQ h1 hC hP hwC]
      have := indegree_cycleTop_le_one hQ h1 hC
      omega
    · rw [contractSetRep_mk_of_not hQ h1 hw]
      have := indegree_le_one_of_forall_notMem hQ h1 fun C hC hwC => hw ⟨C, hC, hall C hC, hwC⟩
      omega

/-- The node of a contracted cycle `C` through the root has `|C| - 1` children, and one off the root
has `|C| - 1` children too: with the cycles inducing cycles of size at most three, every node of the
contracted network has at most two children, but the root, which has at most three. -/
theorem contractSet_outdegree_le
    (hn : ∀ C, IsCycle Q.graph C → P C →
      C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0) ≤ 3)
    (W : Quot (RootedContractRel Q P)) :
    (contractRooted Q P).graph.outdegree W ≤
      if W = (contractRooted Q P).root then 3 else 2 := by
  induction W using Quot.ind with
  | mk w =>
    by_cases hw : InPCycle Q P w
    · obtain ⟨C, hC, hP, hwC⟩ := hw
      rw [contractSet_outdegree_of_mem hQ h1 hC hP hwC]
      have := hn C hC hP
      by_cases hr : Q.root ∈ cycleNodes Q.graph C
      · rw [ite_eq_left hr] at this
        split_ifs with hW
        · omega
        · exact absurd (Quot.sound ⟨C, hC, hP, hwC, hr⟩) hW
      · rw [ite_eq_right hr] at this
        split_ifs <;> omega
    · rw [contractSet_outdegree_of_not hQ h1 hw]
      have := hQ.outdegree_le_two w
      split_ifs <;> omega

end Contract

end Banos2019
