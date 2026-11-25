module

public import Banos2019.Quartet.Defs
public import Phylogenetics.Tree.Splice
public import Phylogenetics.NMSC.Induced
public import Banos2019.Quartet.SemidirectedCycles
public import Banos2019.Quartet.HybridGlue
public import Banos2019.Quartet.ReduceSpec
public import Banos2019.Quartet.DisjointNet
public import Banos2019.Quartet.ContractCompose
public import Banos2019.Quartet.QuartetLSA
public import Banos2019.Quartet.UnrootedIso
public import Banos2019.Quartet.ThreeTwoCherry
public import Banos2019.Quartet.DisjointTree
public import Banos2019.Quartet.RootedIsoUnrooted
public import Banos2019.Quartet.TreeUnrooted
public import Banos2019.Quartet.ReduceUnrooted
public import Banos2019.Quartet.ReduceUnrootedIso
public import Banos2019.Quartet.RootPlacement

/-!
# Computing quartet concordance factors (Baños 2019, Section 5)

An *LSA quartet network* (`IsLSAQuartet`) is a metric binary rooted level-1 network on four taxa whose
root is the LSA of its taxa: `Q⊕_abcd` for a network on more taxa, and its own `Q⊕` for itself. Its
concordance factors are `cf Q θ`, a function on the quartet trees.

* `lemma5`, `lemma6`: the cycles of `Q⁻`.
* `observation1`, `theorem2`.
* `lemma7`, `lemma8`, `corollary2`, `lemma9`, `lemma10`, `lemma11`: the reduction formulas.
* `corollary2Net`, `corollary2Net_spec`: the network `Q̃⊕` of Corollary 2, with its nodes of degree
  two suppressed, as an LSA quartet network for all parameters of `Q⊕`; `corollary2_step`: one step
  of Corollary 2.
* `proposition5`, `corollary3`: the concordance factors depend only on the unrooted network;
  `proposition5_aux`: the induction on the number of cycles, which applies the lemma of the type of a
  cycle to two networks with isomorphic unrooted networks and the induction hypothesis to the
  networks it produces (`nonempty_sdMetricIso_reduceNet_deleteArc`, `nonempty_sdMetricIso_contractNet`,
  `nonempty_sdMetricIso_disjointNet`); `cf_eq_of_forall_not_isCycle`: networks without cycles.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

/-- An *LSA quartet network* `(Q⊕, θ)`: a metric binary rooted level-1 network on four taxa whose root is
the LSA of the taxa. -/
structure IsLSAQuartet (Q : RootedNetwork V E X) (θ : MetricData E) : Prop where
  binary : IsBinaryRootedNetwork Q
  levelOne : IsLevelOne Q.graph
  isLSA : Q.IsLSANetwork
  card_taxa : Fintype.card X = 4
  metric : IsMetricNetwork Q θ

omit [Fintype V] in
theorem IsLSAQuartet.nontrivial {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) :
    Nontrivial X :=
  Fintype.one_lt_card_iff_nontrivial.mp (by rw [hQ.card_taxa]; norm_num)

/-- `Q⁻`, the unrooted network of an LSA quartet network. -/
abbrev IsLSAQuartet.unrooted {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ) :=
  Banos2019.unrooted Q hQ.binary hQ.nontrivial

/-- A cycle of `Q⁻` of type `n_k` is the image of the cycle `liftEdges D` of `Q⊕`, of type `n_k`:
its hybrid node is that of `Q⊕` (`isHybridNodeOf_semidirected_iff`), it has one edge more when it
passes through the root, and the taxa descending from its hybrid node are those below it
(`descendsFrom_semidirected_iff`). -/
theorem inducesCycleType_liftEdges {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {D : Set _} {n k : ℕ} (hD : IsCycleType hQ.unrooted D n k) :
    ∃ v, InducesCycleType Q (liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D) v n k := by
  obtain ⟨hcyc, hn, v', hv', hk⟩ := hD
  have hr := lsa_univ_eq_root hQ.binary.1 hQ.nontrivial hQ.isLSA
  obtain ⟨hvD, h2⟩ := (isHybridNodeOf_semidirected_iff _ _ _ hQ.binary hQ.levelOne hcyc v').1 hv'
  refine ⟨_, isCycle_liftEdges _ _ _ hcyc,
    (sdVert_mem_cycleNodes_liftEdges_iff _ _ _ D v').2 hvD, h2, ?_, ?_⟩
  · have h := card_cycleNodesOffRoot_liftEdges _ _ _ hr hcyc
    rw [card_cycleNodesOffRoot (isCycle_liftEdges _ _ _ hcyc)] at h
    omega
  · rw [← hk]
    congr 1
    ext x
    exact (descendsFrom_semidirected_iff _ _ _ v' h2 x).symm

/-- **The cycles of `Q⁻` are those of `Q⊕`** (Section 5, the paragraph before Lemma 5): a cycle of `Q⊕`
with hybrid node `v` induces an `n_k`-cycle of `Q⁻` exactly when its image is an `n_k`-cycle of `Q⁻`,
and every cycle of `Q⁻` is such an image. The edge of `Q⁻` merged at the root stands for both edges at
the root; the others are the edges of `Q⊕` (`liftEdges`, `exists_liftEdges_eq`). -/
theorem inducesCycleType_iff {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    (n k : ℕ) :
    (∃ C v, InducesCycleType Q C v n k) ↔ ∃ C, IsCycleType hQ.unrooted C n k := by
  have hr := lsa_univ_eq_root hQ.binary.1 hQ.nontrivial hQ.isLSA
  constructor
  · rintro ⟨C, v, hC⟩
    obtain ⟨D, hD, hDC⟩ := exists_liftEdges_eq _ _ _ hr hQ.binary hC.1
    have hvr : v ≠ Q.root := fun h => by
      have := hQ.binary.1.root_indegree
      rw [← h, hC.2.2.1] at this
      exact absurd this (by norm_num)
    obtain ⟨v', rfl⟩ := exists_sdVert_of_ne hQ.binary.1 hQ.nontrivial hr hvr
    have hvD := (sdVert_mem_cycleNodes_liftEdges_iff _ _ _ D v').1 (hDC ▸ hC.2.1)
    refine ⟨D, hD, ?_, v', (isHybridNodeOf_semidirected_iff _ _ _ hQ.binary hQ.levelOne hD v').2
      ⟨hvD, hC.2.2.1⟩, ?_⟩
    · have h := card_cycleNodesOffRoot_liftEdges _ _ _ hr hD
      rw [hDC, card_cycleNodesOffRoot hC.1, hC.2.2.2.1] at h
      exact h.symm
    · rw [← hC.2.2.2.2]
      congr 1
      ext x
      exact descendsFrom_semidirected_iff _ _ _ v' hC.2.2.1 x
  · rintro ⟨D, hD⟩
    obtain ⟨v, hv⟩ := inducesCycleType_liftEdges hQ hD
    exact ⟨_, v, hv⟩

/-- **Lemma 5** (`lem:numberofcycles`): `Q⁻` has no `k`-cycle for `k ≥ 5`, at most one 4-cycle, and then
no 3-cycle, and at most two 3-cycles.

The paper's proof, on the blocks of the cycles (`nodeBlock`), read on the cycles of `Q⊕` that the
cycles of `Q⁻` come from (`liftEdges`): a cycle of `Q⁻` of size `k` has `k` pairwise disjoint nonempty
blocks (`card_cycleNodesOffRoot_le`); two cycles of sizes `k₁`, `k₂` keep `k₁ + k₂ - 2` of them, all
disjoint (`card_add_card_le_of_cycles`). For three cycles the paper counts `k₁ + k₂ + k₃ - 3` blocks;
the cycle between the two others loses two, so the count is `k₁ + k₂ + k₃ - 4`
(`card_add_card_add_card_le_of_cycles`), which is still more than four for three 3-cycles. -/
theorem lemma5 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ) :
    (∀ k ≥ 5, ∀ C, IsCycle hQ.unrooted.graph C → C.ncard ≠ k) ∧
      {C | IsCycle hQ.unrooted.graph C ∧ C.ncard = 4}.ncard ≤ 1 ∧
      ((∃ C, IsCycle hQ.unrooted.graph C ∧ C.ncard = 4) →
        ∀ C, IsCycle hQ.unrooted.graph C → C.ncard ≠ 3) ∧
      {C | IsCycle hQ.unrooted.graph C ∧ C.ncard = 3}.ncard ≤ 2 := by
  have hr := lsa_univ_eq_root hQ.binary.1 hQ.nontrivial hQ.isLSA
  have hX := hQ.card_taxa
  have hsize : ∀ D, IsCycle hQ.unrooted.graph D → D.ncard ≤ 4 := fun D hD => by
    rw [← card_cycleNodesOffRoot_liftEdges _ _ _ hr hD, ← hX]
    exact card_cycleNodesOffRoot_le hQ.binary hQ.levelOne hQ.isLSA (isCycle_liftEdges _ _ _ hD)
  have htwo : ∀ D D', IsCycle hQ.unrooted.graph D → IsCycle hQ.unrooted.graph D' → D ≠ D' →
      D.ncard + D'.ncard ≤ 6 := fun D D' hD hD' hne => by
    have h := card_add_card_le_of_cycles hQ.binary hQ.levelOne hQ.isLSA (isCycle_liftEdges _ _ _ hD)
      (isCycle_liftEdges _ _ _ hD') fun h => hne (liftEdges_injective _ _ _ h)
    rw [card_cycleNodesOffRoot_liftEdges _ _ _ hr hD, card_cycleNodesOffRoot_liftEdges _ _ _ hr hD',
      hX] at h
    exact h
  refine ⟨fun k hk D hD h => by have := hsize D hD; omega, ?_, ?_, ?_⟩
  · refine (Set.ncard_le_one (Set.toFinite _)).2 fun a ha b hb => ?_
    by_contra hne
    have := htwo a b ha.1 hb.1 hne
    rw [ha.2, hb.2] at this
    omega
  · rintro ⟨D₄, hD₄, h4⟩ D hD h3
    have hne : D₄ ≠ D := by
      rintro rfl
      omega
    have := htwo _ _ hD₄ hD hne
    omega
  · by_contra h
    push Not at h
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 h
    have h3 := card_add_card_add_card_le_of_cycles hQ.binary hQ.levelOne hQ.isLSA
      (isCycle_liftEdges _ _ _ ha.1) (isCycle_liftEdges _ _ _ hb.1) (isCycle_liftEdges _ _ _ hc.1)
      (fun h => hab (liftEdges_injective _ _ _ h)) (fun h => hac (liftEdges_injective _ _ _ h))
      (fun h => hbc (liftEdges_injective _ _ _ h))
    rw [card_cycleNodesOffRoot_liftEdges _ _ _ hr ha.1, card_cycleNodesOffRoot_liftEdges _ _ _ hr hb.1,
      card_cycleNodesOffRoot_liftEdges _ _ _ hr hc.1, ha.2, hb.2, hc.2, hX] at h3
    omega

/-- **Lemma 6** (`lem::no2 3_2`): `Q⁻` does not have two `3₂`-cycles, nor a `2₂`-cycle and a
`4₁`-cycle.

The paper's proof, on the cycles of `Q⊕` that the cycles of `Q⁻` come from (`inducesCycleType_liftEdges`):
the two blocks of a `3₂`-cycle away from another `3₂`-cycle lie in the block of the node toward it,
which is therefore the hybrid block, and each hybrid node would be below the other
(`eq_of_inducesCycleType_three_two_of_card`); the blocks of a `4`-cycle are singletons, and a block of
two taxa of the `2₂`-cycle would lie in one of them (`not_inducesCycleType_two_two_of_four`). -/
theorem lemma6 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ) :
    (∀ C C', IsCycleType hQ.unrooted C 3 2 → IsCycleType hQ.unrooted C' 3 2 → C = C') ∧
      ¬ ((∃ C, IsCycleType hQ.unrooted C 2 2) ∧ ∃ C, IsCycleType hQ.unrooted C 4 1) := by
  refine ⟨fun D D' hD hD' => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := inducesCycleType_liftEdges hQ hD
    obtain ⟨v', hv'⟩ := inducesCycleType_liftEdges hQ hD'
    exact liftEdges_injective _ _ _ (eq_of_inducesCycleType_three_two_of_card hQ.binary
      hQ.levelOne hQ.isLSA hQ.card_taxa hv hv')
  · rintro ⟨⟨D, hD⟩, ⟨D', hD'⟩⟩
    obtain ⟨v, hv⟩ := inducesCycleType_liftEdges hQ hD
    obtain ⟨v', hv'⟩ := inducesCycleType_liftEdges hQ hD'
    exact not_inducesCycleType_two_two_of_four hQ.binary hQ.levelOne hQ.isLSA hQ.card_taxa hv hv'

omit [Fintype V] [Fintype E] in
/-- **Observation 1** (`obs:quartetcoales`): the first coalescent event of a gene tree on four taxa
determines its unrooted topology. The two lineages it joins form a cluster `A` with two elements of the
rooted binary gene tree, and the unrooted gene tree displays `A | Aᶜ`: a fact about rooted binary trees
on four taxa, which is what the observation rests on. -/
theorem observation1 (hX : Fintype.card X = 4) {G : Finset (Finset X)} (hG : IsBinaryHierarchy G)
    {A : Finset X} (hA : A ∈ G) (hA2 : #A = 2) :
    ∃ q : QuartetTree X, q.val = {A, Aᶜ} ∧ Displays (unroot G) q := by
  have hc : #Aᶜ = 2 := by rw [card_compl, hX, hA2]
  have hne : A ≠ Aᶜ := fun h => by
    obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < #A)
    exact (mem_compl.1 (h ▸ hx)) hx
  have hq : IsQuartetTree ({A, Aᶜ} : Finset (Finset X)) := by
    refine ⟨card_pair hne, ?_, ?_⟩
    · intro B hB
      rcases mem_insert.1 hB with rfl | hB
      · exact hA2
      · rw [mem_singleton.1 hB]; exact hc
    · intro B hB C hC hBC
      rcases mem_insert.1 hB with rfl | hB <;> rcases mem_insert.1 hC with rfl | hC
      · exact absurd rfl hBC
      · rw [mem_singleton.1 hC]; exact disjoint_compl_right
      · rw [mem_singleton.1 hB]; exact disjoint_compl_left
      · rw [mem_singleton.1 hB, mem_singleton.1 hC] at hBC; exact absurd rfl hBC
  refine ⟨⟨_, hq⟩, rfl, A, ?_, ?_⟩
  · refine mem_unroot.2 (Or.inl ⟨hA, fun h => ?_⟩)
    rw [h, card_univ, hX] at hA2
    omega
  · have ht : QuartetTree.taxa (⟨_, hq⟩ : QuartetTree X) = univ := by
      unfold QuartetTree.taxa
      simp [sup_insert, sup_singleton]
    rw [ht, inter_univ]
    exact mem_insert_self _ _

/-- **Theorem 2** (`thm::MRCA`): the concordance factors of four taxa `s` under the network
multispecies coalescent on a level-1 rooted metric network are those of the LSA network `Q⊕_s`.

This is `Phylogenetics.NMSC.nmscCF_inducedNetwork`. As in the paper, by the Markov property at the LSA
of `s` (`NMSC.sum_sum_mul_injDist_atInj`) the process is a mixture over the forest of the four lineages
arriving there, and a forest with a cluster of two lineages decides the quartet tree (Observation 1,
as `NMSC.cherryMass_of_mem`). With four lineages at the LSA, the paper conditions on the two rooted
shapes of the gene tree (caterpillar and balanced), uses exchangeability of the lineages within each
shape, and notes that four taxa have a single unrooted shape (TeX 592–594). The library uses the same
exchangeability without splitting by rooted shape: the process above the LSA is invariant under the
transpositions of the four lineages, so the three quartet trees are equally likely
(`NMSC.cherryMass_atInj`), whatever lies above the LSA. The library proves it for every phylogenetic
network with valid parameters and every inheritance correlation in `[0, 1]`; the level-1 hypothesis is
not needed. -/
theorem theorem2 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    {θ : MetricData E} (hθ : IsMetricNetwork N θ) {s : Finset X} (hs : #s = 4)
    (q : QuartetTree (s : Set X)) :
    nmscCF (quartetLSA N hN.1 s hs)
        (inducedMetric hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty θ)
        0 q =
      nmscCF N θ 0 (QuartetTree.map Subtype.val_injective q) := by
  convert NMSC.nmscCF_inducedNetwork hN.1 hθ.1 ⟨le_refl 0, zero_le_one⟩ hs _ q

section Reduction

variable {Q : RootedNetwork V E X} {θ : MetricData E} {C : Set E} {v : V}

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The arcs out of a vertex of outdegree two are two given distinct ones. -/
theorem mem_pair_of_source_of_outdegree_eq_two {G : DirectedMultigraph V E} {u : V}
    (h2 : G.outdegree u = 2) {a b : E} (hne : a ≠ b) (ha : G.source a = u) (hb : G.source b = u)
    (f : E) (hf : G.source f = u) : f = a ∨ f = b := by
  obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 h2
  have m : ∀ g, G.source g = u → g = x ∨ g = y := fun g hg => by
    have : g ∈ {e | G.source e = u} := hg
    rw [hs] at this
    simpa using this
  rcases m a ha with r1 | r1 <;> rcases m b hb with r2 | r2 <;> rcases m f hf with r3 | r3 <;>
    subst_vars <;> simp_all

/-- Lemma 7 when the root is not on the cycle: `C` is two edges `a, b` from the top `t` to `v`, and
`CF(Q⊕ ∖ b) = CF(Q₀⊕)`. Both are read from the part above `t`, with the single lineage of the taxon
below `v` at `t` (`cf_eq_of_one_below`): only that lineage is on the edges between `t` and `v`. -/
theorem cf_deleteArc_eq_contract_of_root_notMem (hQ : IsLSAQuartet Q θ) (hcyc : IsCycle Q.graph C)
    (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2)
    (hroot : Q.root ∉ cycleNodes Q.graph C) (hcard : C.ncard = 2) {d : X}
    (hd : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = d) {a b : E} (hab : a ≠ b)
    (ha : Q.graph.target a = v) (hb : Q.graph.target b = v) (q : QuartetTree X) :
    cf (deleteArc Q b) (deleteArcMetric Q b θ) q =
      cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) q := by
  have hN := hQ.binary.1
  have hθ := hQ.metric
  have : Finite E := hN.finite_arcs
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ.binary hQ.levelOne hcyc hv h2
  have haC := mem_of_target_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 ha
  have hbC := mem_of_target_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 hb
  have htv : t ≠ v := fun h => hK.top_entry a (ha.trans h.symm) haC
  -- the nodes of `C` are `t` and `v`, and `a, b` leave `t`
  have hS : cycleNodes Q.graph C = {t, v} := by
    refine (Set.eq_of_subset_of_ncard_le (Set.insert_subset hK.top_mem
      (Set.singleton_subset_iff.2 hv)) ?_ (Set.toFinite _)).symm
    rw [ncard_cycleNodes hcyc, hcard, Set.ncard_pair htv]
  have hsrc : ∀ e ∈ C, Q.graph.target e = v → Q.graph.source e = t := by
    intro e he het
    have hs := source_mem_cycleNodes (G := Q.graph) he
    rw [hS] at hs
    rcases hs with hs | hs
    · exact hs
    · exact absurd ((Set.mem_singleton_iff.1 hs).trans het.symm)
        (source_ne_target_of_binary hQ.binary e)
  have hat := hsrc a haC ha
  have hbt := hsrc b hbC hb
  have htr : t ≠ Q.root := fun h => hroot (h ▸ hK.top_mem)
  -- the parent arc `p` of `t`
  obtain ⟨p, hp⟩ := (Q.graph.one_le_indegree_iff t).1 (hN.nonroot_indegree t htr)
  have hind1 : Q.graph.indegree t ≤ 1 :=
    indegree_le_one_of_mem hQ.binary hQ.levelOne hcyc hv h2 hK.top_mem htv
  have huniq : ∀ g, Q.graph.target g = t → g = p := fun g hg => by
    by_contra hne
    have := two_le_indegree_of_two_targets hQ.binary hne hg hp
    omega
  -- the children of `t` are `v`
  have hout : Q.graph.outdegree t = 2 := by
    have h3 := hQ.binary.2.2 t htr (fun h0 => (Q.graph.outdegree_eq_zero_iff _).1 h0 a hat)
    have h1 : Q.graph.indegree t = 1 := le_antisymm hind1 (hN.nonroot_indegree t htr)
    omega
  have hchild : ∀ w, Q.graph.Reaches t w → w = t ∨ Q.graph.Reaches v w := by
    intro w hw
    rcases Relation.ReflTransGen.cases_head hw with h | ⟨x, ⟨g, hg, rfl⟩, hx⟩
    · exact Or.inl h.symm
    · rcases mem_pair_of_source_of_outdegree_eq_two hout hab hat hbt g hg with rfl | rfl
      · exact Or.inr (ha ▸ hx)
      · exact Or.inr (hb ▸ hx)
  have htvr : Q.graph.Reaches t v := .single ⟨a, hat, ha⟩
  -- `t` is a cut vertex
  have hc : IsCut Q t := by
    refine ⟨fun hr => ?_, fun e he hne => ?_⟩
    · obtain ⟨g, -, hg⟩ := exists_arc_enter (p := fun w => w = Q.root) hr htr rfl
      exact (Q.graph.indegree_eq_zero_iff _ |>.1 hN.root_indegree) g hg
    · rcases hchild _ he with h | h
      · exact absurd h hne
      · by_cases hev : Q.graph.target e = v
        · rcases mem_pair_of_target_of_indegree_eq_two h2 hab ha hb e hev with rfl | rfl
          · rw [hat]
            exact .refl
          · rw [hbt]
            exact .refl
        · exact htvr.trans (reaches_source_of_below_hybrid hQ.binary hQ.levelOne h2 h hev)
  have hdt : ∀ x, Q.graph.Reaches t (Q.leaf x) ↔ x = d := by
    intro x
    rw [← hd x]
    constructor
    · intro h
      rcases hchild _ h with h | h
      · exact absurd h (leaf_ne_source hN x a |>.trans_eq hat |> fun h' => h')
      · exact h
    · exact fun h => htvr.trans h
  -- the network without `b`
  have hs_ab : Q.graph.source a = Q.graph.source b := hat.trans hbt.symm
  have ht_ab : Q.graph.target a = Q.graph.target b := ha.trans hb.symm
  have hN₁ := isPhylogenetic_deleteArc hN hab ht_ab hab hs_ab
  have hθ₁ : IsMetricNetwork (deleteArc Q b) (deleteArcMetric Q b θ) :=
    ⟨isMetric_deleteArc hN hθ.1 hθ.2 hab ht_ab (hb ▸ h2), fun e => hθ.2 e.1⟩
  have hc₁ := isCut_deleteArc_of_parallel hab hs_ab ht_ab hc
  have hpb : p ≠ b := fun h => htv (hp.symm.trans (h ▸ hb))
  have huniq₁ : ∀ g : {e // e ≠ b}, (deleteArc Q b).graph.target g = t → g = ⟨p, hpb⟩ :=
    fun g hg => Subtype.ext (huniq g.1 hg)
  have hd₁ : ∀ x, (deleteArc Q b).graph.Reaches t ((deleteArc Q b).leaf x) ↔ x = d := fun x => by
    rw [← hdt x]
    exact reaches_deleteArc_of_parallel hab hs_ab ht_ab _ _
  -- the contracted network
  have hN₀ := hK.isPhylogenetic hN
  have hθ₀ := hK.isMetric hθ.1
  have hc₀ := hK.isCut_top hc
  let p₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'} :=
    ⟨p, fun C' _ hC' => hC' ▸ hK.top_entry p hp⟩
  have hpt₀ : (contractRooted Q (· = C)).graph.target p₀ = Quot.mk _ t := by
    change Quot.mk _ (Q.graph.target p) = _
    rw [hp]
  have huniq₀ : ∀ g, (contractRooted Q (· = C)).graph.target g = Quot.mk _ t → g = p₀ := by
    intro g hg
    have hgt : Q.graph.target g.1 = t := by
      have := (mk_eq_mk_iff hK.cycle).1 hg
      rcases this with h | ⟨h, -⟩
      · exact h
      · exact hK.entry g.1 (g.2 C hK.cycle rfl) h
    exact Subtype.ext (huniq g.1 hgt)
  have hd₀ : ∀ x, (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ t)
      ((contractRooted Q (· = C)).leaf x) ↔ x = d := by
    intro x
    rw [hK.reaches_top_iff, ← hdt x]
    change Q.graph.Reaches t (hK.rep (Quot.mk _ (Q.leaf x))) ↔ _
    rw [hK.rep_mk_of_notMem (hK.leaf_notMem x)]
  rw [cf_eq_of_one_below hN₁ hθ₁.1 hQ.card_taxa hc₁ (p := ⟨p, hpb⟩) hp huniq₁ hd₁,
    cf_eq_of_one_below hN₀ hθ₀ hQ.card_taxa hc₀ hpt₀ huniq₀ hd₀]
  refine sum_congr rfl fun H _ => ?_
  split_ifs
  · refine sum_congr rfl fun F _ => ?_
    congr 1
    refine sum_congr rfl fun t' _ => ?_
    rw [upperLaw_deleteArc_of_parallel hN hc hab hs_ab ht_ab (hb ▸ htvr) hp huniq hN₁
        (p' := ⟨p, hpb⟩) rfl hp huniq₁,
      hK.upperLaw_contract hN hc hp huniq hN₀ rfl hpt₀ huniq₀]
    rfl
  · rfl

omit [Fintype X] in
/-- The shape of a cycle through the root with three edges: the root `r`, the hybrid node `v` and a
node `w`, with an edge from `r` to `w`; one hybrid edge of `v` leaves `r` and the other `w`, and the
other child arc `g` of `w` is off the cycle. -/
theorem shape_of_root_mem (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    (hcyc : IsCycle Q.graph C) (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2)
    (hroot : Q.root ∈ cycleNodes Q.graph C) (hcard : C.ncard = 3) {a b : E} (hab : a ≠ b)
    (ha : Q.graph.target a = v) (hb : Q.graph.target b = v) :
    ∃ w f g, w ≠ v ∧ w ≠ Q.root ∧ cycleNodes Q.graph C = {Q.root, v, w} ∧
      Q.graph.source f = Q.root ∧ Q.graph.target f = w ∧ (∀ e, Q.graph.target e = w → e = f) ∧
      Q.graph.source g = w ∧ g ∉ C ∧
      ((Q.graph.source a = Q.root ∧ Q.graph.source b = w) ∨
        (Q.graph.source a = w ∧ Q.graph.source b = Q.root)) ∧
      (∀ e, Q.graph.source e = Q.root → Q.graph.target e = v ∨ Q.graph.target e = w) ∧
      (∀ e, Q.graph.source e = w → Q.graph.target e = v ∨ e = g) := by
  have hN := hQ.1
  have : Finite E := hN.finite_arcs
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ h1 hcyc hv h2
  have hloop := source_ne_target_of_binary hQ
  have hnoin : ∀ e, Q.graph.target e ≠ Q.root := fun e =>
    (Q.graph.indegree_eq_zero_iff _).1 hN.root_indegree e
  have hrv : Q.root ≠ v := fun h => hnoin a (ha.trans h.symm)
  have haC := mem_of_target_eq_hybrid hQ h1 hcyc hv h2 ha
  have hbC := mem_of_target_eq_hybrid hQ h1 hcyc hv h2 hb
  have hpar : ∀ e, Q.graph.target e = v → e = a ∨ e = b := fun e he =>
    mem_pair_of_target_of_indegree_eq_two h2 hab ha hb e he
  have hvout : ∀ e, Q.graph.source e = v → e ∉ C := fun e he =>
    notMem_of_source_eq_hybrid hQ h1 hcyc hv h2 he
  -- the out-arcs of the root are edges of `C`
  have hrout : Q.graph.outdegree Q.root = 2 := hQ.2.1
  have hrC : ∀ e, Q.graph.source e = Q.root → e ∈ C := by
    intro e he
    have hinc := hcyc.ncard_incident hloop hroot
    have hsub : {f | f ∈ C ∧ (Q.graph.source f = Q.root ∨ Q.graph.target f = Q.root)} ⊆
        {f | Q.graph.source f = Q.root} := fun f hf => hf.2.resolve_right (hnoin f)
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      unfold DirectedMultigraph.outdegree at hrout
      rw [hinc, hrout]) (Set.toFinite _)
    have : e ∈ {f | f ∈ C ∧ (Q.graph.source f = Q.root ∨ Q.graph.target f = Q.root)} :=
      heq ▸ he
    exact this.1
  -- one hybrid edge of `v` does not leave the root
  have hex : ∃ e, (e = a ∨ e = b) ∧ Q.graph.source e ≠ Q.root := by
    by_contra hno
    push Not at hno
    have hsa := hno a (Or.inl rfl)
    have hsb := hno b (Or.inr rfl)
    -- the third edge of `C`
    have hab2 : ({a, b} : Set E).ncard = 2 := Set.ncard_pair hab
    obtain ⟨f, hfC, hfab⟩ : ∃ f ∈ C, f ∉ ({a, b} : Set E) := by
      by_contra hno'
      push Not at hno'
      have := Set.ncard_le_ncard (fun f hf => hno' f hf) (Set.toFinite ({a, b} : Set E))
      omega
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hfab
    have hfv : Q.graph.target f ≠ v := fun h => (hpar f h).elim hfab.1 hfab.2
    have hfr : Q.graph.source f ≠ Q.root := fun h => by
      rcases mem_pair_of_source_of_outdegree_eq_two hrout hab hsa hsb f h with h' | h'
      · exact hfab.1 h'
      · exact hfab.2 h'
    have hfsv : Q.graph.source f ≠ v := fun h => hvout f h hfC
    -- both ends of `f` are the third node
    have hS3 : (cycleNodes Q.graph C).ncard = 3 := (ncard_cycleNodes hcyc).trans hcard
    have hsub : ({Q.root, v, Q.graph.source f} : Set V) ⊆ cycleNodes Q.graph C := by
      intro x hx
      rcases hx with rfl | rfl | hx
      · exact hroot
      · exact hv
      · rw [Set.mem_singleton_iff.1 hx]; exact source_mem_cycleNodes hfC
    have hne3 : ({Q.root, v, Q.graph.source f} : Set V).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hrv, Ne.symm hfr]) (Set.toFinite _),
        Set.ncard_pair (Ne.symm hfsv)]
    have heqS := Set.eq_of_subset_of_ncard_le hsub (by rw [hS3, hne3]) (Set.toFinite _)
    have ht := target_mem_cycleNodes (G := Q.graph) hfC
    rw [← heqS] at ht
    rcases ht with ht | ht | ht
    · exact hnoin f ht
    · exact hfv ht
    · exact hloop f (Set.mem_singleton_iff.1 ht).symm
  obtain ⟨e₀, he₀ab, he₀r⟩ := hex
  have he₀v : Q.graph.target e₀ = v := he₀ab.elim (fun h => h ▸ ha) fun h => h ▸ hb
  have he₀C : e₀ ∈ C := mem_of_target_eq_hybrid hQ h1 hcyc hv h2 he₀v
  have hwS : Q.graph.source e₀ ∈ cycleNodes Q.graph C := source_mem_cycleNodes he₀C
  have hwv : Q.graph.source e₀ ≠ v := fun h => hloop e₀ (h.trans he₀v.symm)
  have hS : cycleNodes Q.graph C = {Q.root, v, Q.graph.source e₀} := by
    have hsub : ({Q.root, v, Q.graph.source e₀} : Set V) ⊆ cycleNodes Q.graph C := by
      intro x hx
      rcases hx with rfl | rfl | hx
      · exact hroot
      · exact hv
      · rw [Set.mem_singleton_iff.1 hx]; exact hwS
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
    rw [ncard_cycleNodes hcyc, hcard, Set.ncard_insert_of_notMem (by simp [hrv, Ne.symm he₀r])
      (Set.toFinite _), Set.ncard_pair (Ne.symm hwv)]
  have htr : t = Q.root := by
    rcases Relation.ReflTransGen.cases_tail (hK.top_reaches _ hroot) with h | ⟨c, -, e, -, he⟩
    · exact h.symm
    · exact absurd he (hnoin e)
  -- the parent arc of `w` leaves the root
  obtain ⟨f, hf⟩ := (Q.graph.one_le_indegree_iff _).1 (hN.nonroot_indegree _ he₀r)
  have hfC : f ∈ C := by
    by_contra hfC
    exact he₀r ((hf.symm.trans (hK.entry f hfC (hf ▸ hwS))).trans htr)
  have hfs : Q.graph.source f = Q.root := by
    have hs := source_mem_cycleNodes (G := Q.graph) hfC
    rw [hS] at hs
    rcases hs with hs | hs | hs
    · exact hs
    · exact absurd hfC (hvout f hs)
    · exact absurd ((Set.mem_singleton_iff.1 hs).trans hf.symm) (hloop f)
  have hind1 : Q.graph.indegree (Q.graph.source e₀) ≤ 1 :=
    indegree_le_one_of_mem hQ h1 hcyc hv h2 hwS hwv
  have hfuniq : ∀ e, Q.graph.target e = Q.graph.source e₀ → e = f := fun e he => by
    by_contra hne
    have := two_le_indegree_of_two_targets hQ hne he hf
    omega
  -- the other child arc `g` of `w`
  have hwout : Q.graph.outdegree (Q.graph.source e₀) = 2 := by
    have h3 := hQ.2.2 _ he₀r (fun h0 => (Q.graph.outdegree_eq_zero_iff _).1 h0 e₀ rfl)
    have : Q.graph.indegree (Q.graph.source e₀) = 1 := le_antisymm hind1 (hN.nonroot_indegree _ he₀r)
    omega
  obtain ⟨g, hgs, hge₀⟩ : ∃ g, Q.graph.source g = Q.graph.source e₀ ∧ g ≠ e₀ := by
    obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.1 hwout
    have hx : Q.graph.source x = Q.graph.source e₀ := (Set.ext_iff.1 hxy' x).2 (Or.inl rfl)
    have hy : Q.graph.source y = Q.graph.source e₀ := (Set.ext_iff.1 hxy' y).2 (Or.inr rfl)
    by_cases hxe : x = e₀
    · exact ⟨y, hy, fun h => hxy (hxe.trans h.symm)⟩
    · exact ⟨x, hx, hxe⟩
  have hgC : g ∉ C := by
    intro hgC
    have hinc := hcyc.ncard_incident hloop hwS
    have hsub : ({f, e₀, g} : Set E) ⊆
        {e | e ∈ C ∧ (Q.graph.source e = Q.graph.source e₀ ∨ Q.graph.target e = Q.graph.source e₀)} := by
      intro x hx
      rcases hx with rfl | rfl | hx
      · exact ⟨hfC, Or.inr hf⟩
      · exact ⟨he₀C, Or.inl rfl⟩
      · rw [Set.mem_singleton_iff.1 hx]; exact ⟨hgC, Or.inl hgs⟩
    have hfe₀ : f ≠ e₀ := fun h => by
      subst h
      exact hwv (hf.symm.trans he₀v)
    have hfg : f ≠ g := fun h => he₀r (hgs.symm.trans (h ▸ hfs))
    have h3 : ({f, e₀, g} : Set E).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hfe₀, hfg]) (Set.toFinite _),
        Set.ncard_pair (Ne.symm hge₀)]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hother : ∀ e, (e = a ∨ e = b) → e ≠ e₀ → Q.graph.source e = Q.root := by
    intro e he hne
    have hev : Q.graph.target e = v := he.elim (fun h => h ▸ ha) fun h => h ▸ hb
    have heC : e ∈ C := mem_of_target_eq_hybrid hQ h1 hcyc hv h2 hev
    have hs := source_mem_cycleNodes (G := Q.graph) heC
    rw [hS] at hs
    rcases hs with hs | hs | hs
    · exact hs
    · exact absurd (hs.trans hev.symm) (hloop e)
    · rcases mem_pair_of_source_of_outdegree_eq_two hwout (Ne.symm hge₀) rfl hgs e
        (Set.mem_singleton_iff.1 hs) with h | h
      · exact absurd h hne
      · exact absurd (h ▸ heC) hgC
  refine ⟨Q.graph.source e₀, f, g, hwv, he₀r, hS, hfs, hf, hfuniq, hgs, hgC, ?_, fun e he => ?_,
    fun e he => ?_⟩
  · rcases he₀ab with rfl | rfl
    · exact Or.inr ⟨rfl, hother b (Or.inr rfl) (Ne.symm hab)⟩
    · exact Or.inl ⟨hother a (Or.inl rfl) hab, rfl⟩
  · have ht := target_mem_cycleNodes (G := Q.graph) (hrC e he)
    rw [hS] at ht
    rcases ht with ht | ht | ht
    · exact absurd ht (hnoin e)
    · exact Or.inl ht
    · exact Or.inr (Set.mem_singleton_iff.1 ht)
  · rcases mem_pair_of_source_of_outdegree_eq_two hwout (Ne.symm hge₀) rfl hgs e he with h | h
    · exact Or.inl (h ▸ he₀v)
    · exact Or.inr h

/-- Lemma 7 when the root `r` is on the cycle: with `w` the third node of `C` (the paper's `u`) and `y`
the other child of `w`, the three taxa other than the taxon `d` below `v` are below `y`, and
`CF(Q⊕ ∖ b) = CF(Q₀⊕)`. The two networks share the law of the forest at the top of the edge `g` above
`y` (`jointCF_eq_sum_arc`), and the proof conditions on that forest, as the paper conditions on `K'`.
If two of the three lineages have coalesced (`K' = 1`), their cluster decides the quartet tree in both
networks (`NMSC.cherryMass_of_mem`). If not (`K' = 0`), the lineage of `d` goes up unchanged to the
source of its hybrid edge in `Q⊕ ∖ b`, and to the contracted root in `Q₀⊕`
(`cherryMass_liftInj_single`), and the process is the multispecies coalescent on a four-taxon species
tree: in `Q⊕ ∖ b`, the tree `((a,b,c):ℓ,d)`, with `ℓ` the length of the edge from `r` to `w`, if its
hybrid edge leaves `r`, and the star tree if it leaves `w` (`cherryMass_rootArc_eq_quartetProb_erase`,
`cherryMass_rootArc_eq_quartetProb_univ`); in `Q₀⊕`, the star tree
(`cherryMass_atRoot_eq_quartetProb_univ`). These trees have the same unrooted metric tree, and the root
placement does not matter (`pub:rootplace`, `quartetProb_cladeSpeciesTree_erase`), which Allman,
Degnan, Rhodes 2011 prove (Theorem 9 and Proposition 11). For this step the paper cites its Proposition
4, taken from that source, which as printed states identifiability (see `lemma7`). -/
theorem cf_deleteArc_eq_contract_of_root_mem (hQ : IsLSAQuartet Q θ) (hcyc : IsCycle Q.graph C)
    (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2)
    (hroot : Q.root ∈ cycleNodes Q.graph C) (hcard : C.ncard = 3) {d : X}
    (hd : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = d) {a b : E} (hab : a ≠ b)
    (ha : Q.graph.target a = v) (hb : Q.graph.target b = v) (q : QuartetTree X) :
    cf (deleteArc Q b) (deleteArcMetric Q b θ) q =
      cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) q := by
  have hN := hQ.binary.1
  have hθ := hQ.metric
  have : Finite E := hN.finite_arcs
  obtain ⟨w, f, g, hwv, hwr, hS, hfs, hft, hfu, hgs, hgC, hab', hrout, hwout⟩ :=
    shape_of_root_mem hQ.binary hQ.levelOne hcyc hv h2 hroot hcard hab ha hb
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ.binary hQ.levelOne hcyc hv h2
  have hnoin : ∀ e, Q.graph.target e ≠ Q.root := fun e =>
    (Q.graph.indegree_eq_zero_iff _).1 hN.root_indegree e
  set y := Q.graph.target g with hy
  have hwy : Q.graph.Reaches w y := .single ⟨g, hgs, rfl⟩
  have hsrc_v : ∀ e, Q.graph.target e = v → Q.graph.source e = Q.root ∨ Q.graph.source e = w := by
    intro e he
    rcases mem_pair_of_target_of_indegree_eq_two h2 hab ha hb e he with rfl | rfl <;> rcases hab' with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact Or.inr h.2
    · exact Or.inl h.2
  -- every vertex is the root, `w`, below `v` or below `y`
  have hpart : ∀ x, x = Q.root ∨ x = w ∨ Q.graph.Reaches v x ∨ Q.graph.Reaches y x := by
    intro x
    rcases Relation.ReflTransGen.cases_head (hN.root_reaches x) with h | ⟨z, ⟨e, he, rfl⟩, hz⟩
    · exact Or.inl h.symm
    · rcases hrout e he with h | h
      · exact Or.inr (Or.inr (Or.inl (h ▸ hz)))
      · rw [h] at hz
        rcases Relation.ReflTransGen.cases_head hz with h' | ⟨z', ⟨e', he', rfl⟩, hz'⟩
        · exact Or.inr (Or.inl h'.symm)
        · rcases hwout e' he' with h'' | h''
          · exact Or.inr (Or.inr (Or.inl (h'' ▸ hz')))
          · subst h''
            exact Or.inr (Or.inr (Or.inr hz'))
  -- what is not below `y`
  have hyr : ¬ Q.graph.Reaches y Q.root := fun h => by
    rcases Relation.ReflTransGen.cases_tail h with h' | ⟨c, -, e, -, he⟩
    · exact hnoin g h'.symm
    · exact hnoin e he
  have hyw : ¬ Q.graph.Reaches y w := fun h => hN.acyclic w (Relation.TransGen.head' ⟨g, hgs, rfl⟩ h)
  have hyv : ¬ Q.graph.Reaches y v := fun h => by
    rcases Relation.ReflTransGen.cases_tail h with h' | ⟨c, hc, e, rfl, he⟩
    · exact hgC (mem_of_target_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 h'.symm)
    · rcases hsrc_v e he with h'' | h''
      · exact hyr (h'' ▸ hc)
      · exact hyw (h'' ▸ hc)
  have hwvr : Q.graph.Adj w v := by
    rcases hab' with h | h
    · exact ⟨b, h.2, hb⟩
    · exact ⟨a, h.1, ha⟩
  have hyv' : ¬ Q.graph.Reaches v y := by
    intro h
    have hyne : y ≠ v := fun h' => hyv (h' ▸ .refl)
    have hs := reaches_source_of_below_hybrid hQ.binary hQ.levelOne h2 h hyne
    rw [hgs] at hs
    exact hN.acyclic v (Relation.TransGen.tail' hs hwvr)
  -- `d` is not below `y`, the other taxa are
  have hdy : ¬ Q.graph.Reaches y (Q.leaf d) := by
    intro h
    obtain ⟨e, hye, hev, hevt⟩ :=
      exists_arc_enter' (p := fun x => Q.graph.Reaches v x) h hyv' ((hd d).2 rfl)
    by_cases het : Q.graph.target e = v
    · rcases hsrc_v e het with h' | h'
      · exact hyr (h' ▸ hye)
      · exact hyw (h' ▸ hye)
    · exact hev (reaches_source_of_below_hybrid hQ.binary hQ.levelOne h2 hevt het)
  have hbelow : ∀ x, x ≠ d → Q.graph.Reaches y (Q.leaf x) := by
    intro x hx
    rcases hpart (Q.leaf x) with h | h | h | h
    · exact absurd (h.trans hfs.symm) (leaf_ne_source hN x f)
    · exact absurd (h.trans hgs.symm) (leaf_ne_source hN x g)
    · exact absurd ((hd x).1 h) hx
    · exact h
  have hcommon : ∀ x, Q.graph.Reaches v x → ¬ Q.graph.Reaches y x := by
    intro x hvx hyx
    obtain ⟨z, hz⟩ := exists_reaches_leaf hN x
    have hz' := (hd z).1 (hvx.trans hz)
    rw [hz'] at hz
    exact hdy (hyx.trans hz)
  -- `y` is a cut vertex, entered by `g` alone
  have hc : IsCut Q y := by
    refine ⟨hyr, fun e he hne => ?_⟩
    rcases hpart (Q.graph.source e) with h | h | h | h
    · rcases hrout e h with h' | h'
      · exact absurd (h' ▸ he) hyv
      · exact absurd (h' ▸ he) hyw
    · rcases hwout e h with h' | h'
      · exact absurd (h' ▸ he) hyv
      · exact absurd (h' ▸ rfl) hne
    · exact absurd he (hcommon _ (h.tail ⟨e, rfl, rfl⟩))
    · exact h
  have huniq : ∀ e, Q.graph.target e = y → e = g := by
    intro e he
    rcases hpart (Q.graph.source e) with h | h | h | h
    · rcases hrout e h with h' | h'
      · exact absurd (he ▸ h' ▸ .refl) hyv
      · exact absurd (he ▸ h' ▸ .refl) hyw
    · rcases hwout e h with h' | h'
      · exact absurd (he ▸ h' ▸ .refl) hyv
      · exact h'
    · exact absurd (he ▸ h.tail ⟨e, rfl, rfl⟩) hyv'
    · exact absurd (Relation.TransGen.tail' h ⟨e, rfl, he⟩) (hN.acyclic _)
  have hS' : ∀ x, Q.graph.Reaches y x → x ∉ cycleNodes Q.graph C := by
    intro x hx hxC
    rw [hS] at hxC
    rcases hxC with rfl | rfl | hxC
    · exact hyr hx
    · exact hyv hx
    · exact hyw (Set.mem_singleton_iff.1 hxC ▸ hx)
  -- the network without `b`
  have hbsrc := hsrc_v b hb
  have hbC := mem_of_target_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 hb
  have hSb : ∀ x, Q.graph.Reaches y x → Q.graph.source b ≠ x := by
    intro x hx hbx
    rcases hbsrc with h | h
    · exact hyr (h ▸ hbx ▸ hx)
    · exact hyw (h ▸ hbx ▸ hx)
  obtain ⟨g', hg'b, hg's⟩ : ∃ g', g' ≠ b ∧ Q.graph.source g' = Q.graph.source b := by
    rcases hbsrc with h | h
    · exact ⟨f, fun h' => hwv (hft.symm.trans (h' ▸ hb)), hfs.trans h.symm⟩
    · exact ⟨g, fun h' => hgC (h' ▸ hbC), hgs.trans h.symm⟩
  have hN₁ := isPhylogenetic_deleteArc hN hab (ha.trans hb.symm) hg'b hg's
  have hθ₁ := isMetric_deleteArc hN hθ.1 hθ.2 hab (ha.trans hb.symm) (hb ▸ h2)
  have hc₁ := isCut_deleteArc hc hSb
  have hgb : g ≠ b := fun h => hgC (h ▸ hbC)
  have huniq₁ : ∀ e, (deleteArc Q b).graph.target e = (deleteArc Q b).graph.target ⟨g, hgb⟩ →
      e = ⟨g, hgb⟩ := fun e he => Subtype.ext (huniq e.1 he)
  -- the contracted network
  have hN₀ := hK.isPhylogenetic hN
  have hθ₀ := hK.isMetric hθ.1
  have hc₀ := isCut_contract hcyc hc hS'
  let g₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'} := ⟨g, fun C' _ hC' => hC' ▸ hgC⟩
  have huniq₀ : ∀ e, (contractRooted Q (· = C)).graph.target e =
      (contractRooted Q (· = C)).graph.target g₀ → e = g₀ := fun e he =>
    Subtype.ext (huniq e.1 ((mk_eq_mk_iff_of_notMem' hcyc (hS' _ .refl)).1 he))
  have hd₀ : ¬ (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ y)
      ((contractRooted Q (· = C)).leaf d) := fun h => hdy ((reaches_contract_iff hcyc hS' _).1 h)
  have hbelow₀ : ∀ x, x ≠ d → (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ y)
      ((contractRooted Q (· = C)).leaf x) := fun x hx =>
    (reaches_contract_iff hcyc hS' _).2 (hbelow x hx)
  have hX := hQ.card_taxa
  -- the single lineage of `d`: below `v` in `Q⊕ ∖ b`, below the child arc `c` of `v` in `Q₀⊕`
  have hvr' : ¬ Q.graph.Reaches v Q.root := fun h =>
    hnoin a (ha.trans (eq_of_reaches_of_reaches hN.acyclic h (hN.root_reaches v)))
  have hvw' : ¬ Q.graph.Reaches v w := fun h => hN.acyclic w (Relation.TransGen.head' hwvr h)
  have hSbv : ∀ x, Q.graph.Reaches v x → Q.graph.source b ≠ x := by
    intro x hx hbx
    rcases hbsrc with h | h
    · exact hvr' (h ▸ hbx ▸ hx)
    · exact hvw' (h ▸ hbx ▸ hx)
  have hcv₁ : IsCut (deleteArc Q b) v :=
    isCut_deleteArc (isCut_hybrid hQ.binary hQ.levelOne h2) hSbv
  let a₁ : {e // e ≠ b} := ⟨a, hab⟩
  have hta₁ : (deleteArc Q b).graph.target a₁ = v := ha
  have huniqa₁ : ∀ e, (deleteArc Q b).graph.target e = v → e = a₁ := fun e he =>
    Subtype.ext ((mem_pair_of_target_of_indegree_eq_two h2 hab ha hb e.1 he).resolve_right e.2)
  have hdv₁ : ∀ x, (deleteArc Q b).graph.Reaches v ((deleteArc Q b).leaf x) ↔ x = d := fun x =>
    (reaches_deleteArc_iff hSbv _).trans (hd x)
  obtain ⟨c, hcs, hcu⟩ := existsUnique_child_of_hybrid hQ.binary h2
  obtain ⟨hcz, huniqz⟩ := isCut_child_of_hybrid hQ.binary hQ.levelOne h2 hcs hcu
  have hSz : ∀ x, Q.graph.Reaches (Q.graph.target c) x → x ∉ cycleNodes Q.graph C :=
    fun x hx hxC => hN.acyclic v (Relation.TransGen.head' ⟨c, hcs, rfl⟩
      (hx.trans (reaches_hybrid hQ.binary hQ.levelOne hcyc hv h2 x hxC)))
  have hcC : c ∉ C := notMem_of_source_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 hcs
  let c₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'} := ⟨c, fun C' _ hC' => hC' ▸ hcC⟩
  have hcz₀ := isCut_contract hcyc hcz hSz
  have huniqz₀ : ∀ e, (contractRooted Q (· = C)).graph.target e =
      Quot.mk _ (Q.graph.target c) → e = c₀ := fun e he =>
    Subtype.ext (huniqz e.1 ((mk_eq_mk_iff_of_notMem' hcyc (hSz _ .refl)).1 he))
  have hzleaf : ∀ x, Q.graph.Reaches (Q.graph.target c) (Q.leaf x) ↔ Q.graph.Reaches v (Q.leaf x) :=
    fun x => ⟨fun h => Relation.ReflTransGen.head ⟨c, hcs, rfl⟩ h, fun h =>
      (eq_or_reaches_of_unique_child hcu h).resolve_left fun h' => by
        have := hN.leaf_indegree x
        rw [h', h2] at this
        exact absurd this (by norm_num)⟩
  have hdz₀ : ∀ x, (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ (Q.graph.target c))
      ((contractRooted Q (· = C)).leaf x) ↔ x = d := fun x =>
    (reaches_contract_iff hcyc hSz _).trans ((hzleaf x).trans (hd x))
  -- the vertices of `Q₀⊕`: the root, below `c₀` or below `g₀`
  have hwC : w ∈ cycleNodes Q.graph C := by rw [hS]; simp
  have hmkr : ∀ x ∈ cycleNodes Q.graph C,
      (Quot.mk (RootedContractRel Q (· = C)) x) = Quot.mk _ Q.root := fun x hx =>
    (mk_eq_mk_iff hcyc).2 (Or.inr ⟨hx, hroot⟩)
  have hc₀s : (contractRooted Q (· = C)).graph.source c₀ = Quot.mk _ Q.root := by
    change Quot.mk _ (Q.graph.source c) = _
    rw [hcs]
    exact hmkr v hv
  have hg₀s : (contractRooted Q (· = C)).graph.source g₀ = Quot.mk _ Q.root := by
    change Quot.mk _ (Q.graph.source g) = _
    rw [hgs]
    exact hmkr w hwC
  have hpart₀ : ∀ u, u = Quot.mk _ Q.root ∨ u ∈ belowSet (contractRooted Q (· = C)) c₀ ∨
      u ∈ belowSet (contractRooted Q (· = C)) g₀ := by
    intro u
    induction u using Quot.ind with
    | mk x =>
      rcases hpart x with rfl | rfl | h | h
      · exact Or.inl rfl
      · exact Or.inl (hmkr _ hwC)
      · rcases eq_or_reaches_of_unique_child hcu h with rfl | h'
        · exact Or.inl (hmkr _ hv)
        · exact Or.inr (Or.inl (mem_belowSet.2 (reaches_contract_of_reaches hSz h')))
      · exact Or.inr (Or.inr (mem_belowSet.2 (reaches_contract_of_reaches hS' h)))
  have hdisj₀ : ∀ u, u ∈ belowSet (contractRooted Q (· = C)) g₀ →
      u ∉ belowSet (contractRooted Q (· = C)) c₀ := by
    intro u hug huc
    obtain ⟨x, hx, rfl⟩ := exists_of_reaches_contract hcyc hS' (mem_belowSet.1 hug)
    exact hcommon x (Relation.ReflTransGen.head ⟨c, hcs, rfl⟩
      ((reaches_contract_iff hcyc hSz x).1 (mem_belowSet.1 huc))) hx
  have hnotc : Quot.mk (RootedContractRel Q (· = C)) Q.root ∉
      belowSet (contractRooted Q (· = C)) c₀ := hc₀s ▸ source_notMem_belowSet hN₀ c₀
  have hnotg : Quot.mk (RootedContractRel Q (· = C)) Q.root ∉
      belowSet (contractRooted Q (· = C)) g₀ := hg₀s ▸ source_notMem_belowSet hN₀ g₀
  have hinjr₀ : taxaInj (contractRooted Q (· = C)) univ (Quot.mk _ Q.root) = ∅ := by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    exact leaf_ne_source hN₀ x c₀ ((mem_filter.1 hx).2.2.trans hc₀s.symm)
  -- the vertices of `Q⊕ ∖ b`
  have hinjs : ∀ e, taxaInj Q univ (Q.graph.source e) = ∅ := fun e => by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    exact leaf_ne_source hN x e (mem_filter.1 hx).2.2
  have hinjr : taxaInj Q univ Q.root = ∅ := hfs ▸ hinjs f
  have hinjw : taxaInj Q univ w = ∅ := hgs ▸ hinjs g
  have hsg₁ : (deleteArc Q b).graph.source ⟨g, hgb⟩ = w := hgs
  have hfb : f ≠ b := fun h => hwv (hft.symm.trans (h ▸ hb))
  let f₁ : {e // e ≠ b} := ⟨f, hfb⟩
  have huniqf₁ : ∀ e, (deleteArc Q b).graph.target e = (deleteArc Q b).graph.target f₁ → e = f₁ :=
    fun e he => Subtype.ext (hfu e.1 (he.trans hft))
  have htf₁ : (deleteArc Q b).graph.target f₁ = w := hft
  -- `CF = ∑ P(K' = k) CF(· | K' = k)`, with `K'` read from the forest at the top of `g`, whose law
  -- the two networks share
  have h1₁ : (deleteArcMetric Q b θ).inheritance ⟨g, hgb⟩ = 1 :=
    hθ₁.2.2.1 _ (isTreeArc_of_unique rfl huniq₁)
  have h1₀ : (contractMetric Q (· = C) θ).inheritance g₀ = 1 :=
    hθ₀.2.2.1 _ (isTreeArc_of_unique rfl huniq₀)
  have hlaw : ∀ t', arcLaw (deleteArc Q b) y hc₁ (deleteArcMetric Q b θ) 0 ⟨g, hgb⟩
      (taxaInj (deleteArc Q b) univ) t' = arcLaw (contractRooted Q (· = C)) (Quot.mk _ y) hc₀
        (contractMetric Q (· = C) θ) 0 g₀ (taxaInj (contractRooted Q (· = C)) univ) t' := by
    intro t'
    unfold arcLaw
    refine sum_congr rfl fun F₁ _ => ?_
    rw [rootDist_cutLower_deleteArc hc hSb θ 0 F₁, rootDist_cutLower_contract hcyc hc hS' θ 0 F₁]
    rfl
  rw [cf_eq_sum_jointCF _ _ ⟨g, hgb⟩ q, cf_eq_sum_jointCF _ _ g₀ q]
  refine sum_congr rfl fun k _ => ?_
  rw [jointCF_eq_sum_arc hN₁ hc₁ rfl huniq₁ h1₁ k q, jointCF_eq_sum_arc hN₀ hc₀ rfl huniq₀ h1₀ k q]
  refine sum_congr rfl fun t' _ => ?_
  split_ifs with hk
  swap
  · rfl
  rw [hlaw t']
  by_cases h0 : arcLaw (contractRooted Q (· = C)) (Quot.mk _ y) hc₀ (contractMetric Q (· = C) θ) 0
    g₀ (taxaInj (contractRooted Q (· = C)) univ) t' = 0
  · rw [h0, zero_mul, zero_mul]
  have h0₁ : arcLaw (deleteArc Q b) y hc₁ (deleteArcMetric Q b θ) 0 ⟨g, hgb⟩
      (taxaInj (deleteArc Q b) univ) t' ≠ 0 := by
    rw [hlaw]
    exact h0
  congr 1
  rw [sum_displays_injDist hX, sum_displays_injDist hX]
  have hv₁ := validInj_of_arcLaw_ne_zero hN₁ hc₁ rfl (validInj_taxaInj univ) h0₁
  have hv₀ := validInj_of_arcLaw_ne_zero hN₀ hc₀ rfl (validInj_taxaInj univ) h0
  obtain ⟨hgood, hlin⟩ := good_of_arcLaw_ne_zero hN₀ hc₀ (validInj_taxaInj univ) h0
  have hlin' : lineages t' = univ.erase d := by
    ext x
    rw [hlin x, mem_erase]
    simp only [mem_univ, and_true]
    constructor
    · rintro ⟨u, hu, hxu⟩
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
      exact fun h => hd₀ (h ▸ hu)
    · intro hxd
      exact ⟨_, hbelow₀ x hxd, mem_lineages_taxaInj.2 ⟨mem_univ _, rfl⟩⟩
  have hDq : ∀ D : Finset X, D ⊆ q.taxa := fun D => by
    rw [taxa_eq_univ hX q]
    exact subset_univ _
  by_cases hC2 : ∃ D ∈ t', #D = 2
  · -- `K' = 1`: the coalescence below the top of `g` decides the quartet tree in both networks
    obtain ⟨D, hD, hD2⟩ := hC2
    rw [cherryMass_of_mem hN₁ hθ₁ ⟨le_rfl, zero_le_one⟩ hv₁
        (v := (deleteArc Q b).graph.source ⟨g, hgb⟩)
        (by simp only [liftInj, ite_true]; exact mem_union_right _ hD) hD2 (hDq D),
      cherryMass_of_mem hN₀ hθ₀ ⟨le_rfl, zero_le_one⟩ hv₀
        (v := (contractRooted Q (· = C)).graph.source g₀)
        (by simp only [liftInj, ite_true]; exact mem_union_right _ hD) hD2 (hDq D)]
  -- `K' = 0`: the lineages of the three taxa below `y` at the top of `g`, the multispecies coalescent
  -- on a four-taxon species tree above it
  have ht' : t' = (univ.erase d).image fun x => {x} := by rw [hgood.eq_singletons hC2, hlin']
  have hS₃ : (univ.erase d).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ d), card_univ, hX]
    norm_num
  have hU : (univ : Finset X).Nonempty := ⟨d, mem_univ d⟩
  have hall : t' ∪ {{d}} = univ.image fun x => {x} := by
    rw [ht']
    ext D
    simp only [mem_union, mem_image, mem_erase, mem_univ, and_true, true_and, mem_singleton]
    constructor
    · rintro (⟨x, -, rfl⟩ | rfl)
      · exact ⟨x, rfl⟩
      · exact ⟨d, rfl⟩
    · rintro ⟨x, rfl⟩
      by_cases hxd : x = d
      · exact Or.inr (by rw [hxd])
      · exact Or.inl ⟨x, hxd, rfl⟩
  -- in `Q₀⊕`: the lineage of `d` up to the contracted root, where the three others are: the star tree
  have hinj₀ : ∀ u, (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ (Q.graph.target c)) u →
      liftInj (contractRooted Q (· = C)) g₀ (taxaInj (contractRooted Q (· = C)) univ) t' u =
        taxaInj (contractRooted Q (· = C)) univ u := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := exists_of_reaches_contract hcyc hSz hu
    have hvx : Q.graph.Reaches v x := Relation.ReflTransGen.head ⟨c, hcs, rfl⟩ hx
    have hnb : Quot.mk _ x ∉ belowSet (contractRooted Q (· = C)) g₀ := fun h =>
      hcommon x hvx ((reaches_contract_iff hcyc hS' x).1 (mem_belowSet.1 h))
    have hns : Quot.mk (RootedContractRel Q (· = C)) x ≠
        (contractRooted Q (· = C)).graph.source g₀ := by
      rw [hg₀s]
      intro h
      exact hvr' (((mk_eq_mk_iff_of_notMem hcyc (hSz x hx)).1 h) ▸ hvx)
    unfold liftInj
    rw [ite_eq_right hnb, ite_eq_right hns, union_empty]
  have hJ₀ : liftInj (contractRooted Q (· = C)) c₀
      (liftInj (contractRooted Q (· = C)) g₀ (taxaInj (contractRooted Q (· = C)) univ) t') {{d}} =
        atRoot (contractRooted Q (· = C)) (univ.image fun x => {x}) := by
    funext u
    unfold liftInj
    rcases hpart₀ u with rfl | h | h
    · have hat : atRoot (contractRooted Q (· = C)) (univ.image fun x => {x}) (Quot.mk _ Q.root) =
          univ.image fun x => {x} := atRoot_root _ _
      rw [hat, ite_eq_right hnotc, ite_eq_left hc₀s.symm, ite_eq_right hnotg, ite_eq_left hg₀s.symm, hinjr₀,
        empty_union, hall]
    · have hur : u ≠ Quot.mk _ Q.root := fun h' => hnotc (h' ▸ h)
      have huc : u ≠ (contractRooted Q (· = C)).graph.source c₀ := by rw [hc₀s]; exact hur
      rw [atRoot_of_ne _ _ hur, ite_eq_left h, ite_eq_right huc, union_empty]
    · have hur : u ≠ Quot.mk _ Q.root := fun h' => hnotg (h' ▸ h)
      have huc : u ≠ (contractRooted Q (· = C)).graph.source c₀ := by rw [hc₀s]; exact hur
      have hug : u ≠ (contractRooted Q (· = C)).graph.source g₀ := by rw [hg₀s]; exact hur
      rw [atRoot_of_ne _ _ hur, ite_eq_right (hdisj₀ u h), ite_eq_left h, ite_eq_right hug, ite_eq_right huc, union_empty,
        union_empty]
  have hcond₀ : cherryMass (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) 0
      (liftInj (contractRooted Q (· = C)) g₀ (taxaInj (contractRooted Q (· = C)) univ) t') q =
        External.AllmanDegnanRhodes2011.quartetProb (cladeSpeciesTree univ hU 1 one_pos) q := by
    rw [cherryMass_liftInj_single hN₀ hθ₀ hcz₀ rfl huniqz₀ hdz₀ hinj₀ q, hJ₀]
    exact cherryMass_atRoot_eq_quartetProb_univ hX hN₀.acyclic (NMSC.target_ne_root hN₀) _ 0 hU q
  -- in `Q⊕ ∖ b`: the lineage of `d` up to the source of `a`, and the three others at `w`
  have hinj₁ : ∀ u, (deleteArc Q b).graph.Reaches v u →
      liftInj (deleteArc Q b) ⟨g, hgb⟩ (taxaInj (deleteArc Q b) univ) t' u =
        taxaInj (deleteArc Q b) univ u := by
    intro u hu
    have hvu := (reaches_deleteArc_iff hSbv u).1 hu
    have hnb : u ∉ belowSet (deleteArc Q b) ⟨g, hgb⟩ := fun h =>
      hcommon u hvu ((reaches_deleteArc_iff hSb u).1 (mem_belowSet.1 h))
    have hns : u ≠ (deleteArc Q b).graph.source ⟨g, hgb⟩ := by
      rw [hsg₁]
      rintro rfl
      exact hvw' hvu
    unfold liftInj
    rw [ite_eq_right hnb, ite_eq_right hns, union_empty]
  have hJ₁ : ∀ u, liftInj (deleteArc Q b) a₁
      (liftInj (deleteArc Q b) ⟨g, hgb⟩ (taxaInj (deleteArc Q b) univ) t') {{d}} u =
        (if u = w then t' else ∅) ∪ (if u = Q.graph.source a then {{d}} else ∅) := by
    intro u
    have hsa : (deleteArc Q b).graph.source a₁ = Q.graph.source a := rfl
    unfold liftInj
    rw [hsg₁, hsa]
    rcases hpart u with hu | hu | h | h
    · subst u
      have h₁ : Q.root ∉ belowSet (deleteArc Q b) a₁ := root_notMem_belowSet hN₁ a₁
      have h₂ : Q.root ∉ belowSet (deleteArc Q b) ⟨g, hgb⟩ := root_notMem_belowSet hN₁ _
      rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right (Ne.symm hwr)]
      change taxaInj Q univ Q.root ∪ ∅ ∪ _ = _
      rw [hinjr, union_empty]
    · subst u
      have h₁ : w ∉ belowSet (deleteArc Q b) a₁ := fun h' =>
        hvw' ((reaches_deleteArc_iff hSbv w).1 (hta₁ ▸ mem_belowSet.1 h'))
      have h₂ : w ∉ belowSet (deleteArc Q b) ⟨g, hgb⟩ := fun h' =>
        hyw ((reaches_deleteArc_iff hSb w).1 (mem_belowSet.1 h'))
      rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_left rfl]
      change taxaInj Q univ w ∪ t' ∪ _ = _
      rw [hinjw, empty_union]
    · have h₁ : u ∈ belowSet (deleteArc Q b) a₁ :=
        mem_belowSet.2 (hta₁ ▸ (reaches_deleteArc_iff hSbv u).2 h)
      have huw : u ≠ w := fun h' => hvw' (h' ▸ h)
      have hua : u ≠ Q.graph.source a := by
        rcases hab' with h' | h'
        · rw [h'.1]
          exact fun h'' => hvr' (h'' ▸ h)
        · rw [h'.1]
          exact huw
      rw [ite_eq_left h₁, ite_eq_right huw, ite_eq_right hua, empty_union]
    · have h₁ : u ∉ belowSet (deleteArc Q b) a₁ := fun h' =>
        hcommon u ((reaches_deleteArc_iff hSbv u).1 (hta₁ ▸ mem_belowSet.1 h')) h
      have h₂ : u ∈ belowSet (deleteArc Q b) ⟨g, hgb⟩ :=
        mem_belowSet.2 ((reaches_deleteArc_iff hSb u).2 h)
      have huw : u ≠ w := fun h' => hyw (h' ▸ h)
      have hur : u ≠ Q.root := fun h' => hyr (h' ▸ h)
      have hua : u ≠ Q.graph.source a := by
        rcases hab' with h' | h'
        · rw [h'.1]
          exact hur
        · rw [h'.1]
          exact huw
      simp only [ite_eq_right h₁, ite_eq_left h₂, ite_eq_right huw, ite_eq_right hua, union_empty]
  have hinjJ₁ : ∀ u, u ≠ (deleteArc Q b).root → u ≠ (deleteArc Q b).graph.target f₁ →
      liftInj (deleteArc Q b) a₁
        (liftInj (deleteArc Q b) ⟨g, hgb⟩ (taxaInj (deleteArc Q b) univ) t') {{d}} u = ∅ := by
    intro u hur huw
    rw [htf₁] at huw
    have hua : u ≠ Q.graph.source a := by
      rcases hab' with h' | h'
      · rw [h'.1]
        exact hur
      · rw [h'.1]
        exact huw
    rw [hJ₁, ite_eq_right huw, ite_eq_right hua, union_empty]
  have h1f₁ : (deleteArcMetric Q b θ).inheritance f₁ = 1 :=
    hθ₁.2.2.1 _ (isTreeArc_of_unique rfl huniqf₁)
  have hfs₁ : (deleteArc Q b).graph.source f₁ = (deleteArc Q b).root := hfs
  rw [cherryMass_liftInj_single hN₁ hθ₁ hcv₁ hta₁ huniqa₁ hdv₁ hinj₁ q, hcond₀]
  rcases hab' with ⟨har, -⟩ | ⟨haw, -⟩
  · -- the hybrid edge of `Q⊕ ∖ b` leaves the root: the tree `((a,b,c):ℓ,d)`
    rw [cherryMass_rootArc_eq_quartetProb_erase hX hN₁.acyclic (NMSC.target_ne_root hN₁) hfs₁
      huniqf₁ h1f₁ (hθ.2 f) le_rfl hinjJ₁ hS₃
      (by rw [htf₁, hJ₁, ite_eq_left rfl, ite_eq_right fun h => hwr (h.trans har), union_empty, ht'])
      ((hJ₁ Q.root).trans (by rw [ite_eq_right (Ne.symm hwr), ite_eq_left har.symm, empty_union])) q]
    exact quartetProb_cladeSpeciesTree_erase hX d hS₃ _ _ hU 1 one_pos q
  · -- the hybrid edge of `Q⊕ ∖ b` leaves `w`: the star tree
    exact cherryMass_rootArc_eq_quartetProb_univ hX hN₁.acyclic (NMSC.target_ne_root hN₁) hfs₁
      huniqf₁ h1f₁ le_rfl hinjJ₁ hU (by rw [htf₁, hJ₁, ite_eq_left rfl, ite_eq_left haw.symm, hall])
      ((hJ₁ Q.root).trans (by rw [ite_eq_right (Ne.symm hwr), ite_eq_right fun h => hwr (h.trans haw).symm,
        union_empty])) q

/-- **Lemma 7** (`lem::formula2:1`): contracting a cycle that induces a `2₁`-cycle does not change the
concordance factors: `CF(Q⊕) = CF(Q₀⊕)`.

The paper's proof: one taxon is below `v`, so `P(K = 1) = 1` and `CF(Q⊕) = γ CF(Q₁⊕) + (1 - γ) CF(Q₂⊕)`
(`cf_eq_mixture`, as in Lemma 10); it remains that `CF(Q₁⊕) = CF(Q₂⊕) = CF(Q₀⊕)`. If the root is not
on `C`, only the single lineage of the taxon below `v` is on the edges in which `Q₁⊕`, `Q₂⊕` and
`Q₀⊕` differ (`cf_deleteArc_eq_contract_of_root_notMem`). If the root `r` is on `C`, with nodes
`r, u, v` and `y` the other child of `u`, the three other taxa are below `y`, and the paper conditions
on `K'`, whether a coalescent event has occurred among them before they leave `y`
(`cf_deleteArc_eq_contract_of_root_mem`): if so, the event decides the quartet tree in the three
networks alike; if not, the process above `y` is, in each of the three networks, the multispecies
coalescent on a four-taxon species tree, and these trees have the same unrooted metric tree.

For `K' = 0` the paper concludes `CF(Q₁⊕ | K' = 0) = CF(Q₂⊕ | K' = 0) = CF(Q₀⊕ | K' = 0)` "by
Proposition 4", which it takes from Allman, Degnan, Rhodes 2011 (arXiv v1: "Proposition 11 in
[Allman2011]"). As printed in the paper, Proposition 3 states that for four taxa the unrooted metric
species tree is identifiable from the distribution of unrooted gene trees and the rooted one is not, and
Proposition 4 that this remains valid for non-binary trees: these are identifiability statements, not
the invariance of the concordance factors under the root placement. The step uses that the root
placement does not matter, which Allman, Degnan, Rhodes 2011 prove (`pub:rootplace`: the source's
Theorem 9 and Proposition 11, `External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`).
`K'` is read at the top of the edge above `y` (the paper's "before `a`, `b`, `c` trace back to `y`"
counts at its bottom); the argument is the same. -/
theorem lemma7 (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 2 1) :
    cf Q θ = cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) := by
  obtain ⟨hcyc, hv, h2, hn, h1t⟩ := hC
  have hN := hQ.binary.1
  have : Finite E := hN.finite_arcs
  obtain ⟨h₁, h₂, hne, hh₁, hh₂⟩ : ∃ h₁ h₂, h₁ ≠ h₂ ∧ Q.graph.target h₁ = v ∧
      Q.graph.target h₂ = v := by
    obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 h2
    exact ⟨x, y, hxy, (Set.ext_iff.1 hs x).2 (Or.inl rfl), (Set.ext_iff.1 hs y).2 (Or.inr rfl)⟩
  obtain ⟨d, hdset⟩ := Set.ncard_eq_one.1 h1t
  have hd : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = d := fun x => by
    have := Set.ext_iff.1 hdset x
    simpa using this
  have hone : ∀ x y, Q.graph.Reaches (Q.graph.target h₁) (Q.leaf x) →
      Q.graph.Reaches (Q.graph.target h₁) (Q.leaf y) → x = y := by
    rw [hh₁]
    exact fun x y hx hy => ((hd x).1 hx).trans ((hd y).1 hy).symm
  -- `CF(Q₁⊕) = CF(Q₀⊕)` and `CF(Q₂⊕) = CF(Q₀⊕)`
  have key : ∀ a b, a ≠ b → Q.graph.target a = v → Q.graph.target b = v → ∀ q,
      cf (deleteArc Q b) (deleteArcMetric Q b θ) q =
        cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) q := by
    intro a b hab ha hb q
    by_cases hr : Q.root ∈ cycleNodes Q.graph C
    · have hcard : C.ncard = 3 := by
        rw [ite_eq_left hr] at hn
        omega
      exact cf_deleteArc_eq_contract_of_root_mem hQ hcyc hv h2 hr hcard hd hab ha hb q
    · have hcard : C.ncard = 2 := by
        rw [ite_eq_right hr] at hn
        omega
      exact cf_deleteArc_eq_contract_of_root_notMem hQ hcyc hv h2 hr hcard hd hab ha hb q
  funext q
  -- `CF(Q⊕) = γ CF(Q₁⊕) + (1 - γ) CF(Q₂⊕)`
  rw [cf_eq_mixture hN hQ.metric.1 hne (hh₁.trans hh₂.symm)
      (fun f hf => mem_pair_of_target_of_indegree_eq_two h2 hne hh₁ hh₂ f (hf.trans hh₂))
      (inheritance_add_eq_one hQ.metric.1 h2 hne hh₁ hh₂) hone q,
    key h₁ h₂ hne hh₁ hh₂ q, key h₂ h₁ hne.symm hh₂ hh₁ q]
  ring

omit [Fintype V] [Fintype E] in
/-- Three of four taxa satisfy `P`: the fourth does not. -/
theorem exists_fourth_of_three (hX : Fintype.card X = 4) {P : X → Prop}
    (h : {x | P x}.ncard = 3) : ∃ d, ¬ P d ∧ ∀ x, x ≠ d → P x := by
  have hc : ({x | P x}ᶜ).ncard = 1 := by
    rw [Set.ncard_compl, Nat.card_eq_fintype_card, hX, h]
  obtain ⟨d, hd⟩ := Set.ncard_eq_one.1 hc
  refine ⟨d, ?_, fun x hx => ?_⟩
  · have : d ∈ ({x | P x}ᶜ) := hd ▸ Set.mem_singleton d
    exact this
  · by_contra hPx
    have : x ∈ ({x | P x}ᶜ) := hPx
    rw [hd] at this
    exact hx this

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The taxa below a hybrid node are those below its child. -/
theorem reaches_leaf_iff_of_hybrid (hQ : IsBinaryRootedNetwork Q) (h2 : Q.graph.indegree v = 2)
    {c : E} (hc : Q.graph.source c = v) (huniq : ∀ g, Q.graph.source g = v → g = c) (x : X) :
    Q.graph.Reaches v (Q.leaf x) ↔ Q.graph.Reaches (Q.graph.target c) (Q.leaf x) := by
  constructor
  · intro h
    rcases eq_or_reaches_of_unique_child huniq h with h' | h'
    · have := hQ.1.leaf_indegree x
      rw [h', h2] at this
      exact absurd this (by norm_num)
    · exact h'
  · exact fun h => Relation.ReflTransGen.head ⟨c, hc, rfl⟩ h

/-- **Lemma 8** (`lem::formula2:3`): contracting a cycle that induces a `2₃`-cycle does not change the
concordance factors.

The paper's proof: with `K` the number of lineages at the hybrid node `v` (at the top of its child
edge `c`), `CF(Q⊕) = ∑ₖ P(K = k) CF(Q⊕ | K = k)` (`cf_eq_sum_jointCF`), and the same for `Q₀⊕`, whose
part below `c` is that of `Q⊕` (`rootDist_cutLower_contract`), so `K` has the same law. Given the
forest at the top of `c`, its value for a quartet tree is `quartetValue` in both networks
(`jointCF_eq_sum_quartetValue`): for `K = 1, 2` a coalescence has occurred and its cluster of two
lineages decides the quartet tree; for `K = 3` the three quartet trees are equally likely by
exchangeability of the three lineages at `v`.

Departure from the paper: for `K = 3` the paper conditions further on the event `𝔇` that the lineage
of the fourth taxon `d` is in the first coalescent event, and uses exchangeability on each of
`𝔇 = 0, 1`; the formalization uses exchangeability of the three lineages at `v` once
(`NMSC.cherryMass_eq_third`); the order of coalescent events is not part of the gene tree
distribution (`Phylogenetics.geneTreeDist` records topologies, not times), so `𝔇` has no meaning in
the representation. -/
theorem lemma8 (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 2 3) :
    cf Q θ = cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) := by
  obtain ⟨hcyc, hv, h2, -, h3⟩ := hC
  have hN := hQ.binary.1
  obtain ⟨c, hc, hcu⟩ := existsUnique_child_of_hybrid hQ.binary h2
  obtain ⟨hcut, huniq⟩ := isCut_child_of_hybrid hQ.binary hQ.levelOne h2 hc hcu
  -- the three taxa below `v` and the fourth one
  obtain ⟨d, hd, hbelow⟩ := exists_fourth_of_three hQ.card_taxa h3
  have hd' : ¬ Q.graph.Reaches (Q.graph.target c) (Q.leaf d) := fun h =>
    hd ((reaches_leaf_iff_of_hybrid hQ.binary h2 hc hcu d).2 h)
  have hbelow' : ∀ x, x ≠ d → Q.graph.Reaches (Q.graph.target c) (Q.leaf x) := fun x hx =>
    (reaches_leaf_iff_of_hybrid hQ.binary h2 hc hcu x).1 (hbelow x hx)
  -- the contracted network
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ.binary hQ.levelOne hcyc hv h2
  have hN₀ := hK.isPhylogenetic hN
  have hθ₀ := hK.isMetric hQ.metric.1
  have hS : ∀ w, Q.graph.Reaches (Q.graph.target c) w → w ∉ cycleNodes Q.graph C := fun w hw hwC =>
    hN.acyclic v (Relation.TransGen.head' ⟨c, hc, rfl⟩
      (hw.trans (reaches_hybrid hQ.binary hQ.levelOne hcyc hv h2 w hwC)))
  have hcut₀ := isCut_contract hcyc hcut hS
  let c₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'} :=
    ⟨c, fun C' _ hC' => hC' ▸ notMem_of_source_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 hc⟩
  have huniq₀ : ∀ g, (contractRooted Q (· = C)).graph.target g =
      (contractRooted Q (· = C)).graph.target c₀ → g = c₀ := fun g hg =>
    Subtype.ext (huniq g.1 ((mk_eq_mk_iff_of_notMem' hcyc (hS _ .refl)).1 hg))
  have hd₀ : ¬ (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ (Q.graph.target c))
      ((contractRooted Q (· = C)).leaf d) := fun h => hd' ((reaches_contract_iff hcyc hS _).1 h)
  have hbelow₀ : ∀ x, x ≠ d → (contractRooted Q (· = C)).graph.Reaches
      (Quot.mk _ (Q.graph.target c)) ((contractRooted Q (· = C)).leaf x) := fun x hx =>
    (reaches_contract_iff hcyc hS _).2 (hbelow' x hx)
  funext q
  -- `CF(Q⊕) = ∑ₖ P(K = k) CF(Q⊕ | K = k)`, and the same for `Q₀⊕`
  rw [cf_eq_sum_jointCF Q θ c q, cf_eq_sum_jointCF _ _ c₀ q]
  refine sum_congr rfl fun k _ => ?_
  -- `P(K = k) CF(Q⊕ | K = k) = P(K = k) CF(Q₀⊕ | K = k)`
  rw [jointCF_eq_sum_quartetValue hN hQ.metric.1 hQ.card_taxa hcut rfl huniq hd' hbelow' k q,
    jointCF_eq_sum_quartetValue hN₀ hθ₀ hQ.card_taxa hcut₀ rfl huniq₀ hd₀ hbelow₀ k q]
  refine sum_congr rfl fun t _ => ?_
  congr 2
  unfold arcLaw
  refine sum_congr rfl fun F₁ _ => ?_
  rw [rootDist_cutLower_contract hcyc hcut hS θ 0 F₁]
  rfl

/-- The cycles of `Q⊕` that induce `2₁`- or `2₃`-cycles. -/
def IsTwoOneOrThree (Q : RootedNetwork V E X) (C : Set E) : Prop :=
  ∃ v, InducesCycleType Q C v 2 1 ∨ InducesCycleType Q C v 2 3

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The cycles inducing `2₁`- and `2₃`-cycles induce 2-cycles. -/
theorem ncard_sub_eq_two_of_isTwoOneOrThree {C : Set E} (hC : IsTwoOneOrThree Q C) :
    C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0) = 2 := by
  obtain ⟨v, h | h⟩ := hC
  · exact h.2.2.2.1
  · exact h.2.2.2.1

/-- **The network `Q̃⊕` of Corollary 2**: `Q⊕` with the cycles inducing `2₁`- and `2₃`-cycles
contracted, and the nodes of degree two this leaves suppressed (`contractNet`). It depends on `Q⊕`
only; its parameters `corollary2Metric hQ θ'`, from any parameters `θ'` of `Q⊕`, give each of its
arcs the total length of a chain of arcs of `Q⊕` (`contractNetMetric_length`,
`contractNetChain`, `disjoint_contractNetChain`) and the inheritance of the last arc of the chain
(`contractNetMetric_inheritance`, `isHybridArc_contractNet_iff`). -/
abbrev corollary2Net (hQ : IsLSAQuartet Q θ) :=
  contractNet Q hQ.binary hQ.levelOne (IsTwoOneOrThree Q)

/-- The parameters of `Q̃⊕` from parameters `θ'` of `Q⊕`. -/
abbrev corollary2Metric (hQ : IsLSAQuartet Q θ) (θ' : MetricData E) :=
  contractNetMetric Q hQ.binary hQ.levelOne (IsTwoOneOrThree Q) θ'

/-- **`Q̃⊕` is an LSA quartet network**, with the concordance factors of `contractRooted Q
(IsTwoOneOrThree Q)`, the cycles of `Q⊕` that do not induce `2₁`- or `2₃`-cycles with their types,
and the cut edges of `Q⊕` between two pairs of taxa, for all parameters `θ'` of `Q⊕`. -/
theorem corollary2Net_spec (hQ : IsLSAQuartet Q θ) {θ' : MetricData E} (hθ' : IsMetricNetwork Q θ') :
    IsLSAQuartet (corollary2Net hQ) (corollary2Metric hQ θ') ∧
      cf (corollary2Net hQ) (corollary2Metric hQ θ') =
        cf (contractRooted Q (IsTwoOneOrThree Q)) (contractMetric Q (IsTwoOneOrThree Q) θ') ∧
      {D | IsCycle (corollary2Net hQ).graph D}.ncard =
        {D | IsCycle Q.graph D ∧ ¬ IsTwoOneOrThree Q D}.ncard ∧
      (∀ n' k' (Dx : Set X), (∃ D w, InducesCycleType (corollary2Net hQ) D w n' k' ∧
          {x | (corollary2Net hQ).graph.Reaches w ((corollary2Net hQ).leaf x)} = Dx) ↔
        ∃ D w, ¬ IsTwoOneOrThree Q D ∧ InducesCycleType Q D w n' k' ∧
          {x | Q.graph.Reaches w (Q.leaf x)} = Dx) ∧
      (∀ A : Set X, A.ncard = 2 → ((corollary2Net hQ).HasCutSplit A ↔ Q.HasCutSplit A)) := by
  obtain ⟨hb, h1', hlsa', hθ'', hcf, hnum, hcyc, hcut⟩ :=
    contractNet_spec hQ.binary hQ.levelOne hQ.isLSA hQ.card_taxa hθ'
      (P := IsTwoOneOrThree Q) fun _ _ hC => ncard_sub_eq_two_of_isTwoOneOrThree hC
  exact ⟨⟨hb, h1', hlsa', hQ.card_taxa, hθ''⟩, hcf, hnum, hcyc, hcut⟩

/-- With no cycle inducing a `2₁`- or `2₃`-cycle, contracting them changes nothing. -/
theorem cf_contractRooted_of_forall_not (hQ : IsLSAQuartet Q θ)
    (hP : ∀ C, IsCycle Q.graph C → ¬ IsTwoOneOrThree Q C) :
    cf Q θ = cf (contractRooted Q (IsTwoOneOrThree Q)) (contractMetric Q (IsTwoOneOrThree Q) θ) := by
  have hK := isContraction_contractSet_of_forall_not hQ.binary hQ.levelOne hP
  have htwo : ∃ x y : X, x ≠ y := by
    have : Nontrivial X := hQ.nontrivial
    exact exists_pair_ne X
  funext q
  exact (hK.nmscCF_eq hQ.binary.1 htwo θ (fun a _ h1 => by have := hQ.binary.2.1; omega)
    le_rfl q).symm

/-- **One step of Corollary 2**: contracting a cycle `C` inducing a `2₁`- or `2₃`-cycle does not
change the concordance factors (Lemma 7 or 8), and the network obtained, with its nodes of degree two
suppressed (`contractNet`), is an LSA quartet network with one cycle fewer. -/
theorem corollary2_step (hQ : IsLSAQuartet Q θ) (hC : IsCycle Q.graph C) (hCP : IsTwoOneOrThree Q C) :
    IsLSAQuartet (contractNet Q hQ.binary hQ.levelOne (· = C))
        (contractNetMetric Q hQ.binary hQ.levelOne (· = C) θ) ∧
      cf Q θ = cf (contractNet Q hQ.binary hQ.levelOne (· = C))
        (contractNetMetric Q hQ.binary hQ.levelOne (· = C) θ) ∧
      {D | IsCycle (contractNet Q hQ.binary hQ.levelOne (· = C)).graph D}.ncard <
        {D | IsCycle Q.graph D}.ncard := by
  obtain ⟨hb, h1', hlsa', hθ', hcf, hnum, -, -⟩ :=
    contractNet_spec hQ.binary hQ.levelOne hQ.isLSA hQ.card_taxa hQ.metric (P := (· = C))
      fun _ _ hC' => hC' ▸ ncard_sub_eq_two_of_isTwoOneOrThree hCP
  refine ⟨⟨hb, h1', hlsa', hQ.card_taxa, hθ'⟩, ?_, ?_⟩
  · rw [hcf]
    obtain ⟨v, h | h⟩ := hCP
    · exact lemma7 hQ h
    · exact lemma8 hQ h
  · rw [hnum]
    exact Set.ncard_lt_ncard ⟨fun D hD => hD.1, fun hsub => (hsub hC).2 rfl⟩ (Set.toFinite _)

/-- **Contracting the remaining cycles after one step of Corollary 2** has the concordance factors
of contracting the cycles inducing `2₁`- and `2₃`-cycles of `Q⊕` at once: the cycles of the network
of the step that induce `2₁`- and `2₃`-cycles are those of `Q⊕` other than `C`
(`contractNet_spec`), and the two contracted networks, with their nodes of degree two suppressed,
are the same network up to the names of their nodes and arcs, with the same lengths along their
chains and the same inheritance probabilities. -/
theorem cf_contractRooted_contractNet (hQ : IsLSAQuartet Q θ) (hC : IsCycle Q.graph C)
    (hCP : IsTwoOneOrThree Q C) :
    cf (contractRooted (contractNet Q hQ.binary hQ.levelOne (· = C))
        (IsTwoOneOrThree (contractNet Q hQ.binary hQ.levelOne (· = C))))
      (contractMetric _ (IsTwoOneOrThree (contractNet Q hQ.binary hQ.levelOne (· = C)))
        (contractNetMetric Q hQ.binary hQ.levelOne (· = C) θ)) =
      cf (contractRooted Q (IsTwoOneOrThree Q)) (contractMetric Q (IsTwoOneOrThree Q) θ) := by
  have hO : SelectsCycle Q (· = C) C :=
    ⟨hC, rfl, fun _ _ h => h, ncard_sub_eq_two_of_isTwoOneOrThree hCP⟩
  have hQ₁ := (corollary2_step hQ hC hCP).1
  exact cf_contractRooted_contractNet_eq (P := IsTwoOneOrThree Q)
    (P₁ := IsTwoOneOrThree (contractNet Q hQ.binary hQ.levelOne (· = C))) hQ.binary hQ.levelOne
    (fun _ _ hD => ncard_sub_eq_two_of_isTwoOneOrThree hD) hO hCP hQ₁.binary hQ₁.levelOne
    (fun _ hD => contractNet_exists_inducesCycleType_or_iff hQ.binary hQ.levelOne hO hD 2 1 2 3)
    hQ.metric.1 hQ₁.metric.1

omit [Fintype V] [Fintype E] in
/-- **Corollary 2, by induction on the number of cycles**, for networks on `Type`. -/
theorem corollary2_aux (n : ℕ) :
    ∀ {V' E' : Type} [Fintype V'] [Fintype E'] {Q : RootedNetwork V' E' X} {θ : MetricData E'},
      IsLSAQuartet Q θ → {D | IsCycle Q.graph D}.ncard = n →
        cf Q θ = cf (contractRooted Q (IsTwoOneOrThree Q)) (contractMetric Q (IsTwoOneOrThree Q) θ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V' E' _ _ Q θ hQ hn
  by_cases hex : ∃ C, IsCycle Q.graph C ∧ IsTwoOneOrThree Q C
  · obtain ⟨C, hC, hCP⟩ := hex
    obtain ⟨hQ₁, hcf, hlt⟩ := corollary2_step hQ hC hCP
    rw [hcf, ih _ (hn ▸ hlt) hQ₁ rfl, cf_contractRooted_contractNet hQ hC hCP]
  · push Not at hex
    exact cf_contractRooted_of_forall_not hQ hex

/-- **Corollary 2** (`cor:2isgood`): contracting all cycles that induce `2₁`- or `2₃`-cycles does not
change the concordance factors: `CF(Q⊕) = CF(Q̃⊕)`.

The paper's proof applies Lemmas 7 and 8 to these cycles one after the other. Contracting one of them,
`C`, does not change the concordance factors (`corollary2_step`, by Lemma 7 or 8); the network
obtained, with its nodes of degree two suppressed, is an LSA quartet network with the other cycles
(`contractNet_spec`), to which the induction applies (`corollary2_aux`); and contracting its cycles
inducing `2₁`- and `2₃`-cycles has the concordance factors of contracting those of `Q⊕` at once
(`cf_contractRooted_contractNet`). -/
theorem corollary2 (hQ : IsLSAQuartet Q θ) :
    cf Q θ = cf (contractRooted Q (IsTwoOneOrThree Q)) (contractMetric Q (IsTwoOneOrThree Q) θ) := by
  by_cases hex : ∃ C, IsCycle Q.graph C ∧ IsTwoOneOrThree Q C
  · obtain ⟨C, hC, hCP⟩ := hex
    obtain ⟨hQ₁, hcf, -⟩ := corollary2_step hQ hC hCP
    rw [hcf, corollary2_aux _ hQ₁ rfl, cf_contractRooted_contractNet hQ hC hCP]
  · push Not at hex
    exact cf_contractRooted_of_forall_not hQ hex

/-- The law at the top of an arc does not depend on the inheritance probabilities of arcs not below
it. -/
theorem arcLaw_withPair {N : RootedNetwork V E X} {r : V} (hc : IsCut N r) {h₁ h₂ : E}
    (hh₁ : ¬ N.graph.Reaches r (N.graph.target h₁)) (hh₂ : ¬ N.graph.Reaches r (N.graph.target h₂))
    (θ : MetricData E) (γ' : ℝ) (c : E) (inj : V → Finset (Finset X)) (t : Finset (Finset X)) :
    arcLaw N r hc (θ.withPair h₁ h₂ γ') 0 c inj t = arcLaw N r hc θ 0 c inj t := by
  have hm : cutLowerMetric N r (θ.withPair h₁ h₂ γ') = cutLowerMetric N r θ := by
    simp only [cutLowerMetric, MetricData.mk.injEq, withPair_length, true_and]
    funext e
    exact withPair_inheritance_of_ne (fun h => hh₁ (by rw [← h]; exact e.2.1))
      (fun h => hh₂ (by rw [← h]; exact e.2.1)) γ'
  unfold arcLaw
  rw [hm, withPair_length]

omit [Fintype E] [Fintype X] in
/-- Lifting a forest to a vertex `v` whose only child arc is `c` injects it at `v`, with nothing below
`v`. -/
theorem liftInj_eq_cutInj {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {v : V} {c : E}
    (hc : N.graph.source c = v) (hcu : ∀ g, N.graph.source g = v → g = c)
    (inj : V → Finset (Finset X)) (hinj : inj v = ∅) (t : Finset (Finset X)) :
    liftInj N c inj t = cutInj N v inj t := by
  funext w
  unfold liftInj cutInj
  by_cases hvw : N.graph.Reaches v w
  · rw [ite_eq_left hvw]
    rcases eq_or_reaches_of_unique_child hcu hvw with rfl | h
    · have hnot : w ∉ belowSet N c := hc ▸ source_notMem_belowSet hN c
      rw [ite_eq_right hnot, hinj, empty_union, ite_eq_left hc.symm, ite_eq_left rfl]
    · have hmem : w ∈ belowSet N c := mem_belowSet.2 h
      have hne : w ≠ N.graph.source c := fun h' => source_notMem_belowSet hN c (h' ▸ hmem)
      have hne' : w ≠ v := fun h' => hne (h'.trans hc.symm)
      rw [ite_eq_left hmem, ite_eq_right hne, ite_eq_right hne', empty_union]
  · rw [ite_eq_right hvw]
    have hnot : w ∉ belowSet N c := fun h =>
      hvw (Relation.ReflTransGen.head ⟨c, hc, rfl⟩ (mem_belowSet.1 h))
    have hne : w ≠ N.graph.source c := fun h => hvw (by rw [h, hc]; exact .refl)
    rw [ite_eq_right hnot, ite_eq_right hne, union_empty]

/-- **The split of the two lineages at the hybrid node of a cycle inducing a `2₂`-cycle**, the
common part of the two cases of Lemma 9. With `K` the lineages at the top of the child edge `c` of
`v` (`cherryMass_eq_sum_arc`), the forest `G` at `v` splits between the hybrid edges
(`cherryMass_cutInj_hybrid`): both lineages, or the single one, on `h₁` (probability `γ²`, or `γ`),
on `h₂`, or one on each. The first two cases are the processes of `Q₁⊕` and `Q₂⊕`, which are those of
`Q⊕` with inheritance `1` and `0` on `h₁` (`cf_deleteArc`); it remains that one lineage on each
hybrid edge gives the concordance factors of `Q₀⊕` given `G` (the hypothesis `HZ`). -/
theorem cf_eq_of_two_two_of_split (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 2 2)
    {h₁ h₂ : E} (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v)
    {c : E} (hc : Q.graph.source c = v) (hcu : ∀ g, Q.graph.source g = v → g = c)
    (hcut : IsCut Q (Q.graph.target c)) (huniq : ∀ g, Q.graph.target g = Q.graph.target c → g = c)
    (c₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'}) (hc₀ : c₀.1 = c)
    (hcut₀ : IsCut (contractRooted Q (· = C)) (Quot.mk _ (Q.graph.target c)))
    (huniq₀ : ∀ g, (contractRooted Q (· = C)).graph.target g = Quot.mk _ (Q.graph.target c) →
      g = c₀)
    (hlaw : ∀ t, arcLaw (contractRooted Q (· = C)) _ hcut₀ (contractMetric Q (· = C) θ) 0 c₀
      (taxaInj (contractRooted Q (· = C)) univ) t = arcLaw Q _ hcut θ 0 c (taxaInj Q univ) t)
    (q : QuartetTree X)
    (HZ : ∀ G, arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G ≠ 0 →
      (#(roots G) = 1 →
        cherryMass Q θ 0 (hybInj Q v h₁ h₂ (taxaInj Q univ) G ∅) q =
          cherryMass (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) 0
            (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) q ∧
        cherryMass Q θ 0 (hybInj Q v h₁ h₂ (taxaInj Q univ) ∅ G) q =
          cherryMass (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) 0
            (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) q) ∧
      ∀ R₁ R₂, R₁ ≠ R₂ → roots G = {R₁, R₂} →
        cherryMass Q θ 0 (hybInj Q v h₁ h₂ (taxaInj Q univ) (forestBelow G {R₁})
            (forestBelow G {R₂})) q =
          cherryMass (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) 0
            (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) q) :
    cf Q θ q =
      θ.inheritance h₁ ^ 2 * cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q +
        (1 - θ.inheritance h₁) ^ 2 * cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q +
        2 * θ.inheritance h₁ * (1 - θ.inheritance h₁) *
          cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) q := by
  obtain ⟨hcyc, hv, h2, -, hk⟩ := hC
  have hN := hQ.binary.1
  have hθ := hQ.metric.1
  have := hN.finite_arcs
  have hpar := mem_pair_of_target_of_indegree_eq_two h2 hne hh₁ hh₂
  have hsum1 := inheritance_add_eq_one hθ h2 hne hh₁ hh₂
  set γ := θ.inheritance h₁ with hγ
  have hγ₂ : θ.inheritance h₂ = 1 - γ := by linarith
  have hvr : v ≠ Q.root := fun h => by
    have := hN.root_indegree
    rw [← h, h2] at this
    exact absurd this (by norm_num)
  have hcv : IsCut Q v := ⟨fun h => hvr (eq_of_reaches_of_reaches hN.acyclic h (hN.root_reaches v)),
    fun e he hne' => reaches_source_of_below_hybrid hQ.binary hQ.levelOne h2 he hne'⟩
  have hcr : Q.graph.target c ≠ v := fun h => hN.acyclic v (.single ⟨c, hc, h⟩)
  have hnr : ∀ h, Q.graph.target h = v → ¬ Q.graph.Reaches (Q.graph.target c) (Q.graph.target h) :=
    fun h hh hr => hN.acyclic v (Relation.TransGen.head' ⟨c, hc, rfl⟩ (hh ▸ hr))
  have hθc : θ.inheritance c = 1 := hθ.2.2.1 c (isTreeArc_of_unique rfl huniq)
  have hc₁ : c ≠ h₁ := fun h => hcr (h ▸ hh₁)
  have hc₂ : c ≠ h₂ := fun h => hcr (h ▸ hh₂)
  have hnorm : ∀ γ', Q.IsNormalized (θ.withPair h₁ h₂ γ') := fun γ' =>
    isNormalized_withPair hθ.isNormalized hne (hh₂.trans hh₁.symm) (fun f hf hf₁ hf₂ =>
      absurd (hpar f (hf.trans hh₁)) (by tauto)) γ'
  have hX := hQ.card_taxa
  have htaxa := taxa_eq_univ hX q
  have hinjv : taxaInj Q univ v = ∅ := by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    exact leaf_ne_source hN x c ((mem_filter.1 hx).2.2.trans hc.symm)
  -- the polynomial in the inheritance `γ'` of `h₁`
  let W : Finset (Finset X) → Finset (Finset X) → ℝ := fun t₁ t₂ =>
    cherryMass Q θ 0 (hybInj Q v h₁ h₂ (taxaInj Q univ) t₁ t₂) q
  have hΦ : ∀ γ', cf Q (θ.withPair h₁ h₂ γ') q = ∑ G, arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G *
      hybridPoly G (θ.length h₁) (θ.length h₂) W γ' := by
    intro γ'
    have h1' : (θ.withPair h₁ h₂ γ').inheritance c = 1 := by
      rw [withPair_inheritance_of_ne hc₁ hc₂]
      exact hθc
    rw [cf, nmscCF_eq_cherryMass_weak hN (hnorm γ') le_rfl, htaxa,
      cherryMass_eq_sum_arc hN hcut rfl huniq h1']
    refine sum_congr rfl fun G _ => ?_
    rw [arcLaw_withPair hcut (hnr h₁ hh₁) (hnr h₂ hh₂), liftInj_eq_cutInj hN hc hcu _ hinjv,
      cherryMass_cutInj_hybrid hN hcv hne hh₁ hh₂ hpar (withPair_inheritance_left h₁ h₂ γ')
        (withPair_inheritance_right hne γ')]
    unfold hybridPoly
    simp only [withPair_length, W, cherryMass_hybInj_withPair hN hcv hne hh₁ hh₂ hpar rfl hγ₂]
  -- the three networks of the formula
  have hQθ : cf Q θ q = cf Q (θ.withPair h₁ h₂ γ) q := by
    rw [withPair_eq_self rfl fun _ => hγ₂]
  have hQ₁ : cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q = cf Q (θ.withPair h₁ h₂ 1) q :=
    cf_deleteArc hN θ (hh₁.trans hh₂.symm) (fun f hf => hpar f (hf.trans hh₂)) hne q
  have hQ₂ : cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q = cf Q (θ.withPair h₁ h₂ 0) q := by
    rw [cf_deleteArc hN θ (hh₂.trans hh₁.symm) (fun f hf => (hpar f (hf.trans hh₁)).symm)
      hne.symm q]
    have hswap : θ.withPair h₂ h₁ 1 = θ.withPair h₁ h₂ 0 := by
      simp only [RootedNetwork.MetricData.withPair, RootedNetwork.MetricData.mk.injEq, true_and]
      funext f
      by_cases hf₂ : f = h₂
      · simp [hf₂, hne.symm]
      · by_cases hf₁ : f = h₁
        · simp [hf₁, hne]
        · simp [hf₁, hf₂]
    rw [hswap]
  -- `Q₀⊕`
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ.binary hQ.levelOne hcyc hv h2
  have hN₀ := hK.isPhylogenetic hN
  have hθ₀ := hK.isMetric hθ
  have hQ₀ : cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) q =
      ∑ G, arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G *
        cherryMass (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) 0
          (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) q := by
    have h1₀ : (contractMetric Q (· = C) θ).inheritance c₀ = 1 := by
      change θ.inheritance c₀.1 = 1
      rw [hc₀]
      exact hθc
    have hcr₀ : (contractRooted Q (· = C)).graph.target c₀ = Quot.mk _ (Q.graph.target c) := by
      change Quot.mk _ (Q.graph.target c₀.1) = _
      rw [hc₀]
    rw [cf_eq_cherryMass hN₀ hθ₀ hX, cherryMass_eq_sum_arc hN₀ hcut₀ hcr₀ huniq₀ h1₀]
    exact sum_congr rfl fun G _ => by rw [hlaw]
  -- the polynomial, forest by forest
  have hpoint : ∀ G, arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G *
      hybridPoly G (θ.length h₁) (θ.length h₂) W γ =
      arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G *
        (γ ^ 2 * hybridPoly G (θ.length h₁) (θ.length h₂) W 1 +
          (1 - γ) ^ 2 * hybridPoly G (θ.length h₁) (θ.length h₂) W 0 +
          2 * γ * (1 - γ) * cherryMass (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) 0
            (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) q) := by
    intro G
    by_cases hG : arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G = 0
    · rw [hG, zero_mul, zero_mul]
    congr 1
    obtain ⟨hgood, hlin⟩ := good_of_arcLaw_ne_zero hN hcut (validInj_taxaInj univ) hG
    -- the lineages of `G` are the two taxa below `v`
    have hlin' : ∀ x, x ∈ lineages G ↔ Q.graph.Reaches v (Q.leaf x) := fun x => by
      rw [hlin, reaches_leaf_iff_of_hybrid hQ.binary h2 hc hcu]
      constructor
      · rintro ⟨u, hu, hx⟩
        obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hx
        exact hu
      · exact fun h => ⟨_, h, mem_lineages_taxaInj.2 ⟨mem_univ _, rfl⟩⟩
    have hcard : #(lineages G) = 2 := by
      rw [← hk, ← Set.ncard_coe_finset]
      congr 1
      ext x
      simp [hlin']
    have h2r : #(roots G) ≤ 2 := hcard ▸ hgood.1.card_roots_le_card_lineages
    obtain ⟨HZ1, HZ2⟩ := HZ G hG
    refine hybridPoly_eq hgood h2r _ _ W _ (fun h0 => ?_) HZ1 HZ2 γ
    rw [h0] at hcard
    simp [lineages] at hcard
  rw [hQθ, hQ₁, hQ₂, hQ₀, hΦ, hΦ, hΦ, sum_congr rfl fun G _ => hpoint G]
  simp only [mul_add, sum_add_distrib, mul_sum]
  refine congr (congrArg HAdd.hAdd (congrArg₂ _ ?_ ?_)) ?_ <;>
    refine sum_congr rfl fun G _ => ?_ <;> ring

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **A cycle with two edges, off the root**: its top `t` is the source of both edges, has a single
parent arc `p`, and is a cut vertex below which lie only `t` and the part below the hybrid node. -/
theorem top_of_two_cycle (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    (hcyc : IsCycle Q.graph C) (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2)
    (hroot : Q.root ∉ cycleNodes Q.graph C) (hcard : C.ncard = 2) {a b : E} (hab : a ≠ b)
    (ha : Q.graph.target a = v) (hb : Q.graph.target b = v) {t : V} (hK : IsContractible Q C t) :
    Q.graph.source a = t ∧ Q.graph.source b = t ∧ t ≠ v ∧
      (∃ p, Q.graph.target p = t ∧ ∀ g, Q.graph.target g = t → g = p) ∧
      (∀ w, Q.graph.Reaches t w → w = t ∨ Q.graph.Reaches v w) ∧ IsCut Q t := by
  have hN := hQ.1
  have : Finite E := hN.finite_arcs
  have : Finite V := hN.finite_vertices
  have haC := mem_of_target_eq_hybrid hQ h1 hcyc hv h2 ha
  have hbC := mem_of_target_eq_hybrid hQ h1 hcyc hv h2 hb
  have htv : t ≠ v := fun h => hK.top_entry a (ha.trans h.symm) haC
  have hS : cycleNodes Q.graph C = {t, v} := by
    refine (Set.eq_of_subset_of_ncard_le (Set.insert_subset hK.top_mem
      (Set.singleton_subset_iff.2 hv)) ?_ (Set.toFinite _)).symm
    rw [ncard_cycleNodes hcyc, hcard, Set.ncard_pair htv]
  have hsrc : ∀ e ∈ C, Q.graph.target e = v → Q.graph.source e = t := by
    intro e he het
    have hs := source_mem_cycleNodes (G := Q.graph) he
    rw [hS] at hs
    rcases hs with hs | hs
    · exact hs
    · exact absurd ((Set.mem_singleton_iff.1 hs).trans het.symm) (source_ne_target_of_binary hQ e)
  have hat := hsrc a haC ha
  have hbt := hsrc b hbC hb
  have htr : t ≠ Q.root := fun h => hroot (h ▸ hK.top_mem)
  obtain ⟨p, hp⟩ := (Q.graph.one_le_indegree_iff t).1 (hN.nonroot_indegree t htr)
  have hind1 : Q.graph.indegree t ≤ 1 :=
    indegree_le_one_of_mem hQ h1 hcyc hv h2 hK.top_mem htv
  have huniq : ∀ g, Q.graph.target g = t → g = p := fun g hg => by
    by_contra hne
    have := two_le_indegree_of_two_targets hQ hne hg hp
    omega
  have hout : Q.graph.outdegree t = 2 := by
    have h3 := hQ.2.2 t htr (fun h0 => (Q.graph.outdegree_eq_zero_iff _).1 h0 a hat)
    have h1' : Q.graph.indegree t = 1 := le_antisymm hind1 (hN.nonroot_indegree t htr)
    omega
  have hchild : ∀ w, Q.graph.Reaches t w → w = t ∨ Q.graph.Reaches v w := by
    intro w hw
    rcases Relation.ReflTransGen.cases_head hw with h | ⟨x, ⟨g, hg, rfl⟩, hx⟩
    · exact Or.inl h.symm
    · rcases mem_pair_of_source_of_outdegree_eq_two hout hab hat hbt g hg with rfl | rfl
      · exact Or.inr (ha ▸ hx)
      · exact Or.inr (hb ▸ hx)
  have htvr : Q.graph.Reaches t v := .single ⟨a, hat, ha⟩
  refine ⟨hat, hbt, htv, ⟨p, hp, huniq⟩, hchild, fun hr => ?_, fun e he hne => ?_⟩
  · obtain ⟨g, -, hg⟩ := exists_arc_enter (p := fun w => w = Q.root) hr htr rfl
    exact (Q.graph.indegree_eq_zero_iff _ |>.1 hN.root_indegree) g hg
  · rcases hchild _ he with h | h
    · exact absurd h hne
    · by_cases hev : Q.graph.target e = v
      · rcases mem_pair_of_target_of_indegree_eq_two h2 hab ha hb e hev with rfl | rfl
        · rw [hat]
          exact .refl
        · rw [hbt]
          exact .refl
      · exact htvr.trans (reaches_source_of_below_hybrid hQ h1 h2 h hev)

/-- Lemma 9 when the root is not on the cycle: `C` is two edges from its top `t` to `v`, and one
lineage on each of them puts both lineages at `t`, as in `Q₀⊕`, where the contracted node is `t`:
both processes are read from the part above `t` (`cherryMass_cutInj_eq_upperLaw`,
`IsContractible.upperLaw_contract`). -/
theorem lemma9_of_root_notMem (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 2 2)
    (hroot : Q.root ∉ cycleNodes Q.graph C) {h₁ h₂ : E} (hne : h₁ ≠ h₂)
    (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) (q : QuartetTree X) :
    cf Q θ q =
      θ.inheritance h₁ ^ 2 * cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q +
        (1 - θ.inheritance h₁) ^ 2 * cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q +
        2 * θ.inheritance h₁ * (1 - θ.inheritance h₁) *
          cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) q := by
  obtain ⟨hcyc, hv, h2, hn, hk⟩ := hC
  have hN := hQ.binary.1
  have hθ := hQ.metric.1
  have hcard : C.ncard = 2 := by
    rw [ite_eq_right hroot] at hn
    omega
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ.binary hQ.levelOne hcyc hv h2
  obtain ⟨hat, hbt, htv, ⟨p, hp, huniqt⟩, hchild, hct⟩ :=
    top_of_two_cycle hQ.binary hQ.levelOne hcyc hv h2 hroot hcard hne hh₁ hh₂ hK
  obtain ⟨c, hc, hcu⟩ := existsUnique_child_of_hybrid hQ.binary h2
  obtain ⟨hcut, huniq⟩ := isCut_child_of_hybrid hQ.binary hQ.levelOne h2 hc hcu
  have hS : ∀ w, Q.graph.Reaches (Q.graph.target c) w → w ∉ cycleNodes Q.graph C := fun w hw hwC =>
    hN.acyclic v (Relation.TransGen.head' ⟨c, hc, rfl⟩
      (hw.trans (reaches_hybrid hQ.binary hQ.levelOne hcyc hv h2 w hwC)))
  have hcC : c ∉ C := notMem_of_source_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 hc
  let c₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'} := ⟨c, fun C' _ hC' => hC' ▸ hcC⟩
  have hcut₀ := isCut_contract hcyc hcut hS
  have huniq₀ : ∀ g, (contractRooted Q (· = C)).graph.target g =
      Quot.mk _ (Q.graph.target c) → g = c₀ := fun g hg =>
    Subtype.ext (huniq g.1 ((mk_eq_mk_iff_of_notMem' hcyc (hS _ .refl)).1 hg))
  have hlaw : ∀ G, arcLaw (contractRooted Q (· = C)) _ hcut₀ (contractMetric Q (· = C) θ) 0 c₀
      (taxaInj (contractRooted Q (· = C)) univ) G = arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G := by
    intro G
    unfold arcLaw
    refine sum_congr rfl fun F₁ _ => ?_
    rw [rootDist_cutLower_contract hcyc hcut hS θ 0 F₁]
    rfl
  refine cf_eq_of_two_two_of_split hQ ⟨hcyc, hv, h2, hn, hk⟩ hne hh₁ hh₂ hc hcu hcut huniq c₀ rfl
    hcut₀ huniq₀ hlaw q fun G hG => ?_
  -- the process above `t`, in `Q⊕` and in `Q₀⊕`
  have hθp : θ.inheritance p = 1 := hθ.2.2.1 p (isTreeArc_of_unique hp huniqt)
  have hinjt : taxaInj Q univ t = ∅ := by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    exact leaf_ne_source hN x h₁ ((mem_filter.1 hx).2.2.trans hat.symm)
  have hW : ∀ t₁ t₂, hybInj Q v h₁ h₂ (taxaInj Q univ) t₁ t₂ =
      cutInj Q t (taxaInj Q univ) (t₁ ∪ t₂) := by
    intro t₁ t₂
    funext w
    unfold hybInj cutInj
    by_cases hvw : Q.graph.Reaches v w
    · have htw : Q.graph.Reaches t w := (Relation.ReflTransGen.single ⟨h₁, hat, hh₁⟩).trans hvw
      have hwt : w ≠ t := fun h => hN.acyclic t (Relation.TransGen.head' ⟨h₁, hat, hh₁⟩ (h ▸ hvw))
      rw [ite_eq_left hvw, ite_eq_left htw, ite_eq_right hwt]
    · rw [ite_eq_right hvw]
      by_cases htw : Q.graph.Reaches t w
      · have hwt : w = t := (hchild w htw).resolve_right hvw
        subst hwt
        rw [ite_eq_left htw, ite_eq_left rfl, hinjt, empty_union, ite_eq_left hat.symm, ite_eq_left hbt.symm]
      · have hwt : w ≠ t := fun h => htw (h ▸ .refl)
        rw [ite_eq_right htw, ite_eq_right (hat ▸ hwt), ite_eq_right (hbt ▸ hwt), union_empty, union_empty]
  obtain ⟨hgood, -⟩ := good_of_arcLaw_ne_zero hN hcut (validInj_taxaInj univ) hG
  -- `Q₀⊕`: the contracted node is the top
  obtain ⟨t', -⟩ := (⟨t, hK⟩ : ∃ t, IsContractible Q C t)
  have hN₀ := hK.isPhylogenetic hN
  have hθ₀ := hK.isMetric hθ
  have hc₀t : (contractRooted Q (· = C)).graph.source c₀ = Quot.mk _ t := by
    change Quot.mk _ (Q.graph.source c) = _
    rw [hc]
    exact (mk_eq_mk_iff hcyc).2 (Or.inr ⟨hv, hK.top_mem⟩)
  have hcu₀ : ∀ g, (contractRooted Q (· = C)).graph.source g = Quot.mk _ t → g = c₀ := by
    intro g hg
    have hgC : g.1 ∉ C := g.2 C hcyc rfl
    have hs : Q.graph.source g.1 = t ∨ Q.graph.source g.1 = v := by
      rcases (mk_eq_mk_iff hcyc).1 hg with h | ⟨h, -⟩
      · exact Or.inl h
      · have hS2 : cycleNodes Q.graph C = {t, v} := by
          refine (Set.eq_of_subset_of_ncard_le (Set.insert_subset hK.top_mem
            (Set.singleton_subset_iff.2 hv)) ?_ (Set.toFinite _)).symm
          rw [ncard_cycleNodes hcyc, hcard, Set.ncard_pair htv]
        rw [hS2] at h
        exact h
    rcases hs with hs | hs
    · have hout : Q.graph.outdegree t = 2 := by
        have := hQ.binary.2.2 t (fun h => hroot (h ▸ hK.top_mem)) (fun h0 =>
          (Q.graph.outdegree_eq_zero_iff _).1 h0 h₁ hat)
        have h1' : Q.graph.indegree t = 1 :=
          (Q.graph.indegree_eq_one_iff t).2 ⟨p, fun f => ⟨huniqt f, fun h => h ▸ hp⟩⟩
        omega
      rcases mem_pair_of_source_of_outdegree_eq_two hout hne hat hbt g.1 hs with h | h
      · exact absurd (h ▸ mem_of_target_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 hh₁) hgC
      · exact absurd (h ▸ mem_of_target_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 hh₂) hgC
    · exact Subtype.ext (hcu g.1 hs)
  have hinj₀ : taxaInj (contractRooted Q (· = C)) univ (Quot.mk _ t) = ∅ := by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    exact leaf_ne_source hN₀ x c₀ ((mem_filter.1 hx).2.2.trans hc₀t.symm)
  have hc₀ := hK.isCut_top hct
  let p₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'} :=
    ⟨p, fun C' _ hC' => hC' ▸ hK.top_entry p hp⟩
  have hpt₀ : (contractRooted Q (· = C)).graph.target p₀ = Quot.mk _ t := by
    change Quot.mk _ (Q.graph.target p) = _
    rw [hp]
  have huniqp₀ : ∀ g, (contractRooted Q (· = C)).graph.target g = Quot.mk _ t → g = p₀ := by
    intro g hg
    have hgt : Q.graph.target g.1 = t := by
      rcases (mk_eq_mk_iff hcyc).1 hg with h | ⟨h, -⟩
      · exact h
      · exact hK.entry g.1 (g.2 C hcyc rfl) h
    exact Subtype.ext (huniqt g.1 hgt)
  have hθp₀ : (contractMetric Q (· = C) θ).inheritance p₀ = 1 := hθp
  have hZ : cherryMass (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) 0
      (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) q =
      cherryMass Q θ 0 (cutInj Q t (taxaInj Q univ) G) q := by
    rw [liftInj_eq_cutInj hN₀ hc₀t hcu₀ _ hinj₀,
      cherryMass_cutInj_eq_upperLaw hN₀ hc₀ hpt₀ huniqp₀ hθp₀,
      cherryMass_cutInj_eq_upperLaw hN hct hp huniqt hθp]
    refine sum_congr rfl fun t'' _ => ?_
    congr 2
    funext F
    exact hK.upperLaw_contract hN hct hp huniqt hN₀ rfl hpt₀ huniqp₀ θ t'' F
  refine ⟨fun _ => ⟨?_, ?_⟩, fun R₁ R₂ hR hroots => ?_⟩
  · rw [hW, union_empty, hZ]
  · rw [hW, empty_union, hZ]
  · rw [hW, hZ]
    have hR₁ : R₁ ∈ roots G := hroots ▸ mem_insert_self _ _
    have hU := (forestBelow_union hgood (singleton_subset_iff.2 hR₁)).1
    have hd : roots G \ {R₁} = {R₂} := by
      rw [hroots]
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h'⟩
        · exact absurd rfl h'
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, fun h' => hR h'.symm⟩
    rw [hd] at hU
    rw [hU]

/-- Lemma 9 when the root `r` is on the cycle: `C` has nodes `r`, `u`, `v` (`u` is `w` in the proof),
and `y` is the other child of `u`; the two taxa not below `v` are below `y`. With one lineage of `v` on
each hybrid edge, one reaches `r` alone and the other reaches `u`, where the lineages from `y` join it;
in `Q₀⊕` the four lineages meet at the contracted root. The proof conditions on the forest at the top
of the edge `g` above `y` (`cherryMass_eq_sum_arc`), whose law the two processes share, as the paper
conditions on `K_y`. If the two lineages from `y` have coalesced (`K_y = 1`), their cluster decides the
quartet tree (`NMSC.cherryMass_of_mem`). If not (`K_y = 2`), the process is the multispecies coalescent
on a four-taxon species tree: `T_c` or `T_d` above the top of `g`, that is `((a,b,x):ℓ,x')` with `x` the
lineage that reaches `u`, `x'` the one that reaches `r` and `ℓ` the length of the edge from `r` to `u`
(`cherryMass_rootArc_eq_quartetProb_erase`), and in `Q₀⊕` the tree `((a,b):l,(c,d):0)` above the top
of `g`, the star tree (`cherryMass_atRoot_eq_quartetProb_univ`). These trees have the same unrooted
metric tree, and the root placement does not matter (`pub:rootplace`,
`quartetProb_cladeSpeciesTree_erase`), which Allman, Degnan, Rhodes 2011 prove (Theorem 9 and
Proposition 11). For this step the paper cites its Propositions 3 and 4, taken from that source, which
as printed state identifiability (see `lemma9`). -/
theorem lemma9_of_root_mem (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 2 2)
    (hroot : Q.root ∈ cycleNodes Q.graph C) {h₁ h₂ : E} (hne : h₁ ≠ h₂)
    (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) (q : QuartetTree X) :
    cf Q θ q =
      θ.inheritance h₁ ^ 2 * cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q +
        (1 - θ.inheritance h₁) ^ 2 * cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q +
        2 * θ.inheritance h₁ * (1 - θ.inheritance h₁) *
          cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) q := by
  obtain ⟨hcyc, hv, h2, hn, hk⟩ := hC
  have hN := hQ.binary.1
  have hθ := hQ.metric.1
  have := hN.finite_arcs
  have hX := hQ.card_taxa
  have hcard : C.ncard = 3 := by
    rw [ite_eq_left hroot] at hn
    omega
  obtain ⟨w, f, g, hwv, hwr, hS3, hfs, hft, hfu, hgs, hgC, hab', hrout, hwout⟩ :=
    shape_of_root_mem hQ.binary hQ.levelOne hcyc hv h2 hroot hcard hne hh₁ hh₂
  have hwC : w ∈ cycleNodes Q.graph C := by rw [hS3]; simp
  set y := Q.graph.target g with hy
  obtain ⟨hcy, huniqy⟩ := isCut_target_of_exit hQ.binary hQ.levelOne hcyc hwC hgs hgC
  have hyr : ¬ Q.graph.Reaches y Q.root := hcy.not_reaches_root
  have hyw : ¬ Q.graph.Reaches y w := fun h =>
    hN.acyclic w (Relation.TransGen.head' ⟨g, hgs, rfl⟩ h)
  have hsrc_v : ∀ e, Q.graph.target e = v → Q.graph.source e = Q.root ∨ Q.graph.source e = w := by
    intro e he
    rcases mem_pair_of_target_of_indegree_eq_two h2 hne hh₁ hh₂ e he with rfl | rfl <;>
      rcases hab' with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact Or.inr h.2
    · exact Or.inl h.2
  have hyv : ¬ Q.graph.Reaches y v := fun h => by
    rcases Relation.ReflTransGen.cases_tail h with h' | ⟨c', hc', e, rfl, he⟩
    · exact hgC (mem_of_target_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 h'.symm)
    · rcases hsrc_v e he with h'' | h''
      · exact hyr (h'' ▸ hc')
      · exact hyw (h'' ▸ hc')
  have hwvr : Q.graph.Reaches w v := reaches_hybrid hQ.binary hQ.levelOne hcyc hv h2 w hwC
  have hdisj : ∀ x, Q.graph.Reaches v x → ¬ Q.graph.Reaches y x := by
    intro x hvx hyx
    obtain ⟨e, hve, hes, het⟩ := exists_arc_enter' (p := fun x => Q.graph.Reaches y x) hvx hyv hyx
    by_cases hey : Q.graph.target e = y
    · rw [huniqy e hey, hgs] at hve
      exact hwv (eq_of_reaches_of_reaches hN.acyclic hwvr hve)
    · exact hes (hcy.entry e het hey)
  have hpart : ∀ x, x = Q.root ∨ x = w ∨ Q.graph.Reaches v x ∨ Q.graph.Reaches y x := by
    intro x
    rcases Relation.ReflTransGen.cases_head (hN.root_reaches x) with h | ⟨z, ⟨e, he, rfl⟩, hz⟩
    · exact Or.inl h.symm
    · rcases hrout e he with h | h
      · exact Or.inr (Or.inr (Or.inl (h ▸ hz)))
      · rw [h] at hz
        rcases Relation.ReflTransGen.cases_head hz with h' | ⟨z', ⟨e', he', rfl⟩, hz'⟩
        · exact Or.inr (Or.inl h'.symm)
        · rcases hwout e' he' with h'' | h''
          · exact Or.inr (Or.inr (Or.inl (h'' ▸ hz')))
          · subst h''
            exact Or.inr (Or.inr (Or.inr hz'))
  have hleaf : ∀ x, Q.graph.Reaches y (Q.leaf x) ↔ ¬ Q.graph.Reaches v (Q.leaf x) := by
    intro x
    refine ⟨fun h h' => hdisj _ h' h, fun h => ?_⟩
    rcases hpart (Q.leaf x) with h' | h' | h' | h'
    · exact absurd (h'.trans hfs.symm) (leaf_ne_source hN x f)
    · exact absurd (h'.trans hgs.symm) (leaf_ne_source hN x g)
    · exact absurd h' h
    · exact h'
  have hSy : ∀ x, Q.graph.Reaches y x → x ∉ cycleNodes Q.graph C := by
    intro x hx hxC
    rw [hS3] at hxC
    rcases hxC with rfl | rfl | hxC
    · exact hyr hx
    · exact hyv hx
    · exact hyw (Set.mem_singleton_iff.1 hxC ▸ hx)
  -- the child edge `c` of `v` and `Q₀⊕`
  obtain ⟨c, hc, hcu⟩ := existsUnique_child_of_hybrid hQ.binary h2
  obtain ⟨hcut, huniq⟩ := isCut_child_of_hybrid hQ.binary hQ.levelOne h2 hc hcu
  have hS : ∀ w, Q.graph.Reaches (Q.graph.target c) w → w ∉ cycleNodes Q.graph C := fun w hw hwC =>
    hN.acyclic v (Relation.TransGen.head' ⟨c, hc, rfl⟩
      (hw.trans (reaches_hybrid hQ.binary hQ.levelOne hcyc hv h2 w hwC)))
  have hcC : c ∉ C := notMem_of_source_eq_hybrid hQ.binary hQ.levelOne hcyc hv h2 hc
  let c₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'} := ⟨c, fun C' _ hC' => hC' ▸ hcC⟩
  have hcut₀ := isCut_contract hcyc hcut hS
  have huniq₀ : ∀ g, (contractRooted Q (· = C)).graph.target g =
      Quot.mk _ (Q.graph.target c) → g = c₀ := fun g hg =>
    Subtype.ext (huniq g.1 ((mk_eq_mk_iff_of_notMem' hcyc (hS _ .refl)).1 hg))
  have hlaw : ∀ G, arcLaw (contractRooted Q (· = C)) _ hcut₀ (contractMetric Q (· = C) θ) 0 c₀
      (taxaInj (contractRooted Q (· = C)) univ) G = arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G := by
    intro G
    unfold arcLaw
    refine sum_congr rfl fun F₁ _ => ?_
    rw [rootDist_cutLower_contract hcyc hcut hS θ 0 F₁]
    rfl
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ.binary hQ.levelOne hcyc hv h2
  have hN₀ := hK.isPhylogenetic hN
  have hθ₀ := hK.isMetric hθ
  have hcr₀ : (contractRooted Q (· = C)).graph.target c₀ = Quot.mk _ (Q.graph.target c) := rfl
  have hmkr : ∀ x ∈ cycleNodes Q.graph C,
      (Quot.mk (RootedContractRel Q (· = C)) x) = Quot.mk _ Q.root := fun x hx =>
    (mk_eq_mk_iff hcyc).2 (Or.inr ⟨hx, hroot⟩)
  have hc₀s : (contractRooted Q (· = C)).graph.source c₀ = Quot.mk _ Q.root := by
    change Quot.mk _ (Q.graph.source c) = _
    rw [hc]
    exact hmkr v hv
  -- the arc `g` in `Q₀⊕`
  let g₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'} := ⟨g, fun C' _ hC' => hC' ▸ hgC⟩
  have hcy₀ := isCut_contract hcyc hcy hSy
  have hgt₀ : (contractRooted Q (· = C)).graph.target g₀ = Quot.mk _ y := rfl
  have huniqy₀ : ∀ e, (contractRooted Q (· = C)).graph.target e = Quot.mk _ y → e = g₀ :=
    fun e he => Subtype.ext (huniqy e.1 ((mk_eq_mk_iff_of_notMem' hcyc (hSy _ .refl)).1 he))
  have hg₀s : (contractRooted Q (· = C)).graph.source g₀ = Quot.mk _ Q.root := by
    change Quot.mk _ (Q.graph.source g) = _
    rw [hgs]
    exact hmkr w hwC
  have hθg : θ.inheritance g = 1 := hθ.2.2.1 g (isTreeArc_of_unique rfl huniqy)
  have hθg₀ : (contractMetric Q (· = C) θ).inheritance g₀ = 1 := hθg
  -- the vertices of `Q₀⊕`: the root, below `c₀` or below `g₀`
  have hpart₀ : ∀ u, u = Quot.mk _ Q.root ∨ u ∈ belowSet (contractRooted Q (· = C)) c₀ ∨
      u ∈ belowSet (contractRooted Q (· = C)) g₀ := by
    intro u
    induction u using Quot.ind with
    | mk x =>
      rcases hpart x with rfl | rfl | h | h
      · exact Or.inl rfl
      · exact Or.inl (hmkr _ hwC)
      · rcases eq_or_reaches_of_unique_child hcu h with rfl | h'
        · exact Or.inl (hmkr _ hv)
        · exact Or.inr (Or.inl (mem_belowSet.2 (reaches_contract_of_reaches hS h')))
      · exact Or.inr (Or.inr (mem_belowSet.2 (reaches_contract_of_reaches hSy h)))
  have hnotc : Quot.mk (RootedContractRel Q (· = C)) Q.root ∉
      belowSet (contractRooted Q (· = C)) c₀ := hc₀s ▸ source_notMem_belowSet hN₀ c₀
  have hnotg : Quot.mk (RootedContractRel Q (· = C)) Q.root ∉
      belowSet (contractRooted Q (· = C)) g₀ := hg₀s ▸ source_notMem_belowSet hN₀ g₀
  have hinjr₀ : taxaInj (contractRooted Q (· = C)) univ (Quot.mk _ Q.root) = ∅ := by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    exact leaf_ne_source hN₀ x c₀ ((mem_filter.1 hx).2.2.trans hc₀s.symm)
  refine cf_eq_of_two_two_of_split hQ ⟨hcyc, hv, h2, hn, hk⟩ hne hh₁ hh₂ hc hcu hcut huniq c₀ rfl
    hcut₀ huniq₀ hlaw q fun G hG => ?_
  obtain ⟨hgood, hlin⟩ := good_of_arcLaw_ne_zero hN hcut (validInj_taxaInj univ) hG
  have hlin' : ∀ x, x ∈ lineages G ↔ Q.graph.Reaches v (Q.leaf x) := fun x => by
    rw [hlin, reaches_leaf_iff_of_hybrid hQ.binary h2 hc hcu]
    constructor
    · rintro ⟨u, hu, hx⟩
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hx
      exact hu
    · exact fun h => ⟨_, h, mem_lineages_taxaInj.2 ⟨mem_univ _, rfl⟩⟩
  have hcardG : #(lineages G) = 2 := by
    rw [← hk, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [hlin']
  have hsrc12 : Q.graph.source h₁ ≠ Q.graph.source h₂ := by
    rcases hab' with h | h
    · rw [h.1, h.2]
      exact fun h' => hwr h'.symm
    · rw [h.1, h.2]
      exact hwr
  have hinjs : ∀ e, taxaInj Q univ (Q.graph.source e) = ∅ := fun e => by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    exact leaf_ne_source hN x e (mem_filter.1 hx).2.2
  have hsv : ∀ e, Q.graph.target e = v → ¬ Q.graph.Reaches v (Q.graph.source e) := fun e he h =>
    hN.acyclic v (Relation.TransGen.tail' h ⟨e, rfl, he⟩)
  have hvalid : ∀ t₁ t₂ : Finset (Finset X), IsGoodForest t₁ → IsGoodForest t₂ →
      Disjoint (lineages t₁) (lineages t₂) →
      (∀ x, x ∈ lineages t₁ ∨ x ∈ lineages t₂ → Q.graph.Reaches v (Q.leaf x)) →
      ValidInj (hybInj Q v h₁ h₂ (taxaInj Q univ) t₁ t₂) := fun t₁ t₂ hg₁ hg₂ hd hl =>
    validInj_hybInj (validInj_taxaInj univ) hg₁ hg₂ hd hsrc12 (hinjs h₁) (hinjs h₂)
      fun x hx u hvu hxu => by
        obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
        exact hvu (hl x hx)
  have hDq : lineages G ⊆ q.taxa := by rw [taxa_eq_univ hX q]; exact subset_univ _
  refine ⟨fun h1r => ?_, fun R₁ R₂ hR hroots => ?_⟩
  · -- one root: the cluster of the two lineages decides the quartet tree
    have hD := lineages_mem_of_card_roots_eq_one h1r
    have hZ : cherryMass (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) 0
        (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) q =
        if lineages G ∈ q.val then 1 else 0 :=
      cherryMass_of_mem hN₀ hθ₀ ⟨le_rfl, zero_le_one⟩ (validInj_of_arcLaw_ne_zero hN₀ hcut₀ hcr₀
        (validInj_taxaInj univ) (by rw [hlaw]; exact hG))
        (v := (contractRooted Q (· = C)).graph.source c₀)
        (by simp only [liftInj, ite_true]; exact mem_union_right _ hD) hcardG hDq
    have hW : ∀ (e : E) (t₁ t₂ : Finset (Finset X)), Q.graph.target e = v →
        (Q.graph.source e = Q.graph.source h₁ → t₁ = G) →
        (Q.graph.source e = Q.graph.source h₂ → t₂ = G) → (t₁ = ∅ ∨ t₂ = ∅) →
        ValidInj (hybInj Q v h₁ h₂ (taxaInj Q univ) t₁ t₂) →
        cherryMass Q θ 0 (hybInj Q v h₁ h₂ (taxaInj Q univ) t₁ t₂) q =
          if lineages G ∈ q.val then 1 else 0 := by
      intro e t₁ t₂ he h₁' h₂' _ hJ
      refine cherryMass_of_mem hN hθ ⟨le_rfl, zero_le_one⟩ hJ (v := Q.graph.source e) ?_ hcardG hDq
      unfold hybInj
      rw [ite_eq_right (hsv e he)]
      rcases mem_pair_of_target_of_indegree_eq_two h2 hne hh₁ hh₂ e he with rfl | rfl
      · rw [h₁' rfl]
        exact mem_union_right _ (mem_union_left _ (by rw [ite_eq_left rfl]; exact hD))
      · rw [h₂' rfl]
        exact mem_union_right _ (mem_union_right _ (by rw [ite_eq_left rfl]; exact hD))
    have hlinD : ∀ x, x ∈ lineages G ∨ x ∈ lineages (∅ : Finset (Finset X)) →
        Q.graph.Reaches v (Q.leaf x) := fun x hx => by
      rcases hx with hx | hx
      · exact (hlin' x).1 hx
      · simp [lineages] at hx
    have hlinD' : ∀ x, x ∈ lineages (∅ : Finset (Finset X)) ∨ x ∈ lineages G →
        Q.graph.Reaches v (Q.leaf x) := fun x hx => hlinD x hx.symm
    refine ⟨?_, ?_⟩
    · rw [hZ, hW h₁ G ∅ hh₁ (fun _ => rfl) (fun h => absurd h hsrc12) (Or.inr rfl)
        (hvalid G ∅ hgood isGoodForest_empty (by simp [lineages]) hlinD)]
    · rw [hZ, hW h₂ ∅ G hh₂ (fun h => absurd h.symm hsrc12) (fun _ => rfl) (Or.inl rfl)
        (hvalid ∅ G isGoodForest_empty hgood (by simp [lineages]) hlinD')]
  · -- two roots: one lineage on each hybrid edge
    have hR₁ : R₁ ∈ roots G := hroots ▸ mem_insert_self _ _
    have hR₂ : R₂ ∈ roots G := hroots ▸ mem_insert_of_mem (mem_singleton_self _)
    have hsum := hgood.1.sum_card_roots
    rw [hroots, sum_pair hR, hcardG] at hsum
    have hp₁ := (hgood.1.1 R₁ (roots_subset G hR₁)).card_pos
    have hp₂ := (hgood.1.1 R₂ (roots_subset G hR₂)).card_pos
    obtain ⟨x₁, rfl⟩ := card_eq_one.1 (show #R₁ = 1 by omega)
    obtain ⟨x₂, rfl⟩ := card_eq_one.1 (show #R₂ = 1 by omega)
    have hx₁₂ : x₁ ≠ x₂ := fun h => hR (by rw [h])
    have hfb : ∀ x, {x} ∈ roots G → forestBelow G {{x}} = {{x}} := by
      intro x hx
      ext B
      simp only [mem_forestBelow, mem_singleton, exists_eq_left]
      constructor
      · rintro ⟨hB, hBx⟩
        rcases subset_singleton_iff.1 hBx with rfl | h
        · exact absurd (hgood.1.1 ∅ hB) (by simp)
        · exact h
      · rintro rfl
        exact ⟨roots_subset G hx, subset_rfl⟩
    have hg₁ : IsGoodForest ({{x₁}} : Finset (Finset X)) :=
      hfb x₁ hR₁ ▸ isGoodForest_forestBelow hgood
    have hg₂ : IsGoodForest ({{x₂}} : Finset (Finset X)) :=
      hfb x₂ hR₂ ▸ isGoodForest_forestBelow hgood
    have hGeq : G = {{x₁}, {x₂}} := by
      have hU := (forestBelow_union hgood (singleton_subset_iff.2 hR₁)).1
      have hd : roots G \ {{x₁}} = {{x₂}} := by
        rw [hroots]
        ext x
        simp only [mem_sdiff, mem_insert, mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, h'⟩
          · exact absurd rfl h'
          · rfl
        · rintro rfl
          exact ⟨Or.inr rfl, fun h' => hR h'.symm⟩
      rw [hd, hfb x₁ hR₁, hfb x₂ hR₂] at hU
      rw [← hU, insert_eq]
    have hbelowv : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = x₁ ∨ x = x₂ := fun x => by
      rw [← hlin', hGeq]
      simp [lineages]
    rw [hfb x₁ hR₁, hfb x₂ hR₂]
    set J := hybInj Q v h₁ h₂ (taxaInj Q univ) {{x₁}} {{x₂}} with hJdef
    have hJ : ValidInj J := hvalid _ _ hg₁ hg₂ (by simp [hx₁₂]) fun x hx => by
      rw [hbelowv]
      simpa using hx
    have hJu : ∀ u, ¬ Q.graph.Reaches v u → J u = taxaInj Q univ u ∪
        ((if u = Q.graph.source h₁ then {{x₁}} else ∅) ∪
          (if u = Q.graph.source h₂ then {{x₂}} else ∅)) := fun u hu => by
      rw [hJdef]
      unfold hybInj
      rw [ite_eq_right hu]
    -- the lineage that reaches the root, and the one that reaches `w`
    have hvr : v ≠ Q.root := fun h => by
      have := hN.root_indegree
      rw [← h, h2] at this
      exact absurd this (by norm_num)
    have hvr' : ¬ Q.graph.Reaches v Q.root := fun h =>
      hvr (eq_of_reaches_of_reaches hN.acyclic h (hN.root_reaches v))
    have hvw' : ¬ Q.graph.Reaches v w := fun h => hwv (eq_of_reaches_of_reaches hN.acyclic hwvr h)
    have hinjr : taxaInj Q univ Q.root = ∅ := hfs ▸ hinjs f
    have hinjw : taxaInj Q univ w = ∅ := hgs ▸ hinjs g
    obtain ⟨xr, xw, hrw, hxne, hJr, hJw⟩ : ∃ xr xw, (xr = x₁ ∧ xw = x₂ ∨ xr = x₂ ∧ xw = x₁) ∧
        xr ≠ xw ∧ J Q.root = {{xr}} ∧ J w = {{xw}} := by
      rcases hab' with ⟨h₁r, h₂w⟩ | ⟨h₁w, h₂r⟩
      · refine ⟨x₁, x₂, Or.inl ⟨rfl, rfl⟩, hx₁₂, ?_, ?_⟩
        · rw [hJu _ hvr', hinjr, ite_eq_left h₁r.symm, ite_eq_right (h₂w ▸ fun h => hwr h.symm),
            union_empty, empty_union]
        · rw [hJu _ hvw', hinjw, ite_eq_right (h₁r ▸ hwr), ite_eq_left h₂w.symm, empty_union, empty_union]
      · refine ⟨x₂, x₁, Or.inr ⟨rfl, rfl⟩, hx₁₂.symm, ?_, ?_⟩
        · rw [hJu _ hvr', hinjr, ite_eq_right (h₁w ▸ fun h => hwr h.symm), ite_eq_left h₂r.symm,
            empty_union, empty_union]
        · rw [hJu _ hvw', hinjw, ite_eq_left h₁w.symm, ite_eq_right (h₂r ▸ hwr), union_empty, empty_union]
    have hvx : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = xr ∨ x = xw := fun x => by
      rw [hbelowv]
      rcases hrw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Iff.rfl
      · exact or_comm
    -- the forest at the top of the edge above `y`
    rw [cherryMass_eq_sum_arc hN hcy rfl huniqy hθg J q,
      cherryMass_eq_sum_arc hN₀ hcy₀ hgt₀ huniqy₀ hθg₀ _ q]
    refine sum_congr rfl fun t₃ _ => ?_
    have hlawJ : arcLaw Q y hcy θ 0 g J t₃ = arcLaw Q y hcy θ 0 g (taxaInj Q univ) t₃ := by
      have hlow : lowerInj (cutVertices Q y) J = lowerInj (cutVertices Q y) (taxaInj Q univ) := by
        funext u
        unfold lowerInj
        rw [cutVertices_inr, hJu _ fun h => hdisj _ h u.2]
        have hne₁ : u.1 ≠ Q.graph.source h₁ := fun h' => by
          have hu := u.2
          rcases hab' with h | h
          · rw [h', h.1] at hu
            exact hyr hu
          · rw [h', h.1] at hu
            exact hyw hu
        have hne₂ : u.1 ≠ Q.graph.source h₂ := fun h' => by
          have hu := u.2
          rcases hab' with h | h
          · rw [h', h.2] at hu
            exact hyw hu
          · rw [h', h.2] at hu
            exact hyr hu
        rw [ite_eq_right hne₁, ite_eq_right hne₂, union_empty, union_empty]
      unfold arcLaw
      rw [hlow]
    have hlaw₀ : arcLaw (contractRooted Q (· = C)) (Quot.mk _ y) hcy₀ (contractMetric Q (· = C) θ) 0
        g₀ (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) t₃ =
        arcLaw Q y hcy θ 0 g (taxaInj Q univ) t₃ := by
      have hlow₀ : lowerInj (cutVertices (contractRooted Q (· = C)) (Quot.mk _ y))
          (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) =
          lowerInj (cutVertices (contractRooted Q (· = C)) (Quot.mk _ y))
            (taxaInj (contractRooted Q (· = C)) univ) := by
        funext u
        unfold lowerInj
        rw [cutVertices_inr]
        obtain ⟨x, hx, hxu⟩ := exists_of_reaches_contract hcyc hSy u.2
        have hnb : u.1 ∉ belowSet (contractRooted Q (· = C)) c₀ := by
          intro hm
          rw [mem_belowSet, ← hxu] at hm
          exact hdisj x ((Relation.ReflTransGen.single ⟨c, hc, rfl⟩).trans
            ((reaches_contract_iff hcyc hS x).1 hm)) hx
        have hns : u.1 ≠ (contractRooted Q (· = C)).graph.source c₀ := by
          rw [hc₀s, ← hxu]
          intro h
          have := (mk_eq_mk_iff_of_notMem hcyc (hSy x hx)).1 h
          exact hSy x hx (this ▸ hroot)
        unfold liftInj
        rw [ite_eq_right hnb, ite_eq_right hns, union_empty]
      unfold arcLaw
      rw [hlow₀]
      refine sum_congr rfl fun F₁ _ => ?_
      rw [rootDist_cutLower_contract hcyc hcy hSy θ 0 F₁]
      rfl
    rw [hlawJ, hlaw₀]
    by_cases h0 : arcLaw Q y hcy θ 0 g (taxaInj Q univ) t₃ = 0
    · rw [h0, zero_mul, zero_mul]
    congr 1
    obtain ⟨hg₃, hl₃⟩ := good_of_arcLaw_ne_zero hN hcy (validInj_taxaInj univ) h0
    have hl₃' : ∀ x, x ∈ lineages t₃ ↔ ¬ Q.graph.Reaches v (Q.leaf x) := fun x => by
      rw [hl₃, ← hleaf]
      constructor
      · rintro ⟨u, hu, hx⟩
        obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hx
        exact hu
      · exact fun h => ⟨_, h, mem_lineages_taxaInj.2 ⟨mem_univ _, rfl⟩⟩
    have hwnb : w ∉ belowSet Q g := hgs ▸ source_notMem_belowSet hN g
    have hrnb : Q.root ∉ belowSet Q g := root_notMem_belowSet hN g
    have hLw : liftInj Q g J t₃ w = {{xw}} ∪ t₃ := by
      unfold liftInj
      rw [ite_eq_right hwnb, ite_eq_left hgs.symm, hJw]
    have hLr : liftInj Q g J t₃ Q.root = {{xr}} := by
      unfold liftInj
      have hrg : Q.root ≠ Q.graph.source g := by rw [hgs]; exact fun h => hwr h.symm
      rw [ite_eq_right hrnb, ite_eq_right hrg, hJr, union_empty]
    have hlJ : arcLaw Q y hcy θ 0 g J t₃ ≠ 0 := by rw [hlawJ]; exact h0
    have hvJ := validInj_of_arcLaw_ne_zero hN hcy rfl hJ hlJ
    -- in `Q₀⊕`: the four lineages at the contracted root
    have heq : liftInj (contractRooted Q (· = C)) g₀
        (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) t₃ =
        atInj (Quot.mk _ Q.root) (G ∪ t₃) := by
      funext u
      unfold liftInj
      rcases hpart₀ u with rfl | h | h
      · rw [atInj_self, ite_eq_right hnotg, ite_eq_left hg₀s.symm, ite_eq_right hnotc, ite_eq_left hc₀s.symm, hinjr₀,
          empty_union]
      · have hur : u ≠ Quot.mk _ Q.root := fun h' => hnotc (h' ▸ h)
        have hug : u ≠ (contractRooted Q (· = C)).graph.source g₀ := by rw [hg₀s]; exact hur
        have huc : u ≠ (contractRooted Q (· = C)).graph.source c₀ := by rw [hc₀s]; exact hur
        rw [atInj_of_ne hur, ite_eq_right hug, union_empty]
        split_ifs <;> simp
      · have hur : u ≠ Quot.mk _ Q.root := fun h' => hnotg (h' ▸ h)
        have hug : u ≠ (contractRooted Q (· = C)).graph.source g₀ := by rw [hg₀s]; exact hur
        rw [atInj_of_ne hur, ite_eq_left h, ite_eq_right hug, union_empty]
    have hdisj₃ : Disjoint (lineages G) (lineages t₃) := disjoint_left.2 fun x hx hx' =>
      (hl₃' x).1 hx' ((hlin' x).1 hx)
    have hv₀ : ValidInj (atInj (Quot.mk (RootedContractRel Q (· = C)) Q.root) (G ∪ t₃)) :=
      validInj_atInj _ (hgood.union hg₃ hdisj₃)
    have hDq : ∀ D : Finset X, D ⊆ q.taxa := fun D => by
      rw [taxa_eq_univ hX q]
      exact subset_univ _
    rw [heq]
    by_cases hC2 : ∃ D ∈ t₃, #D = 2
    · -- `K_y = 1`: the coalescence below the top of `g` decides the quartet tree in both networks
      obtain ⟨D, hD, hD2⟩ := hC2
      rw [cherryMass_of_mem hN hθ ⟨le_rfl, zero_le_one⟩ hvJ (v := w)
          (by rw [hLw]; exact mem_union_right _ hD) hD2 (hDq D),
        cherryMass_of_mem hN₀ hθ₀ ⟨le_rfl, zero_le_one⟩ hv₀ (v := Quot.mk _ Q.root)
          (by rw [atInj_self]; exact mem_union_right _ hD) hD2 (hDq D)]
    -- `K_y = 2`: the multispecies coalescent on a four-taxon species tree, `T_c` or `T_d` above the
    -- top of `g` (`((a,b,c):ℓ,d)` or `((a,b,d):ℓ,c)` with `ℓ` the length of `f`) in `Q⊕`, and the star
    -- tree in `Q₀⊕`
    have hlin₃ : ∀ x, x ∈ lineages t₃ ↔ x ≠ xr ∧ x ≠ xw := fun x => by
      rw [hl₃', hvx, not_or]
    have ht₃ : t₃ = (lineages t₃).image fun x => {x} := hg₃.eq_singletons hC2
    have hS₃ : (univ.erase xr).Nonempty := ⟨xw, mem_erase.2 ⟨hxne.symm, mem_univ _⟩⟩
    have hU : (univ : Finset X).Nonempty := ⟨xr, mem_univ _⟩
    have hwF : {{xw}} ∪ t₃ = (univ.erase xr).image fun x => {x} := by
      rw [ht₃]
      ext D
      simp only [mem_union, mem_singleton, mem_image, mem_erase, mem_univ, and_true, hlin₃]
      constructor
      · rintro (rfl | ⟨x, ⟨hx, -⟩, rfl⟩)
        · exact ⟨xw, hxne.symm, rfl⟩
        · exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        by_cases hxw : x = xw
        · exact Or.inl (by rw [hxw])
        · exact Or.inr ⟨x, ⟨hx, hxw⟩, rfl⟩
    have hGF : G ∪ t₃ = univ.image fun x => {x} := by
      rw [ht₃, hGeq]
      ext D
      simp only [mem_union, mem_insert, mem_singleton, mem_image, mem_univ, true_and, hlin₃]
      constructor
      · rintro ((rfl | rfl) | ⟨x, -, rfl⟩)
        · exact ⟨x₁, rfl⟩
        · exact ⟨x₂, rfl⟩
        · exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        by_cases hxr : x = xr
        · rcases hrw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl (Or.inl (by rw [hxr]))
          · exact Or.inl (Or.inr (by rw [hxr]))
        by_cases hxw : x = xw
        · rcases hrw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl (Or.inr (by rw [hxw]))
          · exact Or.inl (Or.inl (by rw [hxw]))
        · exact Or.inr ⟨x, ⟨hxr, hxw⟩, rfl⟩
    have hat : atInj (Quot.mk (RootedContractRel Q (· = C)) Q.root) (G ∪ t₃) =
        atRoot (contractRooted Q (· = C)) (univ.image fun x => {x}) := by
      funext u
      by_cases hu : u = Quot.mk _ Q.root
      · rw [hu, atInj_self, hGF]
        exact (atRoot_root _ _).symm
      · rw [atInj_of_ne hu]
        exact (atRoot_of_ne _ _ hu).symm
    have hfu' : ∀ e, Q.graph.target e = Q.graph.target f → e = f := fun e he => hfu e (he.trans hft)
    have h1f : θ.inheritance f = 1 := hθ.2.2.1 f (isTreeArc_of_unique rfl hfu')
    have hinjL : ∀ u, u ≠ Q.root → u ≠ Q.graph.target f → liftInj Q g J t₃ u = ∅ := by
      intro u hur huw
      rw [hft] at huw
      have hug : u ≠ Q.graph.source g := by rw [hgs]; exact huw
      unfold liftInj
      rw [ite_eq_right hug, union_empty]
      rcases hpart u with h | h | h | h
      · exact absurd h hur
      · exact absurd h huw
      · rw [ite_eq_right fun h' => hdisj u h (mem_belowSet.1 h'), hJdef]
        unfold hybInj
        rw [ite_eq_left h]
      · rw [ite_eq_left (mem_belowSet.2 h)]
    rw [cherryMass_rootArc_eq_quartetProb_erase hX hN.acyclic (NMSC.target_ne_root hN) hfs hfu' h1f
        (hQ.metric.2 f) le_rfl hinjL hS₃ (by rw [hft, hLw, hwF]) hLr q, hat,
      cherryMass_atRoot_eq_quartetProb_univ hX hN₀.acyclic (NMSC.target_ne_root hN₀) _ 0 hU q]
    exact quartetProb_cladeSpeciesTree_erase hX xr hS₃ _ _ hU 1 one_pos q

/-- **Lemma 9** (`lem::formula2:2`): for a cycle inducing a `2₂`-cycle, with hybrid edges `h₁`, `h₂` of
its hybrid node `v` and `γ = γ(h₁)`,
`CF(Q⊕) = γ² CF(Q₁⊕) + (1 - γ)² CF(Q₂⊕) + 2γ(1 - γ) CF(Q₀⊕)`.

The paper's proof: with `K` the number of lineages at `v`, the lineages at `v` take `h₁` or `h₂`
(`cf_eq_of_two_two_of_split`); all of them on `h₁`, or all on `h₂`, is the process of `Q₁⊕`, or of
`Q₂⊕`, and for `K = 1` the topology is decided before `v`. With `K = 2` and one lineage on each hybrid
edge: if the root is not on `C`, both lineages meet at the top of `C`, as in `Q₀⊕`
(`lemma9_of_root_notMem`); if the root `r` is on `C`, with `y` the other child of the node `u` of
`C`, the paper conditions on `K_y`, the number of lineages at `y` (`lemma9_of_root_mem`): for
`K_y = 1` the topology is decided; for `K_y = 2` the process is that of a tree `T_c` or `T_d`, that
of `Q₀⊕` given `K = K_y = 2` is that of the tree `((a,b):l,(c,d):0)` with `l` the length of the edge
from `u` to `y`, and the three have the same concordance factors.

For `K = K_y = 2` the paper concludes `CF(T_d | K_y = 2) = CF(T_c | K_y = 2)` "by Proposition 3" and
`CF(T_c | K_y = 2) = CF(Q₀⊕ | K = 2, K_y = 2)` "by Proposition 4", which it takes from Allman, Degnan,
Rhodes 2011 (arXiv v1: "Proposition 3 in [Allman2011]" and "Proposition 11 in [Allman2011]"). As
printed in the paper, Proposition 3 states that for four taxa the unrooted metric species tree is
identifiable from the distribution of unrooted gene trees and the rooted one is not, and Proposition 4
that this remains valid for non-binary trees: these are identifiability statements, not the invariance
of the concordance factors under the root placement. The step uses that the root placement does not
matter, which Allman, Degnan, Rhodes 2011 prove (`pub:rootplace`: the source's Theorem 9 and
Proposition 11, `External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`): `T_c`,
`T_d` and the tree of `Q₀⊕` have the same unrooted metric tree. `K_y` is read at the top of the edge
above `y`, and the trees are taken above it. -/
theorem lemma9 (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 2 2) {h₁ h₂ : E}
    (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) (q : QuartetTree X) :
    cf Q θ q =
      θ.inheritance h₁ ^ 2 * cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q +
        (1 - θ.inheritance h₁) ^ 2 * cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q +
        2 * θ.inheritance h₁ * (1 - θ.inheritance h₁) *
          cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) q := by
  by_cases hroot : Q.root ∈ cycleNodes Q.graph C
  · exact lemma9_of_root_mem hQ hC hroot hne hh₁ hh₂ q
  · exact lemma9_of_root_notMem hQ hC hroot hne hh₁ hh₂ q

/-- A cycle inducing a 4-cycle of `Q⁻` has a single taxon below its hybrid node (Section 5, before
Lemma 7: "if `C'_v` has size four then `l_v = 1`", as Figure 9 shows): the four nodes of the cycle
other than the root have pairwise disjoint nonempty blocks, and the block of the hybrid node is the
set of taxa below it (`add_le_of_inducesCycleType`). -/
theorem le_one_below_of_four (hQ : IsLSAQuartet Q θ) {k : ℕ} (hC : InducesCycleType Q C v 4 k)
    (x y : X) (hx : Q.graph.Reaches v (Q.leaf x)) (hy : Q.graph.Reaches v (Q.leaf y)) : x = y := by
  obtain ⟨h, -, -⟩ := add_le_of_inducesCycleType hQ.binary hQ.levelOne hQ.isLSA hC
  rw [hQ.card_taxa] at h
  have hk : {x | Q.graph.Reaches v (Q.leaf x)}.ncard ≤ 1 := by
    rw [hC.2.2.2.2]
    omega
  exact (Set.ncard_le_one (Set.toFinite _)).1 hk x hx y hy

/-- **Lemma 10** (`lem::formula43:1`): for a cycle inducing a 4-cycle or a `3₁`-cycle,
`CF(Q⊕) = γ CF(Q₁⊕) + (1 - γ) CF(Q₂⊕)`.

The paper's proof: one taxon is below `v`, so exactly one lineage reaches `v` (`P(K = 1) = 1`); it
takes `h₁` with probability `γ` and `h₂` otherwise, and the process is then that of `Q₁⊕` or `Q₂⊕`.
This is `cf_eq_mixture`: the weight of a history is affine in `(γ, 1 - γ)` when a single lineage
passes `v` (`NMSC.nmscCF_withPair`), and the endpoints `(1, 0)` and `(0, 1)` are the networks without
`h₂` and without `h₁` (`cf_deleteArc`). -/
theorem lemma10 (hQ : IsLSAQuartet Q θ)
    (hC : (∃ k, InducesCycleType Q C v 4 k) ∨ InducesCycleType Q C v 3 1) {h₁ h₂ : E}
    (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) (q : QuartetTree X) :
    cf Q θ q =
      θ.inheritance h₁ * cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q +
        (1 - θ.inheritance h₁) * cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q := by
  have h2 : Q.graph.indegree v = 2 := by
    rcases hC with ⟨k, hC⟩ | hC
    · exact hC.2.2.1
    · exact hC.2.2.1
  -- one taxon below `v`: `P(K = 1) = 1`
  have hone : ∀ x y, Q.graph.Reaches (Q.graph.target h₁) (Q.leaf x) →
      Q.graph.Reaches (Q.graph.target h₁) (Q.leaf y) → x = y := by
    rw [hh₁]
    rcases hC with ⟨k, hC⟩ | hC
    · exact le_one_below_of_four hQ hC
    · intro x y hx hy
      have h1 : {x | Q.graph.Reaches v (Q.leaf x)}.ncard = 1 := hC.2.2.2.2
      obtain ⟨z, hz⟩ := Set.ncard_eq_one.1 h1
      have hxz : x ∈ ({z} : Set X) := hz ▸ hx
      have hyz : y ∈ ({z} : Set X) := hz ▸ hy
      exact (Set.mem_singleton_iff.1 hxz).trans (Set.mem_singleton_iff.1 hyz).symm
  exact cf_eq_mixture hQ.binary.1 hQ.metric.1 hne (hh₁.trans hh₂.symm)
    (fun f hf => mem_pair_of_target_of_indegree_eq_two h2 hne hh₁ hh₂ f (hf.trans hh₂))
    (inheritance_add_eq_one hQ.metric.1 h2 hne hh₁ hh₂) hone q

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The two hybrid edges of a cycle with at least three edges leave distinct nodes: two parallel
edges would form a cycle of their own, which shares an edge with `C`. -/
theorem source_ne_of_three_le_ncard (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    (hcyc : IsCycle Q.graph C) (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2)
    (h3 : 3 ≤ C.ncard) {h₁ h₂ : E} (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v)
    (hh₂ : Q.graph.target h₂ = v) : Q.graph.source h₁ ≠ Q.graph.source h₂ := by
  have := hQ.1.finite_arcs
  intro hs
  have hw : Q.graph.Walks {h₂} (Q.graph.target h₁) (Q.graph.source h₁) :=
    .single ⟨h₂, Set.mem_singleton h₂, Or.inr ⟨hs.symm, hh₂.trans hh₁.symm⟩⟩
  obtain ⟨C', hC', hh₁C', hsub⟩ := exists_isCycle_of_walks (F := {h₂})
    (fun h => hne (Set.mem_singleton_iff.1 h)) hw
  have hC : C' = C := h1 C' C hC' hcyc
    ⟨h₁, hh₁C', mem_of_target_eq_hybrid hQ h1 hcyc hv h2 hh₁⟩
  rw [hC] at hsub
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hne] at this
  omega

/-- **`Q_a⊕` is the network with the lineages of `a` and `b` at the sources of `h₁` and `h₂`**: in
`disjointNet Q v h₁ h₂ a b` the leaves of `a` and `b` hang from the sources of `h₁` and `h₂` by these
edges, each carrying a single lineage, and the rest is the part of `Q⊕` not below `v`. -/
theorem cf_disjointNet_eq_cherryMass (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 3 2)
    {h₁ h₂ : E} (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v)
    {a b : X} (hab : a ≠ b) (ha : Q.graph.Reaches v (Q.leaf a))
    (hb : Q.graph.Reaches v (Q.leaf b)) (q : QuartetTree X) :
    cf (disjointNet Q v h₁ h₂ a b) (disjointMetric Q v h₁ h₂ θ) q =
      cherryMass Q θ 0 (hybInj Q v h₁ h₂ (taxaInj Q univ) {{a}} {{b}}) q := by
  obtain ⟨-, -, h2, -, hk⟩ := hC
  -- the taxa below `v` are `a` and `b`
  have hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b := by
    have hsub : ({a, b} : Set X) ⊆ {x | Q.graph.Reaches v (Q.leaf x)} := by
      rintro x (rfl | rfl)
      · exact ha
      · exact hb
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hk, Set.ncard_pair hab])
      (Set.toFinite _)
    intro x
    rw [← Set.mem_ofPred_eq (p := fun x => Q.graph.Reaches v (Q.leaf x)), ← heq]
    rfl
  have hD := disjointNet_isPhylogenetic hQ.binary hQ.levelOne h2 hne hh₁ hh₂ hab hbelow
  have hnorm := disjointNet_isNormalized hQ.binary hQ.levelOne h2 hne hh₁ hh₂ hab hbelow
    hQ.metric.1.isNormalized
  have hsum := inheritance_add_eq_one hQ.metric.1 h2 hne hh₁ hh₂
  rw [cf, nmscCF_eq_cherryMass_weak hD hnorm le_rfl, taxa_eq_univ hQ.card_taxa q,
    cherryMass_eq_cherryOf, cherryMass_eq_cherryOf]
  congr 1
  funext F
  rw [rootDist_disjointNet hQ.binary hQ.levelOne h2 hne hh₁ hh₂ hab hbelow θ F,
    rootDist_hybInj hQ.binary.1 (isCut_hybrid hQ.binary hQ.levelOne h2) hne hh₁ hh₂
      (hpar_of_hybrid hQ.binary h2 hne hh₁ hh₂) (γ := θ.inheritance h₁) rfl (by linarith)]

/-- **Lemma 11** (`lem::formula3:2`): for a cycle inducing a `3₂`-cycle whose hybrid node `v` has the
taxa `a`, `b` below it, with `K` the number of lineages at `v` (at the top of its child edge `c`),
`CF(Q⊕) = γ² CF(Q₁⊕) + (1 - γ)² CF(Q₂⊕) + P(K = 1) 2γ(1 - γ) CF(Q₀⊕ | K = 1)
  + P(K = 2) γ(1 - γ) [CF(Q_a⊕) + CF(Q_b⊕)]`.

The paper's proof: the forest of the lineages of `a`, `b` at `v` splits between `h₁` and `h₂`
(`cherryMass_cutInj_hybrid`); all its lineages on `h₁`, or on `h₂`, is the process of `Q₁⊕`, or of
`Q₂⊕` (`cf_deleteArc`). For `K = 1` the cluster `{a, b}` decides the quartet tree in every network,
and for `K = 2`, with the two lineages on different hybrid edges, the process is that of `Q_a⊕` or of
`Q_b⊕` (`cf_disjointNet_eq_cherryMass`). -/
theorem lemma11 (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 3 2) {h₁ h₂ : E}
    (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) {c : E}
    (hc : Q.graph.source c = v) (c₀ : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'})
    (hc₀ : c₀.1 = c) {a b : X} (hab : a ≠ b) (ha : Q.graph.Reaches v (Q.leaf a))
    (hb : Q.graph.Reaches v (Q.leaf b)) (q : QuartetTree X) :
    cf Q θ q =
      θ.inheritance h₁ ^ 2 * cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q +
        (1 - θ.inheritance h₁) ^ 2 * cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q +
        probLineages Q θ c 1 * (2 * θ.inheritance h₁ * (1 - θ.inheritance h₁)) *
          condCF (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) c₀ 1 q +
        probLineages Q θ c 2 * (θ.inheritance h₁ * (1 - θ.inheritance h₁)) *
          (cf (disjointNet Q v h₁ h₂ a b) (disjointMetric Q v h₁ h₂ θ) q +
            cf (disjointNet Q v h₁ h₂ b a) (disjointMetric Q v h₁ h₂ θ) q) := by
  have hC' := hC
  obtain ⟨hcyc, hv, h2, hn, hk⟩ := hC
  have hN := hQ.binary.1
  have hθ := hQ.metric.1
  have := hN.finite_arcs
  have hpar := mem_pair_of_target_of_indegree_eq_two h2 hne hh₁ hh₂
  have hsum1 := inheritance_add_eq_one hθ h2 hne hh₁ hh₂
  set γ := θ.inheritance h₁ with hγ
  have hγ₂ : θ.inheritance h₂ = 1 - γ := by linarith
  have hvr : v ≠ Q.root := fun h => by
    have := hN.root_indegree
    rw [← h, h2] at this
    exact absurd this (by norm_num)
  have hcv : IsCut Q v := ⟨fun h => hvr (eq_of_reaches_of_reaches hN.acyclic h (hN.root_reaches v)),
    fun e he hne' => reaches_source_of_below_hybrid hQ.binary hQ.levelOne h2 he hne'⟩
  obtain ⟨c', hc', hcu'⟩ := existsUnique_child_of_hybrid hQ.binary h2
  have hcc : c = c' := hcu' c hc
  subst hcc
  have hcu := hcu'
  obtain ⟨hcut, huniq⟩ := isCut_child_of_hybrid hQ.binary hQ.levelOne h2 hc hcu
  have hcr : Q.graph.target c ≠ v := fun h => hN.acyclic v (.single ⟨c, hc, h⟩)
  have hnr : ∀ h, Q.graph.target h = v → ¬ Q.graph.Reaches (Q.graph.target c) (Q.graph.target h) :=
    fun h hh hr => hN.acyclic v (Relation.TransGen.head' ⟨c, hc, rfl⟩ (hh ▸ hr))
  have hθc : θ.inheritance c = 1 := hθ.2.2.1 c (isTreeArc_of_unique rfl huniq)
  have hc₁ : c ≠ h₁ := fun h => hcr (h ▸ hh₁)
  have hc₂ : c ≠ h₂ := fun h => hcr (h ▸ hh₂)
  have hnorm : ∀ γ', Q.IsNormalized (θ.withPair h₁ h₂ γ') := fun γ' =>
    isNormalized_withPair hθ.isNormalized hne (hh₂.trans hh₁.symm) (fun f hf hf₁ hf₂ =>
      absurd (hpar f (hf.trans hh₁)) (by tauto)) γ'
  have hX := hQ.card_taxa
  have htaxa := taxa_eq_univ hX q
  have hinjv : taxaInj Q univ v = ∅ := by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    exact leaf_ne_source hN x c ((mem_filter.1 hx).2.2.trans hc.symm)
  -- the polynomial in the inheritance of `h₁`
  let W : Finset (Finset X) → Finset (Finset X) → ℝ := fun t₁ t₂ =>
    cherryMass Q θ 0 (hybInj Q v h₁ h₂ (taxaInj Q univ) t₁ t₂) q
  have hΦ : ∀ γ', cf Q (θ.withPair h₁ h₂ γ') q = ∑ G, arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G *
      hybridPoly G (θ.length h₁) (θ.length h₂) W γ' := by
    intro γ'
    have h1' : (θ.withPair h₁ h₂ γ').inheritance c = 1 := by
      rw [withPair_inheritance_of_ne hc₁ hc₂]
      exact hθc
    rw [cf, nmscCF_eq_cherryMass_weak hN (hnorm γ') le_rfl, htaxa,
      cherryMass_eq_sum_arc hN hcut rfl huniq h1']
    refine sum_congr rfl fun G _ => ?_
    rw [arcLaw_withPair hcut (hnr h₁ hh₁) (hnr h₂ hh₂), liftInj_eq_cutInj hN hc hcu _ hinjv,
      cherryMass_cutInj_hybrid hN hcv hne hh₁ hh₂ hpar (withPair_inheritance_left h₁ h₂ γ')
        (withPair_inheritance_right hne γ')]
    unfold hybridPoly
    simp only [withPair_length, W, cherryMass_hybInj_withPair hN hcv hne hh₁ hh₂ hpar rfl hγ₂]
  have hQθ : cf Q θ q = cf Q (θ.withPair h₁ h₂ γ) q := by
    rw [withPair_eq_self rfl fun _ => hγ₂]
  have hQ₁ : cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q = cf Q (θ.withPair h₁ h₂ 1) q :=
    cf_deleteArc hN θ (hh₁.trans hh₂.symm) (fun f hf => hpar f (hf.trans hh₂)) hne q
  have hQ₂ : cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q = cf Q (θ.withPair h₁ h₂ 0) q := by
    rw [cf_deleteArc hN θ (hh₂.trans hh₁.symm) (fun f hf => (hpar f (hf.trans hh₁)).symm)
      hne.symm q]
    have hswap : θ.withPair h₂ h₁ 1 = θ.withPair h₁ h₂ 0 := by
      simp only [RootedNetwork.MetricData.withPair, RootedNetwork.MetricData.mk.injEq, true_and]
      funext f
      by_cases hf₂ : f = h₂
      · simp [hf₂, hne.symm]
      · by_cases hf₁ : f = h₁
        · simp [hf₁, hne]
        · simp [hf₁, hf₂]
    rw [hswap]
  -- `Q₀⊕`, the number `K` of lineages at `v`
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ.binary hQ.levelOne hcyc hv h2
  have hN₀ := hK.isPhylogenetic hN
  have hθ₀ := hK.isMetric hθ
  have hS : ∀ w, Q.graph.Reaches (Q.graph.target c) w → w ∉ cycleNodes Q.graph C := fun w hw hwC =>
    hN.acyclic v (Relation.TransGen.head' ⟨c, hc, rfl⟩
      (hw.trans (reaches_hybrid hQ.binary hQ.levelOne hcyc hv h2 w hwC)))
  have hcut₀ := isCut_contract hcyc hcut hS
  have hcr₀ : (contractRooted Q (· = C)).graph.target c₀ = Quot.mk _ (Q.graph.target c) := by
    change Quot.mk _ (Q.graph.target c₀.1) = _
    rw [hc₀]
  have huniq₀ : ∀ g, (contractRooted Q (· = C)).graph.target g =
      Quot.mk _ (Q.graph.target c) → g = c₀ := fun g hg =>
    Subtype.ext ((huniq g.1 ((mk_eq_mk_iff_of_notMem' hcyc (hS _ .refl)).1 hg)).trans hc₀.symm)
  have h1₀ : (contractMetric Q (· = C) θ).inheritance c₀ = 1 := by
    change θ.inheritance c₀.1 = 1
    rw [hc₀]
    exact hθc
  have hlaw : ∀ G, arcLaw (contractRooted Q (· = C)) _ hcut₀ (contractMetric Q (· = C) θ) 0 c₀
      (taxaInj (contractRooted Q (· = C)) univ) G = arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G := by
    intro G
    unfold arcLaw
    have hl : (contractMetric Q (· = C) θ).length c₀ = θ.length c := by
      change θ.length c₀.1 = _
      rw [hc₀]
    rw [hl]
    refine sum_congr rfl fun F₁ _ => ?_
    rw [rootDist_cutLower_contract hcyc hcut hS θ 0 F₁]
  -- the support: forests on the lineages of `a` and `b`
  have hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b := by
    have hsub : ({a, b} : Set X) ⊆ {x | Q.graph.Reaches v (Q.leaf x)} := by
      rintro x (rfl | rfl)
      · exact ha
      · exact hb
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hk, Set.ncard_pair hab])
      (Set.toFinite _)
    intro x
    rw [← Set.mem_ofPred_eq (p := fun x => Q.graph.Reaches v (Q.leaf x)), ← heq]
    simp
  have hsupp : ∀ G, arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G ≠ 0 →
      IsGoodForest G ∧ lineages G = {a, b} := by
    intro G hG
    obtain ⟨hgood, hlin⟩ := good_of_arcLaw_ne_zero hN hcut (validInj_taxaInj univ) hG
    refine ⟨hgood, ?_⟩
    ext x
    rw [hlin, mem_insert, mem_singleton, ← hbelow, reaches_leaf_iff_of_hybrid hQ.binary h2 hc hcu]
    constructor
    · rintro ⟨u, hu, hx⟩
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hx
      exact hu
    · exact fun h => ⟨_, h, mem_lineages_taxaInj.2 ⟨mem_univ _, rfl⟩⟩
  have hDq : ({a, b} : Finset X) ⊆ q.taxa := by rw [htaxa]; exact subset_univ _
  have hcard2 : #({a, b} : Finset X) = 2 := card_pair hab
  set δ : ℝ := if ({a, b} : Finset X) ∈ q.val then 1 else 0 with hδ
  have hsrc12 : Q.graph.source h₁ ≠ Q.graph.source h₂ := by
    refine source_ne_of_three_le_ncard hQ.binary hQ.levelOne hcyc hv h2 ?_ hne hh₁ hh₂
    split_ifs at hn <;> omega
  have hinjs : ∀ e, taxaInj Q univ (Q.graph.source e) = ∅ := fun e => by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    exact leaf_ne_source hN x e (mem_filter.1 hx).2.2
  have hsv : ∀ e, Q.graph.target e = v → ¬ Q.graph.Reaches v (Q.graph.source e) := fun e he h =>
    hN.acyclic v (Relation.TransGen.tail' h ⟨e, rfl, he⟩)
  -- one root: the cluster `{a, b}` decides the quartet tree
  have hone : ∀ G, arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G ≠ 0 → #(roots G) = 1 →
      W G ∅ = δ ∧ W ∅ G = δ ∧
        cherryMass (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) 0
          (liftInj (contractRooted Q (· = C)) c₀ (taxaInj (contractRooted Q (· = C)) univ) G) q =
            δ := by
    intro G hG h1r
    obtain ⟨hgood, hlin⟩ := hsupp G hG
    have hD : ({a, b} : Finset X) ∈ G := hlin ▸ lineages_mem_of_card_roots_eq_one h1r
    have hvalid : ∀ t₁ t₂ : Finset (Finset X), (t₁ = G ∧ t₂ = ∅ ∨ t₁ = ∅ ∧ t₂ = G) →
        ValidInj (hybInj Q v h₁ h₂ (taxaInj Q univ) t₁ t₂) := by
      rintro t₁ t₂ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · refine validInj_hybInj (validInj_taxaInj univ) hgood isGoodForest_empty (by simp [lineages])
          hsrc12 (hinjs h₁) (hinjs h₂) fun x hx u hvu hxu => ?_
        obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
        refine hvu ((hbelow x).2 ?_)
        rcases hx with hx | hx
        · rw [hlin] at hx
          simpa using hx
        · simp [lineages] at hx
      · refine validInj_hybInj (validInj_taxaInj univ) isGoodForest_empty hgood (by simp [lineages])
          hsrc12 (hinjs h₁) (hinjs h₂) fun x hx u hvu hxu => ?_
        obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
        refine hvu ((hbelow x).2 ?_)
        rcases hx with hx | hx
        · simp [lineages] at hx
        · rw [hlin] at hx
          simpa using hx
    refine ⟨?_, ?_, ?_⟩
    · refine cherryMass_of_mem hN hθ ⟨le_rfl, zero_le_one⟩ (hvalid G ∅ (Or.inl ⟨rfl, rfl⟩))
        (v := Q.graph.source h₁) ?_ hcard2 hDq
      unfold hybInj
      rw [ite_eq_right (hsv h₁ hh₁)]
      exact mem_union_right _ (mem_union_left _ (by rw [ite_eq_left rfl]; exact hD))
    · refine cherryMass_of_mem hN hθ ⟨le_rfl, zero_le_one⟩ (hvalid ∅ G (Or.inr ⟨rfl, rfl⟩))
        (v := Q.graph.source h₂) ?_ hcard2 hDq
      unfold hybInj
      rw [ite_eq_right (hsv h₂ hh₂)]
      exact mem_union_right _ (mem_union_right _ (by rw [ite_eq_left rfl]; exact hD))
    · exact cherryMass_of_mem hN₀ hθ₀ ⟨le_rfl, zero_le_one⟩ (validInj_of_arcLaw_ne_zero hN₀ hcut₀ hcr₀
        (validInj_taxaInj univ) (by rw [hlaw]; exact hG))
        (v := (contractRooted Q (· = C)).graph.source c₀)
        (by simp only [liftInj, ite_true]; exact mem_union_right _ hD) hcard2 hDq
  -- two roots: the lineages of `a` and `b`, which go to `Q_a⊕` or `Q_b⊕` when they take different
  -- hybrid edges
  have htwo : ∀ G, arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G ≠ 0 → ∀ R₁ R₂, R₁ ≠ R₂ →
      roots G = {R₁, R₂} →
      W (forestBelow G {R₁}) (forestBelow G {R₂}) + W (forestBelow G {R₂}) (forestBelow G {R₁}) =
        cf (disjointNet Q v h₁ h₂ a b) (disjointMetric Q v h₁ h₂ θ) q +
          cf (disjointNet Q v h₁ h₂ b a) (disjointMetric Q v h₁ h₂ θ) q := by
    intro G hG R₁ R₂ hR hroots
    obtain ⟨hgood, hlin⟩ := hsupp G hG
    have hR₁ : R₁ ∈ roots G := hroots ▸ mem_insert_self _ _
    have hR₂ : R₂ ∈ roots G := hroots ▸ mem_insert_of_mem (mem_singleton_self _)
    have hsum := hgood.1.sum_card_roots
    rw [hroots, sum_pair hR, hlin, hcard2] at hsum
    have hp₁ := (hgood.1.1 R₁ (roots_subset G hR₁)).card_pos
    have hp₂ := (hgood.1.1 R₂ (roots_subset G hR₂)).card_pos
    obtain ⟨x₁, rfl⟩ := card_eq_one.1 (show #R₁ = 1 by omega)
    obtain ⟨x₂, rfl⟩ := card_eq_one.1 (show #R₂ = 1 by omega)
    have hfb : ∀ x, {x} ∈ roots G → forestBelow G {{x}} = {{x}} := by
      intro x hx
      ext B
      simp only [mem_forestBelow, mem_singleton, exists_eq_left]
      constructor
      · rintro ⟨hB, hBx⟩
        rcases subset_singleton_iff.1 hBx with rfl | h
        · exact absurd (hgood.1.1 ∅ hB) (by simp)
        · exact h
      · rintro rfl
        exact ⟨roots_subset G hx, subset_rfl⟩
    have hx₁ : x₁ ∈ ({a, b} : Finset X) := hlin ▸ mem_lineages.2 ⟨{x₁}, roots_subset G hR₁, mem_singleton_self _⟩
    have hx₂ : x₂ ∈ ({a, b} : Finset X) := hlin ▸ mem_lineages.2 ⟨{x₂}, roots_subset G hR₂, mem_singleton_self _⟩
    have hx₁₂ : x₁ ≠ x₂ := fun h => hR (by rw [h])
    rw [hfb x₁ hR₁, hfb x₂ hR₂, cf_disjointNet_eq_cherryMass hQ hC' hne hh₁ hh₂ hab ha hb,
      cf_disjointNet_eq_cherryMass hQ hC' hne hh₁ hh₂ hab.symm hb ha]
    simp only [mem_insert, mem_singleton] at hx₁ hx₂
    rcases hx₁ with rfl | rfl <;> rcases hx₂ with rfl | rfl
    · exact absurd rfl hx₁₂
    · rfl
    · exact add_comm _ _
    · exact absurd rfl hx₁₂
  -- the formula, forest by forest
  have hP1 : probLineages Q θ c 1 = ∑ G, if #(roots G) = 1 then
      arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G else 0 :=
    probLineages_eq_sum_arc hN hθ hcut rfl huniq 1
  have hP2 : probLineages Q θ c 2 = ∑ G, if #(roots G) = 2 then
      arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G else 0 :=
    probLineages_eq_sum_arc hN hθ hcut rfl huniq 2
  have hP₀ : probLineages (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) c₀ 1 =
      probLineages Q θ c 1 := by
    rw [probLineages_eq_sum_arc hN₀ hθ₀ hcut₀ hcr₀ huniq₀ 1, hP1]
    exact sum_congr rfl fun G _ => by rw [hlaw]
  have hJ₀ : jointCF (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) c₀ 1 q =
      δ * probLineages Q θ c 1 := by
    rw [jointCF_eq_sum_arc hN₀ hcut₀ hcr₀ huniq₀ h1₀ 1 q, hP1, mul_sum]
    refine sum_congr rfl fun G _ => ?_
    rw [hlaw]
    split_ifs with h1r
    · by_cases hG : arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G = 0
      · rw [hG, zero_mul, mul_zero]
      · rw [sum_displays_injDist hX, (hone G hG h1r).2.2, mul_comm]
    · rw [mul_zero]
  have hcond : probLineages Q θ c 1 * (2 * γ * (1 - γ)) *
      condCF (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) c₀ 1 q =
      2 * γ * (1 - γ) * (δ * probLineages Q θ c 1) := by
    unfold condCF
    rw [hJ₀, hP₀]
    rcases eq_or_ne (probLineages Q θ c 1) 0 with h | h
    · rw [h]
      ring
    · field_simp
  have hpoint : ∀ G, arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G *
      hybridPoly G (θ.length h₁) (θ.length h₂) W γ =
      γ ^ 2 * (arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G *
          hybridPoly G (θ.length h₁) (θ.length h₂) W 1) +
        (1 - γ) ^ 2 * (arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G *
          hybridPoly G (θ.length h₁) (θ.length h₂) W 0) +
        2 * γ * (1 - γ) * (δ * (if #(roots G) = 1 then
          arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G else 0)) +
        γ * (1 - γ) * ((cf (disjointNet Q v h₁ h₂ a b) (disjointMetric Q v h₁ h₂ θ) q +
          cf (disjointNet Q v h₁ h₂ b a) (disjointMetric Q v h₁ h₂ θ) q) *
            (if #(roots G) = 2 then arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G else 0)) := by
    intro G
    by_cases hG : arcLaw Q _ hcut θ 0 c (taxaInj Q univ) G = 0
    · simp [hG]
    obtain ⟨hgood, hlin⟩ := hsupp G hG
    have h2r : #(roots G) ≤ 2 := by
      have := hgood.1.card_roots_le_card_lineages
      rw [hlin, hcard2] at this
      exact this
    have h0r : #(roots G) ≠ 0 := fun h => by
      have := card_roots_eq_zero_iff.1 h
      rw [this] at hlin
      have := congrArg card hlin
      simp [lineages, hcard2] at this
    rcases (show #(roots G) = 1 ∨ #(roots G) = 2 by omega) with h1r | h2r'
    · obtain ⟨hW₁, hW₂, -⟩ := hone G hG h1r
      simp only [hybridPoly_one_root hgood h1r, hW₁, hW₂, h1r, ite_true,
        (show (1 : ℕ) ≠ 2 by norm_num), ite_false]
      ring
    · obtain ⟨R₁, R₂, hR, hroots⟩ := card_eq_two.1 h2r'
      rw [hybridPoly_two_roots hgood hR hroots, htwo G hG R₁ R₂ hR hroots]
      simp only [h2r', ite_true, (show (2 : ℕ) ≠ 1 by norm_num), ite_false]
      ring
  rw [hQθ, hQ₁, hQ₂, hcond, hP2, hΦ, hΦ, hΦ, sum_congr rfl fun G _ => hpoint G, hP1]
  simp only [sum_add_distrib, ← mul_sum]
  ring

end Reduction

section Proposition5


/-- The cycle `liftEdges D` of `Q⊕` of a cycle `D` of `Q⁻` with hybrid node `w` induces the type of
`D`, with the hybrid node `w`. -/
theorem inducesCycleType_liftEdges_of_isHybridNodeOf {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {D : Set _}
    (hD : IsCycle hQ.unrooted.graph D) {w : SemidirectedVertex hQ.binary.1 hQ.nontrivial}
    (hw : IsHybridNodeOf hQ.unrooted D w) :
    InducesCycleType Q (liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D)
      (sdVert hQ.binary.1 hQ.nontrivial w) D.ncard {x | DescendsFrom hQ.unrooted w x}.ncard := by
  have hr := lsa_univ_eq_root hQ.binary.1 hQ.nontrivial hQ.isLSA
  obtain ⟨hvD, h2⟩ := (isHybridNodeOf_semidirected_iff _ _ _ hQ.binary hQ.levelOne hD w).1 hw
  refine ⟨isCycle_liftEdges _ _ _ hD, (sdVert_mem_cycleNodes_liftEdges_iff _ _ _ D w).2 hvD, h2,
    ?_, ?_⟩
  · have h := card_cycleNodesOffRoot_liftEdges _ _ _ hr hD
    rw [card_cycleNodesOffRoot (isCycle_liftEdges _ _ _ hD)] at h
    exact h
  · congr 1
    ext x
    exact (descendsFrom_semidirected_iff _ _ _ w h2 x).symm

/-- **The types of the cycles of `Q⁻`** (Section 5, before Lemma 5): a cycle of `Q⁻` is a `2₁`-,
`2₂`-, `2₃`-, `3₁`-, `3₂`- or `4₁`-cycle, with a hybrid node (Lemma 3). -/
theorem exists_isCycleType_of_isCycle {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {D : Set _}
    (hD : IsCycle hQ.unrooted.graph D) :
    ∃ n k, IsCycleType hQ.unrooted D n k ∧
      ((n = 2 ∧ 1 ≤ k ∧ k ≤ 3) ∨ (n = 3 ∧ (k = 1 ∨ k = 2)) ∨ (n = 4 ∧ k = 1)) := by
  obtain ⟨⟨w, ⟨hwD, h₁, h₂, hne, hd₁, hd₂, ht₁, ht₂⟩, -⟩, hmem, -⟩ :=
    lemma3_unrooted hQ.binary hQ.levelOne hQ.nontrivial hD
  have hw : IsHybridNodeOf hQ.unrooted D w :=
    ⟨h₁, hmem w hwD h₁ hd₁ ht₁, h₂, hmem w hwD h₂ hd₂ ht₂, hne, hd₁, hd₂, ht₁, ht₂⟩
  have hC := inducesCycleType_liftEdges_of_isHybridNodeOf hQ hD hw
  obtain ⟨h, hk, hn⟩ := add_le_of_inducesCycleType hQ.binary hQ.levelOne hQ.isLSA hC
  rw [hQ.card_taxa] at h
  exact ⟨_, _, ⟨hD, rfl, w, hw, rfl⟩, by omega⟩

/-- **Base case of Proposition 5, the trees**: two LSA quartet networks without hybrid edges whose
unrooted metric networks are isomorphic have species trees with the same unrooted metric tree. -/
theorem sameUnrootedMetricTree_of_sdMetricIso {V' E' : Type*} [Fintype V'] [Fintype E']
    {Q : RootedNetwork V E X} {θ : MetricData E} {Q' : RootedNetwork V' E' X} {θ' : MetricData E'}
    (hQ : IsLSAQuartet Q θ) (hQ' : IsLSAQuartet Q' θ')
    (ht : ∀ e, ¬ Q.IsHybridArc e) (ht' : ∀ e, ¬ Q'.IsHybridArc e)
    (φ : SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ) hQ'.unrooted
      (unrootedMetric Q' hQ'.binary hQ'.nontrivial θ')) :
    (treeSpeciesTree Q hQ.binary.1 ht hQ.metric.1).SameUnrootedMetricTree
      (treeSpeciesTree Q' hQ'.binary.1 ht' hQ'.metric.1) :=
  sameUnrootedMetricTree_of_iso hQ.binary hQ.isLSA hQ'.binary hQ'.isLSA hQ.nontrivial ht ht'
    hQ.metric.1 hQ'.metric.1 φ

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A binary level-1 network without cycles has no hybrid arc: two arcs into one node lie on a
cycle. -/
theorem not_isHybridArc_of_forall_not_isCycle {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (h0 : ∀ D, ¬ IsCycle N.graph D)
    (e : E) : ¬ N.IsHybridArc e := by
  intro he
  have := hN.1.finite_arcs
  unfold IsHybridArc DirectedMultigraph.indegree at he
  obtain ⟨f, hf, hfe⟩ : ∃ f, N.graph.target f = N.graph.target e ∧ f ≠ e := by
    by_contra hno
    push Not at hno
    have : {f | N.graph.target f = N.graph.target e} ⊆ {e} := fun f hf => hno f hf
    have := Set.ncard_le_ncard this (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨C, hC, -⟩ := exists_isCycle_of_target_eq hN h1 hfe hf
  exact h0 C hC

/-- **Proposition 5 for networks without cycles**: LSA quartet networks without cycles are trees
(`not_isHybridArc_of_forall_not_isCycle`), whose concordance factors are those of their species trees
(`nmscCF_eq_quartetProb`); isomorphic unrooted metric networks give the same unrooted metric species
tree (`sameUnrootedMetricTree_of_sdMetricIso`), and so, as the root placement does not matter
(`pub:rootplace`, `External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`, the
source's Theorem 9 and Proposition 11; the paper cites its Proposition 3, which as printed states
identifiability), the same distribution of unrooted gene trees. -/
theorem cf_eq_of_forall_not_isCycle {V' E' : Type*} [Fintype V'] [Fintype E']
    {Q : RootedNetwork V E X} {θ : MetricData E} {Q' : RootedNetwork V' E' X} {θ' : MetricData E'}
    (hQ : IsLSAQuartet Q θ) (hQ' : IsLSAQuartet Q' θ')
    (h0 : ∀ D, ¬ IsCycle Q.graph D) (h0' : ∀ D, ¬ IsCycle Q'.graph D)
    (φ : SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ) hQ'.unrooted
      (unrootedMetric Q' hQ'.binary hQ'.nontrivial θ')) :
    cf Q θ = cf Q' θ' := by
  have ht := not_isHybridArc_of_forall_not_isCycle hQ.binary hQ.levelOne h0
  have ht' := not_isHybridArc_of_forall_not_isCycle hQ'.binary hQ'.levelOne h0'
  have hX : 2 ≤ Fintype.card X := by rw [hQ.card_taxa]; norm_num
  have hσ := External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree hQ.card_taxa
    (sameUnrootedMetricTree_of_sdMetricIso hQ hQ' ht ht' φ)
  funext q
  show nmscCF Q θ 0 q = nmscCF Q' θ' 0 q
  rw [nmscCF_eq_quartetProb hQ.binary.1 ht hQ.metric.1 hX le_rfl,
    nmscCF_eq_quartetProb hQ'.binary.1 ht' hQ'.metric.1 hX le_rfl]
  unfold External.AllmanDegnanRhodes2011.quartetProb
  rw [hσ]


/-- **`Q₁⊕`, `Q₂⊕` as LSA quartet networks**: without a hybrid edge `h` of a cycle `C`, and with its
nodes of degree two suppressed (`reduceNet`), an LSA quartet network gives an LSA quartet network with
the concordance factors of `deleteArc Q h` and fewer cycles. -/
theorem isLSAQuartet_reduceNet_deleteArc {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {C : Set E} {v : V} {n k : ℕ}
    (hC : InducesCycleType Q C v n k) {h : E} (hh : Q.graph.target h = v)
    (hM : IsReducible (deleteArc Q h) (deleteArcMetric Q h θ)) :
    IsLSAQuartet (reduceNet (deleteArc Q h) hM.phylo)
        (reduceMetric (deleteArc Q h) hM.phylo (deleteArcMetric Q h θ)) ∧
      cf (reduceNet (deleteArc Q h) hM.phylo)
          (reduceMetric (deleteArc Q h) hM.phylo (deleteArcMetric Q h θ)) =
        cf (deleteArc Q h) (deleteArcMetric Q h θ) ∧
      {D | IsCycle (reduceNet (deleteArc Q h) hM.phylo).graph D}.ncard <
        {D | IsCycle Q.graph D}.ncard := by
  refine ⟨⟨hM.isBinaryRootedNetwork, hM.isLevelOne, hM.isLSANetwork fun D w k' hD => ?_,
    hQ.card_taxa, hM.isMetricNetwork⟩, hM.cf_eq, ?_⟩
  · obtain ⟨D', w', -, hD', -⟩ := (deleteArc_exists_inducesCycleType_iff hQ.binary hQ.levelOne hC hh
      1 k' _).1 ⟨D, w, hD, rfl⟩
    have := (add_le_of_inducesCycleType hQ.binary hQ.levelOne hQ.isLSA hD').2.2
    omega
  · rw [hM.ncard_setOf_isCycle]
    exact ncard_setOf_isCycle_deleteArc_lt hQ.binary hQ.levelOne hC hh

/-- **The unrooted networks of `Q₁⊕` and `Q̃₁⊕`** (proof of Proposition 5): deleting corresponding
hybrid edges `h` and `φ h` of `Q⁻ ≅ Q̃⁻`, and suppressing the nodes of degree two, gives isomorphic
metric unrooted networks. The unrooted network of `Q₁⊕` is `Q⁻` without `h` with its nodes of degree
two suppressed (`nonempty_sdMetricIso_suppress_deleteHybridEdge`), wherever the root of `Q⊕` is, and
`φ` maps this network to the one of `Q̃⁻` without `φ h`. -/
theorem nonempty_sdMetricIso_reduceNet_deleteArc {V' E' : Type*} [Fintype V'] [Fintype E']
    {Q : RootedNetwork V E X} {θ : MetricData E} {Q' : RootedNetwork V' E' X} {θ' : MetricData E'}
    (hQ : IsLSAQuartet Q θ) (hQ' : IsLSAQuartet Q' θ')
    (φ : SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ) hQ'.unrooted
      (unrootedMetric Q' hQ'.binary hQ'.nontrivial θ'))
    {h : SemidirectedArc hQ.binary.1 hQ.binary.2 hQ.nontrivial} (hh : hQ.unrooted.IsDirected h)
    (hP : (deleteArc Q (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial h)).IsPhylogenetic)
    (hP' : (deleteArc Q' (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge h))).IsPhylogenetic)
    (hb : IsBinaryRootedNetwork (reduceNet _ hP)) (hb' : IsBinaryRootedNetwork (reduceNet _ hP')) :
    Nonempty (SDMetricIso (unrooted _ hb hQ.nontrivial)
      (unrootedMetric _ hb hQ.nontrivial (reduceMetric _ hP
        (deleteArcMetric Q (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial h) θ)))
      (unrooted _ hb' hQ'.nontrivial)
      (unrootedMetric _ hb' hQ'.nontrivial (reduceMetric _ hP'
        (deleteArcMetric Q' (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge h)) θ')))) := by
  obtain ⟨ι⟩ := nonempty_sdMetricIso_suppress_deleteHybridEdge hQ.binary hQ.nontrivial hQ.levelOne
    hQ.isLSA hQ.metric hh hP hb
  obtain ⟨ι'⟩ := nonempty_sdMetricIso_suppress_deleteHybridEdge hQ'.binary hQ'.nontrivial
    hQ'.levelOne hQ'.isLSA hQ'.metric ((φ.isDirected_iff h).2 hh) hP' hb'
  exact ⟨ι.symm.trans ((φ.deleteHybridEdge hh).suppress.trans ι')⟩

/-- **The unrooted networks of `Q₀⊕` and `Q̃₀⊕`** (proof of Proposition 5): contracting corresponding
2-cycles `D` and `φ D` of `Q⁻ ≅ Q̃⁻`, and suppressing the nodes of degree two, gives isomorphic metric
unrooted networks. The unrooted network of `Q₀⊕` is `Q⁻` with `D` contracted and its nodes of degree
two suppressed (`nonempty_sdMetricIso_suppress_contractCycles`), whether or not the cycle of `Q⊕`
passes through the root, and `φ` maps this network to the one of `Q̃⁻` with `φ D` contracted. -/
theorem nonempty_sdMetricIso_contractNet {V' E' : Type*} [Fintype V'] [Fintype E']
    {Q : RootedNetwork V E X} {θ : MetricData E} {Q' : RootedNetwork V' E' X} {θ' : MetricData E'}
    (hQ : IsLSAQuartet Q θ) (hQ' : IsLSAQuartet Q' θ')
    (φ : SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ) hQ'.unrooted
      (unrootedMetric Q' hQ'.binary hQ'.nontrivial θ'))
    {D : Set (SemidirectedArc hQ.binary.1 hQ.binary.2 hQ.nontrivial)}
    (hD : IsCycle hQ.unrooted.graph D) (hD2 : D.ncard = 2)
    (hb : IsBinaryRootedNetwork (contractNet Q hQ.binary hQ.levelOne
      (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D)))
    (hb' : IsBinaryRootedNetwork (contractNet Q' hQ'.binary hQ'.levelOne
      (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D)))) :
    Nonempty (SDMetricIso (unrooted _ hb hQ.nontrivial)
      (unrootedMetric _ hb hQ.nontrivial (contractNetMetric Q hQ.binary hQ.levelOne
        (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D) θ))
      (unrooted _ hb' hQ'.nontrivial)
      (unrootedMetric _ hb' hQ'.nontrivial (contractNetMetric Q' hQ'.binary hQ'.levelOne
        (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D)) θ'))) := by
  obtain ⟨ι⟩ := nonempty_sdMetricIso_suppress_contractCycles hQ.binary hQ.levelOne hQ.nontrivial
    hQ.isLSA hQ.card_taxa hQ.metric hD hD2 hb
  obtain ⟨ι'⟩ := nonempty_sdMetricIso_suppress_contractCycles hQ'.binary hQ'.levelOne
    hQ'.nontrivial hQ'.isLSA hQ'.card_taxa hQ'.metric (φ.isCycle_image hD)
    ((φ.ncard_image D).trans hD2) hb'
  have hcyc : ∀ C, IsCycle hQ.unrooted.graph C → (φ.edge '' C = φ.edge '' D ↔ C = D) :=
    fun C _ => φ.edge.injective.image_injective.eq_iff
  exact ⟨ι.symm.trans ((φ.contractCycles hcyc).suppress.trans ι')⟩

omit [Fintype V] in
/-- **`Q_a⊕` as an LSA quartet network**: when the only cycle `C` of `Q⊕` induces a `3₂`-cycle with
the taxa `a`, `b` below its hybrid node `v`, `Q_a⊕` is an LSA quartet network without cycles. -/
theorem isLSAQuartet_disjointNet {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {C : Set E} {v : V}
    (hC : InducesCycleType Q C v 3 2) (hone : ∀ C', IsCycle Q.graph C' → C' = C) {h₁ h₂ : E}
    (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) {a b : X}
    (hab : a ≠ b) (hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b) :
    IsLSAQuartet (disjointNet Q v h₁ h₂ a b) (disjointMetric Q v h₁ h₂ θ) ∧
      ∀ D, ¬ IsCycle (disjointNet Q v h₁ h₂ a b).graph D := by
  obtain ⟨hb, hl, hθ⟩ := disjointNet_spec hQ.binary hQ.levelOne hone hC.2.1 hC.2.2.1 hne hh₁ hh₂
    hab hbelow hQ.metric
  have h0 := disjointNet_not_isCycle hQ.binary hQ.levelOne hone hC.2.1 hC.2.2.1 hne hh₁ hh₂
    (a := a) (b := b)
  exact ⟨⟨hb, fun C₁ _ hC₁ => absurd hC₁ (h0 C₁), hl, hQ.card_taxa, hθ⟩, h0⟩

omit [Fintype V] in
/-- **The unrooted networks of `Q_a⊕` and `Q̃_a⊕`** (proof of Proposition 5): for corresponding hybrid
nodes `w`, `φ w` of `Q⁻ ≅ Q̃⁻` and corresponding hybrid edges, `Q_a⊕` and `Q̃_a⊕` have isomorphic
metric unrooted networks. The unrooted network of `Q_a⊕` is
`Q⁻` cut below `w` (`nonempty_sdMetricIso_disjointNet_cutSD`), and `φ` maps this network to `Q̃⁻` cut
below `φ w` (`SDMetricIso.nonempty_cutSD_of_isDirected`). -/
theorem nonempty_sdMetricIso_disjointNet {V' E' : Type*} [Fintype V'] [Fintype E']
    {Q : RootedNetwork V E X} {θ : MetricData E} {Q' : RootedNetwork V' E' X} {θ' : MetricData E'}
    (hQ : IsLSAQuartet Q θ) (hQ' : IsLSAQuartet Q' θ')
    (φ : SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ) hQ'.unrooted
      (unrootedMetric Q' hQ'.binary hQ'.nontrivial θ'))
    {w : SemidirectedVertex hQ.binary.1 hQ.nontrivial}
    {h₁ h₂ : SemidirectedArc hQ.binary.1 hQ.binary.2 hQ.nontrivial} (hne : h₁ ≠ h₂)
    (hd₁ : hQ.unrooted.IsDirected h₁) (hd₂ : hQ.unrooted.IsDirected h₂)
    (ht₁ : hQ.unrooted.graph.target h₁ = w) (ht₂ : hQ.unrooted.graph.target h₂ = w) {a b : X}
    (hab : a ≠ b)
    (hb : IsBinaryRootedNetwork (disjointNet Q (sdVert hQ.binary.1 hQ.nontrivial w)
      (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial h₁)
      (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial h₂) a b))
    (hl : (disjointNet Q (sdVert hQ.binary.1 hQ.nontrivial w)
      (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial h₁)
      (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial h₂) a b).IsLSANetwork)
    (hb' : IsBinaryRootedNetwork (disjointNet Q' (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w))
      (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge h₁))
      (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge h₂)) a b))
    (hl' : (disjointNet Q' (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w))
      (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge h₁))
      (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge h₂)) a b).IsLSANetwork) :
    Nonempty (SDMetricIso (unrooted _ hb hQ.nontrivial)
      (unrootedMetric _ hb hQ.nontrivial (disjointMetric Q (sdVert hQ.binary.1 hQ.nontrivial w)
        (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial h₁)
        (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial h₂) θ))
      (unrooted _ hb' hQ'.nontrivial)
      (unrootedMetric _ hb' hQ'.nontrivial (disjointMetric Q'
        (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w))
        (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge h₁))
        (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge h₂)) θ'))) := by
  obtain ⟨ι⟩ := nonempty_sdMetricIso_disjointNet_cutSD hQ.binary hQ.levelOne hQ.nontrivial
    (lsa_univ_eq_root hQ.binary.1 hQ.nontrivial hQ.isLSA) θ hne hd₁ ht₁ ht₂ hab hb hl
  obtain ⟨ι'⟩ := nonempty_sdMetricIso_disjointNet_cutSD hQ'.binary hQ'.levelOne hQ'.nontrivial
    (lsa_univ_eq_root hQ'.binary.1 hQ'.nontrivial hQ'.isLSA) θ' (φ.edge.injective.ne hne)
    ((φ.isDirected_iff h₁).2 hd₁) ((φ.directed h₁ hd₁).2.trans (congrArg φ.vert ht₁))
    ((φ.directed h₂ hd₂).2.trans (congrArg φ.vert ht₂)) hab hb' hl'
  obtain ⟨κ⟩ := φ.nonempty_cutSD_of_isDirected w hd₁ hd₂ a b
  exact ⟨ι.trans (κ.trans ι'.symm)⟩

/-- **`P(K = k)` and `CF(Q₀⊕ | K = 1)` are read from the unrooted network** (proof of Proposition 5,
Lemma 11): when the only cycle of `Q⊕` induces a `3₂`-cycle `D` of `Q⁻`, the child `u` of its hybrid
node `v` has the two leaves `a`, `b` as children; the two lineages coalesce on the edge `c` from `v`
to `u` with probability `1 - e^{-ℓ(c)}`, and given one lineage at `v` the cherry `{a, b}` decides the
quartet tree. The length of `c` is that of the edge of `Q⁻` from `v` that is not hybrid. -/
theorem probLineages_condCF_eq_of_threeTwo {V' E' : Type*} [Fintype V'] [Fintype E']
    {Q : RootedNetwork V E X} {θ : MetricData E} {Q' : RootedNetwork V' E' X} {θ' : MetricData E'}
    (hQ : IsLSAQuartet Q θ) (hQ' : IsLSAQuartet Q' θ')
    (φ : SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ) hQ'.unrooted
      (unrootedMetric Q' hQ'.binary hQ'.nontrivial θ'))
    {D : Set (SemidirectedArc hQ.binary.1 hQ.binary.2 hQ.nontrivial)}
    (hD : IsCycle hQ.unrooted.graph D)
    (hone : ∀ C', IsCycle Q.graph C' → C' = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D)
    (hone' : ∀ C', IsCycle Q'.graph C' →
      C' = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D))
    {w : SemidirectedVertex hQ.binary.1 hQ.nontrivial} (hw : IsHybridNodeOf hQ.unrooted D w)
    (hk : {x | DescendsFrom hQ.unrooted w x}.ncard = 2)
    {c : E} (hc : Q.graph.source c = sdVert hQ.binary.1 hQ.nontrivial w) {c' : E'}
    (hc' : Q'.graph.source c' = sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w))
    (c₀ : {e // ∀ C', IsCycle Q.graph C' →
      C' = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D → e ∉ C'}) (hc₀ : c₀.1 = c)
    (c₀' : {e // ∀ C', IsCycle Q'.graph C' →
      C' = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D) → e ∉ C'})
    (hc₀' : c₀'.1 = c') :
    probLineages Q θ c 1 = probLineages Q' θ' c' 1 ∧
      probLineages Q θ c 2 = probLineages Q' θ' c' 2 ∧
      ∀ q, condCF (contractRooted Q (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D))
          (contractMetric Q (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D) θ) c₀ 1 q =
        condCF (contractRooted Q' (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial
            (φ.edge '' D)))
          (contractMetric Q' (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial
            (φ.edge '' D)) θ') c₀' 1 q := by
  have hC := inducesCycleType_liftEdges_of_isHybridNodeOf hQ hD hw
  have hC' := inducesCycleType_liftEdges_of_isHybridNodeOf hQ' (φ.isCycle_image hD)
    (φ.isHybridNodeOf_image hw)
  obtain ⟨a, b, hab, hs⟩ := Set.ncard_eq_two.1 hk
  have hbelowD : ∀ x, DescendsFrom hQ.unrooted w x ↔ x = a ∨ x = b := fun x => by
    have := Set.ext_iff.1 hs x
    simpa using this
  have hbelow : ∀ x, Q.graph.Reaches (sdVert hQ.binary.1 hQ.nontrivial w) (Q.leaf x) ↔
      x = a ∨ x = b := fun x =>
    (descendsFrom_semidirected_iff _ _ _ w hC.2.2.1 x).symm.trans (hbelowD x)
  have hbelow' : ∀ x, Q'.graph.Reaches (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w))
      (Q'.leaf x) ↔ x = a ∨ x = b := fun x =>
    (descendsFrom_semidirected_iff _ _ _ (φ.vert w) hC'.2.2.1 x).symm.trans
      ((φ.descendsFrom_iff w x).trans (hbelowD x))
  have hl := length_child_eq_of_sdMetricIso hQ.binary hQ.levelOne hQ.isLSA hQ'.binary hQ'.isLSA
    hQ.nontrivial φ hC.2.2.1 hC'.2.2.1 hc hc'
  obtain ⟨hP1, hP2⟩ := probLineages_cherry_of_single_cycle hQ.binary hQ.levelOne hC.1 hone hC.2.1
    hC.2.2.1 hc hab hbelow hQ.metric.1
  obtain ⟨hP1', hP2'⟩ := probLineages_cherry_of_single_cycle hQ'.binary hQ'.levelOne hC'.1 hone'
    hC'.2.1 hC'.2.2.1 hc' hab hbelow' hQ'.metric.1
  refine ⟨by rw [hP1, hP1', hl], by rw [hP2, hP2', hl], fun q => ?_⟩
  rw [condCF_contractRooted_cherry_of_single_cycle hQ.binary hQ.levelOne hC.1 hone hC.2.1 hC.2.2.1
      hc hab hbelow hQ.metric.1 hQ.card_taxa c₀ hc₀ q,
    condCF_contractRooted_cherry_of_single_cycle hQ'.binary hQ'.levelOne hC'.1 hone' hC'.2.1
      hC'.2.2.1 hc' hab hbelow' hQ'.metric.1 hQ'.card_taxa c₀' hc₀' q]


omit [Fintype X] in
/-- **Proposition 5, by induction on the number of cycles**, for networks on `Type`.

The paper's proof. With no cycle, `Q⊕` and `Q̃⊕` are trees, whose concordance factors are those of
their species trees, which have the same unrooted metric tree (`cf_eq_of_forall_not_isCycle`). The
paper cites Proposition 3 of Allman, Degnan, Rhodes (2011) for the equality; the step is the statement
that the root placement does not matter (`pub:rootplace`,
`External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`: the source's Theorem 9
and Proposition 11, for four taxa). Proposition 3 as printed in the paper states that the unrooted
metric tree is identifiable from the concordance factors and the rooted one is not, which is not this
statement. Otherwise a cycle `D` of `Q⁻` is the
cycle `φ D` of `Q̃⁻` of the same type (`SDIso.isCycleType_image`), and `D`, `φ D` come from cycles of
`Q⊕`, `Q̃⊕` of that type (`inducesCycleType_liftEdges_of_isHybridNodeOf`). The lemma of that type
writes the concordance factors of `Q⊕` and of `Q̃⊕` in terms of networks with fewer cycles, the same
for both since their unrooted metric networks are isomorphic (`nonempty_sdMetricIso_reduceNet_deleteArc`,
`nonempty_sdMetricIso_contractNet`, `nonempty_sdMetricIso_disjointNet`), so the induction hypothesis
applies, and the inheritance probabilities are those of corresponding hybrid edges of `Q⁻` and `Q̃⁻`.
The cycles are taken in this order: a `2₁`- or `2₃`-cycle (Lemma 7 or 8, through `corollary2_step`),
then a `2₂`-cycle (Lemma 9), then a `3₁`- or 4-cycle (Lemma 10), then a `3₂`-cycle (Lemma 11).

Lemma 11 has the terms `P(K = k)` and `CF(Q₀⊕ | K = 1)`, which are not concordance factors of networks
with fewer cycles; the paper does not say why they agree for `Q⊕` and `Q̃⊕`. With the `3₂`-cycle taken
last, it is the only cycle (Lemma 6), the child of its hybrid node is the parent of the two taxa below
it, and these terms are `1 - e^{-ℓ}`, `e^{-ℓ}` and the indicator of the cherry of these two taxa, for
the length `ℓ` of the edge out of the hybrid node (`probLineages_condCF_eq_of_threeTwo`). -/
theorem proposition5_aux [Fintype X] (n : ℕ) :
    ∀ {V₀ E₀ V₁ E₁ : Type} [Fintype V₀] [Fintype E₀] [Fintype V₁] [Fintype E₁]
      {Q : RootedNetwork V₀ E₀ X} {θ : MetricData E₀} (hQ : IsLSAQuartet Q θ)
      {Q' : RootedNetwork V₁ E₁ X} {θ' : MetricData E₁} (hQ' : IsLSAQuartet Q' θ'),
      {D | IsCycle Q.graph D}.ncard ≤ n →
      Nonempty (SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ) hQ'.unrooted
        (unrootedMetric Q' hQ'.binary hQ'.nontrivial θ')) → cf Q θ = cf Q' θ' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V₀ E₀ V₁ E₁ _ _ _ _ Q θ hQ Q' θ' hQ' hn ⟨φ⟩
  have IH : ∀ {V₂ E₂ V₃ E₃ : Type} [Fintype V₂] [Fintype E₂] [Fintype V₃] [Fintype E₃]
      {Q₂ : RootedNetwork V₂ E₂ X} {θ₂ : MetricData E₂} (hQ₂ : IsLSAQuartet Q₂ θ₂)
      {Q₃ : RootedNetwork V₃ E₃ X} {θ₃ : MetricData E₃} (hQ₃ : IsLSAQuartet Q₃ θ₃),
      {D | IsCycle Q₂.graph D}.ncard < {D | IsCycle Q.graph D}.ncard →
      Nonempty (SDMetricIso hQ₂.unrooted (unrootedMetric Q₂ hQ₂.binary hQ₂.nontrivial θ₂)
        hQ₃.unrooted (unrootedMetric Q₃ hQ₃.binary hQ₃.nontrivial θ₃)) → cf Q₂ θ₂ = cf Q₃ θ₃ :=
    by
      intro V₂ E₂ V₃ E₃ _ _ _ _ Q₂ θ₂ hQ₂ Q₃ θ₃ hQ₃ hlt hiso
      exact ih _ (lt_of_lt_of_le hlt hn) hQ₂ hQ₃ le_rfl hiso
  have hr := lsa_univ_eq_root hQ.binary.1 hQ.nontrivial hQ.isLSA
  have hr' := lsa_univ_eq_root hQ'.binary.1 hQ'.nontrivial hQ'.isLSA
  have htwo : ∃ x y : X, x ≠ y := by
    have : Nontrivial X := hQ.nontrivial
    exact exists_pair_ne X
  -- the arcs of `Q⊕` and `Q̃⊕` of the edges into a hybrid node `w` of `Q⁻` and `φ w` of `Q̃⁻`
  have harc : ∀ g w, hQ.unrooted.graph.target g = w →
      Q.graph.target (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g) =
        sdVert hQ.binary.1 hQ.nontrivial w := fun g w hg =>
    (sdVert_target _ _ _ g).symm.trans (congrArg _ hg)
  have harc' : ∀ g w, hQ.unrooted.graph.target g = w → hQ.unrooted.IsDirected g →
      Q'.graph.target (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g)) =
        sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w) := fun g w hg hd =>
    (sdVert_target _ _ _ _).symm.trans (congrArg _ ((φ.directed g hd).2.trans (congrArg _ hg)))
  have hγ : ∀ g, hQ.unrooted.IsDirected g →
      θ'.inheritance (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g)) =
        θ.inheritance (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g) := fun g hd =>
    φ.inheritance g hd
  -- the corresponding cycles
  have hcyc : ∀ D, IsCycle hQ.unrooted.graph D → ∀ w, IsHybridNodeOf hQ.unrooted D w →
      InducesCycleType Q (liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D)
          (sdVert hQ.binary.1 hQ.nontrivial w) D.ncard {x | DescendsFrom hQ.unrooted w x}.ncard ∧
        InducesCycleType Q' (liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D))
          (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w)) D.ncard
          {x | DescendsFrom hQ.unrooted w x}.ncard := by
    intro D hD w hw
    refine ⟨inducesCycleType_liftEdges_of_isHybridNodeOf hQ hD hw, ?_⟩
    have h := inducesCycleType_liftEdges_of_isHybridNodeOf hQ' (φ.isCycle_image hD)
      (φ.isHybridNodeOf_image hw)
    rw [φ.ncard_image] at h
    convert h using 3
    ext x
    exact (φ.descendsFrom_iff w x).symm
  -- deleting corresponding hybrid edges
  have hdel : ∀ D, IsCycle hQ.unrooted.graph D → ∀ w, IsHybridNodeOf hQ.unrooted D w →
      ∀ g, hQ.unrooted.IsDirected g → hQ.unrooted.graph.target g = w →
      cf (deleteArc Q (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g))
          (deleteArcMetric Q (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g) θ) =
        cf (deleteArc Q' (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g)))
          (deleteArcMetric Q' (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g)) θ') := by
    intro D hD w hw g hd ht
    obtain ⟨hC, hC'⟩ := hcyc D hD w hw
    have hn2 := (add_le_of_inducesCycleType hQ.binary hQ.levelOne hQ.isLSA hC).2.2
    have hM := isReducible_deleteArc hQ.binary hQ.levelOne hC (harc g w ht) hQ.metric htwo hn2
    have hM' := isReducible_deleteArc hQ'.binary hQ'.levelOne hC' (harc' g w ht hd) hQ'.metric htwo
      hn2
    obtain ⟨hQ₁, hcf₁, hlt₁⟩ := isLSAQuartet_reduceNet_deleteArc hQ hC (harc g w ht) hM
    obtain ⟨hQ₁', hcf₁', -⟩ := isLSAQuartet_reduceNet_deleteArc hQ' hC' (harc' g w ht hd) hM'
    rw [← hcf₁, ← hcf₁']
    exact IH hQ₁ hQ₁' hlt₁ (nonempty_sdMetricIso_reduceNet_deleteArc hQ hQ' φ hd hM.phylo
      hM'.phylo hQ₁.binary hQ₁'.binary)
  -- contracting corresponding 2-cycles
  have hcon : ∀ D, IsCycle hQ.unrooted.graph D → D.ncard = 2 →
      cf (contractNet Q hQ.binary hQ.levelOne (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D))
          (contractNetMetric Q hQ.binary hQ.levelOne
            (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D) θ) =
        cf (contractNet Q' hQ'.binary hQ'.levelOne
            (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D)))
          (contractNetMetric Q' hQ'.binary hQ'.levelOne
            (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D)) θ') ∧
      cf (contractNet Q hQ.binary hQ.levelOne (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D))
          (contractNetMetric Q hQ.binary hQ.levelOne
            (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D) θ) =
        cf (contractRooted Q (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D))
          (contractMetric Q (· = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D) θ) ∧
      cf (contractNet Q' hQ'.binary hQ'.levelOne
            (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D)))
          (contractNetMetric Q' hQ'.binary hQ'.levelOne
            (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D)) θ') =
        cf (contractRooted Q' (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D)))
          (contractMetric Q' (· = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial
            (φ.edge '' D)) θ') := by
    intro D hD hD2
    have hD' := φ.isCycle_image hD
    have hn : ∀ C', IsCycle Q.graph C' → C' = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D →
        C'.ncard - (if Q.root ∈ cycleNodes Q.graph C' then 1 else 0) = 2 := by
      rintro C' - rfl
      have h := card_cycleNodesOffRoot_liftEdges _ _ _ hr hD
      rw [card_cycleNodesOffRoot (isCycle_liftEdges _ _ _ hD), hD2] at h
      exact h
    have hn' : ∀ C', IsCycle Q'.graph C' →
        C' = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D) →
        C'.ncard - (if Q'.root ∈ cycleNodes Q'.graph C' then 1 else 0) = 2 := by
      rintro C' - rfl
      have h := card_cycleNodesOffRoot_liftEdges _ _ _ hr' hD'
      rw [card_cycleNodesOffRoot (isCycle_liftEdges _ _ _ hD'), φ.ncard_image, hD2] at h
      exact h
    obtain ⟨hb, h1, hlsa, hθ, hcf, hnum, -, -⟩ :=
      contractNet_spec hQ.binary hQ.levelOne hQ.isLSA hQ.card_taxa hQ.metric hn
    obtain ⟨hb', h1', hlsa', hθ', hcf', -, -, -⟩ :=
      contractNet_spec hQ'.binary hQ'.levelOne hQ'.isLSA hQ'.card_taxa hQ'.metric hn'
    refine ⟨IH ⟨hb, h1, hlsa, hQ.card_taxa, hθ⟩ ⟨hb', h1', hlsa', hQ'.card_taxa, hθ'⟩ ?_
      (nonempty_sdMetricIso_contractNet hQ hQ' φ hD hD2 hb hb'), hcf, hcf'⟩
    rw [hnum]
    exact Set.ncard_lt_ncard ⟨fun D hD => hD.1, fun hsub =>
      (hsub (isCycle_liftEdges _ _ _ hD)).2 rfl⟩ (Set.toFinite _)
  -- the cases
  by_cases hA : ∃ D, IsCycleType hQ.unrooted D 2 1 ∨ IsCycleType hQ.unrooted D 2 3
  · -- Lemmas 7 and 8 (Corollary 2)
    obtain ⟨D, hD⟩ := hA
    have hDc : IsCycle hQ.unrooted.graph D := by rcases hD with hD | hD <;> exact hD.1
    have hD2 : D.ncard = 2 := by rcases hD with hD | hD <;> exact hD.2.1
    obtain ⟨w, hw, hk⟩ : ∃ w, IsHybridNodeOf hQ.unrooted D w ∧
        ({x | DescendsFrom hQ.unrooted w x}.ncard = 1 ∨
          {x | DescendsFrom hQ.unrooted w x}.ncard = 3) := by
      rcases hD with ⟨-, -, w, hw, hk⟩ | ⟨-, -, w, hw, hk⟩
      · exact ⟨w, hw, Or.inl hk⟩
      · exact ⟨w, hw, Or.inr hk⟩
    obtain ⟨hC, hC'⟩ := hcyc D hDc w hw
    rw [hD2] at hC hC'
    have hCP : IsTwoOneOrThree Q (liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D) := by
      rcases hk with hk | hk
      · rw [hk] at hC; exact ⟨_, Or.inl hC⟩
      · rw [hk] at hC; exact ⟨_, Or.inr hC⟩
    have hCP' : IsTwoOneOrThree Q' (liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial
        (φ.edge '' D)) := by
      rcases hk with hk | hk
      · rw [hk] at hC'; exact ⟨_, Or.inl hC'⟩
      · rw [hk] at hC'; exact ⟨_, Or.inr hC'⟩
    obtain ⟨-, hcf, -⟩ := corollary2_step hQ hC.1 hCP
    obtain ⟨-, hcf', -⟩ := corollary2_step hQ' hC'.1 hCP'
    rw [hcf, hcf']
    exact (hcon D hDc hD2).1
  by_cases hB : ∃ D, IsCycleType hQ.unrooted D 2 2
  · -- Lemma 9
    obtain ⟨D, hD⟩ := hB
    obtain ⟨hDc, hD2, w, hw, hk⟩ := id hD
    obtain ⟨g₁, -, g₂, -, hne, hd₁, hd₂, ht₁, ht₂⟩ := id hw
    obtain ⟨hC, hC'⟩ := hcyc D hDc w hw
    rw [hD2, hk] at hC hC'
    have hne' : sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₁) ≠
        sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₂) := fun h =>
      hne (φ.edge.injective (sdArc_injective _ _ _ h))
    funext q
    rw [lemma9 hQ hC (fun h => hne (sdArc_injective _ _ _ h)) (harc g₁ w ht₁) (harc g₂ w ht₂) q,
      lemma9 hQ' hC' hne' (harc' g₁ w ht₁ hd₁) (harc' g₂ w ht₂ hd₂) q, hγ g₁ hd₁,
      congrFun (hdel D hDc w hw g₁ hd₁ ht₁) q, congrFun (hdel D hDc w hw g₂ hd₂ ht₂) q,
      ← (hcon D hDc hD2).2.1, ← (hcon D hDc hD2).2.2, (hcon D hDc hD2).1]
  by_cases hC4 : ∃ D, IsCycleType hQ.unrooted D 3 1 ∨ ∃ k, IsCycleType hQ.unrooted D 4 k
  · -- Lemma 10
    obtain ⟨D, hD⟩ := hC4
    obtain ⟨n', k', hDc, hD3, w, hw, hk, hnk⟩ : ∃ n' k', IsCycle hQ.unrooted.graph D ∧
        D.ncard = n' ∧ ∃ w, IsHybridNodeOf hQ.unrooted D w ∧
          {x | DescendsFrom hQ.unrooted w x}.ncard = k' ∧ ((n' = 3 ∧ k' = 1) ∨ n' = 4) := by
      rcases hD with ⟨hDc, hD3, w, hw, hk⟩ | ⟨k, hDc, hD4, w, hw, hk⟩
      · exact ⟨3, 1, hDc, hD3, w, hw, hk, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨4, k, hDc, hD4, w, hw, hk, Or.inr rfl⟩
    obtain ⟨g₁, -, g₂, -, hne, hd₁, hd₂, ht₁, ht₂⟩ := id hw
    obtain ⟨hC, hC'⟩ := hcyc D hDc w hw
    rw [hD3, hk] at hC hC'
    have hne' : sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₁) ≠
        sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₂) := fun h =>
      hne (φ.edge.injective (sdArc_injective _ _ _ h))
    have hT : ∀ {V₂ E₂ : Type} [Fintype V₂] [Fintype E₂] {Q₂ : RootedNetwork V₂ E₂ X} {C₂ v₂},
        InducesCycleType Q₂ C₂ v₂ n' k' →
          (∃ k, InducesCycleType Q₂ C₂ v₂ 4 k) ∨ InducesCycleType Q₂ C₂ v₂ 3 1 := by
      intro V₂ E₂ _ _ Q₂ C₂ v₂ h
      rcases hnk with ⟨rfl, rfl⟩ | rfl
      · exact Or.inr h
      · exact Or.inl ⟨_, h⟩
    funext q
    rw [lemma10 hQ (hT hC) (fun h => hne (sdArc_injective _ _ _ h)) (harc g₁ w ht₁)
        (harc g₂ w ht₂) q,
      lemma10 hQ' (hT hC') hne' (harc' g₁ w ht₁ hd₁) (harc' g₂ w ht₂ hd₂) q, hγ g₁ hd₁,
      congrFun (hdel D hDc w hw g₁ hd₁ ht₁) q, congrFun (hdel D hDc w hw g₂ hd₂ ht₂) q]
  by_cases hE : ∃ D, IsCycleType hQ.unrooted D 3 2
  · -- Lemma 11
    obtain ⟨D, hD⟩ := hE
    obtain ⟨hDc, hD3, w, hw, hk⟩ := id hD
    obtain ⟨g₁, -, g₂, -, hne, hd₁, hd₂, ht₁, ht₂⟩ := id hw
    obtain ⟨hC, hC'⟩ := hcyc D hDc w hw
    rw [hD3, hk] at hC hC'
    -- the cycle `D` of `Q⁻` is its only cycle, and `φ D` the only cycle of `Q̃⁻`
    have hnot : ∀ D' n' k', IsCycleType hQ.unrooted D' n' k' →
        ((n' = 2 ∧ 1 ≤ k' ∧ k' ≤ 3) ∨ (n' = 3 ∧ (k' = 1 ∨ k' = 2)) ∨ (n' = 4 ∧ k' = 1)) →
        D' = D := by
      intro D' n' k' hDt hcases
      rcases hcases with ⟨rfl, h1, h3⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
      · exfalso
        interval_cases k'
        · exact hA ⟨D', Or.inl hDt⟩
        · exact hB ⟨D', hDt⟩
        · exact hA ⟨D', Or.inr hDt⟩
      · exact absurd ⟨D', Or.inl hDt⟩ hC4
      · exact (lemma6 hQ).1 D' D hDt hD
      · exact absurd ⟨D', Or.inr ⟨1, hDt⟩⟩ hC4
    have hone : ∀ C', IsCycle Q.graph C' →
        C' = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D := by
      intro C' hC'c
      obtain ⟨D', hD', rfl⟩ := exists_liftEdges_eq hQ.binary.1 hQ.binary.2 hQ.nontrivial hr hQ.binary hC'c
      obtain ⟨n', k', hDt, hcases⟩ := exists_isCycleType_of_isCycle hQ hD'
      rw [hnot D' n' k' hDt hcases]
    have hone' : ∀ C', IsCycle Q'.graph C' →
        C' = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D) := by
      intro C' hC'c
      obtain ⟨D', hD', rfl⟩ := exists_liftEdges_eq hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial hr' hQ'.binary hC'c
      obtain ⟨n', k', hDt, hcases⟩ := exists_isCycleType_of_isCycle hQ' hD'
      have h := hnot _ n' k' (φ.symm.isCycleType_image hDt) hcases
      rw [← h]
      congr 1
      exact (φ.edge.image_symm_image D').symm
    -- the taxa `a`, `b` below the hybrid node
    obtain ⟨a, b, hab, hs⟩ := Set.ncard_eq_two.1 hC.2.2.2.2
    have hbelow : ∀ x, Q.graph.Reaches (sdVert hQ.binary.1 hQ.nontrivial w) (Q.leaf x) ↔
        x = a ∨ x = b := fun x => by
      have := Set.ext_iff.1 hs x
      simpa using this
    have hbelowD : ∀ x, DescendsFrom hQ.unrooted w x ↔ x = a ∨ x = b := fun x =>
      (descendsFrom_semidirected_iff _ _ _ w hC.2.2.1 x).trans (hbelow x)
    have hbelow' : ∀ x, Q'.graph.Reaches (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w))
        (Q'.leaf x) ↔ x = a ∨ x = b := fun x =>
      (descendsFrom_semidirected_iff _ _ _ (φ.vert w) hC'.2.2.1 x).symm.trans
        ((φ.descendsFrom_iff w x).trans (hbelowD x))
    have hbelow_ba : ∀ x, Q.graph.Reaches (sdVert hQ.binary.1 hQ.nontrivial w) (Q.leaf x) ↔
        x = b ∨ x = a := fun x => (hbelow x).trans or_comm
    have hbelow_ba' : ∀ x, Q'.graph.Reaches (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w))
        (Q'.leaf x) ↔ x = b ∨ x = a := fun x => (hbelow' x).trans or_comm
    -- the child edges of the hybrid nodes
    obtain ⟨c, hc, -⟩ := existsUnique_child_of_hybrid hQ.binary hC.2.2.1
    obtain ⟨c', hc', -⟩ := existsUnique_child_of_hybrid hQ'.binary hC'.2.2.1
    let c₀ : {e // ∀ C', IsCycle Q.graph C' →
        C' = liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial D → e ∉ C'} :=
      ⟨c, fun C' _ hC'e => hC'e ▸
        notMem_of_source_eq_hybrid hQ.binary hQ.levelOne hC.1 hC.2.1 hC.2.2.1 hc⟩
    let c₀' : {e // ∀ C', IsCycle Q'.graph C' →
        C' = liftEdges hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge '' D) → e ∉ C'} :=
      ⟨c', fun C' _ hC'e => hC'e ▸
        notMem_of_source_eq_hybrid hQ'.binary hQ'.levelOne hC'.1 hC'.2.1 hC'.2.2.1 hc'⟩
    have e := probLineages_condCF_eq_of_threeTwo hQ hQ' φ hDc hone hone' hw hk hc hc' c₀ rfl c₀' rfl
    have hne₁ : sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g₁ ≠
        sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g₂ := fun h => hne (sdArc_injective _ _ _ h)
    have hne' : sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₁) ≠
        sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₂) := fun h =>
      hne (φ.edge.injective (sdArc_injective _ _ _ h))
    -- `Q_a⊕` and `Q_b⊕`
    have hdisj : ∀ a b, a ≠ b →
        (∀ x, Q.graph.Reaches (sdVert hQ.binary.1 hQ.nontrivial w) (Q.leaf x) ↔ x = a ∨ x = b) →
        (∀ x, Q'.graph.Reaches (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w)) (Q'.leaf x) ↔
          x = a ∨ x = b) →
        cf (disjointNet Q (sdVert hQ.binary.1 hQ.nontrivial w)
            (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g₁)
            (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g₂) a b)
          (disjointMetric Q (sdVert hQ.binary.1 hQ.nontrivial w)
            (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g₁)
            (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g₂) θ) =
        cf (disjointNet Q' (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w))
            (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₁))
            (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₂)) a b)
          (disjointMetric Q' (sdVert hQ'.binary.1 hQ'.nontrivial (φ.vert w))
            (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₁))
            (sdArc hQ'.binary.1 hQ'.binary.2 hQ'.nontrivial (φ.edge g₂)) θ') := by
      intro a b hab hb hb'
      obtain ⟨hQa, h0a⟩ := isLSAQuartet_disjointNet hQ hC hone hne₁ (harc g₁ w ht₁)
        (harc g₂ w ht₂) hab hb
      obtain ⟨hQa', -⟩ := isLSAQuartet_disjointNet hQ' hC' hone' hne' (harc' g₁ w ht₁ hd₁)
        (harc' g₂ w ht₂ hd₂) hab hb'
      refine IH hQa hQa' ?_ (nonempty_sdMetricIso_disjointNet hQ hQ' φ hne hd₁ hd₂ ht₁ ht₂ hab
        hQa.binary hQa.isLSA hQa'.binary hQa'.isLSA)
      have h0 : {D | IsCycle (disjointNet Q (sdVert hQ.binary.1 hQ.nontrivial w)
          (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g₁)
          (sdArc hQ.binary.1 hQ.binary.2 hQ.nontrivial g₂) a b).graph D} = ∅ :=
        Set.eq_empty_of_forall_notMem h0a
      rw [h0, Set.ncard_empty]
      exact (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hC.1⟩
    have ha : Q.graph.Reaches (sdVert hQ.binary.1 hQ.nontrivial w) (Q.leaf a) :=
      (hbelow a).2 (Or.inl rfl)
    have hb : Q.graph.Reaches (sdVert hQ.binary.1 hQ.nontrivial w) (Q.leaf b) :=
      (hbelow b).2 (Or.inr rfl)
    have ha' := (hbelow' a).2 (Or.inl rfl)
    have hb' := (hbelow' b).2 (Or.inr rfl)
    funext q
    rw [lemma11 hQ hC hne₁ (harc g₁ w ht₁) (harc g₂ w ht₂) hc c₀ rfl hab ha hb q,
      lemma11 hQ' hC' hne' (harc' g₁ w ht₁ hd₁) (harc' g₂ w ht₂ hd₂) hc' c₀' rfl hab ha' hb' q,
      hγ g₁ hd₁, congrFun (hdel D hDc w hw g₁ hd₁ ht₁) q, congrFun (hdel D hDc w hw g₂ hd₂ ht₂) q,
      e.1, e.2.1, e.2.2 q, congrFun (hdisj a b hab hbelow hbelow') q,
      congrFun (hdisj b a hab.symm hbelow_ba hbelow_ba') q]
  · -- no cycle: the base case
    have hnone : ∀ D, ¬ IsCycle hQ.unrooted.graph D := by
      intro D hD
      obtain ⟨n', k', hDt, hcases⟩ := exists_isCycleType_of_isCycle hQ hD
      rcases hcases with ⟨rfl, h1, h3⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
      · interval_cases k'
        · exact hA ⟨D, Or.inl hDt⟩
        · exact hB ⟨D, hDt⟩
        · exact hA ⟨D, Or.inr hDt⟩
      · exact hC4 ⟨D, Or.inl hDt⟩
      · exact hE ⟨D, hDt⟩
      · exact hC4 ⟨D, Or.inr ⟨1, hDt⟩⟩
    refine cf_eq_of_forall_not_isCycle hQ hQ' (fun C hC => ?_) (fun C hC => ?_) φ
    · obtain ⟨D, hD, -⟩ := exists_liftEdges_eq _ _ _ hr hQ.binary hC
      exact hnone D hD
    · obtain ⟨D, hD, -⟩ := exists_liftEdges_eq _ _ _ hr' hQ'.binary hC
      exact hnone _ ((φ.isCycle_iff_symm_image D).1 hD)


/-- An LSA quartet network on any types of nodes and edges is isomorphic to one on `Type`, with the
same concordance factors and an isomorphic metric unrooted network. -/
theorem exists_isLSAQuartet_type {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) :
    ∃ (V₀ E₀ : Type) (_ : Fintype V₀) (_ : Fintype E₀) (Q₀ : RootedNetwork V₀ E₀ X)
      (θ₀ : MetricData E₀) (hQ₀ : IsLSAQuartet Q₀ θ₀), cf Q₀ θ₀ = cf Q θ ∧
      Nonempty (SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ)
        hQ₀.unrooted (unrootedMetric Q₀ hQ₀.binary hQ₀.nontrivial θ₀)) := by
  set φ := finCopyIso Q
  have hlen : ∀ e, (finCopyMetric θ).length (φ.arc e) = θ.length e := fun e => by
    simp [finCopyMetric, φ, finCopyIso]
  have hinh : ∀ e, (finCopyMetric θ).inheritance (φ.arc e) = θ.inheritance e := fun e => by
    simp [finCopyMetric, φ, finCopyIso]
  have hQ₀ : IsLSAQuartet (finCopy Q) (finCopyMetric θ) :=
    ⟨φ.isBinaryRootedNetwork hQ.binary, φ.isLevelOne hQ.levelOne, φ.isLSANetwork hQ.isLSA,
      hQ.card_taxa, φ.isMetricNetwork hlen hinh hQ.metric⟩
  exact ⟨_, _, inferInstance, inferInstance, finCopy Q, finCopyMetric θ, hQ₀,
    φ.cf_eq hQ.binary.1 hlen hinh, φ.nonempty_sdMetricIso hQ.binary hQ₀.binary hQ.isLSA hQ₀.isLSA
      hQ.nontrivial hlen hinh⟩

end Proposition5

/-- **Proposition 5** (`prop::CFunrooted`): two LSA quartet networks that induce the same metric unrooted
network have the same concordance factors.

The paper's proof, by induction on the number of cycles (`proposition5_aux`), for networks renamed to
`Type` (`exists_isLSAQuartet_type`). With no cycle the networks are trees, and the root placement does
not matter (`pub:rootplace`, `External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`,
the source's Theorem 9 and Proposition 11; the paper cites Proposition 3 of Allman, Degnan, Rhodes 2011,
which as printed states identifiability). Otherwise Lemmas 7–11 are applied to corresponding cycles of
`Q⊕` and `Q̃⊕`. The cycles are reduced in this order: `2₁`- and `2₃`-cycles (Lemmas 7 and 8), then
`2₂`-cycles (Lemma 9), then `3₁`- and 4-cycles (Lemma 10), then the `3₂`-cycle (Lemma 11), which is
then the only cycle (Lemma 6). This order fills a step the paper leaves unstated (TeX 810–812): Lemma 11
has the terms `P(K = k)` and `CF(Q₀⊕ | K = 1)`, which are not concordance factors of networks with fewer
cycles; with the `3₂`-cycle alone, the child of its hybrid node is the parent of the two taxa below it,
and these terms are `1 - e^{-ℓ}`, `e^{-ℓ}` and the indicator of the cherry of these taxa, for the length
`ℓ` of the edge out of the hybrid node, which the isomorphism keeps. -/
theorem proposition5 {V' E' : Type*} [Fintype V'] [Fintype E'] {Q : RootedNetwork V E X}
    {θ : MetricData E} (hQ : IsLSAQuartet Q θ) {Q' : RootedNetwork V' E' X} {θ' : MetricData E'}
    (hQ' : IsLSAQuartet Q' θ')
    (hiso : Nonempty (SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ)
      hQ'.unrooted (unrootedMetric Q' hQ'.binary hQ'.nontrivial θ'))) :
    cf Q θ = cf Q' θ' := by
  obtain ⟨V₀, E₀, _, _, Q₀, θ₀, hQ₀, hcf₀, ⟨ψ₀⟩⟩ := exists_isLSAQuartet_type hQ
  obtain ⟨V₁, E₁, _, _, Q₁, θ₁, hQ₁, hcf₁, ⟨ψ₁⟩⟩ := exists_isLSAQuartet_type hQ'
  obtain ⟨φ⟩ := hiso
  rw [← hcf₀, ← hcf₁]
  exact proposition5_aux _ hQ₀ hQ₁ le_rfl ⟨(ψ₀.symm.trans φ).trans ψ₁⟩

/-- The metric of `Q⁻_s`: that of `(Q⊕_s)⁻` from the induced metric of `Q⊕_s`. -/
abbrev quartetUnrootedMetric (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (s : Finset X)
    (hs : #s = 4) (θ : MetricData E) :=
  unrootedMetric (quartetLSA N hN.1 s hs) (quartetLSA_isBinaryRootedNetwork hN hs)
    (Finset.one_lt_card_iff_nontrivial.mp (by omega)).coe_sort
    (inducedMetric hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty θ)

omit [Fintype V] [Fintype X] in
/-- **`Q⊕_s` is an LSA quartet network**, with the parameters it inherits from `N`. -/
theorem quartetLSA_isLSAQuartet {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {θ : MetricData E} (hθ : IsMetricNetwork N θ) {s : Finset X}
    (hs : #s = 4) : IsLSAQuartet (quartetLSA N hN.1 s hs)
      (inducedMetric hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty θ)
      where
  binary := quartetLSA_isBinaryRootedNetwork hN hs
  levelOne := isLevelOne_quartetLSA hN h1 hs
  isLSA := isLSANetwork_quartetLSA hN hs
  card_taxa := by simp [hs]
  metric := isMetricNetwork_quartetLSA hN hθ hs

/-- **Corollary 3** (`cor::quartetisgood`): under the network multispecies coalescent on a level-1 rooted
metric network, `CF_abcd = CF(Q⊕_abcd)` (Theorem 2) can be computed from the metric unrooted network
`Q⁻_abcd`: two networks whose induced unrooted networks on `s` are isomorphic have the same concordance
factors on `s`. -/
theorem corollary3 {V' E' : Type*} [Fintype V'] [Fintype E'] {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) {θ : MetricData E}
    (hθ : IsMetricNetwork N θ) {N' : RootedNetwork V' E' X} (hN' : IsBinaryRootedNetwork N')
    (h1' : IsLevelOne N'.graph) {θ' : MetricData E'} (hθ' : IsMetricNetwork N' θ') {s : Finset X}
    (hs : #s = 4)
    (hiso : Nonempty (SDMetricIso (quartetUnrooted N hN s hs) (quartetUnrootedMetric N hN s hs θ)
      (quartetUnrooted N' hN' s hs) (quartetUnrootedMetric N' hN' s hs θ')))
    (q : QuartetTree X) (hq : q.taxa = s) :
    cf N θ q = cf N' θ' q := by
  obtain ⟨r, rfl⟩ := NMSC.exists_map_val_eq hq
  have e := congrFun (proposition5 (quartetLSA_isLSAQuartet hN h1 hθ hs)
    (quartetLSA_isLSAQuartet hN' h1' hθ' hs) hiso) r
  have e₁ := theorem2 hN h1 hθ hs r
  have e₂ := theorem2 hN' h1' hθ' hs r
  have e' : nmscCF (quartetLSA N hN.1 s hs) (inducedMetric hN.1 (s : Set X)
      (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty θ) 0 r =
      nmscCF (quartetLSA N' hN'.1 s hs) (inducedMetric hN'.1 (s : Set X)
        (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty θ') 0 r := by
    convert e using 2
  convert e₁.symm.trans (e'.trans e₂) using 2

end Banos2019
