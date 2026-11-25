module

public import Banos2019.Quartet.Defs
public import Phylogenetics.Tree.Splice
public import Phylogenetics.NMSC.Induced
public import Banos2019.Quartet.Contract

/-!
# Computing quartet concordance factors (Baños 2019, Section 5)

An *LSA quartet network* (`IsLSAQuartet`) is a metric binary rooted level-1 network on four taxa whose
root is the LSA of its taxa: `Q⊕_abcd` for a network on more taxa, and its own `Q⊕` for itself. Its
concordance factors are `cf Q θ`, a function on the quartet trees.

* `lemma5`, `lemma6`: the cycles of `Q⁻`.
* `observation1`, `theorem2`.
* `lemma7`, `lemma8`, `corollary2`, `lemma9`, `lemma10`, `lemma11`: the reduction formulas.
* `proposition5`, `corollary3`: the concordance factors depend only on the unrooted network.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
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
theorem IsLSAQuartet.nontrivial {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ) :
    Nontrivial X :=
  Fintype.one_lt_card_iff_nontrivial.mp (by rw [hQ.card_taxa]; norm_num)

/-- `Q⁻`, the unrooted network of an LSA quartet network. -/
abbrev IsLSAQuartet.unrooted {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ) :=
  Banos2019.unrooted Q hQ.binary hQ.nontrivial

/-- **The cycles of `Q⁻` are those of `Q⊕`** (Section 5, the paragraph before Lemma 5): a cycle of `Q⊕`
with hybrid node `v` induces an `n_k`-cycle of `Q⁻` exactly when its image is an `n_k`-cycle of `Q⁻`,
and every cycle of `Q⁻` is such an image. The edge of `Q⁻` merged at the root stands for both edges at
the root; the others are the edges of `Q⊕`. -/
theorem inducesCycleType_iff {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    (n k : ℕ) :
    (∃ C v, InducesCycleType Q C v n k) ↔ ∃ C, IsCycleType hQ.unrooted C n k := by
  sorry

/-- **Lemma 5** (`lem:numberofcycles`): `Q⁻` has no `k`-cycle for `k ≥ 5`, at most one 4-cycle, and then
no 3-cycle, and at most two 3-cycles. -/
theorem lemma5 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ) :
    (∀ k ≥ 5, ∀ C, IsCycle hQ.unrooted.graph C → C.ncard ≠ k) ∧
      {C | IsCycle hQ.unrooted.graph C ∧ C.ncard = 4}.ncard ≤ 1 ∧
      ((∃ C, IsCycle hQ.unrooted.graph C ∧ C.ncard = 4) →
        ∀ C, IsCycle hQ.unrooted.graph C → C.ncard ≠ 3) ∧
      {C | IsCycle hQ.unrooted.graph C ∧ C.ncard = 3}.ncard ≤ 2 := by
  sorry

/-- **Lemma 6** (`lem::no2 3_2`): `Q⁻` does not have two `3₂`-cycles, nor a `2₂`-cycle and a
`4₁`-cycle. -/
theorem lemma6 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ) :
    (∀ C C', IsCycleType hQ.unrooted C 3 2 → IsCycleType hQ.unrooted C' 3 2 → C = C') ∧
      ¬ ((∃ C, IsCycleType hQ.unrooted C 2 2) ∧ ∃ C, IsCycleType hQ.unrooted C 4 1) := by
  sorry

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

This is `Phylogenetics.NMSC.nmscCF_inducedNetwork`, whose argument is the paper's: by the Markov
property at the LSA of `s` (`NMSC.sum_sum_mul_injDist_atInj`), the process is a mixture over the forest
of the four lineages arriving there; a forest with a cluster of two lineages decides the quartet tree
(Observation 1, as `NMSC.cherryMass_of_mem`), and with four lineages there the three quartet trees are
equally likely by exchangeability (`NMSC.cherryMass_atInj`), whatever lies above the LSA. The library
proves it for every phylogenetic network with valid parameters and every inheritance correlation in
`[0, 1]`; the level-1 hypothesis is not needed. -/
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

/-- Lemma 7 when the root `r` is on the cycle: with `w` the third node of `C` and `y` the other child
of `w`, the three taxa other than the taxon `d` below `v` are below `y`, and
`CF(Q⊕ ∖ b) = CF(Q₀⊕)`: both are read from the law of the forest at the top of the edge above `y`
(`jointCF_eq_sum_quartetValue`), which the two networks share. -/
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
  have hd₁ : ¬ (deleteArc Q b).graph.Reaches y ((deleteArc Q b).leaf d) := fun h =>
    hdy ((reaches_deleteArc_iff hSb _).1 h)
  have hbelow₁ : ∀ x, x ≠ d → (deleteArc Q b).graph.Reaches y ((deleteArc Q b).leaf x) :=
    fun x hx => (reaches_deleteArc_iff hSb _).2 (hbelow x hx)
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
  -- `CF = ∑ P(K' = k) CF(· | K' = k)` with `K'` the lineages at the top of `g`, in both networks
  rw [cf_eq_sum_jointCF _ _ ⟨g, hgb⟩ q, cf_eq_sum_jointCF _ _ g₀ q]
  refine sum_congr rfl fun k _ => ?_
  rw [jointCF_eq_sum_quartetValue hN₁ hθ₁ hQ.card_taxa hc₁ rfl huniq₁ hd₁ hbelow₁ k q,
    jointCF_eq_sum_quartetValue hN₀ hθ₀ hQ.card_taxa hc₀ rfl huniq₀ hd₀ hbelow₀ k q]
  refine sum_congr rfl fun t' _ => ?_
  congr 2
  unfold arcLaw
  refine sum_congr rfl fun F₁ _ => ?_
  rw [rootDist_cutLower_deleteArc hc hSb θ 0 F₁, rootDist_cutLower_contract hcyc hc hS' θ 0 F₁]
  rfl

/-- **Lemma 7** (`lem::formula2:1`): contracting a cycle that induces a `2₁`-cycle does not change the
concordance factors: `CF(Q⊕) = CF(Q₀⊕)`.

The paper's proof: one taxon is below `v`, so `P(K = 1) = 1` and `CF(Q⊕) = γ CF(Q₁⊕) + (1 - γ) CF(Q₂⊕)`
(`cf_eq_mixture`, as in Lemma 10); it remains that `CF(Q₁⊕) = CF(Q₂⊕) = CF(Q₀⊕)`. If the root is not
on `C`, only the single lineage of the taxon below `v` is on the edges in which `Q₁⊕`, `Q₂⊕` and
`Q₀⊕` differ (`cf_deleteArc_eq_contract_of_root_notMem`). If the root `r` is on `C`, with nodes
`r, u, v` and `y` the other child of `u`, the three other taxa are below `y`, and the paper conditions
on `K'`, whether a coalescent event has occurred among them before they leave `y`
(`cf_deleteArc_eq_contract_of_root_mem`): if so, the event decides the quartet tree in the three
networks alike; if not, the three networks give the same concordance factors.

Departure from the paper: for `K' = 0` the paper applies Proposition 4 (the concordance factors of a
four-taxon species tree do not depend on the root placement, `External.AllmanDegnanRhodes2011.
unrootedDist_eq_of_sameUnrootedMetricTree`) to the process above `y`; the formalization computes the
concordance factors given `K' = 0` directly, by exchangeability of the three lineages at the top of
the edge above `y` (`jointCF_eq_sum_quartetValue`: each quartet tree has probability `1/3`, the value
that Proposition 4 gives for the star tree of these four lineages). The process given `K' = 0` is a
process with injected lineages on a part of the network, not the multispecies coalescent of a
`Phylogenetics.SpeciesTree`, so Proposition 4 does not apply to it in the representation. `K'` is read
at the top of that edge (the paper's "before `a`, `b`, `c` trace back to `y`" counts at its bottom); the
argument is the same. -/
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

/-- **Corollary 2** (`cor:2isgood`): contracting all cycles that induce `2₁`- or `2₃`-cycles does not
change the concordance factors: `CF(Q⊕) = CF(Q̃⊕)`. -/
theorem corollary2 (hQ : IsLSAQuartet Q θ) :
    cf Q θ = cf (contractRooted Q (IsTwoOneOrThree Q)) (contractMetric Q (IsTwoOneOrThree Q) θ) := by
  sorry

/-- **Lemma 9** (`lem::formula2:2`): for a cycle inducing a `2₂`-cycle, with hybrid edges `h₁`, `h₂` of
its hybrid node `v` and `γ = γ(h₁)`,
`CF(Q⊕) = γ² CF(Q₁⊕) + (1 - γ)² CF(Q₂⊕) + 2γ(1 - γ) CF(Q₀⊕)`. -/
theorem lemma9 (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 2 2) {h₁ h₂ : E}
    (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) (q : QuartetTree X) :
    cf Q θ q =
      θ.inheritance h₁ ^ 2 * cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q +
        (1 - θ.inheritance h₁) ^ 2 * cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q +
        2 * θ.inheritance h₁ * (1 - θ.inheritance h₁) *
          cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) q := by
  sorry

/-- A cycle inducing a 4-cycle of `Q⁻` has a single taxon below its hybrid node (Section 5, before
Lemma 7: "if `C'_v` has size four then `l_v = 1`"): the four cycle nodes of `Q⁻` other than the hybrid
node each have taxa below them that are not below the others. -/
theorem le_one_below_of_four (hQ : IsLSAQuartet Q θ) {k : ℕ} (hC : InducesCycleType Q C v 4 k)
    (x y : X) (hx : Q.graph.Reaches v (Q.leaf x)) (hy : Q.graph.Reaches v (Q.leaf y)) : x = y := by
  sorry

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

/-- **Lemma 11** (`lem::formula3:2`): for a cycle inducing a `3₂`-cycle whose hybrid node `v` has the
taxa `a`, `b` below it, with `K` the number of lineages at `v` (at the top of its child edge `c`),
`CF(Q⊕) = γ² CF(Q₁⊕) + (1 - γ)² CF(Q₂⊕) + P(K = 1) 2γ(1 - γ) CF(Q₀⊕ | K = 1)
  + P(K = 2) γ(1 - γ) [CF(Q_a⊕) + CF(Q_b⊕)]`. -/
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
  sorry

end Reduction

/-- **Proposition 5** (`prop::CFunrooted`): two LSA quartet networks that induce the same metric unrooted
network have the same concordance factors. -/
theorem proposition5 {V' E' : Type*} [Fintype V'] [Fintype E'] {Q : RootedNetwork V E X}
    {θ : MetricData E} (hQ : IsLSAQuartet Q θ) {Q' : RootedNetwork V' E' X} {θ' : MetricData E'}
    (hQ' : IsLSAQuartet Q' θ')
    (hiso : Nonempty (SDMetricIso hQ.unrooted (unrootedMetric Q hQ.binary hQ.nontrivial θ)
      hQ'.unrooted (unrootedMetric Q' hQ'.binary hQ'.nontrivial θ'))) :
    cf Q θ = cf Q' θ' := by
  sorry

/-- The metric of `Q⁻_s`: that of `(Q⊕_s)⁻` from the induced metric of `Q⊕_s`. -/
abbrev quartetUnrootedMetric (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (s : Finset X)
    (hs : #s = 4) (θ : MetricData E) :=
  unrootedMetric (quartetLSA N hN.1 s hs) (quartetLSA_isBinaryRootedNetwork hN hs)
    (Finset.one_lt_card_iff_nontrivial.mp (by omega)).coe_sort
    (inducedMetric hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty θ)

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
  sorry

end Banos2019
