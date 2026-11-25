module

public import Banos2019.Quartet.Defs
public import Phylogenetics.Tree.Splice
public import Phylogenetics.NMSC.Induced

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
of the four lineages arriving there; a forest with a cluster of two lineages decides the quartet tree,
and with four lineages there the three quartet trees are equally likely by exchangeability
(`NMSC.cherryMass_atInj`), whatever lies above the LSA. The library proves it for every network and
every correlation; the level-1 hypothesis is not needed. -/
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

/-- **Lemma 7** (`lem::formula2:1`): contracting a cycle that induces a `2₁`-cycle does not change the
concordance factors: `CF(Q⊕) = CF(Q₀⊕)`. -/
theorem lemma7 (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 2 1) :
    cf Q θ = cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) := by
  sorry

/-- **Lemma 8** (`lem::formula2:3`): contracting a cycle that induces a `2₃`-cycle does not change the
concordance factors. -/
theorem lemma8 (hQ : IsLSAQuartet Q θ) (hC : InducesCycleType Q C v 2 3) :
    cf Q θ = cf (contractRooted Q (· = C)) (contractMetric Q (· = C) θ) := by
  sorry

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

/-- **Lemma 10** (`lem::formula43:1`): for a cycle inducing a 4-cycle or a `3₁`-cycle,
`CF(Q⊕) = γ CF(Q₁⊕) + (1 - γ) CF(Q₂⊕)`. -/
theorem lemma10 (hQ : IsLSAQuartet Q θ)
    (hC : (∃ k, InducesCycleType Q C v 4 k) ∨ InducesCycleType Q C v 3 1) {h₁ h₂ : E}
    (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) (q : QuartetTree X) :
    cf Q θ q =
      θ.inheritance h₁ * cf (deleteArc Q h₂) (deleteArcMetric Q h₂ θ) q +
        (1 - θ.inheritance h₁) * cf (deleteArc Q h₁) (deleteArcMetric Q h₁ θ) q := by
  sorry

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
