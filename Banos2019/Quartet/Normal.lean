module

public import Banos2019.Quartet.Examples
public import Banos2019.Quartet.Transfer
public import Banos2019.External.AllmanDegnanRhodes2011.Basic
public import Banos2019.Quartet.TreeContract

/-!
# The reduced quartet networks of Sections 6 and 7

The proofs of Sections 6 and 7 reduce an LSA quartet network to a simpler one with the same
concordance factors, and read these off a figure or off equation (1).

* `halfInheritanceMetric`: a metric on a binary network, with inheritance `1/2` on hybrid edges.
* `exists_speciesTree_contractRooted` (proof of Proposition 6): without a `3₂`-cycle or a 4-cycle,
  contracting the 2-cycles and the `3₁`-cycles (the cycles satisfying `P`) leaves a tree, whose concordance factors are those of a
  species tree with an internal edge; `isTreelikeOn_quartetProb`: by equation (1), they are treelike.
* `exists_fig17` (proofs of Propositions 10 and 11): with a 4-cycle, contracting the `2₁`- and
  `2₃`-cycles gives the network of Figure 17, with the taxa named around the 4-cycle.
* `eq_of_walks_compl_of_mem_cycleNodes`: in `N⁻` of a level-1 network, two nodes of a cycle are not
  joined by a walk avoiding its edges.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### A metric on a binary network -/

/-- The parameters with lengths `ℓ`, inheritance `1/2` on the hybrid edges and `1` on the tree edges. -/
def halfInheritanceMetric (N : RootedNetwork V E X) (ℓ : E → ℝ) : MetricData E :=
  ⟨ℓ, fun e => if N.IsHybridArc e then 1 / 2 else 1⟩

/-- `halfInheritanceMetric` with positive lengths is a metric. -/
theorem isMetricNetwork_halfInheritanceMetric [Fintype E] {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) {ℓ : E → ℝ} (hℓ : ∀ e, 0 < ℓ e) :
    IsMetricNetwork N (halfInheritanceMetric N ℓ) := by
  refine ⟨⟨fun e _ => hℓ e, fun e _ => (hℓ e).le, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩, hℓ⟩
  · have : ¬ N.IsHybridArc e := by unfold IsTreeArc at he; unfold IsHybridArc; omega
    simp [halfInheritanceMetric, this]
  · simp [halfInheritanceMetric, he]
  · have h2 := indegree_eq_two_of_two_le hN hv
    have hterm : ∀ e, (if N.graph.target e = v then (halfInheritanceMetric N ℓ).inheritance e else 0) =
        if N.graph.target e = v then 1 / 2 else 0 := by
      intro e
      by_cases he : N.graph.target e = v
      · have hh : N.IsHybridArc e := by unfold IsHybridArc; rw [he]; exact hv
        simp [he, halfInheritanceMetric, hh]
      · simp [he]
    simp only [hterm]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : (univ.filter fun e => N.graph.target e = v).card = 2 := by
      rw [← h2, indegree_eq_card_filter_target]
    rw [hc]
    norm_num

variable [Fintype V] [Fintype E] [Fintype X]

omit [Fintype V] in
/-- An LSA quartet network with other metric parameters. -/
theorem IsLSAQuartet.ofMetric {Q : RootedNetwork V E X} {θ θ' : MetricData E}
    (hQ : IsLSAQuartet Q θ) (hθ' : IsMetricNetwork Q θ') : IsLSAQuartet Q θ' :=
  ⟨hQ.binary, hQ.levelOne, hQ.isLSA, hQ.card_taxa, hθ'⟩

/-! ### Without `3₂`-cycles and 4-cycles: a tree -/

/-- **The network `Q'` of Proposition 6 is a tree** (Section 6): if `Q⁻` has neither a `3₂`-cycle nor
a 4-cycle, its cycles are `2`-cycles and `3₁`-cycles, so contracting them leaves no cycle. The
concordance factors of the tree `Q'` are those of a species tree, the tree obtained by suppressing its
nodes of degree two, which has an internal edge: the contracted cycles of `Q⁻` do not separate the
four taxa into four blocks. The splits of two pairs of taxa of this species tree are those of the cut
edges of `Q⊕`: its edges are those of `Q⊕` on no cycle. -/
theorem exists_speciesTree_contractRooted {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) (h32 : ¬ ∃ C v, InducesCycleType Q C v 3 2)
    (h4 : ¬ ∃ C v k, InducesCycleType Q C v 4 k) (P : Set E → Prop)
    (hP : P = fun C => ∃ v, (∃ k, InducesCycleType Q C v 2 k) ∨ InducesCycleType Q C v 3 1) :
    ∃ σ : SpeciesTree X, (∃ (a b c d : X) (_ : Distinct4 a b c d), {a, b} ∈ unroot σ.clusters) ∧
      (∀ A : Finset X, #A = 2 → (Q.HasCutSplit ↑A ↔ A ∈ unroot σ.clusters)) ∧
      cf (contractRooted Q P) (contractMetric Q P θ) = External.AllmanDegnanRhodes2011.quartetProb σ := by
  have hX := hQ.card_taxa
  -- every cycle is a 2-cycle or a `3₁`-cycle, and is contracted
  have hall : ∀ C, IsCycle Q.graph C → P C := by
    intro C hC
    have := hQ.binary.1.finite_arcs
    obtain ⟨⟨v, ⟨hv, h2⟩, -⟩, -, -⟩ := lemma3 hQ.binary hQ.levelOne hC
    have hCt : InducesCycleType Q C v _ _ := ⟨hC, hv, h2, rfl, rfl⟩
    have hb := add_le_of_inducesCycleType hQ.binary hQ.levelOne hQ.isLSA hCt
    rw [hX] at hb
    rw [hP]
    set n := C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0)
    set k := {x | Q.graph.Reaches v (Q.leaf x)}.ncard
    rcases (by omega : n = 2 ∨ (n = 3 ∧ k = 1) ∨ (n = 3 ∧ k = 2) ∨ n = 4) with h | ⟨h, hk⟩ |
      ⟨h, hk⟩ | h
    · exact ⟨v, Or.inl ⟨k, h ▸ hCt⟩⟩
    · exact ⟨v, Or.inr (h ▸ hk ▸ hCt)⟩
    · exact absurd ⟨C, v, h ▸ hk ▸ hCt⟩ h32
    · exact absurd ⟨C, v, k, h ▸ hCt⟩ h4
  have hn3 : ∀ C, IsCycle Q.graph C → P C →
      C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0) ≤ 3 := by
    intro C _ hPC
    rw [hP] at hPC
    obtain ⟨v, ⟨k, hk⟩ | hk⟩ := hPC
    · rw [hk.2.2.2.1]
      omega
    · rw [hk.2.2.2.1]
  have hM := contractSet_isPhylogenetic (P := P) hQ.binary hQ.levelOne
  have ht := contractSet_not_isHybridArc hQ.binary hQ.levelOne hall
  have hθM := contractSet_isMetric (P := P) hQ.binary hQ.levelOne hQ.metric.1
  refine ⟨treeSpeciesTree _ hM ht hθM, ?_, fun A hA => ?_, funext fun q =>
    nmscCF_eq_quartetProb hM ht hθM (by omega) le_rfl q⟩
  · -- a cluster of two taxa
    obtain ⟨A, hA, hA2⟩ := exists_card_two_mem_treeClusters hM ht hX
      (fun W hW => by
        have := contractSet_outdegree_le hQ.binary hQ.levelOne hn3 W
        rwa [ite_eq_right hW] at this)
      (by
        have := contractSet_outdegree_le hQ.binary hQ.levelOne hn3 (contractRooted Q P).root
        rwa [ite_eq_left rfl] at this)
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hA2
    have hc : #({a, b} : Finset X)ᶜ = 2 := by rw [card_compl, hX, hA2]
    obtain ⟨c, d, hcd, hcd'⟩ := card_eq_two.1 hc
    have hcm : c ∈ ({a, b} : Finset X)ᶜ := hcd' ▸ mem_insert_self c {d}
    have hdm : d ∈ ({a, b} : Finset X)ᶜ := hcd' ▸ mem_insert_of_mem (mem_singleton_self d)
    simp only [mem_compl, mem_insert, mem_singleton, not_or] at hcm hdm
    refine ⟨a, b, c, d, ⟨hab, Ne.symm hcm.1, Ne.symm hdm.1, Ne.symm hcm.2, Ne.symm hdm.2, hcd⟩,
      mem_unroot.2 (Or.inl ⟨hA, fun h => ?_⟩)⟩
    rw [h, card_univ, hX] at hA2
    omega
  · -- the cut edges of `Q` are those of the tree
    have hne : A.Nonempty := card_pos.1 (by omega)
    have hne' : Aᶜ.Nonempty := card_pos.1 (by rw [card_compl, hX]; omega)
    exact (contractSet_hasCutSplit_iff hQ.binary hQ.levelOne (P := P) ↑A).symm.trans
      (hasCutSplit_iff_mem_unroot_treeClusters hM ht hne hne')

/-- **The concordance factors of a species tree are treelike** (equation (1)): on a species tree with
the split `ab|cd`, those of the two alternatives `ac|bd`, `ad|bc` are equal and smaller. -/
theorem isTreelikeOn_quartetProb (hX : Fintype.card X = 4) (σ : SpeciesTree X) {a b c d : X}
    (h : Distinct4 a b c d) (hsplit : {a, b} ∈ unroot σ.clusters) :
    IsTreelikeOn (External.AllmanDegnanRhodes2011.quartetProb σ) {a, b, c, d} := by
  obtain ⟨h₁, h₂⟩ := External.AllmanDegnanRhodes2011.equation1 hX σ
    (q := quartetTree a b c d h) rfl hsplit
  have m₁ : quartetTree a c b d (distinct4_acbd h) ∈ (quartetTree a b c d h).alternatives := by
    rw [QuartetTree.mem_alternatives, quartetTree_taxa_eq_insert, quartetTree_taxa_eq_insert]
    exact ⟨by ext y; simp; tauto, (quartetTree_abcd_ne_acbd h).symm⟩
  have m₂ : quartetTree a d b c (distinct4_adbc h) ∈ (quartetTree a b c d h).alternatives := by
    rw [QuartetTree.mem_alternatives, quartetTree_taxa_eq_insert, quartetTree_taxa_eq_insert]
    exact ⟨by ext y; simp; tauto, (quartetTree_abcd_ne_adbc h).symm⟩
  have hL : 0 ≤ σ.unrootedLength {a, b} := by
    unfold SpeciesTree.unrootedLength
    exact Finset.sum_nonneg fun C hC => (σ.length_pos C (mem_filter.1 hC).1 (mem_filter.1 hC).2.1).le
  have hx : Real.exp (-σ.unrootedLength {a, b}) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [isTreelikeOn_iff_triple _ h]
  left
  rw [h₁, h₂ _ m₁, h₂ _ m₂]
  exact ⟨rfl, by linarith⟩

/-! ### With a 4-cycle: the network of Figure 17 -/

/-- **`Q'` is the network of Figure 17** (proofs of Propositions 10 and 11): if `Q⁻` has a 4-cycle `C`,
its other cycles are `2₁`- or `2₃`-cycles (Lemmas 5 and 6), and contracting them in `Q⊕` gives,
after suppressing the nodes of degree two this leaves, an LSA quartet network `Q'` whose unrooted
network is that of Figure 17: the taxa `a, b, c, d` in the blocks of consecutive nodes `u 0, …, u 3`
of `C`, `c` in the hybrid block. The edge of Figure 17 joining the nodes of `a` and `d` is a chain of
the edges `A` of `Q⊕`, the one joining the nodes of `a` and `b` a chain of the edges `B`, and the
hybrid edge from the node of `b` has the inheritance probability of the hybrid edge `h` of `Q⊕`: so
the parameters of Figure 17 are a linear function of those of `Q⊕` (the map `ν` of Proposition 10). -/
theorem exists_fig17 {Q : RootedNetwork V E X} {θ : MetricData E} (hQ : IsLSAQuartet Q θ)
    {C : Set _} (hC : IsCycle hQ.unrooted.graph C) (hC4 : C.ncard = 4) :
    ∃ (u : Fin 4 → _) (f : Fin 4 → _), IsCycleOf hQ.unrooted.graph 4 u f ∧ Set.range f = C ∧
      ∃ (a b c d : X) (_ : Distinct4 a b c d),
        a ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u 0) ∧
        b ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u 1) ∧
        c ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u 2) ∧
        d ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u 3) ∧
        ∃ (A B : Finset E) (h : E), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ Q.IsHybridArc h ∧
          ∀ θ', IsMetricNetwork Q θ' →
            ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (Q' : RootedNetwork V' E' X)
              (θ'' : MetricData E') (hQ' : IsLSAQuartet Q' θ'') (len : Fin 8 → ℝ),
              cf Q' θ'' =
                  cf (contractRooted Q (IsTwoOneOrThree Q)) (contractMetric Q (IsTwoOneOrThree Q) θ') ∧
                InducesNetwork hQ' (fig17 a b c) (figMetric len (θ'.inheritance h)) ∧
                len 4 = ∑ e ∈ A, θ'.length e ∧ len 5 = ∑ e ∈ B, θ'.length e := by
  sorry

omit [Fintype V] [Fintype X] in
/-- In `N⁻` of a binary level-1 network, two nodes of a cycle `C` are in different components of what
is left after removing the edges of `C`: a walk between them avoiding `C` would close, with a part of
`C`, a second cycle sharing edges with `C`. -/
theorem eq_of_walks_compl_of_mem_cycleNodes {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {u w : _}
    (hu : u ∈ cycleNodes (unrooted N hN hX).graph C) (hw : w ∈ cycleNodes (unrooted N hN hX).graph C)
    (huw : (unrooted N hN hX).graph.Walks Cᶜ u w) : u = w := by
  -- `N⁻` is level-1: two cycles sharing an edge share a node, so they are equal (Lemma 3)
  have h1' : IsLevelOne (unrooted N hN hX).graph := by
    rintro D D' hD hD' ⟨f, hf, hf'⟩
    exact (lemma3_unrooted hN h1 hX hD).2.2 D' hD' ⟨_, ⟨f, hf, Or.inl rfl⟩, ⟨f, hf', Or.inl rfl⟩⟩
  exact h1'.eq_of_walks_compl hC hu hw huw

end Banos2019
