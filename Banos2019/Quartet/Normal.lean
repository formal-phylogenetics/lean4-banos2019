module

public import Banos2019.Quartet.Examples
public import Banos2019.Quartet.Transfer
public import Banos2019.External.AllmanDegnanRhodes2011.Basic
public import Banos2019.Quartet.TreeContract
public import Banos2019.Quartet.FourCycleNet

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
  have hB := hQ.binary
  have h1 := hQ.levelOne
  have hXn := hQ.nontrivial
  have hr := lsa_univ_eq_root hB.1 hXn hQ.isLSA
  -- the cycle `D` of `Q⊕` of `C`, inducing a `4₁`-cycle
  set D := liftEdges hQ.binary.1 hQ.binary.2 hQ.nontrivial C with hD_def
  have hDc : IsCycle Q.graph D := isCycle_liftEdges _ _ _ hC
  have hDoff : #(cycleNodesOffRoot Q D) = 4 := by
    rw [card_cycleNodesOffRoot_liftEdges _ _ _ hr hC, hC4]
  obtain ⟨v, ⟨hvD, hv2⟩, -⟩ := (lemma3 hB h1 hDc).1
  have hDn : D.ncard - (if Q.root ∈ cycleNodes Q.graph D then 1 else 0) = 4 := by
    rw [← card_cycleNodesOffRoot hDc]; exact hDoff
  have hk : {x | Q.graph.Reaches v (Q.leaf x)}.ncard = 1 := by
    have := add_le_of_inducesCycleType hB h1 hQ.isLSA ⟨hDc, hvD, hv2, hDn, rfl⟩
    rw [hQ.card_taxa] at this
    omega
  have hDtype : InducesCycleType Q D v 4 1 := ⟨hDc, hvD, hv2, hDn, hk⟩
  -- `D` is the only cycle of `Q⊕` that is not contracted (Lemmas 5 and 6)
  have hnotP : ¬ IsTwoOneOrThree Q D := fun hP' => by
    have := ncard_sub_eq_two_of_isTwoOneOrThree hP'
    omega
  have hother : ∀ K, IsCycle Q.graph K → K ≠ D → IsTwoOneOrThree Q K := by
    intro K hK hKD
    obtain ⟨w, ⟨hwK, hw2⟩, -⟩ := (lemma3 hB h1 hK).1
    have h2 := card_add_card_le_of_cycles hB h1 hQ.isLSA hK hDc hKD
    rw [hDoff, hQ.card_taxa] at h2
    have hKt : InducesCycleType Q K w #(cycleNodesOffRoot Q K)
        {x | Q.graph.Reaches w (Q.leaf x)}.ncard :=
      ⟨hK, hwK, hw2, (card_cycleNodesOffRoot hK).symm, rfl⟩
    obtain ⟨hkn, hk1, hn2⟩ := add_le_of_inducesCycleType hB h1 hQ.isLSA hKt
    rw [hQ.card_taxa] at hkn
    have hn : #(cycleNodesOffRoot Q K) = 2 := by omega
    rw [hn] at hKt hkn
    have hk2 : {x | Q.graph.Reaches w (Q.leaf x)}.ncard ≠ 2 := fun h =>
      not_inducesCycleType_two_two_of_four hB h1 hQ.isLSA hQ.card_taxa (h ▸ hKt) hDtype
    refine ⟨w, ?_⟩
    rcases (by omega : {x | Q.graph.Reaches w (Q.leaf x)}.ncard = 1 ∨
        {x | Q.graph.Reaches w (Q.leaf x)}.ncard = 3) with h | h
    · exact Or.inl (h ▸ hKt)
    · exact Or.inr (h ▸ hKt)
  -- the network `Q'` of Corollary 2, whose only cycle `D'` is that of `D`
  obtain ⟨hQ'₀, -, hcount, htypes, -⟩ := corollary2Net_spec hQ hQ.metric
  set P := IsTwoOneOrThree Q with hP_def
  set D' := {e | contractNetFirstArc hQ.binary hQ.levelOne P e ∈ D} with hD'_def
  have hD'c : IsCycle (corollary2Net hQ).graph D' := isCycle_contractNet_preimage hDc hnotP
  have hcount1 : {K | IsCycle Q.graph K ∧ ¬ P K}.ncard = 1 := by
    rw [Set.ncard_eq_one]
    refine ⟨D, Set.ext fun K => ⟨fun ⟨hK, hPK⟩ => ?_, fun h => h ▸ ⟨hDc, hnotP⟩⟩⟩
    by_contra hKD
    exact hPK (hother K hK hKD)
  have hone' : ∀ K', IsCycle (corollary2Net hQ).graph K' → K' = D' := by
    intro K' hK'
    obtain ⟨K₀, hK₀⟩ := Set.ncard_eq_one.1 (hcount.trans hcount1)
    have a1 : K' ∈ {K | IsCycle (corollary2Net hQ).graph K} := hK'
    have a2 : D' ∈ {K | IsCycle (corollary2Net hQ).graph K} := hD'c
    rw [hK₀] at a1 a2
    exact a1.trans a2.symm
  obtain ⟨c₀, hc₀⟩ := Set.ncard_eq_one.1 hk
  obtain ⟨D₀, w', hD₀, -⟩ := (htypes 4 1 {c₀}).2 ⟨D, v, hnotP, hDtype, hc₀⟩
  rw [hone' D₀ hD₀.1] at hD₀
  -- `Q'` is a rooting of Figure 17
  obtain ⟨a, b, c, d, hd4, s, φ, hrφ⟩ := exists_rootedIso_fourOne hQ'₀ hD₀ hone'
  -- the nodes and arcs of `Q⊕` of those of the rooting
  set n : Fin 9 → V := fun i => contractNetRep hQ.binary hQ.levelOne P (φ.vert i) with hn_def
  set β : Fin 9 → E := fun j => contractNetFirstArc hQ.binary hQ.levelOne P (φ.arc j) with hβ_def
  have hninj : Function.Injective n := contractNetRep_injective.comp φ.vert.injective
  have hβinj : Function.Injective β := contractNetFirstArc_injective.comp φ.arc.injective
  have hD'φ : φ.arc '' ↑(fig17CycArcs s) = D' :=
    hone' _ (IsCycle.image_of_hom φ.vert.injective φ.arc.injective φ.source φ.target
      (isCycle_fig17Root s))
  have hmem : ∀ j, j ∈ fig17CycArcs s ↔ β j ∈ D := fun j => by
    change _ ↔ φ.arc j ∈ D'
    rw [← hD'φ, φ.arc.injective.mem_set_image]
    rfl
  have hends : ∀ j ∈ fig17CycArcs s, Q.graph.source (β j) = n (fig17RootSrc s j) ∧
      Q.graph.target (β j) = n (fig17RootTgt s j) := fun j hj => by
    obtain ⟨h₁, h₂⟩ := contractNetFirstArc_ends hDc hnotP ((hmem j).1 hj)
    exact ⟨h₁.trans (by rw [φ.source]), h₂.trans (by rw [φ.target])⟩
  have hroot : ∀ i, n i = Q.root → i = 8 := fun i h => by
    have := eq_root_of_contractNetRep_eq_root h
    rw [φ.root] at this
    exact φ.vert.injective this
  have h48 : ∀ i : Fin 4, fig17Node i ≠ 8 := by decide
  have hnr : ∀ i : Fin 4, n (fig17Node i) ≠ Q.root := fun i h => h48 i (hroot _ h)
  have hnD : ∀ i : Fin 4, n (fig17Node i) ∈ cycleNodes Q.graph D := fun i => by
    obtain ⟨j, hj, h | h⟩ := fig17_mem s i
    · exact ⟨β j, (hmem j).1 hj, Or.inl ((hends j hj).1.trans (by rw [h]))⟩
    · exact ⟨β j, (hmem j).1 hj, Or.inr ((hends j hj).2.trans (by rw [h]))⟩
  -- when the root of the rooting is on the cycle, its node is the root of `Q⊕`
  have hn8 : n 8 ∈ cycleNodes Q.graph D → n 8 = Q.root := by
    intro h8
    by_contra h8r
    have hsub : univ.image (fun i : Fin 5 => n ((![4, 5, 6, 7, 8] : Fin 5 → Fin 9) i)) ⊆
        cycleNodesOffRoot Q D := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := mem_image.1 hy
      rw [mem_cycleNodesOffRoot]
      fin_cases i
      exacts [⟨hnD 0, hnr 0⟩, ⟨hnD 1, hnr 1⟩, ⟨hnD 2, hnr 2⟩, ⟨hnD 3, hnr 3⟩, ⟨h8, h8r⟩]
    have hinj5 : Function.Injective (fun i : Fin 5 => n ((![4, 5, 6, 7, 8] : Fin 5 → Fin 9) i)) :=
      fun i j h => (by decide : Function.Injective (![4, 5, 6, 7, 8] : Fin 5 → Fin 9)) (hninj h)
    have := card_le_card hsub
    rw [card_image_of_injective _ hinj5, card_univ, Fintype.card_fin, hDoff] at this
    omega
  -- the 4-cycle `C` of `Q⁻`, read along the rooting
  have hedge : ∀ i : Fin 4, ∃ g ∈ C, Joins hQ.unrooted.graph g
      (sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial (n (fig17Node i)))
      (sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial (n (fig17Node (finRotate 4 i)))) := by
    intro i
    apply exists_joins_sdNode hQ
    rcases fig17_edge s i with ⟨j, hj, hj8, hjn⟩ | ⟨j₁, hj₁, j₂, hj₂, hne, h₁8, h₂8, h₁t, h₂t⟩
    · refine Or.inl ⟨β j, (hmem j).1 hj, ?_, ?_⟩
      · rw [(hends j hj).1]
        exact fun h => hj8 (hroot _ h)
      · unfold Joins
        rw [(hends j hj).1, (hends j hj).2]
        rcases hjn with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨by rw [h₁], by rw [h₂]⟩
        · exact Or.inr ⟨by rw [h₁], by rw [h₂]⟩
    · have h8r := hn8 ⟨β j₁, (hmem j₁).1 hj₁, Or.inl ((hends j₁ hj₁).1.trans (by rw [h₁8]))⟩
      refine Or.inr ⟨β j₁, (hmem j₁).1 hj₁, β j₂, (hmem j₂).1 hj₂, fun h => hne (hβinj h), ?_, ?_,
        ?_, ?_⟩
      · rw [(hends j₁ hj₁).1, h₁8, h8r]
      · rw [(hends j₂ hj₂).1, h₂8, h8r]
      · rw [(hends j₁ hj₁).2, h₁t]
      · rw [(hends j₂ hj₂).2, h₂t]
  choose f hfC hfj using hedge
  set u : Fin 4 → _ := fun i => sdNode hQ.binary.1 hQ.binary.2 hQ.nontrivial (n (fig17Node i))
    with hu_def
  have huinj : Function.Injective u := fun i i' h =>
    (hninj.comp (by decide : Function.Injective fig17Node)) (eq_of_sdNode_eq hQ (hnr i) (hnr i') h)
  have hcyc : IsCycleOf hQ.unrooted.graph 4 u f := by
    refine ⟨by norm_num, hfj, huinj, fun i i' h => ?_⟩
    have j₁ := hfj i
    have j₂ := hfj i'
    rw [h] at j₁
    have key : ∀ i i' : Fin 4, (i = i' ∧ finRotate 4 i = finRotate 4 i') ∨
        (i = finRotate 4 i' ∧ finRotate 4 i = i') → i = i' := by decide
    apply key
    unfold Joins at j₁ j₂
    rcases j₁ with ⟨a₁, a₂⟩ | ⟨a₁, a₂⟩ <;> rcases j₂ with ⟨b₁, b₂⟩ | ⟨b₁, b₂⟩
    · exact Or.inl ⟨huinj (a₁.symm.trans b₁), huinj (a₂.symm.trans b₂)⟩
    · exact Or.inr ⟨huinj (a₁.symm.trans b₁), huinj (a₂.symm.trans b₂)⟩
    · exact Or.inr ⟨huinj (a₂.symm.trans b₂), huinj (a₁.symm.trans b₁)⟩
    · exact Or.inl ⟨huinj (a₂.symm.trans b₂), huinj (a₁.symm.trans b₁)⟩
  have hrange : Set.range f = C := by
    refine Set.eq_of_subset_of_ncard_le (Set.range_subset_iff.2 hfC) ?_ (Set.toFinite _)
    rw [hC4, Set.ncard_range_of_injective hcyc.injective_edge, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  -- the taxa in the blocks of the nodes of `C`
  have hoff : ∀ j, j ∉ fig17CycArcs s → φ.arc j ∈ D'ᶜ := fun j hj h => hj ((hmem j).2 h)
  have hblock : ∀ (i : Fin 4) (x : X), (corollary2Net hQ).leaf x = φ.vert (fig17Leaf i) →
      x ∈ nodeBlock hQ.unrooted.graph hQ.unrooted.leaf C (u i) := by
    intro i x hx
    apply mem_nodeBlock_sdNode_of_walks hQ
    rw [← contractNetRep_leaf (hQ := hQ.binary) (h1 := hQ.levelOne) (P := P) x]
    apply walks_compl_of_contractNet_walks hDc hnotP
    rw [hx]
    rcases fig17_witness s i with ⟨j, hj, hs, ht⟩ | ⟨j₁, j₂, hj₁, hj₂, ht₁, hs₁₂, ht₂⟩
    · exact .single ⟨φ.arc j, hoff j hj, Or.inl ⟨(φ.source j).trans (congrArg φ.vert hs),
        (φ.target j).trans (congrArg φ.vert ht)⟩⟩
    · exact Relation.ReflTransGen.head (b := φ.vert (fig17RootSrc s j₁))
        ⟨φ.arc j₁, hoff j₁ hj₁, Or.inr ⟨φ.source j₁, (φ.target j₁).trans (congrArg φ.vert ht₁)⟩⟩
        (.single ⟨φ.arc j₂, hoff j₂ hj₂, Or.inl ⟨(φ.source j₂).trans (congrArg φ.vert hs₁₂.symm),
          (φ.target j₂).trans (congrArg φ.vert ht₂)⟩⟩)
  have hleaf : ∀ (i : Fin 4) (x : X), quartetLeaf9 a b c x = fig17Leaf i →
      (corollary2Net hQ).leaf x = φ.vert (fig17Leaf i) := fun i x hx =>
    (φ.leaf x).trans (congrArg φ.vert hx)
  -- the chains of the edges `4` and `5` of the figure, and the last arc of the hybrid edge `6`
  set m : Fin 8 := (![0, 0, 1, 1, 5, 5, 6] : Fin 7 → Fin 8) s with hm
  have hm4 : m ≠ 4 := fig17_merged_ne s
  set A : Finset E := contractNetChain Q hQ.binary hQ.levelOne P (φ.arc 4) with hA
  set B : Finset E := contractNetChain Q hQ.binary hQ.levelOne P (φ.arc 5) ∪
    (if m = 5 then contractNetChain Q hQ.binary hQ.levelOne P (φ.arc 8) else ∅) with hB_def
  set hyb := contractNetLastArc Q hQ.binary hQ.levelOne P (φ.arc 6) with hhyb_def
  have hne : ∀ i j : Fin 9, i ≠ j → φ.arc i ≠ φ.arc j := fun i j hij h => hij (φ.arc.injective h)
  have hAne : A.Nonempty := contractNetChain_nonempty _
  have hBne : B.Nonempty := (contractNetChain_nonempty _).mono subset_union_left
  have hAB : Disjoint A B := by
    refine disjoint_union_right.2 ⟨disjoint_contractNetChain (hne 4 5 (by decide)), ?_⟩
    split_ifs
    · exact disjoint_contractNetChain (hne 4 8 (by decide))
    · exact disjoint_empty_right _
  have hv6 : ∀ j : Fin 9, j = 6 ∨ j = 7 → (corollary2Net hQ).graph.target (φ.arc j) = φ.vert 6 := by
    rintro j (rfl | rfl) <;> rw [φ.target]
    · exact congrArg φ.vert (fig17_hybrid_tgt s).1
    · exact congrArg φ.vert (fig17_hybrid_tgt s).2
  have h67 : φ.arc 6 ≠ φ.arc 7 := hne 6 7 (by decide)
  have h2 : (corollary2Net hQ).graph.indegree (φ.vert 6) = 2 := by
    refine le_antisymm (hQ'₀.binary.indegree_le_two _) ?_
    rw [← hv6 6 (Or.inl rfl)]
    exact two_le_indegree_of_two_targets hQ'₀.binary h67 rfl
      ((hv6 7 (Or.inr rfl)).trans (hv6 6 (Or.inl rfl)).symm)
  have hhyb6 : (corollary2Net hQ).IsHybridArc (φ.arc 6) := by
    unfold IsHybridArc
    rw [hv6 6 (Or.inl rfl), h2]
  have hhyb : Q.IsHybridArc hyb := (isHybridArc_contractNet_iff ⟨a, b, hd4.1⟩ (φ.arc 6)).1 hhyb6
  refine ⟨u, f, hcyc, hrange, a, b, c, d, hd4, hblock 0 a (hleaf 0 a quartetLeaf9_a),
    hblock 1 b (hleaf 1 b (quartetLeaf9_b hd4)), hblock 2 c (hleaf 2 c (quartetLeaf9_c hd4)),
    hblock 3 d (hleaf 3 d (quartetLeaf9_d hd4)), A, B, hyb, hAne, hBne, hAB, hhyb,
    fun θ' hθ' => ?_⟩
  -- the parameters of the figure, from those of `Q⊕`
  obtain ⟨hQ'θ, hcf, -⟩ := corollary2Net_spec hQ hθ'
  set θ'' := corollary2Metric hQ θ' with hθ''
  set len : Fin 8 → ℝ := fun j => if j = m then θ''.length (φ.arc m.castSucc) + θ''.length (φ.arc 8)
    else θ''.length (φ.arc j.castSucc) with hlen_def
  have hγ : θ'.inheritance hyb = θ''.inheritance (φ.arc 6) :=
    (contractNetMetric_inheritance hθ'.1 (φ.arc 6)).symm
  have hsum := inheritance_add_eq_one hQ'θ.metric.1 h2 h67 (hv6 6 (Or.inl rfl)) (hv6 7 (Or.inr rfl))
  have hlenm : θ''.length (φ.arc m.castSucc) + θ''.length (φ.arc 8) = len m := by
    simp only [hlen_def, ite_eq_left rfl]
  have hlen' : ∀ j : Fin 8, j ≠ m → θ''.length (φ.arc j.castSucc) = len j := fun j hj => by
    simp only [hlen_def, ite_eq_right hj]
  have hinh : ∀ j : Fin 8, j = 6 ∨ j = 7 →
      (figMetric len (θ'.inheritance hyb)).inheritance j = θ''.inheritance (φ.arc j.castSucc) := by
    rintro j (rfl | rfl)
    · exact hγ
    · show 1 - θ'.inheritance hyb = θ''.inheritance (φ.arc 7)
      rw [hγ]
      linarith
  have hrφ' : (rootTreeArc hQ'θ.binary.1 hQ'θ.binary.2 hQ'θ.nontrivial).1 = φ.arc 8 := hrφ
  refine ⟨_, _, inferInstance, inferInstance, corollary2Net hQ, θ'', hQ'θ, len, hcf, ?_, ?_, ?_⟩
  · fin_cases s
    all_goals
      exact inducesNetwork_of_rootedIso hQ'θ φ hrφ' (by decide) (by decide) (by decide)
        (by decide) hlenm hlen' hinh
  · rw [← hlen' 4 (Ne.symm hm4)]
    exact contractNetMetric_length θ' (φ.arc 4)
  · by_cases h5 : (5 : Fin 8) = m
    · have hl5 : len 5 = θ''.length (φ.arc 5) + θ''.length (φ.arc 8) := by
        simp only [hlen_def, ite_eq_left h5]
        rw [← h5]
        rfl
      rw [hl5, hB_def, ite_eq_left h5.symm,
        sum_union (disjoint_contractNetChain (hne 5 8 (by decide))),
        ← contractNetMetric_length, ← contractNetMetric_length]
    · rw [← hlen' 5 h5, hB_def, ite_eq_right (Ne.symm h5), union_empty]
      exact contractNetMetric_length θ' (φ.arc 5)

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
