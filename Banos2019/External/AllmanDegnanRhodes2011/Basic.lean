module

public import Banos2019.External.AllmanDegnanRhodes2011.Quartets
public import Phylogenetics.MSC.Defs
public import Phylogenetics.Tree.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Allman, Degnan, Rhodes 2011: four-taxon species trees under the multispecies coalescent

E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from the distribution of
unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011), 833–862.

Baños 2019 cites this source for equation (1) and states two of its results as Propositions 3 and 4.
They are stated here in the source's terms: species trees (`Phylogenetics.SpeciesTree`) under the
multispecies coalescent, with one lineage per taxon, and the distribution of the unrooted gene tree
(`SpeciesTree.unrootedDist σ id`).
-/

@[expose] public noncomputable section

open Phylogenetics Finset
open scoped Classical

namespace External.AllmanDegnanRhodes2011

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The probability that the unrooted gene tree displays the quartet tree `q`. -/
def quartetProb (σ : SpeciesTree X) (q : QuartetTree X) : ℝ :=
  ∑ T, if Displays T q then σ.unrootedDist id T else 0

/-- On four taxa, when only the quartet trees `treeOfClusters {C}` (`#C = 2`) have positive probability,
the probability that the unrooted gene tree displays the quartet tree `r` is the probability of the
unrooted tree of the split of `r`, `B | Bᶜ` for a cherry `B` of `r`
(`displays_treeOfClusters_iff`). -/
theorem quartetProb_eq_of_support (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : ∀ T, (∀ C : Finset X, #C = 2 → T ≠ treeOfClusters {C}) → σ.unrootedDist id T = 0)
    (r : QuartetTree X) {B : Finset X} (hB : B ∈ r.val) :
    quartetProb σ r = σ.unrootedDist id (treeOfClusters {B}) := by
  unfold quartetProb
  rw [Finset.sum_eq_single (treeOfClusters {B})]
  · rw [ite_eq_left ((displays_treeOfClusters_iff hX r hB (r.card_of_mem hB)).2 rfl)]
  · intro T _ hT
    by_cases h : ∃ C : Finset X, #C = 2 ∧ T = treeOfClusters {C}
    · obtain ⟨C, hC, rfl⟩ := h
      rw [ite_eq_right fun hd => hT ((displays_treeOfClusters_iff hX r hB hC).1 hd)]
    · simp only [not_exists, not_and] at h
      rw [hσ T h, ite_self]
  · exact fun h => absurd (mem_univ _) h

/-- **Equation (1)** of Baños 2019 (`CFtree`): on a species tree whose unrooted topology has the split
`ab|cd`, with internal edge of length `t`, any rooting gives the concordance factors
`(1 - ⅔e^{-t}, ⅓e^{-t}, ⅓e^{-t})` to `ab|cd` and its two alternatives `ac|bd`, `ad|bc` (Allman, Degnan,
Rhodes 2011, Section 4.1). -/
theorem equation1 (hX : Fintype.card X = 4) (σ : SpeciesTree X) {a b c d : X} {q : QuartetTree X}
    (hq : q.val = {{a, b}, {c, d}}) (hsplit : {a, b} ∈ unroot σ.clusters) :
    quartetProb σ q = 1 - 2 / 3 * Real.exp (-σ.unrootedLength {a, b}) ∧
      ∀ r ∈ q.alternatives, quartetProb σ r = 1 / 3 * Real.exp (-σ.unrootedLength {a, b}) := by
  sorry

/-- **Proposition 3** of Baños 2019 (`pub:prop3`), "proven in [1]" (Allman, Degnan, Rhodes 2011,
Proposition 3): for four taxa, the unrooted metric species tree `T⁻` is identifiable from the
distribution of unrooted gene trees under the multispecies coalescent on a binary `T⁺`, and `T⁺` is not:
two binary species trees with the same distribution have the same unrooted metric tree, and two binary
species trees with different rooted metric trees have the same distribution. -/
theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
      σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
    ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
      σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  sorry

/-- **Proposition 4** of Baños 2019 (`pub:prop4`), "proven in [1]" (Allman, Degnan, Rhodes 2011,
Proposition 11 applied to Proposition 3): Proposition 3 remains valid when the species tree is not
binary. -/
theorem proposition4 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
    ∃ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  sorry

/-- **The root placement does not matter** (`pub:rootplace`): on four taxa, species trees with the same
unrooted metric tree, binary or not, have the same distribution of unrooted gene trees. Baños 2019 states
it in Section 4 ("it is known that the quartet concordance factors do not depend on the root placement
[1]") and uses it in the proofs of Lemmas 7 and 9 and Proposition 5, where it cites Propositions 3 and 4:
"`T⁺` is not identifiable" is read there as this statement, which Allman, Degnan, Rhodes 2011 prove
(Theorem 9 and Proposition 11, for four taxa). -/
theorem unrootedDist_eq_of_sameUnrootedMetricTree (hX : Fintype.card X = 4) {σ σ' : SpeciesTree X}
    (h : σ.SameUnrootedMetricTree σ') : σ.unrootedDist id = σ'.unrootedDist id := by
  sorry

end External.AllmanDegnanRhodes2011
