module

public import Banos2019.External.AllmanDegnanRhodes2011.Quartets
public import Allman2011.FourTaxa.Analysis
public import Allman2011.FourTaxa.Proposition3
public import Allman2011.Nonbinary.FourTaxa
public import Allman2011.Nonbinary.Proposition11
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
  have hsupp : ∀ T, (∀ C : Finset X, #C = 2 → T ≠ treeOfClusters {C}) → σ.unrootedDist id T = 0 :=
    fun T hT => Allman2011.four_unrootedDist_eq_zero hX σ T hT
  have hab : ({a, b} : Finset X) ∈ q.val := by rw [hq]; simp
  have hab2 : #({a, b} : Finset X) = 2 := q.card_of_mem hab
  refine ⟨?_, fun r hr => ?_⟩
  · rw [quartetProb_eq_of_support hX σ hsupp q hab]
    exact Allman2011.n4_unrootedDist_of_mem hX σ hsplit hab2
  · obtain ⟨B, hB⟩ : r.val.Nonempty := Finset.card_pos.1 (by rw [r.2.1]; norm_num)
    rw [quartetProb_eq_of_support hX σ hsupp r hB]
    have hne : r ≠ q := (Finset.mem_filter.1 hr).2.2
    refine Allman2011.n4_unrootedDist_of_ne hX σ hsplit hab2 (r.card_of_mem hB) ?_ ?_
    · rintro rfl
      exact hne (Subtype.ext ((val_eq_pair_compl hX r hB).trans (val_eq_pair_compl hX q hab).symm))
    · rintro rfl
      refine hne (Subtype.ext ?_)
      rw [val_eq_pair_compl hX r hB, val_eq_pair_compl hX q hab, compl_compl, Finset.pair_comm]

/-- **Proposition 3** of Baños 2019 (`pub:prop3`), "proven in [1]" (Allman, Degnan, Rhodes 2011,
Proposition 3): for four taxa, the unrooted metric species tree `T⁻` is identifiable from the
distribution of unrooted gene trees under the multispecies coalescent on a binary `T⁺`, and `T⁺` is not:
two binary species trees with the same distribution have the same unrooted metric tree, and two binary
species trees with different rooted metric trees have the same distribution. It is the source's
Proposition 3, as lean4-allman2011 proves it (`Allman2011.proposition3`). -/
theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
      σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
    ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
      σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' :=
  Allman2011.proposition3 hX

/-- **Proposition 4** of Baños 2019 (`pub:prop4`), "proven in [1]" (Allman, Degnan, Rhodes 2011,
Proposition 11 applied to Proposition 3): Proposition 3 remains valid when the species tree is not
binary. It is the source's Proposition 11 for Proposition 3, as lean4-allman2011 proves it
(`Allman2011.proposition11_proposition3`). -/
theorem proposition4 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
    ∃ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' :=
  Allman2011.proposition11_proposition3 hX

/-- **The root placement does not matter** (`pub:rootplace`): on four taxa, species trees with the same
unrooted metric tree, binary or not, have the same distribution of unrooted gene trees. Baños 2019 states
it in Section 4 ("it is known that the quartet concordance factors do not depend on the root placement
[1]") and uses it in the proofs of Lemmas 7 and 9 and Proposition 5, where it cites Propositions 3 and 4:
"`T⁺` is not identifiable" is read there as this statement, which Allman, Degnan, Rhodes 2011 prove
(Theorem 9 and Proposition 11, for four taxa): lean4-allman2011's `Allman2011.unrootedDist_eq_iff_four`. -/
theorem unrootedDist_eq_of_sameUnrootedMetricTree (hX : Fintype.card X = 4) {σ σ' : SpeciesTree X}
    (h : σ.SameUnrootedMetricTree σ') : σ.unrootedDist id = σ'.unrootedDist id :=
  (Allman2011.unrootedDist_eq_iff_four hX σ σ').2 h

end External.AllmanDegnanRhodes2011
