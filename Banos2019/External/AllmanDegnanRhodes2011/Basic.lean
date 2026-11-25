module

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

/-- **Equation (1)** of Baños 2019 (`CFtree`): on a species tree whose unrooted topology has the split
`ab|cd`, with internal edge of length `t`, any rooting gives the concordance factors
`(1 - ⅔e^{-t}, ⅓e^{-t}, ⅓e^{-t})` to `ab|cd` and its two alternatives `ac|bd`, `ad|bc` (Allman, Degnan,
Rhodes 2011, Section 4.1). -/
theorem equation1 (hX : Fintype.card X = 4) (σ : SpeciesTree X) {a b c d : X} {q : QuartetTree X}
    (hq : q.val = {{a, b}, {c, d}}) (hsplit : {a, b} ∈ unroot σ.clusters) :
    quartetProb σ q = 1 - 2 / 3 * Real.exp (-σ.unrootedLength {a, b}) ∧
      ∀ r ∈ q.alternatives, quartetProb σ r = 1 / 3 * Real.exp (-σ.unrootedLength {a, b}) := by
  sorry

/-- **Proposition 3** of Baños 2019 (`pub:prop3`), "proven in [1]": for four taxa, the unrooted metric
species tree `T⁻` is identifiable from the distribution of unrooted gene trees under the multispecies
coalescent on a binary `T⁺`, and `T⁺` is not. Two binary species trees have the same distribution
exactly when they have the same unrooted metric tree; and two binary species trees with different rooted
metric trees have the same distribution. -/
theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
      ((∀ T, σ.unrootedDist id T = σ'.unrootedDist id T) ↔ σ.SameUnrootedMetricTree σ')) ∧
    ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧ ¬ σ.SameRootedMetricTree σ' ∧
      ∀ T, σ.unrootedDist id T = σ'.unrootedDist id T := by
  sorry

/-- **Proposition 4** of Baños 2019 (`pub:prop4`), "proven in [1]": Proposition 3 remains valid when the
species tree is not binary. -/
theorem proposition4 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X,
      ((∀ T, σ.unrootedDist id T = σ'.unrootedDist id T) ↔ σ.SameUnrootedMetricTree σ')) ∧
    ∃ σ σ' : SpeciesTree X, ¬ σ.SameRootedMetricTree σ' ∧
      ∀ T, σ.unrootedDist id T = σ'.unrootedDist id T := by
  sorry

end External.AllmanDegnanRhodes2011
