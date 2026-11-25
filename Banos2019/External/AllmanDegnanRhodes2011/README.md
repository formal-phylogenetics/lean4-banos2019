# Allman, Degnan, Rhodes 2011

E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from the distribution
of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011), 833–862,
[doi:10.1007/s00285-010-0355-7](https://doi.org/10.1007/s00285-010-0355-7). Reference [1] of
Baños 2019.

Modules [`Banos2019.External.AllmanDegnanRhodes2011.Basic`](Basic.lean) (the statements) and
[`Banos2019.External.AllmanDegnanRhodes2011.Quartets`](Quartets.lean) (displayed quartet trees on four taxa), namespace
`External.AllmanDegnanRhodes2011`. The statements are in the source's terms: rooted species trees
`Phylogenetics.SpeciesTree X` with positive edge lengths, the multispecies coalescent with one lineage
per taxon, and the distribution `σ.unrootedDist id` of the unrooted gene tree topology. The unrooted
metric species tree `T⁻` is compared by [`SpeciesTree.SameUnrootedMetricTree`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/Hierarchy/SpeciesTree.lean#L83) (same splits, same
lengths of internal edges, where the two edges at the root merge into one: [`SpeciesTree.unrootedLength`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/Hierarchy/SpeciesTree.lean#L78)),
the rooted one `T⁺` by [`SpeciesTree.SameRootedMetricTree`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/Hierarchy/SpeciesTree.lean#L89).

## The statements and how the paper uses them

| Declaration | Statement | Used in Baños 2019 |
| --- | --- | --- |
| `quartetProb σ q` | The probability that the unrooted gene tree displays the quartet tree `q`. | The concordance factors of a species tree. |
| [`equation1`](Basic.lean#L60) | Equation (1): on four taxa, if `T⁻` has the split `ab\|cd` with internal edge length `t`, then for any rooting, binary or not, `CF_{AB\|CD} = 1 - (2/3)e^{-t}` and the two other quartet trees have `(1/3)e^{-t}`. | Section 4 (the ordering `CF_{AB\|CD} > CF_{AC\|BD} = CF_{AD\|BC}` for `t > 0`); the computation of concordance factors from the unrooted quartet network after Corollary 3 (steps ii and v) and the formulas of the examples that follow it; Proposition 6 (the quartet trees obtained after contracting the cycles have the ordering of a tree) and Proposition 10 (through the formulas of the 4-cycle). |
| [`proposition3`](Basic.lean#L87) | Proposition 3: on four taxa, two binary species trees with the same distribution have the same `T⁻`; two binary species trees with different `T⁺` have the same distribution. | Stated in Section 5 and cited in Lemma 9 and Proposition 5. |
| [`proposition4`](Basic.lean#L98) | Proposition 4: the same for species trees that need not be binary. | Stated in Section 5 and cited in Lemmas 7 and 9. |
| [`unrootedDist_eq_of_sameUnrootedMetricTree`](Basic.lean#L109) | On four taxa, two species trees with the same `T⁻`, binary or not, have the same distribution: the root placement does not matter. | Section 4 ("the quartet concordance factors do not depend on the root placement [1]"), and the proofs of Lemmas 7 and 9 and Proposition 5, where the citation of Propositions 3 and 4 is used in this form: in Lemma 7 for the two rootings `Q₁⊕`, `Q₂⊕` given `K' = 0`, in Lemma 9 for the trees `T_d`, `T_c` and `Q₀⊕` given `K_y = 2`, in Proposition 5 for the base case of two trees with the same unrooted metric tree. |

The paper applies these statements to rooted networks without hybrid edges (the quartet trees, and the
networks of Section 5 once their cycles are removed), which may have nodes of indegree one and
outdegree one. [`Banos2019.nmscCF_eq_quartetProb`](../../Quartet/Trees.lean#L792) ([`Banos2019/Quartet/Trees.lean`](../../Quartet/Trees.lean)) identifies the
concordance factors of such a network with [`quartetProb`](Basic.lean#L34) of its species tree
[`Banos2019.treeSpeciesTree`](../../Quartet/Trees.lean#L198).

## Where the proofs come from

Allman, Degnan and Rhodes 2011 is formalized in lean4-allman2011
(<https://github.com/vltanh/lean4-allman2011>), on lean4-phylogenetics's [`SpeciesTree`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/Hierarchy/SpeciesTree.lean#L57), which this
repository requires. Each statement is proved from its theorems, which follow the source's arguments:

| Declaration | Theorem of lean4-allman2011 | Its statement | The source's argument |
| --- | --- | --- | --- |
| [`equation1`](Basic.lean#L60) | [`Allman2011.n4_unrootedDist_of_mem`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/Nonbinary/FourTaxa.lean#L186), [`Allman2011.n4_unrootedDist_of_ne`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/Nonbinary/FourTaxa.lean#L198) (`Allman2011/Nonbinary/FourTaxa.lean`), with [`Allman2011.four_unrootedDist_eq_zero`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/FourTaxa/Analysis.lean#L176) (`Allman2011/FourTaxa/Analysis.lean`) | For `A \| Aᶜ` a split of `σ⁻` with `#A = 2`, any `σ` on four taxa: `σ.unrootedDist id (treeOfClusters {A}) = 1 - 2/3 * exp (-σ.unrootedLength A)`, and `1/3 * exp (-σ.unrootedLength A)` for `treeOfClusters {B}`, `#B = 2`, `B ≠ A, Aᶜ`; every other unrooted tree has probability `0`. | Section 4.1: the formulas for the five binary rootings of `ab\|cd` ([`Allman2011.fourTaxa_caterpillar`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/FourTaxa/Formulas.lean#L97), [`Allman2011.fourTaxa_balanced`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/FourTaxa/Formulas.lean#L81), with relabelling); Section 5: the nonbinary rootings `((a,b):t,c,d)` are limits of caterpillars as an edge length tends to `0`. |
| [`proposition3`](Basic.lean#L87) | [`Allman2011.proposition3`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/FourTaxa/Proposition3.lean#L171) (`Allman2011/FourTaxa/Proposition3.lean`) | The same statement. | Section 4.1: a binary `σ` on four taxa has exactly one nontrivial split, whose quartet tree is strictly the most probable, and the internal edge length is `-log((3/2)(1 - ℙ(T)))` for that quartet tree `T`; the caterpillars `(((a,b),c),d)` and `(((a,b),d),c)` have the same distribution. |
| [`proposition4`](Basic.lean#L98) | [`Allman2011.proposition11_proposition3`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/Nonbinary/Proposition11.lean#L66) (`Allman2011/Nonbinary/Proposition11.lean`) | The same statement. | Proposition 11 for Proposition 3: by Section 5 the distribution of any species tree on four taxa determines its unrooted metric tree ([`Allman2011.unrootedDist_eq_iff_four`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/Nonbinary/FourTaxa.lean#L277)); the same two caterpillars. |
| [`unrootedDist_eq_of_sameUnrootedMetricTree`](Basic.lean#L109) | `(Allman2011.unrootedDist_eq_iff_four hX σ σ').2` (`Allman2011/Nonbinary/FourTaxa.lean`) | On four taxa, `σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ'`. | Theorem 9 for four taxa and Proposition 11: the quartet probabilities depend only on `σ⁻` (Sections 4.1 and 5). For binary trees it is [`Allman2011.theorem9_four`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/Identifiability/Theorem9.lean#L245). |

[`equation1`](Basic.lean#L60) is stated with [`quartetProb`](Basic.lean#L34), the sum over the unrooted gene trees that display the
quartet tree, while lean4-allman2011 gives the probabilities of the unrooted gene trees
`treeOfClusters {B}`. The two are linked in [`Banos2019.External.AllmanDegnanRhodes2011.Quartets`](Quartets.lean): on
four taxa the unrooted tree `treeOfClusters {C}` (`#C = 2`) displays the quartet tree `r` exactly when
`treeOfClusters {C} = treeOfClusters {B}` for a cherry `B` of `r` ([`displays_treeOfClusters_iff`](Quartets.lean#L109)), so
that, with [`Allman2011.four_unrootedDist_eq_zero`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/FourTaxa/Analysis.lean#L176) as the hypothesis on the support,
`quartetProb σ r = σ.unrootedDist id (treeOfClusters {B})` ([`quartetProb_eq_of_support`](Basic.lean#L41), in `Basic`).
