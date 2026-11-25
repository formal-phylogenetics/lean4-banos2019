# Audit of Baños 2019 and its formalization

Paper: H. Baños, *Identifying species network features from gene tree quartets under the coalescent model*,
[Bull. Math. Biol. 81 (2019), 494–534](https://doi.org/10.1007/s11538-018-0485-4). The published version is
formalized, read in the PMC author manuscript ([PMC6344282](https://pmc.ncbi.nlm.nih.gov/articles/PMC6344282/)).
The audit was made against that text and against the LaTeX source of the only arXiv version,
[arXiv:1711.10545v1](https://arxiv.org/abs/1711.10545v1). "TeX l. N" is line N of that source's file
`NetidSpringerarxiv.tex`; the docstrings and [`docs/Banos2019/route_differences.tsv`](route_differences.tsv) locate passages the same way.
Section, result and equation numbers are those of the published version. The labels of the route check are the TeX
labels of arXiv v1 (`thm::main`, `lem::MRCAproperties`, …), and `pub:…` for the results that only the published
version has.

The two versions differ as follows. The published version says "lowest stable ancestor" (LSA) for v1's "MRCA", and
"contracting" a cycle for v1's "suppressing" it (both mean removing its edges and identifying its nodes). It states
the results of Allman, Degnan and Rhodes 2011 on four-taxon species trees as its Propositions 3 and 4, so that v1's
Proposition k is the published Proposition k + 2 for k ≥ 3. It writes out the proofs of Proposition 2 (one and two
edges) and Lemma 1 (iii), and corrects a slip of v1 in the proof of Proposition 10; it has misprints of its own in
the proofs of Lemma 9, Proposition 7 and Proposition 10 (E20). Lemma 4 has a proof in v1's source, commented out, and
none in either printed version (E4).

The paper is one of those of the hub [lean4-phylo-network](https://github.com/vltanh/lean4-phylo-network), in the
collection rooted at [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), whose libraries hold the
networks, the network multispecies coalescent and the general results that this formalization uses.

Status of the formalization:

- **Proved, by the paper's arguments** except the departures of Section 7: every numbered result, that is Lemmas
  1–17, Propositions 1–13, Theorems 2–4, Corollaries 1–4, Observation 1 and Examples 2–7, with equations (6)–(9).
  Three statements are proved in corrected forms: Theorem 4, with the nodes of degree two that the contraction leaves in `Ñ` suppressed
  (E14), the second claim of Proposition 7 off the three vertices of the simplex (E9), and Proposition 13 with a
  hypothesis in place of the false step of its proof (E18). Proposition 13 as printed is refuted
  ([`Banos2019.proposition13_asPrinted_false`](../../Banos2019/Identifiability.lean#L474)).
- **Proved cited results.** Equation (1) and the paper's Propositions 3 and 4, which it takes from Allman, Degnan and
  Rhodes 2011, and the invariance of the concordance factors of a species tree under the root placement, which its
  proofs use in their place (E6). They are stated in [`Banos2019/External/AllmanDegnanRhodes2011/`](../../Banos2019/External/AllmanDegnanRhodes2011) and proved from the
  theorems of [lean4-allman2011](https://github.com/vltanh/lean4-allman2011), which formalizes that paper by its own
  arguments. That the quartet trees of a phylogenetic `X`-tree determine it (Semple, Steel 2003, cited in the proof
  of Theorem 4) is stated in [`Banos2019/External/SempleSteel2003/`](../../Banos2019/External/SempleSteel2003) and proved from the Splits Equivalence Theorem of
  lean4-phylogenetics. Lemma 3, whose proof the paper takes from Rosselló and Valiente 2009, is proved by an argument
  of the formalization's own.
- **Unconditional.** No result of the literature is assumed.
- `lake build` passes; the only `sorry`s are those of the Challenge's statements, by design. There is no `axiom`,
  `native_decide` or `implemented_by` in [`Banos2019/`](../../Banos2019) or in the Solution. [`scripts/Audit.lean`](../../scripts/Audit.lean) checks every declaration
  of this repository and of the modules of the libraries it imports, including private and generated ones, against
  the standard axioms [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- The Challenge, [`palomar/Banos2019/Challenge.lean`](../../palomar/Banos2019/Challenge.lean), states Theorems 3 and 4 and Proposition 5, with eight theorems that
  check its definitions against known facts: equation (1) on a quartet tree, the LSA, the root, the non-vacuity of
  "generic", Examples 6 and 7, and the networks of Figures 17 and 18. It imports only Mathlib; its definitions are the
  block of [`Banos2019/Defs.lean`](../../Banos2019/Defs.lean), copied by [`scripts/sync_challenge_defs.py`](../../scripts/sync_challenge_defs.py). [`palomar/Banos2019/Solution.lean`](../../palomar/Banos2019/Solution.lean) proves
  them, under the same names, from the library, through the bridges of [`Banos2019/Bridge/`](../../Banos2019/Bridge), which prove that these
  definitions are the library's. [`palomar/Banos2019/comparator.json`](../../palomar/Banos2019/comparator.json) has Comparator check that the Solution proves
  exactly the Challenge's eleven statements; Lean's kernel, NanoDa and con-ron accept them
  ([`scripts/check_kernels.sh`](../../scripts/check_kernels.sh)).
- **Proofs.** They follow the paper's arguments, except the seven departures of Section 7, each forced by an error or
  a gap in the paper's step or by the representation, and recorded with its reason. Many steps that the paper asserts
  without argument are filled along its lines (Section 3). [`docs/Banos2019/route_differences.tsv`](route_differences.tsv) records every
  difference between the results that the formal proofs use and those that the paper's proofs cite.
- No person has reviewed the proofs. Independent agents reviewed the statements and the Challenge against the paper,
  compared the proofs with the paper's, and searched the literature ([`docs/Banos2019/CREDITS.md`](CREDITS.md)).

## 1. Summary

- **Errors.**
  - Proposition 13 is false as printed: the `3₂`-cycle of `Q⁻_ijke` can come from a cycle of `N⁻` other than the
    4-cycle `C_v`. A counterexample is proved in Lean, and the corrected form (E18).
  - Theorem 4 is false as printed: `Ñ` keeps a node of degree two for each contracted 2-cycle, and where that node
    sits is not identifiable. It holds once those nodes are suppressed, as Allman et al. 2024 restate it (E14).
  - The second claim of Proposition 7 fails at the three vertices of the simplex, which its set `I` contains (E9).
  - Example 7 prints the concordance factors of Figure 17 with the taxa `b` and `c` exchanged (E10).
  - The proof of Lemma 5 miscounts the blocks of three cycles; the lemma holds (E5).
- **Gaps**, all repaired along the paper's lines; every result holds as printed or as corrected above:
  - Lemma 1 (ii), E2; Proposition 2, E3; Lemma 4, which has no printed proof, E4;
  - Proposition 5, which does not account for the terms of Lemma 11, E7; Proposition 6, E8;
  - the correspondence between the cycles of `Q⁻_s` and of `N⁻` in Lemma 12, E11; Lemma 13, which uses a generic
    lemma at given parameters, E12; Lemma 14, E13;
  - Theorem 4: its base case reads the quartet trees from the orderings without saying how, and needs a generic
    condition (E15); its induction step uses unproved claims on the tree of cycles (E16);
  - Proposition 12, which needs Corollary 4 where it cites Propositions 8 and 7, E17; Lemma 17, case 5 (ii), E19.
- **Missing hypotheses.** Definition 4 and Lemma 1 need a nonempty set of taxa (E1), and Proposition 1 at least two
  taxa (Section 4).
- **Redundant hypotheses.** Theorem 2 holds without the level-1 condition, and Proposition 11 without the Big Cycle
  property (Section 5).
- **Use of cited results.** Lemmas 7 and 9 and Proposition 5 cite Propositions 3 and 4, identifiability statements,
  for the equality of the concordance factors of two species trees with the same unrooted metric tree: that is the
  root-placement invariance, which the paper states in Section 4 from the same source (E6). Equation (1) and Semple
  and Steel's theorem are used correctly.
- **Typos.** E20.

## 2. Results from prior work and how the paper uses them

### Proved

| Result | Where the paper uses it | Source | Theorem | Argument |
| --- | --- | --- | --- | --- |
| Equation (1): on four taxa, a species tree whose unrooted tree has the split `ab\|cd` with internal edge `t` has the concordance factors `(1 - ⅔e^{-t}, ⅓e^{-t}, ⅓e^{-t})`, for any rooting | Section 4; the computation after Corollary 3; Examples 2–5; Propositions 6 and 10 | Allman, Degnan, Rhodes 2011, Sections 4.1 and 5 | [`External.AllmanDegnanRhodes2011.equation1`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L60) | The source's, in lean4-allman2011: the formulas for the binary rootings, and the nonbinary ones as limits |
| Proposition 3: for four taxa, the distribution of unrooted gene trees identifies `T⁻` and not `T⁺` | Cited in Lemma 9 and Proposition 5 (E6) | Allman, Degnan, Rhodes 2011, Proposition 3 | [`External.AllmanDegnanRhodes2011.proposition3`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L87) | The source's ([`Allman2011.proposition3`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/FourTaxa/Proposition3.lean#L171)) |
| Proposition 4: Proposition 3 for species trees that need not be binary | Cited in Lemmas 7 and 9 (E6) | Allman, Degnan, Rhodes 2011, Proposition 11 for Proposition 3 | [`External.AllmanDegnanRhodes2011.proposition4`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L98) | The source's ([`Allman2011.proposition11_proposition3`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/Nonbinary/Proposition11.lean#L66)) |
| The root placement does not matter: on four taxa, species trees with the same unrooted metric tree have the same distribution of unrooted gene trees | Section 4 ("it is known … [1]"); the steps of Lemmas 7, 9 and Proposition 5 that cite Propositions 3 and 4 (E6) | Allman, Degnan, Rhodes 2011, Theorem 9 for four taxa, and Section 5 | [`External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L110) | The source's ([`Allman2011.unrootedDist_eq_iff_four`](https://github.com/vltanh/lean4-allman2011/blob/d4ada2c6cbbb5b8629eb9740dc5d5a9984a06a78/Allman2011/Nonbinary/FourTaxa.lean#L277)) |
| Two phylogenetic `X`-trees that display the same quartet trees are isomorphic | Theorem 4, base case ("a standard result [22]") | Semple, Steel 2003 | [`External.SempleSteel2003.exists_iso_of_quartets_eq`](../../Banos2019/External/SempleSteel2003/Quartets.lean#L184) | The quartet trees give the splits ([`Phylogenetics.subset_of_forall_displays`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/Tree/Splits.lean#L737)), and the splits the tree (the Splits Equivalence Theorem, [`Phylogenetics.SplitsEquivalence.xTree_unique`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/Tree/SplitsEquivalence.lean#L604)) |
| Lemma 3: a cycle of a level-1 network has exactly one hybrid node, with both its hybrid edges; a node is on at most one cycle | Throughout, wherever the paper speaks of the hybrid node of a cycle, the cycle `C_v` or the `v`-blocks | Rosselló, Valiente 2009 | [`Banos2019.lemma3`](../../Banos2019/Network/Cycle.lean#L440), [`Banos2019.lemma3_unrooted`](../../Banos2019/Network/Induced.lean#L289) | The formalization's own: the top node of the cycle, and a count of its edges by the node they enter |

The statements of [`Banos2019/External/`](../../Banos2019/External) are in their sources' terms, on species trees ([`Phylogenetics.SpeciesTree`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/Hierarchy/SpeciesTree.lean#L57)).
The paper applies them to rooted networks without hybrid edges, which may have nodes of indegree and outdegree one;
[`Banos2019.nmscCF_eq_quartetProb`](../../Banos2019/Quartet/Trees.lean#L824) identifies the concordance factors of such a network with those of its species
tree. Propositions 3 and 4 are proved as printed, and no proof uses them (E6).

### What was read

| Source | Cited for | Read? |
| --- | --- | --- |
| Allman, Degnan, Rhodes 2011 | Equation (1), Propositions 3 and 4, the root placement | Formalized in [lean4-allman2011](https://github.com/vltanh/lean4-allman2011), from arXiv:0912.4472v2; the statements here are proved from its theorems |
| Semple, Steel 2003 | Theorem 4 | The book was not available. The statement is that of its Theorem 6.3.5 as Allman, Holder and Rhodes (arXiv:0905.4542) cite it and as S. Roch's lecture notes on the book's Chapter 6 state it; the proof goes through the splits, not the book's argument |
| Rosselló, Valiente 2009 | Lemma 3 | Not followed: Lemma 3 is proved by the formalization's own argument |

### Assumed

Nothing: the formalization is unconditional.

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| The network multispecies coalescent: Kingman's coalescent on each edge, independent inheritance at hybrid nodes, exchangeability of the lineages | Section 4; Theorem 2; Lemmas 7–11 | The library `Phylogenetics` ([`Phylogenetics.NMSC.exchangeability`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/NMSC/Exchangeability.lean#L412); the concordance factors `nmscCF N θ 0`) |
| The zero set of a real analytic function that is not identically zero is null | Proposition 10 ("contained in a proper sub-variety … has measure zero") | [`AnalyticOnNhd.volume_setOf_eq_zero`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/ForMathlib/Analysis/AnalyticZeroSet.lean#L178), in lean4-phylogenetics |
| The preimage of a null set under a surjective affine map is null | Proposition 10 ("ν is linear surjective") | [`MeasureTheory.prod_pi_volume_preimage_sum_coords_null`](../../Banos2019/Basic/MeasureTheory/SumCoordsNull.lean#L26) |
| A continuous image of a connected set is connected | Proposition 7 | Mathlib |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Allman, Degnan, Rhodes 2011, equation (1) | Section 4, the examples, Propositions 6 and 10 | Correct |
| Allman, Degnan, Rhodes 2011, Propositions 3 and 11 (the paper's Propositions 3 and 4) | Lemmas 7 and 9, Proposition 5 | Applied loosely: the steps need the root-placement invariance of the same source (E6) |
| Semple, Steel 2003 | Theorem 4, base case | Correct, once the quartet trees of `Ñ` are read from the orderings (E15) |
| Rosselló, Valiente 2009 | Lemma 3 | Lemma 3 holds as stated |

The other citations give context or definitions and are used in no proof: the network multispecies coalescent of Meng
and Kubatko 2009 and of Yu, Degnan and Nakhleh (a definition, Section 4); treks (Sullivant, Talaska, Draisma 2010, a
definition); the lowest stable ancestor (Steel 2016, a definition); Example 1's model with several samples per
population (Degnan et al. 2010); SNaQ (Solís-Lemus, Ané 2016), with the claim of its supplementary materials on
`3₂`-cycles that Example 6 refutes; the tree of blobs (Gusfield et al. 2007), set against the tree of cycles; the
combinatorial reconstructions of level-1 networks (Keijsper, Pendavingh 2014; Huber et al. 2017, 2018); and the
biological references of the introduction.

## 3. Errors and gaps in the paper

### E1. Definition 4 and Lemma 1: the empty set of taxa

Definition 4 says: "To see that LSA(Z) is well defined for any Z ⊆ X, note first that D ≠ ∅ since r ∈ D. Also, since
every pair of nodes u,v ∈ D both lie on a path, we have … a total order on D". For `Z = ∅` the set `D` of the nodes on
every path from the root to a taxon of `Z` is the set of all nodes, which are not totally ordered, and `LSA(∅)` is not
defined. Lemma 1 is stated for `Z ⊆ Y ⊆ X` ("for any Z ⊂ X" in (i)). Nothing in the paper uses `LSA(∅)`. The
formalization states Lemma 1 for nonempty `Z` ([`Banos2019.lemma1`](../../Banos2019/Network/Rooted.lean#L312)).

### E2. Lemma 1 (ii): two steps

The proof says "If both x1 and x2 had parents below LSA(Z), then x1 has a parent below x2 and x2 has a parent below
x1", and "Let z ∈ Z with z below x1", without argument for either. Both hold. A taxon of `Z` is below each child `xᵢ`
of `LSA(Z)`: otherwise every path to `Z` would leave `LSA(Z)` through the other child, a lower node on all of them. A
path from `LSA(Z)` to the other parent of `x₁`, when that parent is below `LSA(Z)`, starts with `e₂`, since through
`e₁` it would close a directed cycle. [`Banos2019.lemma1`](../../Banos2019/Network/Rooted.lean#L312) has both steps.

### E3. Proposition 2: three paths and the level-1 condition

The proof finds three paths `P₁, P₂, P₃` from the root to `m = LSA(X)`, through `e₁`, `e₂` and `(r, y)`, and states
"This contradicts the level-1 condition" without saying how (TeX l. 365–369). The step holds: the paths through `e₁`
and `y`, and through `e₂` and `y`, give two cycles through the edge `(r, x)`; by the level-1 condition they are one
cycle, whose other edge at `x` is `e₁` or `e₂` and lies on only one of them, since the path through `y` cannot enter the
tree node `x` ([`Banos2019.proposition2`](../../Banos2019/Structure.lean#L46), with [`Banos2019.exists_isCycle_of_walks`](../../Banos2019/Network/Cycle.lean#L127)).

### E4. Lemma 4: no printed proof

The published version introduces Lemma 4 with "The following is straightforward to prove" and gives no proof. The TeX
source of arXiv v1 has one, commented out (TeX l. 403–409): an edge `e` of a path from `a` to `b` lies on a cycle `C_v`
of `𝒟`, and a path from `a` to `b` avoiding `C_v` would give a cycle through `e` with edges outside `C_v`. The
formalization follows it, and closes it by the level-1 condition: that cycle is `C_v`, so all the edges of `C_v` lie
on the path, which a cycle cannot ([`Banos2019.lemma4`](../../Banos2019/Structure.lean#L431)). Corollary 1 follows from it as the paper says.

### E5. Lemma 5: the blocks of three cycles

"By removing these three cycles we induce a partition of the taxa into at least k1+k2+k3−3 blocks". When the three
cycles form a chain, the middle one joined to each of the others through a part of the network that holds no taxon,
two of the middle cycle's blocks are empty, and the count is `k₁ + k₂ + k₃ − 4`: three 3-cycles joined in a chain by
single edges, with taxa below their free nodes, leave five nonempty blocks, not six. Since `k₁ + k₂ + k₃ − 4 ≥ 5 > 4`,
the contradiction and the lemma stand ([`Banos2019.lemma5`](../../Banos2019/Quartet/Reduction.lean#L131), with [`Banos2019.card_add_card_add_card_le_of_cycles`](../../Banos2019/Quartet/CycleBlocks.lean#L560)).

### E6. Propositions 3 and 4, as Lemmas 7 and 9 and Proposition 5 use them

As printed, Proposition 3 says that for four taxa "T⁻ is identifiable from the unrooted topological gene tree
distribution under the multispecies coalescent model on T⁺, but T⁺ is not", and Proposition 4 that this "remains
valid" for nonbinary trees: the distribution determines the unrooted metric tree, and does not determine the rooted
one. The proofs cite them for the converse:

- Lemma 7: "by Proposition 4, CF(Q₁⊕ | K′ = 0) = CF(Q₂⊕ | K′ = 0) = CF(Q₀⊕ | K′ = 0)";
- Lemma 9: "By Proposition 3, CF(T_d | K_y = 2) = CF(T_c | K_y = 2)", and "By Proposition 4, CF(T_c | K_y = 2) =
  CF(Q₀⊕ | K = 2, K_y = 2)";
- Proposition 5: "Q and Q̃ are trees, and by Proposition 3, CF(Q) = CF(Q̃)".

Each step needs that two species trees on four taxa with the same unrooted metric tree have the same concordance
factors: the root placement does not matter. That `T⁺` is not identifiable gives only some pair of rooted trees with the
same distribution. The paper states the needed fact in Section 4 ("it is known that the quartet concordance factors do
not depend on the root placement [1]"), and Allman, Degnan and Rhodes 2011 prove it (Theorem 9 for four taxa, and
Section 5 for nonbinary trees; arXiv v1 cites "Proposition 3 in [Allman2011]" and "Proposition 11 in [Allman2011]").
The steps hold. The formalization states the fact as
[`External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L110) (label `pub:rootplace`) and uses it in the
three proofs (Section 7).

### E7. Proposition 5: the terms of Lemma 11

The induction step expresses "the concordance factors of Q and Q̃ in terms of networks with one fewer cycle", notes
that "these networks for Q and Q̃ have the same unrooted metric structure", and concludes from `CF(Q̃ᵢ) = CF(Qᵢ)` for
`i = 0, 1, 2` (TeX l. 810–812). Lemma 11 also has the terms `P(K = 1)`, `P(K = 2)`, `CF(Q₀⊕ | K = 1)`, `CF(Q_a⊕)` and
`CF(Q_b⊕)`. The probabilities and the conditional concordance factor are not concordance factors of networks with
fewer cycles, and the proof does not say why they agree for `Q` and `Q̃`; that the reduced networks of `Q` and `Q̃`
have isomorphic unrooted metric networks is asserted. Both hold. The formalization reduces the cycles in the order
`2₁` and `2₃`, `2₂`, `3₁` and 4, `3₂`; the `3₂`-cycle is then the only one (Lemma 6), and the extra terms are
`1 - e^{-ℓ}`, `e^{-ℓ}` and the indicator of the cherry of the two taxa below the hybrid node, for the length `ℓ` of the
edge below it, which the isomorphism keeps ([`Banos2019.probLineages_condCF_eq_of_threeTwo`](../../Banos2019/Quartet/Reduction.lean#L2879)). The isomorphisms of the
reduced networks are [`Banos2019.nonempty_sdMetricIso_reduceNet_deleteArc`](../../Banos2019/Quartet/Reduction.lean#L2758), [`Banos2019.nonempty_sdMetricIso_contractNet`](../../Banos2019/Quartet/Reduction.lean#L2786)
and [`Banos2019.nonempty_sdMetricIso_disjointNet`](../../Banos2019/Quartet/Reduction.lean#L2834).

### E8. Proposition 6: the reduced trees

The induction ends with "Since Q₀′, Q₁′, Q₂ and Q′ are trees with the same topology, their concordance factors have
the same ordering by equations (1)" (`Q₂` for `Q₂′`, E20). That the networks obtained by contracting all `2₂`- and
`3₁`-cycles are quartet trees with one internal edge, the same for all, is asserted (TeX l. 917). It holds, since each
such cycle has a block of two taxa ([`Banos2019.exists_speciesTree_contractRooted`](../../Banos2019/Quartet/Normal.lean#L89)). The induction also needs the list of
the cycles that can accompany the others, which Lemmas 5 and 6 give and the proof does not cite; the proof of
Proposition 7 uses them the same way (TeX l. 964).

### E9. Proposition 7: the vertices of the simplex

"Then CF(Q) lies in the set I defined by x > 1/6, y = z or y > 1/6, x = z or z > 1/6, x = y … Furthermore, for any
point (x,y,z) in this set there is such a Q with (x,y,z) = CF(Q)." The set contains the vertices `(1, 0, 0)`,
`(0, 1, 0)`, `(0, 0, 1)` of the simplex, and concordance factors are positive, so the second claim fails there. The
proof shows that the image of the `3₂`-cycle of Figure 18 is the open segment `L` from `(1, 0, 0)` to
`(2/12, 5/12, 5/12)`, which excludes the vertex. The correct statement is the second claim for every point of `I` other
than the vertices; [`Banos2019.proposition7`](../../Banos2019/CycleProperty.lean#L539) proves it, with the first claim as printed.

### E10. Example 7: the labels of the taxa

"Let Q̃⁻ be the 4-cycle unrooted quartet in Figure 17, where γ = 1/2, t₁ = −log(48/49) = t₂. By the equations in (8)
the concordance factors are: CF_AB|CD = 32/98, CF_AC|BD = 33/98, CF_AD|BC = 33/98". With `x = 48/49`, equation (8)
gives:

- `CF_{AB|CD} = ½(1 - ⅔x) + ½·⅓x = 17/98 + 16/98 = 33/98`;
- `CF_{AC|BD} = ½·⅓x + ½·⅓x = 32/98`;
- `CF_{AD|BC} = ½·⅓x + ½(1 - ⅔x) = 33/98`.

The printed values are those of Figure 17 with the taxa `b` and `c` exchanged. The point of the example stands: up to
the names of the taxa, the 4-cycle has the concordance factors `(32, 33, 33)/98` of the `3₂`-cycle of Example 6
([`Banos2019.example7`](../../Banos2019/Quartet/Examples.lean#L871), and [`Banos2019Challenge.example7`](../../palomar/Banos2019/Challenge.lean#L640) on the Challenge's definitions; Example 6 is
[`Banos2019.example6`](../../Banos2019/Quartet/Examples.lean#L853)).

### E11. Lemma 12: the statement, and the correspondence of cycles

The statement reads "There exists {a,b,c,d} ⊆ X satisfying the BC property if and only if N⁻ contains a cycle C_v of
size k ≥ 4 with one of these taxa is in the hybrid block, and the others in distinct v-blocks". Its proof, and every
later use of it, is about a given set of four taxa: for generic parameters, `{a, b, c, d}` satisfies the Big Cycle
property if and only if `N⁻` has a cycle `C_v` of size at least four with the four taxa in distinct `v`-blocks, one of
them in the hybrid block. [`Banos2019.lemma12`](../../Banos2019/CycleProperty.lean#L1071) states this, for all sets of four taxa at once.

The proof asserts in both directions how the cycles of `Q⁻_s` and of `N⁻` correspond (TeX l. 1102–1103): "This set of
taxa induces a unrooted quartet network with a 4-cycle", and "Since the other taxa are in distinct v-blocks of Q⁻,
they must be in distinct v-blocks of N⁻". Both hold: [`Banos2019.exists_fourCycle_of_separates`](../../Banos2019/Quartet/Correspondence.lean#L299) and
[`Banos2019.exists_separates_of_fourCycle`](../../Banos2019/Quartet/Correspondence.lean#L506).

### E12. Lemma 13: a generic lemma at given parameters

Lemma 13 is stated for given parameters, and its proof twice cites Lemma 12, which holds for generic parameters, for
"a, b, c, and d belong to different v-blocks". The direction it needs holds for all parameters: a set with the Big
Cycle property induces a 4-cycle (Proposition 9), whose taxa are in distinct blocks of the cycle of `N⁻` that it comes
from (the second half of E11). The formalization uses that direction ([`Banos2019.lemma13`](../../Banos2019/CycleProperty.lean#L1113); Section 7).

### E13. Lemma 14: the cases of `|X|`

"If |X| < 3 there is nothing to prove. The case |X| = 4 follows from Proposition 9, so we assume |X| ≥ 5." The cases
leave out `|X| = 3`, where, as for `|X| < 3`, there is no set of four taxa and nothing to prove: "< 3" reads as "< 4".
For `|X| = 4`, Proposition 9 gives only one inclusion: when `X ∉ S`, that `N⁻` has no 4-cycle needs Proposition 10.
The argument for `|X| ≥ 5` uses no bound on `|X|`, and the formalization applies it to every `X` ([`Banos2019.lemma14`](../../Banos2019/Identifiability.lean#L66);
Section 7).

### E14. Theorem 4: the network `Ñ`

`Ñ` is "obtained from N⁻ by contracting all 2- and 3-cycles, and directions of hybrid edges in 4-cycles, while
retaining directions of hybrid edges of k-cycles for k ≥ 5". Contracting a 2-cycle of `N⁻` leaves a node of degree
two, and its place is not identifiable: a cycle that induces a `2₁`- or `2₃`-cycle in every quartet network does not
change the concordance factors (Corollary 2). A binary tree, and the same tree with a 2-cycle inserted on the pendant
edge of a taxon, have the same orderings for all parameters, and their networks `Ñ`, read as printed, differ by a node
of degree two. The theorem holds when the nodes of degree two that the contraction leaves are suppressed, as every other
construction of the paper does (Definitions 5, 10 and 13, and the gluing step of the proof of Theorem 4, "identifying s1
in N2 with s2 in N1 and suppressing that node"), and as Figure 23's `Ñ` shows. arXiv v1 says "suppressing all 2- and
3-cycles", where suppressing a cycle means contracting it (TeX l. 331). Allman, Baños, Garrote-López and Rhodes 2024
restate the theorem (their Theorem 2, "Baños 2019, Theorem 4") with "suppressing degree-2 nodes", and for `|X| ≥ 4`. The
formalization's `Ñ` suppresses them ([`Banos2019.Model.SDNetwork.tilde`](../../palomar/Banos2019/Challenge.lean#L343), [`Banos2019.theorem4`](../../Banos2019/Identifiability.lean#L223)), and the Challenge's
[`Banos2019Challenge.fig17_fig18_tilde`](../../palomar/Banos2019/Challenge.lean#L660) checks that `Ñ` still tells a 4-cycle from a `3₂`-cycle.

### E15. Theorem 4: the base case

"Then every induced quartet tree will have no cycle of size 4, and the ordering of the concordance factors determines
the topology of the quartet tree obtained by contracting all 2- and 3-cycles. These then determine the topology Ñ by a
standard result [22]" (TeX l. 1180). The paper does not say that this quartet tree is the one that `Ñ` displays, nor
how the ordering tells it. The formalization fills these steps ([`Banos2019.tildeDetermined_zero`](../../Banos2019/Identify/TildeBase.lean#L813)):

- The quartet tree is the one that `Ñ` displays: an edge of `Ñ` between `{a, b}` and `{c, d}` comes from a cut arc of
  `N`, which gives a cut edge of `Q⊕_s` between them.
- The two other quartet trees on `s` have equal concordance factors: by Proposition 6 when `Q⁻_s` has no `3₂`-cycle,
  and by Proposition 7 when it has one, whose two taxa below the hybrid node lie on one side of that cut edge.
- So the quartet tree is the one whose concordance factor differs from the two others. It need not be the largest: with
  a `3₂`-cycle it can be the smallest (Example 6, `(32, 33, 33)/98`).
- This reading needs the three concordance factors not to be all equal, and with a `3₂`-cycle they can be (the
  centroid lies on the segment `L` of Proposition 7). That they are not, on any set of four taxa, holds for generic
  parameters ([`Banos2019.forGenericParams_nonDegenerateCF`](../../Banos2019/Identify/NonDegenerate.lean#L160)), and is part of the generic condition of the
  formalization's Theorem 4.
- The base case also needs that `N₂⁻` has no cycle of size at least four when `N₁⁻` has none: such a cycle would
  separate four taxa with the Big Cycle property for `N₂`, and so for `N₁` (Lemma 12).

Semple and Steel's theorem then gives the isomorphism.

### E16. Theorem 4: the induction

The induction step takes "T, the tree of cycles of Ñ" (Definition 13) and states "A leaf of T arises from a cycle C_v
on N⁻ if and only if all v-blocks but one are 4-network blocks". The paper proves neither this nor that `T` is a tree
("Since contracting cycles in level-1 networks does not introduce loops or multi-edges, we can define a notion of a tree
of cycles"). Both hold, and are proved in [`Banos2019/Identify/TreeOfCycles.lean`](../../Banos2019/Identify/TreeOfCycles.lean)
([`Banos2019.isLeafNode_iff_fourNetworkBlocks_unrooted`](../../Banos2019/Identify/TreeOfCycles.lean#L1516)). The proof also leaves these steps unstated, all filled along its
lines:

- the networks induced on `S_i ∪ {s_j}` have fewer cycles of size at least four;
- their concordance factors are those of `N` on their taxa (Proposition 1 and Theorem 2), so the generic conditions and
  the equal orderings pass to them, and their data are read from their own orderings by the arguments of Lemmas 14–16;
- `Ñ` is the gluing of the networks `Ñ` of the two pieces ([`Banos2019.tilde_sdIso_glue`](../../Banos2019/Identify/Glue.lean#L3482)): contracting the 2- and
  3-cycles and suppressing the nodes of degree two commute with taking a side of the edge of `u` off its cycle.

With one cycle of size at least four, "Doing this for all v-blocks" is an induction on the number of `v`-blocks with at
least two taxa ([`Banos2019.tildeDeterminedOneCycle`](../../Banos2019/Identify/TildeInduction.lean#L410)).

### E17. Proposition 12: Propositions 8 and 7

"Since {a,b,c,d} ⊂ X satisfy the Cycle property but not the BC property, by Proposition 8, there is a 3₂-cycle in
Q⁻_abcd." Proposition 8 gives a `3₂`-cycle or a 4-cycle, and the failure of the Big Cycle property excludes the 4-cycle
only for generic parameters (Theorem 3): that is Corollary 4, which the formal proof uses. "This implies C_v is not a
k-cycle for k ≥ 4" uses Lemma 12 without citing it. The last step, "Thus by Proposition 7, C_v has size 3 and at least
two of a, b, c, d descend from v", miscites Proposition 7, which says where the concordance factors of a `3₂`-cycle
lie: the size three follows from the three blocks of `C_v` that hold taxa of `s`, and the two taxa below `v` from the
definition of a `3₂`-cycle ([`Banos2019.proposition12`](../../Banos2019/Identifiability.lean#L271)).

### E18. Proposition 13 is false as printed

"Let C_v be a 4-cycle in N⁻. Let a,b,c,d ∈ X be in different v-blocks in N⁻. Suppose under the NMSC model, for generic
parameters, for distinct i,j,k ∈ {a,b,c,d}, there exists a taxon e ∈ X such that {i,j,k,e} satisfies the Cycle property
but not the BC property. Then the v-block containing e is the v-hybrid block." The proof asserts "The 4-cycle in
Q⁻_abcd and the 3-cycle in Q⁻_abce have to have the same hybrid edges, otherwise the level-1 condition would be
violated" (TeX l. 1231). The `3₂`-cycle of `Q⁻_abce` can come from another cycle of `N⁻`.

Counterexample ([`Banos2019.proposition13_asPrinted_false`](../../Banos2019/Identifiability.lean#L474)): the network with the edges `r → a`, `r → t`, `t → p`,
`t → u`, `p → e`, `p → u`, `u → w`, `w → x`, `w → y`, `x → b`, `x → v`, `y → c`, `y → v`, `v → d`.

- It is binary and level-1, with a 3-cycle `t, p, u` (hybrid node `u`) and a 4-cycle `C_v = {wx, xv, wy, yv}`
  (hybrid node `v`); `LSA(X)` is the root.
- In `N⁻`, the blocks of `C_v` are `{a, e}`, `{b}`, `{c}` and `{d}`, the hybrid block is `{d}`, and `a, b, c, d` are in
  distinct blocks.
- In `Q⁻_abce` the cycle `C_v` disappears, as no simple trek between taxa of `{a, b, c, e}` passes through `v`, and the
  3-cycle `t, p, u` is a `3₂`-cycle with hybrid block `{b, c}`: Figure 18, relabelled.
- So on an open set of parameters around those of Example 6, `{a, b, c, e}` satisfies the Cycle property but not the
  Big Cycle property ([`Banos2019.cex_not_forGenericParams`](../../Banos2019/Identify/Counterexample.lean#L1203)), while `e` is not in the `v`-hybrid block `{d}`.

This reads "for generic parameters" as qualifying the implication. Read as part of the hypothesis ("{i,j,k,e} satisfies
the Cycle property but not the BC property" for generic parameters), the printed statement holds vacuously, as that
hypothesis never holds: with a 4-cycle in `Q⁻_ijke` the Big Cycle property holds for generic parameters (Theorem 3);
with neither a 4-cycle nor a `3₂`-cycle the Cycle property fails (Proposition 8); with a `3₂`-cycle it fails whenever
the edge below the hybrid node is longer than `log(3/2)`, an open set of parameters.

The corrected statement, [`Banos2019.proposition13`](../../Banos2019/Identifiability.lean#L359), makes the false step a hypothesis: no cycle of `N⁻` other than `C_v`
has two of `i, j, k, e` below its hybrid node and three of them, one of those two, in distinct blocks
([`Banos2019.OnlyThreeTwoSource`](../../Banos2019/Identifiability.lean#L323)). A `3₂`-cycle of `Q⁻_ijke` always comes from such a cycle
([`Banos2019.exists_cycle_of_hasThreeTwoCycle`](../../Banos2019/Identify/QuartetCycles.lean#L1758)), so the hypothesis is exactly the paper's step. With it, the proof is the
paper's (Section 7). The maintainer agreed to this correction.

### E19. Lemma 17: case 5 (ii)

"For case 5 (ii), we assume without loss of generality that w is in Px." The paths `Px` and `Py` play different roles,
one passing through `e` and the other avoiding its child, so the case of `w` on `Py` only is not symmetric to it. The
construction of case 5 (i) handles it ([`Banos2019.trek_mainStep`](../../Banos2019/Network/TrekArc.lean#L132); Section 7), and the lemma holds.

### E20. Typos

- Proposition 2, proof: a stray "sssss" after "form a 2-cycle." in the PMC author manuscript.
- Lemma 9, published proof: "CF(Q₂⊗ | K = 2)" for `CF(Q₂⊕ | K = 2)`, and "CF(Q₀⊕ | K = 2 or K_y = 2)" for
  `CF(Q₀⊕ | K = 2, K_y = 2)`, which the next sentence and arXiv v1 have. In arXiv v1 the last display of the proof
  lacks a "+" before `2γ(1−γ)`.
- Proposition 6, proof: "Q₀′, Q₁′, Q₂ and Q′" for `Q₂′`.
- Proposition 7, published proof: "given by the equations (7)" for equations (9), and "To minimize CF_AD|BC it is
  enough to let t3 → ∞" for `t₁ → ∞`; arXiv v1 has (9) and `t₁`. With `t₃ → ∞` alone the concordance factors do not
  tend to `(1, 0, 0)`.
- Proposition 10, published proof: "by equations (6)", twice, for equations (8), those of Figure 17. arXiv v1 has (8),
  but names the blocks adjacent to the hybrid block `{c}` as those of `a` and `b`, where Figure 17 and the published
  proof have `b` and `d`.
- Lemma 14: "|X| < 3" for `|X| < 4` (E13).
- Lemma 17, proof, in both versions: "the subpath of Py from f to y" for the node `u`; "let C2 be the set of nodes below
  b⁻, common to P* and Py" for `Px`; in case 5 (ii), "the edges in Px that are above a but below b", where no node is
  above `a` and below `b`, for the edges of `Px` below `b` and above `w`.
- Reference [22], Semple and Steel's *Phylogenetics*, is dated 2005; the book appeared in 2003.

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| Definition 4, Lemma 1 | `Z ≠ ∅` | `LSA(∅)` is undefined (E1) | [`Banos2019.lemma1`](../../Banos2019/Network/Rooted.lean#L312) assumes `Z.Nonempty` |
| Proposition 1 | `\|Z\| ≥ 2` | With one taxon, `LSA(Z)` is a leaf, which Definition 5 cannot suppress, and `(N⁺_Z)⁻` is undefined | [`Banos2019.proposition1`](../../Banos2019/Network/Induced.lean#L665) takes at least two taxa |

### Corrections of statements

- Theorem 4: `Ñ` with the nodes of degree two left by the contraction suppressed (E14).
- Proposition 7: the second claim for the points of `I` other than the vertices of the simplex (E9).
- Proposition 13: the hypothesis [`Banos2019.OnlyThreeTwoSource`](../../Banos2019/Identifiability.lean#L323) in place of the false step of the proof (E18); the
  printed statement is refuted.

## 5. Redundant hypotheses

| Result | Hypothesis that is not needed | Lean |
| --- | --- | --- |
| Theorem 2 | The level-1 condition: the library's theorem, [`Phylogenetics.NMSC.nmscCF_inducedNetwork`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/NMSC/Induced.lean#L76), holds for every phylogenetic network with valid parameters | [`Banos2019.theorem2`](../../Banos2019/Quartet/Reduction.lean#L243) keeps the paper's hypotheses |
| Proposition 11 | The Big Cycle property: with a 4-cycle, the quartet tree that pairs the taxa of non-adjacent blocks always has the strictly smallest concordance factor (equation (8)) | [`Banos2019.proposition11`](../../Banos2019/CycleProperty.lean#L959) keeps the hypothesis |

## 6. How the formalization reads the paper

- **Networks.** A rooted network is a finite directed multigraph with named edges, so that two edges may join the same
  two nodes and 2-cycles exist, as Definition 1 allows. Definition 1's connectedness and the bijectivity of its
  labelling follow from its other clauses ([`Banos2019Challenge.root_reaches`](../../palomar/Banos2019/Challenge.lean#L607), [`Banos2019.isBinaryRootedNetwork_iff`](../../Banos2019/Network/Rooted.lean#L45)).
  The library works on the rooted and semidirected networks of lean4-phylogenetics; the Challenge restates them in
  Mathlib's vocabulary ([`Banos2019/Defs.lean`](../../Banos2019/Defs.lean)), and [`Banos2019/Bridge/`](../../Banos2019/Bridge) proves that the two agree.
- **Metric.** Every edge has a positive length, a tree edge has inheritance probability one, and the two hybrid edges
  into a hybrid node have probabilities in `(0, 1)` that sum to one (Definition 2).
- **The model.** The network multispecies coalescent with one lineage per taxon and independent inheritance (correlation
  `0` in the library's `nmscCF N θ 0`): Kingman's coalescent on forests of lineages along each edge, as a matrix
  exponential, for an infinite time above the root. A concordance factor is the probability that the unrooted gene tree
  displays a quartet tree (Definition 14). An ordering (Definition 15) is the family of comparisons `≤` between the
  concordance factors of quartet trees on the same four taxa, ties included.
- **"For generic parameters".** The metrics that violate the property form a Lebesgue-null set, in the coordinates given
  by the edge lengths and, at each hybrid node, the inheritance probability of one of its two hybrid edges (any
  choice). The paper's space `(0,∞)^m × [0,1]^h` (Proposition 10) has the same null sets.
  [`Banos2019Challenge.not_forGenericParams_false`](../../palomar/Banos2019/Challenge.lean#L614) checks that the metrics do not form a null set.
- **"Can be determined from S", "identifies".** Lemmas 14–16 give a function of `S`, or of the orderings, alone, the same
  for every network, that returns the blocks, the size, the hybrid block or the adjacencies at generic parameters.
  Theorem 4: there is a property `G` of the parameters of each network, holding for generic parameters, such that two
  binary level-1 networks on the same taxa with parameters satisfying `G` and the same orderings have isomorphic
  networks `Ñ`. Both networks must satisfy `G`: the `3₂`-cycle of Figure 18 near the parameters of Example 6 and the
  4-cycle of Figure 17 at those of Example 7, relabelled, have the same orderings and non-isomorphic networks `Ñ`. The
  Challenge's Theorem 4 holds for any set of taxa, the library's for at least two.
- **Unrooted and induced networks.** Suppression follows Figure 3: a chain of edges through nodes of degree two becomes
  one edge, hybrid and directed when its hybrid edges point to one end, with the sum of the lengths and the product of
  the inheritance probabilities. `N⁻` (Definition 5) is the part below `LSA(X)`, with its tree edges undirected and
  `LSA(X)` suppressed. The library's `Q⁻_s` is `(N⊕_s)⁻`; the Challenge's Theorem 3 uses `(N⁻)_s` of Definition 10;
  Proposition 1 joins them ([`Banos2019/Bridge/Quartet.lean`](../../Banos2019/Bridge/Quartet.lean)).
- **Statements on quartet networks.** Theorem 2: the concordance factors of `N` on `s` are those of `Q⊕_s` with its
  induced metric. Proposition 5: "induce the same unrooted network" is an isomorphism of the metric unrooted networks.
  Corollary 3: two networks whose metric unrooted networks induced on `s` are isomorphic have the same concordance
  factors on `s`. Propositions 6–11 are stated for LSA quartet networks, Proposition 7 on four taxa.
- **Lemma 7.** `K′`, whether "there has been a coalescent event before a, b, and c trace back to y", is read at the top
  of the edge above `y`; the argument is the same.
- **Examples 6 and 7.** The networks of Figures 18 and 17 are rooted on one of their hybrid edges. Example 7 gives no
  lengths to the hybrid edges, which do not change the concordance factors, since at most one lineage crosses them;
  the Challenge gives them length one.

The corrections of statements are listed at the end of Section 4.

## 7. Departures from the paper's proofs

Each row is a step where the formal proof does not follow the paper's argument, with its reason: the paper's step is
wrong or has a gap that cannot be repaired along its own lines (gap), or the step has no meaning in the formalization's
representation (representation). The docstrings say the same, and [`docs/Banos2019/route_differences.tsv`](route_differences.tsv) records the
changes of route. Steps that the paper asserts without argument and that the formalization fills along its lines are in
Section 3, not here.

| Result | The paper's argument | The formalization's | Why | E-item |
| --- | --- | --- | --- | --- |
| Lemmas 7 and 9, the root on the cycle; Proposition 5, the base case | Cites Propositions 3 and 4 for the equality of the concordance factors of species trees with the same unrooted metric tree | The same argument, with the root-placement invariance of Allman, Degnan, Rhodes 2011 ([`External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L110)) in place of the cited statements | Gap: the cited statements do not give the step | E6 |
| Lemma 8, `K = 3` | Conditions on `𝔇`, whether the lineage of `d` is in the first coalescent event, and uses exchangeability for `𝔇 = 0` and `𝔇 = 1` | Exchangeability of the three lineages at `v`, once ([`Phylogenetics.NMSC.cherryMass_eq_third`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/NMSC/Symmetry.lean#L262)) | Representation: the model gives the distribution of gene tree topologies, not the order of coalescent events, and `𝔇` is not defined in it | – |
| Lemma 13 | Cites Lemma 12, a generic statement, at given parameters | The direction of Lemma 12's proof that holds for all parameters: Proposition 9 and the correspondence of cycles | Gap | E12 |
| Lemma 14 | Cases `\|X\| < 3`, `\|X\| = 4` by Proposition 9, and `\|X\| ≥ 5` | The argument for `\|X\| ≥ 5`, for every `X` | Gap: `\|X\| = 3` is not covered, and Proposition 9 gives one inclusion | E13 |
| Proposition 12 | Proposition 8 gives a `3₂`-cycle; Proposition 7 gives the size and the taxa below `v` | Corollary 4 gives the `3₂`-cycle; Lemma 12 excludes a size of four or more; the type `3₂` gives the rest | Gap: Proposition 8 also allows a 4-cycle, and Proposition 7 does not give the step | E17 |
| Proposition 13 | Fixes the order of the cycle (Theorem 4) and, in its labels, that `{a, b, c, d}` and `{e, b, c, d}` determine the same hybrid node (Lemma 13), then claims that the two quartet networks have the same hybrid edges | That claim is the hypothesis [`Banos2019.OnlyThreeTwoSource`](../../Banos2019/Identifiability.lean#L323); the two taxa of the hybrid block are read from the `3₂`-cycle, without the preparations | The step is false, and the statement is corrected | E18 |
| Lemma 17, case 5 (ii) | Takes `w` on `Px` without loss of generality | The case of `w` on `Py` only, by the construction of case 5 (i) | Gap: the two cases are not symmetric | E19 |

Not counted as departures:

- Theorem 2 is the library's [`Phylogenetics.NMSC.nmscCF_inducedNetwork`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/NMSC/Induced.lean#L76). Like the paper's proof, it conditions on the
  lineages at the LSA of `s` and uses their exchangeability, applied to the four lineages at once rather than after
  conditioning on the rooted shape of the gene tree. Observation 1 enters it on forests of lineages
  ([`Phylogenetics.NMSC.cherryMass_of_mem`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/NMSC/Symmetry.lean#L200)).
- In Proposition 10, the zero-set lemma for analytic functions, applied to `f ∘ η`, stands for the paper's two steps
  (`f⁻¹(V)` lies in a proper subvariety; `η` is biholomorphic). The maps `ν`, `η` and `f` are the paper's
  ([`Banos2019.cf_eq_fig17`](../../Banos2019/CycleProperty.lean#L695), [`Banos2019.volume_fig17_eq_null`](../../Banos2019/CycleProperty.lean#L772)).
- Proposition 2's induction runs on the top node of the chain of 2-cycles rather than on the network below it: the same
  induction, without building a new network.

## 8. What each result depends on

<!-- Generated from scripts/Audit.lean -->

Every result below depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). The last column lists the results
from prior work that its proof uses:

- equation (1): [`External.AllmanDegnanRhodes2011.equation1`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L60);
- root placement: [`External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L110);
- Semple–Steel: [`External.SempleSteel2003.exists_iso_of_quartets_eq`](../../Banos2019/External/SempleSteel2003/Quartets.lean#L184).

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Definition 1 | [`Banos2019.isBinaryRootedNetwork_iff`](../../Banos2019/Network/Rooted.lean#L45) | – |
| Definition 2 | [`Banos2019.isMetricNetwork_iff`](../../Banos2019/Network/Rooted.lean#L229) | – |
| Definition 4 | [`Banos2019.isLeastStableAncestor_iff_def4`](../../Banos2019/Network/Rooted.lean#L290) | – |
| Lemma 1 | [`Banos2019.lemma1`](../../Banos2019/Network/Rooted.lean#L312) | – |
| Lemma 2 | [`Banos2019.lemma2`](../../Banos2019/Network/Rooted.lean#L441) | – |
| Proposition 1 | [`Banos2019.proposition1`](../../Banos2019/Network/Induced.lean#L665), [`Banos2019.proposition1_metric`](../../Banos2019/Network/Induced.lean#L678) | – |
| Lemma 3 | [`Banos2019.lemma3`](../../Banos2019/Network/Cycle.lean#L440), [`Banos2019.lemma3_unrooted`](../../Banos2019/Network/Induced.lean#L289) | – |
| Proposition 2 | [`Banos2019.proposition2`](../../Banos2019/Structure.lean#L46) | – |
| Lemma 4 | [`Banos2019.lemma4`](../../Banos2019/Structure.lean#L431) | – |
| Corollary 1 | [`Banos2019.corollary1`](../../Banos2019/Structure.lean#L491) | – |
| Lemma 5 | [`Banos2019.lemma5`](../../Banos2019/Quartet/Reduction.lean#L131) | – |
| Lemma 6 | [`Banos2019.lemma6`](../../Banos2019/Quartet/Reduction.lean#L182) | – |
| Observation 1 | [`Banos2019.observation1`](../../Banos2019/Quartet/Reduction.lean#L200) | – |
| Theorem 2 | [`Banos2019.theorem2`](../../Banos2019/Quartet/Reduction.lean#L243) | – |
| Lemma 7 | [`Banos2019.lemma7`](../../Banos2019/Quartet/Reduction.lean#L1056) | root placement |
| Lemma 8 | [`Banos2019.lemma8`](../../Banos2019/Quartet/Reduction.lean#L1126) | – |
| Corollary 2 | [`Banos2019.corollary2`](../../Banos2019/Quartet/Reduction.lean#L1296) | root placement |
| Lemma 9 | [`Banos2019.lemma9`](../../Banos2019/Quartet/Reduction.lean#L2213) | root placement |
| Lemma 10 | [`Banos2019.lemma10`](../../Banos2019/Quartet/Reduction.lean#L2245) | – |
| Lemma 11 | [`Banos2019.lemma11`](../../Banos2019/Quartet/Reduction.lean#L2334) | – |
| Proposition 5 | [`Banos2019.proposition5`](../../Banos2019/Quartet/Reduction.lean#L3317) | root placement |
| Corollary 3 | [`Banos2019.corollary3`](../../Banos2019/Quartet/Reduction.lean#L3351) | root placement |
| Examples 2–5 | [`Banos2019.example2`](../../Banos2019/Quartet/Examples.lean#L553), [`Banos2019.example3`](../../Banos2019/Quartet/Examples.lean#L622), [`Banos2019.example4`](../../Banos2019/Quartet/Examples.lean#L673), [`Banos2019.example5`](../../Banos2019/Quartet/Examples.lean#L723) | equation (1), root placement |
| Proposition 6 | [`Banos2019.proposition6`](../../Banos2019/CycleProperty.lean#L154) | equation (1), root placement |
| Example 6 | [`Banos2019.example6`](../../Banos2019/Quartet/Examples.lean#L853) | equation (1), root placement |
| Proposition 7 | [`Banos2019.proposition7`](../../Banos2019/CycleProperty.lean#L539) | equation (1), root placement |
| Proposition 8 | [`Banos2019.proposition8`](../../Banos2019/CycleProperty.lean#L633) | equation (1), root placement |
| Example 7 | [`Banos2019.example7`](../../Banos2019/Quartet/Examples.lean#L871) | equation (1), root placement |
| Proposition 9 | [`Banos2019.proposition9`](../../Banos2019/CycleProperty.lean#L655) | equation (1), root placement |
| Proposition 10 | [`Banos2019.proposition10`](../../Banos2019/CycleProperty.lean#L805) | equation (1), root placement |
| Theorem 3 | [`Banos2019.theorem3`](../../Banos2019/CycleProperty.lean#L878) | equation (1), root placement |
| Corollary 4 | [`Banos2019.corollary4`](../../Banos2019/CycleProperty.lean#L894) | equation (1), root placement |
| Proposition 11 | [`Banos2019.proposition11`](../../Banos2019/CycleProperty.lean#L959) | equation (1), root placement |
| Lemma 12 | [`Banos2019.lemma12`](../../Banos2019/CycleProperty.lean#L1071) | equation (1), root placement |
| Lemma 13 | [`Banos2019.lemma13`](../../Banos2019/CycleProperty.lean#L1113) | equation (1), root placement |
| Lemma 14 | [`Banos2019.lemma14`](../../Banos2019/Identifiability.lean#L66) | equation (1), root placement |
| Lemma 15 | [`Banos2019.lemma15`](../../Banos2019/Identifiability.lean#L91) | equation (1), root placement |
| Lemma 16 | [`Banos2019.lemma16`](../../Banos2019/Identifiability.lean#L125) | equation (1), root placement |
| Theorem 4 | [`Banos2019.theorem4`](../../Banos2019/Identifiability.lean#L223) | equation (1), root placement, Semple–Steel |
| Proposition 12 | [`Banos2019.proposition12`](../../Banos2019/Identifiability.lean#L271) | equation (1), root placement |
| Proposition 13, corrected | [`Banos2019.proposition13`](../../Banos2019/Identifiability.lean#L359) | equation (1), root placement |
| Proposition 13 as printed is false | [`Banos2019.proposition13_asPrinted_false`](../../Banos2019/Identifiability.lean#L474) | equation (1), root placement |
| Lemma 17 | [`Banos2019.lemma17`](../../Banos2019/Network/Induced.lean#L544) | – |

The cited results, [`External.AllmanDegnanRhodes2011.proposition3`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L87) and [`External.AllmanDegnanRhodes2011.proposition4`](../../Banos2019/External/AllmanDegnanRhodes2011/Basic.lean#L98)
among them, use none; the theorems of the Challenge, as the Solution proves them, depend on the same three axioms.

The route check (`python3 scripts/route_check.py check docs/Banos2019/paper_routes.tsv --accept
docs/Banos2019/route_differences.tsv`) confirms that every proof uses the results that the paper's proof cites, except
the differences recorded in [`docs/Banos2019/route_differences.tsv`](route_differences.tsv), each with its reason: the departures of Section 7,
and uses that the paper leaves implicit (Lemma 3 throughout; Lemma 1 (iii) where a cycle of `N⁻` is read below
`LSA(s)`; Lemmas 5 and 6 in Propositions 6 and 7 and in the base case of Theorem 4; Theorem 2 where the concordance
factors of `N` on `s` are read on `Q⁻_s`; Proposition 1 and Lemma 17 in Theorem 4). The TeX label of Lemma 6 contains a
space, so the check does not map it to the Lean result, and the route of Lemma 6 is not checked.
[`docs/Banos2019/paper_routes.tsv`](paper_routes.tsv) holds the routes of the paper's proofs, extracted from the TeX of arXiv v1 and
completed by hand.

## 9. Not formalized

- **Illustrations and remarks with no statement to prove:**
  - Example 1, the computation of a gene tree probability on Figure 7;
  - the remark after Theorem 2 that its argument extends to five taxa but not to six;
  - Figure 11, the list of the possible quartet networks that Lemmas 5 and 6 determine;
  - the remark after Lemma 13 that the 4-cycle networks of Figure 21, with different hybrid nodes, have the same
    concordance factors, and Figure 22;
  - the remark after Proposition 12 that, for a set with the Cycle property but not the Big Cycle property, the
    smallest concordance factor names a pair of taxa in the hybrid block, stated without proof;
  - the discussion of Figure 23, and Section 10 (Discussion).
- **The procedure (i)–(v) after Corollary 3** for computing concordance factors is not stated as a theorem. Its steps are
  Corollary 2, Lemmas 5, 6, 9, 10 and 11 and equation (1), and Examples 2–5 apply it.
- **The citations that give context only** (Section 2).

## 10. The paper in the literature

The search was made on 2026-11-24: the citing works on Semantic Scholar (52) and OpenAlex (59), Crossref and PubMed for
corrections, the arXiv listing, and web searches on the paper's results; the citation contexts were screened for
corrections and criticisms. The works below are the closest ones, and every correction or criticism found. Each claim
about them was checked again against their texts on 2026-11-25.

### Before the paper

- **SNaQ.** Solís-Lemus and Ané, [PLoS Genet. 12 (2016), e1005896](https://doi.org/10.1371/journal.pgen.1005896), infer
  level-1 networks from quartet concordance factors by pseudolikelihood, and show that a single hybridization can be
  detected. Baños sets out to prove what the concordance factors identify of the whole topology. Proposition 7 and
  Example 6 answer a claim of SNaQ's supplementary materials, that a quartet network with a `3₂`-cycle always reduces
  to a quartet tree; Solís-Lemus, Ané and Yang, [Syst. Biol. 65 (2016), 843–851](https://doi.org/10.1093/sysbio/syw030),
  had observed that such networks need not be treelike.
- **The model.** Meng and Kubatko, [Theor. Popul. Biol. 75 (2009), 35–45](https://doi.org/10.1016/j.tpb.2008.10.004), and
  Yu, Degnan and Nakhleh, [PLoS Genet. 8 (2012), e1002660](https://doi.org/10.1371/journal.pgen.1002660), give the network
  multispecies coalescent.
- **Four-taxon species trees.** Allman, Degnan and Rhodes,
  [J. Math. Biol. 62 (2011), 833–862](https://doi.org/10.1007/s00285-010-0355-7): Section 2.
- **Combinatorial reconstruction** of level-1 networks from small networks: Keijsper and Pendavingh,
  [Bull. Math. Biol. 76 (2014)](https://doi.org/10.1007/s11538-014-0022-z); Huber, van Iersel, Moulton, Scornavacca and Wu,
  [Algorithmica 77 (2017)](https://doi.org/10.1007/s00453-015-0069-8); Huber, Moulton, Semple and Wu,
  [Bull. Math. Biol. 80 (2018)](https://doi.org/10.1007/s11538-018-0450-2). The paper calls them "primarily combinatorial
  in nature": they do not use the coalescent or semidirected networks.

### Concurrent work

Gross and Long, *Distinguishing phylogenetic networks*,
[SIAM J. Appl. Algebra Geom. 2 (2018), 72–93](https://doi.org/10.1137/17M1134238) (arXiv:1706.03060, 9 June 2017, about five
months before arXiv:1711.10545 of 28 November 2017), prove that the semidirected topology of networks with a single
reticulation on a cycle of size at least four is generically identifiable from sequence data under the Jukes–Cantor
model. It is the same kind of question for other data; neither paper cites the other. No other concurrent work was found.

### Since the paper

- **The main result, reproved and restated.**
  - Allman, Baños and Rhodes, *NANUQ*, [Algorithms Mol. Biol. 14 (2019), 24](https://doi.org/10.1186/s13015-019-0159-2): its
    Corollary 35 "recovers the main result of [3]", this paper: for generic parameters, `N⁻` with its 2- and 3-cycles
    suppressed and its 4-cycles undirected is identifiable.
  - Allman, Baños, Garrote-López and Rhodes, [Bull. Math. Biol. 86 (2024), 110](https://doi.org/10.1007/s11538-024-01339-4):
    their Theorem 2, "(Baños 2019, Theorem 4)", restates it with "suppressing degree-2 nodes", and for `|X| ≥ 4` (E14).
- **What it left open.**
  - Allman et al. 2024, Proposition 18: for `n ≥ 5` taxa and generic parameters, the directions of the hybrid edges of
    4-cycles are identifiable from the concordance factors; their Theorem 19 says what can be identified of 3-cycles.
    Their Appendix A.1: "because it considered only one CF at a time … it did not obtain the strongest possible result
    … results in (Baños 2019) simply left all 4-cycles undirected".
  - Tiley, Liu and Solís-Lemus, *Extracting diamonds*,
    [Evol. J. Linn. Soc. 4 (2025), kzaf019](https://doi.org/10.1093/evolinnean/kzaf019): in a network with one
    hybridization forming a 4-cycle, the place of the hybrid node is generically identifiable from quartet concordance
    factors when `n > 5`.
- **Uses of its results.**
  - Gross, van Iersel, Janssen, Jones, Long and Murakami,
    [J. Math. Biol. 83 (2021), 32](https://doi.org/10.1007/s00285-021-01653-8): their Lemma 5 is "Lemmas 12 and 13 of
    Baños (2019)".
  - Allman, Baños and Rhodes, [J. Math. Biol. 84 (2022), 35](https://doi.org/10.1007/s00285-022-01734-2), on the logDet
    distance: their Lemma 1 is "extracted from the proof of Theorem 4 of [Bn19]".
  - Allman, Baños, Mitchell and Rhodes, [J. Math. Biol. 86 (2023), 10](https://doi.org/10.1007/s00285-022-01838-9), on the
    tree of blobs: "The most complete result in the level-1 topological case comes from Baños' study".
  - Xu and Ané, [J. Math. Biol. 86 (2023), 12](https://doi.org/10.1007/s00285-022-01847-8): identifiability from average
    distances.
  - Ané, Fogg, Allman, Baños and Rhodes, [J. Math. Biol. 88 (2024), 29](https://doi.org/10.1007/s00285-024-02050-7), on
    anomalous networks, use Propositions 1 and 6 and Lemma 10.
  - Frohn, Holtgrefe, van Iersel, Jones and Kelk,
    [J. Comput. Syst. Sci. 152 (2025), 103655](https://doi.org/10.1016/j.jcss.2025.103655): "Baños [6] showed that the
    displayed quartets of a semi-directed level-1 network do not provide enough information to reconstruct every
    possible semi-directed level-1 network."
- **A criticism.** Solís-Lemus, Coen and Ané, [arXiv:2010.01758](https://arxiv.org/abs/2010.01758) (2020, a preprint; no
  journal version was found), write that "[4] falsely claims that [19] '[...] arguments do not include investigations on
  network properties such as cycle sizes'", where [4] is this paper and [19] SNaQ. It disputes a sentence of the
  introduction, not a result.
- **Corrections.** No erratum was found: Crossref records no update to the article, Europe PMC no comment or
  correction, and arXiv has only v1. No later work reports an error in the paper's results. Allman et al. 2024 state
  Theorem 4 with the suppression that E14 adds, without comment. Nothing was found on Propositions 7 and 13, Example 7,
  Lemma 5 or Lemma 14.

### Formalizations

No formalization of the paper, or of its main results, was found outside this collection. In the collection,
[lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) holds the network multispecies coalescent, Theorem 2
in the general form of Section 5 ([`Phylogenetics.NMSC.nmscCF_inducedNetwork`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/NMSC/Induced.lean#L76)), and the concordance factors of four taxa
in distinct components of one cycle of a level-1 network; this formalization builds on them.
[lean4-allman2011](https://github.com/vltanh/lean4-allman2011) formalizes the source of Section 2. NANUQ, which builds on
this paper, is formalized in [lean4-nanuq](https://github.com/vltanh/lean4-nanuq), whose proofs do not use this
repository.

## 11. What's next

Below: what the formalization holds for
reuse.

### The formalization

- **What could move up the tree.** The semidirected networks, suppression, treks, induced networks, the contraction of
  cycles and Proposition 1 are general, and belong in lean4-phylogenetics or lean4-phylo-network once a second paper
  needs them. The reduction lemmas of Section 5 (Lemmas 7–11, Proposition 5) compute concordance factors of level-1
  quartet networks, as NANUQ and the later works do.
- **[`Banos2019/Basic/`](../../Banos2019/Basic)** holds a few general lemmas, in Mathlib's namespaces, each a candidate for Mathlib: paths of a
  relation that avoid a point, sums of cardinalities of disjoint sets, greatest elements of finite totally ordered
  sets, and null preimages under sums of coordinates ([`Banos2019/Basic/README.md`](../../Banos2019/Basic/README.md)).
- **[`Banos2019/External/`](../../Banos2019/External)** holds the four-taxon results of Allman, Degnan and Rhodes 2011 in the form the paper uses
  them, and Semple and Steel's quartet theorem for phylogenetic `X`-trees, which any formalization that cites them can
  reuse ([`Banos2019/External/README.md`](../../Banos2019/External/README.md)).
