# Baños 2019: identifying species network features from gene tree quartets, in Lean

A Lean 4 formalization of H. Baños, *Identifying species network features from gene tree quartets under the
coalescent model*, [Bull. Math. Biol. 81 (2019), 494–534](https://doi.org/10.1007/s11538-018-0485-4). Under the network
multispecies coalescent, gene trees form inside a species network with hybridization. The paper asks what the
concordance factors of quartets (the probabilities of the three unrooted gene trees on four taxa) identify of a
level-1 network. Its main result, Theorem 4, says that for generic numerical parameters the orderings of these
concordance factors identify the unrooted semidirected network `Ñ` obtained from `N⁻` by contracting its 2- and
3-cycles and forgetting the directions of the hybrid edges of its 4-cycles: all cycles of size at least four, and
the hybrid nodes of the cycles of size at least five. On the way, it computes the concordance factors of quartet
networks from those of trees (Section 5), and characterizes the 4-cycles of quartet networks by the Big Cycle property
(Theorem 3).

Every numbered result of the paper is proved, with no `sorry` and on the standard axioms only, and no result of the
literature is assumed. Three statements are proved in corrected forms: Theorem 4, with the nodes of degree two that
the contraction leaves in `Ñ` suppressed; Proposition 7, off the vertices of the simplex; and Proposition 13, which is false as printed and
whose refutation is proved too. No person has reviewed the proofs.

It is a paper of the hub [lean4-phylo-network](https://github.com/vltanh/lean4-phylo-network), in the collection of
formalizations rooted at [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics).

## Status

| Part of the paper | Status |
| --- | --- |
| §2: networks, LSA, unrooted and induced networks, Lemmas 1, 2, Proposition 1 | proved; Lemma 1 for nonempty sets of taxa, Proposition 1 for at least two taxa |
| §3: cycles, level-1 networks, Lemmas 3, 4, Proposition 2, Corollary 1, the tree of cycles | proved |
| §4: the network multispecies coalescent, concordance factors, equation (1) | defined; equation (1) proved from Allman, Degnan, Rhodes 2011 |
| §5: Observation 1, Theorem 2, Lemmas 5–11, Corollaries 2, 3, Proposition 5, Examples 2–5 | proved |
| §6: Proposition 6, Example 6, Propositions 7, 8 | proved; Proposition 7 off the vertices of the simplex (E9) |
| §7: Example 7, Propositions 9–11, Theorem 3, Corollary 4, Lemmas 12, 13 | proved; Example 7's values are the paper's up to the names of two taxa (E10) |
| §8: Lemmas 14–16, Theorem 4 | proved; Theorem 4 with the nodes of degree two that the contraction leaves in `Ñ` suppressed (E14) |
| §9: Propositions 12, 13 | Proposition 12 proved; Proposition 13 false as printed, refuted, and proved in a corrected form (E18) |
| Appendix: Lemma 17, the proof of Proposition 1 | proved |
| Cited results: Allman, Degnan, Rhodes 2011 (equation (1), Propositions 3, 4, the root placement); Semple, Steel 2003 | proved, in [`Banos2019/External/`](Banos2019/External), from lean4-allman2011 and lean4-phylogenetics |
| Example 1, remarks without a statement to prove | not formalized |

[Section 9 of the report](docs/Banos2019/REPORT.md#9-not-formalized) lists what is not formalized.

## Main results

The statements of record are the theorems of the Challenge, [`palomar/Banos2019/Challenge.lean`](palomar/Banos2019/Challenge.lean), in the namespace
`Banos2019Challenge`. The Challenge imports only Mathlib; its definitions are those of [`Banos2019/Defs.lean`](Banos2019/Defs.lean), copied by
[`scripts/sync_challenge_defs.py`](scripts/sync_challenge_defs.py). [`palomar/Banos2019/Solution.lean`](palomar/Banos2019/Solution.lean) proves each of them, under the same name, from the
library, through the bridges of [`Banos2019/Bridge/`](Banos2019/Bridge). They keep the paper's hypotheses.

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 3 | [`Banos2019Challenge.theorem3`](palomar/Banos2019/Challenge.lean#L548) | for generic parameters, four taxa have the Big Cycle property (three different concordance factors) exactly when their induced unrooted network has a 4-cycle |
| Theorem 4 | [`Banos2019Challenge.theorem4`](palomar/Banos2019/Challenge.lean#L562) | for generic parameters, two binary level-1 networks on the same taxa with the same orderings of quartet concordance factors have isomorphic networks `Ñ` |
| Proposition 5 | [`Banos2019Challenge.proposition5`](palomar/Banos2019/Challenge.lean#L575) | two LSA quartet networks with isomorphic metric unrooted networks have the same concordance factors |
| Equation (1) | [`Banos2019Challenge.equation1_balanced`](palomar/Banos2019/Challenge.lean#L589) | check: the concordance factors of a balanced rooted quartet tree |
| Definition 4 | [`Banos2019Challenge.lsa_isLSA`](palomar/Banos2019/Challenge.lean#L601) | check: a binary network has a lowest stable ancestor of its taxa |
| Definition 1 | [`Banos2019Challenge.root_reaches`](palomar/Banos2019/Challenge.lean#L607) | check: the root reaches every node |
| "Generic" | [`Banos2019Challenge.not_forGenericParams_false`](palomar/Banos2019/Challenge.lean#L614) | check: the metrics of a binary network are not a null set |
| Examples 6, 7 | [`Banos2019Challenge.example6`](palomar/Banos2019/Challenge.lean#L622), [`Banos2019Challenge.example7`](palomar/Banos2019/Challenge.lean#L640) | check: the concordance factors `(32, 33, 33)/98` of Figures 18 and 17 |
| Figures 17, 18 | [`Banos2019Challenge.fig17_fig18_unrooted`](palomar/Banos2019/Challenge.lean#L652), [`Banos2019Challenge.fig17_fig18_tilde`](palomar/Banos2019/Challenge.lean#L660) | check: `N⁻` of Figure 17 has a 4-cycle and that of Figure 18 none; their networks `Ñ` are not isomorphic |

The rows marked "check" test the Challenge's definitions against known facts. Theorem 4 is stated as identifiability:
a property of the parameters, holding for generic parameters of every binary level-1 network, under which the orderings
determine `Ñ` up to isomorphism.

### Also proved in the library

| Paper | Lean | Statement |
| --- | --- | --- |
| Proposition 1 | [`Banos2019.proposition1`](Banos2019/Network/Induced.lean#L665), [`Banos2019.proposition1_metric`](Banos2019/Network/Induced.lean#L678) | unrooting and inducing on a set of taxa commute |
| Theorem 2 | [`Banos2019.theorem2`](Banos2019/Quartet/Reduction.lean#L243) | the concordance factors of four taxa are those of their induced LSA network |
| Lemmas 7–11 | [`Banos2019.lemma7`](Banos2019/Quartet/Reduction.lean#L1056), …, [`Banos2019.lemma11`](Banos2019/Quartet/Reduction.lean#L2334) | the reduction formulas for the cycles of quartet networks |
| Proposition 7 | [`Banos2019.proposition7`](Banos2019/CycleProperty.lean#L539) | the concordance factors of a `3₂`-cycle lie in `I`, and fill it but for its vertices |
| Proposition 10 | [`Banos2019.proposition10`](Banos2019/CycleProperty.lean#L805) | a 4-cycle gives the Cycle property, and the Big Cycle property for generic parameters |
| Lemmas 12–16 | [`Banos2019.lemma12`](Banos2019/CycleProperty.lean#L1071), …, [`Banos2019.lemma16`](Banos2019/Identifiability.lean#L125) | the set of quartets with the Big Cycle property, and the orderings, give the blocks of the large cycles and their order |
| Proposition 13 | [`Banos2019.proposition13`](Banos2019/Identifiability.lean#L359), [`Banos2019.proposition13_asPrinted_false`](Banos2019/Identifiability.lean#L474) | the corrected statement, and the refutation of the printed one |
| Lemma 17 | [`Banos2019.lemma17`](Banos2019/Network/Induced.lean#L544) | an edge below `LSA(Z)` above a taxon of `Z` lies on a simple trek between taxa of `Z` |

[Section 8 of the report](docs/Banos2019/REPORT.md#8-what-each-result-depends-on) lists every numbered result with its Lean name.

## What the audit found

| Finding | Where |
| --- | --- |
| Proposition 13 is false as printed: the `3₂`-cycle that its proof compares with the 4-cycle can come from another cycle of `N⁻`. Counterexample and corrected form | E18 |
| Theorem 4 is false as printed: `Ñ` keeps a node of degree two for each contracted 2-cycle, whose place is not identifiable; it holds with those nodes suppressed, as Allman et al. 2024 restate it | E14 |
| Proposition 7's second claim fails at the vertices of the simplex | E9 |
| Example 7 prints the concordance factors of Figure 17 with two taxa exchanged | E10 |
| Lemmas 7 and 9 and Proposition 5 cite Propositions 3 and 4, identifiability statements, for the root-placement invariance of the same source | E6 |
| Theorem 4's proof leaves out how the orderings give the quartet trees (they need a generic condition) and that the tree of cycles is a tree with the leaves it claims | E15, E16 |
| Gaps in the proofs of Lemma 1, Proposition 2, Lemma 4 (no printed proof), Propositions 5, 6, Lemmas 12–14, Proposition 12 and Lemma 17; a miscount in Lemma 5. All repaired, and the results hold | E2–E5, E7, E8, E11–E13, E17, E19 |
| Lemma 1 needs a nonempty set of taxa; misprints in the proofs of Lemmas 9, 14, 17 and Propositions 6, 7, 10 | E1, E20 |

[Section 3 of the report](docs/Banos2019/REPORT.md#3-errors-and-gaps-in-the-paper) gives each finding with the paper's
sentence and the repair; 20 findings in all. The proofs follow the paper's arguments, except seven departures, each
forced by an error or a gap in the paper's step or by the representation, listed in
[Section 7 of the report](docs/Banos2019/REPORT.md#7-departures-from-the-papers-proofs) with what the paper does, what
Lean does and why.

## Trust

- `lake build` passes; the only `sorry`s are the Challenge's statements. There is no `sorry`, `axiom`, `native_decide`
  or `implemented_by` in [`Banos2019/`](Banos2019) or in the Solution.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks every declaration of this repository and of the modules of the libraries it imports,
  including private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and writes the routes of
  the proofs.
- [`scripts/route_check.py`](scripts/route_check.py) compares those routes with the paper's, in [`docs/Banos2019/paper_routes.tsv`](docs/Banos2019/paper_routes.tsv);
  [`docs/Banos2019/route_differences.tsv`](docs/Banos2019/route_differences.tsv) records every difference, with its reason.
- [`palomar/Banos2019/comparator.json`](palomar/Banos2019/comparator.json) configures Comparator, which checks that the Solution proves exactly the
  Challenge's statements. [`scripts/check_kernels.sh`](scripts/check_kernels.sh) runs it and checks the eleven theorems under the three kernels
  that Palomar uses: Lean's kernel and NanoDa (through Comparator) and con-ron; all three accept them.
- **No person has reviewed the proofs.** Independent agents reviewed the statements and the Challenge against the
  paper, compared the proofs with the paper's, and checked the findings and the literature.

## Dependencies

Pinned by commit in [`lakefile.toml`](lakefile.toml) and [`lake-manifest.json`](lake-manifest.json):

| Library | Commit | What it provides |
| --- | --- | --- |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | `v4.37.0-rc1` | everything general |
| [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) (`Phylogenetics`) | `3fcabfd` | rooted and semidirected networks, species trees, the network multispecies coalescent and its exchangeability, Theorem 2 in general form, the Splits Equivalence Theorem, analytic null sets |
| [lean4-phylo-network](https://github.com/vltanh/lean4-phylo-network) (`PhyloNetwork`) | `4ed2bb0` | the library of the hub of network estimation |
| [lean4-allman2011](https://github.com/vltanh/lean4-allman2011) (`Allman2011`) | `d4ada2c` | Allman, Degnan, Rhodes 2011, from which [`Banos2019/External/AllmanDegnanRhodes2011/`](Banos2019/External/AllmanDegnanRhodes2011) proves the results the paper cites |

## Palomar

[`palomar/Banos2019/`](palomar/Banos2019) has the files of an entry: the Challenge, which imports only Mathlib, the
Solution, [`palomar/Banos2019/comparator.json`](palomar/Banos2019/comparator.json), which names them and the eleven theorems, and
[`palomar/Banos2019/formalization.yaml`](palomar/Banos2019/formalization.yaml), the entry's metadata. CI checks that the Challenge's copy of the definitions is
the block of [`Banos2019/Defs.lean`](Banos2019/Defs.lean) (`python3 scripts/sync_challenge_defs.py --check`).

## Building

From the root of the repository:

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean                                    # axioms and dependencies
python3 scripts/route_check.py check docs/Banos2019/paper_routes.tsv --accept docs/Banos2019/route_differences.tsv
scripts/check_kernels.sh                                            # Comparator and con-ron (needs bubblewrap)
python3 scripts/linkify_docs.py                                     # the documents' links to the code
```

Toolchain: Lean and Mathlib `v4.37.0-rc1` ([`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json)), the release of the collection.

## Layout

| Folder | Content |
| --- | --- |
| [`Banos2019/Basic/`](Banos2019/Basic) | General mathematics, in Mathlib's namespaces; [its README](Banos2019/Basic/README.md) says where each part could go |
| [`Banos2019/External/`](Banos2019/External) | The cited results, in the namespaces `External.<Source>`; [its README](Banos2019/External/README.md) lists them |
| [`Banos2019/Defs.lean`](Banos2019/Defs.lean), [`Banos2019/Bridge/`](Banos2019/Bridge) | The definitions of the Challenge, and the proof that they are the library's |
| [`Banos2019/Network/`](Banos2019/Network), [`Banos2019/Structure.lean`](Banos2019/Structure.lean) | §2, §3 and the Appendix: networks, LSA, suppression, induced networks, cycles, Proposition 1, Lemma 17 |
| [`Banos2019/Coalescent.lean`](Banos2019/Coalescent.lean) | §4: concordance factors, orderings, the Cycle and Big Cycle properties |
| [`Banos2019/Quartet/`](Banos2019/Quartet) | §5: quartet networks, Theorem 2, Lemmas 5–11, Proposition 5, the examples |
| [`Banos2019/CycleProperty.lean`](Banos2019/CycleProperty.lean) | §6 and §7: Propositions 6–11, Theorem 3, Corollary 4, Lemmas 12, 13 |
| [`Banos2019/Identifiability.lean`](Banos2019/Identifiability.lean), [`Banos2019/Identify/`](Banos2019/Identify) | §8 and §9: Lemmas 14–16, Theorem 4, the tree of cycles, Propositions 12, 13 |
| [`palomar/Banos2019/`](palomar/Banos2019) | The Challenge, the Solution, the Comparator configuration and the metadata |
| [`docs/Banos2019/`](docs/Banos2019) | [The report](docs/Banos2019/REPORT.md), [the credits](docs/Banos2019/CREDITS.md) and the routes of the proofs |
| [`scripts/`](scripts) | The audit, the route check, the copy of the definitions into the Challenge, the links and the tables |

The paper's library is in the namespace [`Banos2019`](Banos2019).

## Related work

From [Section 10 of the report](docs/Banos2019/REPORT.md#10-the-paper-in-the-literature), searched on 2026-11-24.

- No other formalization of the paper was found. lean4-phylogenetics holds Theorem 2 in general form, and lean4-nanuq
  formalizes NANUQ, which builds on this paper.
- Before: SNaQ (Solís-Lemus, Ané 2016) infers level-1 networks from quartet concordance factors; Allman, Degnan, Rhodes
  2011 give the four-taxon results on species trees.
- Concurrent: Gross and Long 2018 prove a similar identifiability for sequence data under Jukes–Cantor.
- Since: NANUQ (2019) recovers Theorem 4; Allman, Baños, Garrote-López, Rhodes 2024 restate it with the suppression of
  E14 and identify the hybrid nodes of 4-cycles for five taxa or more, as Tiley, Liu, Solís-Lemus 2025 do for networks
  with one hybridization. No erratum was found.

## What's next

A private `NEXT.md` holds the candidate follow-up papers. [Section 11 of the report](docs/Banos2019/REPORT.md#11-whats-next)
says what the formalization holds for reuse.

## Credits

- Requested and supervised by The-Anh Vu-Le, who chose the paper and decided the layout and the libraries, and agreed to
  the correction of Proposition 13. **No person has reviewed the proofs.**
- Statements, proofs, audit and documents by Claude (Opus 5.5) in Claude Code, with sub-agents, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure, on 2026-11-24 and 2026-11-25.
  [`docs/Banos2019/CREDITS.md`](docs/Banos2019/CREDITS.md) has the details.

## License

[Apache-2.0](LICENSE).
