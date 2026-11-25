# The results the paper cites

One directory per source, `Banos2019/External/<Source>/`, with modules
`Banos2019.External.<Source>.…`, declarations in the namespace `External.<Source>`, and a [`README.md`](README.md)
giving the source, the statements, how the paper uses them and how they are proved. Each result is
stated in its source's terms, in the form the paper uses, and proved. These modules import Mathlib,
[`Banos2019/Basic/`](../Basic) and the libraries this repository requires, never the paper's library.

A source that another repository of the collection already formalizes (lean4-phylogenetics, a
hub's library, or the repository of a paper) is not formalized again: its statement here is
proved from that repository's theorem (lean4-phylogenetics, `docs/CONVENTIONS.md`, Sections 4
and 6).

| Source | Directory | What the paper takes from it | Proved from |
| --- | --- | --- | --- |
| E. S. Allman, J. H. Degnan, J. A. Rhodes, J. Math. Biol. 62 (2011) | [`Banos2019/External/AllmanDegnanRhodes2011/`](AllmanDegnanRhodes2011) | Equation (1), the paper's Propositions 3 and 4, and the invariance of the concordance factors of a four-taxon species tree under the root placement, which the proofs of Lemmas 7 and 9 and Proposition 5 use | The theorems of [lean4-allman2011](https://github.com/vltanh/lean4-allman2011), which formalizes that paper by its own arguments ([its README](AllmanDegnanRhodes2011/README.md)) |
| C. Semple, M. Steel, *Phylogenetics* (2003) | [`Banos2019/External/SempleSteel2003/`](SempleSteel2003) | Two phylogenetic `X`-trees displaying the same quartet trees are isomorphic (the proof of Theorem 4) | The Splits Equivalence Theorem of lean4-phylogenetics ([its README](SempleSteel2003/README.md)) |

The paper also takes Lemma 3, on the cycles of level-1 networks, from Rosselló and Valiente 2009.
It is one of the paper's numbered results, so it is in the paper's library, proved by an argument
of the formalization's own: [`Banos2019.lemma3`](../Network/Cycle.lean#L440) and [`Banos2019.lemma3_unrooted`](../Network/Induced.lean#L289). The network
multispecies coalescent of Meng and Kubatko 2009 is a definition, the library `Phylogenetics`'s.
