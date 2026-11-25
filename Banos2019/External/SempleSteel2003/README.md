# Semple, Steel 2003

C. Semple, M. Steel, *Phylogenetics*, Oxford Lecture Series in Mathematics and its Applications 24,
Oxford University Press, 2003. Reference [22] of Baños 2019, listed there with the year 2005.

Module `Banos2019.External.SempleSteel2003.Quartets`, namespace `External.SempleSteel2003`. Baños
2019 cites the book in the proof of Theorem 4: without cycles of size at least four, the quartet
trees that `Ñ` displays "determine the topology `Ñ` by a standard result". The statement,
`exists_iso_of_quartets_eq` (`ext:semple-steel`), is in the source's terms: two phylogenetic
`X`-trees (`IsPhylogeneticXTree`, an `X`-tree `Phylogenetics.SplitsEquivalence.IsXTree` labelled
bijectively onto its leaves) displaying the same quartet trees (`quartets`, read on the splits of
the edges) are isomorphic, by an isomorphism fixing the taxa. It is the case of phylogenetic
`X`-trees of the book's Theorem 6.3.5, by which an `X`-tree is determined by its restrictions to the
sets of at most four taxa; the book was not available to compare with, and the number is the one
under which Allman, Holder and Rhodes (arXiv:0905.4542) cite it, with the statement of S. Roch's
lecture notes on the book's Chapter 6 (Wisconsin, 2010, lecture 6). It is proved from
lean4-phylogenetics: the splits of a phylogenetic `X`-tree form an unrooted tree, so its quartet
trees give its splits (`Phylogenetics.subset_of_forall_displays`), and the splits give the tree by
the Splits Equivalence Theorem (the book's Theorem 3.1.4,
`Phylogenetics.SplitsEquivalence.xTree_unique`). The base case of Theorem 4,
`Banos2019.tildeDetermined_zero`, applies it to `Ñ₁` and `Ñ₂`.
