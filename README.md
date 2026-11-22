# Baños 2019, in Lean

A Lean 4 and Mathlib formalization, in progress, of

> Baños, *Identifying Species Network Features from Gene Tree Quartets Under the Coalescent Model* (2019), <https://doi.org/10.1007/s11538-018-0485-4>.

It is a paper of the hub [lean4-phylo-network](https://github.com/vltanh/lean4-phylo-network) (Phylogenetic network estimation), in the collection of formalizations
rooted at [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), one paper per repository.

This page is rewritten when the formalization is done.

## Building

```sh
lake exe cache get
lake build
```

Lean and Mathlib `v4.37.0-rc1` ([`lean-toolchain`](lean-toolchain),
[`lake-manifest.json`](lake-manifest.json)).

## License

Apache-2.0: [LICENSE](LICENSE).
