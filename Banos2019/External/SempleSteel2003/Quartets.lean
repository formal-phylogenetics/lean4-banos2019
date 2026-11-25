module

public import Phylogenetics.Tree.SplitsEquivalence
public import Phylogenetics.Tree.Splits

/-!
# Semple, Steel 2003: a phylogenetic `X`-tree is determined by its quartet trees

C. Semple, M. Steel, *Phylogenetics*, Oxford Lecture Series in Mathematics and its Applications 24,
Oxford University Press, 2003.

Baños 2019 cites this source in the proof of Theorem 4: without cycles of size at least four, the
quartet trees displayed by `Ñ` "determine the topology `Ñ` by a standard result". It is stated here
in the source's terms: phylogenetic `X`-trees, Mathlib graphs that are `X`-trees
(`Phylogenetics.SplitsEquivalence.IsXTree`) labelled bijectively onto their leaves
(`IsPhylogeneticXTree`), and the set `Q(T)` of the quartet trees they display (`quartets`), read on
the splits of their edges (`splitFinset`).

* `isUnrootedTree_splitFinset`: the splits of a phylogenetic `X`-tree form an unrooted tree.
* `exists_iso_of_quartets_eq`: two phylogenetic `X`-trees with the same quartet trees are
  isomorphic, by an isomorphism fixing the taxa. The quartet trees give the splits
  (`Phylogenetics.subset_of_forall_displays`), and the splits give the tree (the Splits Equivalence
  Theorem, `Phylogenetics.SplitsEquivalence.xTree_unique`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.SplitsEquivalence Finset
open scoped Classical

namespace External.SempleSteel2003

variable {W W' X : Type*} {T : SimpleGraph W} {φ : X → W}

/-- A phylogenetic `X`-tree: an `X`-tree whose labelling is a bijection onto its leaves. Every node
of degree at most two of an `X`-tree is labelled, so the other nodes have degree at least three. -/
structure IsPhylogeneticXTree (T : SimpleGraph W) (φ : X → W) : Prop where
  isXTree : IsXTree T φ
  injective : Function.Injective φ
  leaf : ∀ x, (T.neighborSet (φ x)).ncard = 1

/-- The sides of the splits of the edges of `T`, as finite sets. -/
def splitFinset [Fintype X] (T : SimpleGraph W) (φ : X → W) : Finset (Finset X) :=
  univ.filter fun A => (↑A : Set X) ∈ splitSides T φ

/-- A finite set of taxa is in `splitFinset T φ` exactly when it is a side of a split of `T`. -/
theorem mem_splitFinset [Fintype X] {A : Finset X} :
    A ∈ splitFinset T φ ↔ (↑A : Set X) ∈ splitSides T φ := by
  simp [splitFinset]

/-- The quartet trees `Q(T)` displayed by the `X`-tree `T`: the quartet trees `ab|cd` for which the
split of an edge of `T` has `a` and `b` on one side and `c` and `d` on the other. -/
def quartets [Fintype X] [DecidableEq X] (T : SimpleGraph W) (φ : X → W) : Set (QuartetTree X) :=
  {s | Displays (splitFinset T φ) s}

/-- A node with a single neighbour `n` reaches only itself without the edge to `n`. -/
theorem eq_of_reachable_deleteEdges_of_ncard_eq_one {w n z : W}
    (hw : (T.neighborSet w).ncard = 1) (hn : T.Adj w n)
    (h : (T.deleteEdges {s(w, n)}).Reachable w z) : z = w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  rcases Relation.ReflTransGen.cases_head h with h | ⟨m, hm, -⟩
  · exact h.symm
  · exfalso
    rw [SimpleGraph.deleteEdges_adj] at hm
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.1 hw
    have h1 : n ∈ T.neighborSet w := hn
    have h2 : m ∈ T.neighborSet w := hm.1
    rw [hy, Set.mem_singleton_iff] at h1 h2
    exact hm.2 (by rw [h2, ← h1]; exact Set.mem_singleton _)

/-- The side of the edge at a leaf is its label alone. -/
theorem sideOf_leaf (hinj : Function.Injective φ) {x : X} (hw : (T.neighborSet (φ x)).ncard = 1)
    {n : W} (hn : T.Adj (φ x) n) : sideOf T φ s(φ x, n) (φ x) = {x} := by
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · intro h
    exact hinj (eq_of_reachable_deleteEdges_of_ncard_eq_one hw hn h)
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

/-- Each side of a split of an `X`-tree is nonempty, and its complement is a side too. -/
theorem compl_mem_splitSides [Finite W] (hX : IsXTree T φ) {A : Set X}
    (hA : A ∈ splitSides T φ) : A.Nonempty ∧ Aᶜ.Nonempty ∧ Aᶜ ∈ splitSides T φ := by
  obtain ⟨e, he, x, rfl⟩ := hA
  refine ⟨⟨x, SimpleGraph.Reachable.refl _⟩, ?_⟩
  induction e using Sym2.ind with
  | _ a b =>
  have hab : T.Adj a b := he
  have key : ∀ {a b : W}, T.Adj a b → (T.deleteEdges {s(a, b)}).Reachable a (φ x) →
      (edgeSide T φ s(a, b) x)ᶜ.Nonempty ∧ (edgeSide T φ s(a, b) x)ᶜ ∈ splitSides T φ := by
    intro a b hab hax
    obtain ⟨y, hy⟩ := exists_label_branch hX hab
    have hnr : ¬ (T.deleteEdges {s(a, b)}).Reachable a b :=
      not_reachable_deleteEdges hX.isTree.2 hab
    have hc : (edgeSide T φ s(a, b) x)ᶜ = sideOf T φ s(a, b) b := by
      rw [edgeSide_eq_sideOf, ← sideOf_eq_of_reachable hax]
      exact sideOf_compl hX.isTree hab hnr
    rw [hc]
    refine ⟨⟨y, hy⟩, s(a, b), hab, y, ?_⟩
    rw [edgeSide_eq_sideOf]
    exact sideOf_eq_of_reachable hy
  rcases reachable_deleteEdges_or hX.isTree.1 a b (φ x) with h | h
  · exact key hab h
  · rw [Sym2.eq_swap]
    exact key hab.symm (by rw [Sym2.eq_swap]; exact h)

/-- The splits of an `X`-tree are pairwise compatible (Semple, Steel 2003, Theorem 3.1.4). -/
theorem pairwiseCompatible_splitSides [Finite X] [Nonempty X] [Finite W] (hX : IsXTree T φ) :
    PairwiseCompatible (splitSides T φ) := by
  obtain ⟨n, T', ⟨f⟩⟩ := exists_iso_fin T
  exact (exists_xTree_iff (F := splitSides T φ) fun A hA => compl_mem_splitSides hX hA).2
    ⟨n, T', f ∘ φ, hX.map f, splitSides_map f⟩

/-- **The splits of an `X`-tree with injectively labelled leaves form an unrooted tree.** -/
theorem isUnrootedTree_splitFinset [Fintype X] [DecidableEq X] [Finite W] (hX : IsXTree T φ)
    (hinj : Function.Injective φ) (hleaf : ∀ x, (T.neighborSet (φ x)).ncard = 1)
    (h2 : 2 ≤ Fintype.card X) : IsUnrootedTree (splitFinset T φ) := by
  have : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  refine (isUnrootedTree_iff h2 _).2 ⟨fun A hA => ?_, fun A hA => ?_, fun A hA => ?_,
    fun x => ?_, fun A hA B hB => ?_⟩
  · obtain ⟨y, hy⟩ := (compl_mem_splitSides hX (mem_splitFinset.1 hA)).1
    exact ⟨y, hy⟩
  · obtain ⟨y, hy⟩ := (compl_mem_splitSides hX (mem_splitFinset.1 hA)).2.1
    exact ⟨y, by simpa using hy⟩
  · rw [mem_splitFinset, Finset.coe_compl]
    exact (compl_mem_splitSides hX (mem_splitFinset.1 hA)).2.2
  · rw [mem_splitFinset, Finset.coe_singleton]
    obtain ⟨n, hn⟩ := Set.ncard_eq_one.1 (hleaf x)
    have hadj : T.Adj (φ x) n := by
      have : n ∈ T.neighborSet (φ x) := by rw [hn]; exact Set.mem_singleton _
      exact this
    refine ⟨s(φ x, n), hadj, x, ?_⟩
    rw [edgeSide_eq_sideOf, sideOf_leaf hinj (hleaf x) hadj]
  · have hc := pairwiseCompatible_splitSides hX _ (mem_splitFinset.1 hA) _
      (mem_splitFinset.1 hB)
    rcases hc with h | h | h | h
    · refine Or.inr (Or.inr (Or.inl (Finset.disjoint_left.2 fun x hxA hxB => ?_)))
      exact (Set.eq_empty_iff_forall_notMem.1 h x) ⟨hxA, hxB⟩
    · exact Or.inl fun x hxA => by_contra fun hxB =>
        (Set.eq_empty_iff_forall_notMem.1 h x) ⟨hxA, hxB⟩
    · exact Or.inr (Or.inl fun x hxB => by_contra fun hxA =>
        (Set.eq_empty_iff_forall_notMem.1 h x) ⟨hxA, hxB⟩)
    · refine Or.inr (Or.inr (Or.inr (Finset.eq_univ_of_forall fun x => ?_)))
      by_contra hx
      rw [Finset.mem_union, not_or] at hx
      exact (Set.eq_empty_iff_forall_notMem.1 h x) ⟨hx.1, hx.2⟩

/-- A phylogenetic `X`-tree has at least two taxa: the branch beyond the leaf of a taxon holds
another label. -/
theorem IsPhylogeneticXTree.two_le_card [Fintype X] [Finite W] (hT : IsPhylogeneticXTree T φ) :
    2 ≤ Fintype.card X := by
  have hX := hT.isXTree
  have : Nonempty W := hX.isTree.1.nonempty
  obtain ⟨w⟩ := this
  obtain ⟨x⟩ : Nonempty X := by
    by_cases hw : (T.neighborSet w).ncard ≤ 2
    · obtain ⟨x, -⟩ := hX.labelled w hw
      exact ⟨x⟩
    · obtain ⟨b, hb⟩ := (Set.nonempty_of_ncard_ne_zero (by omega) : (T.neighborSet w).Nonempty)
      obtain ⟨x, -⟩ := exists_label_branch hX (b := b) hb
      exact ⟨x⟩
  obtain ⟨n, hn⟩ := Set.ncard_eq_one.1 (hT.leaf x)
  have hadj : T.Adj (φ x) n := by
    have : n ∈ T.neighborSet (φ x) := by rw [hn]; exact Set.mem_singleton _
    exact this
  obtain ⟨y, hy⟩ := exists_label_branch hX hadj
  refine Fintype.one_lt_card_iff.2 ⟨x, y, fun hxy => ?_⟩
  subst hxy
  exact not_reachable_deleteEdges hX.isTree.2 hadj hy.symm

/-- **A phylogenetic `X`-tree is determined by its quartet trees** (`ext:semple-steel`): two
phylogenetic `X`-trees `T` and `T'` with `Q(T) = Q(T')` are isomorphic, by an isomorphism fixing the
taxa. Baños 2019 cites it in the proof of Theorem 4 ("these then determine the topology `Ñ` by a
standard result [22]"). It is the case of phylogenetic `X`-trees of Semple and Steel 2003,
Theorem 6.3.5, by which an `X`-tree is determined up to isomorphism by its restrictions to the sets
of at most four taxa: the restrictions of a phylogenetic `X`-tree to at most three taxa are always
the same, and its restriction to four taxa is the quartet tree it displays on them, or the star when
it displays none. The quartet trees give the splits: the splits of a phylogenetic `X`-tree form an
unrooted tree (`isUnrootedTree_splitFinset`), and an unrooted tree has a split with at least two
taxa on each side when it displays the quartet trees of the split
(`Phylogenetics.subset_of_forall_displays`). The splits give the tree up to isomorphism (the Splits
Equivalence Theorem, Semple and Steel 2003, Theorem 3.1.4, `SplitsEquivalence.xTree_unique`). -/
theorem exists_iso_of_quartets_eq [Fintype X] [DecidableEq X] [Finite W] [Finite W']
    {T' : SimpleGraph W'} {φ' : X → W'} (hT : IsPhylogeneticXTree T φ)
    (hT' : IsPhylogeneticXTree T' φ') (h : quartets T φ = quartets T' φ') :
    ∃ f : T ≃g T', ∀ x, f (φ x) = φ' x := by
  have h2 := hT.two_le_card
  have : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  have hU := isUnrootedTree_splitFinset hT.isXTree hT.injective hT.leaf h2
  have hU' := isUnrootedTree_splitFinset hT'.isXTree hT'.injective hT'.leaf h2
  have hF : splitFinset T φ = splitFinset T' φ' := Finset.Subset.antisymm
    (subset_of_forall_displays hU' hU fun s hs => (Set.ext_iff.1 h s).1 hs)
    (subset_of_forall_displays hU hU' fun s hs => (Set.ext_iff.1 h s).2 hs)
  refine xTree_unique hT.isXTree hT'.isXTree ?_
  ext A
  rw [← Set.Finite.coe_toFinset (Set.toFinite A), ← mem_splitFinset, ← mem_splitFinset, hF]

end External.SempleSteel2003
