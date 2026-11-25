module

public import Banos2019.Identify.Generic
public import Banos2019.Identify.QuartetCycles
public import Banos2019.Identify.Counterexample
public import Banos2019.Identify.BlocksFromS
public import Banos2019.Identify.TildeInduction

/-!
# Identifying cycles in networks (Baños 2019, Sections 8 and 9)

The 4-network blocks, the blocks of each cycle of size at least four and their cyclic order are
determined by the set `S` of sets of four taxa with the Big Cycle property, for generic parameters; with
them, the orderings of the quartet concordance factors determine the network `Ñ` (`theorem4`). "Can be
determined from `S`" is stated as: there is a function of `S` that gives the object for every network
and generic parameters.

* `lemma14`, `lemma15`, `lemma16`, `theorem4`; `proposition12`, `proposition13` (Section 9).

The set `S` (`bcSets`), the constructions of the proofs of Lemmas 14, 15 and 16 from `S` and from the
comparisons of concordance factors, and these three lemmas at parameters satisfying the statement of
Lemma 12, are in `Identify/BlocksFromS.lean`. The facts on the cycles of `N⁻` and of `Q⁻_s` that the
proofs use are in `Identify/`: the blocks of a cycle (`Identify/Blocks.lean`,
`Identify/HybridBlock.lean`), their order (`Identify/CycleOrder.lean`), and the cycles that a cycle of
`N⁻` induces in `Q⁻_s` (`Identify/QuartetCycles.lean`). The network refuting Proposition 13 as printed
is in `Identify/Counterexample.lean`.

The induction of Theorem 4 is in `Identify/TildeInduction.lean` (`tilde_sdIso_of_data`,
`tildeDetermined`), on: its generic conditions (`Identify/TildeDefs.lean`,
`Identify/NonDegenerate.lean`), the base case (`Identify/TildeBase.lean`, with
`Identify/TreeIso.lean`), the induced networks (`Identify/InducedCycles.lean`), the gluing of two
networks at leaves (`Identify/Glue.lean`), the tree of cycles (`Identify/TreeOfCycles.lean`), the leaf
cycle and a cycle whose blocks are single taxa (`Identify/TildeCycle.lean`), and the 4-network blocks
and cycle data that Lemmas 14, 15 and 16 read from the orderings of the concordance factors
(`Identify/SameData.lean`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-- The edges of the cycles of size at least four of `N⁻`; their network blocks are the 4-network
blocks. -/
def bigCycleEdges {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') : Set E' :=
  familyEdges (cyclesOfSizeAtLeast G.graph 4)

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **Lemma 14** (`netblo`): for generic parameters, the 4-network blocks of a level-1 network are
determined by `S`.

The proof is the paper's: the 4-network block of `a` is the complement of `Y_a`. A set of four taxa with
the Big Cycle property is separated by a cycle of size at least four (Lemma 12), so its taxa are in
distinct 4-network blocks. Conversely, a taxon `b` outside the 4-network block of `a` is in another
block than `a` of some cycle `C_v` of size at least four (Lemma 4); with taxa `c`, `d` of two other
blocks, one of the four in the hybrid block, `{a, b, c, d}` has the Big Cycle property (Lemma 12), and
`b ∈ Y_a`.
Departure from the paper: the paper's cases `|X| < 3` ("nothing to prove"), `|X| = 4` and `|X| ≥ 5`
leave out `|X| = 3`; "`|X| < 3`" reads as "`|X| < 4`", where there is no set of four taxa. The paper
derives the case `|X| = 4` from Proposition 9, which gives only one of the two inclusions; its argument
for `|X| ≥ 5` uses no bound on `|X|`, and the proof applies it to every `X`. -/
theorem lemma14 (hX : Nontrivial X) :
    ∃ F : Set (Finset X) → X → X → Prop,
      ∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X)
        (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph →
        ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ x y,
          (F (bcSets N θ) x y ↔
            SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf
              (bigCycleEdges (unrooted N hN hX)) x y) := by
  refine ⟨fun S x y => y ∉ complementBlock S x, ?_⟩
  intro V E _ _ N hN h1
  exact (lemma12 hN h1 hX).mono fun θ h12 hθ x y =>
    lemma14_core hN h1 hX (fun s h4 => by convert h12 hθ s h4) x y

/-- **Lemma 15** (`blov`): for generic parameters, for every set `s ∈ S`, the blocks of the cycle `C_v`
of `N⁻` whose hybrid node `v` it determines and the size `k_v` of the cycle are determined by `S`, and so
is the hybrid block when `k_v ≥ 5`.

The proof is the paper's. The taxa of `s` are in four distinct blocks of `C_v`, one in the hybrid block
(Lemma 12), and a set of `S` sharing three taxa with `s` determines `v` too (Lemma 13), so it is a set of
four taxa that `C_v` separates: `Z_{s ∖ {t}}` is the union of the blocks other than those of `s ∖ {t}`,
or the hybrid block when `t` is the taxon `a` of `s` in it (`mem_extensions_iff`). When `k_v = 4`, the
four sets `Z_{s ∖ {t}}` are the four blocks; when `k_v ≥ 5`, those for `t ≠ a` meet, and `Z_{s ∖ {a}}`
is the hybrid block. The other blocks come from the sets `{y} ∪ s ∖ {g}` and, for the taxa outside the
blocks of `s`, from the same steps applied to `T ∪ {x}` (`SameBlockFive`). -/
theorem lemma15 (hX : Nontrivial X) :
    ∃ (B : Set (Finset X) → Finset X → X → X → Prop) (K : Set (Finset X) → Finset X → ℕ)
      (H : Set (Finset X) → Finset X → Set X),
      ∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X)
        (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph →
        ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ s (hs : s ∈ bcSets N θ),
          ∀ C w, IsCycle (unrooted N hN hX).graph C → IsHybridNodeOf (unrooted N hN hX) C w →
            Determines hN s hs.1 w.1.1 →
              (∀ x y, B (bcSets N θ) s x y ↔
                SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) ∧
              K (bcSets N θ) s = C.ncard ∧
              (5 ≤ C.ncard → H (bcSets N θ) s = {x | DescendsFrom (unrooted N hN hX) w x}) := by
  refine ⟨blockRelation, blockCount, hybridBlock, ?_⟩
  intro V E _ _ N hN h1
  refine (lemma12 hN h1 hX).mono fun θ h12 hθ s hs C w hC hw hdet => ?_
  exact lemma15_core hN h1 hX hθ (fun s h4 => by convert h12 hθ s h4) hs hC hw hdet

/-- **Lemma 16** (`orderofcycles`): for generic parameters, the order of the blocks around each cycle
`C_v` of size at least four (which blocks are adjacent) is determined by the orderings of the
concordance factors: the function `A` sees only how the concordance factors of quartet trees on the same
four taxa compare (Definition 15).

The proof is the paper's: the blocks, the size and, for `k_v ≥ 5`, the hybrid block come from Lemma 15,
and the order from `q^BC` of the sets of four taxa that `C_v` separates, by Proposition 11. For `k_v = 4`
these are the sets with one taxon in each block. For `k_v ≥ 5` the procedure is the paper's (`adjacencyOf`). With `a₁` in the
hybrid block `A₁`, the test `q^BC_{a₁aⱼxy} ≠ a₁aⱼ|xy` for all `x, y` in distinct other blocks gives the
two blocks `A_p` and `A_q` adjacent to `A₁` (`AdjacencyTest`). The block `A_j` (`j ≠ 1, p, q`) adjacent
to `A_q` is the one with `q^BC_{a₁aⱼa_px} ≠ a₁aⱼ|xa_p` for all `x` in the blocks other than `A₁`, `A_p`,
`A_q` and `A_j`: by Proposition 11 this says that the blocks of `a₁` and `aⱼ` are joined along `C_v`
avoiding those of `x` and `a_p`, which fails exactly when the block of `x` lies between `A₁` and `A_j` on
the side of `A_q`. Continuing in this way, each step places the block that passes this test against the
blocks not yet placed (`IsNextBlock`, `placedBlocks`), and two blocks are adjacent when they are
consecutive in the order `A₁, A_q, …, A_p` so built (`FollowsBlock`, `followsBlock_iff`). -/
theorem lemma16 (hX : Nontrivial X) :
    ∃ A : (QuartetTree X → QuartetTree X → Prop) → Finset X → X → X → Prop,
      ∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X)
        (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph →
        ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ s (hs : s ∈ bcSets N θ),
          ∀ C w, IsCycle (unrooted N hN hX).graph C → IsHybridNodeOf (unrooted N hN hX) C w →
            Determines hN s hs.1 w.1.1 → ∀ x y,
              (A (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) s x y ↔
                AdjacentBlocks (unrooted N hN hX) C x y) := by
  -- the blocks, the size and the hybrid block of the cycle, from `S` (Lemma 15)
  obtain ⟨B, K, H, h15⟩ := lemma15 hX
  refine ⟨adjacencyOf B K H, ?_⟩
  intro V E _ _ N hN h1
  refine ((h15 V E N hN h1).and (lemma12 hN h1 hX)).mono
    fun θ ⟨h15θ, h12⟩ hθ s hs C w hC hw hdet x y => ?_
  obtain ⟨hB, hK, hH⟩ := h15θ hθ s hs C w hC hw hdet
  exact lemma16_core hN h1 hX hθ (fun s h4 => by convert h12 hθ s h4) hs hC hw hdet hB hK hH x y

/-- **Theorem 4** (`thm::main`): under the network multispecies coalescent, for generic parameters, the
orderings of the quartet concordance factors identify the semidirected topological network `Ñ` obtained
from `N⁻` by contracting all 2- and 3-cycles and forgetting the directions of the hybrid edges in
4-cycles, while retaining the directions of the hybrid edges of larger cycles. There is a property `G`
of the parameters of each network, which holds for generic parameters, such that two level-1 networks on
the same taxa, with parameters satisfying `G` and the same orderings of concordance factors, have
isomorphic networks `Ñ`.

The proof is the paper's. `G` is the conditions `GoodParams` (the statement of Lemma 12, and
concordance factors not all equal on any set of four taxa), which hold for generic parameters
(`forGenericParams_goodParams`), with the conclusions of Lemmas 14, 15 and 16 for the functions these
lemmas give (`GivesFourNetworkBlocks`, `GivesBlocks`, `GivesAdjacency`). For `N₁` and `N₂`, Lemma 14
gives the same 4-network blocks (`sameFourNetworkBlocks_of_gives`), and Lemmas 15 and 16 give, for each
cycle of size at least four of `N₁⁻`, a cycle of `N₂⁻` with the same blocks, size, order of the blocks
and, for size at least five, hybrid block (`sameCycleData_of_gives`). The induction is on the number of
cycles of size at least four of `N₁⁻` (`tilde_sdIso_of_data`, `tildeDetermined`,
`Identify/TildeInduction.lean`). Its claim is the theorem for that number of cycles (`TildeDetermined`):
the networks it is applied to, induced on sets of taxa, have their data read from their own orderings
by the arguments of Lemmas 14, 15 and 16 at their parameters (`sameCycleData_of_sameOrdering`,
`sameFourNetworkBlocks_of_sameOrdering`).

* No cycle of size at least four (`tildeDetermined_zero`): `Ñ₁` and `Ñ₂` are trees. A quartet tree that
  `Ñ` displays is that of a cut edge of `Q⊕_s`, and the two other quartet trees on its taxa have equal
  concordance factors, by Proposition 6 without a `3₂`-cycle and by Proposition 7 with one. So the
  orderings give the quartet trees that `Ñ₁` and `Ñ₂` display, and these determine the trees (Semple
  and Steel 2003).
* One cycle `C_v` (`tilde_sdIso_one_of_sameCycleData`). When its `v`-blocks are single taxa, `Ñ` is the
  cycle with a taxon at each node, in the order that the data give, its hybrid edges directed when
  its size is at least five (`tilde_sdIso_of_singletonBlocks`). The network induced on `P_u ∪ {q}`, for a `v`-block `P_u` with at
  least two taxa and `q ∉ P_u`, has no cycle of size at least four, so its network `Ñ` is a tree that
  the orderings determine. Gluing it at its leaf `q` to the network `Ñ` of the network induced on
  `(X ∖ P_u) ∪ {x}` (`x ∈ P_u`), at its leaf `x`, joins the root of the tree of `P_u` for the outgroup
  `q` to `u` by an edge. "Doing this for all `v`-blocks" is an induction on the number of `v`-blocks
  with at least two taxa (`tildeDeterminedOneCycle`): the cycle of size at least four of the network
  induced on `(X ∖ P_u) ∪ {x}` is `C_v` with `P_u` replaced by `x`, with fewer such blocks
  (`ncard_nontrivialBlocks_inducedLSA_lt`), and the data of that network are read from its orderings.
* More cycles (`tilde_sdIso_of_lt_of_data`). Following Definition 13, a leaf of `T₁`, the tree of
  cycles of `Ñ₁`, arises from a cycle `C_v` of `N₁⁻` all of whose `v`-blocks but one, `S_2`, the block
  of a node `u`, are 4-network blocks (`exists_leaf_bigCycle`); every other cycle of size at least four
  then has the taxa of `S_1 = X ∖ S_2` in one of its blocks. The cycle of `N₂⁻` with the same blocks,
  all of them but `S_2` 4-network blocks of `N₂⁻`, gives a leaf of `T₂`, the tree of cycles of `Ñ₂`,
  and its node with the block `S_2` (`exists_isLeafNode_counterpart`); both networks split at these
  leaves. The networks induced on `S_1 ∪ {s_2}` and on `S_2 ∪ {s_1}` have fewer cycles of size at
  least four, so the claim applies to them, with their data read from their own orderings; `Ñ` is
  obtained by identifying `s_1` in the network `Ñ` of one with `s_2` in that of the other and
  suppressing that node (`tilde_sdIso_glue`, `glue_congr`).

The induced networks `N⁻_{S_i ∪ {s_j}}` (Definition 10) are read as `(N⊕_Y)⁻`, the network `N⁻` of the
induced LSA network on `Y`, as `Q⁻_s` is for quartets (Section 5): the two are isomorphic
(`nonempty_sdIso_inducedUnrooted_unrooted_inducedLSA`, from Proposition 1).

The proof fills the following steps, which the paper does not give, along its lines.

* The networks induced on sets of taxa satisfy the generic conditions: their concordance factors are
  those of `N` on their taxa (Theorem 2), and a cycle of `(N⊕_Y)⁻` that separates four taxa comes from
  one of `N⁻` that separates them (`exists_separatesQuartet_induced_iff`), so the statement of Lemma 12
  and the non-degeneracy pass to them (`goodParams_inducedLSA`), and so do the same orderings
  (`sameOrdering_inducedLSA`).
* The numbers of cycles of size at least four of the pieces: a cycle of size at least four of
  `(N⊕_Y)⁻` comes from one of `N⁻` that separates four taxa of `Y` (`bigCycleCount_inducedLSA_le`,
  `bigCycleCount_inducedLSA_insert_compl_le_one`, `bigCycleCount_inducedLSA_insert_lt`).
* `Ñ` is the gluing of the networks `Ñ` of the two pieces (`tilde_sdIso_glue`): the edge of `u` off its
  cycle lies on no cycle, and contracting the 2- and 3-cycles and suppressing the nodes of degree two
  commute with taking a side of that edge.
* In the base case, `N₂⁻` has no cycle of size at least four either: such a cycle would separate four
  taxa with the Big Cycle property for `N₂`, so for `N₁` (Lemma 12, `ncard_le_three_of_sameOrdering`).
* The base case (TeX l. 1180) reads from "the ordering of the concordance factors" the quartet tree
  obtained from `Q⁻_s` by suppressing its 2- and 3-cycles; that this is the quartet tree `Ñ` displays
  on `s` is not stated, and holds through the cut arcs of `Ñ` (`alternatives_eq_of_displays`). The reading that holds is the quartet tree whose concordance factor differs
  from the other two, which are equal (Propositions 6 and 7); it need not have the largest one (with a
  `3₂`-cycle, Example 6). The reading needs the three concordance factors not to be all equal, which
  with a `3₂`-cycle they can be (Proposition 7); this holds for generic parameters
  (`forGenericParams_nonDegenerateCF`) and is part of `G`, with the statement of Lemma 12
  (`GoodParams`).
* The tree of cycles (Definition 13): that `T` is a tree, and that a leaf of `T` arises from a cycle
  `C_v` exactly when all `v`-blocks but one are 4-network blocks (`Identify/TreeOfCycles.lean`). -/
theorem theorem4 (hX : Nontrivial X) :
    ∃ G : ∀ (V E : Type) [Fintype V] [Fintype E], RootedNetwork V E X → MetricData E → Prop,
      (∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X),
        IsBinaryRootedNetwork N → IsLevelOne N.graph → ForGenericParams N (G V E N)) ∧
      ∀ (V₁ E₁ V₂ E₂ : Type) [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
        (N₁ : RootedNetwork V₁ E₁ X) (N₂ : RootedNetwork V₂ E₂ X)
        (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂),
        IsLevelOne N₁.graph → IsLevelOne N₂.graph →
        ∀ θ₁ θ₂, IsMetricNetwork N₁ θ₁ → IsMetricNetwork N₂ θ₂ → G V₁ E₁ N₁ θ₁ → G V₂ E₂ N₂ θ₂ →
          SameOrdering (cf N₁ θ₁) (cf N₂ θ₂) →
          Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX))) := by
  -- the functions of Lemmas 14, 15 and 16
  obtain ⟨F, h14⟩ := lemma14 hX
  obtain ⟨B, K, H, h15⟩ := lemma15 hX
  obtain ⟨A, h16⟩ := lemma16 hX
  refine ⟨fun V E _ _ N θ => GoodParams hX N θ ∧ ∀ hN : IsBinaryRootedNetwork N,
      IsLevelOne N.graph → GivesFourNetworkBlocks F hN hX θ ∧ GivesBlocks B K H hN hX θ ∧
        GivesAdjacency A hN hX θ,
    fun V E _ _ N hN h1 => (forGenericParams_goodParams hN h1 hX).and
      (((h14 V E N hN h1).and ((h15 V E N hN h1).and (h16 V E N hN h1))).mono
        fun θ h _ _ => h), ?_⟩
  intro V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord
  obtain ⟨h14₁, h15₁, h16₁⟩ := hG₁.2 hN₁ h1₁
  obtain ⟨h14₂, h15₂, h16₂⟩ := hG₂.2 hN₂ h1₂
  -- the data of `N₁` and `N₂`: the cycle data by Lemmas 15 and 16, the 4-network blocks by
  -- Lemma 14; then the induction, whose pieces read their data from their own orderings
  exact tilde_sdIso_of_data (fun k _ => tildeDetermined k) hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁.1 hG₂.1
    hord (sameCycleData_of_gives hN₁ hN₂ h1₁ h1₂ hX hθ₁ hθ₂ hG₁.1 hG₂.1 hord h15₁ h15₂ h16₁ h16₂)
    (sameFourNetworkBlocks_of_gives hN₁ hN₂ hX hθ₁ hθ₂ hord h14₁ h14₂) rfl

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **Proposition 12** (`pub:prop12`; unlabelled in the TeX): for generic parameters, if `s` satisfies the
Cycle property but not the Big Cycle property, and no `{i, j, k, e}` with `i, j, k ∈ s` distinct satisfies
the Big Cycle property, then `N⁻` contains a 3-cycle with at least two taxa descending from its hybrid
node.

The paper's proof: by Proposition 8, `Q⁻_s` has a `3₂`-cycle, so three taxa of `s` are in distinct
blocks of a cycle `C_v` of `N⁻`; no extension of three of them satisfies the Big Cycle property, so
`C_v` has size less than four; and by Proposition 7, `C_v` has size three with two taxa of `s` below `v`.
Departure from the paper: Proposition 8 gives a `3₂`-cycle or a 4-cycle, and only for generic parameters
does the failure of the Big Cycle property exclude the 4-cycle (Theorem 3): that is Corollary 4, which
the proof uses. A fourth block of `C_v` would give, with a taxon of `s` in the hybrid block and two in
other blocks, a set of four taxa with the Big Cycle property (Lemma 12). The last step miscites
Proposition 7, which says where the concordance factors of a `3₂`-cycle lie: with the size less than
four, the size three follows from the three blocks of `C_v` that hold taxa of `s`, and the two taxa
below `v` from the definition of a `3₂`-cycle. -/
theorem proposition12 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) :
    ForGenericParams N fun θ => IsMetricNetwork N θ → CyclePropertyOn (cf N θ) s →
      ¬ BigCycleOn (cf N θ) s →
      (¬ ∃ t ⊆ s, #t = 3 ∧ ∃ e ∉ t, BigCycleOn (cf N θ) (insert e t)) →
      ∃ C v, IsCycle (unrooted N hN hX).graph C ∧ C.ncard = 3 ∧
        IsHybridNodeOf (unrooted N hN hX) C v ∧
        2 ≤ {x | DescendsFrom (unrooted N hN hX) v x}.ncard := by
  refine ((corollary4 hN h1 hs).and (lemma12 hN h1 hX)).mono ?_
  rintro θ ⟨h4, h12⟩ hθ hcp hbc hno
  -- the `3₂`-cycle of `Q⁻_s` and the cycle `C_v` of `N⁻` it comes from
  obtain ⟨C, v, hC, hv, p, hp, q, hq, r, hr, t, ht, hpq, hdp, hdq, hpr, hpt, hrt⟩ :=
    exists_cycle_of_hasThreeTwoCycle hN h1 hX hs (h4 hθ (by convert hcp) (by convert hbc))
  have hβp := (blockNode_eq_iff_descendsFrom h1 hC hv p).2 hdp
  rw [sameBlock_iff_blockNode_eq h1 hC] at hpr hpt hrt
  set β := blockNode (unrooted N hN hX) C
  have hsub : ({β p, β r, β t} : Set _) ⊆ cycleNodes (unrooted N hN hX).graph C := by
    rintro u (rfl | rfl | rfl) <;> exact blockNode_mem hC _
  have h3 : ({β p, β r, β t} : Set _).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨_, _, _, hpr, hpt, hrt, rfl⟩
  refine ⟨C, v, hC, le_antisymm ?_ ?_, hv, ?_⟩
  · -- a fourth block would give a set of four taxa with the Big Cycle property (Lemma 12)
    by_contra hlt
    obtain ⟨u, hu, hun⟩ :=
      hC.exists_mem_cycleNodes_notMem (Set.toFinite {β p, β r, β t}) (by omega)
    obtain ⟨e, rfl⟩ := exists_blockNode_eq h1 hC hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hun
    obtain ⟨hep, her, het⟩ := hun
    have hne : ∀ {a b : X}, β a ≠ β b → a ≠ b := fun h h' => h (h' ▸ rfl)
    refine hno ⟨{p, r, t}, ?_, card_eq_three.2 ⟨p, r, t, hne hpr, hne hpt, hne hrt, rfl⟩, e, ?_, ?_⟩
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hne hep, hne her, hne het⟩
    · have h4' := card_four_of_ne (hne hep) (hne her) (hne het) (hne hpr) (hne hpt) (hne hrt)
      convert (h12 hθ _ h4').2 ⟨C, v, by omega, (separatesQuartet_iff h1 hC hv _).2
        ⟨injOn_four hep her het hpr hpt hrt, p, by simp, hβp⟩⟩
  · -- three taxa of `s` in distinct blocks
    rw [← ncard_cycleNodes hC, ← h3]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  · -- two taxa descend from the hybrid node
    rw [← Set.ncard_pair hpq]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro x (rfl | rfl)
    · exact hdp
    · exact hdq

/-- `C` is the only cycle of `G` that a `3₂`-cycle on `T` can come from: no cycle `C'` of `G` other
than `C`, with hybrid node `w`, has two taxa `p ≠ q` of `T` descending from `w` and three taxa
`p, r, t` of `T` in pairwise distinct blocks (the cycles that `exists_cycle_of_hasThreeTwoCycle`
gives). -/
def OnlyThreeTwoSource {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E')
    (T : Finset X') : Prop :=
  ∀ C' w, IsCycle G.graph C' → IsHybridNodeOf G C' w → C' ≠ C →
    ¬ ∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T, ∃ t ∈ T, p ≠ q ∧ DescendsFrom G w p ∧ DescendsFrom G w q ∧
      ¬ SameBlock G.graph G.leaf C' p r ∧ ¬ SameBlock G.graph G.leaf C' p t ∧
      ¬ SameBlock G.graph G.leaf C' r t

/-- **Proposition 13** (`lem::cpto4c`), corrected: let `C_v` be a 4-cycle of `N⁻` and `a, b, c, d` taxa
in distinct `v`-blocks. For generic parameters, if for distinct `i, j, k ∈ {a, b, c, d}` some taxon `e`
makes `{i, j, k, e}` satisfy the Cycle property but not the Big Cycle property, and no cycle of `N⁻`
other than `C_v` has two of `i, j, k, e` below its hybrid node and three of them, one of those two, in
distinct blocks (`OnlyThreeTwoSource`), then `e` is in the `v`-hybrid block.

The paper states this without the last hypothesis, and its proof asserts that the 4-cycle of `Q⁻_abcd`
and the `3₂`-cycle of `Q⁻_abce` "have to have the same hybrid edges, otherwise the level-1 condition
would be violated". The `3₂`-cycle can come from another cycle of `N⁻`, and then the conclusion fails:
`proposition13_asPrinted_false`. A `3₂`-cycle of `Q⁻_ijke` comes from a cycle of `N⁻` with two of
`i, j, k, e` below its hybrid node and three of them, one of those two, in distinct blocks
(`exists_cycle_of_hasThreeTwoCycle`); the last hypothesis, that `C_v` is the only such cycle, is the
paper's step made a hypothesis.

The proof is the paper's. Say `l` is the fourth of `a, b, c, d`. The taxon `e` is not in the block of
`l`, or `i, j, k, e` would be in the four blocks of `C_v`, one of them the hybrid block, and would
satisfy the Big Cycle property (Lemma 12); so `e` is in the block of one of `i, j, k`, say `g`. By
Corollary 4, `Q⁻_ijke` has a `3₂`-cycle, which comes from a cycle of `N⁻` with two of `i, j, k, e`
below its hybrid node and three of them in distinct blocks: by the last hypothesis, from `C_v`. Its two
taxa below the hybrid node are in the hybrid block of `C_v`, and the only two of `i, j, k, e` in one
block are `g` and `e`.
Departure from the paper (reason 1, the paper's step is wrong): the step that the 4-cycle of `Q⁻_abcd`
and the `3₂`-cycle of `Q⁻_abce` have the same hybrid edges is false, and is made the last hypothesis,
as above. The paper prepares that step by fixing the order of the cycle (Theorem 4, the labels of
Figure 24) and the hybrid node of `{e, l}` together with the two of `i, j, k` other than `g`
(`{e, b, c, d}` in the paper's labels; Lemma 13), so as to compare the hybrid edges of the
two quartet networks; with the step a hypothesis, the two taxa in the hybrid block are read from the
`3₂`-cycle, and these preparations are not used.
-/
theorem proposition13 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _} {v : SemidirectedVertex hN.1 hX}
    (hC : IsCycle (unrooted N hN hX).graph C) (hC4 : C.ncard = 4)
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) {a b c d : X}
    (hblocks : ∀ x ∈ ({a, b, c, d} : Finset X), ∀ y ∈ ({a, b, c, d} : Finset X), x ≠ y →
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) :
    ForGenericParams N fun θ => IsMetricNetwork N θ →
      ∀ i ∈ ({a, b, c, d} : Finset X), ∀ j ∈ ({a, b, c, d} : Finset X),
        ∀ k ∈ ({a, b, c, d} : Finset X), i ≠ j → i ≠ k → j ≠ k → ∀ e,
          #({i, j, k, e} : Finset X) = 4 →
          OnlyThreeTwoSource (unrooted N hN hX) C {i, j, k, e} →
          CyclePropertyOn (cf N θ) {i, j, k, e} →
          ¬ BigCycleOn (cf N θ) {i, j, k, e} → DescendsFrom (unrooted N hN hX) v e := by
  refine ((forGenericParams_iInter (ι := {s : Finset X // #s = 4})
    fun s => corollary4 hN h1 s.2).and (lemma12 hN h1 hX)).mono ?_
  rintro θ ⟨h4, h12⟩ hθ i hi j hj k hk hij hik hjk e he4 honly hcp hbc
  set β := blockNode (unrooted N hN hX) C
  have hβ : ∀ x ∈ ({a, b, c, d} : Finset X), ∀ y ∈ ({a, b, c, d} : Finset X), x ≠ y → β x ≠ β y :=
    fun x hx y hy hxy => (sameBlock_iff_blockNode_eq h1 hC x y).not.1 (hblocks x hx y hy hxy)
  have hβij := hβ i hi j hj hij
  have hβik := hβ i hi k hk hik
  have hβjk := hβ j hj k hk hjk
  -- the blocks of `i, j, k` and a fourth block: the four blocks of `C_v`
  have hsub : ({β i, β j, β k} : Set _) ⊆ cycleNodes (unrooted N hN hX).graph C := by
    rintro u (rfl | rfl | rfl) <;> exact blockNode_mem hC _
  have h3 : ({β i, β j, β k} : Set _).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨_, _, _, hβij, hβik, hβjk, rfl⟩
  obtain ⟨u₄, hu₄, hu₄ijk⟩ :=
    hC.exists_mem_cycleNodes_notMem (Set.toFinite {β i, β j, β k}) (by omega)
  have hnodes : cycleNodes (unrooted N hN hX).graph C = insert u₄ {β i, β j, β k} := by
    refine (Set.eq_of_subset_of_ncard_le (Set.insert_subset hu₄ hsub) ?_ (Set.toFinite _)).symm
    rw [ncard_cycleNodes hC, hC4, Set.ncard_insert_of_notMem hu₄ijk, h3]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu₄ijk
  obtain ⟨hu₄i, hu₄j, hu₄k⟩ := hu₄ijk
  -- `e` is not in the fourth block: otherwise `{i, j, k, e}` would satisfy the Big Cycle property
  have he₄ : β e ≠ u₄ := by
    intro h
    apply hbc
    have hv' := hv.mem_cycleNodes
    rw [hnodes] at hv'
    convert (h12 hθ _ he4).2 ⟨C, v, by omega, (separatesQuartet_iff h1 hC hv _).2
      ⟨injOn_four hβij hβik (fun h' => hu₄i (h.symm.trans h'.symm)) hβjk
        (fun h' => hu₄j (h.symm.trans h'.symm)) (fun h' => hu₄k (h.symm.trans h'.symm)), ?_⟩⟩
    rcases hv' with h' | h' | h' | h'
    · exact ⟨e, by simp, h.trans h'.symm⟩
    · exact ⟨i, by simp, h'.symm⟩
    · exact ⟨j, by simp, h'.symm⟩
    · exact ⟨k, by simp, h'.symm⟩
  -- so `e` is in the block of one of `i, j, k`
  obtain ⟨g, hg, hge⟩ : ∃ g ∈ ({i, j, k} : Finset X), β g = β e := by
    have he' := blockNode_mem hC e
    rw [hnodes] at he'
    rcases he' with h' | h' | h' | h'
    · exact absurd h' he₄
    · exact ⟨i, by simp, h'.symm⟩
    · exact ⟨j, by simp, h'.symm⟩
    · exact ⟨k, by simp, h'.symm⟩
  -- by Corollary 4, `Q⁻_ijke` has a `3₂`-cycle; it comes from `C_v`
  obtain ⟨C', w, hC', hw, p, hp, q, hq, r, hr, t, ht, hpq, hdp, hdq, hpr, hpt, hrt⟩ :=
    exists_cycle_of_hasThreeTwoCycle hN h1 hX he4
      (h4 ⟨_, he4⟩ hθ (by convert hcp) (by convert hbc))
  have hCC' : C' = C := by
    by_contra hCC'
    exact honly C' w hC' hw hCC' ⟨p, hp, q, hq, r, hr, t, ht, hpq, hdp, hdq, hpr, hpt, hrt⟩
  subst hCC'
  have hwv : w = v := hw.eq h1 hC' hv
  subst hwv
  -- its two taxa below the hybrid node are `g` and `e`
  have hβp := (blockNode_eq_iff_descendsFrom h1 hC' hw p).2 hdp
  have hβq := (blockNode_eq_iff_descendsFrom h1 hC' hw q).2 hdq
  have hpair : ∀ x ∈ ({i, j, k, e} : Finset X), ∀ y ∈ ({i, j, k, e} : Finset X), x ≠ y →
      β x = β y → x = e ∨ y = e := by
    intro x hx y hy hxy hβxy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
        | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hxy
        | exact absurd hβxy ‹_› | exact absurd hβxy.symm ‹_›
  rcases hpair p hp q hq hpq (hβp.trans hβq.symm) with rfl | rfl
  · exact hdp
  · exact hdq

/-- **Proposition 13 as printed**: for every binary level-1 network, 4-cycle `C_v` of `N⁻`, and taxa
`a, b, c, d` in distinct `v`-blocks, for generic parameters, if `{i, j, k, e}` with distinct
`i, j, k ∈ {a, b, c, d}` satisfies the Cycle property but not the Big Cycle property, then `e` is in the
`v`-hybrid block. -/
def Proposition13AsPrinted : Prop :=
  ∀ (V E X : Type) [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
    (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph → ∀ (hX : Nontrivial X) (C : Set _)
    (v : SemidirectedVertex hN.1 hX), IsCycle (unrooted N hN hX).graph C → C.ncard = 4 →
    IsHybridNodeOf (unrooted N hN hX) C v → ∀ a b c d : X,
    (∀ x ∈ ({a, b, c, d} : Finset X), ∀ y ∈ ({a, b, c, d} : Finset X), x ≠ y →
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y) →
    ForGenericParams N fun θ => IsMetricNetwork N θ →
      ∀ i ∈ ({a, b, c, d} : Finset X), ∀ j ∈ ({a, b, c, d} : Finset X),
        ∀ k ∈ ({a, b, c, d} : Finset X), i ≠ j → i ≠ k → j ≠ k → ∀ e,
          #({i, j, k, e} : Finset X) = 4 → CyclePropertyOn (cf N θ) {i, j, k, e} →
          ¬ BigCycleOn (cf N θ) {i, j, k, e} → DescendsFrom (unrooted N hN hX) v e

/-- **Proposition 13 as printed is false.** In the network with edges `r → a`, `r → t`, `t → p`,
`t → u`, `p → e`, `p → u`, `u → w`, `w → x`, `w → y`, `x → b`, `x → v`, `y → c`, `y → v`, `v → d`,
`C_v = {wx, xv, wy, yv}` is a 4-cycle of `N⁻` with blocks `{a, e}`, `{b}`, `{c}`, `{d}` and hybrid block
`{d}`. In `Q⁻_abce` the cycle `C_v` disappears and the 3-cycle `t, p, u` is a `3₂`-cycle with hybrid
block `{b, c}` (Figure 18 relabelled), so on an open set of parameters around those of Example 6,
`{a, b, c, e}` satisfies the Cycle property but not the Big Cycle property, while `e` is not in the
`v`-hybrid block.
`Proposition13AsPrinted` reads "for generic parameters" as qualifying the implication, with one null set
for all `i, j, k, e` (as `X` is finite, a null set for each gives the same statement); read as part of
the hypothesis, "`{i, j, k, e}` satisfies the Cycle property but not the Big Cycle property for generic
parameters", the printed statement holds vacuously, since that hypothesis never holds: with a 4-cycle
in `Q⁻_ijke` the Big Cycle property holds for generic parameters (Theorem 3), with neither a 4-cycle
nor a `3₂`-cycle the Cycle property fails (Proposition 8), and with a `3₂`-cycle it fails when the edge
below the hybrid node is longer than `log (3/2)`, as the two taxa below it then coalesce there with
probability more than `1/3` and the other two concordance factors are equal (Proposition 7). -/
theorem proposition13_asPrinted_false : ¬ Proposition13AsPrinted :=
  proposition13AsPrinted_counterexample

end Banos2019
