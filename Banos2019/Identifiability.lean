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
* `complementBlock` (`Y_a`): the construction of the proof of Lemma 14 from `S`.

The set `S` (`bcSets`), the constructions of the proofs of Lemmas 15 and 16 from `S` and from the
comparisons of concordance factors, and these two lemmas at parameters satisfying the statement of
Lemma 12, are in `Identify/BlocksFromS.lean`. The facts on the cycles of `N⁻` and of `Q⁻_s` that the
proofs use are in `Identify/`: the blocks of a cycle (`Identify/Blocks.lean`,
`Identify/HybridBlock.lean`), their order (`Identify/CycleOrder.lean`), and the cycles that a cycle of
`N⁻` induces in `Q⁻_s` (`Identify/QuartetCycles.lean`). The network refuting Proposition 13 as printed
is in `Identify/Counterexample.lean`.

The induction of Theorem 4 is in `Identify/TildeInduction.lean` (`tildeDetermined`), on: its claim and
generic conditions (`Identify/TildeDefs.lean`, `Identify/NonDegenerate.lean`), the base case
(`Identify/TildeBase.lean`, with `Identify/TreeIso.lean`), the induced networks
(`Identify/InducedCycles.lean`), the gluing of two networks at leaves (`Identify/Glue.lean`), the tree
of cycles (`Identify/TreeOfCycles.lean`), the leaf cycle and a cycle whose blocks are single taxa
(`Identify/TildeCycle.lean`), and the counterpart of a
cycle in a network with the same orderings (`Identify/SameData.lean`).
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

/-- `Y_a` (proof of Lemma 14): the taxa other than `a` of the sets of `S` that contain `a`. -/
def complementBlock (S : Set (Finset X)) (a : X) : Set X :=
  ⋃ s ∈ {s | s ∈ S ∧ a ∈ s}, ↑(s.erase a)

/-- **Lemma 14** (`netblo`): for generic parameters, the 4-network blocks of a level-1 network are
determined by `S`.

The proof is the paper's: the 4-network block of `a` is the complement of `Y_a`. A set of four taxa with
the Big Cycle property is separated by a cycle of size at least four (Lemma 12), so its taxa are in
distinct 4-network blocks. Conversely, a taxon `b` outside the 4-network block of `a` is in another
block than `a` of some cycle `C_v` of size at least four (Lemma 4); with taxa `c`, `d` of two other
blocks, one of the four in the hybrid block, `{a, b, c, d}` has the Big Cycle property (Lemma 12), and
`b ∈ Y_a`.
Departure from the paper: the paper leaves out `|X| < 3` ("nothing to prove"; there is no set of four
taxa when `|X| < 4`) and derives the case `|X| = 4` from Proposition 9, which gives only one of the two
inclusions; its argument for `|X| ≥ 5` uses no bound on `|X|`, and the proof applies it to every `X`. -/
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
  refine (lemma12 hN h1 hX).mono fun θ h12 hθ x y => ?_
  have h12 := h12 hθ
  constructor
  · -- a taxon outside the 4-network block of `x` is in `Y_x`
    intro hy
    by_contra hnb
    obtain ⟨C, ⟨hC, hC4⟩, hCxy⟩ := lemma4 (unrooted N hN hX).leaf (unrooted_isConnected hN hX)
      (unrooted_isLevelOne hN h1 hX)
      (fun C (hC : C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4) => hC.1) hnb
    obtain ⟨v, hv⟩ := exists_isHybridNodeOf h1 hC
    obtain ⟨c, d, h4, hsep⟩ := exists_separatesQuartet_of_not_sameBlock h1 hC hC4 hv hCxy
    have hxy : y ≠ x := fun h => hCxy (h ▸ .refl)
    refine hy (Set.mem_biUnion (x := {x, y, c, d}) ⟨⟨h4, (h12 _ h4).2 ⟨C, v, hC4, hsep⟩⟩, by simp⟩ ?_)
    simp [hxy]
  · -- the taxa of a set of `S` are in distinct 4-network blocks
    intro hsb hy
    obtain ⟨s, ⟨hsS, hxs⟩, hys⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨hyx, hys⟩ := mem_erase.1 hys
    obtain ⟨C, v, hC4, hsep⟩ := (h12 s hsS.1).1 hsS.2
    exact hsep.2.2.1 x hxs y hys (Ne.symm hyx)
      (hsb.mono (Set.subset_sUnion_of_mem (show C ∈ cyclesOfSizeAtLeast _ 4 from ⟨hsep.1, hC4⟩)))

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
these are the sets with one taxon in each block. For `k_v ≥ 5` the paper finds the two blocks adjacent to
the hybrid block `A_1` with the test `q^BC_{a₁aⱼxy} ≠ a₁aⱼ|xy` for all `x, y` in other blocks, and
continues around the cycle.
Departure from the paper: the continuation step is printed as `q^BC_{a₁aⱼa_px} ≠ a₁aⱼ|xa_p`, which does
not involve the block `A_q` whose neighbour it looks for. The proof applies the test of the first step,
with a taxon of the hybrid block among the four, to every pair of blocks: two blocks are adjacent exactly
when `q^BC_{xyzz'} ≠ xy|zz'` for all `z, z'` such that `x, y, z, z'` are in four distinct blocks, one of
them the hybrid block. -/
theorem lemma16 (hX : Nontrivial X) :
    ∃ A : (QuartetTree X → QuartetTree X → Prop) → Finset X → X → X → Prop,
      ∀ (V E : Type) [Fintype V] [Fintype E] (N : RootedNetwork V E X)
        (hN : IsBinaryRootedNetwork N), IsLevelOne N.graph →
        ForGenericParams N fun θ => IsMetricNetwork N θ → ∀ s (hs : s ∈ bcSets N θ),
          ∀ C w, IsCycle (unrooted N hN hX).graph C → IsHybridNodeOf (unrooted N hN hX) C w →
            Determines hN s hs.1 w.1.1 → ∀ x y,
              (A (fun q r => q.taxa = r.taxa ∧ cf N θ q ≤ cf N θ r) s x y ↔
                AdjacentBlocks (unrooted N hN hX) C x y) := by
  refine ⟨adjacencyOf, ?_⟩
  intro V E _ _ N hN h1
  refine (lemma12 hN h1 hX).mono fun θ h12 hθ s hs C w hC hw hdet x y => ?_
  exact lemma16_core hN h1 hX hθ (fun s h4 => by convert h12 hθ s h4) hs hC hw hdet x y

/-- **Theorem 4** (`thm::main`): under the network multispecies coalescent, for generic parameters, the
orderings of the quartet concordance factors identify the semidirected topological network `Ñ` obtained
from `N⁻` by contracting all 2- and 3-cycles and forgetting the directions of the hybrid edges in
4-cycles, while retaining the directions of the hybrid edges of larger cycles. There is a property `G`
of the parameters of each network, which holds for generic parameters, such that two level-1 networks on
the same taxa, with parameters satisfying `G` and the same orderings of concordance factors, have
isomorphic networks `Ñ`.

The proof is the paper's induction on the number of cycles of size at least four of `N₁⁻`
(`tildeDetermined`, `Identify/TildeInduction.lean`), with `G` the conditions `GoodParams`, which hold
for generic parameters (`forGenericParams_goodParams`). Without such a cycle, `Ñ₁` and `Ñ₂` are trees,
the orderings give the quartet trees they display, and these determine the trees (Semple and Steel
2003; `tildeDetermined_zero`). With one cycle `C_v`, Lemmas 15 and 16 give a cycle of `N₂⁻` with the
same blocks, size, order of the blocks and, for size at least five, hybrid block
(`exists_bigCycle_sameData`). When the blocks are single taxa, `Ñ` is that cycle with a taxon at each
node (`tilde_sdIso_of_singletonBlocks`). Otherwise the tree of a block `P_u` of at least two taxa,
read from the network induced on `P_u ∪ {q}` with an outgroup `q`, is joined to the node `u`: `Ñ` is
the gluing at `u` of the networks `Ñ` of the networks induced on `P_u ∪ {q}`, which has no cycle of
size at least four, and on the other taxa with one taxon of `P_u`, which has fewer taxa
(`tildeDetermined_one`, by induction on the number of taxa). With more cycles, following Definition 13,
a leaf of `T`, the tree of cycles of `Ñ`, arises from a cycle `C_v` all of whose `v`-blocks but one,
`S_2`, the block of a node `u`, are 4-network blocks (`exists_leaf_bigCycle`); every other cycle of
size at least four then has the taxa of `S_1 = X ∖ S_2` in one of its blocks. The networks `Ñ` of the
networks induced on `S_1 ∪ {s_2}` and on `S_2 ∪ {s_1}` have fewer cycles of size at least four, and
`Ñ` is obtained by identifying `s_1` in one with `s_2` in the other and suppressing that node
(`tildeDetermined_of_lt`, `tilde_sdIso_glue`, `glue_congr`).

The induced networks `N⁻_{S_i ∪ {s_j}}` (Definition 10) are read as `(N⊕_Y)⁻`, the network `N⁻` of the
induced LSA network on `Y`, as `Q⁻_s` is for quartets (Section 5): the two are isomorphic
(`nonempty_sdIso_inducedUnrooted_unrooted_inducedLSA`, from Proposition 1).
The paper's base case (TeX l.1180) is filled as follows. It reads the quartet tree of `Ñ` on four taxa
from "the ordering of the concordance factors"; the reading that holds is the quartet tree whose
concordance factor differs from the other two, which are equal (exchangeability across the cut edge of
`N` under the edge of `Ñ`), and which need not be the largest (with a `3₂`-cycle, Example 6). The
reading needs the three concordance factors not to be all equal, which with a `3₂`-cycle they can be
(Proposition 7); this holds for generic parameters (`forGenericParams_nonDegenerateCF`) and is part
of `G`, with the statement of Lemma 12 (`GoodParams`).
The paper's claims on the tree of cycles (Definition 13) that `T` is a tree and that a leaf of `T`
arises from a cycle `C_v` exactly when all `v`-blocks but one are 4-network blocks are proved in
`Identify/TreeOfCycles.lean`. -/
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
  refine ⟨fun V E _ _ N θ => GoodParams hX N θ, fun V E _ _ N hN h1 =>
    forGenericParams_goodParams hN h1 hX, ?_⟩
  intro V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord
  exact tildeDetermined _ X hX V₁ E₁ V₂ E₂ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hG₁ hG₂ hord rfl

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
other blocks, a set of four taxa with the Big Cycle property (Lemma 12). The two taxa below `v` come from
the type `3₂` of the cycle, and Proposition 7 (where the concordance factors lie) is not needed. -/
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

/-- No cycle of `G` other than `C` has three taxa of `T` in pairwise distinct blocks. -/
def OnlyCycleSeparatingThree {V' E' X' : Type*} (G : SemidirectedNetwork V' E' X') (C : Set E')
    (T : Finset X') : Prop :=
  ∀ C', IsCycle G.graph C' → C' ≠ C → ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T, x ≠ y → x ≠ z → y ≠ z →
    SameBlock G.graph G.leaf C' x y ∨ SameBlock G.graph G.leaf C' x z ∨
      SameBlock G.graph G.leaf C' y z

/-- **Proposition 13** (`lem::cpto4c`), corrected: let `C_v` be a 4-cycle of `N⁻` and `a, b, c, d` taxa
in distinct `v`-blocks. For generic parameters, if for distinct `i, j, k ∈ {a, b, c, d}` some taxon `e`
makes `{i, j, k, e}` satisfy the Cycle property but not the Big Cycle property, and no cycle of `N⁻`
other than `C_v` has three of `i, j, k, e` in distinct blocks, then `e` is in the `v`-hybrid block.

The paper states this without the last hypothesis, and its proof asserts that the 4-cycle of `Q⁻_abcd`
and the `3₂`-cycle of `Q⁻_abce` "have to have the same hybrid edges, otherwise the level-1 condition
would be violated". The `3₂`-cycle can come from another cycle of `N⁻`, and then the conclusion fails:
`proposition13_asPrinted_false`.

The proof is the paper's. Say `l` is the fourth of `a, b, c, d`. The taxon `e` is not in the block of
`l`, or `i, j, k, e` would be in the four blocks of `C_v`, one of them the hybrid block, and would
satisfy the Big Cycle property (Lemma 12); so `e` is in the block of one of `i, j, k`, say `g`. By
Corollary 4, `Q⁻_ijke` has a `3₂`-cycle, which comes from a cycle of `N⁻` with three of `i, j, k, e` in
distinct blocks: by the added hypothesis, from `C_v`. Its two taxa below the hybrid node are in the
hybrid block of `C_v`, and the only two of `i, j, k, e` in one block are `g` and `e`.
Departure from the paper: the step that the two cycles have the same hybrid edges is replaced by the
added hypothesis, as above; the paper also fixes the order of the cycle by Theorem 4 and the hybrid
node of `{e, j, k, l}` by Lemma 13 before that step, which the corrected argument does not use. -/
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
          OnlyCycleSeparatingThree (unrooted N hN hX) C {i, j, k, e} →
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
    have hsb : ∀ {x y : X}, ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C' x y →
        x ≠ y := fun h h' => h (h' ▸ .refl)
    rcases honly C' hC' hCC' p hp r hr t ht (hsb hpr) (hsb hpt) (hsb hrt) with h | h | h
    · exact hpr h
    · exact hpt h
    · exact hrt h
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
`v`-hybrid block. -/
theorem proposition13_asPrinted_false : ¬ Proposition13AsPrinted :=
  proposition13AsPrinted_counterexample

end Banos2019
