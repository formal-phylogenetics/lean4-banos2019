module

public import Banos2019.Quartet.Conditioning
public import Banos2019.Quartet.Trees
public import Banos2019.Quartet.DisjointNet
public import Phylogenetics.MSC.Basic
public import Phylogenetics.MSC.Small

/-!
# Four-taxon species trees in Lemmas 7 and 9 (Baños 2019, Section 5)

When the root of `Q⊕` is on the cycle, the proofs of Lemmas 7 and 9 condition on the lineages at the
top of the edge above a node `y`. When none of them have coalesced, the remaining process is the
multispecies coalescent on a four-taxon species tree: the lineages are its taxa, on pendant edges,
each of which carries a single lineage and so does not change the process. The trees of the networks
that the lemmas compare have the same unrooted metric tree, and the root placement does not matter
(`pub:rootplace`, Allman, Degnan, Rhodes 2011, Theorem 9 and Proposition 11): species trees with the
same unrooted metric tree have the same distribution of unrooted gene trees
(`External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`). For these steps the
paper cites its Propositions 3 and 4, which as printed state identifiability (see `lemma7`,
`lemma9`).

The trees that occur have at most one nontrivial cluster: `cladeSpeciesTree S`, with the cluster `S`
above an edge of length `ℓ`. They are the star tree (`S = univ`) and the tree `((a,b,c):ℓ,d)`
(`S = univ.erase d`), which on four taxa have the same unrooted metric tree, the star
(`sameUnrootedMetricTree_cladeSpeciesTree`).

* `forestDist_id_of_card_childClusters`, `cladeSpeciesTree_rootedDist_univ`,
  `cladeSpeciesTree_rootedDist_erase`: the gene tree distributions of these species trees.
* `rootDist_rootArc`, `injDist_rootArc`: the network multispecies coalescent with forests injected
  at the root and at the end `w` of an arc `f` from the root that is the only arc into `w`, and
  nothing elsewhere: the forest at `w` goes up `f` by Kingman's coalescent and joins the forest at
  the root.
* `rootDist_liftInj_single`, `cherryMass_liftInj_single`: the single lineage of the only taxon below
  a cut vertex goes up the arc into it unchanged.
* `quartetProb_eq_sum_rootedDist`: the quartet probabilities of a species tree from its rooted gene
  tree distribution; `cherryMass_rootArc_eq_quartetProb_erase`,
  `cherryMass_rootArc_eq_quartetProb_univ`, `cherryMass_atRoot_eq_quartetProb_univ`: the processes
  of Lemmas 7 and 9 are those of `cladeSpeciesTree`, and the masses of the quartet trees are its
  quartet probabilities.
* `quartetProb_cladeSpeciesTree_erase`: the root placement, for these trees.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {X : Type*} [Fintype X]

/-! ### Species trees with one nontrivial cluster -/

section Clade

omit [Fintype X] in
theorem mem_hierarchyOf_singleton [Fintype X] {S A : Finset X} :
    A ∈ hierarchyOf {S} ↔ A = univ ∨ A = S ∨ ∃ x, A = {x} := by
  simp only [hierarchyOf, mem_insert, mem_union, mem_singleton, mem_image, mem_univ, true_and]
  constructor
  · rintro (h | h | ⟨x, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, rfl⟩)
  · rintro (h | h | ⟨x, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, rfl⟩)

/-- The species tree whose only cluster other than `univ` and the singletons is `S`, with an edge of
length `ℓ` above `S` and pendant edges of length `1`. With `S = univ` it is the star tree. -/
def cladeSpeciesTree (S : Finset X) (hS : S.Nonempty) (ℓ : ℝ) (hℓ : 0 < ℓ) : SpeciesTree X where
  clusters := hierarchyOf {S}
  univ_mem := mem_hierarchyOf_singleton.2 (Or.inl rfl)
  singleton_mem x := mem_hierarchyOf_singleton.2 (Or.inr (Or.inr ⟨x, rfl⟩))
  nonempty_of_mem A hA := by
    rcases mem_hierarchyOf_singleton.1 hA with h | h | ⟨x, h⟩
    · rw [h]
      exact hS.mono (subset_univ S)
    · rw [h]
      exact hS
    · rw [h]
      exact singleton_nonempty x
  laminar A hA B hB := by
    rcases mem_hierarchyOf_singleton.1 hA with hA' | hA' | ⟨x, hA'⟩ <;>
      rcases mem_hierarchyOf_singleton.1 hB with hB' | hB' | ⟨y, hB'⟩ <;> subst A <;> subst B
    · exact Or.inl subset_rfl
    · exact Or.inr (Or.inl (subset_univ _))
    · exact Or.inr (Or.inl (subset_univ _))
    · exact Or.inl (subset_univ _)
    · exact Or.inl subset_rfl
    · by_cases hy : y ∈ S
      · exact Or.inr (Or.inl (singleton_subset_iff.2 hy))
      · exact Or.inr (Or.inr (disjoint_singleton_right.2 hy))
    · exact Or.inl (subset_univ _)
    · by_cases hx : x ∈ S
      · exact Or.inl (singleton_subset_iff.2 hx)
      · exact Or.inr (Or.inr (disjoint_singleton_left.2 hx))
    · by_cases hxy : x = y
      · exact Or.inl (by rw [hxy])
      · exact Or.inr (Or.inr (disjoint_singleton.2 hxy))
  length A := if A = S then ℓ else 1
  length_pos A _ _ := by
    split_ifs
    · exact hℓ
    · exact one_pos

theorem cladeSpeciesTree_clusters (S : Finset X) (hS : S.Nonempty) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (cladeSpeciesTree S hS ℓ hℓ).clusters = hierarchyOf {S} := rfl

/-- **A cluster whose children are leaves**: with one lineage per taxon, the forest entering the
population above `A` is that of the singletons of `A`. -/
theorem forestDist_id_of_card_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {A : Finset X} (hch : ∀ B ∈ childClusters H A, #B = 1)
    (G : Finset (Finset X)) :
    forestDist H len id A G = populationKernel len A (A.image fun x => {x}) G := by
  rw [forestDist]
  let f₀ : childClusters H A → Finset (Finset X) := fun B => B.1.image fun x => {x}
  have hval : ∀ (B : childClusters H A) (F : Finset (Finset X)),
      forestDist H len id B.1 F = if F = f₀ B then 1 else 0 := by
    intro B F
    obtain ⟨x, hx⟩ := card_eq_one.1 (hch B.1 B.2)
    have hf : f₀ B = {{x}} := by
      change B.1.image (fun x => ({x} : Finset X)) = _
      rw [hx, image_singleton]
    rw [hf, hx]
    exact forestDist_id_singleton hH len x F
  rw [Fintype.sum_eq_single f₀]
  · rw [prod_eq_one fun B _ => by rw [hval, ite_eq_left rfl], one_mul, sampledForest_id]
    congr 1
    refine union_eq_right.2 fun C hC => ?_
    obtain ⟨B, -, hCB⟩ := mem_sup.1 hC
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hCB
    exact mem_image_of_mem _ ((mem_childClusters.1 B.2).2.1.subset hx)
  · intro f hf
    obtain ⟨B, hB⟩ : ∃ B, f B ≠ f₀ B := by
      by_contra h
      push Not at h
      exact hf (funext h)
    rw [prod_eq_zero (mem_univ B) (by rw [hval, ite_eq_right hB]), zero_mul]

/-- **The star tree**: the four lineages enter the population above the root together. -/
theorem cladeSpeciesTree_rootedDist_univ (hU : (univ : Finset X).Nonempty) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (G : Finset (Finset X)) :
    (cladeSpeciesTree univ hU ℓ hℓ).rootedDist id G =
      kingmanAbsorption (univ.image fun x => {x}) G := by
  unfold SpeciesTree.rootedDist
  rw [forestDist_id_of_card_childClusters (cladeSpeciesTree univ hU ℓ hℓ).isHierarchy _
    (fun B hB => ?_), populationKernel, ite_eq_left rfl]
  obtain ⟨hB, hBu, -⟩ := mem_childClusters.1 hB
  rcases mem_hierarchyOf_singleton.1 hB with h | h | ⟨x, h⟩
  · exact absurd (h ▸ hBu) (ssubset_irrefl _)
  · exact absurd (h ▸ hBu) (ssubset_irrefl _)
  · rw [h, card_singleton]

/-- **The tree `((a,b,c):ℓ,d)`**: the three lineages of `univ.erase d` coalesce along the edge of
length `ℓ`, and then join the lineage of `d` above the root. -/
theorem cladeSpeciesTree_rootedDist_erase (hX : 3 ≤ Fintype.card X) (d : X)
    (hS : (univ.erase d).Nonempty) (ℓ : ℝ) (hℓ : 0 < ℓ) (G : Finset (Finset X)) :
    (cladeSpeciesTree (univ.erase d) hS ℓ hℓ).rootedDist id G =
      ∑ s, kingmanTransition ℓ ((univ.erase d).image fun x => {x}) s *
        kingmanAbsorption ({{d}} ∪ s) G := by
  have hdS : d ∉ univ.erase d := notMem_erase d univ
  have hS2 : 2 ≤ #(univ.erase d) := by
    rw [card_erase_of_mem (mem_univ d), card_univ]
    omega
  have hSu : univ.erase d ≠ univ := fun h => hdS (by rw [h]; exact mem_univ d)
  have hSd : univ.erase d ≠ {d} := fun h => hdS (h ▸ mem_singleton_self d)
  have hdu : ({d} : Finset X) ≠ univ := fun h => by
    have := card_univ (α := X)
    rw [← h, card_singleton] at this
    omega
  have hSmem : univ.erase d ∈ hierarchyOf {univ.erase d} :=
    mem_hierarchyOf_singleton.2 (Or.inr (Or.inl rfl))
  have hch : childClusters (cladeSpeciesTree (univ.erase d) hS ℓ hℓ).clusters univ =
      {univ.erase d, {d}} := by
    rw [cladeSpeciesTree_clusters]
    ext B
    rw [mem_childClusters, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hB, hBu, hmax⟩
      rcases mem_hierarchyOf_singleton.1 hB with h | h | ⟨x, h⟩
      · exact absurd (h ▸ hBu) (ssubset_irrefl _)
      · exact Or.inl h
      · by_cases hx : x = d
        · exact Or.inr (by rw [h, hx])
        · refine absurd (ssubset_univ_iff.2 hSu) (hmax _ hSmem ?_)
          rw [h]
          refine Finset.ssubset_iff_subset_ne.2
            ⟨singleton_subset_iff.2 (mem_erase.2 ⟨hx, mem_univ x⟩),
            fun h' => ?_⟩
          rw [← h', card_singleton] at hS2
          omega
    · rintro (rfl | rfl)
      · refine ⟨hSmem, ssubset_univ_iff.2 hSu, fun C hC hSC hCu => ?_⟩
        rcases mem_hierarchyOf_singleton.1 hC with h | h | ⟨x, h⟩
        · exact ssubset_irrefl _ (h ▸ hCu)
        · exact ssubset_irrefl _ (h ▸ hSC)
        · have := card_lt_card hSC
          rw [h, card_singleton] at this
          omega
      · refine ⟨mem_hierarchyOf_singleton.2 (Or.inr (Or.inr ⟨d, rfl⟩)), ssubset_univ_iff.2 hdu,
          fun C hC hdC hCu => ?_⟩
        rcases mem_hierarchyOf_singleton.1 hC with h | h | ⟨x, h⟩
        · exact ssubset_irrefl _ (h ▸ hCu)
        · exact hdS (h ▸ hdC.subset (mem_singleton_self d))
        · have := card_lt_card hdC
          rw [h, card_singleton, card_singleton] at this
          omega
  have hSF : ∀ F, forestDist (cladeSpeciesTree (univ.erase d) hS ℓ hℓ).clusters
      (cladeSpeciesTree (univ.erase d) hS ℓ hℓ).length id (univ.erase d) F =
        kingmanTransition ℓ ((univ.erase d).image fun x => {x}) F := by
    intro F
    rw [forestDist_id_of_card_childClusters (cladeSpeciesTree (univ.erase d) hS ℓ hℓ).isHierarchy _
      (fun B hB => ?_), populationKernel, ite_eq_right hSu]
    · change kingmanTransition (if univ.erase d = univ.erase d then ℓ else 1) _ F = _
      rw [ite_eq_left rfl]
    · obtain ⟨hB, hBS, -⟩ := mem_childClusters.1 hB
      rcases mem_hierarchyOf_singleton.1 hB with h | h | ⟨x, h⟩
      · rw [h] at hBS
        exact absurd (hBS.subset (mem_univ d)) hdS
      · exact absurd (h ▸ hBS) (ssubset_irrefl _)
      · rw [h, card_singleton]
  unfold SpeciesTree.rootedDist
  rw [forestDist_of_childClusters_eq_pair hch hSd]
  simp only [hSF, forestDist_id_singleton (cladeSpeciesTree (univ.erase d) hS ℓ hℓ).isHierarchy,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true,
    populationKernel]
  refine sum_congr rfl fun s _ => ?_
  by_cases h0 : kingmanTransition ℓ ((univ.erase d).image fun x => {x}) s = 0
  · rw [h0, zero_mul, zero_mul]
  congr 2
  obtain ⟨-, hsub, -⟩ := kingmanTransition_support_good (isGoodForest_singletons _) h0
  rw [sampledForest_id]
  ext C
  simp only [mem_union, mem_singleton, mem_image, mem_univ, true_and]
  constructor
  · rintro ((h | h) | ⟨x, rfl⟩)
    · exact Or.inr h
    · exact Or.inl h
    · by_cases hx : x = d
      · exact Or.inl (by rw [hx])
      · exact Or.inr (hsub (mem_image.2 ⟨x, mem_erase.2 ⟨hx, mem_univ x⟩, rfl⟩))
  · rintro (h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)

/-- On four taxa, the sides of the splits of the unrooted star tree are the singletons and their
complements. -/
theorem mem_unroot_cladeSpeciesTree_univ (hX : Fintype.card X = 4) (hU : (univ : Finset X).Nonempty)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (A : Finset X) :
    A ∈ unroot (cladeSpeciesTree univ hU ℓ hℓ).clusters ↔ (∃ x, A = {x}) ∨ ∃ x, Aᶜ = {x} := by
  have hsu : ∀ x : X, ({x} : Finset X) ≠ univ := fun x h => by
    have := card_univ (α := X)
    rw [← h, card_singleton] at this
    omega
  rw [cladeSpeciesTree_clusters, mem_unroot, mem_hierarchyOf_singleton, mem_hierarchyOf_singleton]
  constructor
  · rintro (⟨h | h | h, hne⟩ | ⟨h | h | h, hne⟩)
    · exact absurd h hne
    · exact absurd h hne
    · exact Or.inl h
    · exact absurd h hne
    · exact absurd h hne
    · exact Or.inr h
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact Or.inl ⟨Or.inr (Or.inr ⟨x, hx⟩), hx ▸ hsu x⟩
    · exact Or.inr ⟨Or.inr (Or.inr ⟨x, hx⟩), hx ▸ hsu x⟩

/-- On four taxa, the sides of the splits of the unrooted tree of `((a,b,c):ℓ,d)` are those of the
star tree. -/
theorem mem_unroot_cladeSpeciesTree_erase (hX : Fintype.card X = 4) (d : X)
    (hS : (univ.erase d).Nonempty) (ℓ : ℝ) (hℓ : 0 < ℓ) (A : Finset X) :
    A ∈ unroot (cladeSpeciesTree (univ.erase d) hS ℓ hℓ).clusters ↔
      (∃ x, A = {x}) ∨ ∃ x, Aᶜ = {x} := by
  have hsu : ∀ x : X, ({x} : Finset X) ≠ univ := fun x h => by
    have := card_univ (α := X)
    rw [← h, card_singleton] at this
    omega
  have hcu : ∀ x : X, ({x}ᶜ : Finset X) ≠ univ := fun x h =>
    (singleton_nonempty x).ne_empty ((compl_eq_univ_iff _).1 h)
  rw [cladeSpeciesTree_clusters, mem_unroot, mem_hierarchyOf_singleton, mem_hierarchyOf_singleton,
    ← compl_singleton]
  constructor
  · rintro (⟨h | h | h, hne⟩ | ⟨h | h | h, hne⟩)
    · exact absurd h hne
    · exact Or.inr ⟨d, by rw [h, compl_compl]⟩
    · exact Or.inl h
    · exact absurd h hne
    · exact Or.inl ⟨d, by rw [← compl_compl A, h, compl_compl]⟩
    · exact Or.inr h
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact Or.inl ⟨Or.inr (Or.inr ⟨x, hx⟩), hx ▸ hsu x⟩
    · exact Or.inr ⟨Or.inr (Or.inr ⟨x, hx⟩), hx ▸ hsu x⟩

/-- **On four taxa, `((a,b,c):ℓ,d)` and the star tree have the same unrooted metric tree**: the
star, without internal edges. -/
theorem sameUnrootedMetricTree_cladeSpeciesTree (hX : Fintype.card X = 4) (d : X)
    (hS : (univ.erase d).Nonempty) (ℓ : ℝ) (hℓ : 0 < ℓ) (hU : (univ : Finset X).Nonempty) (ℓ' : ℝ)
    (hℓ' : 0 < ℓ') :
    (cladeSpeciesTree (univ.erase d) hS ℓ hℓ).SameUnrootedMetricTree
      (cladeSpeciesTree univ hU ℓ' hℓ') := by
  refine ⟨?_, fun A hA h2 h2' => ?_⟩
  · ext A
    rw [mem_unroot_cladeSpeciesTree_erase hX, mem_unroot_cladeSpeciesTree_univ hX]
  · exfalso
    rcases (mem_unroot_cladeSpeciesTree_erase hX d hS ℓ hℓ A).1 hA with ⟨x, hx⟩ | ⟨x, hx⟩
    · rw [hx, card_singleton] at h2
      omega
    · rw [hx, card_singleton] at h2'
      omega

/-- The probability that the unrooted gene tree displays `q` is the mass of the rooted gene trees
that display it. -/
theorem quartetProb_eq_sum_rootedDist (σ : SpeciesTree X) (q : QuartetTree X) :
    External.AllmanDegnanRhodes2011.quartetProb σ q =
      ∑ G, if Displays (unroot G) q then σ.rootedDist id G else 0 := by
  unfold External.AllmanDegnanRhodes2011.quartetProb SpeciesTree.unrootedDist
  have h : ∀ T : Finset (Finset X),
      (if Displays T q then ∑ G, (if unroot G = T then σ.rootedDist id G else 0) else 0) =
        ∑ G, if unroot G = T then (if Displays (unroot G) q then σ.rootedDist id G else 0)
          else 0 := by
    intro T
    by_cases hT : Displays T q
    · rw [ite_eq_left hT]
      refine sum_congr rfl fun G _ => ?_
      by_cases hG : unroot G = T
      · rw [ite_eq_left hG, ite_eq_left hG, ite_eq_left (hG ▸ hT)]
      · rw [ite_eq_right hG, ite_eq_right hG]
    · rw [ite_eq_right hT]
      refine (sum_eq_zero fun G _ => ?_).symm
      by_cases hG : unroot G = T
      · rw [ite_eq_left hG, ite_eq_right (hG ▸ hT)]
      · rw [ite_eq_right hG]
  rw [sum_congr rfl fun T _ => h T, sum_comm]
  refine sum_congr rfl fun G _ => ?_
  rw [sum_ite_eq, ite_eq_left (mem_univ _)]

/-- **The root placement does not matter** (`pub:rootplace`, for these trees): on four taxa,
`((a,b,c):ℓ,d)` and the star tree give each quartet tree the same probability, as they have the same
unrooted metric tree (`External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree`).
-/
theorem quartetProb_cladeSpeciesTree_erase (hX : Fintype.card X = 4) (d : X)
    (hS : (univ.erase d).Nonempty) (ℓ : ℝ) (hℓ : 0 < ℓ) (hU : (univ : Finset X).Nonempty) (ℓ' : ℝ)
    (hℓ' : 0 < ℓ') (q : QuartetTree X) :
    External.AllmanDegnanRhodes2011.quartetProb (cladeSpeciesTree (univ.erase d) hS ℓ hℓ) q =
      External.AllmanDegnanRhodes2011.quartetProb (cladeSpeciesTree univ hU ℓ' hℓ') q := by
  unfold External.AllmanDegnanRhodes2011.quartetProb
  rw [External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree hX
    (sameUnrootedMetricTree_cladeSpeciesTree hX d hS ℓ hℓ hU ℓ' hℓ')]

end Clade

/-! ### The network process with forests at the root and below one arc from it -/

section RootArc

variable {V' E' : Type*} [Fintype V'] [Fintype E'] {M : RootedNetwork V' E' X}

/-- **Forests at the root and at the end `w` of an arc `f` from the root**, `f` the only arc into
`w`, and nothing elsewhere: the forest at `w` goes up `f` by Kingman's coalescent and joins the
forest at the root. -/
theorem rootDist_rootArc (hacyc : ∀ v, ¬ Relation.TransGen M.graph.Adj v v)
    (hroot : ∀ e, M.graph.target e ≠ M.root) {f : E'} (hfs : M.graph.source f = M.root)
    (huniq : ∀ e, M.graph.target e = M.graph.target f → e = f) {θ : MetricData E'}
    (h1 : θ.inheritance f = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) {inj : V' → Finset (Finset X)}
    (hinj : ∀ u, u ≠ M.root → u ≠ M.graph.target f → inj u = ∅) (F : Finset (Finset X)) :
    rootDist M θ ρ inj F = ∑ s, kingmanTransition (θ.length f) (inj (M.graph.target f)) s *
      if inj M.root ∪ s = F then 1 else 0 := by
  have hw : M.graph.target f ≠ M.root := hroot f
  have hsf : ∀ e, M.graph.source e ≠ M.root → e ≠ f := fun e he h => he (h ▸ hfs)
  -- on a history of nonzero weight, only `f` carries a forest, that of `w`
  have hsupp : ∀ b t : E' → Finset (Finset X), injWeight M θ ρ inj b t ≠ 0 →
      (∀ e, e ≠ f → b e = ∅ ∧ t e = ∅) ∧ b f = inj (M.graph.target f) := by
    intro b t h
    let rel : V' → V' → Prop := fun a c => Relation.TransGen M.graph.Adj c a
    have : IsTrans V' rel := ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
    have : Std.Irrefl rel := ⟨fun a ha => hacyc a ha⟩
    have hwf : WellFounded rel := Finite.wellFounded_of_trans_of_irrefl rel
    have hall : ∀ x, ∀ e, M.graph.target e = x → e ≠ f → b e = ∅ ∧ t e = ∅ := by
      intro x
      induction x using hwf.induction with
      | _ x ih =>
        intro e he hef
        have hx : x ≠ M.root := he ▸ hroot e
        have hxw : x ≠ M.graph.target f := fun h' => hef (huniq e (he.trans h'))
        have hv : vertexWeight M θ ρ inj x b t ≠ 0 :=
          prod_ne_zero_iff.1 h x (mem_erase.2 ⟨hx, mem_univ _⟩)
        have harr : arriving M inj t x = ∅ := by
          unfold arriving
          rw [hinj x hx hxw, empty_union]
          refine eq_empty_of_forall_notMem fun A hA => ?_
          obtain ⟨e', he', hAe'⟩ := mem_biUnion.1 hA
          have he's := (mem_filter.1 he').2
          rw [(ih (M.graph.target e') (.single ⟨e', he's, rfl⟩) e' rfl
            (hsf e' (he's ▸ hx))).2] at hAe'
          exact notMem_empty _ hAe'
        unfold vertexWeight at hv
        rw [harr] at hv
        have hb : b e = ∅ :=
          eq_empty_of_allocationFactor_empty_ne_zero M (left_ne_zero_of_mul hv) he
        have hk : kingmanTransition (θ.length e) (b e) (t e) ≠ 0 :=
          prod_ne_zero_iff.1 (right_ne_zero_of_mul hv) e (mem_arcsInto.2 he)
        rw [hb, kingmanTransition_of_card_roots_le_one isForest_empty (by simp)] at hk
        exact ⟨hb, (ite_ne_right_iff.1 hk).1⟩
    refine ⟨fun e hef => hall _ e rfl hef, ?_⟩
    have hv : vertexWeight M θ ρ inj (M.graph.target f) b t ≠ 0 :=
      prod_ne_zero_iff.1 h _ (mem_erase.2 ⟨hw, mem_univ _⟩)
    have harr : arriving M inj t (M.graph.target f) = inj (M.graph.target f) := by
      unfold arriving
      refine union_eq_left.2 fun A hA => ?_
      obtain ⟨e', he', hAe'⟩ := mem_biUnion.1 hA
      have he's := (mem_filter.1 he').2
      rw [(hall _ e' rfl (hsf e' (he's ▸ hw))).2] at hAe'
      exact absurd hAe' (notMem_empty _)
    unfold vertexWeight at hv
    rw [harr, allocationFactor_of_unique_arc hρ rfl huniq h1] at hv
    exact (ite_ne_right_iff.1 (left_ne_zero_of_mul hv)).1
  -- the histories of nonzero weight
  let B₀ : E' → Finset (Finset X) := fun e => if e = f then inj (M.graph.target f) else ∅
  let T : Finset (Finset X) → E' → Finset (Finset X) := fun s e => if e = f then s else ∅
  have hW : ∀ s, injWeight M θ ρ inj B₀ (T s) =
      kingmanTransition (θ.length f) (inj (M.graph.target f)) s := by
    intro s
    unfold injWeight
    rw [← mul_prod_erase _ _ (mem_erase.2 ⟨hw, mem_univ _⟩)]
    have hrest : ∏ u ∈ (univ.erase M.root).erase (M.graph.target f),
        vertexWeight M θ ρ inj u B₀ (T s) = 1 := by
      refine prod_eq_one fun u hu => ?_
      have huw : u ≠ M.graph.target f := ne_of_mem_erase hu
      have hur : u ≠ M.root := ne_of_mem_erase (mem_of_mem_erase hu)
      have hne : ∀ e, M.graph.target e = u → e ≠ f := fun e he h' => huw (by rw [← he, h'])
      unfold vertexWeight
      have harr : arriving M inj (T s) u = ∅ := by
        unfold arriving
        rw [hinj u hur huw, empty_union]
        refine eq_empty_of_forall_notMem fun A hA => ?_
        obtain ⟨e', he', hAe'⟩ := mem_biUnion.1 hA
        have he'f : e' ≠ f := hsf e' ((mem_filter.1 he').2 ▸ hur)
        simp [T, he'f] at hAe'
      rw [harr, allocationFactor_empty_eq_one fun e he => by simp [B₀, hne e he], one_mul]
      refine prod_eq_one fun e he => ?_
      have hef := hne e (mem_arcsInto.1 he)
      simp only [B₀, T, ite_eq_right hef]
      rw [kingmanTransition_of_card_roots_le_one isForest_empty (by simp), ite_eq_left rfl]
    rw [hrest, mul_one]
    unfold vertexWeight
    have harr : arriving M inj (T s) (M.graph.target f) = inj (M.graph.target f) := by
      unfold arriving
      refine union_eq_left.2 fun A hA => ?_
      obtain ⟨e', he', hAe'⟩ := mem_biUnion.1 hA
      have he'f : e' ≠ f := hsf e' ((mem_filter.1 he').2 ▸ hw)
      simp [T, he'f] at hAe'
    have harcs : arcsInto M (M.graph.target f) = {f} := by
      ext e
      rw [mem_arcsInto, mem_singleton]
      exact ⟨huniq e, fun h => h ▸ rfl⟩
    rw [harr, allocationFactor_of_unique_arc hρ rfl huniq h1, harcs, prod_singleton]
    simp [B₀, T]
  have harrR : ∀ s, arriving M inj (T s) M.root = inj M.root ∪ s := by
    intro s
    unfold arriving
    congr 1
    ext A
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨e, he, hA⟩
      by_cases hef : e = f
      · simpa [T, hef] using hA
      · simp [T, hef] at hA
    · intro hA
      exact ⟨f, hfs, by simpa [T] using hA⟩
  have hT : Function.Injective T := fun s s' h => by simpa [T] using congrFun h f
  unfold rootDist
  rw [Finset.sum_eq_single B₀]
  · have hsub : ∑ top, injWeight M θ ρ inj B₀ top *
        (if arriving M inj top M.root = F then 1 else 0) =
        ∑ top ∈ univ.image T, injWeight M θ ρ inj B₀ top *
          (if arriving M inj top M.root = F then 1 else 0) := by
      refine (sum_subset (subset_univ _) fun top _ htop => ?_).symm
      by_contra hne
      obtain ⟨h₁, -⟩ := hsupp B₀ top (left_ne_zero_of_mul hne)
      refine htop (mem_image.2 ⟨top f, mem_univ _, funext fun e => ?_⟩)
      by_cases hef : e = f
      · simp [T, hef]
      · simp [T, hef, (h₁ e hef).2]
    rw [hsub, sum_image fun s _ s' _ h => hT h]
    exact sum_congr rfl fun s _ => by rw [hW s, harrR s]
  · intro b _ hb
    refine sum_eq_zero fun top _ => ?_
    by_contra hne
    obtain ⟨h₁, h₂⟩ := hsupp b top (left_ne_zero_of_mul hne)
    refine hb (funext fun e => ?_)
    by_cases hef : e = f
    · simp [B₀, hef, ← h₂]
    · simp [B₀, hef, (h₁ e hef).1]
  · simp

/-- **Forests at the root and below one arc from it**, for the distribution above the root. -/
theorem injDist_rootArc (hacyc : ∀ v, ¬ Relation.TransGen M.graph.Adj v v)
    (hroot : ∀ e, M.graph.target e ≠ M.root) {f : E'} (hfs : M.graph.source f = M.root)
    (huniq : ∀ e, M.graph.target e = M.graph.target f → e = f) {θ : MetricData E'}
    (h1 : θ.inheritance f = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) {inj : V' → Finset (Finset X)}
    (hinj : ∀ u, u ≠ M.root → u ≠ M.graph.target f → inj u = ∅) (G : Finset (Finset X)) :
    injDist M θ ρ inj G = ∑ s, kingmanTransition (θ.length f) (inj (M.graph.target f)) s *
      kingmanAbsorption (inj M.root ∪ s) G := by
  rw [injDist_eq_sum_rootDist]
  simp only [rootDist_rootArc hacyc hroot hfs huniq h1 hρ hinj, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  simp only [mul_assoc, ite_mul, one_mul, zero_mul]
  rw [← mul_sum, sum_ite_eq, ite_eq_left (mem_univ _)]

/-- **The process of the tree `((a,b,c):ℓ,d)`**: the three singletons of `univ.erase d` at the end
of an arc `f` from the root and the singleton of `d` at the root. -/
theorem cherryMass_rootArc_eq_quartetProb_erase (hX : Fintype.card X = 4)
    (hacyc : ∀ v, ¬ Relation.TransGen M.graph.Adj v v) (hroot : ∀ e, M.graph.target e ≠ M.root)
    {f : E'} (hfs : M.graph.source f = M.root)
    (huniq : ∀ e, M.graph.target e = M.graph.target f → e = f) {θ : MetricData E'}
    (h1 : θ.inheritance f = 1) (hℓ : 0 < θ.length f) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {inj : V' → Finset (Finset X)} (hinj : ∀ u, u ≠ M.root → u ≠ M.graph.target f → inj u = ∅)
    {d : X} (hS : (univ.erase d).Nonempty)
    (hw : inj (M.graph.target f) = (univ.erase d).image fun x => {x}) (hr : inj M.root = {{d}})
    (q : QuartetTree X) :
    cherryMass M θ ρ inj q = External.AllmanDegnanRhodes2011.quartetProb
      (cladeSpeciesTree (univ.erase d) hS (θ.length f) hℓ) q := by
  rw [← sum_displays_injDist hX, quartetProb_eq_sum_rootedDist]
  refine sum_congr rfl fun G _ => ?_
  rw [injDist_rootArc hacyc hroot hfs huniq h1 hρ hinj, hw, hr,
    cladeSpeciesTree_rootedDist_erase (by omega)]

/-- **The process of the star tree**: the four singletons at the end of an arc `f` from the root,
and nothing at the root. -/
theorem cherryMass_rootArc_eq_quartetProb_univ (hX : Fintype.card X = 4)
    (hacyc : ∀ v, ¬ Relation.TransGen M.graph.Adj v v) (hroot : ∀ e, M.graph.target e ≠ M.root)
    {f : E'} (hfs : M.graph.source f = M.root)
    (huniq : ∀ e, M.graph.target e = M.graph.target f → e = f) {θ : MetricData E'}
    (h1 : θ.inheritance f = 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {inj : V' → Finset (Finset X)} (hinj : ∀ u, u ≠ M.root → u ≠ M.graph.target f → inj u = ∅)
    (hU : (univ : Finset X).Nonempty) (hw : inj (M.graph.target f) = univ.image fun x => {x})
    (hr : inj M.root = ∅) (q : QuartetTree X) :
    cherryMass M θ ρ inj q = External.AllmanDegnanRhodes2011.quartetProb
      (cladeSpeciesTree univ hU 1 one_pos) q := by
  rw [← sum_displays_injDist hX, quartetProb_eq_sum_rootedDist]
  refine sum_congr rfl fun G _ => ?_
  rw [injDist_rootArc hacyc hroot hfs huniq h1 hρ hinj, hw, hr, cladeSpeciesTree_rootedDist_univ]
  simp only [empty_union]
  rw [kingmanTransition_mul_kingmanAbsorption (isGoodForest_singletons _).1]

/-- **The process of the star tree**: the four singletons at the root. -/
theorem cherryMass_atRoot_eq_quartetProb_univ (hX : Fintype.card X = 4)
    (hacyc : ∀ v, ¬ Relation.TransGen M.graph.Adj v v) (hroot : ∀ e, M.graph.target e ≠ M.root)
    (θ : MetricData E') (ρ : ℝ) (hU : (univ : Finset X).Nonempty) (q : QuartetTree X) :
    cherryMass M θ ρ (atRoot M (univ.image fun x => {x})) q =
      External.AllmanDegnanRhodes2011.quartetProb (cladeSpeciesTree univ hU 1 one_pos) q := by
  rw [← sum_displays_injDist hX, quartetProb_eq_sum_rootedDist]
  refine sum_congr rfl fun G _ => ?_
  rw [injDist_eq_sum_rootDist, cladeSpeciesTree_rootedDist_univ]
  simp only [rootDist_atRoot hacyc hroot, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
    ite_true]

end RootArc

/-! ### A single lineage below a cut vertex -/

section Single

variable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}

/-- **The single lineage of the only taxon `d` below a cut vertex `r`** goes up the arc `c` into `r`
unchanged: the process is that with `{{d}}` at the source of `c` and nothing below `c`. -/
theorem rootDist_liftInj_single (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ)
    {r : V} (hc : IsCut N r) {c : E} (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) {d : X}
    (hd : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = d) {inj : V → Finset (Finset X)}
    (hinj : ∀ u, N.graph.Reaches r u → inj u = taxaInj N univ u) (F : Finset (Finset X)) :
    rootDist N θ 0 inj F = rootDist N θ 0 (liftInj N c inj {{d}}) F := by
  have h1 : θ.inheritance c = 1 := hθ.2.2.1 c (isTreeArc_of_unique hcr huniq)
  rw [rootDist_eq_sum_arc hN hc hcr huniq h1 le_rfl inj F]
  have hlow : lowerInj (cutVertices N r) inj = lowerInj (cutVertices N r) (taxaInj N univ) := by
    funext u
    unfold lowerInj
    rw [cutVertices_inr]
    exact hinj u.1 u.2
  have hlaw : ∀ t, arcLaw N r hc θ 0 c inj t = if t = {{d}} then 1 else 0 := by
    intro t
    unfold arcLaw
    rw [hlow]
    simp only [rootDist_cutLower_of_one hN hc hθ hd, ite_mul, one_mul, zero_mul, sum_ite_eq',
      mem_univ, ite_true, kingmanTransition_singleton]
  simp only [hlaw, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

/-- **The single lineage of the only taxon below a cut vertex**, for the mass of a quartet tree. -/
theorem cherryMass_liftInj_single (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ)
    {r : V} (hc : IsCut N r) {c : E} (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) {d : X}
    (hd : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = d) {inj : V → Finset (Finset X)}
    (hinj : ∀ u, N.graph.Reaches r u → inj u = taxaInj N univ u) (q : QuartetTree X) :
    cherryMass N θ 0 inj q = cherryMass N θ 0 (liftInj N c inj {{d}}) q := by
  unfold cherryMass
  simp only [injDist_eq_sum_rootDist, rootDist_liftInj_single hN hθ hc hcr huniq hd hinj]

end Single

end Banos2019
