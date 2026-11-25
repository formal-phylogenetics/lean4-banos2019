module

public import Banos2019.Identify.TildeDefs

/-!
# The networks induced on a set of taxa (Baños 2019, proof of Theorem 4)

The induction step of Theorem 4 applies the induction hypothesis to the networks `N⁻_{S_i ∪ {s_j}}`
induced on sets of taxa. As for quartets (Section 5, `quartetUnrooted`), the induced network on `Y` is
taken as `(N⊕_Y)⁻`, the unrooted network of the induced LSA network `N⊕_Y` (`inducedLSA`), which is a
binary rooted network on the taxa of `Y`. Its concordance factors are those of `N` on `Y` (Theorem 2),
its cycles are those that the cycles of `N⁻` induce on `Y`, and the conditions of Theorem 4 pass to it.

* `inducedLSA_isLevelOne`, `inducedLSA_isMetricNetwork`, `cf_inducedLSA`.
* `goodParams_inducedLSA`, `sameOrdering_inducedLSA`.
* `bigCycleCount_inducedLSA_le`: the cycles of size at least four of `(N⊕_Y)⁻` come from distinct
  cycles of size at least four of `N⁻` separating sets of four taxa of `Y`.

The concordance factors are compared through the four taxa of a quartet tree:

* `nmscCF_iso`: concordance factors are invariant under an isomorphism of networks with their
  parameters, along a bijection of the taxa.
* `nmscCF_belowNetwork_of_superset`: below a stable ancestor of `Y`, a quartet tree on `Y` has the
  concordance factor it has in `N`. The library's theorem for four taxa (`NMSC.nmscCF_belowNetwork`)
  applies to `N` and to the part of `N` below the stable ancestor, whose parts below the four taxa
  are isomorphic.

The cycles are compared as in `Banos2019.Identify.QuartetCycles` for four taxa:

* `inducedNode_blockNode`: for a cycle of `(N⊕_Y)⁻` and the cycle of `N⁻` with the same hybrid node,
  a taxon of `Y` is in the block of the same node of `N` in both.
* `exists_unrooted_cycle_of_induced`, `exists_induced_cycle_of_unrooted`: a cycle of `(N⊕_Y)⁻` comes
  from the cycle of `N⁻` with the same hybrid node, and a cycle of `N⁻` whose hybrid node is above a
  taxon of `Y` and not above another induces a cycle of `(N⊕_Y)⁻`.
* `separatesQuartet_induced_iff`, `exists_separatesQuartet_induced_iff`: the sets of four taxa of `Y`
  separated by a cycle of `(N⊕_Y)⁻` are those separated by the cycle of `N⁻` with the same hybrid
  node.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-! ### Concordance factors along an isomorphism -/

section CFIso

variable {V₁ E₁ X₁ V₂ E₂ X₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype V₂] [Fintype E₂] [Fintype X₂] [DecidableEq X₂]
  {N₁ : RootedNetwork V₁ E₁ X₁} {N₂ : RootedNetwork V₂ E₂ X₂}
  {θ₁ : MetricData E₁} {θ₂ : MetricData E₂} {ρ : ℝ}
  {eV : V₁ ≃ V₂} {eE : E₁ ≃ E₂} {eX : X₁ ≃ X₂}

/-- The forests on the arcs of a network carried along bijections of the arcs and of the taxa. -/
def isoForests (eE : E₁ ≃ E₂) (eX : X₁ ≃ X₂) (t : E₁ → Finset (Finset X₁)) :
    E₂ → Finset (Finset X₂) :=
  fun e => relabelFamily eX (t (eE.symm e))

omit [Fintype V₁] [Fintype V₂] in
/-- The forest arriving at a vertex, carried along an isomorphism. -/
theorem arrivingForest_iso (hs : ∀ e, N₂.graph.source (eE e) = eV (N₁.graph.source e))
    (hl : ∀ x, N₂.leaf (eX x) = eV (N₁.leaf x)) (top : E₁ → Finset (Finset X₁)) (v : V₁) :
    arrivingForest N₂ (isoForests eE eX top) (eV v) =
      relabelFamily eX (arrivingForest N₁ top v) := by
  unfold arrivingForest
  rw [relabelFamily_union, relabelFamily_biUnion]
  congr 1
  · ext B
    simp only [mem_image, mem_filter, mem_univ, true_and, relabelFamily]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨{eX.symm x}, ⟨eX.symm x, ?_, rfl⟩, by simp⟩
      apply eV.injective
      rw [← hl, Equiv.apply_symm_apply, hx]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨eX x, by rw [hl, hx], by simp⟩
  · ext B
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, isoForests]
    constructor
    · rintro ⟨e, he, hB⟩
      refine ⟨eE.symm e, ?_, hB⟩
      apply eV.injective
      rw [← hs, Equiv.apply_symm_apply, he]
    · rintro ⟨e, he, hB⟩
      exact ⟨eE e, by rw [hs, he], by simpa using hB⟩

omit [Fintype V₁] [Fintype V₂] in
/-- The allocation at a vertex, carried along an isomorphism. -/
theorem allocationFactor_iso (ht : ∀ e, N₂.graph.target (eE e) = eV (N₁.graph.target e))
    (hθi : ∀ e, θ₂.inheritance (eE e) = θ₁.inheritance e) (F : Finset (Finset X₁)) (v : V₁)
    (bot : E₁ → Finset (Finset X₁)) :
    allocationFactor N₁ θ₁ ρ F v bot =
      allocationFactor N₂ θ₂ ρ (relabelFamily eX F) (eV v) (isoForests eE eX bot) := by
  have hσ : ∀ e : E₂, N₂.graph.target e = eV v ↔ N₁.graph.target (eE.symm e) = v := fun e => by
    rw [← eV.injective.eq_iff, ← ht, Equiv.apply_symm_apply]
  let σ : {e // N₂.graph.target e = eV v} ≃ {e // N₁.graph.target e = v} :=
    eE.symm.subtypeEquiv hσ
  have hτ : ∀ A : Finset X₂, A ∈ roots (relabelFamily eX F) ↔
      (Equiv.finsetCongr eX).symm A ∈ roots F := fun A => by
    rw [roots_relabelFamily, mem_relabelFamily]
    rfl
  let τ : {A // A ∈ roots (relabelFamily eX F)} ≃ {A // A ∈ roots F} :=
    (Equiv.finsetCongr eX).symm.subtypeEquiv hτ
  refine NMSC.allocationFactor_eq_of_equiv σ τ (fun e => ?_) fun a e => ?_
  · show θ₂.inheritance e.1 = θ₁.inheritance (eE.symm e.1)
    rw [← hθi, Equiv.apply_symm_apply]
  · have himg : ((univ.filter fun r => a r = e).image Subtype.val) =
        relabelFamily eX ((univ.filter fun r => a (τ.symm r) = e).image Subtype.val) := by
      ext B
      rw [mem_relabelFamily]
      simp only [mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨r, hr, rfl⟩
        refine ⟨τ r, ?_, rfl⟩
        rw [Equiv.symm_apply_apply]
        exact hr
      · rintro ⟨r, hr, hrB⟩
        refine ⟨τ.symm r, hr, ?_⟩
        show r.1.map eX.toEmbedding = B
        rw [hrB]
        exact map_map_symm_equiv eX B
    show relabelFamily eX (bot (eE.symm e.1)) = _ ↔ _
    rw [himg, forestBelow_relabelFamily, (relabelFamily_injective eX).eq_iff]
    rfl

/-- The weight of a history, carried along an isomorphism. -/
theorem historyWeight_iso (hs : ∀ e, N₂.graph.source (eE e) = eV (N₁.graph.source e))
    (ht : ∀ e, N₂.graph.target (eE e) = eV (N₁.graph.target e)) (hr : N₂.root = eV N₁.root)
    (hl : ∀ x, N₂.leaf (eX x) = eV (N₁.leaf x))
    (hθl : ∀ e, θ₂.length (eE e) = θ₁.length e) (hθi : ∀ e, θ₂.inheritance (eE e) = θ₁.inheritance e)
    (bot top : E₁ → Finset (Finset X₁)) :
    historyWeight N₂ θ₂ ρ (isoForests eE eX bot) (isoForests eE eX top) =
      historyWeight N₁ θ₁ ρ bot top := by
  unfold historyWeight
  congr 1
  · refine (prod_equiv eV (fun v => ?_) fun v _ => ?_).symm
    · simp only [mem_erase, mem_univ, and_true, hr, ne_eq, eV.injective.eq_iff]
    · rw [arrivingForest_iso hs hl, allocationFactor_iso ht hθi]
  · refine (Fintype.prod_equiv eE _ _ fun e => ?_).symm
    simp only [isoForests, Equiv.symm_apply_apply, hθl, kingmanTransition_relabelFamily]

/-- The distribution of gene trees, carried along an isomorphism. -/
theorem geneTreeDist_iso (hs : ∀ e, N₂.graph.source (eE e) = eV (N₁.graph.source e))
    (ht : ∀ e, N₂.graph.target (eE e) = eV (N₁.graph.target e)) (hr : N₂.root = eV N₁.root)
    (hl : ∀ x, N₂.leaf (eX x) = eV (N₁.leaf x))
    (hθl : ∀ e, θ₂.length (eE e) = θ₁.length e) (hθi : ∀ e, θ₂.inheritance (eE e) = θ₁.inheritance e)
    (G : Finset (Finset X₁)) :
    geneTreeDist N₂ θ₂ ρ (relabelFamily eX G) = geneTreeDist N₁ θ₁ ρ G := by
  unfold geneTreeDist
  let Φ : (E₁ → Finset (Finset X₁)) ≃ (E₂ → Finset (Finset X₂)) :=
    Equiv.arrowCongr eE (relabelFamilyEquiv eX)
  have hΦ : ∀ t, Φ t = isoForests eE eX t := fun _ => rfl
  rw [← Φ.sum_comp]
  refine sum_congr rfl fun bot _ => ?_
  rw [← Φ.sum_comp]
  refine sum_congr rfl fun top _ => ?_
  rw [hΦ, hΦ, historyWeight_iso hs ht hr hl hθl hθi, hr, arrivingForest_iso hs hl,
    kingmanAbsorption_relabelFamily]

omit [Fintype X₁] [Fintype X₂] in
/-- A family of clusters displays a quartet tree exactly when its relabelling displays the relabelled
quartet tree. -/
theorem displays_relabelFamily (T : Finset (Finset X₁)) (q : QuartetTree X₁) :
    Displays (relabelFamily eX T) (q.map eX.injective) ↔ Displays T q := by
  have hm : ∀ A : Finset X₁, A.map eX.toEmbedding = A.image eX := fun A => map_eq_image _ _
  unfold Displays
  simp only [QuartetTree.map_taxa, QuartetTree.map_val, relabelFamily, exists_mem_image, hm]
  refine exists_congr fun A => and_congr_right fun _ => ?_
  rw [← image_inter _ _ eX.injective]
  exact (image_injective eX.injective).mem_finset_image

/-- **Concordance factors are invariant under isomorphism** of networks with their parameters,
along a bijection of the taxa. -/
theorem nmscCF_iso (hs : ∀ e, N₂.graph.source (eE e) = eV (N₁.graph.source e))
    (ht : ∀ e, N₂.graph.target (eE e) = eV (N₁.graph.target e)) (hr : N₂.root = eV N₁.root)
    (hl : ∀ x, N₂.leaf (eX x) = eV (N₁.leaf x))
    (hθl : ∀ e, θ₂.length (eE e) = θ₁.length e) (hθi : ∀ e, θ₂.inheritance (eE e) = θ₁.inheritance e)
    (q : QuartetTree X₁) : nmscCF N₂ θ₂ ρ (q.map eX.injective) = nmscCF N₁ θ₁ ρ q := by
  unfold nmscCF
  rw [← (relabelFamilyEquiv eX).sum_comp]
  refine sum_congr rfl fun G _ => ?_
  rw [relabelFamilyEquiv_apply, unroot_relabelFamily, displays_relabelFamily,
    geneTreeDist_iso hs ht hr hl hθl hθi]

end CFIso

/-! ### Concordance factors below a stable ancestor of `Y` -/

section Below

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
  {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A stable ancestor of a set of taxa is one of its subsets. -/
theorem isStableAncestor_of_subset {Y Z : Set X} {l : V} (h : N.IsStableAncestor Y l)
    (hZ : Z ⊆ Y) : N.IsStableAncestor Z l :=
  fun x hx => h x (hZ hx)

/-- **Concordance factors in the part below a stable ancestor of a set of taxa** are those of the
network: the library's theorem for the four taxa of a quartet tree, applied to the network and to
the part below the stable ancestor, whose parts below the four taxa are isomorphic. -/
theorem nmscCF_belowNetwork_of_superset (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {Y : Set X} (hY : Y.Nontrivial) {l : V} (hst : N.IsStableAncestor Y l)
    {hl : l ∈ N.ancestralVertices Y} {hleaf : ∀ x ∈ Y, N.graph.Reaches l (N.leaf x)}
    (q : QuartetTree Y) :
    nmscCF (N.belowNetwork l Y hl hleaf) (belowMetric l Y θ) ρ q =
      nmscCF N θ ρ (q.map Subtype.val_injective) := by
  set M := N.belowNetwork l Y hl hleaf with hM_def
  have hM : M.IsPhylogenetic := belowNetwork_isPhylogenetic hN hY hst
  have hθM : M.IsMetric (belowMetric l Y θ) := isMetric_belowMetric hN hst hθ
  set t : Finset Y := q.taxa with ht_def
  have ht4 : #t = 4 := q.card_taxa
  set t₁ : Finset X := t.map (Function.Embedding.subtype _) with ht₁_def
  have ht₁4 : #t₁ = 4 := by rw [card_map, ht4]
  have hmem₁ : ∀ x : X, x ∈ t₁ ↔ ∃ h : x ∈ Y, (⟨x, h⟩ : Y) ∈ t := fun x => by
    simp only [ht₁_def, mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, ha⟩
    · rintro ⟨h, hx⟩
      exact ⟨_, hx, rfl⟩
  have ht₁Y : (t₁ : Set X) ⊆ Y := fun x hx => ((hmem₁ x).1 hx).1
  have hnt : (t : Set Y).Nontrivial := one_lt_card_iff_nontrivial.mp (by omega)
  have hnt₁ : (t₁ : Set X).Nontrivial := one_lt_card_iff_nontrivial.mp (by omega)
  have hst₁ : N.IsStableAncestor (t₁ : Set X) l := isStableAncestor_of_subset hst ht₁Y
  obtain ⟨x₀, hx₀⟩ := hnt.nonempty
  have hlM : M.root ∈ M.ancestralVertices (t : Set Y) := ⟨x₀, hx₀, hM.root_reaches _⟩
  have hleafM : ∀ x ∈ (t : Set Y), M.graph.Reaches M.root (M.leaf x) :=
    fun _ _ => hM.root_reaches _
  have hleaf₁ : ∀ x ∈ (t₁ : Set X), N.graph.Reaches l (N.leaf x) :=
    fun x hx => hst.reaches_leaf hN (ht₁Y hx)
  have hl₁ : l ∈ N.ancestralVertices (t₁ : Set X) :=
    ⟨x₀.1, (hmem₁ _).2 ⟨x₀.2, hx₀⟩, hleaf₁ _ ((hmem₁ _).2 ⟨x₀.2, hx₀⟩)⟩
  -- the quartet trees on the four taxa
  obtain ⟨q₀, hq₀⟩ := NMSC.exists_map_val_eq (Q := t) (r := q) rfl
  -- the parts below the four taxa
  set A := M.belowNetwork M.root (t : Set Y) hlM hleafM with hA_def
  set B := N.belowNetwork l (t₁ : Set X) hl₁ hleaf₁ with hB_def
  have hvA : ∀ u : M.belowVertices M.root (t : Set Y), u.1.1 ∈ N.belowVertices l (t₁ : Set X) := by
    rintro ⟨u, -, x, hx, hux⟩
    exact ⟨u.2.1, x.1, (hmem₁ _).2 ⟨x.2, hx⟩, belowNetwork_reaches_iff.1 hux⟩
  have hvB : ∀ v : N.belowVertices l (t₁ : Set X), ∃ h : v.1 ∈ N.belowVertices l Y,
      (⟨v.1, h⟩ : N.belowVertices l Y) ∈ M.belowVertices M.root (t : Set Y) := by
    rintro ⟨v, hlv, x, hx, hvx⟩
    obtain ⟨hxY, hxt⟩ := (hmem₁ x).1 hx
    exact ⟨⟨hlv, x, hxY, hvx⟩, belowNetwork_reaches_iff.2 hlv, ⟨x, hxY⟩, hxt,
      belowNetwork_reaches_iff.2 hvx⟩
  have heA : ∀ c : M.belowArcs M.root (t : Set Y), c.1.1 ∈ N.belowArcs l (t₁ : Set X) := by
    rintro ⟨c, -, x, hx, hcx⟩
    exact ⟨c.2.1, x.1, (hmem₁ _).2 ⟨x.2, hx⟩, belowNetwork_reaches_iff.1 hcx⟩
  have heB : ∀ e : N.belowArcs l (t₁ : Set X), ∃ h : e.1 ∈ N.belowArcs l Y,
      (⟨e.1, h⟩ : N.belowArcs l Y) ∈ M.belowArcs M.root (t : Set Y) := by
    rintro ⟨e, hle, x, hx, hex⟩
    obtain ⟨hxY, hxt⟩ := (hmem₁ x).1 hx
    exact ⟨⟨hle, x, hxY, hex⟩, belowNetwork_reaches_iff.2 hle, ⟨x, hxY⟩, hxt,
      belowNetwork_reaches_iff.2 hex⟩
  let eV : M.belowVertices M.root (t : Set Y) ≃ N.belowVertices l (t₁ : Set X) :=
    { toFun := fun u => ⟨u.1.1, hvA u⟩
      invFun := fun v => ⟨⟨v.1, (hvB v).1⟩, (hvB v).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eE : M.belowArcs M.root (t : Set Y) ≃ N.belowArcs l (t₁ : Set X) :=
    { toFun := fun c => ⟨c.1.1, heA c⟩
      invFun := fun e => ⟨⟨e.1, (heB e).1⟩, (heB e).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eX : (t : Set Y) ≃ (t₁ : Set X) :=
    { toFun := fun x => ⟨x.1.1, (hmem₁ _).2 ⟨x.1.2, x.2⟩⟩
      invFun := fun y => ⟨⟨y.1, ((hmem₁ _).1 y.2).1⟩, ((hmem₁ _).1 y.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hiso := nmscCF_iso (N₁ := A) (N₂ := B) (θ₁ := belowMetric M.root (t : Set Y)
    (belowMetric l Y θ)) (θ₂ := belowMetric l (t₁ : Set X) θ) (ρ := ρ) (eV := eV) (eE := eE)
    (eX := eX) (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) q₀
  have hAq := NMSC.nmscCF_belowNetwork (hl := hlM) (hleaf := hleafM) hM hθM hρ ht4 hnt
    (M.root_isStableAncestor _) q₀
  have hBq := NMSC.nmscCF_belowNetwork (hl := hl₁) (hleaf := hleaf₁) hN hθ hρ ht₁4 hnt₁ hst₁
    (q₀.map eX.injective)
  have hmap : (q₀.map eX.injective).map Subtype.val_injective = q.map Subtype.val_injective := by
    rw [← hq₀]
    apply Subtype.ext
    simp only [QuartetTree.map_val, image_image]
    refine congrArg (fun f => image f _) (funext fun B => ?_)
    simp only [Function.comp, image_image]
    rfl
  rw [hmap] at hBq
  rw [hq₀] at hAq
  rw [← hAq, ← hiso]
  convert hBq using 2

end Below

/-! ### `N⊕_Y` and the part of `N` below `LSA(Y)` -/

section InducedBelow

variable {V E X : Type*} {N : RootedNetwork V E X}

/-- The part of `N` below `LSA(Y)` ancestral to `Y`, rooted at `LSA(Y)`: `N⊕_Y` before the vertices
of indegree one and outdegree one are suppressed. -/
abbrev inducedBelow (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (Y : Set X)
    (hY : Y.Nontrivial) :=
  lsaNetwork hN Y hY.nonempty

/-- `(N⊕_Y)⁻`: the unrooted network of the induced LSA network on `Y`. -/
abbrev inducedLSAUnrooted (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (Y : Set X)
    (hY : Y.Nontrivial) :=
  unrooted (inducedLSA N hN.1 Y hY) (inducedLSA_isBinaryRootedNetwork hN hY) hY.coe_sort

/-- The node of `N` underlying a node of `(N⊕_Y)⁻`. -/
def inducedNode (hN : IsBinaryRootedNetwork N) {Y : Set X} (hY : Y.Nontrivial)
    (w : SemidirectedVertex (inducedLSA_isBinaryRootedNetwork hN hY).1 hY.coe_sort) : V :=
  w.1.1.1.1

/-- **`N⊕_Y` of a level-1 network is level-1**: its cycles are made of chains forming cycles of
`N`. -/
theorem isLevelOne_inducedLSA_graph (hN : N.IsPhylogenetic) (h1 : IsLevelOne N.graph)
    {Y : Set X} (hY : Y.Nontrivial) : IsLevelOne (inducedLSA N hN Y hY).graph :=
  isLevelOne_suppress (lsaNetwork_isPhylogenetic hN hY) (isLevelOne_belowNetwork h1)

/-- **The chains of a cycle of `N⊕_Y` form a cycle of `N`.** -/
theorem isCycle_inducedChainArcs (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nontrivial)
    {D : Set _} (hD : IsCycle (inducedLSA N hN Y hY).graph D) :
    IsCycle N.graph (Subtype.val '' suppressChainArcs (inducedBelow N hN Y hY) D) :=
  isCycle_image_val_belowNetwork (isCycle_suppressChainArcs (lsaNetwork_isPhylogenetic hN hY) hD)

/-- The LSA of the taxa of `N⊕_Y` is its root. -/
theorem lsa_univ_inducedLSA (hN : IsBinaryRootedNetwork N) {Y : Set X} (hY : Y.Nontrivial)
    (hne : (Set.univ : Set Y).Nonempty) :
    lsa (inducedLSA_isBinaryRootedNetwork hN hY).1 Set.univ hne = (inducedLSA N hN.1 Y hY).root :=
  IsLeastStableAncestor.unique (inducedLSA_isBinaryRootedNetwork hN hY).1 (lsa_spec _ _ _)
    (inducedNetwork_isLSANetwork hN.1 hY)

/-- `LSA(X)` is above `LSA(Y)` (Lemma 1 (iii)). -/
theorem reaches_lsa_induced (hN : IsBinaryRootedNetwork N) {Y : Set X} (hY : Y.Nontrivial)
    (hne : (Set.univ : Set X).Nonempty) :
    N.graph.Reaches (lsa hN.1 Set.univ hne) (lsa hN.1 Y hY.nonempty) :=
  (lemma1 hN _ (Set.subset_univ _)).2.2

/-- **A vertex of `N⊕_Y` other than its root is a vertex of `N⁻`**: it is strictly below `LSA(Y)`,
which is below `LSA(X)`. -/
theorem exists_unrooted_node_of_induced (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X)
    {Y : Set X} (hY : Y.Nontrivial) {z : {v // ¬ (inducedBelow N hN.1 Y hY).IsChainVertex v}}
    (hz : z ≠ (inducedLSA N hN.1 Y hY).root) :
    z.1.1 ≠ lsa hN.1 Y hY.nonempty ∧ ∃ u : SemidirectedVertex hN.1 hX, u.1.1 = z.1.1 := by
  have hzl : z.1.1 ≠ lsa hN.1 Y hY.nonempty := fun h => hz (Subtype.ext (Subtype.ext h))
  have hr := (reaches_lsa_induced hN hY Set.univ_nonempty).trans z.1.2.1
  refine ⟨hzl, exists_unrooted_node hN.1 hr fun h => hzl ?_⟩
  have h₁ : N.graph.Reaches (lsa hN.1 Y hY.nonempty) (lsa hN.1 Set.univ Set.univ_nonempty) :=
    h ▸ z.1.2.1
  exact h.trans (eq_of_reaches_of_reaches hN.1.acyclic (reaches_lsa_induced hN hY _) h₁)

/-- A hybrid node of `N⊕_Y` is a hybrid node of `N`. -/
theorem indegree_eq_two_of_inducedLSA (hN : IsBinaryRootedNetwork N) {Y : Set X}
    (hY : Y.Nontrivial) {y : {v // ¬ (inducedBelow N hN.1 Y hY).IsChainVertex v}}
    (h2 : (inducedLSA N hN.1 Y hY).graph.indegree y = 2) : N.graph.indegree y.1.1 = 2 := by
  have hyr : y ≠ (inducedLSA N hN.1 Y hY).root := fun h => by
    rw [h, (inducedLSA_isBinaryRootedNetwork hN hY).1.root_indegree] at h2
    exact absurd h2 (by norm_num)
  have hl : y.1.1 ≠ lsa hN.1 Y hY.nonempty := fun h => hyr (Subtype.ext (Subtype.ext h))
  exact le_antisymm (hN.indegree_le_two _)
    ((two_le_indegree_of_suppress_indegree_eq_two (lsaNetwork_isPhylogenetic hN.1 hY) h2).trans_eq
      (belowNetwork_indegree hN.1 (lsa_spec hN.1 _ _).1 y.1 hl))

end InducedBelow

/-! ### The cycles and blocks of `(N⊕_Y)⁻` and those of `N⁻` -/

section InducedCorrespondence


variable {V E X : Type*} {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
  (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {Y : Set X} (hY : Y.Nontrivial)

include h1 in
/-- **The cycle of `N` of a cycle of `N⁻` is made of the chains of the cycle of `N⊕_Y` of a cycle of
`(N⊕_Y)⁻` with the same hybrid node**: both are cycles of `N` through that node (Lemma 3). -/
theorem unrootedCycleArcs_eq_image_induced {C' : Set _}
    (hC' : IsCycle (inducedLSAUnrooted N hN Y hY).graph C') {w}
    (hw : IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : inducedNode hN hY w = v.1.1) :
    unrootedCycleArcs hN C = Subtype.val '' suppressChainArcs (inducedBelow N hN.1 Y hY)
      (unrootedCycleArcs (inducedLSA_isBinaryRootedNetwork hN hY) C') := by
  have := hN.1.finite_arcs
  have hQb := inducedLSA_isBinaryRootedNetwork hN hY
  refine (lemma3 hN h1 (isCycle_unrootedCycleArcs hN hC)).2.2 _
    (isCycle_inducedChainArcs hN.1 hY (isCycle_unrootedCycleArcs hQb hC'))
    ⟨v.1.1, mem_cycleNodes_unrootedCycleArcs hN hv.mem_cycleNodes, ?_⟩
  rw [← hwv]
  exact mem_cycleNodes_image_val_iff.2 ⟨_, mem_cycleNodes_suppressChainArcs
    (lsaNetwork_isPhylogenetic hN.1 hY) (mem_cycleNodes_unrootedCycleArcs hQb hw.mem_cycleNodes),
    rfl⟩

include h1 in
/-- **The blocks of `(N⊕_Y)⁻` are the traces on `Y` of the blocks of `N⁻`**: for a cycle of `(N⊕_Y)⁻`
and the cycle of `N⁻` with the same hybrid node, the block of a taxon of `Y` is that of the same node of
`N` in both. A node other than the top of its cycle has the taxa below its arc off the cycle as
block (`exists_reaches_offCycle_of_mem_nodeBlock`, `mem_nodeBlock_of_reaches_offCycle`); these
arcs are those of `N⊕_Y` and their first arcs in `N`, and the tops of the two cycles are the same
node. -/
theorem inducedNode_blockNode {C' : Set _} (hC' : IsCycle (inducedLSAUnrooted N hN Y hY).graph C')
    {w} (hw : IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : inducedNode hN hY w = v.1.1)
    (x : X) (hx : x ∈ Y) :
    inducedNode hN hY (blockNode (inducedLSAUnrooted N hN Y hY) C' ⟨x, hx⟩) =
      (blockNode (unrooted N hN hX) C x).1.1 := by
  have := hN.1.finite_arcs
  have hQb := inducedLSA_isBinaryRootedNetwork hN hY
  have := hQb.1.finite_arcs
  have h1Q := isLevelOne_inducedLSA_graph hN.1 h1 hY
  have hL := lsaNetwork_isPhylogenetic hN.1 hY
  set Q := inducedLSA N hN.1 Y hY with hQ_def
  set L := inducedBelow N hN.1 Y hY with hL_def
  set D := unrootedCycleArcs hQb C' with hD_def
  have hD : IsCycle Q.graph D := isCycle_unrootedCycleArcs hQb hC'
  set Ĉ := unrootedCycleArcs hN C with hĈ_def
  have hĈ : IsCycle N.graph Ĉ := isCycle_unrootedCycleArcs hN hC
  have hcorr : Ĉ = Subtype.val '' suppressChainArcs L D :=
    unrootedCycleArcs_eq_image_induced hN h1 hX hY hC' hw hC hv hwv
  have hLD : IsCycle L.graph (suppressChainArcs L D) := isCycle_suppressChainArcs hL hD
  -- the nodes of `D` are nodes of `Ĉ`
  have hnodes : ∀ z ∈ cycleNodes Q.graph D, z.1.1 ∈ cycleNodes N.graph Ĉ := fun z hz => by
    rw [hcorr]
    exact mem_cycleNodes_image_val_iff.2 ⟨_, mem_cycleNodes_suppressChainArcs hL hz, rfl⟩
  -- the arcs of `N⊕_Y` off `D` are off `Ĉ`
  have hoff : ∀ c, c ∉ D → c.1.1 ∉ Ĉ := by
    intro c hc h
    rw [hcorr] at h
    obtain ⟨g, hg, hgc⟩ := h
    obtain rfl : g = c.1 := Subtype.ext hgc
    exact hc ((mem_suppressChainArcs_iff D c).1 hg)
  -- the tops of `D` and `Ĉ`
  obtain ⟨aQ, haQ, -, hGQ, hEQ, hrQ⟩ := h1Q.exists_top hQb.1 hD
  obtain ⟨aN, haN, hFN, -, hEN, hrN⟩ := h1.exists_top hN.1 hĈ
  have htop : aQ.1.1 = aN := by
    refine eq_top_of_forall_target_ne hN.1 hEN hrN (hnodes aQ haQ) fun g hg hgt => ?_
    rw [hcorr] at hg
    obtain ⟨g', ⟨f, hf, hfg⟩, rfl⟩ := hg
    refine hGQ f hf (Subtype.ext ?_)
    have h' : L.graph.target g' = aQ.1 := Subtype.ext hgt
    exact (chainEnd_eq_of_isOnChain hL hfg (by rw [h']; exact aQ.2)).trans h'
  obtain ⟨hq, hxq⟩ := blockNode_spec hC' (⟨x, hx⟩ : Y)
  obtain ⟨hn, hxn⟩ := blockNode_spec hC x
  set q := blockNode (inducedLSAUnrooted N hN Y hY) C' ⟨x, hx⟩ with hq_def
  set n := blockNode (unrooted N hN hX) C x with hn_def
  have hqr : q.1.1 ≠ Q.root := fun h =>
    unrooted_node_ne_lsa q (h.trans (lsa_univ_inducedLSA hN hY _).symm)
  show q.1.1.1.1 = n.1.1
  by_cases hqa : q.1.1 = aQ
  · -- the node of the block of `x` in `(N⊕_Y)⁻` is the top: so is that in `N⁻`
    rw [hqa, htop]
    by_contra hna
    have hna' : n.1.1 ≠ aN := fun h => hna h.symm
    obtain ⟨c, hc, hcs, hcx⟩ :=
      exists_reaches_offCycle_of_mem_nodeBlock hN h1 hC hEN hrN hn hna' hxn
    have hnĈ : n.1.1 ∈ cycleNodes N.graph Ĉ := mem_cycleNodes_unrootedCycleArcs hN hn
    rw [hcorr] at hnĈ
    obtain ⟨yL, hyL, hyLn⟩ := mem_cycleNodes_image_val_iff.1 hnĈ
    -- the arc `c` is below `LSA(Y)`
    have hcB : c ∈ N.belowArcs
        (lsa hN.1 Y hY.nonempty)
        Y := ⟨by rw [hcs, ← hyLn]; exact yL.2.1, ⟨x, hx, hcx⟩⟩
    set cL : N.belowArcs _ Y := ⟨c, hcB⟩ with hcL_def
    have hcLs : L.graph.source cL = yL := Subtype.ext (hcs.trans hyLn.symm)
    have hcL : cL ∉ suppressChainArcs L D := fun h =>
      hc (show c ∈ Ĉ by rw [hcorr]; exact ⟨cL, h, rfl⟩)
    -- the vertex `yL` is not a chain vertex: it has an arc of the cycle leaving it, and `c`
    have hyc : ¬ L.IsChainVertex yL := by
      intro hyc
      obtain ⟨f₁, hf₁, f₂, hf₂, h12, hu₁, hu₂⟩ := hLD.exists_ne_of_mem
        (fun e _ h => hL.acyclic _ (.single ⟨e, rfl, h.symm⟩)) hyL
      obtain ⟨i, hi⟩ := (L.graph.indegree_eq_one_iff yL).mp hyc.1
      obtain ⟨o, ho⟩ := (L.graph.outdegree_eq_one_iff yL).mp hyc.2
      have hco := (ho cL).mp hcLs
      have key : ∀ e ∈ suppressChainArcs L D, (L.graph.source e = yL ∨ L.graph.target e = yL) →
          L.graph.target e = yL := by
        rintro e he (h | h)
        · exact absurd (((ho e).mp h).trans hco.symm ▸ he) hcL
        · exact h
      exact h12 (((hi f₁).mp (key f₁ hf₁ hu₁)).trans ((hi f₂).mp (key f₂ hf₂ hu₂)).symm)
    have hyD : (⟨yL, hyc⟩ : {v // ¬ L.IsChainVertex v}) ∈ cycleNodes Q.graph D :=
      mem_cycleNodes_suppress_of_mem hL hyL
    have hcQ : (⟨cL, by rw [hcLs]; exact hyc⟩ : {e // ¬ L.IsChainVertex (L.graph.source e)}) ∉ D :=
      fun h => hcL ((mem_suppressChainArcs_iff D _).2 h)
    have hcQx : Q.graph.Reaches (Q.graph.target ⟨cL, by rw [hcLs]; exact hyc⟩)
        (Q.leaf ⟨x, hx⟩) := by
      have h₁ : L.graph.Reaches (L.graph.target cL) (L.leaf ⟨x, hx⟩) :=
        belowNetwork_reaches_iff.2 hcx
      exact suppress_reaches_of_reaches hL _ _
        (reaches_of_chainEnd_of_reaches hL h₁ (not_isChainVertex_leaf hL _))
    -- the vertex `yL` is not the root of `N⊕_Y`, which is `LSA(Y)`
    have hyr : (⟨yL, hyc⟩ : {v // ¬ L.IsChainVertex v}) ≠ Q.root := by
      intro h
      apply hna'
      have hy : n.1.1 = lsa hN.1 Y
          hY.nonempty :=
        hyLn.symm.trans (congrArg (fun z => z.1.1) h)
      have haNĈ := haN
      rw [hcorr] at haNĈ
      obtain ⟨aL, -, haL⟩ : ∃ z ∈ cycleNodes L.graph (suppressChainArcs L D), z.1 = aN :=
        mem_cycleNodes_image_val_iff.1 haNĈ
      have h₂ : N.graph.Reaches aN n.1.1 := hFN _ (mem_cycleNodes_unrootedCycleArcs hN hn)
      rw [hy] at h₂ ⊢
      exact eq_of_reaches_of_reaches hN.1.acyclic (haL ▸ aL.2.1) h₂
    obtain ⟨u, hu, huy⟩ := exists_mem_cycleNodes_of_unrootedCycleArcs hQb hyD
      (by rw [lsa_univ_inducedLSA hN hY]; exact hyr)
    have hxu := mem_nodeBlock_of_reaches_offCycle hQb h1Q hC' hu hcQ
      (Subtype.ext (show L.graph.source cL = u.1.1.1 by rw [hcLs, huy])) hcQx
    have huq : u = q := eq_blockNode h1Q hC' hu hxu
    apply hna'
    rw [← htop, ← hqa, ← huq, huy]
    exact hyLn.symm
  · obtain ⟨c, hc, hcs, hcx⟩ :=
      exists_reaches_offCycle_of_mem_nodeBlock hQb h1Q hC' hEQ hrQ hq hqa hxq
    have hcNs : N.graph.source c.1.1 = q.1.1.1.1 := congrArg (fun z => z.1.1) hcs
    have hcNx : N.graph.Reaches (N.graph.target c.1.1) (N.leaf x) :=
      (belowNetwork_reaches_iff.1 (chainReach_chainEnd hL (L.graph.target c.1)).reaches).trans
        (belowNetwork_reaches_iff.1 (reaches_val_of_suppress_reaches hL hcx))
    obtain ⟨-, u, huq⟩ := exists_unrooted_node_of_induced hN hX hY hqr
    obtain ⟨u', hu', hu'q⟩ := exists_mem_cycleNodes_of_unrootedCycleArcs hN
      (hnodes _ (mem_cycleNodes_unrootedCycleArcs hQb hq))
      (by rw [← huq]; exact unrooted_node_ne_lsa u)
    have hxu' := mem_nodeBlock_of_reaches_offCycle hN h1 hC hu' (hoff c hc)
      (hcNs.trans hu'q.symm) hcNx
    exact hu'q.symm.trans (congrArg (fun z => z.1.1) (eq_blockNode h1 hC hu' hxu'))

/-- A node of `(N⊕_Y)⁻` is determined by its node of `N`. -/
theorem inducedNode_injective : Function.Injective (inducedNode hN hY) :=
  fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext h)))

include h1 in
/-- Two taxa of `Y` are in the same block of the cycle of `N⁻` exactly when they are in the same
block of the cycle of `(N⊕_Y)⁻` with the same hybrid node. -/
theorem blockNode_eq_iff_induced {C' : Set _} (hC' : IsCycle (inducedLSAUnrooted N hN Y hY).graph C')
    {w} (hw : IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : inducedNode hN hY w = v.1.1) {x y : X}
    (hx : x ∈ Y) (hy : y ∈ Y) :
    blockNode (unrooted N hN hX) C x = blockNode (unrooted N hN hX) C y ↔
      blockNode (inducedLSAUnrooted N hN Y hY) C' ⟨x, hx⟩ =
        blockNode (inducedLSAUnrooted N hN Y hY) C' ⟨y, hy⟩ := by
  rw [← (inducedNode_injective hN hY).eq_iff,
    inducedNode_blockNode hN h1 hX hY hC' hw hC hv hwv x hx,
    inducedNode_blockNode hN h1 hX hY hC' hw hC hv hwv y hy]
  exact ⟨fun h => congrArg (fun z => z.1.1) h, fun h => unrooted_node_ext h⟩

include h1 in
/-- A taxon of `Y` is in the hybrid block of the cycle of `N⁻` exactly when it is in the hybrid
block of the cycle of `(N⊕_Y)⁻` with the same hybrid node. -/
theorem blockNode_eq_hybrid_iff_induced {C' : Set _}
    (hC' : IsCycle (inducedLSAUnrooted N hN Y hY).graph C') {w}
    (hw : IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : inducedNode hN hY w = v.1.1) {x : X}
    (hx : x ∈ Y) :
    blockNode (unrooted N hN hX) C x = v ↔
      blockNode (inducedLSAUnrooted N hN Y hY) C' ⟨x, hx⟩ = w := by
  rw [← (inducedNode_injective hN hY).eq_iff,
    inducedNode_blockNode hN h1 hX hY hC' hw hC hv hwv x hx, hwv]
  exact ⟨fun h => congrArg (fun z => z.1.1) h, fun h => unrooted_node_ext h⟩


end InducedCorrespondence

/-! ### The sets of four taxa that the cycles of `(N⊕_Y)⁻` separate -/

section InducedSeparation

/-- **A cycle of size at least four separates a set of four taxa**: a taxon of the hybrid block and a
taxon of another block, with taxa of two more blocks. -/
theorem exists_separatesQuartet_of_four_le {V' E' X' : Type*} [DecidableEq X'] [Finite E']
    {M : RootedNetwork V' E' X'} {hM : IsBinaryRootedNetwork M} {hX' : Nontrivial X'}
    (h1 : IsLevelOne M.graph) {C : Set _} (hC : IsCycle (unrooted M hM hX').graph C)
    (hC4 : 4 ≤ C.ncard) {v} (hv : IsHybridNodeOf (unrooted M hM hX') C v) :
    ∃ s : Finset X', #s = 4 ∧ SeparatesQuartet (unrooted M hM hX') C v s := by
  obtain ⟨x, hx⟩ := exists_blockNode_eq h1 hC hv.mem_cycleNodes
  obtain ⟨u, hu, huv⟩ := hC.exists_mem_cycleNodes_notMem (Set.toFinite {v})
    (by rw [Set.ncard_singleton]; omega)
  obtain ⟨y, hy⟩ := exists_blockNode_eq h1 hC hu
  have hxy : ¬ SameBlock (unrooted M hM hX').graph (unrooted M hM hX').leaf C x y := by
    rw [sameBlock_iff_blockNode_eq h1 hC, hx, hy]
    exact fun h => huv (h ▸ rfl)
  obtain ⟨c, d, h4, hsep⟩ := exists_separatesQuartet_of_not_sameBlock h1 hC hC4 hv hxy
  exact ⟨_, h4, hsep⟩

variable {V E X : Type*} {N : RootedNetwork V E X} [Finite E] (hN : IsBinaryRootedNetwork N)
  (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {Y : Set X} (hY : Y.Nontrivial)

include h1 in
/-- **A cycle of `(N⊕_Y)⁻` separates a set of taxa of `Y` exactly when the cycle of `N⁻` with the
same hybrid node separates it**: the blocks of `(N⊕_Y)⁻` are the traces on `Y` of those of `N⁻`. -/
theorem separatesQuartet_induced_iff {C' : Set _}
    (hC' : IsCycle (inducedLSAUnrooted N hN Y hY).graph C') {w}
    (hw : IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : inducedNode hN hY w = v.1.1)
    (s : Finset Y) :
    SeparatesQuartet (inducedLSAUnrooted N hN Y hY) C' w s ↔
      SeparatesQuartet (unrooted N hN hX) C v (s.map (Function.Embedding.subtype _)) := by
  have h1Y := isLevelOne_inducedLSA_graph hN.1 h1 hY
  rw [separatesQuartet_iff h1Y hC' hw, separatesQuartet_iff h1 hC hv]
  constructor
  · rintro ⟨hinj, x, hx, hxw⟩
    refine ⟨?_, x.1, mem_map_of_mem _ hx,
      (blockNode_eq_hybrid_iff_induced hN h1 hX hY hC' hw hC hv hwv x.2).2 hxw⟩
    intro a ha b hb h
    obtain ⟨x, hx, rfl⟩ := mem_map.1 (mem_coe.1 ha)
    obtain ⟨y, hy, rfl⟩ := mem_map.1 (mem_coe.1 hb)
    exact congrArg Subtype.val (hinj (mem_coe.2 hx) (mem_coe.2 hy)
      ((blockNode_eq_iff_induced hN h1 hX hY hC' hw hC hv hwv x.2 y.2).1 h))
  · rintro ⟨hinj, x₁, hx₁, hx₁v⟩
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hx₁
    refine ⟨fun a ha b hb h => Subtype.ext (hinj (mem_coe.2 (mem_map_of_mem _ (mem_coe.1 ha)))
      (mem_coe.2 (mem_map_of_mem _ (mem_coe.1 hb)))
      ((blockNode_eq_iff_induced hN h1 hX hY hC' hw hC hv hwv a.2 b.2).2 h)), x, hx,
      (blockNode_eq_hybrid_iff_induced hN h1 hX hY hC' hw hC hv hwv x.2).1 hx₁v⟩

omit [Finite E] in
include h1 in
/-- **A cycle of `(N⊕_Y)⁻` comes from a cycle of `N⁻`** with the same hybrid node. -/
theorem exists_unrooted_cycle_of_induced {C' : Set _} {w}
    (hw : IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w) :
    ∃ C v, IsCycle (unrooted N hN hX).graph C ∧ IsHybridNodeOf (unrooted N hN hX) C v ∧
      inducedNode hN hY w = v.1.1 := by
  have h2 := indegree_eq_two_of_inducedLSA hN hY hw.unrooted_indegree
  have hwr : w.1.1 ≠ (inducedLSA N hN.1 Y hY).root := fun h =>
    unrooted_node_ne_lsa w (h.trans (lsa_univ_inducedLSA hN hY _).symm)
  obtain ⟨-, v, hv⟩ := exists_unrooted_node_of_induced hN hX hY hwr
  obtain ⟨C, hC, hvC⟩ := exists_isHybridNodeOf_of_indegree_eq_two hN h1 v (hv ▸ h2)
  exact ⟨C, v, hC, hvC, hv.symm⟩

omit [Finite E] in
include h1 in
/-- **A cycle of `N⁻` whose hybrid node is above a taxon of `Y` and not above another induces a cycle
of `(N⊕_Y)⁻`** with the same hybrid node: the two parents of the hybrid node are below `LSA(Y)`, so
the hybrid node is a hybrid node of `N⊕_Y`. -/
theorem exists_induced_cycle_of_unrooted {C : Set _} {v : SemidirectedVertex hN.1 hX} (hv : IsHybridNodeOf (unrooted N hN hX) C v) {x₀ y₀ : X}
    (hx₀ : x₀ ∈ Y) (hy₀ : y₀ ∈ Y) (hvx : N.graph.Reaches v.1.1 (N.leaf x₀))
    (hvy : ¬ N.graph.Reaches v.1.1 (N.leaf y₀)) :
    ∃ C' w, IsCycle (inducedLSAUnrooted N hN Y hY).graph C' ∧
      IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w ∧ inducedNode hN hY w = v.1.1 := by
  have hQb := inducedLSA_isBinaryRootedNetwork hN hY
  have h1Q := isLevelOne_inducedLSA_graph hN.1 h1 hY
  have hst := (lsa_spec hN.1 Y hY.nonempty).1
  have hvl : ¬ N.graph.Reaches v.1.1 (lsa hN.1 Y hY.nonempty) :=
    fun h => hvy (h.trans (hst.reaches_leaf hN.1 hy₀))
  -- the two parents of `v` are below `LSA(Y)`
  obtain ⟨p₁, p₂, hne, hps⟩ := Set.ncard_eq_two.mp hv.unrooted_indegree
  have hp₁ : N.graph.target p₁ = v.1.1 := by
    have : p₁ ∈ {f | N.graph.target f = v.1.1} := by rw [hps]; exact Or.inl rfl
    exact this
  have hp₂ : N.graph.target p₂ = v.1.1 := by
    have : p₂ ∈ {f | N.graph.target f = v.1.1} := by rw [hps]; exact Or.inr rfl
    exact this
  have hpB : ∀ p, N.graph.target p = v.1.1 →
      p ∈ N.belowArcs (lsa hN.1 Y hY.nonempty) Y := fun p hp =>
    ⟨hst.reaches_source hN.1 hx₀ (by rw [hp]; exact hvx) (by rw [hp]; exact hvl),
      ⟨x₀, hx₀, by rw [hp]; exact hvx⟩⟩
  have hvB : v.1.1 ∈ N.belowVertices (lsa hN.1 Y hY.nonempty) Y :=
    ⟨((hpB p₁ hp₁).1).tail ⟨p₁, rfl, hp₁⟩, ⟨x₀, hx₀, hvx⟩⟩
  have hL := lsaNetwork_isPhylogenetic hN.1 hY
  -- `v` is a vertex of `N⊕_Y`, entered by two of its arcs
  have := hL.finite_arcs
  have hchain : ¬ (inducedBelow N hN.1 Y hY).IsChainVertex ⟨v.1.1, hvB⟩ := fun h => by
    have h2 := two_le_indegree_of_ne_targets (G := (inducedBelow N hN.1 Y hY).graph)
      (w := ⟨v.1.1, hvB⟩) (e := ⟨p₁, hpB p₁ hp₁⟩) (e' := ⟨p₂, hpB p₂ hp₂⟩)
      (fun h => hne (congrArg Subtype.val h)) (Subtype.ext hp₁) (Subtype.ext hp₂)
    have := h.1
    omega
  have hy2 : (inducedLSA N hN.1 Y hY).graph.indegree ⟨⟨v.1.1, hvB⟩, hchain⟩ = 2 :=
    le_antisymm (hQb.indegree_le_two _) (two_le_suppress_indegree hL
      (p₁ := ⟨p₁, hpB p₁ hp₁⟩) (p₂ := ⟨p₂, hpB p₂ hp₂⟩) (fun h => hne (congrArg Subtype.val h))
      (Subtype.ext hp₁) (Subtype.ext hp₂))
  have hyr : (⟨⟨v.1.1, hvB⟩, hchain⟩ : {v // ¬ (inducedBelow N hN.1 Y hY).IsChainVertex v}) ≠
      (inducedLSA N hN.1 Y hY).root := fun h =>
    hvl (by rw [show v.1.1 = _ from congrArg (fun z => z.1.1) h]; exact .refl)
  obtain ⟨w, hwy⟩ := exists_unrooted_node (hX := hY.coe_sort) (a := ⟨⟨v.1.1, hvB⟩, hchain⟩) hQb.1
    (by rw [lsa_univ_inducedLSA hN hY]; exact hQb.1.root_reaches _)
    (by rw [lsa_univ_inducedLSA hN hY]; exact hyr)
  obtain ⟨C', hC', hw⟩ := exists_isHybridNodeOf_of_indegree_eq_two hQb h1Q w (hwy ▸ hy2)
  exact ⟨C', w, hC', hw, congrArg (fun z => z.1.1) hwy⟩

include h1 in
/-- **A set of four taxa of `Y` is separated by a cycle of size at least four of `(N⊕_Y)⁻` exactly
when it is separated by one of `N⁻`.** -/
theorem exists_separatesQuartet_induced_iff (s : Finset Y) (hs : #s = 4) :
    (∃ C' w, 4 ≤ C'.ncard ∧ SeparatesQuartet (inducedLSAUnrooted N hN Y hY) C' w s) ↔
      ∃ C v, 4 ≤ C.ncard ∧
        SeparatesQuartet (unrooted N hN hX) C v (s.map (Function.Embedding.subtype _)) := by
  have h1Y := isLevelOne_inducedLSA_graph hN.1 h1 hY
  have hs₁ : #(s.map (Function.Embedding.subtype (· ∈ Y))) = 4 := by rw [card_map, hs]
  constructor
  · rintro ⟨C', w, -, hsep⟩
    obtain ⟨C, v, hC, hv, hwv⟩ := exists_unrooted_cycle_of_induced hN h1 hX hY hsep.2.1
    have hsep' := (separatesQuartet_induced_iff hN h1 hX hY hsep.1 hsep.2.1 hC hv hwv s).1 hsep
    exact ⟨C, v, four_le_ncard_of_separatesQuartet h1 hC hv hs₁ hsep', hsep'⟩
  · rintro ⟨C, v, -, hsep⟩
    obtain ⟨hC, hv, hblk, x₀, hx₀, hd⟩ := hsep
    have hreach := (descendsFrom_iff_reaches hN h1 hC hv x₀).1 hd
    obtain ⟨y₀, hy₀, hyx⟩ := Finset.exists_mem_ne (by omega : 1 < #(s.map
      (Function.Embedding.subtype (· ∈ Y)))) x₀
    have hny : ¬ N.graph.Reaches v.1.1 (N.leaf y₀) := fun h => hblk x₀ hx₀ y₀ hy₀ hyx.symm (by
      rw [sameBlock_iff_blockNode_eq h1 hC, (blockNode_eq_iff_descendsFrom h1 hC hv x₀).2 hd,
        (blockNode_eq_iff_descendsFrom h1 hC hv y₀).2
          ((descendsFrom_iff_reaches hN h1 hC hv y₀).2 h)])
    have hmemY : ∀ x ∈ s.map (Function.Embedding.subtype (· ∈ Y)), x ∈ Y := fun x hx => by
      obtain ⟨a, -, rfl⟩ := mem_map.1 hx
      exact a.2
    obtain ⟨C', w, hC', hw, hwv⟩ := exists_induced_cycle_of_unrooted hN h1 hX hY hv
      (hmemY x₀ hx₀) (hmemY y₀ hy₀) hreach hny
    have hsep' := (separatesQuartet_induced_iff hN h1 hX hY hC' hw hC hv hwv s).2
      ⟨hC, hv, hblk, x₀, hx₀, hd⟩
    exact ⟨C', w, four_le_ncard_of_separatesQuartet h1Y hC' hw hs hsep', hsep'⟩

end InducedSeparation

/-! ### The quartet trees on a set of taxa of `Y` -/

section TreesOn

variable {X : Type*} [Fintype X] [DecidableEq X] {Y : Set X} [Fintype Y] [DecidableEq Y]

/-- The quartet trees on a set of taxa of `Y`, as taxa of `X`, are the images of those on it as taxa
of `Y`. -/
theorem treesOn_map_subtype (s : Finset Y) :
    treesOn (s.map (Function.Embedding.subtype (· ∈ Y))) =
      (treesOn s).image (QuartetTree.map Subtype.val_injective) := by
  ext q
  simp only [mem_treesOn, mem_image]
  constructor
  · intro hq
    obtain ⟨q₀, rfl⟩ := QuartetTree.exists_map_eq Subtype.val_injective q (by
      rw [hq]
      intro x hx
      obtain ⟨a, -, rfl⟩ := mem_map.1 hx
      exact mem_image_of_mem _ (mem_univ a))
    refine ⟨q₀, ?_, rfl⟩
    apply image_injective Subtype.val_injective
    rw [← QuartetTree.map_taxa Subtype.val_injective, hq, map_eq_image]
    rfl
  · rintro ⟨q₀, hq₀, rfl⟩
    rw [QuartetTree.map_taxa, hq₀, map_eq_image]
    rfl

/-- The Big Cycle property on a set of taxa of `Y`, for concordance factors read through `X`. -/
theorem bigCycleOn_comp_map_subtype_iff (p : QuartetTree X → ℝ) (s : Finset Y) :
    BigCycleOn (fun q => p (q.map Subtype.val_injective)) s ↔
      BigCycleOn p (s.map (Function.Embedding.subtype (· ∈ Y))) := by
  unfold BigCycleOn
  rw [treesOn_map_subtype s]
  simp only [forall_mem_image]
  refine forall₂_congr fun q _ => forall₂_congr fun r _ => ?_
  exact ⟨fun H hqr => H fun e => hqr (congrArg _ e),
    fun H hqr => H fun e => hqr (QuartetTree.map_injective Subtype.val_injective e)⟩

end TreesOn

variable {X : Type} [Fintype X] [DecidableEq X] {V E : Type} [Fintype V] [Fintype E]
  {N : RootedNetwork V E X}

omit [Fintype X] [DecidableEq X] [Fintype V] [Fintype E] in
/-- **The induced network of a level-1 network is level-1.** -/
theorem inducedLSA_isLevelOne (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) {Y : Set X}
    (hY : Y.Nontrivial) : IsLevelOne (inducedLSA N hN.1 Y hY).graph :=
  isLevelOne_inducedLSA_graph hN.1 h1 hY

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- The induced parameters are a metric. -/
theorem inducedLSA_isMetricNetwork (hN : IsBinaryRootedNetwork N) {θ : MetricData E}
    (hθ : IsMetricNetwork N θ) {Y : Set X} (hY : Y.Nontrivial) :
    IsMetricNetwork (inducedLSA N hN.1 Y hY) (inducedMetric hN.1 Y hY.nonempty θ) := by
  refine ⟨isMetric_inducedMetric hN.1 hY hθ.1, fun e => ?_⟩
  simp only [inducedMetric, belowMetric]
  exact Finset.sum_pos (fun f _ => hθ.2 _)
    ⟨e.1, Finset.mem_filter.mpr ⟨@Finset.mem_univ _ (Fintype.ofFinite _) _, Or.inl rfl⟩⟩

/-- **The concordance factors of the induced network are those of `N`** (Theorem 2). -/
theorem cf_inducedLSA (hN : IsBinaryRootedNetwork N) {θ : MetricData E} (hθ : IsMetricNetwork N θ) {Y : Set X} (hY : Y.Nontrivial) (q : QuartetTree Y) :
    cf (inducedLSA N hN.1 Y hY) (inducedMetric hN.1 Y hY.nonempty θ) q =
      cf N θ (q.map Subtype.val_injective) := by
  have hL := lsaNetwork_isPhylogenetic hN.1 hY
  have hst := (lsa_spec hN.1 Y hY.nonempty).1
  have hθL : (lsaNetwork hN.1 Y hY.nonempty).IsMetric
      (belowMetric (lsa hN.1 Y hY.nonempty) Y θ) := isMetric_belowMetric hN.1 hst hθ.1
  have hm : inducedMetric hN.1 Y hY.nonempty θ =
      (lsaNetwork hN.1 Y hY.nonempty).suppressMetric (belowMetric (lsa hN.1 Y hY.nonempty) Y θ) := by
    unfold inducedMetric
    dsimp only
    congr
    exact Subsingleton.elim _ _
  have h₁ := NMSC.nmscCF_suppress hL hθL.isNormalized le_rfl q
  have h₂ := nmscCF_belowNetwork_of_superset hN.1 hθ.1 ⟨le_rfl, zero_le_one⟩ hY hst
    (hl := lsa_mem_ancestralVertices hN.1 hY.nonempty)
    (hleaf := fun _ hx => hst.reaches_leaf hN.1 hx) q
  rw [hm]
  exact h₁.trans h₂

/-- **The conditions of Theorem 4 pass to the induced network.** -/
theorem goodParams_inducedLSA (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {θ : MetricData E} (hθ : IsMetricNetwork N θ) (hG : GoodParams hX N θ)
    {Y : Set X} (hY : Y.Nontrivial) :
    GoodParams hY.coe_sort (inducedLSA N hN.1 Y hY) (inducedMetric hN.1 Y hY.nonempty θ) := by
  intro _ _
  obtain ⟨hG₁, hG₂⟩ := hG hθ hN
  have hcf : cf (inducedLSA N hN.1 Y hY) (inducedMetric hN.1 Y hY.nonempty θ) =
      fun q => cf N θ (q.map Subtype.val_injective) := funext (cf_inducedLSA hN hθ hY)
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [hcf, bigCycleOn_comp_map_subtype_iff, hG₁ _ (by rw [card_map, hs])]
    exact (exists_separatesQuartet_induced_iff hN h1 hX hY s hs).symm
  · obtain ⟨q, hq, r, hr, hqr⟩ := hG₂ (s.map (Function.Embedding.subtype (· ∈ Y)))
      (by rw [card_map, hs])
    rw [treesOn_map_subtype] at hq hr
    obtain ⟨q₀, hq₀, rfl⟩ := mem_image.1 hq
    obtain ⟨r₀, hr₀, rfl⟩ := mem_image.1 hr
    exact ⟨q₀, hq₀, r₀, hr₀, by rw [hcf]; exact hqr⟩

/-- **The same orderings on `X` give the same orderings on `Y`.** -/
theorem sameOrdering_inducedLSA {V' E' : Type} [Fintype V'] [Fintype E'] {N' : RootedNetwork V' E' X}
    (hN : IsBinaryRootedNetwork N) (hN' : IsBinaryRootedNetwork N') {θ : MetricData E}
    {θ' : MetricData E'} (hθ : IsMetricNetwork N θ) (hθ' : IsMetricNetwork N' θ')
    (h : SameOrdering (cf N θ) (cf N' θ')) {Y : Set X}
    (hY : Y.Nontrivial) :
    SameOrdering (cf (inducedLSA N hN.1 Y hY) (inducedMetric hN.1 Y hY.nonempty θ))
      (cf (inducedLSA N' hN'.1 Y hY) (inducedMetric hN'.1 Y hY.nonempty θ')) := by
  intro q r hqr
  rw [cf_inducedLSA hN hθ hY, cf_inducedLSA hN hθ hY, cf_inducedLSA hN' hθ' hY,
    cf_inducedLSA hN' hθ' hY]
  exact h _ _ (by rw [QuartetTree.map_taxa, QuartetTree.map_taxa, hqr])

omit [Fintype X] [Fintype V] in
/-- **The cycles of size at least four of the induced network** come from distinct cycles of size at
least four of `N⁻` that separate a set of four taxa of `Y`. -/
theorem bigCycleCount_inducedLSA_le (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {Y : Set X} (hY : Y.Nontrivial) :
    bigCycleCount (unrooted (inducedLSA N hN.1 Y hY) (inducedLSA_isBinaryRootedNetwork hN hY)
        hY.coe_sort) ≤
      {C | C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4 ∧ ∃ s : Finset X, ↑s ⊆ Y ∧ #s = 4 ∧
        ∃ v, SeparatesQuartet (unrooted N hN hX) C v s}.ncard := by
  have h1Y := isLevelOne_inducedLSA_graph hN.1 h1 hY
  -- the cycle of `N⁻` with the hybrid node of a cycle of `(N⊕_Y)⁻`
  let f : Set (SemidirectedArc (inducedLSA_isBinaryRootedNetwork hN hY).1
      (inducedLSA_isBinaryRootedNetwork hN hY).2 hY.coe_sort) → Set (SemidirectedArc hN.1 hN.2 hX) :=
    fun C' => Classical.epsilon fun C => ∃ w v,
      IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w ∧ IsCycle (unrooted N hN hX).graph C ∧
        IsHybridNodeOf (unrooted N hN hX) C v ∧ inducedNode hN hY w = v.1.1
  have hf : ∀ C', IsCycle (inducedLSAUnrooted N hN Y hY).graph C' → ∃ w v,
      IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w ∧ IsCycle (unrooted N hN hX).graph (f C') ∧
        IsHybridNodeOf (unrooted N hN hX) (f C') v ∧ inducedNode hN hY w = v.1.1 := by
    intro C' hC'
    obtain ⟨w, hw⟩ := exists_isHybridNodeOf h1Y hC'
    obtain ⟨C, v, hC, hv, hwv⟩ := exists_unrooted_cycle_of_induced hN h1 hX hY hw
    exact Classical.epsilon_spec (p := fun C => ∃ w v,
      IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w ∧ IsCycle (unrooted N hN hX).graph C ∧
        IsHybridNodeOf (unrooted N hN hX) C v ∧ inducedNode hN hY w = v.1.1) ⟨C, w, v, hw, hC, hv, hwv⟩
  unfold bigCycleCount
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (Set.toFinite _)
  · rintro C' ⟨hC', hC'4⟩
    obtain ⟨w, v, hw, hC, hv, hwv⟩ := hf C' hC'
    obtain ⟨s, hs4, hsep⟩ := exists_separatesQuartet_of_four_le h1Y hC' hC'4 hw
    have hsep' := (separatesQuartet_induced_iff hN h1 hX hY hC' hw hC hv hwv s).1 hsep
    have hs₁ : #(s.map (Function.Embedding.subtype (· ∈ Y))) = 4 := by rw [card_map, hs4]
    refine ⟨⟨hC, four_le_ncard_of_separatesQuartet h1 hC hv hs₁ hsep'⟩, _, ?_, hs₁, v, hsep'⟩
    intro x hx
    obtain ⟨a, -, rfl⟩ := mem_map.1 (mem_coe.1 hx)
    exact a.2
  · intro C₁ hC₁ C₂ hC₂ h
    obtain ⟨w₁, v₁, hw₁, -, hv₁, hwv₁⟩ := hf C₁ hC₁.1
    obtain ⟨w₂, v₂, hw₂, hC, hv₂, hwv₂⟩ := hf C₂ hC₂.1
    have hv₁' : IsHybridNodeOf (unrooted N hN hX) (f C₂) v₁ := h ▸ hv₁
    obtain rfl := IsHybridNodeOf.eq h1 hC hv₁' hv₂
    obtain rfl := inducedNode_injective hN hY (hwv₁.trans hwv₂.symm)
    exact IsHybridNodeOf.cycle_eq h1Y hC₁.1 hC₂.1 hw₁ hw₂

end Banos2019
