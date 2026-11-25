module

public import Banos2019.Network.Semidirected
public import Phylogenetics.NMSC.InducedParams

/-!
# Induced networks on a set of taxa (Baños 2019, Section 2.4, Appendix)

* `inducedRooted` (Definition 7): `N⁺_Z`, the paths from the root to the taxa of `Z`, with the nodes
  of degree two other than the root suppressed, and the edge at the root contracted when the root then
  has outdegree one.
* `inducedLSA` (Definition 8): `N⊕_Z`, the part of `N⁺_Z` below `LSA(Z)`, rooted at `LSA(Z)`. It is the
  library's `RootedNetwork.inducedNetwork`, which removes what is above the LSA before suppressing the
  nodes of degree two. The order does not matter: a node below the LSA that is ancestral to `Z` has all
  its parents below or at the LSA (a parent above it would give a path to a taxon of `Z` avoiding the
  LSA), so its degree is the same either way, and on a binary network the LSA keeps outdegree two.
* `inducedUnrooted` (Definition 10): `(N⁻)_Z`, the edges of `N⁻` on simple treks between taxa of `Z`,
  with the nodes of degree two suppressed.
* `proposition1`: `(N⁻)_Z` and `(N⁺_Z)⁻` are isomorphic; `lemma17` (Appendix).
* `quartetLSA`, `quartetUnrooted`: `Q⊕_s` and `Q⁻_s` for a set `s` of four taxa. In Sections 5–9 the
  induced unrooted quartet network `Q⁻_s` is `(Q⊕_s)⁻`, which Section 5 identifies with `(N⁻)_s` by
  Proposition 1 ("`Q⁻_abcd` is the same graph as `(N⁺_abcd)⁻` and `(N⊕_abcd)⁻`").
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-! ### Definition 7 -/

/-- Contracting the edge at the root when the root has outdegree one: the root and its edge are
removed and the child becomes the root. When the root has another outdegree, nothing changes (the
types only exclude what would be removed). -/
def contractRoot (M : RootedNetwork V E X) (hM : M.IsPhylogenetic) :
    RootedNetwork {v // ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)}
      {e // ¬ (M.graph.source e = M.root ∧ M.graph.outdegree M.root = 1)} X where
  graph :=
    { source := fun e => ⟨M.graph.source e.1, e.2⟩
      target := fun e => ⟨M.graph.target e.1, fun h => hM.target_ne_root e.1 h.1⟩ }
  root :=
    if h : M.graph.outdegree M.root = 1 then
      ⟨M.graph.target (Set.nonempty_of_ncard_ne_zero (s := {e | M.graph.source e = M.root})
          (by unfold DirectedMultigraph.outdegree at h; omega)).some,
        fun h' => hM.target_ne_root _ h'.1⟩
    else ⟨M.root, fun h' => h h'.2⟩
  leaf x := ⟨M.leaf x, fun h => M.leaf_ne_root hM x h.1⟩

/-- The ancestral subnetwork on `Z` with its nodes of indegree one and outdegree one suppressed. -/
def ancestralSuppressed (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (Z : Set X)
    (hZ : Z.Nonempty) :=
  (N.ancestralNetwork Z hZ hN.root_reaches).suppress (N.ancestralNetwork_isPhylogenetic hN Z hZ)

theorem ancestralSuppressed_isPhylogenetic {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (Z : Set X) (hZ : Z.Nonempty) : (ancestralSuppressed N hN Z hZ).IsPhylogenetic :=
  suppress_isPhylogenetic _

/-- **Definition 7** (`def:inducerootnetontaxa`): the *induced rooted network* `N⁺_Z` on `Z`: retain
the edges and nodes on paths from the root to the taxa of `Z`; suppress the nodes of degree two except
the root (a node other than the root has degree two exactly when it has indegree one and outdegree one);
if the root then has outdegree one, contract the edge at the root. -/
def inducedRooted (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (Z : Set X) (hZ : Z.Nonempty) :=
  contractRoot (ancestralSuppressed N hN Z hZ) (ancestralSuppressed_isPhylogenetic hN Z hZ)

/-- **Contracting the edge at the root gives a binary network** when the network has no node of
indegree one and outdegree one, every node other than the root and the taxa has degree three, the
root has outdegree one or two, and there are two taxa. -/
theorem contractRoot_isBinaryRootedNetwork {V' E' X' : Type*} {M : RootedNetwork V' E' X'}
    (hM : M.IsPhylogenetic)
    (hMchain : ∀ v, ¬ (M.graph.indegree v = 1 ∧ M.graph.outdegree v = 1))
    (hMdeg : ∀ v, v ≠ M.root → M.graph.outdegree v ≠ 0 →
      M.graph.indegree v + M.graph.outdegree v = 3)
    (hMroot : M.graph.outdegree M.root = 1 ∨ M.graph.outdegree M.root = 2) {z₁ z₂ : X'}
    (hleaves : z₁ ≠ z₂) : IsBinaryRootedNetwork (contractRoot M hM) := by
  classical
  have : Finite V' := hM.finite_vertices
  have : Finite E' := hM.finite_arcs
  have hMr0 : ∀ e, M.graph.target e ≠ M.root := hM.target_ne_root
  have hreach_root : ∀ a, M.graph.Reaches a M.root → a = M.root := fun a h => by
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, -, f, -, hf⟩
    · exact h.symm
    · exact absurd hf (hMr0 f)
  have hKout : ∀ v, (contractRoot M hM).graph.outdegree v = M.graph.outdegree v.1 := fun v =>
    Set.ncard_congr'
      { toFun := fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩
        invFun := fun e => ⟨⟨e.1, fun h => v.2 ⟨e.2.symm.trans h.1, h.2⟩⟩, Subtype.ext e.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hKin : ∀ v, (∀ e, M.graph.target e = v.1 →
        ¬ (M.graph.source e = M.root ∧ M.graph.outdegree M.root = 1)) →
      (contractRoot M hM).graph.indegree v = M.graph.indegree v.1 := fun v hv =>
    Set.ncard_congr'
      { toFun := fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩
        invFun := fun e => ⟨⟨e.1, hv e.1 e.2⟩, Subtype.ext e.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  -- a path of `M` from a node of `K = contractRoot M hM` is a path of `K`
  have hlift : ∀ a (ha : ¬ (a = M.root ∧ M.graph.outdegree M.root = 1)) b
      (hb : ¬ (b = M.root ∧ M.graph.outdegree M.root = 1)),
      M.graph.Reaches a b → (contractRoot M hM).graph.Reaches ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a ha b hb hab
    induction hab with
    | refl => exact .refl
    | @tail y b hay hyb ih =>
      have hy : ¬ (y = M.root ∧ M.graph.outdegree M.root = 1) := fun h =>
        ha ⟨hreach_root a (h.1 ▸ hay), h.2⟩
      obtain ⟨f, hfs, hft⟩ := hyb
      exact (ih hy).tail ⟨⟨f, fun h => hy ⟨hfs.symm.trans h.1, h.2⟩⟩, Subtype.ext hfs,
        Subtype.ext hft⟩
  have hacyc : (contractRoot M hM).graph.IsAcyclic := fun v h => hM.acyclic v.1
    (Relation.TransGen.lift Subtype.val
      (fun a b ⟨e, hs, ht⟩ => ⟨e.1, congrArg Subtype.val hs, congrArg Subtype.val ht⟩) v v h)
  have hleafinj : Function.Injective (contractRoot M hM).leaf := fun x y h =>
    hM.leaf_injective (congrArg Subtype.val h)
  have hKleaves : ∀ v, (contractRoot M hM).graph.outdegree v = 0 ↔
      ∃ x, (contractRoot M hM).leaf x = v := fun v => by
    rw [hKout]
    exact (hM.leaves v.1).trans ⟨fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩,
      fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩⟩
  rcases hMroot with hP1 | hP2
  · -- the root of `M` has one child `c`, which is the root of `contractRoot M hM`
    obtain ⟨e₀, he₀⟩ := (M.graph.outdegree_eq_one_iff _).mp hP1
    have hKroot : (contractRoot M hM).root.1 = M.graph.target e₀ := by
      show (contractRoot M hM).root.1 = _
      simp only [contractRoot, dite_eq_left hP1]
      refine congrArg M.graph.target ((he₀ _).mp ?_)
      exact Set.Nonempty.some_mem (s := {e | M.graph.source e = M.root}) _
    have hcr : M.graph.target e₀ ≠ M.root := hMr0 e₀
    have hcreach : ∀ v, v ≠ M.root → M.graph.Reaches (M.graph.target e₀) v := fun v hv => by
      rcases Relation.ReflTransGen.cases_head (hM.root_reaches v) with h | ⟨b, ⟨g, hg, rfl⟩, hb⟩
      · exact absurd h.symm hv
      · rwa [(he₀ g).mp hg] at hb
    -- `c` is not a taxon: two taxa are below it
    have hcout0 : M.graph.outdegree (M.graph.target e₀) ≠ 0 := fun h => by
      have h₁ := M.graph.eq_of_reaches_of_outdegree_eq_zero
        (hcreach _ (M.leaf_ne_root hM z₁)) h
      have h₂ := M.graph.eq_of_reaches_of_outdegree_eq_zero
        (hcreach _ (M.leaf_ne_root hM z₂)) h
      exact hleaves (hM.leaf_injective (h₁.trans h₂.symm))
    -- `c` has the root as its only parent, so it has two children
    have hcin : ∀ f, M.graph.target f = M.graph.target e₀ → f = e₀ := fun f hf => by
      by_contra hfe
      have hfs : M.graph.source f ≠ M.root := fun h => hfe ((he₀ f).mp h)
      exact hM.acyclic _ (Relation.TransGen.tail' (hcreach _ hfs) ⟨f, rfl, hf⟩)
    have hcin1 : M.graph.indegree (M.graph.target e₀) = 1 :=
      (M.graph.indegree_eq_one_iff _).mpr ⟨e₀, fun f => ⟨hcin f, fun h => h ▸ rfl⟩⟩
    have hcout : M.graph.outdegree (M.graph.target e₀) = 2 := by
      have := hMdeg _ hcr hcout0
      have := hMchain (M.graph.target e₀)
      omega
    have hKin' : ∀ v : {v // ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)},
        v.1 ≠ M.graph.target e₀ → (contractRoot M hM).graph.indegree v = M.graph.indegree v.1 :=
      fun v hvc =>
      hKin v fun e he h => hvc (he.symm.trans (congrArg M.graph.target ((he₀ e).mp h.1)))
    have hvr : ∀ v : {v // ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)}, v.1 ≠ M.root :=
      fun v h => v.2 ⟨h, hP1⟩
    have hvc : ∀ v, v ≠ (contractRoot M hM).root → v.1 ≠ M.graph.target e₀ :=
      fun v hv h => hv (Subtype.ext (h.trans hKroot.symm))
    refine ⟨⟨Subtype.finite, Subtype.finite, hM.finite_taxa, hacyc, fun v => ?_, ?_,
      fun v hv => ?_, hleafinj, fun x => ?_, hKleaves⟩, ?_, fun v hv h0 => ?_⟩
    · have := hlift _ (fun h => hcr h.1) v.1 v.2 (hcreach v.1 (hvr v))
      rwa [show (⟨M.graph.target e₀, fun h => hcr h.1⟩ :
          {v // ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)}) = (contractRoot M hM).root from
        Subtype.ext hKroot.symm] at this
    · rw [DirectedMultigraph.indegree_eq_zero_iff]
      intro e he
      have : e.1 = e₀ := hcin _ ((congrArg Subtype.val he).trans hKroot)
      exact e.2 ⟨by rw [this]; exact (he₀ e₀).mpr rfl, hP1⟩
    · rw [hKin' v (hvc v hv)]
      exact hM.nonroot_indegree _ (hvr v)
    · have hxc : ((contractRoot M hM).leaf x).1 ≠ M.graph.target e₀ := fun h => hcout0 (by
        rw [← h]
        exact (hM.leaves _).mpr ⟨x, rfl⟩)
      rw [hKin' _ hxc]
      exact hM.leaf_indegree x
    · rw [hKout, hKroot, hcout]
    · rw [hKin' v (hvc v hv), hKout]
      rw [hKout] at h0
      exact hMdeg _ (hvr v) h0
  · -- the root of `M` has two children: `contractRoot M hM` is `M`
    have hnP : ¬ M.graph.outdegree M.root = 1 := by omega
    have hKroot : (contractRoot M hM).root.1 = M.root := by
      show (contractRoot M hM).root.1 = _
      simp only [contractRoot, dite_eq_right hnP]
    have hKin'' : ∀ v, (contractRoot M hM).graph.indegree v = M.graph.indegree v.1 := fun v =>
      hKin v fun _ _ h => hnP h.2
    have hvr : ∀ v, v ≠ (contractRoot M hM).root → v.1 ≠ M.root :=
      fun v hv h => hv (Subtype.ext (h.trans hKroot.symm))
    refine ⟨⟨Subtype.finite, Subtype.finite, hM.finite_taxa, hacyc, fun v => ?_, ?_,
      fun v hv => ?_, hleafinj, fun x => ?_, hKleaves⟩, ?_, fun v hv h0 => ?_⟩
    · have := hlift _ (fun h => hnP h.2) v.1 v.2 (hM.root_reaches v.1)
      rwa [show (⟨M.root, fun h => hnP h.2⟩ :
          {v // ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)}) = (contractRoot M hM).root from
        Subtype.ext hKroot.symm] at this
    · rw [hKin'', hKroot]
      exact hM.root_indegree
    · rw [hKin'']
      exact hM.nonroot_indegree _ (hvr v hv)
    · rw [hKin'']
      exact hM.leaf_indegree x
    · rw [hKout, hKroot, hP2]
    · rw [hKin'', hKout]
      rw [hKout] at h0
      exact hMdeg _ (hvr v hv) h0

/-- `N⁺_Z` is a binary rooted network, for at least two taxa: the ancestral network keeps the
indegrees of `N` and its taxa, suppression removes the nodes of indegree and outdegree one, and when
the root is left with one child, that child is a tree node, which contracting the edge at the root
makes the root (`contractRoot_isBinaryRootedNetwork`). -/
theorem inducedRooted_isBinaryRootedNetwork {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    {Z : Set X} (hZ : Z.Nontrivial) :
    IsBinaryRootedNetwork (inducedRooted N hN.1 Z hZ.nonempty) := by
  classical
  have : Finite V := hN.1.finite_vertices
  have : Finite E := hN.1.finite_arcs
  have hA := N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty
  set M := ancestralSuppressed N hN.1 Z hZ.nonempty with hM_def
  have hM : M.IsPhylogenetic := ancestralSuppressed_isPhylogenetic hN.1 Z hZ.nonempty
  have : Finite (N.AncestralArc Z) := Subtype.finite
  -- the degrees of `M`: those of `N` for the indegree, at most those of `N` for the outdegree
  have hMin : ∀ v, M.graph.indegree v = N.graph.indegree v.1.1 := fun v =>
    (suppress_indegree hA v).trans (N.ancestralGraph_indegree Z v.1)
  have hMout : ∀ v, M.graph.outdegree v ≤ N.graph.outdegree v.1.1 := fun v =>
    (suppress_outdegree hA v).le.trans (Set.ncard_le_ncard_of_injOn (fun e => e.1)
      (fun _ he => congrArg Subtype.val he) (fun _ _ _ _ h => Subtype.ext h) (Set.toFinite _))
  have hMchain : ∀ v, ¬ (M.graph.indegree v = 1 ∧ M.graph.outdegree v = 1) :=
    suppress_not_isChainVertex hA
  have hMroot_val : M.root.1.1 = N.root := rfl
  have hMne : ∀ v : _, v ≠ M.root → v.1.1 ≠ N.root := fun v hv h =>
    hv (Subtype.ext (Subtype.ext h))
  -- `M` is binary but for a root of outdegree one
  have hMdeg : ∀ v, v ≠ M.root → M.graph.outdegree v ≠ 0 →
      M.graph.indegree v + M.graph.outdegree v = 3 := by
    intro v hv h0
    have hr := hMne v hv
    have h1 := hN.1.nonroot_indegree _ hr
    have hle := hMout v
    have h3 := hN.2.2 _ hr (by omega)
    have := hMchain v
    rw [hMin] at this ⊢
    omega
  have hMroot : M.graph.outdegree M.root = 1 ∨ M.graph.outdegree M.root = 2 := by
    have hle := hMout M.root
    rw [hMroot_val, hN.2.1] at hle
    have h0 : M.graph.outdegree M.root ≠ 0 := fun h => by
      obtain ⟨x, hx⟩ := (hM.leaves _).mp h
      exact M.leaf_ne_root hM x hx
    omega
  obtain ⟨z₁, hz₁, z₂, hz₂, hz₁₂⟩ := id hZ
  exact contractRoot_isBinaryRootedNetwork hM hMchain hMdeg hMroot
    (z₁ := ⟨z₁, hz₁⟩) (z₂ := ⟨z₂, hz₂⟩) fun h => hz₁₂ (congrArg Subtype.val h)

/-! ### Definition 8 -/

/-- **Definition 8** (`def:inducemrcanetontaxa`): the *induced LSA network* `N⊕_Z`: `N⁺_Z` without what
is above `LSA(Z)`, rooted at `LSA(Z)`. This is `RootedNetwork.inducedNetwork`. -/
abbrev inducedLSA (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (Z : Set X) (hZ : Z.Nontrivial) :=
  inducedNetwork hN Z hZ

theorem inducedLSA_isBinaryRootedNetwork {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    {Z : Set X} (hZ : Z.Nontrivial) : IsBinaryRootedNetwork (inducedLSA N hN.1 Z hZ) :=
  ⟨inducedNetwork_isPhylogenetic hN.1 hZ, inducedNetwork_isBinary hN.1 hN.2 hZ⟩

/-! ### The semidirected networks -/

/-- `N⁻` (Definition 5), for a binary rooted network on at least two taxa. -/
abbrev unrooted (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X) :=
  semidirected hN.1 hN.2 hX

/-- The metric of `N⁻` (Definition 6). -/
abbrev unrootedMetric (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X)
    (θ : MetricData E) :=
  semidirectedMetric hN.1 hN.2 hX θ

/-- **Lemma 3** (`lem:assos`), for unrooted networks: in `N⁻` of a binary level-1 rooted network, a
cycle `C` contains exactly one hybrid node (a node entered by two hybrid edges), the hybrid edges
entering a node of `C` are edges of `C`, and two cycles with a common node are the same.

Proved from `lemma3` for `N`: the edges of `C` are edges of `N` below `LSA(X)`, the edge of `N⁻`
that merges the two edges of `LSA(X)` standing for both, and they form a cycle of `N` (through
`LSA(X)` when `C` has the merged edge); the hybrid edges of `N⁻` are those of `N`, and the nodes of
`N⁻` keep their parents. -/
theorem lemma3_unrooted [Finite E] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) :
    (∃! v, v ∈ cycleNodes (unrooted N hN hX).graph C ∧
      ∃ h₁ h₂, h₁ ≠ h₂ ∧ (unrooted N hN hX).IsDirected h₁ ∧ (unrooted N hN hX).IsDirected h₂ ∧
        (unrooted N hN hX).graph.target h₁ = v ∧ (unrooted N hN hX).graph.target h₂ = v) ∧
      (∀ v ∈ cycleNodes (unrooted N hN hX).graph C, ∀ h, (unrooted N hN hX).IsDirected h →
        (unrooted N hN hX).graph.target h = v → h ∈ C) ∧
      ∀ C', IsCycle (unrooted N hN hX).graph C' →
        (cycleNodes (unrooted N hN hX).graph C ∩ cycleNodes (unrooted N hN hX).graph C').Nonempty →
        C = C' := by
  classical
  set G := unrooted N hN hX with hG_def
  set m := lsa hN.1 Set.univ Set.univ_nonempty with hm_def
  have hst : N.IsStableAncestor Set.univ m := (lsa_spec hN.1 Set.univ Set.univ_nonempty).1
  set e₀ := rootTreeArc hN.1 hN.2 hX with he₀_def
  have he₀s : N.graph.source e₀.1 = m := congrArg Subtype.val (rootTreeArc_spec hN.1 hN.2 hX).1
  have hindeg : ∀ v : N.belowVertices m Set.univ, v.1 ≠ m →
      (lsaPlus hN.1 hX).graph.indegree v = N.graph.indegree v.1 := fun v hv =>
    belowNetwork_indegree (hl := lsa_mem_ancestralVertices hN.1 Set.univ_nonempty)
      (hleaf := fun _ hx => hst.reaches_leaf hN.1 hx) hN.1 hst v hv
  have he₀t : N.graph.indegree (N.graph.target e₀.1) = 1 := by
    have h := (rootTreeArc_spec hN.1 hN.2 hX).2
    unfold IsTreeArc at h
    rwa [hindeg _ (target_ne_of_mem_belowArcs hN.1 e₀)] at h
  -- the nodes and edges of `N⁻` as nodes and edges of `N`
  let ι : SemidirectedVertex hN.1 hX → V := fun u => u.1.1
  let κ : SemidirectedArc hN.1 hN.2 hX → E := fun c => c.1.1
  have hι : Function.Injective ι := fun u u' h => Subtype.ext (Subtype.ext h)
  have hκ : Function.Injective κ := fun c c' h => Subtype.ext (Subtype.ext h)
  have hιm : ∀ u, ι u ≠ m := fun u h => u.2 (Subtype.ext h)
  have hκe₀ : ∀ c, κ c ≠ e₀.1 := fun c h => c.2 (Subtype.ext h)
  have htgt : ∀ c, ι (G.graph.target c) = N.graph.target (κ c) := fun c => rfl
  have hsrc : ∀ c, (N.graph.source (κ c) ≠ m ∧ ι (G.graph.source c) = N.graph.source (κ c)) ∨
      (N.graph.source (κ c) = m ∧ ι (G.graph.source c) = N.graph.target e₀.1) := by
    intro c
    by_cases h : (lsaPlus hN.1 hX).graph.source c.1 = (lsaPlus hN.1 hX).root
    · right
      refine ⟨congrArg Subtype.val h, ?_⟩
      simp only [ι, G, semidirected, unrootAt, dite_eq_left h]
      rfl
    · left
      refine ⟨fun h' => h (Subtype.ext h'), ?_⟩
      simp only [ι, G, semidirected, unrootAt, dite_eq_right h]
      rfl
  have hdir : ∀ c, G.IsDirected c ↔ N.IsHybridArc (κ c) := fun c => by
    show 2 ≤ (lsaPlus hN.1 hX).graph.indegree _ ↔ _
    rw [hindeg _ (target_ne_of_mem_belowArcs hN.1 c.1)]
    rfl
  -- the edges of `N⁻` leaving `m` in `N`: only the edge merged with `e₀`
  have hm_out : ∀ c c', N.graph.source (κ c) = m → N.graph.source (κ c') = m → c = c' := by
    intro c c' hc hc'
    by_contra hne
    have hne' : κ c ≠ κ c' := fun h => hne (hκ h)
    have hsub : ({e₀.1, κ c, κ c'} : Set E) ⊆ {f | N.graph.source f = m} := by
      rintro f (rfl | rfl | rfl)
      · exact he₀s
      · exact hc
      · exact hc'
    have h3 : ({e₀.1, κ c, κ c'} : Set E).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair hne']
      rintro (h | h)
      · exact hκe₀ c h.symm
      · exact hκe₀ c' h.symm
    have := h3 ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
    have := hN.outdegree_le_two m
    unfold DirectedMultigraph.outdegree at *
    omega
  -- the edges of `N` of a set of edges of `N⁻`: `e₀` is added to the edge leaving `m`
  let hat : Set (SemidirectedArc hN.1 hN.2 hX) → Set E := fun D =>
    {f | ∃ c ∈ D, f = κ c ∨ (N.graph.source (κ c) = m ∧ f = e₀.1)}
  have hmem_hat : ∀ D c, κ c ∈ hat D ↔ c ∈ D := by
    intro D c
    constructor
    · rintro ⟨c', hc', h | ⟨-, h⟩⟩
      · exact hκ h ▸ hc'
      · exact absurd h (hκe₀ c)
    · intro hc
      exact ⟨c, hc, Or.inl rfl⟩
  have hjoin : ∀ c u w, N.graph.source (κ c) ≠ m → Joins G.graph c u w →
      Joins N.graph (κ c) (ι u) (ι w) := by
    intro c u w hcm h
    have hs : ι (G.graph.source c) = N.graph.source (κ c) :=
      ((hsrc c).resolve_right fun h => hcm h.1).2
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨hs.symm.trans (congrArg ι h₁), (htgt c).symm.trans (congrArg ι h₂)⟩
    · exact Or.inr ⟨hs.symm.trans (congrArg ι h₁), (htgt c).symm.trans (congrArg ι h₂)⟩
  -- a cycle of `N⁻` gives a cycle of `N`, through `m` if it has the merged edge
  have hT : ∀ D, IsCycle G.graph D → IsCycle N.graph (hat D) := by
    rintro D ⟨k, v, e, hD, rfl⟩
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hD.pos; omega⟩
    by_cases hj : ∃ j, N.graph.source (κ (e j)) = m
    · obtain ⟨j, hj⟩ := hj
      -- read the cycle so that the merged edge is last
      have hR := hD.rotate (j + 1)
      have hlast : e (Fin.last n + (j + 1)) = e j := by
        congr 1
        rw [add_comm j 1, ← add_assoc, Fin.last_add_one, zero_add]
      have hrange : Set.range (fun i => e (i + (j + 1))) = Set.range e :=
        (Equiv.addRight (j + 1)).surjective.range_comp e
      have hP := hR.isPathOf
      have hother : ∀ l : Fin n, N.graph.source (κ (e (l.castSucc + (j + 1)))) ≠ m := fun l h => by
        have h' := hR.injective_edge ((hm_out _ _ h hj).trans hlast.symm)
        exact (Fin.castSucc_lt_last l).ne h'
      have hPN : IsPathOf N.graph Set.univ n (fun i => ι (v (i + (j + 1))))
          (fun l => κ (e (l.castSucc + (j + 1)))) :=
        ⟨fun _ => trivial, fun l => hjoin _ _ _ (hother l) (hP.link l), hι.comp hP.injective⟩
      have hjl := hR.joins (Fin.last n)
      simp only [finRotate_last, hlast] at hjl
      have hs := ((hsrc (e j)).resolve_left fun h => h.1 hj).2
      have hz : m ∉ Set.range (fun i => ι (v (i + (j + 1)))) := fun ⟨i, hi⟩ => hιm _ hi
      have hnot₀ : e₀.1 ∉ Set.range (fun l : Fin n => κ (e (l.castSucc + (j + 1)))) :=
        fun ⟨l, hl⟩ => hκe₀ _ hl
      have hnotj : κ (e j) ∉ Set.range (fun l : Fin n => κ (e (l.castSucc + (j + 1)))) :=
        fun ⟨l, hl⟩ => hother l (by simp only at hl; rw [hl]; exact hj)
      have hne₀j : e₀.1 ≠ κ (e j) := fun h => hκe₀ _ h.symm
      have hcalc : hat (Set.range e) = insert e₀.1 (insert (κ (e j))
          (Set.range fun l : Fin n => κ (e (l.castSucc + (j + 1))))) := by
        ext f
        constructor
        · rintro ⟨c, hc, rfl | ⟨-, rfl⟩⟩
          · rw [← hrange] at hc
            obtain ⟨i, rfl⟩ := hc
            induction i using Fin.lastCases with
            | last => exact Or.inr (Or.inl (by simp only; rw [hlast]))
            | cast l => exact Or.inr (Or.inr ⟨l, rfl⟩)
          · exact Or.inl rfl
        · rintro (rfl | rfl | ⟨l, rfl⟩)
          · exact ⟨e j, ⟨j, rfl⟩, Or.inr ⟨hj, rfl⟩⟩
          · exact ⟨e j, ⟨j, rfl⟩, Or.inl rfl⟩
          · exact ⟨_, ⟨_, rfl⟩, Or.inl rfl⟩
      rw [hcalc]
      rcases hjl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · -- the path ends at the child of `e₀`: close it by `e₀` and the merged edge
        have hend : ι (v (Fin.last n + (j + 1))) = N.graph.target e₀.1 := by rw [← h₁]; exact hs
        have h0 : ι (v (0 + (j + 1))) = N.graph.target (κ (e j)) := by rw [← h₂]; rfl
        exact hPN.isCycle_insert_insert hz hnotj hne₀j (Or.inr ⟨he₀s, hend.symm⟩)
          (Or.inl ⟨hj, h0.symm⟩)
      · -- the path starts at the child of `e₀`: close it by the merged edge and `e₀`
        have h0 : ι (v (0 + (j + 1))) = N.graph.target e₀.1 := by rw [← h₁]; exact hs
        have hend : ι (v (Fin.last n + (j + 1))) = N.graph.target (κ (e j)) := by rw [← h₂]; rfl
        rw [Set.insert_comm]
        exact hPN.isCycle_insert_insert hz hnot₀ hne₀j.symm (Or.inr ⟨hj, hend.symm⟩)
          (Or.inl ⟨he₀s, h0.symm⟩)
    · push Not at hj
      refine ⟨n + 1, fun i => ι (v i), fun i => κ (e i), ⟨hD.pos, fun i => hjoin _ _ _ (hj i)
        (hD.joins i), hι.comp hD.injective_node, hκ.comp hD.injective_edge⟩, ?_⟩
      ext f
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, ⟨i, rfl⟩, Or.inl rfl⟩
      · rintro ⟨c, ⟨i, rfl⟩, rfl | ⟨h, -⟩⟩
        · exact ⟨i, rfl⟩
        · exact absurd h (hj i)
  -- the nodes of a cycle of `N⁻` are nodes of the cycle of `N`
  have hcn : ∀ D u, u ∈ cycleNodes G.graph D → ι u ∈ cycleNodes N.graph (hat D) := by
    rintro D u ⟨c, hc, hu | hu⟩
    · rcases hsrc c with ⟨-, h⟩ | ⟨hm', h⟩
      · exact ⟨κ c, ⟨c, hc, Or.inl rfl⟩, Or.inl (h.symm.trans (congrArg ι hu))⟩
      · exact ⟨e₀.1, ⟨c, hc, Or.inr ⟨hm', rfl⟩⟩, Or.inr (h.symm.trans (congrArg ι hu))⟩
    · exact ⟨κ c, ⟨c, hc, Or.inl rfl⟩, Or.inr ((htgt c).symm.trans (congrArg ι hu))⟩
  -- a node of `N⁻` entered by two hybrid edges is a hybrid node of `N`
  have hin2 : ∀ u, (∃ h₁ h₂, h₁ ≠ h₂ ∧ G.IsDirected h₁ ∧ G.IsDirected h₂ ∧
      G.graph.target h₁ = u ∧ G.graph.target h₂ = u) → N.graph.indegree (ι u) = 2 := by
    rintro u ⟨h₁, h₂, hne, -, -, ht₁, ht₂⟩
    refine le_antisymm (hN.indegree_le_two _) ?_
    rw [← Set.ncard_pair (fun h => hne (hκ h))]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro f (rfl | rfl)
    · exact (htgt h₁).symm.trans (congrArg ι ht₁)
    · exact (htgt h₂).symm.trans (congrArg ι ht₂)
  obtain ⟨⟨w, ⟨hwC, hw2⟩, hwuniq⟩, h2N, h3N⟩ := lemma3 hN h1 (hT C hC)
  refine ⟨?_, fun u hu h hh ht => ?_, fun C' hC' ⟨u, huC, huC'⟩ => ?_⟩
  · -- the hybrid node of the cycle of `N`, with its two hybrid edges, is in `N⁻`
    obtain ⟨g₁, g₂, hne, hs⟩ := Set.ncard_eq_two.mp hw2
    have hg₁ : N.graph.target g₁ = w := by
      have : g₁ ∈ {f | N.graph.target f = w} := by rw [hs]; exact Or.inl rfl
      exact this
    have hg₂ : N.graph.target g₂ = w := by
      have : g₂ ∈ {f | N.graph.target f = w} := by rw [hs]; exact Or.inr rfl
      exact this
    have hhyb : ∀ g, N.graph.target g = w → N.IsHybridArc g := fun g hg => by
      unfold IsHybridArc
      rw [hg, hw2]
    have hlift : ∀ g, N.graph.target g = w → g ∈ hat C → ∃ c ∈ C, κ c = g := by
      rintro g hg ⟨c, hc, rfl | ⟨-, rfl⟩⟩
      · exact ⟨c, hc, rfl⟩
      · rw [hg, hw2] at he₀t
        exact absurd he₀t (by norm_num)
    obtain ⟨c₁, hc₁, rfl⟩ := hlift g₁ hg₁ (h2N w hwC hw2 g₁ hg₁)
    obtain ⟨c₂, hc₂, rfl⟩ := hlift g₂ hg₂ (h2N w hwC hw2 g₂ hg₂)
    have hu₂ : G.graph.target c₂ = G.graph.target c₁ := hι (by rw [htgt, htgt, hg₁, hg₂])
    refine ⟨G.graph.target c₁, ⟨⟨c₁, hc₁, Or.inr rfl⟩, c₁, c₂, fun h => hne (h ▸ rfl),
      (hdir c₁).mpr (hhyb _ hg₁), (hdir c₂).mpr (hhyb _ hg₂), rfl, hu₂⟩, ?_⟩
    rintro u ⟨huC, hh⟩
    refine hι ((hwuniq _ ⟨hcn C u huC, hin2 u hh⟩).trans (hwuniq _ ⟨hcn C _ ⟨c₁, hc₁, Or.inr rfl⟩,
      ?_⟩).symm)
    rw [htgt, hg₁]
    exact hw2
  · -- a hybrid edge entering a node of the cycle is an edge of the cycle
    have hu2 : N.graph.indegree (ι u) = 2 := by
      refine le_antisymm (hN.indegree_le_two _) ?_
      have := (hdir h).mp hh
      unfold IsHybridArc at this
      rwa [← htgt, ht] at this
    exact (hmem_hat C h).mp (h2N _ (hcn C u hu) hu2 (κ h) ((htgt h).symm.trans (congrArg ι ht)))
  · -- two cycles with a common node
    have hEq := h3N (hat C') (hT C' hC') ⟨ι u, hcn C u huC, hcn C' u huC'⟩
    ext c
    rw [← hmem_hat C c, ← hmem_hat C' c, hEq]

/-- **Definition 10** (`def:inducenetontaxa`): the *induced unrooted network* `(N⁻)_Z`: retain only the
edges of `N⁻` on simple treks between pairs of taxa of `Z`, then suppress all nodes of degree two. -/
def inducedUnrooted {V' E' : Type*} (G : SemidirectedNetwork V' E' X) (Z : Set X) :=
  suppress (restrict G (trekEdges G Z) Z)

/-- The metric of `(N⁻)_Z`: on the retained edges, that of `N⁻`; a suppressed chain has the sum of the
lengths of its edges and the inheritance probability of its hybrid edges. -/
def inducedUnrootedMetric {V' E' : Type*} (G : SemidirectedNetwork V' E' X) (Z : Set X)
    (θ : MetricData E') :=
  suppressMetric (restrict G (trekEdges G Z) Z) ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩

/-- The metric of `N⁺_Z`: on the retained edges, that of `N⁺`; a suppressed chain has the sum of the
lengths and the product of the inheritance probabilities of its edges (the library's
`RootedNetwork.suppressMetric`). -/
def inducedRootedMetric [Finite E] (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (Z : Set X)
    (hZ : Z.Nonempty) (θ : MetricData E) :
    MetricData {e // ¬ ((ancestralSuppressed N hN Z hZ).graph.source e =
      (ancestralSuppressed N hN Z hZ).root ∧
        (ancestralSuppressed N hN Z hZ).graph.outdegree (ancestralSuppressed N hN Z hZ).root = 1)} :=
  have : Fintype (N.AncestralArc Z) := Fintype.ofFinite _
  let μ := (N.ancestralNetwork Z hZ hN.root_reaches).suppressMetric
    ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩
  ⟨fun e => μ.length e.1, fun e => μ.inheritance e.1⟩

/-- **Proposition 1** (`prop::ancestralinduced`): for a binary rooted network `N` and a set `Z` of at
least two taxa, `(N⁻)_Z` and `(N⁺_Z)⁻` are isomorphic as leaf-labelled semidirected networks;
`proposition1_metric` gives the isomorphism of metric networks. The paper allows any `Z ⊆ X`; with one
taxon the LSA is a leaf, which Definition 5 cannot suppress, so `(N⁺_Z)⁻` is defined only for at least
two taxa. -/
theorem proposition1 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X)
    {Z : Set X} (hZ : Z.Nontrivial) :
    Nonempty (SDIso (inducedUnrooted (unrooted N hN hX) Z)
      (unrooted (inducedRooted N hN.1 Z hZ.nonempty) (inducedRooted_isBinaryRootedNetwork hN hZ)
        hZ.coe_sort)) := by
  sorry

/-- **Proposition 1**, for metric networks: `(N⁻)_Z` and `(N⁺_Z)⁻`, with their metrics, are
isomorphic. -/
theorem proposition1_metric [Fintype E] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (hX : Nontrivial X) {θ : MetricData E} (hθ : IsMetricNetwork N θ) {Z : Set X}
    (hZ : Z.Nontrivial) :
    Nonempty (SDMetricIso (inducedUnrooted (unrooted N hN hX) Z)
      (inducedUnrootedMetric (unrooted N hN hX) Z (unrootedMetric N hN hX θ))
      (unrooted (inducedRooted N hN.1 Z hZ.nonempty) (inducedRooted_isBinaryRootedNetwork hN hZ)
        hZ.coe_sort)
      (unrootedMetric _ (inducedRooted_isBinaryRootedNetwork hN hZ) hZ.coe_sort
        (inducedRootedMetric N hN.1 Z hZ.nonempty θ))) := by
  sorry

/-! ### Appendix -/

/-- A rooted network as a semidirected network in which every edge is directed. -/
def asSemidirected (N : RootedNetwork V E X) : SemidirectedNetwork V E X :=
  ⟨N.graph, fun _ => True, N.leaf⟩

/-- **Lemma 17** (`lem::trekmrca`): in a binary rooted network, an edge `e` below `LSA(Z)` with a
descendant in `Z` lies on a simple trek of `N⁺` between two taxa `x, y ∈ Z` whose edges are all below
`LSA(Z)`. -/
theorem lemma17 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {Z : Set X}
    (hZ : Z.Nonempty) {e : E} (he : N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source e))
    (hdesc : ∃ z ∈ Z, N.graph.Reaches (N.graph.target e) (N.leaf z)) :
    ∃ x ∈ Z, ∃ y ∈ Z, ∃ t P₁ P₂, IsSimpleTrek (asSemidirected N) (N.leaf x) (N.leaf y) t P₁ P₂ ∧
      e ∈ P₁ ∪ P₂ ∧ ∀ f ∈ P₁ ∪ P₂, N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source f) := by
  sorry

/-! ### Quartet networks -/

/-- `Q⊕_s`: the induced LSA network on a set `s` of four taxa. -/
abbrev quartetLSA (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (s : Finset X) (hs : s.card = 4) :=
  inducedLSA N hN (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega))

/-- `Q⊕_s` is a binary rooted network. -/
theorem quartetLSA_isBinaryRootedNetwork {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    {s : Finset X} (hs : s.card = 4) : IsBinaryRootedNetwork (quartetLSA N hN.1 s hs) :=
  inducedLSA_isBinaryRootedNetwork hN _

/-- `Q⁻_s`: the induced unrooted quartet network on a set `s` of four taxa, taken as `(Q⊕_s)⁻`
(Proposition 1). -/
abbrev quartetUnrooted (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (s : Finset X)
    (hs : s.card = 4) :=
  unrooted (quartetLSA N hN.1 s hs) (quartetLSA_isBinaryRootedNetwork hN hs)
    (Finset.one_lt_card_iff_nontrivial.mp (by omega)).coe_sort

end Banos2019
