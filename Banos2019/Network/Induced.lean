module

public import Banos2019.Network.TrekArc
public import Banos2019.Network.Proposition1
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

/-- `N⁺_Z` is a binary rooted network, for at least two taxa. -/
theorem inducedRooted_isBinaryRootedNetwork {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    {Z : Set X} (hZ : Z.Nontrivial) :
    IsBinaryRootedNetwork (inducedRooted N hN.1 Z hZ.nonempty) := by
  sorry

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
entering a node of `C` are edges of `C`, and two cycles with a common node are the same. -/
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
  sorry

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

/-! ### Appendix -/

/-- A rooted network as a semidirected network in which every edge is directed. -/
def asSemidirected (N : RootedNetwork V E X) : SemidirectedNetwork V E X :=
  ⟨N.graph, fun _ => True, N.leaf⟩

/-- **Lemma 17** (`lem::trekmrca`): in a binary rooted network, an edge `e` below `LSA(Z)` with a
descendant in `Z` lies on a simple trek of `N⁺` between two taxa `x, y ∈ Z` whose edges are all below
`LSA(Z)`.

The proof is the paper's: `y` comes from Lemma 2; when `y` is not below `e`, the trek is
`trek_of_not_below`; otherwise `trek_of_config` is the induction on the number of nodes below `e`
common to the two paths, with the five cases on the position of `w` in `trek_mainStep`. -/
theorem lemma17 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {Z : Set X}
    (hZ : Z.Nonempty) {e : E} (he : N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source e))
    (hdesc : ∃ z ∈ Z, N.graph.Reaches (N.graph.target e) (N.leaf z)) :
    ∃ x ∈ Z, ∃ y ∈ Z, ∃ t P₁ P₂, IsSimpleTrek (asSemidirected N) (N.leaf x) (N.leaf y) t P₁ P₂ ∧
      e ∈ P₁ ∪ P₂ ∧ ∀ f ∈ P₁ ∪ P₂, N.graph.Reaches (lsa hN.1 Z hZ) (N.graph.source f) := by
  have hA := hN.1.acyclic
  have : Finite V := hN.1.finite_vertices
  let _ : PartialOrder V := reachOrderOfIsAcyclic N.graph hA
  have hle : ∀ a b, N.graph.Reaches a b ↔ a ≤ b := fun _ _ => Iff.rfl
  obtain ⟨x, hx, hex⟩ := hdesc
  -- with one taxon, the LSA is the taxon, and no edge is below it
  by_cases hZ2 : Z.Nontrivial
  swap
  · exfalso
    have hZx : ∀ z ∈ Z, z = x := fun z hz => by
      by_contra hne
      exact hZ2 ⟨z, hz, x, hx, hne⟩
    have hst : N.IsStableAncestor Z (N.leaf x) := fun z hz hp => hp.2.1 (by rw [hZx z hz])
    exact hA _ (Relation.TransGen.trans_right (((lsa_spec hN.1 Z hZ).2 _ hst).trans he)
      (Relation.TransGen.head' ⟨e, rfl, rfl⟩ hex))
  -- Lemma 2: some `y ∈ Z` has `LSA(x, y) = LSA(Z)`
  obtain ⟨y, hy, hxy⟩ := lemma2 hN hZ2 hx
  rw [← hxy] at he ⊢
  set m := lsa hN.1 {x, y} (Set.insert_nonempty x {y})
  have hlsa := lsa_spec hN.1 {x, y} (Set.insert_nonempty x {y})
  have hmpaths : ∀ b, m ≤ b → b ≠ m → ∃ Z₀, (Z₀ = N.leaf x ∨ Z₀ = N.leaf y) ∧
      ∃ S P, IsDPath N.graph m Z₀ S P ∧ b ∉ S := by
    intro b hb hbm
    obtain ⟨z, hz, S, P, hP, hbS⟩ := exists_isDPath_avoiding hN.1 hlsa hb hbm
    refine ⟨N.leaf z, ?_, S, P, hP, hbS⟩
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · rw [Set.mem_singleton_iff.mp hz]
      exact Or.inr rfl
  have hmy : N.graph.Reaches m (N.leaf y) :=
    hlsa.1.reaches_leaf hN.1 (Set.mem_insert_of_mem x rfl)
  -- a path from `m` to a taxon below `e`, through `e`
  have hthrough : ∀ z, N.graph.Reaches (N.graph.target e) (N.leaf z) →
      ∃ S P, IsDPath N.graph m (N.leaf z) S P ∧ e ∈ P := by
    intro z hz
    obtain ⟨S₁, P₁, h₁⟩ := IsDPath.of_reaches he
    obtain ⟨S₂, P₂, h₂⟩ := IsDPath.of_reaches hz
    exact ⟨_, _, h₁.append (.cons e h₂), Or.inr (Set.mem_insert _ _)⟩
  obtain ⟨Sx, Px, hPx, hePx⟩ := hthrough x hex
  have key : HasTrekThrough N.graph m (N.leaf x) (N.leaf y) e := by
    by_cases hyb : N.graph.Reaches (N.graph.target e) (N.leaf y)
    · -- `y` below `e`: a path from `m` to `x` or `y` avoids the child of `e`
      have htm : N.graph.target e ≠ m := fun h =>
        not_reaches_target_source_of_isAcyclic hA e (h ▸ he)
      obtain ⟨Z₀, hZ₀, Sy, Py, hPy, hey⟩ :=
        hmpaths _ (he.tail ⟨e, rfl, rfl⟩) htm
      rcases hZ₀ with rfl | rfl
      · obtain ⟨Sx', Px', hPx', hePx'⟩ := hthrough y hyb
        exact (trek_of_config hle hA _ _ _ _ _ _ _
          (fun b h h' => (hmpaths b h h').imp fun _ h => ⟨h.1.symm, h.2⟩)
          hPx' hePx' hPy hey rfl).symm
      · exact trek_of_config hle hA _ _ _ _ _ _ _ hmpaths hPx hePx hPy hey rfl
    · -- `y` not below `e`
      obtain ⟨Sy, Py, hPy⟩ := IsDPath.of_reaches hmy
      exact trek_of_not_below hle hA hPx hePx hPy hyb
  obtain ⟨t, S₁, P₁, S₂, P₂, h₁, h₂, hS, heP, hmS⟩ := key
  refine ⟨x, hx, y, hy, t, P₁, P₂, ⟨S₁, S₂, ⟨h₁.isSDPath hA rfl, h₂.isSDPath hA rfl⟩, hS⟩, heP, ?_⟩
  rintro f (hf | hf)
  · exact hmS _ (Or.inl (h₁.ends_mem hf).1)
  · exact hmS _ (Or.inr (h₂.ends_mem hf).1)

/-- `contractRoot` contracts the edge at the root (Definition 7, step 3). -/
theorem isContraction_contractRoot (M : RootedNetwork V E X) (hM : M.IsPhylogenetic) :
    IsContraction M (contractRoot M hM) Subtype.val Subtype.val where
  inj_v := Subtype.val_injective
  inj_e := Subtype.val_injective
  source _ := rfl
  target _ := rfl
  range_v s := ⟨fun ⟨c, hc⟩ => hc ▸ c.2, fun h => ⟨⟨s, h⟩, rfl⟩⟩
  range_e a := ⟨fun ⟨e, he⟩ => he ▸ e.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  leaf _ := rfl
  root_one h := by
    simp only [contractRoot, h, ↓reduceDIte]
    exact ⟨_, Set.Nonempty.some_mem (s := {e | M.graph.source e = M.root}) _, rfl⟩
  root_ne h := by simp only [contractRoot, h, ↓reduceDIte]

/-- **Proposition 1** (`prop::ancestralinduced`): for a binary rooted network `N` and a set `Z` of at
least two taxa, `(N⁻)_Z` and `(N⁺_Z)⁻` are isomorphic as leaf-labelled semidirected networks;
`proposition1_metric` gives the isomorphism of metric networks. The paper allows any `Z ⊆ X`; with one
taxon the LSA is a leaf, which Definition 5 cannot suppress, so `(N⁺_Z)⁻` is defined only for at least
two taxa. -/
theorem proposition1 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X)
    {Z : Set X} (hZ : Z.Nontrivial) :
    Nonempty (SDIso (inducedUnrooted (unrooted N hN hX) Z)
      (unrooted (inducedRooted N hN.1 Z hZ.nonempty) (inducedRooted_isBinaryRootedNetwork hN hZ)
        hZ.coe_sort)) :=
  -- the edges of `N⁻` on simple treks between taxa of `Z` are those of the LSA network (by Lemma 17,
  -- `mem_trekEdges_iff`), and suppressing their nodes of degree two gives `(N⁺_Z)⁻`
  nonempty_sdIso_trekNet hN hX hZ (fun _ he hd => lemma17 hN hZ.nonempty he hd)
    (inducedRooted_isBinaryRootedNetwork hN hZ) Subtype.val Subtype.val
    (isContraction_contractRoot _ _)

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
        (inducedRootedMetric N hN.1 Z hZ.nonempty θ))) :=
  -- the same isomorphism; along a chain, lengths add, and the inheritance probability is that of the
  -- last arc, the others being tree arcs
  nonempty_sdMetricIso_trekNet hN hX hZ (fun _ he hd => lemma17 hN hZ.nonempty he hd)
    (inducedRooted_isBinaryRootedNetwork hN hZ) Subtype.val Subtype.val
    (isContraction_contractRoot _ _) θ hθ.1.2.2.1 _ fun e => by
      let _ : Fintype (N.AncestralArc Z) := Fintype.ofFinite _
      exact ⟨suppressMetric_length_ancestral hN.1 hZ.nonempty θ e.1,
        suppressMetric_inheritance_ancestral hN.1 hZ.nonempty θ e.1⟩

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
