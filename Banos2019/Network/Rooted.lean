module

public import Phylogenetics.Network.Semidirected

/-!
# Rooted networks and the lowest stable ancestor (Baños 2019, Sections 2.1 and 2.2)

The paper's networks are the library's `Phylogenetics.RootedNetwork`: a directed multigraph with named
arcs, a root and a labelling of the taxa. Definition 1 allows up to two edges between two nodes, as the
library does.

* `IsBinaryRootedNetwork` (Definition 1): `IsPhylogenetic` and `IsBinary`; `isBinaryRootedNetwork_iff`
  restates the clauses of Definition 1.
* `IsMetricNetwork` (Definition 2): positive edge lengths and inheritance probabilities in `(0, 1)` that
  sum to one at each hybrid node. The library's `MetricData` gives every arc an inheritance probability,
  and the coalescent reads it on tree arcs too, so a tree arc has inheritance probability `1`
  (`isMetricNetwork_iff`).
* `IsAbove` (Definition 3).
* The lowest stable ancestor (Definition 4) is the library's `RootedNetwork.lsa`, characterized by
  `RootedNetwork.IsLeastStableAncestor`; `isLeastStableAncestor_iff_def4` restates Definition 4.
* `lemma1`, `lemma2`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-- **Definition 1** (`def::network`): a *topological binary rooted phylogenetic network* on the taxa
`X`: a phylogenetic network (a finite directed acyclic graph whose root, of indegree `0`, reaches every
node, and whose sinks are exactly the leaves, labelled bijectively by `X`, each of indegree `1`) that is
binary (the root has outdegree `2`, every other node that is not a leaf has degree `3`). Up to two edges
may join the same two nodes. `isBinaryRootedNetwork_iff` gives the clauses of Definition 1. -/
def IsBinaryRootedNetwork (N : RootedNetwork V E X) : Prop :=
  N.IsPhylogenetic ∧ N.IsBinary

/-- **Definition 1, clause by clause**: a connected directed acyclic graph with root of indegree `0` and
outdegree `2`, leaves of indegree `1` and outdegree `0` labelled injectively by `X`, and every other node
a tree node (indegree `1`, outdegree `2`) or a hybrid node (indegree `2`, outdegree `1`). -/
theorem isBinaryRootedNetwork_iff (N : RootedNetwork V E X) :
    IsBinaryRootedNetwork N ↔
      Finite V ∧ Finite E ∧ Finite X ∧ N.graph.IsConnected ∧ N.graph.IsAcyclic ∧
        N.graph.indegree N.root = 0 ∧ N.graph.outdegree N.root = 2 ∧
        (∀ x, N.graph.indegree (N.leaf x) = 1 ∧ N.graph.outdegree (N.leaf x) = 0) ∧
        Function.Injective N.leaf ∧
        ∀ v, v ≠ N.root → v ∉ Set.range N.leaf →
          (N.graph.indegree v = 1 ∧ N.graph.outdegree v = 2) ∨
            (N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1) := by
  constructor
  · rintro ⟨hP, hB⟩
    have := hP.finite_arcs
    refine ⟨hP.finite_vertices, hP.finite_arcs, hP.finite_taxa, graph_connected N hP, hP.acyclic,
      hP.root_indegree, hB.1, fun x => ⟨hP.leaf_indegree x, (hP.leaves _).mpr ⟨x, rfl⟩⟩,
      hP.leaf_injective, fun v hr hl => ?_⟩
    have h1 := hP.nonroot_indegree v hr
    have h0 : N.graph.outdegree v ≠ 0 := fun h => hl ((hP.leaves v).mp h)
    have h3 := hB.2 v hr h0
    omega
  · rintro ⟨hV, hE, hX, -, hA, hr0, hr2, hleaf, hinj, hother⟩
    have hnonroot : ∀ v, v ≠ N.root → 1 ≤ N.graph.indegree v := fun v hv => by
      by_cases hl : v ∈ Set.range N.leaf
      · obtain ⟨x, rfl⟩ := hl
        exact (hleaf x).1.ge
      · rcases hother v hv hl with h | h <;> omega
    -- the root reaches every node: go up along entering arcs, which ends at the root
    let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj a b
    have : IsTrans V r := ⟨fun _ _ _ h h' => h.trans h'⟩
    have : Std.Irrefl r := ⟨fun a h => hA a h⟩
    have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
    have hreach : ∀ v, N.graph.Reaches N.root v := fun v => by
      induction v using hwf.induction with
      | _ v ih =>
        by_cases hv : v = N.root
        · rw [hv]
          exact .refl
        · obtain ⟨e, he⟩ := (N.graph.one_le_indegree_iff v).mp (hnonroot v hv)
          exact (ih (N.graph.source e) (.single ⟨e, rfl, he⟩)).tail ⟨e, rfl, he⟩
    refine ⟨⟨hV, hE, hX, hA, hreach, hr0, hnonroot, hinj, fun x => (hleaf x).1, fun v => ?_⟩,
      hr2, fun v hv h0 => ?_⟩
    · constructor
      · intro h0
        by_contra hl
        have hvr : v ≠ N.root := fun h => by rw [h, hr2] at h0; exact absurd h0 (by norm_num)
        rcases hother v hvr (fun ⟨x, hx⟩ => hl ⟨x, hx⟩) with h | h <;> omega
      · rintro ⟨x, rfl⟩
        exact (hleaf x).2
    · have hl : v ∉ Set.range N.leaf := by
        rintro ⟨x, rfl⟩
        exact h0 (hleaf x).2
      rcases hother v hv hl with h | h <;> omega

/-! ### Degrees in a binary network, and paths avoiding a node -/

section Helpers

/-- A node of a binary rooted network has degree at most three. -/
theorem IsBinaryRootedNetwork.indegree_add_outdegree_le {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (v : V) :
    N.graph.indegree v + N.graph.outdegree v ≤ 3 := by
  by_cases hr : v = N.root
  · rw [hr, hN.1.root_indegree, hN.2.1]
    norm_num
  by_cases h0 : N.graph.outdegree v = 0
  · obtain ⟨x, rfl⟩ := (hN.1.leaves v).mp h0
    rw [hN.1.leaf_indegree, h0]
    norm_num
  · exact (hN.2.2 v hr h0).le

/-- A node of a binary rooted network has indegree at most two. -/
theorem IsBinaryRootedNetwork.indegree_le_two {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (v : V) :
    N.graph.indegree v ≤ 2 := by
  by_cases hr : v = N.root
  · rw [hr, hN.1.root_indegree]
    norm_num
  by_cases h0 : N.graph.outdegree v = 0
  · obtain ⟨x, rfl⟩ := (hN.1.leaves v).mp h0
    rw [hN.1.leaf_indegree]
    norm_num
  · have := hN.2.2 v hr h0
    omega

/-- A node of a binary rooted network has outdegree at most two. -/
theorem IsBinaryRootedNetwork.outdegree_le_two {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (v : V) :
    N.graph.outdegree v ≤ 2 := by
  by_cases hr : v = N.root
  · rw [hr, hN.2.1]
  have := hN.1.nonroot_indegree v hr
  have := hN.indegree_add_outdegree_le v
  omega

/-- The arcs entering a node of indegree two are the two given distinct arcs entering it. -/
theorem eq_or_eq_of_indegree_eq_two {N : RootedNetwork V E X} [Finite E] {v : V}
    (hv : N.graph.indegree v = 2) {h₁ h₂ : E} (hne : h₁ ≠ h₂) (h₁v : N.graph.target h₁ = v)
    (h₂v : N.graph.target h₂ = v) :
    {f | N.graph.target f = v} = {h₁, h₂} := by
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro f (rfl | rfl)
    · exact h₁v
    · exact h₂v
  · rw [Set.ncard_pair hne]
    exact hv.le

/-- The arcs leaving a node of outdegree two are the two given distinct arcs leaving it. -/
theorem eq_or_eq_of_outdegree_eq_two {N : RootedNetwork V E X} [Finite E] {v : V}
    (hv : N.graph.outdegree v = 2) {e₁ e₂ : E} (hne : e₁ ≠ e₂) (he₁ : N.graph.source e₁ = v)
    (he₂ : N.graph.source e₂ = v) :
    {f | N.graph.source f = v} = {e₁, e₂} := by
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro f (rfl | rfl)
    · exact he₁
    · exact he₂
  · rw [Set.ncard_pair hne]
    exact hv.le

/-- Paths avoiding a node compose. -/
theorem hasPathAvoiding_trans {N : RootedNetwork V E X} {u v t w : V}
    (h₁ : N.HasPathAvoiding u v w) (h₂ : N.HasPathAvoiding v t w) : N.HasPathAvoiding u t w :=
  ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩

/-- A path that reaches `t` but not through `w` avoids `w`: if it cannot avoid `w`, then `w` is
between its ends. -/
theorem hasPathAvoiding_of_not_reaches_reaches {N : RootedNetwork V E X} {u t w : V}
    (h : N.graph.Reaches u t) (hw : ¬ (N.graph.Reaches u w ∧ N.graph.Reaches w t)) :
    N.HasPathAvoiding u t w := by
  by_contra hn
  exact hw (reaches_of_not_hasPathAvoiding h hn)

/-- The part up to `c` of a path avoiding `w`, when the path cannot avoid `c`. -/
theorem hasPathAvoiding_prefix {N : RootedNetwork V E X} {u t w c : V}
    (h : N.HasPathAvoiding u t w) (hc : ¬ N.HasPathAvoiding u t c) : N.HasPathAvoiding u c w := by
  obtain ⟨hu, ht, hp⟩ := h
  suffices Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ w ∧ b ≠ w) u c ∧ c ≠ w from
    ⟨hu, this.2, this.1⟩
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have : t = c := by
      by_contra hne
      exact hc ⟨hne, hne, .refl⟩
    subst this
    exact ⟨.refl, ht⟩
  | @head a b hab hbt ih =>
    by_cases ha : a = c
    · subst ha
      exact ⟨.refl, hab.2.1⟩
    · obtain ⟨h₁, h₂⟩ := ih (fun h => hc (hasPathAvoiding_head hab.1 ha h)) hab.2.2
      exact ⟨h₁.head hab, h₂⟩

/-- If every child of the stable ancestor `m` of `Z` other than `c` is above no taxon of `Z`, then
the paths to `Z` leave `m` through `c`, so `c` is a stable ancestor of `Z`. -/
theorem isStableAncestor_of_forall_adj {N : RootedNetwork V E X} {Z : Set X} {m c : V}
    (hm : N.IsStableAncestor Z m) (hleaf : ∀ z ∈ Z, N.leaf z ≠ m)
    (h : ∀ b, N.graph.Adj m b → b ≠ c → ∀ z ∈ Z, ¬ N.graph.Reaches b (N.leaf z)) :
    N.IsStableAncestor Z c := by
  intro z hz hp
  obtain ⟨-, -, hq⟩ := hp.suffix_of_not_hasPathAvoiding (hm z hz)
  rcases Relation.ReflTransGen.cases_head hq with heq | ⟨b, ⟨hadj, -, hb⟩, hbt⟩
  · exact hleaf z hz heq.symm
  · exact h b hadj hb z hz (Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hbt)

/-- No child of the least stable ancestor of `Z` is a stable ancestor of `Z`. -/
theorem not_isStableAncestor_of_adj_lsa {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {Z : Set X} (hZ : Z.Nonempty) {c : V} (hadj : N.graph.Adj (lsa hN Z hZ) c) :
    ¬ N.IsStableAncestor Z c := fun hc =>
  hN.acyclic _ (Relation.TransGen.head' hadj ((lsa_spec hN Z hZ).2 c hc))

end Helpers

/-- **Definition 2**: a *metric* `(λ, γ)` for a binary rooted network: every edge has a positive length,
and the inheritance probabilities make the library's valid parameters (`RootedNetwork.IsMetric`: those
of the two hybrid edges of a hybrid node are positive and sum to `1`; a tree edge has `1`). -/
def IsMetricNetwork [Fintype E] (N : RootedNetwork V E X) (θ : MetricData E) : Prop :=
  N.IsMetric θ ∧ ∀ e, 0 < θ.length e

/-- **Definition 2, as printed**: on a binary rooted network, a metric gives every edge a positive
length, every hybrid edge an inheritance probability in `(0, 1)`, with those of the two hybrid edges of
a hybrid node summing to `1`; tree edges carry inheritance probability `1`, which the coalescent reads. -/
theorem isMetricNetwork_iff [Fintype E] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (θ : MetricData E) :
    IsMetricNetwork N θ ↔
      (∀ e, 0 < θ.length e) ∧ (∀ e, N.IsTreeArc e → θ.inheritance e = 1) ∧
        (∀ h, N.IsHybridArc h → 0 < θ.inheritance h ∧ θ.inheritance h < 1) ∧
        ∀ h₁ h₂, h₁ ≠ h₂ → N.IsHybridArc h₁ → N.graph.target h₁ = N.graph.target h₂ →
          θ.inheritance h₁ + θ.inheritance h₂ = 1 := by
  classical
  -- a node entered by two arcs has exactly two, and the sum at it is over those two
  have hsum : ∀ v, 2 ≤ N.graph.indegree v → ∀ h₁ h₂, h₁ ≠ h₂ → N.graph.target h₁ = v →
      N.graph.target h₂ = v →
      ∑ e, (if N.graph.target e = v then θ.inheritance e else 0) =
        θ.inheritance h₁ + θ.inheritance h₂ := by
    intro v hv h₁ h₂ hne h₁v h₂v
    have hset := eq_or_eq_of_indegree_eq_two (le_antisymm (hN.indegree_le_two v) hv) hne h₁v h₂v
    rw [← Finset.sum_filter]
    have : Finset.univ.filter (fun e => N.graph.target e = v) = {h₁, h₂} := by
      ext f
      simpa using Set.ext_iff.mp hset f
    rw [this, Finset.sum_pair hne]
  have hpair : ∀ v, 2 ≤ N.graph.indegree v → ∃ h₁ h₂, h₁ ≠ h₂ ∧ N.graph.target h₁ = v ∧
      N.graph.target h₂ = v := by
    intro v hv
    obtain ⟨h₁, h₂, hne, hs⟩ := Set.ncard_eq_two.mp (le_antisymm (hN.indegree_le_two v) hv)
    have h₁v : h₁ ∈ {f | N.graph.target f = v} := by rw [hs]; exact Or.inl rfl
    have h₂v : h₂ ∈ {f | N.graph.target f = v} := by rw [hs]; exact Or.inr rfl
    exact ⟨h₁, h₂, hne, h₁v, h₂v⟩
  constructor
  · rintro ⟨⟨-, -, hT, hH, hS⟩, hpos⟩
    refine ⟨hpos, hT, fun h hh => ⟨hH h hh, ?_⟩, fun h₁ h₂ hne hh₁ ht => ?_⟩
    · obtain ⟨g₁, g₂, hne, hg₁, hg₂⟩ := hpair _ hh
      have hS' := hS _ hh
      rw [hsum _ hh g₁ g₂ hne hg₁ hg₂] at hS'
      have hg₁h : N.IsHybridArc g₁ := by unfold IsHybridArc; rw [hg₁]; exact hh
      have hg₂h : N.IsHybridArc g₂ := by unfold IsHybridArc; rw [hg₂]; exact hh
      have hmem : h ∈ ({g₁, g₂} : Set E) := by
        rw [← eq_or_eq_of_indegree_eq_two (le_antisymm (hN.indegree_le_two _) hh) hne hg₁ hg₂]
        rfl
      rcases hmem with rfl | rfl
      · exact lt_of_lt_of_eq (lt_add_of_pos_right _ (hH _ hg₂h)) hS'
      · exact lt_of_lt_of_eq (lt_add_of_pos_left _ (hH _ hg₁h)) hS'
    · rw [← hsum _ hh₁ h₁ h₂ hne rfl ht.symm]
      exact hS _ hh₁
  · rintro ⟨hpos, hT, hH, hS⟩
    refine ⟨⟨fun e _ => hpos e, fun e _ => (hpos e).le, hT, fun h hh => (hH h hh).1,
      fun v hv => ?_⟩, hpos⟩
    obtain ⟨h₁, h₂, hne, h₁v, h₂v⟩ := hpair v hv
    rw [hsum v hv h₁ h₂ hne h₁v h₂v]
    exact hS h₁ h₂ hne (by unfold IsHybridArc; rw [h₁v]; exact hv) (h₁v.trans h₂v.symm)

/-- **Definition 3** (`def::above`): `v` is *above* `u` (and `u` *below* `v`) if a non-empty directed
path leads from `v` to `u`. An edge from `x` to `y` is above `v` if `y` is above or equal to `v`
(`N.graph.Reaches y v`), and below `v` if `x` is below or equal to `v` (`N.graph.Reaches v x`). -/
def IsAbove (N : RootedNetwork V E X) (v u : V) : Prop :=
  Relation.TransGen N.graph.Adj v u

/-- **Definition 4** (`def::MRCA`; LSA in the published version), as printed: for `D` the set of nodes
on every directed path from the root to a taxon of `Z`, the LSA of `Z` is the node of `D` below every
other node of `D`. The library's stable ancestors are the nodes of `D`, and its least stable ancestor
(`RootedNetwork.lsa`) is this node. -/
theorem isLeastStableAncestor_iff_def4 (N : RootedNetwork V E X) (Z : Set X) (v : V) :
    N.IsLeastStableAncestor Z v ↔
      N.IsStableAncestor Z v ∧ ∀ u, N.IsStableAncestor Z u → u ≠ v → IsAbove N u v := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, fun u hu huv => ?_⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, fun u hu => ?_⟩⟩
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp (h₂ u hu) with h | h
    · exact absurd h.symm huv
    · exact h
  · by_cases huv : u = v
    · rw [huv]
      exact .refl
    · exact (h₂ u hu huv).to_reflTransGen

/-- **Lemma 1** (`lem::MRCAproperties`): for nonempty sets of taxa `Z ⊆ Y` of a binary rooted network,
(i) the LSA of `Z` has indegree at most one; (ii) at most one of its out-edges is hybrid; (iii) the LSA
of `Z` is below or equal to the LSA of `Y`. The paper states the lemma for every `Z ⊆ X`; the LSA of
the empty set does not exist (every node lies on every path to a taxon of `∅`).

The proof of (ii) is the paper's, with two steps filled in. A taxon of `Z` is below each child `xᵢ` of
`LSA(Z)`: otherwise every path to `Z` would leave `LSA(Z)` through the other child, a lower stable
ancestor. If the other parent of `x₁` is below `LSA(Z)`, a path to it from `LSA(Z)` starts with `e₂`,
since through `e₁` it would close a directed cycle; so it is below `x₂`, and symmetrically. -/
theorem lemma1 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {Z Y : Set X}
    (hZ : Z.Nonempty) (hZY : Z ⊆ Y) :
    N.graph.indegree (lsa hN.1 Z hZ) ≤ 1 ∧
      (∀ e f, N.graph.source e = lsa hN.1 Z hZ → N.graph.source f = lsa hN.1 Z hZ →
        N.IsHybridArc e → N.IsHybridArc f → e = f) ∧
      N.graph.Reaches (lsa hN.1 Y (hZ.mono hZY)) (lsa hN.1 Z hZ) := by
  have : Finite E := hN.1.finite_arcs
  set m := lsa hN.1 Z hZ with hm_def
  obtain ⟨hst, hleast⟩ := lsa_spec hN.1 Z hZ
  rw [← hm_def] at hst hleast
  -- (i): an LSA of indegree two would have outdegree one, and its child would be a lower stable
  -- ancestor
  have hi : N.graph.indegree m ≤ 1 := by
    by_contra hin
    have h2 : N.graph.indegree m = 2 := by have := hN.indegree_le_two m; omega
    have hr : m ≠ N.root := fun h => by
      rw [h, hN.1.root_indegree] at h2; exact absurd h2 (by norm_num)
    have hleaf : ∀ z ∈ Z, N.leaf z ≠ m := fun z _ h => by
      rw [← h, hN.1.leaf_indegree] at h2; exact absurd h2 (by norm_num)
    have h0 : N.graph.outdegree m ≠ 0 := fun h => by
      obtain ⟨z, hz⟩ := (hN.1.leaves m).mp h
      rw [← hz, hN.1.leaf_indegree] at h2; exact absurd h2 (by norm_num)
    have h3 := hN.2.2 m hr h0
    obtain ⟨e, he⟩ := (N.graph.outdegree_eq_one_iff m).mp (by omega)
    refine not_isStableAncestor_of_adj_lsa hN.1 hZ (c := N.graph.target e) ⟨e, (he e).mpr rfl, rfl⟩
      (isStableAncestor_of_forall_adj hst hleaf fun b ⟨f, hfs, hft⟩ hb => ?_)
    exact absurd (by rw [← hft, (he f).mp hfs]) hb
  refine ⟨hi, fun e f hes hfs he hf => ?_, hleast _ fun x hx => (lsa_spec hN.1 Y _).1 x (hZY hx)⟩
  -- (ii)
  by_contra hef
  have hleaf : ∀ z ∈ Z, N.leaf z ≠ m := fun z _ h => by
    have h0 := (hN.1.leaves m).mpr ⟨z, h⟩
    exact (N.graph.outdegree_eq_zero_iff m).mp h0 e hes
  -- the out-edges of `m` are `e` and `f`
  have hout2 : N.graph.outdegree m = 2 := by
    by_cases hr : m = N.root
    · rw [hr, hN.2.1]
    · have h1 := hN.1.nonroot_indegree m hr
      have h0 : N.graph.outdegree m ≠ 0 := fun h => (N.graph.outdegree_eq_zero_iff m).mp h e hes
      have := hN.2.2 m hr h0
      omega
  have hout : ∀ g, N.graph.source g = m → g = e ∨ g = f := fun g hg => by
    have := Set.ext_iff.mp (eq_or_eq_of_outdegree_eq_two hout2 hef hes hfs) g
    simpa using this.mp hg
  -- a child of `m` above no taxon of `Z` would make the other child a stable ancestor
  have hchild : ∀ c, N.graph.Adj m c →
      (∀ b, N.graph.Adj m b → b ≠ c → ∀ z ∈ Z, ¬ N.graph.Reaches b (N.leaf z)) → False :=
    fun c hc h =>
      not_isStableAncestor_of_adj_lsa hN.1 hZ hc (isStableAncestor_of_forall_adj hst hleaf h)
  have hadj : ∀ b, N.graph.Adj m b → b = N.graph.target e ∨ b = N.graph.target f := by
    rintro b ⟨g, hgs, rfl⟩
    rcases hout g hgs with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- if `e` and `f` have the same child, that child is on every path from `m` to `Z`
  by_cases hsame : N.graph.target e = N.graph.target f
  · refine hchild _ ⟨e, hes, rfl⟩ fun b hb hbe => ?_
    rcases hadj b hb with rfl | rfl
    · exact absurd rfl hbe
    · exact absurd hsame.symm hbe
  -- otherwise, each child `x₁`, `x₂` is above a taxon of `Z`
  set x₁ := N.graph.target e
  set x₂ := N.graph.target f
  have hz₁ : ∃ z ∈ Z, N.graph.Reaches x₁ (N.leaf z) := by
    by_contra hno
    push Not at hno
    refine hchild x₂ ⟨f, hfs, rfl⟩ fun b hb hb₂ z hz hbz => ?_
    rcases hadj b hb with rfl | rfl
    · exact hno z hz hbz
    · exact hb₂ rfl
  have hz₂ : ∃ z ∈ Z, N.graph.Reaches x₂ (N.leaf z) := by
    by_contra hno
    push Not at hno
    refine hchild x₁ ⟨e, hes, rfl⟩ fun b hb hb₁ z hz hbz => ?_
    rcases hadj b hb with rfl | rfl
    · exact hb₁ rfl
    · exact hno z hz hbz
  obtain ⟨z₁, hz₁, hx₁z₁⟩ := hz₁
  obtain ⟨z₂, hz₂, hx₂z₂⟩ := hz₂
  -- the other parents of `x₁` and `x₂`
  have hother : ∀ g, N.IsHybridArc g → ∃ g', g' ≠ g ∧ N.graph.target g' = N.graph.target g :=
    fun g hg => by
      obtain ⟨g', hg', hne⟩ :=
        Set.exists_ne_of_one_lt_ncard (s := {g' | N.graph.target g' = N.graph.target g}) hg g
      exact ⟨g', hne, hg'⟩
  obtain ⟨e₁, he₁e, he₁⟩ := hother e he
  obtain ⟨f₁, hf₁f, hf₁⟩ := hother f hf
  have hv₁ : N.graph.source e₁ ≠ m := fun h => by
    rcases hout e₁ h with rfl | rfl
    · exact he₁e rfl
    · exact hsame he₁.symm
  have hw₁ : N.graph.source f₁ ≠ m := fun h => by
    rcases hout f₁ h with rfl | rfl
    · exact hsame hf₁
    · exact hf₁f rfl
  have hcyc : ∀ {a b}, N.graph.Reaches a b → N.graph.Adj b a → False := fun h hab =>
    hN.1.acyclic _ (Relation.TransGen.tail' h hab)
  -- a parent not below `m` of a child `x` of `m` gives a path from the root to a taxon below `x`
  -- avoiding `m`
  have hnotbelow : ∀ g g', N.graph.source g = m → N.graph.target g' = N.graph.target g →
      N.graph.source g' ≠ m → ∀ z ∈ Z, N.graph.Reaches (N.graph.target g) (N.leaf z) →
      N.graph.Reaches m (N.graph.source g') := by
    intro g g' hg hg' hg'm z hz hxz
    by_contra hnr
    have h₁ : N.HasPathAvoiding N.root (N.graph.source g') m :=
      hasPathAvoiding_of_not_reaches_reaches (hN.1.root_reaches _) fun h => hnr h.2
    have h₂ : N.HasPathAvoiding (N.graph.target g) (N.leaf z) m :=
      hasPathAvoiding_of_not_reaches_reaches hxz fun h => hcyc h.1 ⟨g, hg, rfl⟩
    exact hst z hz (hasPathAvoiding_trans h₁ (hasPathAvoiding_head ⟨g', rfl, hg'⟩ hg'm
      (hg' ▸ h₂)))
  have hv₁m := hnotbelow e e₁ hes he₁ hv₁ z₁ hz₁ hx₁z₁
  have hw₁m := hnotbelow f f₁ hfs hf₁ hw₁ z₂ hz₂ hx₂z₂
  -- both other parents below `m`: a path from `m` to the other parent of `x₁` starts with `f`, and
  -- one to the other parent of `x₂` with `e`, which closes a directed cycle
  have hvia : ∀ v, N.graph.Reaches m v → v ≠ m → N.graph.Reaches x₁ v ∨ N.graph.Reaches x₂ v := by
    intro v hv hvm
    rcases Relation.ReflTransGen.cases_head hv with h | ⟨b, hb, hbv⟩
    · exact absurd h.symm hvm
    · rcases hadj b hb with rfl | rfl
      · exact Or.inl hbv
      · exact Or.inr hbv
  have h₁ : N.graph.Reaches x₂ (N.graph.source e₁) :=
    (hvia _ hv₁m hv₁).resolve_left fun h => hcyc h ⟨e₁, rfl, he₁⟩
  have h₂ : N.graph.Reaches x₁ (N.graph.source f₁) :=
    (hvia _ hw₁m hw₁).resolve_right fun h => hcyc h ⟨f₁, rfl, hf₁⟩
  exact hcyc ((h₂.tail ⟨f₁, rfl, hf₁⟩).trans h₁) ⟨e₁, rfl, he₁⟩

/-- **Lemma 2** (`lem::mrcaxy`): for a set `Z` of at least two taxa and `x ∈ Z`, some `y ∈ Z` has
`LSA(x, y) = LSA(Z)`. -/
theorem lemma2 {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {Z : Set X}
    (hZ : Z.Nontrivial) {x : X} (hx : x ∈ Z) :
    ∃ y ∈ Z, lsa hN.1 {x, y} (Set.insert_nonempty x {y}) = lsa hN.1 Z hZ.nonempty := by
  have : Finite V := hN.1.finite_vertices
  have : Finite X := hN.1.finite_taxa
  set m := lsa hN.1 Z hZ.nonempty with hm_def
  obtain ⟨hst, hleast⟩ := lsa_spec hN.1 Z hZ.nonempty
  rw [← hm_def] at hst hleast
  let a : X → V := fun y => lsa hN.1 {x, y} (Set.insert_nonempty x {y})
  have ha_st : ∀ y, N.IsStableAncestor {x, y} (a y) := fun y => (lsa_spec hN.1 _ _).1
  have hx_mem : ∀ y, x ∈ ({x, y} : Set X) := fun y => Set.mem_insert x _
  have hy_mem : ∀ y, y ∈ ({x, y} : Set X) := fun y => Set.mem_insert_of_mem x rfl
  -- `LSA(x, y)` is below or equal to `m` (Lemma 1)
  have hma : ∀ y ∈ Z, N.graph.Reaches m (a y) := fun y hy =>
    (lemma1 hN (Set.insert_nonempty x {y})
      (Set.insert_subset hx (Set.singleton_subset_iff.mpr hy))).2.2
  -- the nodes `LSA(x, y)` are on every path from the root to `x`, so they are comparable
  have hcomp : ∀ y y', N.graph.Reaches (a y) (a y') ∨ N.graph.Reaches (a y') (a y) := fun y y' =>
    reaches_or_reaches_of_not_hasPathAvoiding (hN.1.root_reaches (N.leaf x)) (ha_st y x (hx_mem y))
      (ha_st y' x (hx_mem y'))
  by_contra hne
  push Not at hne
  -- `z` with `LSA(x, z)` highest
  let r : V → V → Prop := fun u w => Relation.TransGen N.graph.Adj u w
  have : IsTrans V r := ⟨fun _ _ _ h h' => h.trans h'⟩
  have : Std.Irrefl r := ⟨fun u h => hN.1.acyclic u h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨_, ⟨z, hz, rfl⟩, hmin⟩ := hwf.has_min (a '' Z) (hZ.nonempty.image a)
  have hhigh : ∀ y ∈ Z, N.graph.Reaches (a z) (a y) := fun y hy => by
    rcases hcomp z y with h | h
    · exact h
    · rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with h | h
      · rw [h]
        exact .refl
      · exact absurd h (hmin _ ⟨y, hy, rfl⟩)
  set w := a z
  have hwm : w ≠ m := hne z hz
  have hmw : N.graph.Reaches m w := hma z hz
  -- every path from `m` to a taxon `y` of `Z` passes through `LSA(x, z)`
  have hclaim : ∀ y ∈ Z, ¬ N.HasPathAvoiding m (N.leaf y) w := by
    intro y hy hP
    -- the path passes through `LSA(x, y)`, which is below `m`
    have h₁ : ¬ N.HasPathAvoiding m (N.leaf y) (a y) := fun hq => by
      have hrm : N.HasPathAvoiding N.root m (a y) :=
        hasPathAvoiding_of_not_reaches_reaches (hN.1.root_reaches m) fun h =>
          hne y hy (eq_of_reaches_of_reaches hN.1.acyclic h.2 (hma y hy))
      exact ha_st y y (hy_mem y) (hasPathAvoiding_trans hrm hq)
    have h₂ : N.HasPathAvoiding m (a y) w := hasPathAvoiding_prefix hP h₁
    -- `LSA(x, y)` is strictly below `LSA(x, z)`, so the path continues to `x` avoiding `LSA(x, z)`
    have h₃ : N.HasPathAvoiding (a y) (N.leaf x) w :=
      hasPathAvoiding_of_not_reaches_reaches ((ha_st y).reaches_leaf hN.1 (hx_mem y)) fun h =>
        h₂.2.1 (eq_of_reaches_of_reaches hN.1.acyclic h.1 (hhigh y hy))
    have h₄ : N.HasPathAvoiding N.root m w :=
      hasPathAvoiding_of_not_reaches_reaches (hN.1.root_reaches m) fun h =>
        hwm (eq_of_reaches_of_reaches hN.1.acyclic h.2 hmw)
    exact ha_st z x (hx_mem z) (hasPathAvoiding_trans (hasPathAvoiding_trans h₄ h₂) h₃)
  -- so `LSA(x, z)` is a stable ancestor of `Z` below `m`
  have hwst : N.IsStableAncestor Z w := fun y hy hp =>
    hclaim y hy (hp.suffix_of_not_hasPathAvoiding (hst y hy))
  exact hwm (eq_of_reaches_of_reaches hN.1.acyclic (hleast w hwst) hmw)

end Banos2019
