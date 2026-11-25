module

public import Banos2019.Quartet.Normal
public import Banos2019.Quartet.GraphMaps
public import Banos2019.Basic.Logic.RelationAvoid
public import Phylogenetics.Graph.Tree

/-!
# The 4-cycles of `Q⁻_s` and the cycles of `N⁻` (Section 7, Lemmas 12 and 13)

A set `s` of four taxa induces a quartet network `Q⁻_s` with a 4-cycle exactly when `N⁻` has a cycle
`C_v` of size at least four that separates `s`: its four taxa are in distinct `v`-blocks, one in the
hybrid block. The hybrid node of the 4-cycle of `Q⁻_s` is then that of `C_v`.

* `exists_fourCycle_of_separates`, `exists_separates_of_fourCycle`: the two directions, as the proof
  of Lemma 12 states them. The two cycles correspond through a cycle of `N`: the arcs of the edges
  of `C_v` (`liftEdges`), and the chains of the arcs of the cycle of `Q⊕_s` (`cycleChainArcs`).
* `unrooted_isConnected`: `N⁻` is connected.
* `walks_cycle_of_mem_cycleNodes`: two nodes of a cycle are joined along it.
* `exists_walks_cycleNodes_of_not_walks`: in a connected graph, a node not joined to a node `z₀` of
  a cycle `C'` by a walk avoiding a cycle `C`, disjoint from `C'`, reaches a node of `C` by a walk
  avoiding both (the argument of Lemma 13).
* `exists_walks_unrooted_quartetLSA`: the taxa of `s` in the blocks of the nodes of a cycle of
  `Q⊕_s` are in the blocks of those nodes in `N⁻`, for the cycle of `N⁻` of its chains.
-/
@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Walks -/

section Walks

variable {V' E' : Type*} (G : DirectedMultigraph V' E')

/-- Two nodes of a cycle are joined by a walk along its edges. -/
theorem walks_cycle_of_mem_cycleNodes {C : Set E'} (hC : IsCycle G C) {p q : V'}
    (hp : p ∈ cycleNodes G C) (hq : q ∈ cycleNodes G C) : G.Walks C p q := by
  obtain ⟨k, v, e, hcyc, hrange⟩ := hC
  -- every node of the cycle is joined to `v 0`
  have hpos := hcyc.pos
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have h₀ : ∀ i : Fin (m + 1), G.Walks C (v ⟨0, hpos⟩) (v i) := by
    intro i
    obtain ⟨i, hi⟩ := i
    induction i with
    | zero => exact .refl
    | succ n ih =>
      have hn : n < m + 1 := by omega
      refine (ih hn).tail ⟨e ⟨n, hn⟩, hrange ▸ ⟨_, rfl⟩, ?_⟩
      have hj := hcyc.joins ⟨n, hn⟩
      have hrot : finRotate (m + 1) ⟨n, hn⟩ = ⟨n + 1, hi⟩ := by
        rw [finRotate_of_lt (by omega)]
      rw [hrot] at hj
      rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨h₁, h₂⟩
  have hnode : ∀ r ∈ cycleNodes G C, ∃ i, v i = r := by
    rintro r ⟨f, hf, hr⟩
    rw [← hrange] at hf
    obtain ⟨i, rfl⟩ := hf
    rcases hcyc.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hr with hr | hr
    · exact ⟨i, h₁.symm.trans hr⟩
    · exact ⟨finRotate (m + 1) i, h₂.symm.trans hr⟩
    · exact ⟨finRotate (m + 1) i, h₁.symm.trans hr⟩
    · exact ⟨i, h₂.symm.trans hr⟩
  obtain ⟨i, rfl⟩ := hnode p hp
  obtain ⟨j, rfl⟩ := hnode q hq
  exact (G.walks_symm (h₀ i)).trans (h₀ j)

/-- **The first node of a cycle on a walk** (the argument of Lemma 13): in a connected graph, take a
node `z₀` and a set `K` of edges whose ends are joined to `z₀` avoiding `C`. A node `p` that is not
joined to `z₀` by a walk avoiding `C` reaches a node of `C` by a walk avoiding `C` and `K`: follow a
walk from `p` to `z₀` up to its first edge of `C`. -/
theorem exists_walks_cycleNodes_of_not_walks (hG : G.IsConnected) {C K : Set E'} {z₀ : V'}
    (hK : ∀ f ∈ K, G.Walks Cᶜ (G.source f) z₀) {p : V'} (hp : ¬ G.Walks Cᶜ p z₀) :
    ∃ z ∈ cycleNodes G C, G.Walks (Cᶜ ∩ Kᶜ) p z := by
  have hw := hG p z₀
  induction hw using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd .refl hp
  | @head p q hpq _ ih =>
    obtain ⟨f, -, hf⟩ := hpq
    by_cases hfC : f ∈ C
    · refine ⟨p, ⟨f, hfC, ?_⟩, .refl⟩
      rcases hf with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · have hstep : G.AdjOn Cᶜ p q := ⟨f, hfC, hf⟩
      have hq : ¬ G.Walks Cᶜ q z₀ := fun h => hp (Relation.ReflTransGen.head hstep h)
      obtain ⟨z, hz, hqz⟩ := ih hq
      have hfK : f ∉ K := by
        intro hfK
        have hs := hK f hfK
        rcases hf with ⟨h₁, -⟩ | ⟨h₁, -⟩
        · exact hp (h₁ ▸ hs)
        · exact hq (h₁ ▸ hs)
      exact ⟨z, hz, Relation.ReflTransGen.head ⟨f, ⟨hfC, hfK⟩, hf⟩ hqz⟩

end Walks

/-- A path along the arcs of `C` is a walk on the arcs of `C` between its ends. -/
theorem walks_of_reflTransGen_mem {G : DirectedMultigraph V E} {C F : Set E} {a b : V}
    (h : Relation.ReflTransGen (fun x y => ∃ f ∈ C, G.source f = x ∧ G.target f = y) a b)
    (hF : ∀ f ∈ C, G.Reaches a (G.source f) → G.Reaches (G.target f) b → f ∈ F) :
    G.Walks F a b := by
  induction h with
  | refl => exact .refl
  | @tail y z hay hyz ih =>
    obtain ⟨f, hfC, hfs, hft⟩ := hyz
    have hr : G.Reaches a y := Relation.ReflTransGen.mono (fun _ _ ⟨g, _, hg⟩ => ⟨g, hg⟩) _ _ hay
    refine (ih fun f' hf' h₁ h₂ => hF f' hf' h₁ (h₂.tail ⟨f, hfs, hft⟩)).tail
      ⟨f, hF f hfC (hfs ▸ hr) (hft ▸ .refl), Or.inl ⟨hfs, hft⟩⟩

/-! ### `N⁻` is connected -/

/-- **`N⁻` is connected**: every node is joined to the child of the edge of the root that
suppression merges, along a directed path from the root. -/
theorem unrooted_isConnected {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (hX : Nontrivial X) : (unrooted N hN hX).graph.IsConnected := by
  set M := lsaPlus hN.1 hX
  have hM : M.IsPhylogenetic := lsaPlus_isPhylogenetic hN.1 hX
  set e₀ := rootTreeArc hN.1 hN.2 hX
  have he₀ := (rootTreeArc_spec hN.1 hN.2 hX).1
  set t₀ : SemidirectedVertex hN.1 hX := ⟨M.graph.target e₀, hM.target_ne_root e₀⟩
  have key : ∀ w (hw : w ≠ M.root), (unrooted N hN hX).graph.Walks Set.univ t₀ ⟨w, hw⟩ := by
    intro w hw
    have hr := hM.root_reaches w
    induction hr with
    | refl => exact absurd rfl hw
    | @tail a b hra hab ih =>
      obtain ⟨f, hfs, hft⟩ := hab
      by_cases ha : a = M.root
      · by_cases hf : f = e₀
        · have : (⟨b, hw⟩ : SemidirectedVertex hN.1 hX) = t₀ :=
            Subtype.ext (show b = M.graph.target e₀ by rw [← hft, hf])
          rw [this]
          exact .refl
        · refine Relation.ReflTransGen.single ⟨⟨f, hf⟩, Set.mem_univ _, Or.inl ⟨?_, ?_⟩⟩
          · show (unrootAt M hM e₀).graph.source ⟨f, hf⟩ = t₀
            simp only [unrootAt]
            rw [dite_eq_left (hfs.trans ha)]
          · exact Subtype.ext hft
      · have hf : f ≠ e₀ := by
          rintro rfl
          exact ha (hfs.symm.trans he₀)
        refine (ih ha).tail ⟨⟨f, hf⟩, Set.mem_univ _, Or.inl ⟨?_, ?_⟩⟩
        · show (unrootAt M hM e₀).graph.source ⟨f, hf⟩ = ⟨a, ha⟩
          simp only [unrootAt]
          rw [dite_eq_right (by rw [hfs]; exact ha)]
          exact Subtype.ext hfs
        · exact Subtype.ext hft
  intro u w
  exact ((unrooted N hN hX).graph.walks_symm (key u.1 u.2)).trans (key w.1 w.2)

/-! ### The blocks of a cycle of `Q⊕_s` in `N⁻` -/

section Quartet

variable {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (hX : Nontrivial X) {s : Finset X}
  (hs : #s = 4)

/-- A node of `Q⊕_s` other than its root is, in `N`, strictly below `LSA(X)`. -/
theorem quartetLSA_val_ne_lsa_univ {u : _} (hu : u ≠ (quartetLSA N hN.1 s hs).root) :
    u.1.1 ≠ lsa hN.1 Set.univ Set.univ_nonempty := by
  have hZ : (s : Set X).Nontrivial := Finset.one_lt_card_iff_nontrivial.mp (by omega)
  have hm := lsa_univ_reaches hN.1 hZ.nonempty
  intro h
  refine hu (Subtype.ext (Subtype.ext ?_))
  show u.1.1 = lsa hN.1 (s : Set X) hZ.nonempty
  rw [h]
  exact eq_of_reaches_of_reaches hN.1.acyclic hm (h ▸ u.1.2.1)

include hX in
/-- **A walk of `Q⊕_s` avoiding a set `D` of its arcs gives a walk of `N⁻` avoiding the edges whose
arcs are on the chains of `D`**: the chains of the arcs of the walk are not on those of `D`. -/
theorem walks_unrooted_of_walks_quartetLSA {D : Set _} {u w : _}
    (h : (quartetLSA N hN.1 s hs).graph.Walks Dᶜ u w) {C' : Set (SemidirectedArc hN.1 hN.2 hX)}
    (hC' : ∀ g ∈ C', sdArc hN.1 hN.2 hX g ∈ Subtype.val '' cycleChainArcs _ D) :
    (unrooted N hN hX).graph.Walks C'ᶜ (sdNode hN.1 hN.2 hX u.1.1) (sdNode hN.1 hN.2 hX w.1.1) := by
  have hZ : (s : Set X).Nontrivial := Finset.one_lt_card_iff_nontrivial.mp (by omega)
  have h₁ := walks_cycleChainArcs_of_walks (lsaNetwork_isPhylogenetic hN.1 hZ) h
  have h₂ := walks_image_of_hom (φ := Subtype.val) (ψ := Subtype.val) (fun _ => rfl)
    (fun _ => rfl) h₁
  refine walks_semidirected_of_walks hN.1 hN.2 hX (fun f hf => ?_) (fun g hg hgC => ?_) h₂
  · obtain ⟨e, -, rfl⟩ := hf
    exact (lsa_univ_reaches hN.1 hZ.nonempty).trans e.2.1
  · obtain ⟨e, ⟨g₁, hg₁, hon₁⟩, he⟩ := hg
    obtain ⟨e', ⟨g₂, hg₂, hon₂⟩, he'⟩ := hC' g hgC
    have hee' : e = e' := Subtype.ext (he.trans he'.symm)
    subst hee'
    exact hg₁ (eq_of_isOnChain_of_isOnChain hon₁ hon₂ ▸ hg₂)

include hX in
/-- A node of a cycle of `Q⊕_s` other than its root is a node of the cycle of `N⁻` whose arcs are on
its chains. -/
theorem sdNode_mem_cycleNodes_of_quartetLSA {D : Set _} {u : _}
    (hu : u ∈ cycleNodes (quartetLSA N hN.1 s hs).graph D)
    (hur : u ≠ (quartetLSA N hN.1 s hs).root) {C' : Set (SemidirectedArc hN.1 hN.2 hX)}
    (hC' : liftEdges hN.1 hN.2 hX C' = Subtype.val '' cycleChainArcs _ D) :
    sdNode hN.1 hN.2 hX u.1.1 ∈ cycleNodes (unrooted N hN hX).graph C' := by
  have hZ : (s : Set X).Nontrivial := Finset.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨f, hf, hfu⟩ := val_mem_cycleNodes_cycleChainArcs (lsaNetwork_isPhylogenetic hN.1 hZ) hu
  have hmem : sdVert hN.1 hX (sdNode hN.1 hN.2 hX u.1.1) ∈
      cycleNodes N.graph (liftEdges hN.1 hN.2 hX C') := by
    rw [sdVert_sdNode hN.1 hN.2 hX ((lsa_univ_reaches hN.1 hZ.nonempty).trans u.1.2.1)
      (quartetLSA_val_ne_lsa_univ hN hX hs hur), hC']
    refine ⟨f.1, ⟨f, hf, rfl⟩, ?_⟩
    rcases hfu with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  exact (sdVert_mem_cycleNodes_liftEdges_iff hN.1 hN.2 hX C' _).1 hmem

include hX in
/-- **The taxa in the blocks of a cycle of `Q⊕_s` are in the blocks of `N⁻`** of the cycle of `N⁻`
whose arcs are on its chains: every taxon of `s` is joined, avoiding that cycle, to a node of the
cycle of `Q⊕_s` other than the root (whose block in `Q⊕_s` holds it), and every such node to a taxon
of `s` (`nodeBlock_nonempty`). -/
theorem exists_walks_unrooted_quartetLSA (h1 : IsLevelOne N.graph) {D : Set _}
    (hD : IsCycle (quartetLSA N hN.1 s hs).graph D) {v : _}
    (hv : v ∈ cycleNodes (quartetLSA N hN.1 s hs).graph D)
    (h2 : (quartetLSA N hN.1 s hs).graph.indegree v = 2) {C' : Set (SemidirectedArc hN.1 hN.2 hX)}
    (hC' : liftEdges hN.1 hN.2 hX C' = Subtype.val '' cycleChainArcs _ D) :
    (∀ x : (s : Set X), ∃ u ∈ cycleNodes (quartetLSA N hN.1 s hs).graph D,
      u ≠ (quartetLSA N hN.1 s hs).root ∧
        (unrooted N hN hX).graph.Walks C'ᶜ (sdNode hN.1 hN.2 hX u.1.1)
          ((unrooted N hN hX).leaf x)) ∧
    (∀ u ∈ cycleNodes (quartetLSA N hN.1 s hs).graph D, u ≠ (quartetLSA N hN.1 s hs).root →
      ∃ x : (s : Set X),
        (unrooted N hN hX).graph.Walks C'ᶜ (sdNode hN.1 hN.2 hX u.1.1)
          ((unrooted N hN hX).leaf x)) := by
  have hQ := quartetLSA_isBinaryRootedNetwork hN hs
  have hsub : ∀ g ∈ C', sdArc hN.1 hN.2 hX g ∈ Subtype.val '' cycleChainArcs _ D := fun g hg =>
    hC' ▸ (sdArc_mem_liftEdges_iff hN.1 hN.2 hX C' g).2 hg
  refine ⟨fun x => ?_, fun u hu hur => ?_⟩
  · obtain ⟨u, hu, hx⟩ := exists_mem_nodeBlock hQ.1 hD x
    have hur : u ≠ (quartetLSA N hN.1 s hs).root := by
      rintro rfl
      rw [nodeBlock_root hQ hD hu] at hx
      exact hx
    refine ⟨u, hu, hur, ?_⟩
    have h := walks_unrooted_of_walks_quartetLSA hN hX hs hx hsub
    rwa [show ((quartetLSA N hN.1 s hs).leaf x).1.1 = N.leaf x.1 from rfl, sdNode_leaf] at h
  · obtain ⟨x, hx⟩ := nodeBlock_nonempty hQ (quartetLSA_isLevelOne hN h1 hs) hD hv h2
      (quartetLSA_isLSANetwork hN hs) hu hur
    refine ⟨x, ?_⟩
    have h := walks_unrooted_of_walks_quartetLSA hN hX hs hx hsub
    rwa [show ((quartetLSA N hN.1 s hs).leaf x).1.1 = N.leaf x.1 from rfl, sdNode_leaf] at h

include hX in
/-- Two nodes of a cycle of `Q⊕_s` other than the root joined in `N⁻` avoiding the cycle of `N⁻`
whose arcs are on its chains are equal. -/
theorem eq_of_walks_unrooted_quartetLSA (h1 : IsLevelOne N.graph) {D : Set _} {u u' : _}
    (hu : u ∈ cycleNodes (quartetLSA N hN.1 s hs).graph D) (hur : u ≠ (quartetLSA N hN.1 s hs).root)
    (hu' : u' ∈ cycleNodes (quartetLSA N hN.1 s hs).graph D)
    (hur' : u' ≠ (quartetLSA N hN.1 s hs).root) {C' : Set (SemidirectedArc hN.1 hN.2 hX)}
    (hcyc : IsCycle (unrooted N hN hX).graph C')
    (hC' : liftEdges hN.1 hN.2 hX C' = Subtype.val '' cycleChainArcs _ D)
    (h : (unrooted N hN hX).graph.Walks C'ᶜ (sdNode hN.1 hN.2 hX u.1.1)
      (sdNode hN.1 hN.2 hX u'.1.1)) : u = u' := by
  have hZ : (s : Set X).Nontrivial := Finset.one_lt_card_iff_nontrivial.mp (by omega)
  have : Finite E := hN.1.finite_arcs
  have : Fintype E := Fintype.ofFinite E
  have heq := eq_of_walks_compl_of_mem_cycleNodes hN h1 hX hcyc
    (sdNode_mem_cycleNodes_of_quartetLSA hN hX hs hu hur hC')
    (sdNode_mem_cycleNodes_of_quartetLSA hN hX hs hu' hur' hC') h
  have hval := congrArg (sdVert hN.1 hX) heq
  rw [sdVert_sdNode hN.1 hN.2 hX ((lsa_univ_reaches hN.1 hZ.nonempty).trans u.1.2.1)
      (quartetLSA_val_ne_lsa_univ hN hX hs hur),
    sdVert_sdNode hN.1 hN.2 hX ((lsa_univ_reaches hN.1 hZ.nonempty).trans u'.1.2.1)
      (quartetLSA_val_ne_lsa_univ hN hX hs hur')] at hval
  exact Subtype.ext (Subtype.ext hval)

end Quartet

/-! ### The correspondence -/

/-- **Lemma 12, the cycle of `N⁻` gives the 4-cycle of `Q⁻_s`** (proof of Lemma 12): if `N⁻` has a
cycle `C_v` for which the taxa of `s` are in distinct `v`-blocks, one of them in the hybrid block,
then `s` induces a quartet network with a 4-cycle.

The cycle of `N` of `C_v` lies below `LSA(s)`. Otherwise the root reaches the top of the cycle
avoiding `LSA(s)`, then `v` along one of the two sides of the cycle (were `LSA(s)` on both, the two
sides from `LSA(s)` to the parents of `v` would close a cycle through an arc into `v` without the
arc into `LSA(s)`, another cycle sharing an arc with `C_v`), and then the taxon of `s` below `v`;
and `LSA(s)` is not below `v`, whose block would then hold all of `s`. The arcs of the cycle are
above that taxon, so they are arcs of the LSA network of `s` (the edges of `N⁻` on simple treks
between taxa of `s`, `mem_trekEdges_iff`), and their chains form a cycle of `Q⊕_s` with hybrid node
`v`. Each taxon of `s` is in the block of a node of this cycle other than the root, and then in the
block of that node in `N⁻`; the four taxa being in distinct `v`-blocks, the cycle has four nodes
other than the root, and no more since `Q⊕_s` has four taxa. The size of `C_v`, at least four in the
paper's statement, follows from the other hypotheses, and the statement leaves it out.

The paper asserts this step without argument (TeX l. 1102); this proof fills it. -/
theorem exists_fourCycle_of_separates {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) {C : Set _} {v : _}
    (hC : IsCycle (unrooted N hN hX).graph C) (hv : IsHybridNodeOf (unrooted N hN hX) C v)
    (hblk : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y)
    (hdesc : ∃ x ∈ s, DescendsFrom (unrooted N hN hX) v x) :
    ∃ C' v' k, InducesCycleType (quartetLSA N hN.1 s hs) C' v' 4 k := by
  have : Finite V := hN.1.finite_vertices
  have : Finite E := hN.1.finite_arcs
  have hZ : (s : Set X).Nontrivial := Finset.one_lt_card_iff_nontrivial.mp (by omega)
  set G := unrooted N hN hX with hG_def
  set m₀ := lsa hN.1 Set.univ Set.univ_nonempty with hm₀_def
  set m := lsa hN.1 (s : Set X) hZ.nonempty with hm_def
  have hst := (lsa_spec hN.1 (s : Set X) hZ.nonempty).1
  have hm₀m : N.graph.Reaches m₀ m := lsa_univ_reaches hN.1 hZ.nonempty
  -- the cycle `CN` of `N` of `C`, with the hybrid node `vN` of `v`
  set CN := liftEdges hN.1 hN.2 hX C with hCN_def
  have hCN : IsCycle N.graph CN := isCycle_liftEdges _ _ _ hC
  obtain ⟨hvC, hv2⟩ := (isHybridNodeOf_semidirected_iff hN.1 hN.2 hX hN h1 hC v).1 hv
  set vN := sdVert hN.1 hX v with hvN_def
  have hvCN : vN ∈ cycleNodes N.graph CN := (sdVert_mem_cycleNodes_liftEdges_iff _ _ _ C v).2 hvC
  obtain ⟨a, ha, hda⟩ := hdesc
  have hva : N.graph.Reaches vN (N.leaf a) :=
    (descendsFrom_semidirected_iff hN.1 hN.2 hX v hv2 a).1 hda
  have hm₀v : N.graph.Reaches m₀ vN := ((mem_range_sdVert hN.1 hX vN).1 ⟨v, rfl⟩).1
  have hCNbelow : ∀ f ∈ CN, N.graph.Reaches m₀ (N.graph.source f) := by
    rintro f ⟨g, -, rfl | ⟨hg, rfl⟩⟩
    · exact ((mem_range_sdArc hN.1 hN.2 hX _).1 ⟨g, rfl⟩).1
    · rw [(sdRootArc_spec hN.1 hN.2 hX).1]
      exact .refl
  -- no node below `vN` is above every taxon of `s`: the taxa below `vN` are in its block
  have hbelowv : ∀ y, N.graph.Reaches vN y → (∀ x ∈ s, N.graph.Reaches y (N.leaf x)) → False := by
    intro y hvy hy
    have hwalk : ∀ x ∈ s, G.graph.Walks Cᶜ v (G.leaf x) := by
      intro x hx
      have hW : N.graph.Walks {f | f ∉ CN ∧ N.graph.Reaches m₀ (N.graph.source f)} vN (N.leaf x) :=
        walks_of_reaches_of_forall (hvy.trans (hy x hx)) fun f hf _ => by
          refine ⟨fun hfCN => ?_, hm₀v.trans hf⟩
          have hfs : N.graph.source f = vN := eq_of_reaches_of_reaches hN.1.acyclic
            (reaches_hybrid hN h1 hCN hvCN hv2 _ (source_mem_cycleNodes hfCN)) hf
          exact notMem_of_source_eq_hybrid hN h1 hCN hvCN hv2 hfs hfCN
      have h := walks_semidirected_of_walks hN.1 hN.2 hX (F := Cᶜ)
        (A := {f | f ∉ CN ∧ N.graph.Reaches m₀ (N.graph.source f)}) (fun f hf => hf.2)
        (fun g hg hgC => hg.1 ((sdArc_mem_liftEdges_iff hN.1 hN.2 hX C g).2 hgC)) hW
      rwa [sdNode_sdVert, sdNode_leaf] at h
    obtain ⟨x, hx, y', hy', hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < #s)
    exact hblk x hx y' hy' hxy ((G.graph.walks_symm (hwalk x hx)).trans (hwalk y' hy'))
  have hvm : vN ≠ m := fun h => hbelowv m (h ▸ .refl) fun x hx => hst.reaches_leaf hN.1 hx
  -- the top `t` of `CN`
  obtain ⟨t, htC, htreach, htin, hentry, hroot⟩ := h1.exists_top hN.1 hCN
  -- **`LSA(s)` is above `t`**: otherwise the root reaches `t` avoiding `LSA(s)`, and then one
  -- of the two parents of `vN` along `CN`, and `vN`, and then a taxon of `s` below `vN`
  have hmt : N.graph.Reaches m t := by
    by_contra hmt
    have htm : t ≠ m := fun h => hmt (h ▸ .refl)
    have hpt : N.HasPathAvoiding N.root t m := by
      by_contra hp
      exact hmt (reaches_of_not_hasPathAvoiding (hN.1.root_reaches t) hp).2
    have hpv : N.HasPathAvoiding N.root vN m := by
      refine ⟨hpt.1, hvm, hpt.2.2.trans ?_⟩
      by_contra hno
      -- the two arcs into `vN`, on `CN`
      obtain ⟨h₁, h₂, hne, hs₂⟩ := Set.ncard_eq_two.1 hv2
      have ht₁ : N.graph.target h₁ = vN := (Set.ext_iff.1 hs₂ h₁).2 (Or.inl rfl)
      have ht₂ : N.graph.target h₂ = vN := (Set.ext_iff.1 hs₂ h₂).2 (Or.inr rfl)
      have hh₁ : h₁ ∈ CN := mem_of_target_eq_hybrid hN h1 hCN hvCN hv2 ht₁
      have hh₂ : h₂ ∈ CN := mem_of_target_eq_hybrid hN h1 hCN hvCN hv2 ht₂
      set CAdj : V → V → Prop := fun a b => ∃ f ∈ CN, N.graph.source f = a ∧ N.graph.target f = b
        with hCAdj
      -- `t` reaches every node of `CN` along `CN`
      have hS1 : ∀ c ∈ cycleNodes N.graph CN, Relation.ReflTransGen CAdj t c := by
        let rel : V → V → Prop := fun x y => Relation.TransGen N.graph.Adj x y
        have : IsTrans V rel := ⟨fun _ _ _ h h' => h.trans h'⟩
        have : Std.Irrefl rel := ⟨fun x h => hN.1.acyclic x h⟩
        have hwf : WellFounded rel := Finite.wellFounded_of_trans_of_irrefl rel
        intro c
        induction c using hwf.induction with
        | _ c ih =>
          intro hc
          by_cases hct : c = t
          · rw [hct]
          have hcr : c ≠ N.root := fun h => hct (h ▸ hroot (h ▸ hc))
          obtain ⟨g, hg⟩ := (N.graph.one_le_indegree_iff c).1 (hN.1.nonroot_indegree c hcr)
          have hgC := hentry c hc hct g hg
          exact (ih _ (.single ⟨g, rfl, hg⟩) (source_mem_cycleNodes hgC)).tail ⟨g, hgC, rfl, hg⟩
      -- neither parent of `vN` is reached from `t` along `CN` avoiding `m`
      have hnav : ∀ h ∈ CN, N.graph.target h = vN →
          ¬ Relation.ReflTransGen (fun x y => CAdj x y ∧ x ≠ m ∧ y ≠ m) t (N.graph.source h) := by
        intro h hh hth hp
        refine hno ((Relation.ReflTransGen.mono (fun x y ⟨⟨f, _, hf⟩, hx, hy⟩ => ⟨⟨f, hf⟩, hx, hy⟩)
          _ _ hp).tail ⟨⟨h, rfl, hth⟩, ?_, hvm⟩)
        exact Relation.ReflTransGen.ne_of_avoiding hp htm
      have hpar₁ := Relation.ReflTransGen.through_of_not_avoiding
        (hS1 _ (source_mem_cycleNodes hh₁)) (hnav h₁ hh₁ ht₁)
      have hpar₂ := Relation.ReflTransGen.through_of_not_avoiding
        (hS1 _ (source_mem_cycleNodes hh₂)) (hnav h₂ hh₂ ht₂)
      -- so `m` is on `CN`; its arc `gm` in is on `CN`
      have hmC : m ∈ cycleNodes N.graph CN := by
        rcases Relation.ReflTransGen.cases_tail hpar₁.1 with h | ⟨c, -, f, hf, -, hft⟩
        · exact absurd h.symm htm
        · exact hft ▸ target_mem_cycleNodes hf
      have hmr : m ≠ N.root := fun h => hmt (h ▸ hN.1.root_reaches t)
      obtain ⟨gm, hgm⟩ := (N.graph.one_le_indegree_iff m).1 (hN.1.nonroot_indegree m hmr)
      have hgmC := hentry m hmC htm.symm gm hgm
      -- the paths from `m` to the parents of `vN` avoid `gm` and `h₁`
      set F : Set E := {f | f ∈ CN ∧ f ≠ gm ∧ f ≠ h₁} with hF_def
      have hcyc : ∀ {x y}, N.graph.Reaches x y → N.graph.Adj y x → False := fun h hab =>
        hN.1.acyclic _ (Relation.TransGen.tail' h hab)
      have hpath : ∀ h ∈ CN, N.graph.target h = vN →
          Relation.ReflTransGen CAdj m (N.graph.source h) →
          N.graph.Walks F m (N.graph.source h) := by
        intro h _ hth hp
        refine walks_of_reflTransGen_mem hp fun f hf h₁' h₂' => ⟨hf, fun hfg => ?_, fun hfh => ?_⟩
        · exact hcyc (by rw [← hfg]; exact h₁') ⟨gm, rfl, hgm⟩
        · exact hcyc (by rw [← ht₁, ← hfh]; exact h₂') ⟨h, rfl, hth⟩
      have hW₁ := hpath h₁ hh₁ ht₁ hpar₁.2
      have hW₂ := hpath h₂ hh₂ ht₂ hpar₂.2
      have hh₂F : h₂ ∈ F := ⟨hh₂, fun h => hvm (ht₂.symm.trans (h ▸ hgm)), Ne.symm hne⟩
      have hW : N.graph.Walks F (N.graph.target h₁) (N.graph.source h₁) := by
        rw [ht₁, ← ht₂]
        exact (Relation.ReflTransGen.single ⟨h₂, hh₂F, Or.inr ⟨rfl, rfl⟩⟩).trans
          ((N.graph.walks_symm hW₂).trans hW₁)
      obtain ⟨D, hD, hh₁D, hDsub⟩ := exists_isCycle_of_walks (e := h₁) (F := F)
        (fun h => h.2.2 rfl) hW
      have hDC : D = CN := h1 D CN hD hCN ⟨h₁, hh₁D, hh₁⟩
      rcases hDsub (hDC ▸ hgmC : gm ∈ D) with h | h
      · exact hvm (ht₁.symm.trans (h ▸ hgm))
      · exact h.2.1 rfl
    have hpa : N.HasPathAvoiding vN (N.leaf a) m := by
      by_contra hp
      exact hbelowv m (reaches_of_not_hasPathAvoiding hva hp).1 fun x hx =>
        hst.reaches_leaf hN.1 hx
    exact hst a ha ⟨hpv.1, hpa.2.1, hpv.2.2.trans hpa.2.2⟩
  -- so the arcs of `CN` are arcs of the LSA network `L` on `s`: they form a cycle `CL` of `L`, and
  -- the arcs of `Q⊕_s` whose chains are on `CL` a cycle `CQ` of `Q⊕_s`
  have hCNL : ∀ f ∈ CN, f ∈ N.belowArcs m (s : Set X) := fun f hf =>
    ⟨hmt.trans (htreach _ (source_mem_cycleNodes hf)),
      ⟨a, ha, (reaches_hybrid hN h1 hCN hvCN hv2 _ (target_mem_cycleNodes hf)).trans hva⟩⟩
  have hL := lsaNetwork_isPhylogenetic hN.1 hZ
  have hL1 : IsLevelOne (lsaNetwork hN.1 (s : Set X) hZ.nonempty).graph :=
    IsLevelOne.of_injective h1 Subtype.val Subtype.val Subtype.val_injective Subtype.val_injective
      (fun _ => rfl) (fun _ => rfl)
  have hCL : IsCycle (lsaNetwork hN.1 (s : Set X) hZ.nonempty).graph (Subtype.val ⁻¹' CN) :=
    hCN.preimage_of_hom Subtype.val_injective Subtype.val_injective (fun _ => rfl) (fun _ => rfl)
      fun f hf => ⟨⟨f, hCNL f hf⟩, rfl⟩
  obtain ⟨hCQ, hchain⟩ := isCycle_suppress_preimage hL hL1 hCL
  set CQ : Set {e // ¬ (lsaNetwork hN.1 (s : Set X) hZ.nonempty).IsChainVertex
      ((lsaNetwork hN.1 (s : Set X) hZ.nonempty).graph.source e)} :=
    {g | g.1 ∈ Subtype.val ⁻¹' CN} with hCQ_def
  -- the hybrid node `vQ` of `CQ`
  have hvL : vN ∈ N.belowVertices m (s : Set X) := ⟨hmt.trans (htreach _ hvCN), ⟨a, ha, hva⟩⟩
  have hv2L : (lsaNetwork hN.1 (s : Set X) hZ.nonempty).graph.indegree ⟨vN, hvL⟩ = 2 :=
    (belowNetwork_indegree hN.1 hst ⟨vN, hvL⟩ hvm).trans hv2
  have hvnc : ¬ (lsaNetwork hN.1 (s : Set X) hZ.nonempty).IsChainVertex ⟨vN, hvL⟩ := fun h => by
    have := h.1
    omega
  have hvQC : (⟨⟨vN, hvL⟩, hvnc⟩ : {v // ¬
    (lsaNetwork hN.1 (s : Set X) hZ.nonempty).IsChainVertex v})
      ∈ cycleNodes (quartetLSA N hN.1 s hs).graph CQ := by
    refine mem_cycleNodes_suppress_of_val hL ?_
    rw [hchain]
    obtain ⟨f, hf, h⟩ := hvCN
    refine ⟨⟨f, hCNL f hf⟩, hf, ?_⟩
    rcases h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hvQ2 : (quartetLSA N hN.1 s hs).graph.indegree ⟨⟨vN, hvL⟩, hvnc⟩ = 2 :=
    (suppress_indegree hL _).trans hv2L
  -- `CQ` has four nodes other than the root: at most as many as taxa, and the taxa of `s`, in
  -- distinct blocks of `C`, are in the blocks of distinct nodes of `CQ`
  have : Fintype {v // ¬ (lsaNetwork hN.1 (s : Set X) hZ.nonempty).IsChainVertex v} :=
    Fintype.ofFinite _
  have : Fintype {e // ¬ (lsaNetwork hN.1 (s : Set X) hZ.nonempty).IsChainVertex
      ((lsaNetwork hN.1 (s : Set X) hZ.nonempty).graph.source e)} := Fintype.ofFinite _
  have hcs : Fintype.card (s : Set X) = 4 := by simp [hs]
  have hcard : #(cycleNodesOffRoot (quartetLSA N hN.1 s hs) CQ) = 4 := by
    refine le_antisymm ?_ ?_
    · have := card_cycleNodesOffRoot_le (quartetLSA_isBinaryRootedNetwork hN hs)
        (quartetLSA_isLevelOne hN h1 hs) (quartetLSA_isLSANetwork hN hs) hCQ
      rwa [hcs] at this
    · have hlift : liftEdges hN.1 hN.2 hX C = Subtype.val '' cycleChainArcs _ CQ := by
        rw [hchain, Set.image_preimage_eq_of_subset fun f hf => ⟨⟨f, hCNL f hf⟩, rfl⟩]
      obtain ⟨hall, -⟩ := exists_walks_unrooted_quartetLSA hN hX hs h1 hCQ hvQC hvQ2 hlift
      choose uOf huOf hur hwalk using hall
      have hinj : Set.InjOn uOf (Finset.univ : Finset (s : Set X)) := fun x _ y _ hxy => by
        by_contra hne
        exact hblk x.1 x.2 y.1 y.2 (fun h => hne (Subtype.ext h))
          ((G.graph.walks_symm (hwalk x)).trans (by rw [hxy]; exact hwalk y))
      have := Finset.card_le_card_of_injOn uOf
        (fun x _ => mem_cycleNodesOffRoot.2 ⟨huOf x, hur x⟩) hinj
      rwa [Finset.card_univ, hcs] at this
  refine ⟨_, _, _, hCQ, hvQC, hvQ2, ?_, rfl⟩
  exact (card_cycleNodesOffRoot (N := quartetLSA N hN.1 s hs) hCQ).symm.trans hcard

/-- **Lemma 12, the 4-cycle of `Q⁻_s` gives the cycle of `N⁻`** (proof of Lemma 12): if `Q⁻_s` has a
4-cycle with hybrid node `w`, then `N⁻` has a cycle of size at least four with hybrid node `w'`, the
same node of `N`, for which the taxa of `s` are in distinct `w'`-blocks, one of them descending from
`w'`.

The 4-cycle is the image of a cycle of `Q⊕_s` with four nodes other than the root. The chains of its
arcs form a cycle of `N` below `LSA(X)`, the cycle of `N` of a cycle `C'` of `N⁻` with at least as
many edges. The block in `Q⊕_s` of each of the four nodes holds a taxon of `s`, joined to the node
by a walk of `Q⊕_s` avoiding the cycle, and the chains of the arcs of that walk give a walk of `N⁻`
avoiding `C'`. So the four nodes, distinct nodes of `C'`, have taxa of `s` in their `w'`-blocks,
which are disjoint: two taxa in distinct blocks of `Q⁻_s` are in distinct blocks of `N⁻`.

The paper asserts this step without argument (TeX l. 1103); this proof fills it. -/
theorem exists_separates_of_fourCycle {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {s : Finset X} (hs : #s = 4) {C : Set _} {w : _}
    (hC : IsCycle (quartetUnrooted N hN s hs).graph C) (hC4 : C.ncard = 4)
    (hw : IsHybridNodeOf (quartetUnrooted N hN s hs) C w) :
    ∃ C' w', 4 ≤ C'.ncard ∧ IsCycle (unrooted N hN hX).graph C' ∧
      IsHybridNodeOf (unrooted N hN hX) C' w' ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C' x y) ∧
      (∃ x ∈ s, DescendsFrom (unrooted N hN hX) w' x) ∧ w'.1.1 = w.1.1.1.1 := by
  have : Finite V := hN.1.finite_vertices
  have : Finite E := hN.1.finite_arcs
  have hZ : (s : Set X).Nontrivial := Finset.one_lt_card_iff_nontrivial.mp (by omega)
  have hL := lsaNetwork_isPhylogenetic hN.1 hZ
  have hQ := quartetLSA_isBinaryRootedNetwork hN hs
  have hQ1 := quartetLSA_isLevelOne hN h1 hs
  have hQlsa := quartetLSA_isLSANetwork hN hs
  have hXs : Nontrivial (s : Set X) := hZ.coe_sort
  have hr := lsa_univ_eq_root hQ.1 hXs hQlsa
  have : Fintype {v // ¬ (lsaNetwork hN.1 (s : Set X) hZ.nonempty).IsChainVertex v} :=
    Fintype.ofFinite _
  have : Fintype {e // ¬ (lsaNetwork hN.1 (s : Set X) hZ.nonempty).IsChainVertex
      ((lsaNetwork hN.1 (s : Set X) hZ.nonempty).graph.source e)} := Fintype.ofFinite _
  -- the cycle `CQ` of `Q⊕_s` of `C`, with the hybrid node `wQ` of `w`
  set CQ := liftEdges hQ.1 hQ.2 hXs C with hCQ_def
  have hCQ : IsCycle (quartetLSA N hN.1 s hs).graph CQ := isCycle_liftEdges _ _ _ hC
  obtain ⟨hwC, hw2⟩ := (isHybridNodeOf_semidirected_iff _ _ _ hQ hQ1 hC w).1 hw
  have hwCQ := (sdVert_mem_cycleNodes_liftEdges_iff _ _ _ C w).2 hwC
  set wQ := sdVert hQ.1 hXs w with hwQ_def
  have hwQr : wQ ≠ (quartetLSA N hN.1 s hs).root := hr ▸ sdVert_ne_lsa hQ.1 hXs w
  -- the cycle `CN` of `N` of the chains of `CQ`, and the cycle `C'` of `N⁻`
  have hCL := isCycle_cycleChainArcs hL hCQ
  have hCN : IsCycle N.graph (Subtype.val '' cycleChainArcs _ CQ) :=
    hCL.image_of_hom Subtype.val_injective Subtype.val_injective (fun _ => rfl) (fun _ => rfl)
  have hbelow : ∀ f ∈ Subtype.val '' cycleChainArcs _ CQ,
      N.graph.Reaches (lsa hN.1 Set.univ Set.univ_nonempty) (N.graph.source f) := by
    rintro _ ⟨e, -, rfl⟩
    exact (lsa_univ_reaches hN.1 hZ.nonempty).trans e.2.1
  obtain ⟨hC', hlift⟩ := isCycle_semidirected_preimage hN.1 hN.2 hX hN h1 hCN hbelow
  set C' := {g | sdArc hN.1 hN.2 hX g ∈ Subtype.val '' cycleChainArcs _ CQ} with hC'_def
  -- the hybrid node `w'` of `C'`
  set w' := sdNode hN.1 hN.2 hX wQ.1.1 with hw'_def
  have hw'v : sdVert hN.1 hX w' = wQ.1.1 :=
    sdVert_sdNode _ _ _ ((lsa_univ_reaches hN.1 hZ.nonempty).trans wQ.1.2.1)
      (quartetLSA_val_ne_lsa_univ hN hX hs hwQr)
  have hw2N : N.graph.indegree wQ.1.1 = 2 := by
    rw [← hw2, show (quartetLSA N hN.1 s hs).graph.indegree wQ =
      (lsaNetwork hN.1 (s : Set X) hZ.nonempty).graph.indegree wQ.1 from suppress_indegree hL wQ]
    exact (belowNetwork_indegree hN.1 (lsa_spec hN.1 _ hZ.nonempty).1 wQ.1
      fun h => hwQr (Subtype.ext (Subtype.ext h))).symm
  have hw'C : w' ∈ cycleNodes (unrooted N hN hX).graph C' :=
    sdNode_mem_cycleNodes_of_quartetLSA hN hX hs hwCQ hwQr hlift
  have hw' : IsHybridNodeOf (unrooted N hN hX) C' w' :=
    (isHybridNodeOf_semidirected_iff hN.1 hN.2 hX hN h1 hC' w').2 ⟨hw'C, hw'v ▸ hw2N⟩
  refine ⟨C', w', ?_, hC', hw', ?_, ?_, hw'v⟩
  · -- `C'` has at least four edges: as many as `CN`, less one when it passes through `LSA(X)`, and
    -- then `CQ` passes through the root and has five edges
    have hncard := ncard_liftEdges hN.1 hN.2 hX C'
    rw [hlift, Set.ncard_image_of_injective _ Subtype.val_injective] at hncard
    have h₂ : CQ.ncard ≤ (cycleChainArcs _ CQ).ncard := by
      rw [← Set.ncard_image_of_injective CQ Subtype.val_injective]
      exact Set.ncard_le_ncard (by rintro _ ⟨g, hg, rfl⟩; exact val_mem_cycleChainArcs_iff.2 hg)
        (Set.toFinite _)
    have h₃ := card_cycleNodesOffRoot_liftEdges _ _ _ hr hC
    rw [card_cycleNodesOffRoot hCQ, hC4] at h₃
    split_ifs at hncard with hm
    · obtain ⟨g, ⟨f, hf, hgf⟩, hgm⟩ := hm
      have hfm : (lsaNetwork hN.1 (s : Set X) hZ.nonempty).graph.source f =
          (lsaNetwork hN.1 (s : Set X) hZ.nonempty).root := by
        refine Subtype.ext ?_
        show N.graph.source f.1 = lsa hN.1 (s : Set X) hZ.nonempty
        rw [hgf, hgm]
        exact eq_of_reaches_of_reaches hN.1.acyclic (lsa_univ_reaches hN.1 hZ.nonempty)
          (hgm ▸ hgf ▸ f.2.1)
      have hroot : (quartetLSA N hN.1 s hs).root ∈ cycleNodes (quartetLSA N hN.1 s hs).graph CQ :=
        mem_cycleNodes_suppress_of_val hL ⟨f, hf, Or.inl hfm⟩
      simp only [hroot, ↓reduceIte] at h₃
      omega
    · split_ifs at h₃ <;> omega
  · -- the taxa of `s` are in the blocks of the four nodes of `CQ` other than the root, one in each
    obtain ⟨hall, hnode⟩ := exists_walks_unrooted_quartetLSA hN hX hs h1 hCQ hwCQ hw2 hlift
    choose uOf huOf hur hwalk using hall
    have hsurj : cycleNodesOffRoot (quartetLSA N hN.1 s hs) CQ ⊆ Finset.univ.image uOf := by
      intro u hu
      obtain ⟨huC, hur'⟩ := mem_cycleNodesOffRoot.1 hu
      obtain ⟨x, hx⟩ := hnode u huC hur'
      refine Finset.mem_image.2 ⟨x, Finset.mem_univ _, ?_⟩
      exact eq_of_walks_unrooted_quartetLSA hN hX hs h1 (huOf x) (hur x) huC hur' hC' hlift
        ((hwalk x).trans ((unrooted N hN hX).graph.walks_symm hx))
    have h₃ : #(cycleNodesOffRoot (quartetLSA N hN.1 s hs) CQ) = C.ncard :=
      card_cycleNodesOffRoot_liftEdges _ _ _ hr hC
    rw [hC4] at h₃
    have hinj : Set.InjOn uOf (Finset.univ : Finset (s : Set X)) := by
      refine Finset.card_image_iff.1 (le_antisymm Finset.card_image_le ?_)
      have := Finset.card_le_card hsurj
      have hcs : Fintype.card (s : Set X) = 4 := by simp [hs]
      rw [Finset.card_univ, hcs]
      omega
    intro x hx y hy hxy hsame
    have hW : (unrooted N hN hX).graph.Walks C'ᶜ (sdNode hN.1 hN.2 hX (uOf ⟨x, hx⟩).1.1)
        (sdNode hN.1 hN.2 hX (uOf ⟨y, hy⟩).1.1) :=
      ((hwalk ⟨x, hx⟩).trans hsame).trans ((unrooted N hN hX).graph.walks_symm (hwalk ⟨y, hy⟩))
    have := hinj (Finset.mem_coe.2 (Finset.mem_univ ⟨x, hx⟩))
      (Finset.mem_coe.2 (Finset.mem_univ ⟨y, hy⟩))
      (eq_of_walks_unrooted_quartetLSA hN hX hs h1 (huOf ⟨x, hx⟩) (hur ⟨x, hx⟩) (huOf ⟨y, hy⟩)
        (hur ⟨y, hy⟩) hC' hlift hW)
    exact hxy (congrArg Subtype.val this)
  · -- a taxon below the hybrid node `wQ` of `Q⊕_s`, so below `w'` in `N`
    obtain ⟨x, hx⟩ := RootedNetwork.exists_reaches_leaf hQ.1 wQ
    have : Fintype (N.belowVertices (lsa hN.1 (s : Set X) hZ.nonempty) (s : Set X)) :=
      Fintype.ofFinite _
    have : Fintype (N.belowArcs (lsa hN.1 (s : Set X) hZ.nonempty) (s : Set X)) :=
      Fintype.ofFinite _
    have hxL := reaches_of_suppress_reaches hL hx
    have hxN : N.graph.Reaches wQ.1.1 (N.leaf x.1) := belowNetwork_reaches_iff.1 hxL
    exact ⟨x.1, x.2, (descendsFrom_semidirected_iff hN.1 hN.2 hX w' (hw'v ▸ hw2N) x.1).2
      (hw'v ▸ hxN)⟩

end Banos2019
