module

public import Banos2019.Identify.TildeDefs
public import Banos2019.Identify.TildeBase
public import Banos2019.Identify.TreeOfCycles

/-!
# A cycle of size at least four in the proof of Theorem 4 (Baños 2019, Section 8)

* `exists_not_isFourNetworkBlock_of_ne`: for two cycles of size at least four, the block of the node
  of the first toward the second is not a 4-network block, and the second has all the taxa outside
  it in one of its blocks.
* `exists_leaf_bigCycle`: when `N⁻` has at least two cycles of size at least four, one of them,
  `C_v`, is a leaf of the tree of cycles: all its `v`-blocks but that of a node `u` are 4-network
  blocks, the block of `u` is not, and every other such cycle has all the taxa outside the block of
  `u` in one of its blocks.
* `tilde_sdIso_of_singletonBlocks`: two networks each with a cycle of size at least four whose
  blocks are single taxa, with the same adjacent blocks and, for size at least five, the same hybrid
  block, have isomorphic networks `Ñ`.

The second rests on a description of `Ñ` when the blocks of a cycle `C` of size at least four are
single taxa, for a semidirected network with the properties of `N⁻` that it uses
(`SingletonBlockCycle`, `singletonBlockCycle_unrooted`):

* `SingletonBlockCycle.ncard_le_two`, `SingletonBlockCycle.exists_leaf_eq`: the other cycles have
  size two, and a node on no cycle is a taxon.
* `SingletonBlockCycle.isBranch_iff`: the nodes that `Ñ` keeps are the taxa and the nodes of `C`.
* `SingletonBlockCycle.exists_isChainOf_pendantEdges`: the edges hanging from the node of `C` of the
  block of a taxon form a chain from that node to the taxon.
* `SingletonBlockCycle.nonempty_sdIso_cycleModel`: `Ñ` is a cycle with a taxon hanging from each
  node (`cycleModel`).
* `walks_compl_of_not_walks_compl`: the argument of Lemma 13, for two cycles with no common edge.
* `contract_mk_eq_iff_of_cycles`, `contract_degree_of_notMem_of_cycles`,
  `contract_degree_of_mem_of_cycles`, `walks_of_contract_walks_of_cycles`,
  `contract_walks_of_walks_of_cycles`: contracting some of the cycles of a network whose cycles
  share no node.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

section Leaf

variable {V' E' : Type*} (G : DirectedMultigraph V' E')

/-- **Another cycle collects the nodes outside one component** (the argument of Lemma 13): let `C`
and `C'` be cycles with no common edge, `C'` in the component of the node `w` of `C` once the edges
of `C` are removed, and `u'` a node joined to a node of `C` avoiding `C'`. A node `p` outside that
component reaches `C` avoiding `C'`, so `u'` and `p` are joined avoiding `C'`. -/
theorem walks_compl_of_not_walks_compl (hG : G.IsConnected) {C C' : Set E'} (hC : IsCycle G C)
    (hC' : IsCycle G C') (hCC' : ∀ f ∈ C, f ∉ C') {w z₀ : V'} (hz₀ : z₀ ∈ cycleNodes G C')
    (hwz : G.Walks Cᶜ w z₀) {a u' : V'} (ha : a ∈ cycleNodes G C) (hu'a : G.Walks C'ᶜ u' a) {p : V'}
    (hp : ¬ G.Walks Cᶜ w p) : G.Walks C'ᶜ u' p := by
  have hK : ∀ f ∈ C', G.Walks Cᶜ (G.source f) z₀ := fun f hf =>
    walks_mono (show C' ⊆ Cᶜ from fun g hg hgC => hCC' g hgC hg)
      (walks_cycle_of_mem_cycleNodes G hC' ⟨f, hf, Or.inl rfl⟩ hz₀)
  obtain ⟨z, hz, hpz⟩ := exists_walks_cycleNodes_of_not_walks G hG hK
    (fun h => hp (hwz.trans (G.walks_symm h)))
  exact (hu'a.trans (walks_mono (show C ⊆ C'ᶜ from fun g hg => hCC' g hg)
    (walks_cycle_of_mem_cycleNodes G hC ha hz))).trans
    (G.walks_symm (walks_mono Set.inter_subset_right hpz))

/-- At a node of degree one of a multigraph without loops, two edges are equal. -/
theorem eq_of_incident_of_degree_eq_one [Finite E'] {G : DirectedMultigraph V' E'}
    (hloop : ∀ e, G.source e ≠ G.target e) {u : V'} (hu : degree G u = 1) {e e' : E'}
    (he : G.source e = u ∨ G.target e = u) (he' : G.source e' = u ∨ G.target e' = u) : e = e' := by
  rw [degree_eq_ncard_incident hloop] at hu
  obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 hu
  have h₁ : e ∈ ({e₀} : Set E') := he₀ ▸ he
  have h₂ : e' ∈ ({e₀} : Set E') := he₀ ▸ he'
  rw [Set.mem_singleton_iff] at h₁ h₂
  rw [h₁, h₂]

end Leaf

section ContractSome

variable {V E X : Type*} {G : SemidirectedNetwork V E X} {P : Set E → Prop}

/-- Nodes identified by contracting the cycles satisfying `P` are joined along such cycles. -/
theorem walks_of_contract_eq_of_cycles {a b : V}
    (h : (Quot.mk _ a : Quot (ContractRel G.graph P)) = Quot.mk _ b) :
    G.graph.Walks {e | ∃ C, IsCycle G.graph C ∧ P C ∧ e ∈ C} a b := by
  have hg := Quot.eqvGen_exact h
  clear h
  induction hg with
  | rel x y hxy =>
    obtain ⟨C, hC, hPC, hx, hy⟩ := hxy
    obtain ⟨g, hg, -⟩ := id hx
    refine walks_mono ?_ (hC.walks_sdiff_singleton hg hx hy)
    intro e he
    exact ⟨C, hC, hPC, he.1⟩
  | refl => exact .refl
  | symm x y _ ih => exact G.graph.walks_symm ih
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A walk of the contracted network is a walk of the network**, on its edges and on edges of the
contracted cycles. -/
theorem walks_of_contract_walks_of_cycles {F : Set {e // ∀ C, IsCycle G.graph C → P C → e ∉ C}}
    {a b : V} (h : (contractCycles G P).graph.Walks F (Quot.mk _ a) (Quot.mk _ b)) :
    G.graph.Walks (Subtype.val '' F ∪ {e | ∃ C, IsCycle G.graph C ∧ P C ∧ e ∈ C}) a b := by
  suffices key : ∀ x y, (contractCycles G P).graph.Walks F x y → ∀ a b, Quot.mk _ a = x →
      Quot.mk _ b = y →
      G.graph.Walks (Subtype.val '' F ∪ {e | ∃ C, IsCycle G.graph C ∧ P C ∧ e ∈ C}) a b from
    key _ _ h a b rfl rfl
  intro x y hxy
  induction hxy with
  | refl =>
    intro a b ha hb
    exact walks_mono Set.subset_union_right (walks_of_contract_eq_of_cycles (ha.trans hb.symm))
  | @tail y z _ hst ih =>
    intro a b ha hb
    obtain ⟨f, hf, hj⟩ := hst
    have hstep : G.graph.Walks (Subtype.val '' F ∪ {e | ∃ C, IsCycle G.graph C ∧ P C ∧ e ∈ C})
        (G.graph.source f.1) (G.graph.target f.1) :=
      .single ⟨f.1, Or.inl ⟨f, hf, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ((ih a _ ha h₁).trans hstep).trans
        (walks_mono Set.subset_union_right (walks_of_contract_eq_of_cycles (h₂.trans hb.symm)))
    · exact ((ih a _ ha h₂).trans (G.graph.walks_symm hstep)).trans
        (walks_mono Set.subset_union_right (walks_of_contract_eq_of_cycles (h₁.trans hb.symm)))

/-- **A walk of the network is a walk of the contracted network**, on the edges of the walk that
are kept, when every cycle with an edge of the walk is contracted. -/
theorem contract_walks_of_walks_of_cycles {F : Set E} {a b : V} (h : G.graph.Walks F a b)
    (hF : ∀ f ∈ F, ∀ C, IsCycle G.graph C → f ∈ C → P C) :
    (contractCycles G P).graph.Walks {e | e.1 ∈ F} (Quot.mk _ a) (Quot.mk _ b) := by
  induction h with
  | refl => exact .refl
  | @tail c d _ hst ih =>
    obtain ⟨f, hf, hj⟩ := hst
    by_cases hc : ∃ C, IsCycle G.graph C ∧ f ∈ C
    · obtain ⟨C, hC, hfC⟩ := hc
      have : (Quot.mk _ c : Quot (ContractRel G.graph P)) = Quot.mk _ d := by
        apply Quot.sound
        refine ⟨C, hC, hF f hf C hC hfC, ?_, ?_⟩
        · rcases hj with ⟨h₁, -⟩ | ⟨-, h₂⟩
          exacts [⟨f, hfC, Or.inl h₁⟩, ⟨f, hfC, Or.inr h₂⟩]
        · rcases hj with ⟨-, h₂⟩ | ⟨h₁, -⟩
          exacts [⟨f, hfC, Or.inr h₂⟩, ⟨f, hfC, Or.inl h₁⟩]
      rw [← this]
      exact ih
    · push Not at hc
      refine ih.tail ⟨⟨f, fun C hC _ => hc C hC⟩, hf, ?_⟩
      rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg _ h₁, congrArg _ h₂⟩
      · exact Or.inr ⟨congrArg _ h₁, congrArg _ h₂⟩

variable (hnd : ∀ C C', IsCycle G.graph C → IsCycle G.graph C' →
  (cycleNodes G.graph C ∩ cycleNodes G.graph C').Nonempty → C = C')
include hnd

/-- With cycles sharing no node, contracting identifies exactly the nodes of each contracted
cycle. -/
theorem contract_mk_eq_iff_of_cycles {a b : V} :
    (Quot.mk _ a : Quot (ContractRel G.graph P)) = Quot.mk _ b ↔
      a = b ∨ ∃ C, IsCycle G.graph C ∧ P C ∧ a ∈ cycleNodes G.graph C ∧
        b ∈ cycleNodes G.graph C := by
  constructor
  · intro h
    have hg := Quot.eqvGen_exact h
    clear h
    induction hg with
    | rel x y hxy =>
      obtain ⟨C, hC, hPC, hx, hy⟩ := hxy
      exact Or.inr ⟨C, hC, hPC, hx, hy⟩
    | refl => exact Or.inl rfl
    | symm x y _ ih =>
      rcases ih with rfl | ⟨C, hC, hPC, h₁, h₂⟩
      exacts [Or.inl rfl, Or.inr ⟨C, hC, hPC, h₂, h₁⟩]
    | trans x y z _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨C, hC, hPC, h₁, h₂⟩
      · exact ih₂
      · rcases ih₂ with rfl | ⟨C', hC', -, h₁', h₂'⟩
        · exact Or.inr ⟨C, hC, hPC, h₁, h₂⟩
        · obtain rfl := hnd C C' hC hC' ⟨y, h₂, h₁'⟩
          exact Or.inr ⟨C, hC, hPC, h₁, h₂'⟩
  · rintro (rfl | ⟨C, hC, hPC, h₁, h₂⟩)
    · rfl
    · exact Quot.sound ⟨C, hC, hPC, h₁, h₂⟩

/-- **The contracted network has no loops**, when the network has none and its cycles share no
node: an edge joining two nodes of a contracted cycle would close another cycle with it. -/
theorem contract_source_ne_target_of_cycles (hloop : ∀ e, G.graph.source e ≠ G.graph.target e)
    (g : {e // ∀ C, IsCycle G.graph C → P C → e ∉ C}) :
    (contractCycles G P).graph.source g ≠ (contractCycles G P).graph.target g := by
  intro h
  rcases (contract_mk_eq_iff_of_cycles hnd).1 h with h' | ⟨C, hC, hPC, hs, ht⟩
  · exact hloop g.1 h'
  · have hgC : g.1 ∉ C := g.2 C hC hPC
    obtain ⟨C'', hC'', hgC'', -⟩ := exists_isCycle_of_walks hgC
      (walks_cycle_of_mem_cycleNodes G.graph hC ht hs)
    have := hnd C'' C hC'' hC ⟨_, ⟨g.1, hgC'', Or.inl rfl⟩, hs⟩
    exact hgC (this ▸ hgC'')

/-- A node on no contracted cycle keeps its degree in the contraction. -/
theorem contract_degree_of_notMem_of_cycles {v : V}
    (hv : ∀ C, IsCycle G.graph C → P C → v ∉ cycleNodes G.graph C) :
    degree (contractCycles G P).graph (Quot.mk _ v) = degree G.graph v := by
  have hcls : ∀ w, (Quot.mk _ w : Quot (ContractRel G.graph P)) = Quot.mk _ v ↔ w = v := fun w => by
    rw [contract_mk_eq_iff_of_cycles hnd]
    constructor
    · rintro (h | ⟨C, hC, hPC, -, hvC⟩)
      exacts [h, absurd hvC (hv C hC hPC)]
    · exact Or.inl
  have hall : ∀ e : E, (G.graph.source e = v ∨ G.graph.target e = v) →
      ∀ C, IsCycle G.graph C → P C → e ∉ C := by
    intro e he C hC hPC heC
    rcases he with he | he
    · exact hv C hC hPC ⟨e, heC, Or.inl he⟩
    · exact hv C hC hPC ⟨e, heC, Or.inr he⟩
  unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree
  congr 1
  · refine Set.ncard_congr (fun e _ => e.1) (fun e he => (hcls _).1 he)
      (fun e e' _ _ h => Subtype.ext h) fun e he => ⟨⟨e, hall e (Or.inr he)⟩, (hcls _).2 he, rfl⟩
  · refine Set.ncard_congr (fun e _ => e.1) (fun e he => (hcls _).1 he)
      (fun e e' _ _ h => Subtype.ext h) fun e he => ⟨⟨e, hall e (Or.inl he)⟩, (hcls _).2 he, rfl⟩

/-- **A contracted cycle has degree its size**, when every node of the cycle has degree three: each
node of the cycle has one edge off it. -/
theorem contract_degree_of_mem_of_cycles [Finite E]
    (hloop : ∀ e, G.graph.source e ≠ G.graph.target e) {C : Set E} (hC : IsCycle G.graph C)
    (hPC : P C) (h3 : ∀ w ∈ cycleNodes G.graph C, degree G.graph w = 3) {v : V}
    (hv : v ∈ cycleNodes G.graph C) :
    degree (contractCycles G P).graph (Quot.mk _ v) = C.ncard := by
  have hcls : ∀ w, (Quot.mk _ w : Quot (ContractRel G.graph P)) = Quot.mk _ v ↔
      w ∈ cycleNodes G.graph C := fun w => by
    rw [contract_mk_eq_iff_of_cycles hnd]
    constructor
    · rintro (rfl | ⟨C', hC', -, hw, hv'⟩)
      · exact hv
      · rwa [hnd C' C hC' hC ⟨v, hv', hv⟩] at hw
    · intro hw
      exact Or.inr ⟨C, hC, hPC, hw, hv⟩
  -- one edge off the cycle at each of its nodes
  have hone : ∀ w ∈ cycleNodes G.graph C,
      {e | (G.graph.source e = w ∨ G.graph.target e = w) ∧ e ∉ C}.ncard = 1 := by
    intro w hw
    have h2 := hC.ncard_incident hloop hw
    have hd := degree_eq_ncard_incident hloop w
    rw [h3 w hw] at hd
    have := Set.ncard_inter_add_ncard_sdiff_eq_ncard
      {e | G.graph.source e = w ∨ G.graph.target e = w} C
    have hi : {e | G.graph.source e = w ∨ G.graph.target e = w} ∩ C =
        {e | e ∈ C ∧ (G.graph.source e = w ∨ G.graph.target e = w)} := by
      ext e
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hi, h2] at this
    have hd' : {e | G.graph.source e = w ∨ G.graph.target e = w} \ C =
        {e | (G.graph.source e = w ∨ G.graph.target e = w) ∧ e ∉ C} := rfl
    rw [hd'] at this
    omega
  have hoff : ∀ w ∈ cycleNodes G.graph C, ∀ e e' : E, ((G.graph.source e = w ∨
      G.graph.target e = w) ∧ e ∉ C) → ((G.graph.source e' = w ∨ G.graph.target e' = w) ∧ e' ∉ C) →
      e = e' := by
    intro w hw e e' he he'
    obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 (hone w hw)
    have h1 : e ∈ ({e₀} : Set E) := he₀ ▸ he
    have h2 : e' ∈ ({e₀} : Set E) := he₀ ▸ he'
    rw [Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  have hloopT := contract_source_ne_target_of_cycles hnd hloop (P := P)
  rw [degree_eq_ncard_incident hloopT, ← ncard_cycleNodes hC]
  refine Set.ncard_congr (fun e _ => if G.graph.source e.1 ∈ cycleNodes G.graph C then
    G.graph.source e.1 else G.graph.target e.1) ?_ ?_ ?_
  · intro e he
    split_ifs with h
    · exact h
    · rcases he with he | he
      · exact absurd ((hcls _).1 he) h
      · exact (hcls _).1 he
  · intro e e' he he' heq
    have hnot : ∀ f : {e // ∀ C, IsCycle G.graph C → P C → e ∉ C}, f.1 ∉ C := fun f =>
      f.2 C hC hPC
    have hinc : ∀ f : {e // ∀ C, IsCycle G.graph C → P C → e ∉ C},
        f ∈ {e : {e // ∀ C, IsCycle G.graph C → P C → e ∉ C} |
          (contractCycles G P).graph.source e = Quot.mk _ v ∨
            (contractCycles G P).graph.target e = Quot.mk _ v} →
        (if G.graph.source f.1 ∈ cycleNodes G.graph C then G.graph.source f.1
          else G.graph.target f.1) ∈ cycleNodes G.graph C ∧
        ((G.graph.source f.1 = (if G.graph.source f.1 ∈ cycleNodes G.graph C then
          G.graph.source f.1 else G.graph.target f.1) ∨ G.graph.target f.1 =
          (if G.graph.source f.1 ∈ cycleNodes G.graph C then G.graph.source f.1
            else G.graph.target f.1)) ∧ f.1 ∉ C) := by
      intro f hf
      split_ifs with h
      · exact ⟨h, Or.inl rfl, hnot f⟩
      · refine ⟨?_, Or.inr rfl, hnot f⟩
        rcases hf with hf | hf
        · exact absurd ((hcls _).1 hf) h
        · exact (hcls _).1 hf
    obtain ⟨hw, he₁⟩ := hinc e he
    obtain ⟨-, he₂⟩ := hinc e' he'
    rw [← heq] at he₂
    exact Subtype.ext (hoff _ hw _ _ he₁ he₂)
  · intro w hw
    obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 (hone w hw)
    have hmem : e₀ ∈ {e | (G.graph.source e = w ∨ G.graph.target e = w) ∧ e ∉ C} := by
      rw [he₀]; exact Set.mem_singleton _
    obtain ⟨hinc, hnC⟩ := hmem
    -- `e₀` is on no cycle
    have hoffc : ∀ C', IsCycle G.graph C' → P C' → e₀ ∉ C' := by
      intro C' hC' _ he₀C'
      have hwC' : w ∈ cycleNodes G.graph C' := by
        rcases hinc with h | h
        exacts [⟨e₀, he₀C', Or.inl h⟩, ⟨e₀, he₀C', Or.inr h⟩]
      rw [hnd C' C hC' hC ⟨w, hwC', hw⟩] at he₀C'
      exact hnC he₀C'
    refine ⟨⟨e₀, hoffc⟩, ?_, ?_⟩
    · rcases hinc with h | h
      · exact Or.inl ((hcls _).2 (h ▸ hw))
      · exact Or.inr ((hcls _).2 (h ▸ hw))
    · split_ifs with h
      · rcases hinc with h' | h'
        · exact h'
        · exact absurd (((hcls _).2 h).trans ((hcls _).2 (h' ▸ hw)).symm)
            (hloopT ⟨e₀, hoffc⟩)
      · exact hinc.resolve_left fun h' => h (h' ▸ hw)

end ContractSome


section Abstract

variable {V E X : Type*}

/-- **A cycle of size at least four with one taxon in each block**, in a semidirected network with
the properties of `N⁻` that the description of `Ñ` uses: connected, without loops, its cycles
pairwise without common node, its taxa of degree one and labelled injectively, its other nodes of
degree three, a taxon on each side of each edge on no cycle, its hybrid edges on cycles, a taxon in
the block of each node of each cycle. -/
structure SingletonBlockCycle (G : SemidirectedNetwork V E X) (C : Set E) : Prop where
  conn : G.graph.IsConnected
  loop : ∀ e, G.graph.source e ≠ G.graph.target e
  nd : ∀ C₁ C₂, IsCycle G.graph C₁ → IsCycle G.graph C₂ →
    (cycleNodes G.graph C₁ ∩ cycleNodes G.graph C₂).Nonempty → C₁ = C₂
  leaf_deg : ∀ x, degree G.graph (G.leaf x) = 1
  deg : ∀ u, (¬ ∃ x, G.leaf x = u) → degree G.graph u = 3
  inj : Function.Injective G.leaf
  side : ∀ g, ¬ G.graph.Walks {g}ᶜ (G.graph.source g) (G.graph.target g) → ∀ b,
    (b = G.graph.source g ∨ b = G.graph.target g) → ∃ x, G.graph.Walks {g}ᶜ b (G.leaf x)
  dir : ∀ e, G.IsDirected e → ∃ C', IsCycle G.graph C' ∧ e ∈ C'
  block : ∀ C', IsCycle G.graph C' → ∀ u ∈ cycleNodes G.graph C',
    (nodeBlock G.graph G.leaf C' u).Nonempty
  cycle : IsCycle G.graph C
  four : 4 ≤ C.ncard
  single : ∀ x y, SameBlock G.graph G.leaf C x y → x = y

/-- The edges of `Ñ` before suppression off `C` hanging from the node of `C` of the block of `x`:
reached from it by a walk off `C`. -/
def pendantEdges (G : SemidirectedNetwork V E X) (C : Set E) (x : X) :
    Set {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'} :=
  {g | g.1 ∉ C ∧ (tildeContracted G).graph.Walks {g | g.1 ∉ C} (Quot.mk _ (blockNode G C x))
    ((tildeContracted G).graph.source g)}

/-- **A cycle with a taxon hanging from each node**: nodes `inl x`, the taxon `x`, and `inr x`, a
node of the cycle; edges `inl x`, from `inr x` to `inl x`, and `inr τ`, from `inr (s τ)` to
`inr (t τ)`, hybrid when `D τ`. -/
def cycleModel {X T : Type*} (s t : T → X) (D : T → Prop) :
    SemidirectedNetwork (X ⊕ X) (X ⊕ T) X where
  graph :=
    { source := Sum.elim Sum.inr fun τ => Sum.inr (s τ)
      target := Sum.elim Sum.inl fun τ => Sum.inr (t τ) }
  IsDirected := Sum.elim (fun _ => False) D
  leaf := Sum.inl

namespace SingletonBlockCycle

variable {G : SemidirectedNetwork V E X} {C : Set E} (hG : SingletonBlockCycle G C)
include hG

/-- The network is level-1: cycles with a common edge have a common node. -/
theorem isLevelOne : IsLevelOne G.graph := fun C₁ C₂ h₁ h₂ ⟨f, hf₁, hf₂⟩ =>
  hG.nd C₁ C₂ h₁ h₂ ⟨_, ⟨f, hf₁, Or.inl rfl⟩, ⟨f, hf₂, Or.inl rfl⟩⟩

/-- Two distinct cycles have no common edge. -/
theorem notMem_of_ne {C₁ C₂ : Set E} (h₁ : IsCycle G.graph C₁) (h₂ : IsCycle G.graph C₂)
    (hne : C₁ ≠ C₂) {f : E} (hf : f ∈ C₁) : f ∉ C₂ := fun hf' =>
  hne (hG.nd C₁ C₂ h₁ h₂ ⟨_, ⟨f, hf, Or.inl rfl⟩, ⟨f, hf', Or.inl rfl⟩⟩)

/-- **The other cycles have size two**: a cycle `C'` other than `C` lies in the component of a node
`w` of `C` without the edges of `C`, and the taxa outside the block of `w` are in one block of `C'`;
the blocks of two more nodes of `C'` would hold two taxa of the block of `w`. -/
theorem ncard_le_two {C' : Set E} (hC' : IsCycle G.graph C') (hne : C' ≠ C) :
    C'.ncard ≤ 2 := by
  by_contra h3
  have h1 := hG.isLevelOne
  have hCC' : ∀ f ∈ C, f ∉ C' := fun f hf => hG.notMem_of_ne hG.cycle hC' (Ne.symm hne) hf
  obtain ⟨z₀, hz₀⟩ := hC'.nonempty_cycleNodes
  obtain ⟨w, hw, hwz⟩ := exists_walks_compl_cycleNodes hG.conn hG.cycle z₀
  obtain ⟨u', hu', hu'w⟩ := exists_walks_compl_cycleNodes hG.conn hC' w
  have key : ∀ p, ¬ G.graph.Walks Cᶜ w p → G.graph.Walks C'ᶜ u' p := fun p hp =>
    walks_compl_of_not_walks_compl G.graph hG.conn hG.cycle hC' hCC' hz₀ hwz hw
      hu'w hp
  obtain ⟨a, ha, hau⟩ := hC'.exists_mem_cycleNodes_notMem (Set.toFinite {u'})
    (by rw [Set.ncard_singleton]; omega)
  obtain ⟨b, hb, hbu⟩ := hC'.exists_mem_cycleNodes_notMem (Set.toFinite {u', a})
    (lt_of_le_of_lt ((Set.ncard_insert_le u' {a}).trans (by rw [Set.ncard_singleton])) (by omega))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hau hbu
  obtain ⟨ta, hta⟩ := hG.block C' hC' a ha
  obtain ⟨tb, htb⟩ := hG.block C' hC' b hb
  have hin : ∀ c t, c ∈ cycleNodes G.graph C' → c ≠ u' → t ∈ nodeBlock G.graph G.leaf C' c →
      G.graph.Walks Cᶜ w (G.leaf t) := fun c t hc hcu ht => by
    by_contra hn
    exact hcu (h1.eq_of_walks_compl hC' hc hu' (ht.trans (G.graph.walks_symm (key _ hn))))
  have hab := hG.single ta tb
    ((G.graph.walks_symm (hin a ta ha hau hta)).trans (hin b tb hb hbu.1 htb))
  subst hab
  exact hbu.2 (h1.eq_of_walks_compl hC' hb ha (htb.trans (G.graph.walks_symm hta)))

/-- **A node on no cycle is a taxon**: a node of degree three on no cycle has three edges on no
cycle; the far sides of two of them miss `C` and hold distinct taxa, both in the block of the node
of `C` toward which the node lies. -/
theorem exists_leaf_eq [Finite E] {w : V}
    (hw : ∀ C', IsCycle G.graph C' → w ∉ cycleNodes G.graph C') :
    ∃ x, G.leaf x = w := by
  by_contra hnl
  have hd := hG.deg w hnl
  rw [degree_eq_ncard_incident hG.loop] at hd
  obtain ⟨g₀, g₁, g₂, h01, h02, h12, hI⟩ := Set.ncard_eq_three.1 hd
  have hinc : ∀ g, g ∈ ({g₀, g₁, g₂} : Set E) → (G.graph.source g = w ∨ G.graph.target g = w) :=
    fun g hg => by rw [← hI] at hg; exact hg
  -- the far end of an edge at `w`
  let b : E → V := fun g => if G.graph.source g = w then G.graph.target g else G.graph.source g
  have hb : ∀ g, (G.graph.source g = w ∨ G.graph.target g = w) →
      Joins G.graph g w (b g) ∧ (b g = G.graph.source g ∨ b g = G.graph.target g) := by
    intro g hg
    by_cases hs : G.graph.source g = w
    · have hbg : b g = G.graph.target g := ite_eq_left hs
      rw [hbg]
      exact ⟨Or.inl ⟨hs, rfl⟩, Or.inr rfl⟩
    · have hbg : b g = G.graph.source g := ite_eq_right hs
      rw [hbg]
      exact ⟨Or.inr ⟨rfl, hg.resolve_left hs⟩, Or.inl rfl⟩
  -- the edges at `w` are on no cycle
  have hbr : ∀ g, (G.graph.source g = w ∨ G.graph.target g = w) →
      ¬ G.graph.Walks {g}ᶜ (G.graph.source g) (G.graph.target g) := by
    intro g hg hW
    obtain ⟨C', hC', hgC', -⟩ := exists_isCycle_of_walks
      (show g ∉ ({g}ᶜ : Set E) from fun h => h rfl) (G.graph.walks_symm hW)
    exact hw C' hC' ⟨g, hgC', hg⟩
  have hfar : ∀ g, (G.graph.source g = w ∨ G.graph.target g = w) →
      ¬ G.graph.Walks {g}ᶜ (b g) w := by
    intro g hg hW
    apply hbr g hg
    rcases (hb g hg).1 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]; exact G.graph.walks_symm hW
    · rw [h₁, h₂]; exact hW
  -- a walk from the far end avoiding the edge does not reach `w`
  have hoff : ∀ g, (G.graph.source g = w ∨ G.graph.target g = w) → ∀ z,
      G.graph.Walks {g}ᶜ (b g) z →
        G.graph.Walks {f | ¬ (G.graph.source f = w ∨ G.graph.target f = w)} (b g) z := by
    intro g hg z hz
    refine walks_mono_of_reach hz fun y hy f hf hfy hfw => hfar g hg ?_
    have hyw : y ≠ w := fun h => hfar g hg (h ▸ hy)
    refine hy.tail ⟨f, hf, ?_⟩
    rcases hfy with h | h <;> rcases hfw with h' | h'
    · exact absurd (h.symm.trans h') hyw
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h', h⟩
    · exact absurd (h.symm.trans h') hyw
  -- the far sides of two edges at `w` are disjoint
  have hdisj : ∀ g g', (G.graph.source g = w ∨ G.graph.target g = w) →
      (G.graph.source g' = w ∨ G.graph.target g' = w) → g ≠ g' → ∀ z,
      G.graph.Walks {g}ᶜ (b g) z → ¬ G.graph.Walks {g'}ᶜ (b g') z := by
    intro g g' hg hg' hne z hz hz'
    have h₁ := hoff g hg z hz
    have h₂ := hoff g' hg' z hz'
    have hsub : {f | ¬ (G.graph.source f = w ∨ G.graph.target f = w)} ⊆ ({g}ᶜ : Set E) :=
      fun f hf hfg => hf (by rw [Set.mem_singleton_iff.1 hfg]; exact hg)
    have hw' : G.graph.Walks {g}ᶜ (b g') w := by
      refine Relation.ReflTransGen.single ⟨g', fun h => hne (Set.mem_singleton_iff.1 h).symm, ?_⟩
      rcases (hb g' hg').1 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inr ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁, h₂⟩
    exact hfar g hg ((walks_mono hsub (h₁.trans (G.graph.walks_symm h₂))).trans hw')
  have hwC : w ∉ cycleNodes G.graph C := hw C hG.cycle
  have hgC : ∀ g, (G.graph.source g = w ∨ G.graph.target g = w) → g ∉ C := fun g hg hgC =>
    hwC ⟨g, hgC, hg⟩
  -- a far side without a node of `C` holds a taxon of the block of `w`
  obtain ⟨w₀, hw₀, hw₀w⟩ := exists_walks_compl_cycleNodes hG.conn hG.cycle w
  have htax : ∀ g, (G.graph.source g = w ∨ G.graph.target g = w) →
      (∀ z, G.graph.Walks {g}ᶜ (b g) z → z ∉ cycleNodes G.graph C) →
      ∃ x, G.graph.Walks {g}ᶜ (b g) (G.leaf x) ∧ G.graph.Walks Cᶜ w₀ (G.leaf x) := by
    intro g hg hnC
    obtain ⟨x, hx⟩ := hG.side g (hbr g hg) (b g) (hb g hg).2
    refine ⟨x, hx, hw₀w.trans ((Relation.ReflTransGen.single ⟨g, hgC g hg, (hb g hg).1⟩).trans
      (walks_mono_of_reach hx fun y hy f _ hfy hfC => hnC y hy ⟨f, hfC, hfy⟩))⟩
  have htwo : ∀ g g', (G.graph.source g = w ∨ G.graph.target g = w) →
      (G.graph.source g' = w ∨ G.graph.target g' = w) → g ≠ g' →
      (∀ z, G.graph.Walks {g}ᶜ (b g) z → z ∉ cycleNodes G.graph C) →
      (∀ z, G.graph.Walks {g'}ᶜ (b g') z → z ∉ cycleNodes G.graph C) → False := by
    intro g g' hg hg' hne hn hn'
    obtain ⟨x, hx, hx₀⟩ := htax g hg hn
    obtain ⟨x', hx', hx₀'⟩ := htax g' hg' hn'
    obtain rfl := hG.single x x' ((G.graph.walks_symm hx₀).trans hx₀')
    exact hdisj g g' hg hg' hne _ hx hx'
  -- at most one far side meets `C`
  have hone : ∀ g g', (G.graph.source g = w ∨ G.graph.target g = w) →
      (G.graph.source g' = w ∨ G.graph.target g' = w) → g ≠ g' →
      (∃ z, G.graph.Walks {g}ᶜ (b g) z ∧ z ∈ cycleNodes G.graph C) →
      ∀ z, G.graph.Walks {g'}ᶜ (b g') z → z ∉ cycleNodes G.graph C := by
    rintro g g' hg hg' hne ⟨c, hc, hcC⟩ z hz hzC
    exact hdisj g g' hg hg' hne z (hc.trans (walks_mono (show C ⊆ ({g}ᶜ : Set E) from
      fun f hf hfg => hgC g hg (Set.mem_singleton_iff.1 hfg ▸ hf))
      (walks_cycle_of_mem_cycleNodes G.graph hG.cycle hcC hzC))) hz
  have i0 := hinc g₀ (Or.inl rfl)
  have i1 := hinc g₁ (Or.inr (Or.inl rfl))
  have i2 := hinc g₂ (Or.inr (Or.inr rfl))
  by_cases c0 : ∃ z, G.graph.Walks {g₀}ᶜ (b g₀) z ∧ z ∈ cycleNodes G.graph C
  · exact htwo g₁ g₂ i1 i2 h12 (hone g₀ g₁ i0 i1 h01 c0) (hone g₀ g₂ i0 i2 h02 c0)
  · push Not at c0
    by_cases c1 : ∃ z, G.graph.Walks {g₁}ᶜ (b g₁) z ∧ z ∈ cycleNodes G.graph C
    · exact htwo g₀ g₂ i0 i2 h02 c0 (hone g₁ g₂ i1 i2 h12 c1)
    · push Not at c1
      exact htwo g₀ g₁ i0 i1 h01 c0 c1


/-- A taxon is on no cycle: it has degree one. -/
theorem leaf_notMem [Finite E] (x : X) {C' : Set E} (hC' : IsCycle G.graph C') :
    G.leaf x ∉ cycleNodes G.graph C' := fun h => by
  have h2 := hC'.ncard_incident hG.loop h
  have hd := degree_eq_ncard_incident hG.loop (G.leaf x)
  rw [hG.leaf_deg x] at hd
  have := Set.ncard_le_ncard (s := {e | e ∈ C' ∧ (G.graph.source e = G.leaf x ∨
    G.graph.target e = G.leaf x)}) (t := {e | G.graph.source e = G.leaf x ∨
    G.graph.target e = G.leaf x}) (fun e he => he.2) (Set.toFinite _)
  omega

/-- The cycles of size at most three are those other than `C`. -/
theorem small_iff {C' : Set E} (hC' : IsCycle G.graph C') : C'.ncard ≤ 3 ↔ C' ≠ C := by
  refine ⟨fun h hc => ?_, fun h => (hG.ncard_le_two hC' h).trans (by norm_num)⟩
  subst hc
  have := hG.four
  omega

/-- A node of `C` is on no other cycle. -/
theorem notMem_small {u : V} (hu : u ∈ cycleNodes G.graph C) (C' : Set E)
    (hC' : IsCycle G.graph C') (h3 : C'.ncard ≤ 3) : u ∉ cycleNodes G.graph C' := fun hu' =>
  (hG.small_iff hC').1 h3 (hG.nd C' C hC' hG.cycle ⟨u, hu', hu⟩)

/-- **The nodes identified in `Ñ`** are those of a cycle other than `C`. -/
theorem mk_eq_iff {a b : V} :
    (Quot.mk _ a : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) = Quot.mk _ b ↔
      a = b ∨ ∃ C', IsCycle G.graph C' ∧ C' ≠ C ∧ a ∈ cycleNodes G.graph C' ∧
        b ∈ cycleNodes G.graph C' := by
  rw [contract_mk_eq_iff_of_cycles hG.nd]
  constructor
  · rintro (h | ⟨C', hC', h3, ha, hb⟩)
    exacts [Or.inl h, Or.inr ⟨C', hC', (hG.small_iff hC').1 h3, ha, hb⟩]
  · rintro (h | ⟨C', hC', hne, ha, hb⟩)
    exacts [Or.inl h, Or.inr ⟨C', hC', (hG.small_iff hC').2 hne, ha, hb⟩]

/-- The class of a node of `C` is that node alone. -/
theorem mk_eq_mk_iff_of_mem {u a : V} (hu : u ∈ cycleNodes G.graph C) :
    (Quot.mk _ a : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) = Quot.mk _ u ↔ a = u := by
  rw [hG.mk_eq_iff]
  constructor
  · rintro (h | ⟨C', hC', hne, -, hu'⟩)
    · exact h
    · exact absurd (hG.nd C' C hC' hG.cycle ⟨u, hu', hu⟩) hne
  · exact Or.inl

/-- The degree of a taxon in `Ñ` before suppression is one. -/
theorem degree_leaf [Finite E] (x : X) :
    degree (tildeContracted G).graph ((tildeContracted G).leaf x) = 1 :=
  (contract_degree_of_notMem_of_cycles hG.nd fun _ hC' _ => hG.leaf_notMem x hC').trans
    (hG.leaf_deg x)

/-- The degree of a node of `C` in `Ñ` before suppression is three. -/
theorem degree_cycle [Finite E] {u : V} (hu : u ∈ cycleNodes G.graph C) :
    degree (tildeContracted G).graph (Quot.mk _ u) = 3 :=
  (contract_degree_of_notMem_of_cycles hG.nd (hG.notMem_small hu)).trans
    (hG.deg u fun ⟨x, hx⟩ => hG.leaf_notMem x hG.cycle (hx ▸ hu))

/-- The degree of a contracted cycle other than `C` is two. -/
theorem degree_small [Finite E] {C' : Set E} (hC' : IsCycle G.graph C') (hne : C' ≠ C) {a : V}
    (ha : a ∈ cycleNodes G.graph C') : degree (tildeContracted G).graph (Quot.mk _ a) = 2 := by
  have h := contract_degree_of_mem_of_cycles (P := fun C => C.ncard ≤ 3) hG.nd hG.loop hC'
    ((hG.small_iff hC').2 hne)
    (fun w hw => hG.deg w fun ⟨x, hx⟩ => hG.leaf_notMem x hC' (hx ▸ hw)) ha
  have h2 := hC'.ncard_incident hG.loop ha
  have := Set.ncard_le_ncard (s := {e | e ∈ C' ∧ (G.graph.source e = a ∨
    G.graph.target e = a)}) (t := C') (fun e he => he.1) (Set.toFinite C')
  have := hG.ncard_le_two hC' hne
  change degree (contractCycles G fun C => C.ncard ≤ 3).graph (Quot.mk _ a) = 2
  omega

/-- **The kept nodes of `Ñ`**: the taxa and the nodes of `C`. -/
theorem isBranch_iff [Finite E] (q : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) :
    IsBranch (tildeContracted G) ∅ q ↔
      (∃ x, q = (tildeContracted G).leaf x) ∨ ∃ u ∈ cycleNodes G.graph C, q = Quot.mk _ u := by
  induction q using Quot.ind with
  | mk w =>
  constructor
  · rintro (hd | ⟨x, hx⟩ | h)
    · by_cases hl : ∃ x, G.leaf x = w
      · obtain ⟨x, rfl⟩ := hl
        exact Or.inl ⟨x, rfl⟩
      · by_cases hc : ∃ C', IsCycle G.graph C' ∧ w ∈ cycleNodes G.graph C'
        · obtain ⟨C', hC', hw⟩ := hc
          by_cases hCC : C' = C
          · subst hCC
            exact Or.inr ⟨w, hw, rfl⟩
          · exact absurd (hG.degree_small hC' hCC hw) hd
        · push Not at hc
          exact absurd (hG.exists_leaf_eq hc) hl
    · exact Or.inl ⟨x, hx.symm⟩
    · exact absurd h (Set.notMem_empty _)
  · rintro (⟨x, hx⟩ | ⟨u, hu, hq⟩)
    · exact Or.inr (Or.inl ⟨x, hx.symm⟩)
    · rw [hq]
      exact Or.inl (by rw [hG.degree_cycle hu]; norm_num)

/-- A walk of `Ñ` before suppression avoiding the edges of `C` is a walk of the network avoiding
`C`. -/
theorem walks_lift {a b : V}
    (h : (tildeContracted G).graph.Walks {g | g.1 ∉ C} (Quot.mk _ a) (Quot.mk _ b)) :
    G.graph.Walks Cᶜ a b := by
  refine walks_mono ?_ (walks_of_contract_walks_of_cycles h)
  rintro e (⟨g, hg, rfl⟩ | ⟨C', hC', h3, heC'⟩)
  · exact hg
  · exact hG.notMem_of_ne hC' hG.cycle ((hG.small_iff hC').1 h3) heC'

/-- A walk of the network avoiding `C` is a walk of `Ñ` before suppression avoiding `C`. -/
theorem walks_push {a b : V} (h : G.graph.Walks Cᶜ a b) :
    (tildeContracted G).graph.Walks {g | g.1 ∉ C} (Quot.mk _ a) (Quot.mk _ b) :=
  contract_walks_of_walks_of_cycles h fun _ hf _ hC' hfC' =>
    (hG.small_iff hC').2 fun h => hf (h ▸ hfC')

/-- `blockNode C x` is a node of `C`, and `x` is in its block. -/
theorem blockNode_mem_and (x : X) :
    blockNode G C x ∈ cycleNodes G.graph C ∧ x ∈ nodeBlock G.graph G.leaf C (blockNode G C x) := by
  obtain ⟨u, hu, hux⟩ := exists_walks_compl_cycleNodes hG.conn hG.cycle (G.leaf x)
  exact Classical.epsilon_spec (p := fun u => u ∈ cycleNodes G.graph C ∧
    x ∈ nodeBlock G.graph G.leaf C u) ⟨u, hu, hux⟩

/-- The block of `x` is that of `blockNode C x` only. -/
theorem eq_blockNode_of_mem {u : V} (hu : u ∈ cycleNodes G.graph C) {x : X}
    (hx : x ∈ nodeBlock G.graph G.leaf C u) : u = blockNode G C x :=
  hG.isLevelOne.eq_of_walks_compl hG.cycle hu (hG.blockNode_mem_and x).1
    (hx.trans (G.graph.walks_symm (hG.blockNode_mem_and x).2))

/-- The taxa are one in each block: `blockNode` is injective. -/
theorem blockNode_injective : Function.Injective (blockNode G C) := fun x y h =>
  hG.single x y ((G.graph.walks_symm (hG.blockNode_mem_and x).2).trans
    (h ▸ (hG.blockNode_mem_and y).2))

/-- Every node of `C` is the node of the block of a taxon. -/
theorem exists_blockNode_eq_of_mem {u : V} (hu : u ∈ cycleNodes G.graph C) :
    ∃ x, blockNode G C x = u := by
  obtain ⟨x, hx⟩ := hG.block C hG.cycle u hu
  exact ⟨x, (hG.eq_blockNode_of_mem hu hx).symm⟩

/-- At a node of `C`, the edge off `C` is unique. -/
theorem eq_of_notMem_of_mem_cycleNodes [Finite E] {u : V} (hu : u ∈ cycleNodes G.graph C)
    {e e' : E} (he : G.graph.source e = u ∨ G.graph.target e = u) (heC : e ∉ C)
    (he' : G.graph.source e' = u ∨ G.graph.target e' = u) (he'C : e' ∉ C) : e = e' := by
  have hnl : ¬ ∃ x, G.leaf x = u := fun ⟨x, hx⟩ => hG.leaf_notMem x hG.cycle (hx ▸ hu)
  have h2 := hG.cycle.ncard_incident hG.loop hu
  have hd := degree_eq_ncard_incident hG.loop u
  rw [hG.deg u hnl] at hd
  by_contra hne
  obtain ⟨c₁, c₂, hc, hcs⟩ := Set.ncard_eq_two.1 h2
  have hc₁ : c₁ ∈ {f | f ∈ C ∧ (G.graph.source f = u ∨ G.graph.target f = u)} := by
    rw [hcs]; exact Or.inl rfl
  have hc₂ : c₂ ∈ {f | f ∈ C ∧ (G.graph.source f = u ∨ G.graph.target f = u)} := by
    rw [hcs]; exact Or.inr rfl
  have h4 : ({e, e', c₁, c₂} : Set E).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hc]
    · rintro (h | h)
      · exact he'C (h ▸ hc₁.1)
      · exact he'C (h ▸ hc₂.1)
    · rintro (h | h | h)
      · exact hne h
      · exact heC (h ▸ hc₁.1)
      · exact heC (h ▸ hc₂.1)
  have hsub : ({e, e', c₁, c₂} : Set E) ⊆ {f | G.graph.source f = u ∨ G.graph.target f = u} := by
    rintro f (rfl | rfl | rfl | rfl)
    exacts [he, he', hc₁.2, hc₂.2]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- An edge of `C` is on no cycle of size at most three: it is an edge of `Ñ` before
suppression. -/
theorem notMem_small_of_mem {e : E} (he : e ∈ C) (C' : Set E) (hC' : IsCycle G.graph C')
    (h3 : C'.ncard ≤ 3) : e ∉ C' := fun heC' =>
  (hG.small_iff hC').1 h3 (hG.isLevelOne C' C hC' hG.cycle ⟨e, heC', he⟩)

/-- **The chain of the taxon `x`**: in `Ñ` before suppression, the edges off `C` hanging from the
node of `C` of the block of `x` form a chain from that node to `x`. Its inner nodes are contracted
cycles other than `C`, of degree two: a walk from the node of `C` to `x` off `C` gives a path, and
the edges off `C` at its nodes are its edges, since the node of `C` has one edge off `C`, the taxon
one edge, and the inner nodes two. -/
theorem exists_isChainOf_pendantEdges [Finite E] (x : X) :
    ∃ (n : ℕ) (p : Fin (n + 1) → Quot (ContractRel G.graph fun C => C.ncard ≤ 3))
      (q : Fin n → {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'}),
      IsChainOf (tildeContracted G) ∅ n p q ∧ Set.range q = pendantEdges G C x ∧
        p 0 = Quot.mk _ (blockNode G C x) ∧ p (Fin.last n) = (tildeContracted G).leaf x := by
  set K := tildeContracted G with hK
  set F : Set {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'} := {g | g.1 ∉ C} with hF
  obtain ⟨hu, hux⟩ := hG.blockNode_mem_and x
  set u := blockNode G C x with hu_def
  have hw : K.graph.Walks F (Quot.mk _ u) (K.leaf x) := hG.walks_push hux
  obtain ⟨n, p, q, hP, hp0, hpn⟩ := exists_isPathOf_of_walks hw
  have hloopK : ∀ g, K.graph.source g ≠ K.graph.target g :=
    contract_source_ne_target_of_cycles hG.nd hG.loop
  have hpre : ∀ i, K.graph.Walks F (Quot.mk _ u) (p i) := fun i => by
    rw [← hp0]
    refine walks_mono ?_ (hP.walks_of_le (Fin.zero_le i))
    rintro _ ⟨l, -, -, rfl⟩
    exact hP.mem l
  -- the kept nodes reached from `u` off `C` are `u` and `x`
  have hreach : ∀ z, K.graph.Walks F (Quot.mk _ u) z → IsBranch K ∅ z →
      z = Quot.mk _ u ∨ z = K.leaf x := by
    intro z hz hb
    rcases (hG.isBranch_iff z).1 hb with ⟨y, rfl⟩ | ⟨u', hu', rfl⟩
    · right
      obtain rfl := hG.single x y ((G.graph.walks_symm hux).trans (hG.walks_lift hz))
      rfl
    · left
      rw [hG.isLevelOne.eq_of_walks_compl hG.cycle hu hu' (hG.walks_lift hz)]
  have hbu : IsBranch K ∅ (Quot.mk _ u) := (hG.isBranch_iff _).2 (Or.inr ⟨u, hu, rfl⟩)
  have hbx : IsBranch K ∅ (K.leaf x) := Or.inr (Or.inl ⟨x, rfl⟩)
  have hne : (Quot.mk _ u : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) ≠ K.leaf x :=
    fun h => by
      rcases hG.mk_eq_iff.1 h with h | ⟨C', hC', -, -, hx⟩
      · exact hG.leaf_notMem x hG.cycle (h ▸ hu)
      · exact hG.leaf_notMem x hC' hx
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (hp0.symm.trans hpn) hne
    · exact h
  have hchain : IsChainOf K ∅ n p q :=
    { pos := hn
      joins := fun i => hP.link i
      inner := fun i hi0 hil hb => by
        rcases hreach (p i) (hpre i) hb with h | h
        · exact hi0 (hP.injective (h.trans hp0.symm))
        · exact hil (hP.injective (h.trans hpn.symm))
      ends := ⟨hp0 ▸ hbu, hpn ▸ hbx⟩
      injective_edge := hP.injective_edge }
  -- every edge off `C` at a node of the path is an edge of the path
  have hat : ∀ g ∈ F, ∀ i, (K.graph.source g = p i ∨ K.graph.target g = p i) →
      g ∈ Set.range q := by
    intro g hg i hgi
    by_cases hi0 : i = 0
    · subst hi0
      have hq0 : K.graph.source (q ⟨0, hn⟩) = p 0 ∨ K.graph.target (q ⟨0, hn⟩) = p 0 := by
        rcases hP.link ⟨0, hn⟩ with ⟨h, -⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
      rw [hp0] at hgi hq0
      have hv : ∀ f : {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'},
          (K.graph.source f = Quot.mk _ u ∨ K.graph.target f = Quot.mk _ u) →
            G.graph.source f.1 = u ∨ G.graph.target f.1 = u := fun f hf =>
        hf.imp (hG.mk_eq_mk_iff_of_mem hu).1 (hG.mk_eq_mk_iff_of_mem hu).1
      exact ⟨⟨0, hn⟩, Subtype.ext (hG.eq_of_notMem_of_mem_cycleNodes hu (hv _ hq0) (hP.mem _)
        (hv _ hgi) hg)⟩
    have hi0' : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
    by_cases hil : i = Fin.last n
    · subst hil
      have hs : (⟨n - 1, by omega⟩ : Fin n).succ = Fin.last n := Fin.ext (by simp; omega)
      have hql : K.graph.source (q ⟨n - 1, by omega⟩) = p (Fin.last n) ∨
          K.graph.target (q ⟨n - 1, by omega⟩) = p (Fin.last n) := by
        rcases hP.link ⟨n - 1, by omega⟩ with ⟨-, h⟩ | ⟨h, -⟩
        · exact Or.inr (h.trans (by rw [hs]))
        · exact Or.inl (h.trans (by rw [hs]))
      rw [hpn] at hgi hql
      exact ⟨_, eq_of_incident_of_degree_eq_one hloopK (hG.degree_leaf x) hql hgi⟩
    · have hil' : (i : ℕ) ≠ n := fun h => hil (Fin.ext (by simp [h]))
      have hd : degree K.graph (p i) = 2 := by
        by_contra h
        exact hchain.inner i hi0 hil (Or.inl h)
      have hi := i.isLt
      have hj : (⟨i - 1, by omega⟩ : Fin n).succ = i := Fin.ext (by simp; omega)
      have hl : (⟨i, by omega⟩ : Fin n).castSucc = i := rfl
      have hqj : K.graph.source (q ⟨i - 1, by omega⟩) = p i ∨
          K.graph.target (q ⟨i - 1, by omega⟩) = p i := by
        rcases hP.link ⟨i - 1, by omega⟩ with ⟨-, h⟩ | ⟨h, -⟩
        · exact Or.inr (h.trans (by rw [hj]))
        · exact Or.inl (h.trans (by rw [hj]))
      have hql : K.graph.source (q ⟨i, by omega⟩) = p i ∨
          K.graph.target (q ⟨i, by omega⟩) = p i := by
        rcases hP.link ⟨i, by omega⟩ with ⟨h, -⟩ | ⟨-, h⟩
        · exact Or.inl (h.trans (by rw [hl]))
        · exact Or.inr (h.trans (by rw [hl]))
      have hjl : q ⟨i - 1, by omega⟩ ≠ q ⟨i, by omega⟩ := fun h => by
        have := congrArg Fin.val (hP.injective_edge h)
        simp only at this
        omega
      rcases eq_or_eq_of_degree_eq_two hd hqj hql hgi hjl with h | h
      · exact ⟨_, h.symm⟩
      · exact ⟨_, h.symm⟩
  have hends : ∀ g ∈ Set.range q, K.graph.source g ∈ Set.range p ∧
      K.graph.target g ∈ Set.range p := by
    rintro _ ⟨j, rfl⟩
    rcases hP.link j with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨⟨_, h₁.symm⟩, ⟨_, h₂.symm⟩⟩
    · exact ⟨⟨_, h₁.symm⟩, ⟨_, h₂.symm⟩⟩
  have hcross : ∀ g ∈ F, ¬ K.graph.Crosses g (Set.range p) := by
    intro g hg hcr
    rcases hcr with ⟨⟨i, hi⟩, ht⟩ | ⟨⟨i, hi⟩, hs⟩
    · exact ht (hends g (hat g hg i (Or.inl hi.symm))).2
    · exact hs (hends g (hat g hg i (Or.inr hi.symm))).1
  have hQ : Set.range q = pendantEdges G C x := by
    ext g
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨hP.mem j, ?_⟩
      rcases hP.link j with ⟨h₁, -⟩ | ⟨h₁, -⟩
      · rw [h₁]; exact hpre _
      · rw [h₁]; exact hpre _
    · rintro ⟨hg, hgw⟩
      obtain ⟨i, hi⟩ := (K.graph.mem_iff_mem_of_walks hcross hgw).1 ⟨0, hp0⟩
      exact hat g hg i (Or.inl hi.symm)
  exact ⟨n, p, q, hchain, hQ, hp0, hpn⟩

/-- An edge off `C` hangs from the node of `C` of the block of some taxon. -/
theorem exists_mem_pendantEdges
    (g : {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'}) (hg : g.1 ∉ C) :
    ∃ x, g ∈ pendantEdges G C x := by
  obtain ⟨u, hu, hug⟩ := exists_walks_compl_cycleNodes hG.conn hG.cycle (G.graph.source g.1)
  obtain ⟨x, rfl⟩ := hG.exists_blockNode_eq_of_mem hu
  exact ⟨x, hg, hG.walks_push hug⟩

/-- An edge off `C` hangs from one node of `C` only. -/
theorem eq_of_mem_pendantEdges
    {g : {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'}} {x y : X}
    (hx : g ∈ pendantEdges G C x) (hy : g ∈ pendantEdges G C y) : x = y :=
  hG.blockNode_injective (hG.isLevelOne.eq_of_walks_compl hG.cycle (hG.blockNode_mem_and x).1
    (hG.blockNode_mem_and y).1
    (hG.walks_lift (hx.2.trans ((tildeContracted G).graph.walks_symm hy.2))))

/-- **An edge of `C` is a chain** of `Ñ` before suppression: its ends are nodes of `C`, which are
kept. -/
theorem isChainOf_cycle [Finite E] {e : E} (he : e ∈ C) :
    IsChainOf (tildeContracted G) ∅ 1
      ![Quot.mk _ (G.graph.source e), Quot.mk _ (G.graph.target e)]
      ![⟨e, hG.notMem_small_of_mem he⟩] where
  pos := one_pos
  joins i := by
    fin_cases i
    exact Or.inl ⟨rfl, rfl⟩
  inner i hi0 hil := by
    fin_cases i
    · exact absurd rfl hi0
    · exact absurd rfl hil
  ends := ⟨(hG.isBranch_iff _).2 (Or.inr ⟨_, ⟨e, he, Or.inl rfl⟩, rfl⟩),
    (hG.isBranch_iff _).2 (Or.inr ⟨_, ⟨e, he, Or.inr rfl⟩, rfl⟩)⟩
  injective_edge i j _ := Subsingleton.elim i j


/-- **The network `Ñ` of a cycle with one taxon in each block** is the cycle with a taxon hanging
from each node (`cycleModel`), given the edges of `C` as `T` (through `β`), each joining the nodes
of the blocks of `s τ` and `t τ`, hybrid exactly when `D τ`, and then entering the node of `t τ`.
The isomorphism comes from `exists_sdIso_suppressExcept`: the kept nodes are the taxa and the nodes
of `C`; the chains are the edges of `C` and, for each taxon, the edges hanging from the node of its
block. -/
theorem nonempty_sdIso_cycleModel [Finite E] {T : Type*} (s t : T → X) (D : T → Prop)
    (β : T ≃ C) (hj : ∀ τ, Joins G.graph (β τ).1 (blockNode G C (s τ)) (blockNode G C (t τ)))
    (hD : ∀ τ, D τ ↔ 5 ≤ C.ncard ∧ G.IsDirected (β τ).1)
    (hDt : ∀ τ, D τ → G.graph.target (β τ).1 = blockNode G C (t τ)) :
    Nonempty (SDIso (tildeNetwork G) (cycleModel s t D)) := by
  set K := tildeContracted G with hK
  -- the kept nodes: the taxa and the nodes of `C`
  let ι : X ⊕ X → {q // IsBranch K ∅ q} := Sum.elim
    (fun x => ⟨K.leaf x, Or.inr (Or.inl ⟨x, rfl⟩)⟩)
    (fun x => ⟨Quot.mk _ (blockNode G C x),
      (hG.isBranch_iff _).2 (Or.inr ⟨_, (hG.blockNode_mem_and x).1, rfl⟩)⟩)
  have hι : Function.Bijective ι := by
    constructor
    · have hlb : ∀ x y, K.leaf x ≠ Quot.mk _ (blockNode G C y) := fun x y h => by
        rcases hG.mk_eq_iff.1 h with h | ⟨C', hC', -, hx, -⟩
        · exact hG.leaf_notMem x hG.cycle (h ▸ (hG.blockNode_mem_and y).1)
        · exact hG.leaf_notMem x hC' hx
      rintro (x | x) (y | y) h <;> have h' := congrArg Subtype.val h
      · change (Quot.mk _ (G.leaf x) : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) =
          Quot.mk _ (G.leaf y) at h'
        rcases hG.mk_eq_iff.1 h' with h | ⟨C', hC', -, hx, -⟩
        · rw [hG.inj h]
        · exact absurd hx (hG.leaf_notMem x hC')
      · exact absurd h' (hlb x y)
      · exact absurd h'.symm (hlb y x)
      · change (Quot.mk _ (blockNode G C x) : Quot (ContractRel G.graph fun C => C.ncard ≤ 3)) =
          Quot.mk _ (blockNode G C y) at h'
        rw [hG.blockNode_injective ((hG.mk_eq_mk_iff_of_mem (hG.blockNode_mem_and y).1).1 h')]
    · rintro ⟨q, hq⟩
      rcases (hG.isBranch_iff q).1 hq with ⟨x, rfl⟩ | ⟨u, hu, rfl⟩
      · exact ⟨Sum.inl x, rfl⟩
      · obtain ⟨x, rfl⟩ := hG.exists_blockNode_eq_of_mem hu
        exact ⟨Sum.inr x, rfl⟩
  set φ := (Equiv.ofBijective ι hι).symm with hφ
  have hφs : ∀ y, φ.symm y = ι y := fun y => rfl
  -- the chains: for a taxon, the edges hanging from the node of its block; for an edge of `C`,
  -- itself
  let chainOf : X ⊕ T → Set {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'} :=
    Sum.elim (pendantEdges G C) fun τ => {⟨(β τ).1, hG.notMem_small_of_mem (β τ).2⟩}
  have hpend := fun x => hG.exists_isChainOf_pendantEdges x
  have hchain : ∀ f, IsChain K ∅ (chainOf f) := by
    rintro (x | τ)
    · obtain ⟨n, p, q, hc, hq, -, -⟩ := hpend x
      exact ⟨n, p, q, hc, hq⟩
    · exact ⟨1, _, _, hG.isChainOf_cycle (β τ).2, by simp [chainOf]⟩
  have hmem : ∀ (g : {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'}), g.1 ∉ C →
      ∃ x, g ∈ pendantEdges G C x := fun g hg => hG.exists_mem_pendantEdges g hg
  let ψ : {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'} → X ⊕ T := fun g =>
    if h : g.1 ∈ C then Sum.inr (β.symm ⟨g.1, h⟩) else Sum.inl (Classical.choose (hmem g h))
  have hψ : ∀ g, g ∈ chainOf (ψ g) := by
    intro g
    by_cases h : g.1 ∈ C
    · simp only [ψ, h, ↓reduceDIte, chainOf, Sum.elim_inr, Equiv.apply_symm_apply,
        Set.mem_singleton_iff]
    · simp only [ψ, h, ↓reduceDIte, chainOf, Sum.elim_inl]
      exact Classical.choose_spec (hmem g h)
  have hψ' : ∀ f, ∀ g ∈ chainOf f, ψ g = f := by
    rintro (x | τ) g hg
    · have hgC : g.1 ∉ C := hg.1
      simp only [ψ, hgC, ↓reduceDIte, Sum.inl.injEq]
      exact hG.eq_of_mem_pendantEdges (Classical.choose_spec (hmem g hgC)) hg
    · have hg' : g = ⟨(β τ).1, hG.notMem_small_of_mem (β τ).2⟩ := hg
      subst hg'
      simp only [ψ, (β τ).2, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
  have hloop : ∀ τ, blockNode G C (s τ) ≠ blockNode G C (t τ) := fun τ h => by
    rcases hj τ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hG.loop _ (h₁.trans (h.trans h₂.symm))
    · exact hG.loop _ (h₁.trans (h.symm.trans h₂.symm))
  have hends : ∀ f, chainEnds K ∅ (chainOf f) = {(φ.symm ((cycleModel s t D).graph.source f)).1,
      (φ.symm ((cycleModel s t D).graph.target f)).1} := by
    rintro (x | τ)
    · obtain ⟨n, p, q, hc, hq, hp0, hpn⟩ := hpend x
      show chainEnds K ∅ (pendantEdges G C x) = _
      rw [← hq, hc.chainEnds_eq, hp0, hpn]
      rfl
    · show chainEnds K ∅ {⟨(β τ).1, hG.notMem_small_of_mem (β τ).2⟩} = _
      have h := (hG.isChainOf_cycle (β τ).2).chainEnds_eq
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty] at h
      rw [h]
      change ({Quot.mk _ (G.graph.source (β τ).1), Quot.mk _ (G.graph.target (β τ).1)} :
        Set (Quot (ContractRel G.graph fun C => C.ncard ≤ 3))) =
          {Quot.mk _ (blockNode G C (s τ)), Quot.mk _ (blockNode G C (t τ))}
      rcases hj τ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
      · rw [h₁, h₂, Set.pair_comm]
  have hne : ∀ f, (cycleModel s t D).graph.source f ≠ (cycleModel s t D).graph.target f := by
    rintro (x | τ) h
    · exact Sum.inr_ne_inl h
    · exact hloop τ (congrArg (blockNode G C) (Sum.inr.inj h))
  -- the hybrid edges of `Ñ` before suppression are the hybrid edges of `C` when it has size at
  -- least five
  have hKdir : ∀ g : {e // ∀ C', IsCycle G.graph C' → C'.ncard ≤ 3 → e ∉ C'}, K.IsDirected g →
      g.1 ∈ C ∧ 5 ≤ C.ncard ∧ G.IsDirected g.1 := by
    rintro g ⟨hd, h4⟩
    obtain ⟨C', hC', hgC'⟩ := hG.dir g.1 hd
    by_cases hCC : C' = C
    · subst hCC
      refine ⟨hgC', ?_, hd⟩
      have := hG.four
      by_contra h5
      exact h4 ⟨C', hC', by omega, hgC'⟩
    · exact absurd hgC' (g.2 C' hC' ((hG.small_iff hC').2 hCC))
  have hdir : ∀ f, (cycleModel s t D).IsDirected f ↔ ∃ g ∈ chainOf f, K.IsDirected g := by
    rintro (x | τ)
    · simp only [cycleModel, Sum.elim_inl, false_iff, not_exists, not_and]
      intro g hg hd
      exact hg.1 (hKdir g hd).1
    · show D τ ↔ ∃ g ∈ ({⟨(β τ).1, hG.notMem_small_of_mem (β τ).2⟩} : Set _), K.IsDirected g
      simp only [Set.mem_singleton_iff, exists_eq_left]
      rw [hD τ]
      constructor
      · rintro ⟨h5, hd⟩
        refine ⟨hd, ?_⟩
        rintro ⟨C', hC', h4, hC'τ⟩
        have := hG.isLevelOne C' C hC' hG.cycle ⟨_, hC'τ, (β τ).2⟩
        subst this
        omega
      · intro h
        exact (hKdir _ h).2
  have hdirt : ∀ f, ∀ g ∈ chainOf f, K.IsDirected g →
      K.graph.target g = (φ.symm ((cycleModel s t D).graph.target f)).1 := by
    rintro (x | τ) g hg hd
    · exact absurd (hKdir g hd).1 hg.1
    · have hg' : g = ⟨(β τ).1, hG.notMem_small_of_mem (β τ).2⟩ := hg
      subst hg'
      have hDτ : D τ := (hD τ).2 (hKdir _ hd).2
      change Quot.mk _ (G.graph.target (β τ).1) = Quot.mk _ (blockNode G C (t τ))
      rw [hDt τ hDτ]
  have hleaf : ∀ x, (cycleModel s t D).leaf x = φ ⟨K.leaf x, Or.inr (Or.inl ⟨x, rfl⟩)⟩ := by
    intro x
    show Sum.inl x = (Equiv.ofBijective ι hι).symm (ι (Sum.inl x))
    rw [Equiv.ofBijective_symm_apply_apply]
  obtain ⟨ι', -⟩ := exists_sdIso_suppressExcept φ chainOf hchain ψ hψ hψ' hends hne hdir hdirt hleaf
  exact ⟨ι'⟩


/-- The size of `C` is the number of taxa: one taxon in the block of each node. -/
theorem ncard_eq_card : C.ncard = Nat.card X := by
  rw [← ncard_cycleNodes hG.cycle, ← Set.ncard_range_of_injective hG.blockNode_injective]
  congr 1
  ext u
  constructor
  · intro hu
    exact hG.exists_blockNode_eq_of_mem hu
  · rintro ⟨x, rfl⟩
    exact (hG.blockNode_mem_and x).1

/-- Two edges of `C` joining the same two nodes are equal: with another such edge, an edge of `C`
would be on a cycle of size two. -/
theorem eq_of_joins_of_mem [Finite E] {e e' : E} (he : e ∈ C) (he' : e' ∈ C) {a b : V}
    (hj : Joins G.graph e a b) (hj' : Joins G.graph e' a b) : e = e' := by
  by_contra hne
  have hw : G.graph.Walks {e'} (G.graph.target e) (G.graph.source e) := by
    refine .single ⟨e', rfl, ?_⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hj' with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
    · exact Or.inr ⟨k₁.trans h₁.symm, k₂.trans h₂.symm⟩
    · exact Or.inl ⟨k₁.trans h₂.symm, k₂.trans h₁.symm⟩
    · exact Or.inl ⟨k₁.trans h₂.symm, k₂.trans h₁.symm⟩
    · exact Or.inr ⟨k₁.trans h₁.symm, k₂.trans h₂.symm⟩
  obtain ⟨C₀, hC₀, heC₀, hsub⟩ := exists_isCycle_of_walks (F := {e'})
    (fun h => hne (Set.mem_singleton_iff.1 h)) hw
  have := hG.isLevelOne C₀ C hC₀ hG.cycle ⟨e, heC₀, he⟩
  subst this
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  have := Set.ncard_insert_le e {e'}
  rw [Set.ncard_singleton] at this
  have := hG.four
  omega

end SingletonBlockCycle

end Abstract

/-! ### The network `N⁻` -/

section Unrooted

variable {V E X : Type*} {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
  {hX : Nontrivial X}

/-- **Each side of an edge of `N⁻` on no cycle holds a taxon.** The side of the target holds the
taxa below the arc in `N`. If the side of the source held none, the arc would dominate every taxon,
so its child would be a stable ancestor of all taxa below `LSA(X)`, which is impossible. -/
theorem unrooted_exists_leaf_side (g : SemidirectedArc hN.1 hN.2 hX)
    (hg : ¬ (unrooted N hN hX).graph.Walks {g}ᶜ ((unrooted N hN hX).graph.source g)
      ((unrooted N hN hX).graph.target g)) {b : SemidirectedVertex hN.1 hX}
    (hb : b = (unrooted N hN hX).graph.source g ∨ b = (unrooted N hN hX).graph.target g) :
    ∃ x, (unrooted N hN hX).graph.Walks {g}ᶜ b ((unrooted N hN hX).leaf x) := by
  set G := unrooted N hN hX
  have hsep := unrooted_separates hN g hg
  rcases hb with rfl | rfl
  · by_contra hno
    push Not at hno
    have hall : ∀ x, G.graph.Walks {g}ᶜ (G.graph.target g) (G.leaf x) := fun x =>
      (walks_compl_or_of_isConnected (unrooted_isConnected hN hX) g _).resolve_left (hno x)
    have : Nonempty X := hX.to_nonempty
    -- the child of the arc is a stable ancestor of all taxa
    have hst : N.IsStableAncestor Set.univ (N.graph.target g.1.1) := by
      intro x _ hpath
      apply hsep.1 x (hall x)
      obtain ⟨-, -, hp⟩ := hpath
      refine Relation.ReflTransGen.mono (fun a b h => ?_) _ _ hp
      obtain ⟨⟨f, hfs, hft⟩, -, hbt⟩ := h
      refine ⟨f, ?_, hfs, hft⟩
      rintro rfl
      exact hbt hft.symm
    exact hN.1.acyclic _ (Relation.TransGen.head' ⟨g.1.1, rfl, rfl⟩
      (((lsa_spec hN.1 Set.univ Set.univ_nonempty).2 _ hst).trans g.1.2.1))
  · obtain ⟨x, hx⟩ := exists_reaches_leaf hN.1 (N.graph.target g.1.1)
    exact ⟨x, by_contra fun h => hsep.2 x h hx⟩

/-- `N⁻` of a binary level-1 network, with a cycle of size at least four whose blocks are single
taxa, has the properties of `SingletonBlockCycle`. -/
theorem singletonBlockCycle_unrooted [Finite E] (h1 : IsLevelOne N.graph) {C : Set _}
    (hC : C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4)
    (hs : ∀ x y, SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y → x = y) :
    SingletonBlockCycle (unrooted N hN hX) C where
  conn := unrooted_isConnected hN hX
  loop := unrooted_source_ne_target hN
  nd _ C₂ h₁ h₂ hne := (lemma3_unrooted hN h1 hX h₁).2.2 C₂ h₂ hne
  leaf_deg := unrooted_degree_leaf hN
  deg := unrooted_degree_of_not_leaf hN
  inj := unrooted_leaf_injective hN
  side g hg _ hb := unrooted_exists_leaf_side hN g hg hb
  dir := unrooted_mem_cycle_of_isDirected hN h1
  block _ hC' _ hu := nodeBlock_nonempty_unrooted h1 hC' hu
  cycle := hC.1
  four := hC.2
  single := hs

/-- **The edges of a cycle of `N⁻` at its hybrid node enter it, and they are its only hybrid
edges**: an edge of `C` is hybrid exactly when it enters the hybrid node `v`. -/
theorem unrooted_isDirected_iff_target_eq_of_mem [Finite E] (h1 : IsLevelOne N.graph) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v} (hv : IsHybridNodeOf (unrooted N hN hX) C v)
    {e} (he : e ∈ C) :
    ((unrooted N hN hX).IsDirected e ↔ (unrooted N hN hX).graph.target e = v) ∧
      ((unrooted N hN hX).graph.source e = v → (unrooted N hN hX).graph.target e = v) := by
  set G := unrooted N hN hX
  -- the two edges of `C` at `v` are its two hybrid edges
  have hat : (G.graph.source e = v ∨ G.graph.target e = v) →
      G.IsDirected e ∧ G.graph.target e = v := by
    intro hev
    have hinc : {f | f ∈ C ∧ (G.graph.source f = v ∨ G.graph.target f = v)}.ncard = 2 :=
      hC.ncard_incident (unrooted_source_ne_target hN) hv.mem_cycleNodes
    obtain ⟨h₁, hh₁, h₂, hh₂, hne, hd₁, hd₂, ht₁, ht₂⟩ := hv
    by_contra hn
    have he₁ : e ≠ h₁ := by rintro rfl; exact hn ⟨hd₁, ht₁⟩
    have he₂ : e ≠ h₂ := by rintro rfl; exact hn ⟨hd₂, ht₂⟩
    have hsub : ({e, h₁, h₂} : Set _) ⊆ {f | f ∈ C ∧ (G.graph.source f = v ∨
        G.graph.target f = v)} := by
      rintro f (rfl | rfl | rfl)
      · exact ⟨he, hev⟩
      · exact ⟨hh₁, Or.inr ht₁⟩
      · exact ⟨hh₂, Or.inr ht₂⟩
    have h3 : ({e, h₁, h₂} : Set (SemidirectedArc hN.1 hN.2 hX)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by rintro (h | h) <;> [exact he₁ h; exact he₂ h]),
        Set.ncard_pair hne]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  refine ⟨⟨fun hd => ?_, fun ht => (hat (Or.inr ht)).1⟩, fun hs => (hat (Or.inl hs)).2⟩
  -- a hybrid edge of `C` enters a node with two parents in `N`, the hybrid node of `C`
  have h2 : N.graph.indegree (G.graph.target e).1.1 = 2 := by
    refine le_antisymm (hN.indegree_le_two _) (le_trans hd ?_)
    exact Set.ncard_le_ncard_of_injOn (fun e => e.1) (fun e he => congrArg Subtype.val he)
      (fun _ _ _ _ h => Subtype.ext h) (Set.toFinite _)
  exact (isHybridNodeOf_of_indegree h1 hC ⟨e, he, Or.inr rfl⟩ h2).eq h1 hC hv

end Unrooted

section Main

variable {X : Type} [Fintype X] [DecidableEq X] {V E : Type} [Fintype V] [Fintype E]

omit [Fintype X] [DecidableEq X] in
/-- **The block of a cycle toward another cycle of size at least four is not a 4-network block**:
for distinct cycles `C`, `C'` of size at least four of `N⁻`, there is a node `w` of `C` whose block
is not a 4-network block, such that `C'` has all the taxa outside the block of `w` in one of its
blocks.

`C` and `C'` have no common node (Lemma 3), so `C'` lies in the component of a node `w` of `C` once
the edges of `C` are removed, and every taxon outside the block of `w` is in the block of the node
`u'` of `C'` toward `C` (`walks_compl_of_not_walks_compl`). The block of `w` contains the taxa of
the blocks of the other nodes of `C'`, at least two of them, which `C'` separates. -/
theorem exists_not_isFourNetworkBlock_of_ne {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {C C' : Set _}
    (hC : C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4)
    (hC' : C' ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4) (hne : C' ≠ C) :
    ∃ w ∈ cycleNodes (unrooted N hN hX).graph C, ¬ IsFourNetworkBlock (unrooted N hN hX) C w ∧
      ∀ x y, x ∉ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C w →
        y ∉ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C w →
        SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C' x y := by
  set G := unrooted N hN hX with hG
  have hconn : G.graph.IsConnected := unrooted_isConnected hN hX
  have h1' : IsLevelOne G.graph := unrooted_isLevelOne hN h1 hX
  -- `C` and `C'` have no common node (Lemma 3), so no common edge
  have hdisj : ∀ z, z ∈ cycleNodes G.graph C → z ∉ cycleNodes G.graph C' := fun z hz hz' =>
    hne ((lemma3_unrooted hN h1 hX hC.1).2.2 C' hC'.1 ⟨z, hz, hz'⟩).symm
  have hCC' : ∀ f ∈ C, f ∉ C' := fun f hf hf' =>
    hdisj _ ⟨f, hf, Or.inl rfl⟩ ⟨f, hf', Or.inl rfl⟩
  -- `C'` is in the component of the node `w` of `C`, and every taxon outside the block of `w` is in
  -- the block of the node `u'` of `C'` toward `C`
  obtain ⟨z₀, hz₀⟩ := hC'.1.nonempty_cycleNodes
  obtain ⟨w, hw, hwz⟩ := exists_walks_compl_cycleNodes hconn hC.1 z₀
  obtain ⟨u', hu', hu'w⟩ := exists_walks_compl_cycleNodes hconn hC'.1 w
  have key : ∀ t, t ∉ nodeBlock G.graph G.leaf C w → t ∈ nodeBlock G.graph G.leaf C' u' :=
    fun t ht => walks_compl_of_not_walks_compl G.graph hconn hC.1 hC'.1 hCC' hz₀ hwz hw
      hu'w ht
  refine ⟨w, hw, fun hblock => ?_, fun x y hx hy =>
    (G.graph.walks_symm (key x hx)).trans (key y hy)⟩
  -- the block of `w` holds taxa of the blocks of two nodes `a`, `b` of `C'` other than `u'`
  obtain ⟨a, ha, hau⟩ := hC'.1.exists_mem_cycleNodes_notMem (Set.toFinite {u'})
    (by rw [Set.ncard_singleton]; have := hC'.2; omega)
  obtain ⟨b, hb, hbu⟩ := hC'.1.exists_mem_cycleNodes_notMem (Set.toFinite {u', a})
    (lt_of_le_of_lt ((Set.ncard_insert_le u' {a}).trans (by rw [Set.ncard_singleton]))
      (by have := hC'.2; omega))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hau hbu
  obtain ⟨ta, hta⟩ := nodeBlock_nonempty_unrooted h1 hC'.1 ha
  obtain ⟨tb, htb⟩ := nodeBlock_nonempty_unrooted h1 hC'.1 hb
  have hin : ∀ c t, c ∈ cycleNodes G.graph C' → c ≠ u' → t ∈ nodeBlock G.graph G.leaf C' c →
      t ∈ nodeBlock G.graph G.leaf C w := fun c t hc hcu ht => by
    by_contra hn
    exact hcu (h1'.eq_of_walks_compl hC'.1 hc hu' (ht.trans (G.graph.walks_symm (key t hn))))
  have hab : G.graph.Walks C'ᶜ (G.leaf ta) (G.leaf tb) :=
    walks_mono (Set.compl_subset_compl.2 (Set.subset_sUnion_of_mem hC'))
      (hblock ta (hin a ta ha hau hta) tb (hin b tb hb hbu.1 htb))
  exact hbu.2 (h1'.eq_of_walks_compl hC'.1 hb ha
    (htb.trans ((G.graph.walks_symm hab).trans (G.graph.walks_symm hta))))

omit [Fintype X] [DecidableEq X] in
/-- **A leaf of the tree of cycles** (proof of Theorem 4): if `N⁻` has at least two cycles of size
at least four, one of them, `C`, has a node `u` such that the blocks of the other nodes of `C` are
4-network blocks and that of `u` is not, and every other cycle of size at least four has all the
taxa outside the block of `u` in one of its blocks.

The tree of cycles `T` of `Ñ` has a leaf (`exists_isLeafNode_treeOfCycles_unrooted`), which
arises from a cycle `C` of size at least four (`exists_arisesFrom_of_isLeafNode_unrooted`) all of
whose blocks but that of a node `u` are 4-network blocks
(`fourNetworkBlocks_of_isLeafNode_unrooted`). For another such cycle `C'`, the node `w` of `C`
toward `C'` has a block that is not a 4-network block (`exists_not_isFourNetworkBlock_of_ne`), so
`w = u`, and `C'` has the taxa outside the block of `u` in one of its blocks.

The step follows Definition 13. The paper's claims that `T` is a tree and that a leaf of `T` arises
from a cycle all of whose blocks but one are 4-network blocks, which it does not prove, are the
lemmas of `Identify/TreeOfCycles.lean`. -/
theorem exists_leaf_bigCycle {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) (hX : Nontrivial X) (h2 : 2 ≤ bigCycleCount (unrooted N hN hX)) :
    ∃ C u, C ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4 ∧
      u ∈ cycleNodes (unrooted N hN hX).graph C ∧
      (∀ u' ∈ cycleNodes (unrooted N hN hX).graph C, u' ≠ u →
        IsFourNetworkBlock (unrooted N hN hX) C u') ∧
      ¬ IsFourNetworkBlock (unrooted N hN hX) C u ∧
      ∀ C' ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4, C' ≠ C → ∀ x y,
        x ∉ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u →
        y ∉ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u →
        SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C' x y := by
  -- a leaf of the tree of cycles, from a cycle `C` all of whose blocks but that of `u` are
  -- 4-network blocks
  obtain ⟨C₀, hC₀⟩ : (cyclesOfSizeAtLeast (unrooted N hN hX).graph 4).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by unfold bigCycleCount at h2; omega)
  obtain ⟨t, ht⟩ := exists_isLeafNode_treeOfCycles_unrooted hN h1 hX ⟨C₀, hC₀⟩
  obtain ⟨C, hC, htC⟩ := exists_arisesFrom_of_isLeafNode_unrooted hN h1 hX ht
  obtain ⟨u, hu, hblock⟩ := fourNetworkBlocks_of_isLeafNode_unrooted hN h1 hX hC htC ht
  -- the node of `C` toward another cycle of size at least four is `u`
  have htoward : ∀ C' ∈ cyclesOfSizeAtLeast (unrooted N hN hX).graph 4, C' ≠ C →
      ¬ IsFourNetworkBlock (unrooted N hN hX) C u ∧ ∀ x y,
        x ∉ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u →
        y ∉ nodeBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C u →
        SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C' x y := by
    intro C' hC' hne
    obtain ⟨w, hw, hnw, hside⟩ := exists_not_isFourNetworkBlock_of_ne hN h1 hX hC hC' hne
    obtain rfl : w = u := by_contra fun hwu => hnw (hblock w hw hwu)
    exact ⟨hnw, hside⟩
  obtain ⟨C', hC', hne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := cyclesOfSizeAtLeast (unrooted N hN hX).graph 4)
    (by unfold bigCycleCount at h2; omega) C
  exact ⟨C, u, hC, hu, hblock, (htoward C' hC' hne).1, fun C' hC' hne => (htoward C' hC' hne).2⟩

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- **A cycle with one taxon in each block** (Theorem 4, one cycle): two networks each with a cycle
of size at least four whose blocks are single taxa, with the same adjacent blocks and, for size at
least five, the same taxon descending from the hybrid node, have isomorphic networks `Ñ`: a cycle
with a leaf at each node, in the same order, its hybrid edges directed for size at least five.

Both are isomorphic to the same `cycleModel` (`SingletonBlockCycle.nonempty_sdIso_cycleModel`),
whose cycle edges are those of `C₁`, each joining the taxa of the blocks of its ends: the edge of
`C₂` joining the nodes of the same blocks exists by the adjacency of the blocks, and is unique since
a cycle of size at least three has no two edges with the same ends. An edge of the cycle is hybrid
exactly when it enters the hybrid node, whose block is the taxon descending from it. -/
theorem tilde_sdIso_of_singletonBlocks {V' E' : Type} [Fintype V'] [Fintype E']
    {N₁ : RootedNetwork V E X} {N₂ : RootedNetwork V' E' X} (hN₁ : IsBinaryRootedNetwork N₁)
    (hN₂ : IsBinaryRootedNetwork N₂) (h1₁ : IsLevelOne N₁.graph) (h1₂ : IsLevelOne N₂.graph)
    (hX : Nontrivial X) {C₁ : Set _} {C₂ : Set _} {v₁ v₂}
    (hC₁ : C₁ ∈ cyclesOfSizeAtLeast (unrooted N₁ hN₁ hX).graph 4)
    (hC₂ : C₂ ∈ cyclesOfSizeAtLeast (unrooted N₂ hN₂ hX).graph 4)
    (hv₁ : IsHybridNodeOf (unrooted N₁ hN₁ hX) C₁ v₁)
    (hv₂ : IsHybridNodeOf (unrooted N₂ hN₂ hX) C₂ v₂)
    (hs₁ : ∀ x y, SameBlock (unrooted N₁ hN₁ hX).graph (unrooted N₁ hN₁ hX).leaf C₁ x y → x = y)
    (hs₂ : ∀ x y, SameBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C₂ x y → x = y)
    (hadj : ∀ x y, AdjacentBlocks (unrooted N₁ hN₁ hX) C₁ x y ↔
        AdjacentBlocks (unrooted N₂ hN₂ hX) C₂ x y)
    (hhyb : 5 ≤ C₁.ncard → ∀ x, DescendsFrom (unrooted N₁ hN₁ hX) v₁ x ↔
      DescendsFrom (unrooted N₂ hN₂ hX) v₂ x) :
    Nonempty (SDIso (tildeNetwork (unrooted N₁ hN₁ hX)) (tildeNetwork (unrooted N₂ hN₂ hX))) := by
  have hS₁ := singletonBlockCycle_unrooted hN₁ h1₁ hC₁ hs₁
  have hS₂ := singletonBlockCycle_unrooted hN₂ h1₂ hC₂ hs₂
  set G₁ := unrooted N₁ hN₁ hX with hG₁
  set G₂ := unrooted N₂ hN₂ hX with hG₂
  -- the taxa of the blocks of the ends of each edge of `C₁`
  have hex : ∀ u ∈ cycleNodes G₁.graph C₁, ∃ x, blockNode G₁ C₁ x = u := fun _ hu =>
    hS₁.exists_blockNode_eq_of_mem hu
  let s : C₁ → X := fun e => Classical.choose (hex _ ⟨e.1, e.2, Or.inl rfl⟩)
  let t : C₁ → X := fun e => Classical.choose (hex _ ⟨e.1, e.2, Or.inr rfl⟩)
  have hs : ∀ e : C₁, blockNode G₁ C₁ (s e) = G₁.graph.source e.1 := fun e =>
    Classical.choose_spec (hex _ ⟨e.1, e.2, Or.inl rfl⟩)
  have ht : ∀ e : C₁, blockNode G₁ C₁ (t e) = G₁.graph.target e.1 := fun e =>
    Classical.choose_spec (hex _ ⟨e.1, e.2, Or.inr rfl⟩)
  let D : C₁ → Prop := fun e => 5 ≤ C₁.ncard ∧ G₁.IsDirected e.1
  obtain ⟨φ₁⟩ := hS₁.nonempty_sdIso_cycleModel s t D (Equiv.refl _)
    (fun e => Or.inl ⟨(hs e).symm, (ht e).symm⟩) (fun _ => Iff.rfl) (fun e _ => (ht e).symm)
  -- for each edge of `C₁`, the edge of `C₂` joining the nodes of the same blocks
  have hβ : ∀ e : C₁, ∃ e' : C₂,
      Joins G₂.graph e'.1 (blockNode G₂ C₂ (s e)) (blockNode G₂ C₂ (t e)) := by
    intro e
    have hadj₁ : AdjacentBlocks G₁ C₁ (s e) (t e) := ⟨e.1, e.2, _, _, Or.inl ⟨rfl, rfl⟩,
      (hs e) ▸ (hS₁.blockNode_mem_and _).2, (ht e) ▸ (hS₁.blockNode_mem_and _).2⟩
    obtain ⟨e', he', u, w, hj, hu, hw⟩ := (hadj _ _).1 hadj₁
    have hu' := hS₂.eq_blockNode_of_mem (u := u) (by
      rcases hj with ⟨h, -⟩ | ⟨-, h⟩
      exacts [⟨e', he', Or.inl h⟩, ⟨e', he', Or.inr h⟩]) hu
    have hw' := hS₂.eq_blockNode_of_mem (u := w) (by
      rcases hj with ⟨-, h⟩ | ⟨h, -⟩
      exacts [⟨e', he', Or.inr h⟩, ⟨e', he', Or.inl h⟩]) hw
    exact ⟨⟨e', he'⟩, hu' ▸ hw' ▸ hj⟩
  let β : C₁ → C₂ := fun e => Classical.choose (hβ e)
  have hβj : ∀ e, Joins G₂.graph (β e).1 (blockNode G₂ C₂ (s e)) (blockNode G₂ C₂ (t e)) :=
    fun e => Classical.choose_spec (hβ e)
  -- `β` is injective: an edge of a cycle of size at least three is determined by its ends
  have hβinj : Function.Injective β := by
    intro e₁ e₂ h
    have hj₂ := hβj e₂
    rw [← h] at hj₂
    have hst : (s e₁ = s e₂ ∧ t e₁ = t e₂) ∨ (s e₁ = t e₂ ∧ t e₁ = s e₂) := by
      rcases joins_unique (hβj e₁) hj₂ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨hS₂.blockNode_injective h₁, hS₂.blockNode_injective h₂⟩
      · exact Or.inr ⟨hS₂.blockNode_injective h₁, hS₂.blockNode_injective h₂⟩
    have hj : Joins G₁.graph e₂.1 (G₁.graph.source e₁.1) (G₁.graph.target e₁.1) := by
      rcases hst with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [← hs, ← ht, h₁, h₂, hs, ht]
        exact Or.inl ⟨rfl, rfl⟩
      · rw [← hs, ← ht, h₁, h₂, hs, ht]
        exact Or.inr ⟨rfl, rfl⟩
    exact Subtype.ext (hS₁.eq_of_joins_of_mem e₁.2 e₂.2 (Or.inl ⟨rfl, rfl⟩) hj)
  have hβbij : Function.Bijective β := hβinj.bijective_of_nat_card_le (by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, hS₁.ncard_eq_card, hS₂.ncard_eq_card])
  have hcard : C₁.ncard = C₂.ncard := by rw [hS₁.ncard_eq_card, hS₂.ncard_eq_card]
  -- for size at least five, the hybrid edges correspond
  have hkey : 5 ≤ C₁.ncard → ∀ e : C₁, (G₁.IsDirected e.1 ↔ blockNode G₂ C₂ (t e) = v₂) ∧
      (G₂.IsDirected (β e).1 ↔ blockNode G₂ C₂ (t e) = v₂) := by
    intro h5 e
    have hb : ∀ x, blockNode G₁ C₁ x = v₁ ↔ blockNode G₂ C₂ x = v₂ := fun x => by
      rw [blockNode_eq_iff_descendsFrom h1₁ hC₁.1 hv₁, blockNode_eq_iff_descendsFrom h1₂ hC₂.1 hv₂,
        hhyb h5]
    have hd₁ := unrooted_isDirected_iff_target_eq_of_mem hN₁ h1₁ hC₁.1 hv₁ e.2
    have hd₂ := unrooted_isDirected_iff_target_eq_of_mem hN₂ h1₂ hC₂.1 hv₂ (β e).2
    refine ⟨hd₁.1.trans (by rw [← ht, hb]), hd₂.1.trans ⟨fun h => ?_, fun h => ?_⟩⟩
    · rcases hβj e with ⟨-, h₂⟩ | ⟨h₁, h₂⟩
      · exact h₂ ▸ h
      · exfalso
        have hsv : G₁.graph.source e.1 = v₁ := by rw [← hs, hb, ← h₂, h]
        exact hS₁.loop _ (hsv.trans (hd₁.2 hsv).symm)
    · rcases hβj e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₂, h]
      · exact hd₂.2 (h₁.trans h)
  obtain ⟨φ₂⟩ := hS₂.nonempty_sdIso_cycleModel s t D (Equiv.ofBijective β hβbij) hβj
    (fun e => by
      show 5 ≤ C₁.ncard ∧ G₁.IsDirected e.1 ↔ 5 ≤ C₂.ncard ∧ G₂.IsDirected (β e).1
      rw [← hcard]
      constructor
      · rintro ⟨h5, hd⟩
        exact ⟨h5, ((hkey h5 e).2).2 (((hkey h5 e).1).1 hd)⟩
      · rintro ⟨h5, hd⟩
        exact ⟨h5, ((hkey h5 e).1).2 (((hkey h5 e).2).1 hd)⟩)
    (fun e ⟨h5, hd⟩ => by
      show G₂.graph.target (β e).1 = blockNode G₂ C₂ (t e)
      rw [(unrooted_isDirected_iff_target_eq_of_mem hN₂ h1₂ hC₂.1 hv₂ (β e).2).1.1
        (((hkey h5 e).2).2 (((hkey h5 e).1).1 hd))]
      exact (((hkey h5 e).1).1 hd).symm)
  exact ⟨φ₁.trans φ₂.symm⟩

end Main

end Banos2019
