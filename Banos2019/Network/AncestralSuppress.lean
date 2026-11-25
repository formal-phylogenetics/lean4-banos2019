module

public import Banos2019.Network.Contraction

/-!
# The suppressed ancestral network, in the terms of the network

For a network `N` and a set `Z` of taxa, `M` is the ancestral network on `Z` (the arcs and nodes on
paths from the root to the taxa of `Z`) and `S` is `M` with its nodes of indegree and outdegree one
suppressed (Definition 7, steps 1 and 2). The nodes of `S` are the nodes of `M` that are not chain
nodes (`ChainZ`); an arc of `S` is the chain of `M` starting with an arc out of such a node, from its
source to the end of the chain (`chainEndZ`).

* `valS`, `valSE`: the node and the arc of `N` of a node and an arc of `S`.
* `suppressAnc_reaches_iff`: paths of `S` are paths of `N`.
* `suppressAnc_lsa`: the LSA of the taxa in `S` is `LSA(Z)` (Definition 7: "MRCA(Z, N⁺_Z) =
  MRCA(Z, N⁺)").
* `suppressAnc_isHybridArc_iff`: an arc of `S` is hybrid when the end of its chain has two parents.
* `isDPath_chainTail`: the chain of `M` from a node, as a path of `N`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

section Anc

variable {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {Z : Set X} (hZ : Z.Nonempty)

/-- A node of the ancestral network on `Z` of indegree one and outdegree one in it. -/
def ChainZ (v : V) : Prop :=
  ∃ h : v ∈ N.ancestralVertices Z, (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex ⟨v, h⟩

open Classical in
/-- The end of the chain of the ancestral network on `Z` from a node. -/
def chainEndZ (v : V) : V :=
  if h : v ∈ N.ancestralVertices Z then
    (chainEnd (N.ancestralNetwork_isPhylogenetic hN Z hZ) ⟨v, h⟩).1
  else v

theorem chainEndZ_of_mem {v : V} (h : v ∈ N.ancestralVertices Z) :
    chainEndZ hN hZ v = (chainEnd (N.ancestralNetwork_isPhylogenetic hN Z hZ) ⟨v, h⟩).1 := by
  unfold chainEndZ
  split_ifs
  rfl

/-- The node of `N` of a node of `S`. -/
def valS (s : {v : N.AncestralVertex Z //
    ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex v}) : V := s.1.1

/-- The arc of `N` of an arc of `S`. -/
def valSE (a : {e : N.AncestralArc Z // ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex
    ((N.ancestralNetwork Z hZ hN.root_reaches).graph.source e)}) : E := a.1.1

theorem valS_injective : Function.Injective (valS hN hZ) := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

theorem valSE_injective : Function.Injective (valSE hN hZ) := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

theorem mem_range_valS (v : V) :
    (∃ s, valS hN hZ s = v) ↔ v ∈ N.ancestralVertices Z ∧ ¬ ChainZ hN hZ v := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.1.2, fun ⟨h, hc⟩ => s.2 hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨⟨v, h⟩, fun h' => hc ⟨h, h'⟩⟩, rfl⟩

theorem mem_range_valSE (e : E) :
    (∃ a, valSE hN hZ a = e) ↔ e ∈ N.ancestralArcs Z ∧ ¬ ChainZ hN hZ (N.graph.source e) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1.2, fun ⟨h, hc⟩ => a.2 hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨⟨e, h⟩, fun h' => hc ⟨N.source_mem_ancestralVertices h, h'⟩⟩, rfl⟩

theorem valS_source (a) : valS hN hZ (((N.ancestralNetwork Z hZ hN.root_reaches).suppress
    (N.ancestralNetwork_isPhylogenetic hN Z hZ)).graph.source a) = N.graph.source (valSE hN hZ a) :=
  rfl

theorem valS_target (a) : valS hN hZ (((N.ancestralNetwork Z hZ hN.root_reaches).suppress
    (N.ancestralNetwork_isPhylogenetic hN Z hZ)).graph.target a) =
      chainEndZ hN hZ (N.graph.target (valSE hN hZ a)) := by
  show _ = chainEndZ hN hZ (N.graph.target a.1.1)
  rw [chainEndZ_of_mem hN hZ a.1.2]
  rfl

theorem valS_leaf (z : Z) : valS hN hZ (((N.ancestralNetwork Z hZ hN.root_reaches).suppress
    (N.ancestralNetwork_isPhylogenetic hN Z hZ)).leaf z) = N.leaf z := rfl

theorem valS_root : valS hN hZ (((N.ancestralNetwork Z hZ hN.root_reaches).suppress
    (N.ancestralNetwork_isPhylogenetic hN Z hZ)).root) = N.root := rfl

/-- The chain end of a node is reached from it. -/
theorem reaches_chainEndZ {v : V} : N.graph.Reaches v (chainEndZ hN hZ v) := by
  by_cases h : v ∈ N.ancestralVertices Z
  · rw [chainEndZ_of_mem hN hZ h]
    exact (N.ancestralGraph_reaches_iff Z ⟨v, h⟩ _).mp
      (chainReach_chainEnd (N.ancestralNetwork_isPhylogenetic hN Z hZ) ⟨v, h⟩).reaches
  · unfold chainEndZ
    split_ifs
    exact .refl

/-- **Paths of `S` are paths of `N`.** -/
theorem suppressAnc_reaches_iff (s s' : {v : N.AncestralVertex Z //
    ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex v}) :
    ((N.ancestralNetwork Z hZ hN.root_reaches).suppress
      (N.ancestralNetwork_isPhylogenetic hN Z hZ)).graph.Reaches s s' ↔
      N.graph.Reaches (valS hN hZ s) (valS hN hZ s') := by
  constructor
  · intro h
    refine Relation.ReflTransGen.lift' (valS hN hZ) (fun a b hab => ?_) s s' h
    obtain ⟨e, rfl, rfl⟩ := hab
    show N.graph.Reaches (valS hN hZ _) (valS hN hZ _)
    rw [valS_source, valS_target]
    exact (Relation.ReflTransGen.single ⟨_, rfl, rfl⟩).trans (reaches_chainEndZ hN hZ)
  · intro h
    exact suppress_reaches_of_reaches _ s s' ((N.ancestralGraph_reaches_iff Z _ _).mpr h)

/-- An arc of `S` is hybrid when the end of its chain has two parents in `N`. -/
theorem suppressAnc_isHybridArc_iff (a) :
    ((N.ancestralNetwork Z hZ hN.root_reaches).suppress
      (N.ancestralNetwork_isPhylogenetic hN Z hZ)).IsHybridArc a ↔
      2 ≤ N.graph.indegree (chainEndZ hN hZ (N.graph.target (valSE hN hZ a))) := by
  unfold IsHybridArc
  rw [suppress_indegree]
  change 2 ≤ (N.ancestralGraph Z).indegree _ ↔ _
  rw [N.ancestralGraph_indegree, ← valS_target hN hZ a]
  rfl

theorem suppressAnc_isTreeArc_iff (a) :
    ((N.ancestralNetwork Z hZ hN.root_reaches).suppress
      (N.ancestralNetwork_isPhylogenetic hN Z hZ)).IsTreeArc a ↔
      N.graph.indegree (chainEndZ hN hZ (N.graph.target (valSE hN hZ a))) = 1 := by
  unfold IsTreeArc
  rw [suppress_indegree]
  change (N.ancestralGraph Z).indegree _ = 1 ↔ _
  rw [N.ancestralGraph_indegree, ← valS_target hN hZ a]
  rfl

/-- The outdegree of a node in the ancestral network: its arcs above a taxon of `Z`. -/
theorem ancestral_outdegree (v : N.AncestralVertex Z) :
    (N.ancestralNetwork Z hZ hN.root_reaches).graph.outdegree v =
      {e | N.graph.source e = v.1 ∧ e ∈ N.ancestralArcs Z}.ncard := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext e
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨congrArg Subtype.val ha, a.2⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨e, h'⟩, Subtype.ext h, rfl⟩

/-- **The LSA of `Z` has two arcs above taxa of `Z`.** -/
theorem lsa_outdegree_ancestral (hN : N.IsPhylogenetic) (hB : N.IsBinary) (hZ : Z.Nontrivial) :
    {e | N.graph.source e = lsa hN Z hZ.nonempty ∧ e ∈ N.ancestralArcs Z}.ncard = 2 := by
  have h := lsaNetwork_outdegree_root hN hB hZ
  unfold DirectedMultigraph.outdegree at h
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective] at h
  rw [← h]
  congr 1
  ext e
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨e, h₁ ▸ .refl, h₂⟩, Subtype.ext h₁, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨congrArg Subtype.val ha, a.2.2⟩

/-- The LSA of `Z` is not a chain node. -/
theorem not_chainZ_lsa (hB : N.IsBinary) (hZ : Z.Nontrivial) :
    ¬ ChainZ hN hZ.nonempty (lsa hN Z hZ.nonempty) := by
  rintro ⟨h, -, h1⟩
  rw [ancestral_outdegree hN, lsa_outdegree_ancestral hN hB hZ] at h1
  exact absurd h1 (by norm_num)

/-- A chain of the ancestral network from a chain node, or from its end, avoids a node that is not a
chain node, when it ends elsewhere. -/
theorem chainReach_avoiding {w : N.AncestralVertex Z}
    (hw : ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex w)
    {x y : N.AncestralVertex Z} (hxy : (N.ancestralNetwork Z hZ hN.root_reaches).ChainReach x y)
    (hyw : y ≠ w) (hx : (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex x ∨ x = y) :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ w.1 ∧ b ≠ w.1) x.1 y.1 := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b hab hby ih =>
    have ha : a.1 ≠ w.1 := fun h => hw (Subtype.ext h ▸ hab.1)
    have hb : (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex b ∨ b = y := by
      rcases Relation.ReflTransGen.cases_head hby with h | ⟨c, hc, -⟩
      · exact Or.inr h
      · exact Or.inl hc.1
    have hb' : b.1 ≠ w.1 := by
      rcases hb with hb | rfl
      · exact fun h => hw (Subtype.ext h ▸ hb)
      · exact fun h => hyw (Subtype.ext h)
    exact (ih hb).head ⟨(N.ancestralGraph_adj_iff Z a b).mp hab.2, ha, hb'⟩

/-- A path of `S` avoiding a node is a path of `N` avoiding it. -/
theorem suppressAnc_avoiding {w s s' : {v : N.AncestralVertex Z //
    ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex v}}
    (h : Relation.ReflTransGen (fun a b => ((N.ancestralNetwork Z hZ hN.root_reaches).suppress
      (N.ancestralNetwork_isPhylogenetic hN Z hZ)).graph.Adj a b ∧ a ≠ w ∧ b ≠ w) s s') :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ valS hN hZ w ∧ b ≠ valS hN hZ w)
      (valS hN hZ s) (valS hN hZ s') := by
  have hM := N.ancestralNetwork_isPhylogenetic hN Z hZ
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨⟨e, he₁, he₂⟩, ha, hb⟩ := hab
    refine ih.trans ?_
    have hsrc : valS hN hZ a = N.graph.source e.1.1 := by rw [← he₁]; rfl
    have htgt : valS hN hZ b =
        (chainEnd hM ((N.ancestralNetwork Z hZ hN.root_reaches).graph.target e.1)).1 := by
      rw [← he₂]; rfl
    rw [hsrc, htgt]
    have hend : chainEnd hM ((N.ancestralNetwork Z hZ hN.root_reaches).graph.target e.1) ≠ w.1 :=
      fun h => hb (by rw [← he₂]; exact Subtype.ext h)
    have hta : ((N.ancestralNetwork Z hZ hN.root_reaches).graph.target e.1).1 ≠ w.1.1 := by
      intro h
      by_cases hc : (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex
          ((N.ancestralNetwork Z hZ hN.root_reaches).graph.target e.1)
      · exact w.2 ((Subtype.ext h : _ = w.1) ▸ hc)
      · rw [chainEnd_eq_self hM hc] at hend
        exact hend (Subtype.ext h)
    refine Relation.ReflTransGen.head ⟨⟨e.1.1, rfl, rfl⟩, fun h => ha
      (valS_injective hN hZ (hsrc.trans h)), hta⟩
      (chainReach_avoiding hN hZ w.2 (chainReach_chainEnd hM _) hend ?_)
    by_cases hc : (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex
        ((N.ancestralNetwork Z hZ hN.root_reaches).graph.target e.1)
    · exact Or.inl hc
    · exact Or.inr (chainEnd_eq_self hM hc).symm

/-- A path of `N` to a taxon of `Z` avoiding a node of `S` gives a path of `S` avoiding it, from the
end of the chain of its first node. -/
theorem suppressAnc_of_avoiding {w : {v : N.AncestralVertex Z //
    ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex v}} {a : V} {z : Z}
    (h : Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ valS hN hZ w ∧ b ≠ valS hN hZ w)
      a (N.leaf z)) (hzw : N.leaf z ≠ valS hN hZ w) (ha : a ∈ N.ancestralVertices Z)
    (haw : a ≠ valS hN hZ w) :
    ∃ s, valS hN hZ s = (chainEnd (N.ancestralNetwork_isPhylogenetic hN Z hZ) ⟨a, ha⟩).1 ∧ s ≠ w ∧
      Relation.ReflTransGen (fun a b => ((N.ancestralNetwork Z hZ hN.root_reaches).suppress
        (N.ancestralNetwork_isPhylogenetic hN Z hZ)).graph.Adj a b ∧ a ≠ w ∧ b ≠ w) s
        (((N.ancestralNetwork Z hZ hN.root_reaches).suppress
          (N.ancestralNetwork_isPhylogenetic hN Z hZ)).leaf z) := by
  set M := N.ancestralNetwork Z hZ hN.root_reaches
  have hM := N.ancestralNetwork_isPhylogenetic hN Z hZ
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have hz : ¬ M.IsChainVertex ⟨N.leaf z, ha⟩ := not_isChainVertex_leaf hM z
    refine ⟨(M.suppress hM).leaf z, (congrArg Subtype.val (chainEnd_eq_self hM hz)).symm,
      fun h => hzw (congrArg (valS hN hZ) h), .refl⟩
  | @head a b hab hbz ih =>
    obtain ⟨⟨f, hfs, hft⟩, -, hbw⟩ := hab
    have hb : b ∈ N.ancestralVertices Z := N.mem_ancestralVertices_of_reaches
      (Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hbz) (N.leaf_mem_ancestralVertices z.2)
    obtain ⟨sb, hsb, hsbw, hpb⟩ := ih hb hbw
    have hf : f ∈ N.ancestralArcs Z := by
      change N.graph.target f ∈ N.ancestralVertices Z
      rw [hft]
      exact hb
    have hadj : M.graph.Adj ⟨a, ha⟩ ⟨b, hb⟩ := ⟨⟨f, hf⟩, Subtype.ext hfs, Subtype.ext hft⟩
    by_cases hc : M.IsChainVertex ⟨a, ha⟩
    · refine ⟨sb, ?_, hsbw, hpb⟩
      rw [hsb, chainEnd_eq_of_adj hM hc hadj]
    · refine ⟨⟨⟨a, ha⟩, hc⟩, (congrArg Subtype.val (chainEnd_eq_self hM hc)).symm,
        fun h => haw (congrArg (valS hN hZ) h), Relation.ReflTransGen.head ⟨?_, fun h =>
          haw (congrArg (valS hN hZ) h), hsbw⟩ hpb⟩
      refine ⟨⟨⟨f, hf⟩, by
        change ¬ M.IsChainVertex (M.graph.source ⟨f, hf⟩)
        rwa [show M.graph.source ⟨f, hf⟩ = ⟨a, ha⟩ from Subtype.ext hfs]⟩, ?_, ?_⟩
      · exact Subtype.ext (Subtype.ext hfs)
      · refine valS_injective hN hZ ?_
        have hfb : (⟨N.graph.target f, hf⟩ : N.AncestralVertex Z) = ⟨b, hb⟩ := Subtype.ext hft
        show (chainEnd hM ⟨N.graph.target f, hf⟩).1 = valS hN hZ sb
        rw [hsb, hfb]

/-- **The LSA of the taxa in `S` is `LSA(Z)`** (Definition 7: `MRCA(Z, N⁺_Z) = MRCA(Z, N⁺)`). -/
theorem suppressAnc_isLeastStableAncestor (hB : N.IsBinary) (hZ : Z.Nontrivial) :
    ((N.ancestralNetwork Z hZ.nonempty hN.root_reaches).suppress
      (N.ancestralNetwork_isPhylogenetic hN Z hZ.nonempty)).IsLeastStableAncestor Set.univ
      ⟨⟨lsa hN Z hZ.nonempty, lsa_mem_ancestralVertices hN hZ.nonempty⟩,
        fun h => not_chainZ_lsa hN hB hZ ⟨_, h⟩⟩ := by
  set S := (N.ancestralNetwork Z hZ.nonempty hN.root_reaches).suppress
    (N.ancestralNetwork_isPhylogenetic hN Z hZ.nonempty)
  have hlsa := lsa_spec hN Z hZ.nonempty
  refine ⟨fun z _ ⟨hr, hz, hp⟩ => ?_, fun w hw => ?_⟩
  · refine hlsa.1 z z.2 ⟨fun h => hr (valS_injective hN hZ.nonempty h), fun h => hz
      (valS_injective hN hZ.nonempty h), suppressAnc_avoiding hN hZ.nonempty hp⟩
  · have hst : N.IsStableAncestor Z (valS hN hZ.nonempty w) := by
      rintro x hx ⟨hr, hz, hp⟩
      have hroot : ¬ (N.ancestralNetwork Z hZ.nonempty hN.root_reaches).IsChainVertex
          (N.ancestralNetwork Z hZ.nonempty hN.root_reaches).root :=
        not_isChainVertex_root (N.ancestralNetwork_isPhylogenetic hN Z hZ.nonempty)
      obtain ⟨s, hs, hsw, hps⟩ := suppressAnc_of_avoiding hN hZ.nonempty (z := ⟨x, hx⟩) hp hz
        (N.root_mem_ancestralVertices hZ.nonempty hN.root_reaches) hr
      have : s = S.root := valS_injective hN hZ.nonempty (hs.trans
        (congrArg Subtype.val (chainEnd_eq_self _ hroot)))
      subst this
      exact hw ⟨x, hx⟩ trivial ⟨hsw, fun h => hz (congrArg (valS hN hZ.nonempty) h), hps⟩
    exact (suppressAnc_reaches_iff hN hZ.nonempty _ _).mpr (hlsa.2 _ hst)

/-- The nodes of the chain of the ancestral network from `a`. -/
def chainNodes (a : V) : Set V :=
  {v | ∃ (ha : a ∈ N.ancestralVertices Z) (hv : v ∈ N.ancestralVertices Z),
    (N.ancestralNetwork Z hZ hN.root_reaches).ChainReach ⟨a, ha⟩ ⟨v, hv⟩}

/-- The arcs of the chain of the ancestral network from `a`: those out of its chain nodes. -/
def chainTailArcs (a : V) : Set E :=
  {e | ∃ (ha : a ∈ N.ancestralVertices Z) (he : e ∈ N.ancestralArcs Z),
    (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex
      ((N.ancestralNetwork Z hZ hN.root_reaches).graph.source ⟨e, he⟩) ∧
    (N.ancestralNetwork Z hZ hN.root_reaches).ChainReach ⟨a, ha⟩
      ((N.ancestralNetwork Z hZ hN.root_reaches).graph.source ⟨e, he⟩)}

/-- **The chain of the ancestral network from a node, as a path of `N`**, to the end of the chain. -/
theorem isDPath_chainTail [Finite V] {a : V} (ha : a ∈ N.ancestralVertices Z) :
    IsDPath N.graph a (chainEndZ hN hZ a) (chainNodes hN hZ a) (chainTailArcs hN hZ a) := by
  set M := N.ancestralNetwork Z hZ hN.root_reaches
  have hM := N.ancestralNetwork_isPhylogenetic hN Z hZ
  rw [chainEndZ_of_mem hN hZ ha]
  suffices key : ∀ b : N.AncestralVertex Z, IsDPath N.graph b.1 (chainEnd hM b).1
      {v | ∃ hv : v ∈ N.ancestralVertices Z, M.ChainReach b ⟨v, hv⟩}
      {e | ∃ he : e ∈ N.ancestralArcs Z, M.IsChainVertex (M.graph.source ⟨e, he⟩) ∧
        M.ChainReach b (M.graph.source ⟨e, he⟩)} by
    have h := key ⟨a, ha⟩
    convert h using 1
    · ext v
      exact ⟨fun ⟨_, hv, h⟩ => ⟨hv, h⟩, fun ⟨hv, h⟩ => ⟨ha, hv, h⟩⟩
    · ext e
      exact ⟨fun ⟨_, he, h⟩ => ⟨he, h⟩, fun ⟨he, h⟩ => ⟨ha, he, h⟩⟩
  let r : N.AncestralVertex Z → N.AncestralVertex Z → Prop :=
    fun a b => Relation.TransGen M.graph.Adj b a
  have : IsTrans _ r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hM.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  intro b
  induction b using hwf.induction with
  | _ b ih =>
    by_cases hc : M.IsChainVertex b
    · obtain ⟨g, hg⟩ := (M.graph.outdegree_eq_one_iff b).mp hc.2
      have hgs : M.graph.source g = b := (hg g).mpr rfl
      have hadj : M.graph.Adj b (M.graph.target g) := ⟨g, hgs, rfl⟩
      have ih' := ih _ (.single hadj)
      rw [chainEnd_eq_of_adj hM hc hadj]
      -- the chain from `b` is the arc `g` followed by the chain from its child
      have hreach : ∀ x, M.ChainReach b x ↔ x = b ∨ M.ChainReach (M.graph.target g) x := by
        intro x
        constructor
        · intro h
          rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc', hcx⟩
          · exact Or.inl h.symm
          · exact Or.inr (hc.adj_unique hc'.2 hadj ▸ hcx)
        · rintro (rfl | h)
          · exact .refl
          · exact h.head ⟨hc, hadj⟩
      have := IsDPath.cons g.1 ih'
      rw [show N.graph.source g.1 = b.1 from congrArg Subtype.val hgs] at this
      convert this using 1
      · ext v
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
        constructor
        · rintro ⟨hv, h⟩
          rcases (hreach _).mp h with h | h
          · exact Or.inl (congrArg Subtype.val h)
          · exact Or.inr ⟨hv, h⟩
        · rintro (rfl | ⟨hv, h⟩)
          · exact ⟨b.2, (hreach _).mpr (Or.inl rfl)⟩
          · exact ⟨hv, (hreach _).mpr (Or.inr h)⟩
      · ext e
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
        constructor
        · rintro ⟨he, hce, h⟩
          rcases (hreach _).mp h with h | h
          · exact Or.inl (congrArg Subtype.val ((hg ⟨e, he⟩).mp h))
          · exact Or.inr ⟨he, hce, h⟩
        · rintro (rfl | ⟨he, hce, h⟩)
          · exact ⟨g.2, hgs ▸ hc, (hreach _).mpr (Or.inl hgs)⟩
          · exact ⟨he, hce, (hreach _).mpr (Or.inr h)⟩
    · rw [chainEnd_eq_self hM hc]
      have hreach : ∀ x, M.ChainReach b x ↔ x = b := by
        intro x
        constructor
        · intro h
          rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc', -⟩
          · exact h.symm
          · exact absurd hc'.1 hc
        · rintro rfl
          exact .refl
      convert IsDPath.nil (G := N.graph) b.1 using 1
      · ext v
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hv, h⟩
          exact congrArg Subtype.val ((hreach _).mp h)
        · rintro rfl
          exact ⟨b.2, .refl⟩
      · ext e
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨he, hce, h⟩
        exact hc ((hreach _).mp h ▸ hce)

/-- A node of a chain other than its end is a chain node. -/
theorem chainZ_of_mem_chainNodes {a v : V} (hv : v ∈ chainNodes hN hZ a)
    (hne : v ≠ chainEndZ hN hZ a) : ChainZ hN hZ v := by
  obtain ⟨ha, hv', h⟩ := hv
  refine ⟨hv', ?_⟩
  by_contra hc
  rw [chainEndZ_of_mem hN hZ ha, chainEnd_eq_of_chainReach _ h hc] at hne
  exact hne rfl

/-- The end of a chain is not a chain node. -/
theorem not_chainZ_chainEndZ {a : V} (ha : a ∈ N.ancestralVertices Z) :
    ¬ ChainZ hN hZ (chainEndZ hN hZ a) := by
  rintro ⟨h, hc⟩
  have heq : (⟨chainEndZ hN hZ a, h⟩ : N.AncestralVertex Z) =
      chainEnd (N.ancestralNetwork_isPhylogenetic hN Z hZ) ⟨a, ha⟩ :=
    Subtype.ext (chainEndZ_of_mem hN hZ ha)
  rw [heq] at hc
  exact not_isChainVertex_chainEnd (N.ancestralNetwork_isPhylogenetic hN Z hZ) ⟨a, ha⟩ hc

/-- The arcs of the chain of the ancestral network starting with `f`. -/
def chainArcs (f : E) : Set E :=
  {g | ∃ (hf : f ∈ N.ancestralArcs Z) (hg : g ∈ N.ancestralArcs Z),
    (N.ancestralNetwork Z hZ hN.root_reaches).IsOnChain ⟨f, hf⟩ ⟨g, hg⟩}

theorem chainArcs_eq {f : E} (hf : f ∈ N.ancestralArcs Z) :
    chainArcs hN hZ f = insert f (chainTailArcs hN hZ (N.graph.target f)) := by
  ext g
  constructor
  · intro hgm
    obtain ⟨_, hg, h⟩ := hgm
    rcases h with h | ⟨hc, hr⟩
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr ⟨hf, hg, hc, hr⟩
  · intro hgm
    rcases hgm with h | hgm
    · subst h
      exact ⟨hf, hf, Or.inl rfl⟩
    · obtain ⟨_, hg, hc, hr⟩ := hgm
      exact ⟨hf, hg, Or.inr ⟨hc, hr⟩⟩

/-- The chain from a node of a chain ends where the chain does. -/
theorem chainEndZ_eq_of_mem {a v : V} (hv : v ∈ chainNodes hN hZ a) :
    chainEndZ hN hZ a = chainEndZ hN hZ v := by
  obtain ⟨ha, hv', h⟩ := hv
  rw [chainEndZ_of_mem hN hZ ha, chainEndZ_of_mem hN hZ hv',
    chainEnd_eq_of_chainReach_left _ h]

theorem reaches_of_mem_chainNodes {a v : V} (hv : v ∈ chainNodes hN hZ a) :
    N.graph.Reaches a v := by
  obtain ⟨ha, hv', h⟩ := hv
  exact (N.ancestralGraph_reaches_iff Z ⟨a, ha⟩ ⟨v, hv'⟩).mp h.reaches

theorem mem_chainNodes_self {a : V} (ha : a ∈ N.ancestralVertices Z) : a ∈ chainNodes hN hZ a :=
  ⟨ha, ha, .refl⟩

theorem chainEndZ_mem_chainNodes {a : V} (ha : a ∈ N.ancestralVertices Z) :
    chainEndZ hN hZ a ∈ chainNodes hN hZ a := by
  have hM := N.ancestralNetwork_isPhylogenetic hN Z hZ
  rw [chainEndZ_of_mem hN hZ ha]
  exact ⟨ha, (chainEnd hM ⟨a, ha⟩).2, chainReach_chainEnd hM ⟨a, ha⟩⟩

theorem chainEndZ_mem {a : V} (ha : a ∈ N.ancestralVertices Z) :
    chainEndZ hN hZ a ∈ N.ancestralVertices Z := by
  rw [chainEndZ_of_mem hN hZ ha]
  exact (chainEnd (N.ancestralNetwork_isPhylogenetic hN Z hZ) ⟨a, ha⟩).2

/-- An arc into a node that is not a chain node is the last arc of its chain. -/
theorem target_eq_chainEndZ_of_mem_chainArcs {f g : E} (hg : g ∈ chainArcs hN hZ f)
    (hc : ¬ ChainZ hN hZ (N.graph.target g)) :
    N.graph.target g = chainEndZ hN hZ (N.graph.target f) := by
  obtain ⟨hf, hg', h⟩ := hg
  have hM := N.ancestralNetwork_isPhylogenetic hN Z hZ
  have hc' : ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex ⟨N.graph.target g, hg'⟩ :=
    fun h' => hc ⟨hg', h'⟩
  rw [chainEndZ_of_mem hN hZ hf]
  have := h.chainEnd_eq hM
  have hc'' : ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex
      ((N.ancestralNetwork Z hZ hN.root_reaches).graph.target ⟨g, hg'⟩) := hc'
  rw [chainEnd_eq_self hM hc''] at this
  exact (congrArg Subtype.val this).symm

/-- Distinct chains from nodes that are not chain nodes end at distinct nodes, when one of them
ends at a node with one parent. -/
theorem chainEndZ_ne {f f' : E} (hf : f ∈ N.ancestralArcs Z) (hf' : f' ∈ N.ancestralArcs Z)
    (hs : ¬ ChainZ hN hZ (N.graph.source f)) (hs' : ¬ ChainZ hN hZ (N.graph.source f'))
    (hne : f ≠ f') (hin : N.graph.indegree (chainEndZ hN hZ (N.graph.target f)) = 1) :
    chainEndZ hN hZ (N.graph.target f) ≠ chainEndZ hN hZ (N.graph.target f') := by
  have := hN.finite_arcs
  set M := N.ancestralNetwork Z hZ hN.root_reaches
  have hM := N.ancestralNetwork_isPhylogenetic hN Z hZ
  have hsA : ¬ M.IsChainVertex (M.graph.source ⟨f, hf⟩) :=
    fun h => hs ⟨N.source_mem_ancestralVertices hf, h⟩
  have hsA' : ¬ M.IsChainVertex (M.graph.source ⟨f', hf'⟩) :=
    fun h => hs' ⟨N.source_mem_ancestralVertices hf', h⟩
  intro heq
  have h₁ := target_chainLast hM ⟨f, hf⟩
  have h₂ := target_chainLast hM ⟨f', hf'⟩
  have hl : chainLast hM ⟨f, hf⟩ ≠ chainLast hM ⟨f', hf'⟩ := fun h => hne (congrArg Subtype.val
    (congrArg Subtype.val (chainLast_injective hM (a₁ := ⟨⟨f, hf⟩, hsA⟩) (a₂ := ⟨⟨f', hf'⟩, hsA'⟩) h)))
  have hl' : (chainLast hM ⟨f, hf⟩).1 ≠ (chainLast hM ⟨f', hf'⟩).1 := fun h => hl (Subtype.ext h)
  have ht₁ : N.graph.target (chainLast hM ⟨f, hf⟩).1 = chainEndZ hN hZ (N.graph.target f) := by
    rw [chainEndZ_of_mem hN hZ hf]
    exact congrArg Subtype.val h₁
  have ht₂ : N.graph.target (chainLast hM ⟨f', hf'⟩).1 = chainEndZ hN hZ (N.graph.target f) := by
    rw [heq, chainEndZ_of_mem hN hZ hf']
    exact congrArg Subtype.val h₂
  have hsub : ({(chainLast hM ⟨f, hf⟩).1, (chainLast hM ⟨f', hf'⟩).1} : Set E) ⊆
      {e | N.graph.target e = chainEndZ hN hZ (N.graph.target f)} := by
    rintro e (rfl | rfl)
    · exact ht₁
    · exact ht₂
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hl'] at this
  unfold DirectedMultigraph.indegree at hin
  omega

/-- A chain has one first arc. -/
theorem eq_of_mem_chainArcs {f f' a : E} (h : a ∈ chainArcs hN hZ f) (h' : a ∈ chainArcs hN hZ f')
    (hs : ¬ ChainZ hN hZ (N.graph.source f)) (hs' : ¬ ChainZ hN hZ (N.graph.source f')) : f = f' := by
  obtain ⟨hf, ha, hon⟩ := h
  obtain ⟨hf', ha', hon'⟩ := h'
  exact congrArg Subtype.val (hon.unique hon'
    (fun (hc : (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex
      ((N.ancestralNetwork Z hZ hN.root_reaches).graph.source ⟨f, hf⟩)) =>
        hs ⟨N.source_mem_ancestralVertices hf, hc⟩)
    fun (hc : (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex
      ((N.ancestralNetwork Z hZ hN.root_reaches).graph.source ⟨f', hf'⟩)) =>
        hs' ⟨N.source_mem_ancestralVertices hf', hc⟩)

/-- The arcs of a chain leave nodes below its first node. -/
theorem reaches_source_of_mem_chainArcs {f a : E} (h : a ∈ chainArcs hN hZ f) :
    N.graph.Reaches (N.graph.source f) (N.graph.source a) := by
  obtain ⟨hf, ha, h | ⟨-, hr⟩⟩ := h
  · rw [show a = f from congrArg Subtype.val h]
    exact .refl
  · exact (Relation.ReflTransGen.single ⟨f, rfl, rfl⟩).trans
      ((N.ancestralGraph_reaches_iff Z _ _).mp hr.reaches)

/-- A chain node has one parent. -/
theorem indegree_of_chainZ {v : V} (hv : ChainZ hN hZ v) : N.graph.indegree v = 1 := by
  obtain ⟨h, h₁, -⟩ := hv
  exact (N.ancestralGraph_indegree Z ⟨v, h⟩).symm.trans h₁

/-- The last arc of a chain enters its end. -/
theorem exists_last_mem_chainArcs {f : E} (hf : f ∈ N.ancestralArcs Z) :
    ∃ a ∈ chainArcs hN hZ f, N.graph.target a = chainEndZ hN hZ (N.graph.target f) := by
  have hM := N.ancestralNetwork_isPhylogenetic hN Z hZ
  refine ⟨(chainLast hM ⟨f, hf⟩).1, ⟨hf, (chainLast hM ⟨f, hf⟩).2, isOnChain_chainLast hM _⟩, ?_⟩
  rw [chainEndZ_of_mem hN hZ hf]
  exact congrArg Subtype.val (target_chainLast hM ⟨f, hf⟩)

/-- **Every arc of the ancestral network is on a chain** starting at a node that is not a chain
node. -/
theorem exists_mem_chainArcs {a : E} (ha : a ∈ N.ancestralArcs Z) :
    ∃ f, ¬ ChainZ hN hZ (N.graph.source f) ∧ a ∈ chainArcs hN hZ f := by
  have hM := N.ancestralNetwork_isPhylogenetic hN Z hZ
  refine ⟨(chainHead hM ⟨a, ha⟩).1.1, fun ⟨_, hc⟩ => (chainHead hM ⟨a, ha⟩).2 hc,
    (chainHead hM ⟨a, ha⟩).1.2, ha, isOnChain_chainHead hM ⟨a, ha⟩⟩

/-- Two arcs of a chain entering a node that is not a chain node are the same. -/
theorem eq_of_mem_chainArcs_of_target {f a b : E} (ha : a ∈ chainArcs hN hZ f)
    (hb : b ∈ chainArcs hN hZ f) (ht : N.graph.target a = N.graph.target b)
    (hc : ¬ ChainZ hN hZ (N.graph.target a)) : a = b := by
  obtain ⟨hf, ha', hona⟩ := ha
  obtain ⟨_, hb', honb⟩ := hb
  exact congrArg Subtype.val (hona.eq_of_target honb
    (Subtype.ext ht : (N.ancestralNetwork Z hZ hN.root_reaches).graph.target ⟨a, ha'⟩ =
      (N.ancestralNetwork Z hZ hN.root_reaches).graph.target ⟨b, hb'⟩) fun h => hc ⟨ha', h⟩)

/-- **The lengths of the suppressed ancestral network** are the sums along the chains. -/
theorem suppressMetric_length_ancestral [Fintype (N.AncestralArc Z)] (θ : MetricData E)
    (a : {e : N.AncestralArc Z // ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex
      ((N.ancestralNetwork Z hZ hN.root_reaches).graph.source e)}) :
    ((N.ancestralNetwork Z hZ hN.root_reaches).suppressMetric
      ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩).length a =
      ∑ᶠ b ∈ chainArcs hN hZ a.1.1, θ.length b := by
  classical
  unfold RootedNetwork.suppressMetric
  simp only
  rw [← finsum_mem_coe_finset, Finset.coe_filter]
  simp only [Finset.mem_univ, true_and]
  rw [← finsum_mem_image (g := Subtype.val) Subtype.val_injective.injOn]
  refine finsum_mem_congr (Set.ext fun b => ?_) fun _ _ => rfl
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨a.1.2, c.2, hc⟩
  · rintro ⟨_, hb, h⟩
    exact ⟨⟨b, hb⟩, h, rfl⟩

/-- **The inheritance probabilities of the suppressed ancestral network** are the products along the
chains. -/
theorem suppressMetric_inheritance_ancestral [Fintype (N.AncestralArc Z)] (θ : MetricData E)
    (a : {e : N.AncestralArc Z // ¬ (N.ancestralNetwork Z hZ hN.root_reaches).IsChainVertex
      ((N.ancestralNetwork Z hZ hN.root_reaches).graph.source e)}) :
    ((N.ancestralNetwork Z hZ hN.root_reaches).suppressMetric
      ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩).inheritance a =
      ∏ᶠ b ∈ chainArcs hN hZ a.1.1, θ.inheritance b := by
  classical
  unfold RootedNetwork.suppressMetric
  simp only
  rw [← finprod_mem_coe_finset, Finset.coe_filter]
  simp only [Finset.mem_univ, true_and]
  rw [← finprod_mem_image (g := Subtype.val) Subtype.val_injective.injOn]
  refine finprod_mem_congr (Set.ext fun b => ?_) fun _ _ => rfl
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨a.1.2, c.2, hc⟩
  · rintro ⟨_, hb, h⟩
    exact ⟨⟨b, hb⟩, h, rfl⟩

end Anc

end Banos2019
