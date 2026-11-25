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

end Anc

end Banos2019
