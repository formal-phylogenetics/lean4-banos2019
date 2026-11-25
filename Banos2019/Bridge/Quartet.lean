module

public import Banos2019.Bridge.Unrooted
public import Banos2019.CycleProperty

/-!
# The induced unrooted network of the Challenge and the library's `Q⁻_s`

The Challenge's Theorem 3 speaks of `(N⁻)_s`, the induced unrooted network of Definition 10. The
library's speaks of `Q⁻_s = (N⊕_s)⁻`, the unrooted network of the induced LSA network, through its
4-cycles (`HasFourCycle`). They are joined by Proposition 1, `(N⁻)_s ≅ (N⁺_s)⁻`, and by the fact
that `N⊕_s` is the part of `N⁺_s` below its LSA: below `LSA(s)`, both are the nodes and arcs of `N`
above taxa of `s`, with the nodes of indegree and outdegree one suppressed
(`belowLSA_inducedRooted_sdIso`), so that `(N⁺_s)⁻ ≅ (N⊕_s)⁻` (`unrooted_inducedRooted_sdIso`).

* `SDIso.ofValues`: an isomorphism of two semidirected networks whose nodes and edges are given, by
  injective maps with the same images, by the same objects.
* `lsaNetwork_isChainVertex_iff`, `lsaNetwork_chainEnd_val`: below `LSA(Z)`, the network below the LSA
  and the ancestral network have the same nodes of indegree and outdegree one, and the same chains.
* `Model.Network.exists_fourCycle_induced_iff`: the right side of Theorem 3.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-! ### Isomorphisms from common values -/

section OfValues

variable {V₁ E₁ V₂ E₂ W F : Type*} {G₁ : SemidirectedNetwork V₁ E₁ X}
  {G₂ : SemidirectedNetwork V₂ E₂ X}

theorem ofInjectiveSubtype_trans_symm_apply {α β γ : Type*} (f₁ : α → γ)
    (hf₁ : Function.Injective f₁) (f₂ : β → γ) (hf₂ : Function.Injective f₂) (Q : γ → Prop)
    (hQ₁ : ∀ c, Q c ↔ ∃ a, f₁ a = c) (hQ₂ : ∀ c, Q c ↔ ∃ b, f₂ b = c) (a : α) :
    f₂ (((Equiv.ofInjectiveSubtype f₁ hf₁ Q hQ₁).trans
      (Equiv.ofInjectiveSubtype f₂ hf₂ Q hQ₂).symm) a) = f₁ a :=
  Equiv.ofInjectiveSubtype_symm_apply f₂ hf₂ Q hQ₂ _

/-- **An isomorphism from common values**: the nodes of `G₁` and of `G₂` are given by injective maps
to `W` with the same image, their edges by injective maps to `F` with the same image, the ends of an
edge are the values `σ`, `τ` of its value, and an edge is directed according to its value. -/
def SDIso.ofValues (f₁ : V₁ → W) (hf₁ : Function.Injective f₁) (f₂ : V₂ → W)
    (hf₂ : Function.Injective f₂) (hrv : ∀ w, (∃ a, f₁ a = w) ↔ ∃ b, f₂ b = w)
    (g₁ : E₁ → F) (hg₁ : Function.Injective g₁) (g₂ : E₂ → F) (hg₂ : Function.Injective g₂)
    (hre : ∀ y, (∃ a, g₁ a = y) ↔ ∃ b, g₂ b = y) (σ τ : F → W) (D : F → Prop) (lab : X → W)
    (hs₁ : ∀ e, f₁ (G₁.graph.source e) = σ (g₁ e)) (ht₁ : ∀ e, f₁ (G₁.graph.target e) = τ (g₁ e))
    (hs₂ : ∀ e, f₂ (G₂.graph.source e) = σ (g₂ e)) (ht₂ : ∀ e, f₂ (G₂.graph.target e) = τ (g₂ e))
    (hd₁ : ∀ e, G₁.IsDirected e ↔ D (g₁ e)) (hd₂ : ∀ e, G₂.IsDirected e ↔ D (g₂ e))
    (hl₁ : ∀ x, f₁ (G₁.leaf x) = lab x) (hl₂ : ∀ x, f₂ (G₂.leaf x) = lab x) : SDIso G₁ G₂ where
  vert := (Equiv.ofInjectiveSubtype f₁ hf₁ (fun w => ∃ b, f₂ b = w) fun w => (hrv w).symm).trans
    (Equiv.ofInjectiveSubtype f₂ hf₂ (fun w => ∃ b, f₂ b = w) fun _ => Iff.rfl).symm
  edge := (Equiv.ofInjectiveSubtype g₁ hg₁ (fun y => ∃ b, g₂ b = y) fun y => (hre y).symm).trans
    (Equiv.ofInjectiveSubtype g₂ hg₂ (fun y => ∃ b, g₂ b = y) fun _ => Iff.rfl).symm
  isDirected_iff e := by
    rw [hd₂, hd₁, ofInjectiveSubtype_trans_symm_apply g₁ hg₁ g₂ hg₂]
  joins e := Or.inl
    ⟨hf₂ (by rw [hs₂, ofInjectiveSubtype_trans_symm_apply g₁ hg₁ g₂ hg₂,
      ofInjectiveSubtype_trans_symm_apply f₁ hf₁ f₂ hf₂, hs₁]),
    hf₂ (by rw [ht₂, ofInjectiveSubtype_trans_symm_apply g₁ hg₁ g₂ hg₂,
      ofInjectiveSubtype_trans_symm_apply f₁ hf₁ f₂ hf₂, ht₁])⟩
  directed e _ :=
    ⟨hf₂ (by rw [hs₂, ofInjectiveSubtype_trans_symm_apply g₁ hg₁ g₂ hg₂,
      ofInjectiveSubtype_trans_symm_apply f₁ hf₁ f₂ hf₂, hs₁]),
    hf₂ (by rw [ht₂, ofInjectiveSubtype_trans_symm_apply g₁ hg₁ g₂ hg₂,
      ofInjectiveSubtype_trans_symm_apply f₁ hf₁ f₂ hf₂, ht₁])⟩
  leaf x := hf₂ (by rw [ofInjectiveSubtype_trans_symm_apply f₁ hf₁ f₂ hf₂, hl₁, hl₂])

end OfValues

/-! ### Below the LSA of `Z`: the network below the LSA and the ancestral network -/

section Below

variable {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {Z : Set X} (hZ : Z.Nontrivial)

/-- The arcs out of a node below `LSA(Z)` in the network below the LSA: its arcs above a taxon of
`Z`. -/
theorem lsaNetwork_outdegree (v : N.belowVertices (lsa hN.1 Z hZ.nonempty) Z) :
    (lsaNetwork hN.1 Z hZ.nonempty).graph.outdegree v =
      {e | N.graph.source e = v.1 ∧ e ∈ N.ancestralArcs Z}.ncard := by
  refine Set.ncard_congr' ?_
  exact
    { toFun := fun e => ⟨e.1.1, congrArg Subtype.val e.2, e.1.2.2⟩
      invFun := fun f => ⟨⟨f.1, by rw [show N.graph.source f.1 = v.1 from f.2.1]; exact v.2.1, f.2.2⟩,
        Subtype.ext f.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Below `LSA(Z)`, the chain nodes of the network below the LSA are those of the ancestral network
on `Z`.** -/
theorem lsaNetwork_isChainVertex_iff (v : N.belowVertices (lsa hN.1 Z hZ.nonempty) Z) :
    (lsaNetwork hN.1 Z hZ.nonempty).IsChainVertex v ↔ ChainZ hN.1 hZ.nonempty v.1 := by
  have := hN.1.finite_arcs
  rw [chainZ_iff hN hZ.nonempty v.2.2]
  unfold IsChainVertex
  rw [lsaNetwork_outdegree hN hZ]
  by_cases hv : v.1 = lsa hN.1 Z hZ.nonempty
  · have h0 : (lsaNetwork hN.1 Z hZ.nonempty).graph.indegree v = 0 := by
      have : v = (lsaNetwork hN.1 Z hZ.nonempty).root := Subtype.ext hv
      rw [this]
      exact (lsaNetwork_isPhylogenetic hN.1 hZ).root_indegree
    rw [h0, hv, lsa_outdegree_ancestral hN.1 hN.2 hZ]
    simp
  · have h : (lsaNetwork hN.1 Z hZ.nonempty).graph.indegree v = N.graph.indegree v.1 :=
      belowNetwork_indegree hN.1 (lsa_spec hN.1 Z hZ.nonempty).1 v hv
    rw [h]

/-- **Below `LSA(Z)`, the chains of the network below the LSA end where those of the ancestral network
on `Z` end.** -/
theorem lsaNetwork_chainEnd_val (t : N.belowVertices (lsa hN.1 Z hZ.nonempty) Z) :
    (chainEnd (lsaNetwork_isPhylogenetic hN.1 hZ) t).1 = chainEndZ hN.1 hZ.nonempty t.1 := by
  have hL := lsaNetwork_isPhylogenetic hN.1 hZ
  have hA := N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty
  rw [chainEndZ_of_mem hN.1 hZ.nonempty t.2.2]
  -- a chain of the network below the LSA is a chain of the ancestral network
  have hlift : ∀ a b, (lsaNetwork hN.1 Z hZ.nonempty).ChainReach a b →
      (N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).ChainReach ⟨a.1, a.2.2⟩ ⟨b.1, b.2.2⟩ := by
    intro a b h
    induction h with
    | refl => exact .refl
    | @tail b c _ hbc ih =>
      refine ih.tail ⟨?_, ?_⟩
      · obtain ⟨_, h⟩ := (lsaNetwork_isChainVertex_iff hN hZ b).mp hbc.1
        exact h
      · exact (N.ancestralGraph_adj_iff Z _ _).mpr ((belowNetwork_adj_iff).mp hbc.2)
  have hw := chainReach_chainEnd hL t
  have hnw := not_isChainVertex_chainEnd hL t
  have hnw' : ¬ (N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).IsChainVertex
      ⟨(chainEnd hL t).1, (chainEnd hL t).2.2⟩ := fun h =>
    hnw ((lsaNetwork_isChainVertex_iff hN hZ _).mpr ⟨_, h⟩)
  rw [chainEnd_eq_of_chainReach hA (hlift _ _ hw) hnw']

end Below

/-! ### `(N⁺_Z)⁻` and `(N⊕_Z)⁻` -/

section Induced

variable {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) {Z : Set X} (hZ : Z.Nontrivial)

/-- The arcs of `N⁺_Z` out of nodes below its LSA are the arcs of `N` below `LSA(Z)` above a taxon of
`Z` whose source is not a chain node. -/
theorem mem_range_valCE_below (f : E) :
    (∃ e : {e : _ // (inducedRooted N hN.1 Z hZ.nonempty).graph.Reaches
        (lsa (inducedRooted_isBinaryRootedNetwork hN hZ).1 Set.univ
          (@Set.univ_nonempty _ hZ.coe_sort.to_nonempty))
        ((inducedRooted N hN.1 Z hZ.nonempty).graph.source e)},
        valCE hN hZ (Subtype.val : _ → {e : N.AncestralArc Z //
          ¬ (N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).IsChainVertex
            ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).graph.source e)}) e.1 = f) ↔
      N.graph.Reaches (lsa hN.1 Z hZ.nonempty) (N.graph.source f) ∧ f ∈ N.ancestralArcs Z ∧
        ¬ ChainZ hN.1 hZ.nonempty (N.graph.source f) := by
  have hK : IsContraction ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).suppress
      (N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty)) (inducedRooted N hN.1 Z hZ.nonempty)
      Subtype.val Subtype.val :=
    isContraction_contractRoot _ _
  have hC := inducedRooted_isBinaryRootedNetwork hN hZ
  have hl := valC_lsa hN hZ hC Subtype.val Subtype.val hK
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨hf, hnc⟩ := (mem_range_valSE hN.1 hZ.nonempty _).mp ⟨_, rfl⟩
    refine ⟨?_, hf, hnc⟩
    rw [← hl, ← valC_source hN hZ Subtype.val Subtype.val hK]
    exact (valC_reaches_iff hN hZ Subtype.val Subtype.val hK _ _).mp e.2
  · rintro ⟨hmf, hf, hnc⟩
    obtain ⟨a, rfl⟩ := (mem_range_valSE hN.1 hZ.nonempty f).mpr ⟨hf, hnc⟩
    obtain ⟨e, rfl⟩ := (hK.range_e a).mpr fun ⟨hs, h1⟩ => by
      -- the root of `N` is then `LSA(Z)`, of outdegree two in the ancestral network
      have hsr : N.graph.source (valSE hN.1 hZ.nonempty a) = N.root :=
        (valS_source hN.1 hZ.nonempty a).symm.trans (hs ▸ valS_root hN.1 hZ.nonempty)
      have hmr : lsa hN.1 Z hZ.nonempty = N.root :=
        eq_of_reaches_of_reaches hN.1.acyclic (hsr ▸ hmf) (hN.1.root_reaches _)
      rw [suppress_outdegree, ancestral_outdegree hN.1 hZ.nonempty] at h1
      change ({e | N.graph.source e = N.root ∧ e ∈ N.ancestralArcs Z} : Set E).ncard = 1 at h1
      rw [← hmr, lsa_outdegree_ancestral hN.1 hN.2 hZ] at h1
      exact absurd h1 (by norm_num)
    have : Nonempty Z := hZ.coe_sort.to_nonempty
    refine ⟨⟨e, (valC_reaches_iff hN hZ Subtype.val Subtype.val hK _ _).mpr ?_⟩, rfl⟩
    rw [hl, valC_source hN hZ Subtype.val Subtype.val hK]
    exact hmf

/-- The induced LSA network `N⊕_Z` is rooted at the LSA of its taxa. -/
theorem lsa_inducedNetwork :
    lsa (inducedLSA_isBinaryRootedNetwork hN hZ).1 Set.univ
        (@Set.univ_nonempty _ hZ.coe_sort.to_nonempty) =
      (inducedNetwork hN.1 Z hZ).root :=
  IsLeastStableAncestor.unique (N := inducedNetwork hN.1 Z hZ) (inducedLSA_isBinaryRootedNetwork hN hZ).1
    (lsa_spec _ _ _) (inducedNetwork_isLSANetwork hN.1 hZ)

/-- A node of `N` strictly below `LSA(Z)` is not the root, when `LSA(Z)` has two arcs above taxa of
`Z`: the suppressed ancestral network keeps the root, and its outdegree is not one. -/
theorem not_root_outdegree_one {v : V} (hv : N.graph.Reaches (lsa hN.1 Z hZ.nonempty) v) :
    ¬ (v = N.root ∧ ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).suppress
      (N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty)).graph.outdegree
        ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).suppress
          (N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty)).root = 1) := by
  rintro ⟨rfl, h1⟩
  have hmr : lsa hN.1 Z hZ.nonempty = N.root :=
    eq_of_reaches_of_reaches hN.1.acyclic hv (hN.1.root_reaches _)
  rw [suppress_outdegree, ancestral_outdegree hN.1 hZ.nonempty] at h1
  change ({e | N.graph.source e = N.root ∧ e ∈ N.ancestralArcs Z} : Set E).ncard = 1 at h1
  rw [← hmr, lsa_outdegree_ancestral hN.1 hN.2 hZ] at h1
  exact absurd h1 (by norm_num)

/-- **`N⊕_Z` is the part of `N⁺_Z` below its LSA**, as semidirected networks with their tree edges
undirected: both are, below `LSA(Z)`, the nodes and arcs of `N` above taxa of `Z` with the nodes of
indegree and outdegree one suppressed. -/
def belowLSA_inducedRooted_sdIso :
    SDIso (Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).belowLSA.toSD
      (Model.ofRooted (inducedNetwork hN.1 Z hZ)).belowLSA.toSD :=
  have hK : IsContraction ((N.ancestralNetwork Z hZ.nonempty hN.1.root_reaches).suppress
      (N.ancestralNetwork_isPhylogenetic hN.1 Z hZ.nonempty)) (inducedRooted N hN.1 Z hZ.nonempty)
      Subtype.val Subtype.val :=
    isContraction_contractRoot _ _
  have hC := inducedRooted_isBinaryRootedNetwork hN hZ
  have hD := inducedLSA_isBinaryRootedNetwork hN hZ
  have : Nontrivial Z := hZ.coe_sort
  have hl := valC_lsa hN hZ hC Subtype.val Subtype.val hK
  have hL := lsaNetwork_isPhylogenetic hN.1 hZ
  have hCb := (Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).isBinaryNetwork_iff.mpr hC
  have hDb := (Model.ofRooted (inducedNetwork hN.1 Z hZ)).isBinaryNetwork_iff.mpr hD
  -- the values in `N`
  have hreachC : ∀ c, (inducedRooted N hN.1 Z hZ.nonempty).graph.Reaches
      (lsa hC.1 Set.univ (@Set.univ_nonempty _ hZ.coe_sort.to_nonempty)) c ↔
      N.graph.Reaches (lsa hN.1 Z hZ.nonempty) (valC hN hZ Subtype.val c) := fun c => by
    rw [← hl]
    exact valC_reaches_iff hN hZ Subtype.val Subtype.val hK _ _
  have hrootD : ∀ d, (inducedNetwork hN.1 Z hZ).graph.Reaches
      (lsa hD.1 Set.univ (@Set.univ_nonempty _ hZ.coe_sort.to_nonempty)) d := fun d => by
    rw [lsa_inducedNetwork hN hZ]
    exact hD.1.root_reaches d
  SDIso.ofValues
    (fun c => valC hN hZ Subtype.val c.1) (fun a b h => Subtype.ext
      (valC_injective hN hZ Subtype.val Subtype.val hK h))
    (fun d => d.1.1.1) (fun a b h => Subtype.ext (Subtype.ext (Subtype.ext h)))
    (fun v => by
      constructor
      · rintro ⟨c, rfl⟩
        have hr := (hreachC c.1).mp (((Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).mem_belowLSA_iff hC c.1).mp c.2)
        obtain ⟨hv, hnc, -⟩ := (mem_range_valC hN hZ Subtype.val Subtype.val hK _).mp ⟨_, rfl⟩
        exact ⟨⟨⟨⟨_, hr, hv⟩, fun h => hnc ((lsaNetwork_isChainVertex_iff hN hZ _).mp h)⟩,
          ((Model.ofRooted (inducedNetwork hN.1 Z hZ)).mem_belowLSA_iff hD _).mpr (hrootD _)⟩, rfl⟩
      · rintro ⟨d, rfl⟩
        obtain ⟨hr, hv⟩ := d.1.1.2
        have hnc : ¬ ChainZ hN.1 hZ.nonempty d.1.1.1 := fun h =>
          d.1.2 ((lsaNetwork_isChainVertex_iff hN hZ _).mpr h)
        obtain ⟨c, hc⟩ := (mem_range_valC hN hZ Subtype.val Subtype.val hK _).mpr
          ⟨hv, hnc, not_root_outdegree_one hN hZ hr⟩
        exact ⟨⟨c, ((Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).mem_belowLSA_iff hC c).mpr ((hreachC c).mpr (hc ▸ hr))⟩, hc⟩)
    (fun e => valCE hN hZ Subtype.val e.1) (fun a b h => Subtype.ext
      (valCE_injective hN hZ Subtype.val Subtype.val hK h))
    (fun e => e.1.1.1) (fun a b h => Subtype.ext (Subtype.ext (Subtype.ext h)))
    (fun f => by
      have key := mem_range_valCE_below hN hZ f
      constructor
      · rintro ⟨e, rfl⟩
        have hr := ((Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).reaches_lsaL_source_iff hC e.1).mp e.2
        obtain ⟨hmf, hf, hnc⟩ := key.mp ⟨⟨e.1, hr⟩, rfl⟩
        exact ⟨⟨⟨⟨_, hmf, hf⟩, fun h => hnc ((lsaNetwork_isChainVertex_iff hN hZ _).mp h)⟩,
          ((Model.ofRooted (inducedNetwork hN.1 Z hZ)).reaches_lsaL_source_iff hD _).mpr (hrootD _)⟩, rfl⟩
      · rintro ⟨e, rfl⟩
        obtain ⟨hmf, hf⟩ := e.1.1.2
        have hnc : ¬ ChainZ hN.1 hZ.nonempty (N.graph.source e.1.1.1) := fun h =>
          e.1.2 ((lsaNetwork_isChainVertex_iff hN hZ _).mpr h)
        obtain ⟨⟨e', he'⟩, he⟩ := key.mpr ⟨hmf, hf, hnc⟩
        exact ⟨⟨e', ((Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).reaches_lsaL_source_iff hC e').mpr he'⟩, he⟩)
    N.graph.source (fun f => chainEndZ hN.1 hZ.nonempty (N.graph.target f))
    (fun f => 2 ≤ N.graph.indegree (chainEndZ hN.1 hZ.nonempty (N.graph.target f)))
    (fun z => N.leaf z)
    (fun e => valC_source hN hZ Subtype.val Subtype.val hK e.1)
    (fun e => valC_target hN hZ Subtype.val Subtype.val hK e.1)
    (fun e => rfl)
    (fun e => lsaNetwork_chainEnd_val hN hZ _)
    (fun e => by
      change (Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).IsHybridEdge e.1 ↔ _
      rw [(Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).isHybridEdge_iff hCb]
      exact isHybridArc_iff_valC hN hZ hC Subtype.val Subtype.val hK e.1)
    (fun e => by
      change (Model.ofRooted (inducedNetwork hN.1 Z hZ)).IsHybridEdge e.1 ↔ _
      rw [(Model.ofRooted (inducedNetwork hN.1 Z hZ)).isHybridEdge_iff hDb]
      change 2 ≤ (inducedNetwork hN.1 Z hZ).graph.indegree
        ((inducedNetwork hN.1 Z hZ).graph.target e.1) ↔ _
      have h₁ : (inducedNetwork hN.1 Z hZ).graph.indegree
          ((inducedNetwork hN.1 Z hZ).graph.target e.1) =
          (lsaNetwork hN.1 Z hZ.nonempty).graph.indegree
            (chainEnd hL ((lsaNetwork hN.1 Z hZ.nonempty).graph.target e.1.1)) :=
        suppress_indegree hL _
      have hne : (chainEnd hL ((lsaNetwork hN.1 Z hZ.nonempty).graph.target e.1.1)).1 ≠
          lsa hN.1 Z hZ.nonempty := by
        rw [lsaNetwork_chainEnd_val hN hZ]
        intro h
        change chainEndZ hN.1 hZ.nonempty (N.graph.target e.1.1.1) = _ at h
        have h₂ := reaches_chainEndZ hN.1 hZ.nonempty (v := N.graph.target e.1.1.1)
        rw [h] at h₂
        exact not_reaches_target_source hN.1.acyclic _ (h₂.trans e.1.1.2.1)
      have h₃ : (lsaNetwork hN.1 Z hZ.nonempty).graph.indegree
          (chainEnd hL ((lsaNetwork hN.1 Z hZ.nonempty).graph.target e.1.1)) =
          N.graph.indegree (chainEnd hL ((lsaNetwork hN.1 Z hZ.nonempty).graph.target e.1.1)).1 :=
        belowNetwork_indegree hN.1 (lsa_spec hN.1 Z hZ.nonempty).1 _ hne
      rw [h₁, h₃, lsaNetwork_chainEnd_val hN hZ]
      rfl)
    (fun z => valC_leaf hN hZ Subtype.val Subtype.val hK z)
    (fun z => rfl)

/-- **`(N⁺_Z)⁻` and `(N⊕_Z)⁻` are isomorphic.** -/
theorem nonempty_sdIso_unrooted_inducedRooted :
    Nonempty (SDIso (unrooted (inducedRooted N hN.1 Z hZ.nonempty)
      (inducedRooted_isBinaryRootedNetwork hN hZ) hZ.coe_sort)
      (unrooted (inducedNetwork hN.1 Z hZ) (inducedLSA_isBinaryRootedNetwork hN hZ) hZ.coe_sort)) := by
  have : Nontrivial Z := hZ.coe_sort
  have := hN.1.finite_arcs
  obtain ⟨uC⟩ := (Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).nonempty_sdIso_unrooted
    (inducedRooted_isBinaryRootedNetwork hN hZ)
  obtain ⟨uD⟩ := (Model.ofRooted (inducedNetwork hN.1 Z hZ)).nonempty_sdIso_unrooted
    (inducedLSA_isBinaryRootedNetwork hN hZ)
  have := (inducedRooted_isBinaryRootedNetwork hN hZ).1.finite_arcs
  have := (inducedLSA_isBinaryRootedNetwork hN hZ).1.finite_arcs
  exact ⟨uC.symm.trans
    ((((Model.ofRooted (inducedRooted N hN.1 Z hZ.nonempty)).belowLSA.suppressIso ∅).trans
      (((belowLSA_inducedRooted_sdIso hN hZ).suppressExcept fun _ => Iff.rfl).trans
        ((Model.ofRooted (inducedNetwork hN.1 Z hZ)).belowLSA.suppressIso ∅).symm)).trans uD)⟩

end Induced

/-! ### The right side of Theorem 3 -/

/-- **The right side of Theorem 3**: `(N⁻)_s`, the Challenge's induced unrooted network, has a
4-cycle exactly when `Q⁻_s` does (`HasFourCycle`). By Proposition 1, `(N⁻)_s ≅ (N⁺_s)⁻ ≅ (N⊕_s)⁻ = Q⁻_s`;
a cycle of `Q⁻_s` has a hybrid node (Lemma 3), so it is an `n_k`-cycle, and `inducesCycleType_iff`
relates the cycles of `Q⁻_s` to those of `Q⊕_s`. -/
theorem Model.Network.exists_fourCycle_induced_iff [Fintype V] [Fintype E] [Fintype X]
    (N : Model.Network V E X) (hN : N.IsBinaryNetwork) (h1 : N.graph.IsLevelOne) {θ : Model.Params E}
    (hθ : N.IsMetric θ) (s : Finset X) (hs : s.card = 4) :
    (∃ C, (N.unrooted.induced (s : Set X)).graph.IsCycle C ∧ C.ncard = 4) ↔
      HasFourCycle N.toRooted (N.isBinaryNetwork_iff.mp hN) s hs := by
  classical
  have hb := N.isBinaryNetwork_iff.mp hN
  have hZ : (s : Set X).Nontrivial := Finset.one_lt_card_iff_nontrivial.mp (by omega)
  have hX : Nontrivial X := by
    obtain ⟨x, -, y, -, hxy⟩ := hZ
    exact ⟨⟨x, y, hxy⟩⟩
  have e1 : (∃ C, (N.unrooted.induced (s : Set X)).graph.IsCycle C ∧ C.ncard = 4) ↔
      ∃ C, IsCycle (N.unrooted.induced (s : Set X)).toSD.graph C ∧ C.ncard = 4 := by
    simp only [Model.Digraph.isCycle_iff]
    rfl
  obtain ⟨u⟩ := N.nonempty_sdIso_unrooted hb
  obtain ⟨p1⟩ := proposition1 hb hX hZ
  obtain ⟨p2⟩ := nonempty_sdIso_unrooted_inducedRooted hb hZ
  rw [e1, ((((N.unrooted.inducedIso (s : Set X)).trans (u.inducedUnrooted (s : Set X))).trans
    p1).trans p2).exists_isCycle_ncard_iff 4]
  have hQ := isLSAQuartet_quartetLSA hb ((N.graph.isLevelOne_iff).mp h1) ((N.isMetric_iff hN θ).mp hθ) hs
  have := hQ.binary.1.finite_arcs
  unfold HasFourCycle
  constructor
  · rintro ⟨C, hC, h4⟩
    obtain ⟨⟨v, ⟨hv, h₁, h₂, hne, hd₁, hd₂, ht₁, ht₂⟩, -⟩, hin, -⟩ :=
      lemma3_unrooted hQ.binary hQ.levelOne hQ.nontrivial hC
    obtain ⟨C', v', h'⟩ := (inducesCycleType_iff hQ 4 _).mpr ⟨C, hC, h4, v,
      ⟨h₁, hin v hv h₁ hd₁ ht₁, h₂, hin v hv h₂ hd₂ ht₂, hne, hd₁, hd₂, ht₁, ht₂⟩, rfl⟩
    exact ⟨C', v', _, h'⟩
  · rintro ⟨C, v, k, h⟩
    obtain ⟨C', hC', h4, -⟩ := (inducesCycleType_iff hQ 4 k).mp ⟨C, v, h⟩
    exact ⟨C', hC', h4⟩

end Banos2019
