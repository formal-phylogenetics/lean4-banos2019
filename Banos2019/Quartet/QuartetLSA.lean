module

public import Banos2019.Network.Induced
public import Banos2019.Network.Suppress

/-!
# `Q⊕_s` is a metric binary level-1 LSA network

The facts that make `Q⊕_s = quartetLSA N hN.1 s hs`, with the parameters it inherits from `N`, an
LSA quartet network (`Banos2019.Quartet.Reduction`).

* `inducedNetwork_isLSANetwork`: the root of the induced network is the LSA of its taxa; a stable
  ancestor of the suppressed network, or of the part below the LSA, is one of the network
  (`isStableAncestor_of_suppress`, `isStableAncestor_of_lsaNetwork`).
* `quartetLSAMetric`: the parameters of `Q⊕_s` inherited from `N`; `quartetLSA_isMetricNetwork`,
  `quartetLSA_isLSANetwork`, `quartetLSA_isLevelOne`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-- A path avoiding a kept vertex `w` gives a path of the suppressed network avoiding `w`, from the
end of the chain of its first vertex. -/
theorem reflTransGen_avoiding_suppress {M : RootedNetwork V E X} (hM : M.IsPhylogenetic)
    (w : {v // ¬ M.IsChainVertex v}) {a b : V} (hb : ¬ M.IsChainVertex b) (hbw : b ≠ w.1)
    (h : Relation.ReflTransGen (fun x y => M.graph.Adj x y ∧ x ≠ w.1 ∧ y ≠ w.1) a b) :
    Relation.ReflTransGen (fun x y => (M.suppress hM).graph.Adj x y ∧ x ≠ w ∧ y ≠ w)
        ⟨chainEnd hM a, not_isChainVertex_chainEnd hM a⟩ ⟨b, hb⟩ ∧
      chainEnd hM a ≠ w.1 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have he : chainEnd hM b = b := chainEnd_eq_self hM hb
    refine ⟨?_, by rw [he]; exact hbw⟩
    have : (⟨chainEnd hM b, not_isChainVertex_chainEnd hM b⟩ : {v // ¬ M.IsChainVertex v}) =
        ⟨b, hb⟩ := Subtype.ext he
    rw [this]
  | @head a c hac _ ih =>
    obtain ⟨ihp, ihw⟩ := ih
    by_cases ha : M.IsChainVertex a
    · have he : chainEnd hM a = chainEnd hM c := chainEnd_eq_of_adj hM ha hac.1
      have : (⟨chainEnd hM a, not_isChainVertex_chainEnd hM a⟩ : {v // ¬ M.IsChainVertex v}) =
          ⟨chainEnd hM c, not_isChainVertex_chainEnd hM c⟩ := Subtype.ext he
      rw [this, he]
      exact ⟨ihp, ihw⟩
    · have he : chainEnd hM a = a := chainEnd_eq_self hM ha
      have : (⟨chainEnd hM a, not_isChainVertex_chainEnd hM a⟩ : {v // ¬ M.IsChainVertex v}) =
          ⟨a, ha⟩ := Subtype.ext he
      rw [this, he]
      refine ⟨Relation.ReflTransGen.head ⟨?_, fun h => hac.2.1 (congrArg Subtype.val h),
        fun h => ihw (congrArg Subtype.val h)⟩ ihp, hac.2.1⟩
      obtain ⟨f, hfs, hft⟩ := hac.1
      exact ⟨⟨f, hfs ▸ ha⟩, Subtype.ext hfs, Subtype.ext (by
        show chainEnd hM (M.graph.target f) = chainEnd hM c
        rw [hft])⟩

/-- A stable ancestor of the suppressed network is one of the network. -/
theorem isStableAncestor_of_suppress {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) {Y : Set X}
    {w : {v // ¬ M.IsChainVertex v}} (hw : (M.suppress hM).IsStableAncestor Y w) :
    M.IsStableAncestor Y w.1 := by
  intro x hx hp
  obtain ⟨hr, hl, hpath⟩ := hp
  have h := reflTransGen_avoiding_suppress hM w (not_isChainVertex_leaf hM x) hl hpath
  have he : chainEnd hM M.root = M.root := chainEnd_eq_self hM (not_isChainVertex_root hM)
  have : (⟨chainEnd hM M.root, not_isChainVertex_chainEnd hM M.root⟩ :
      {v // ¬ M.IsChainVertex v}) = (M.suppress hM).root := Subtype.ext he
  rw [this] at h
  exact hw x hx ⟨fun e => hr (congrArg Subtype.val e), fun e => hl (congrArg Subtype.val e), h.1⟩

/-- A stable ancestor of the part below the LSA is one of the network. -/
theorem isStableAncestor_of_lsaNetwork {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {Y : Set X}
    (hY : Y.Nonempty) {w : N.belowVertices (lsa hN Y hY) Y}
    (hw : (lsaNetwork hN Y hY).IsStableAncestor Set.univ w) : N.IsStableAncestor Y w.1 := by
  obtain ⟨hst, -⟩ := lsa_spec hN Y hY
  intro x hx hp
  have hs := hp.suffix_of_not_hasPathAvoiding (hst x hx)
  obtain ⟨hlw, hxw, hpath⟩ := hs
  -- lift the path from the LSA to `x` into the part below the LSA
  have hlift : ∀ a, N.graph.Reaches (lsa hN Y hY) a →
      Relation.ReflTransGen (fun u v => N.graph.Adj u v ∧ u ≠ w.1 ∧ v ≠ w.1) a (N.leaf x) →
      ∀ ha : a ∈ N.belowVertices (lsa hN Y hY) Y,
      Relation.ReflTransGen (fun u v => (lsaNetwork hN Y hY).graph.Adj u v ∧ u ≠ w ∧ v ≠ w)
        ⟨a, ha⟩ ((lsaNetwork hN Y hY).leaf ⟨x, hx⟩) := by
    intro a hla hax
    induction hax using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => .refl
    | @head a c hac hcx ih =>
      intro ha
      obtain ⟨⟨f, hfs, hft⟩, haw, hcw⟩ := hac
      have hlc : N.graph.Reaches (lsa hN Y hY) c := hla.tail ⟨f, hfs, hft⟩
      have hcY : c ∈ N.ancestralVertices Y :=
        ⟨x, hx, Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hcx⟩
      have hc : c ∈ N.belowVertices (lsa hN Y hY) Y := ⟨hlc, hcY⟩
      have hf : f ∈ N.belowArcs (lsa hN Y hY) Y :=
        ⟨hfs ▸ hla, by show N.graph.target f ∈ N.ancestralVertices Y; rw [hft]; exact hcY⟩
      refine Relation.ReflTransGen.head ⟨⟨⟨f, hf⟩, Subtype.ext hfs,
        (Subtype.ext hft : (lsaNetwork hN Y hY).graph.target ⟨f, hf⟩ = ⟨c, hc⟩)⟩,
        fun h => haw (congrArg Subtype.val h), fun h => hcw (congrArg Subtype.val h)⟩ (ih hlc hc)
  refine hw ⟨x, hx⟩ (Set.mem_univ _) ⟨fun h => hlw (congrArg Subtype.val h),
    fun h => hxw (congrArg Subtype.val h), ?_⟩
  exact hlift _ .refl hpath (lsa_mem_ancestralVertices hN hY |> fun h => ⟨.refl, h⟩)

/-- **The induced network is an LSA network**: its root is the LSA of its taxa. -/
theorem inducedNetwork_isLSANetwork {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {Y : Set X}
    (hY : Y.Nontrivial) : (inducedNetwork hN Y hY).IsLSANetwork := by
  refine ⟨root_isStableAncestor _ _, fun w hw => ?_⟩
  have hM := lsaNetwork_isPhylogenetic hN hY
  have h₁ := isStableAncestor_of_lsaNetwork hN hY.nonempty (isStableAncestor_of_suppress hM hw)
  have h₂ := (lsa_spec hN Y hY.nonempty).2 _ h₁
  have hw' : w.1.1 = lsa hN Y hY.nonempty :=
    eq_of_reaches_of_reaches hN.acyclic h₂ w.1.2.1
  have : w = (inducedNetwork hN Y hY).root := Subtype.ext (Subtype.ext hw')
  rw [this]
  exact .refl

variable [Fintype V] [Fintype E] [Fintype X]

/-- The parameters of `Q⊕_s` inherited from `N`. -/
abbrev quartetLSAMetric (N : RootedNetwork V E X) (hN : IsBinaryRootedNetwork N) (s : Finset X)
    (hs : #s = 4) (θ : MetricData E) :=
  inducedMetric hN.1 (s : Set X) (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty θ

omit [Fintype V] [Fintype X] in
/-- The parameters that `Q⊕_s` inherits from a metric are a metric: every edge, a chain of edges of
`N`, has positive length. -/
theorem quartetLSA_isMetricNetwork {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    {θ : MetricData E} (hθ : IsMetricNetwork N θ) {s : Finset X} (hs : #s = 4) :
    IsMetricNetwork (quartetLSA N hN.1 s hs) (quartetLSAMetric N hN s hs θ) := by
  refine ⟨isMetric_inducedMetric hN.1 _ hθ.1, fun e => ?_⟩
  simp only [quartetLSAMetric, inducedMetric, belowMetric]
  exact Finset.sum_pos (fun f _ => hθ.2 _) ⟨e.1, Finset.mem_filter.mpr
    ⟨@Finset.mem_univ _ (Fintype.ofFinite _) _, Or.inl rfl⟩⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- `Q⊕_s` is the LSA network of its taxa. -/
theorem quartetLSA_isLSANetwork {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    {s : Finset X} (hs : #s = 4) : (quartetLSA N hN.1 s hs).IsLSANetwork :=
  inducedNetwork_isLSANetwork hN.1 _

omit [Fintype V] [Fintype E] [Fintype X] in
/-- `Q⊕_s` of a level-1 network is level-1: a cycle of the induced network is made of chains of
edges of `N` that form a cycle of `N`, and two cycles sharing a chain share its edges. -/
theorem quartetLSA_isLevelOne {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {s : Finset X} (hs : #s = 4) :
    IsLevelOne (quartetLSA N hN.1 s hs).graph :=
  suppress_isLevelOne _ (IsLevelOne.of_injective h1 Subtype.val Subtype.val Subtype.val_injective
    Subtype.val_injective (fun _ => rfl) (fun _ => rfl))

end Banos2019
