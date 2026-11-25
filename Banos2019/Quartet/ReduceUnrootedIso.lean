module

public import Banos2019.Quartet.ReduceUnrootedKeep
public import Banos2019.Quartet.DeleteHybridUnrooted
public import Banos2019.Quartet.ContractCyclesUnrooted
public import Banos2019.Quartet.DisjointUnrooted
public import Banos2019.Quartet.ReduceSpec
public import Banos2019.Quartet.ContractCompose

/-!
# The unrooted networks of the reduced networks of Section 5, in the terms of `Q⁻`

For a binary level-1 network `Q` whose root is the LSA of its taxa, the unrooted networks of the
networks that Lemmas 7–11 produce are built from `Q⁻` alone, so isomorphic `Q⁻` and `Q̃⁻` give
isomorphic unrooted networks (proof of Proposition 5).

* `nonempty_sdMetricIso_unrootAt_swap`: merging either of two tree arcs at a root of outdegree two
  gives isomorphic metric networks; `nonempty_sdMetricIso_unrootAt_keepRootSD`: with a root of
  outdegree one, `unrootAt M hP e₀` is `keepRootSD M hP`.
* Without a hybrid edge `h` (`Q₁⊕`, `Q₂⊕`): the unrooted network of `reduceNet (deleteArc Q h)` is
  `deleteHybridEdge Q⁻ h` with its nodes of degree two suppressed
  (`nonempty_sdMetricIso_suppress_deleteHybridEdge`). `deleteHybridEdge Q⁻ h` is `unrootAt` of
  `deleteArc Q h` at the arc of `Q` that `Q⁻` merges
  (`nonempty_sdMetricIso_deleteHybridEdge_unrootAt`).
* Contracting a 2-cycle `D` (`Q₀⊕`): the unrooted network of `contractNet Q (· = liftEdges D)` is
  `contractCycles Q⁻ (· = D)` with its nodes of degree two suppressed
  (`nonempty_sdMetricIso_suppress_contractCycles`). When the cycle of `Q` is off the root,
  `contractCycles Q⁻ (· = D)` is `unrootAt` of the contracted network
  (`nonempty_sdMetricIso_contractCycles_unrootAt`); when it passes through the root, it is the
  contracted network with its root kept (`nonempty_sdMetricIso_contractCycles_keepRootSD`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Swap

variable {M : RootedNetwork V E X} (hP : M.IsPhylogenetic) (θ : MetricData E)

/-- **Merging either tree arc at a root of outdegree two** gives isomorphic metric networks: the
merged edge joins the same two nodes, in the other order. -/
theorem nonempty_sdMetricIso_unrootAt_swap {e₀ e₁ : E} (h₀ : M.graph.source e₀ = M.root)
    (h₁ : M.graph.source e₁ = M.root) (h2 : M.graph.outdegree M.root = 2)
    (ht₀ : ¬ M.IsHybridArc e₀) (ht₁ : ¬ M.IsHybridArc e₁) :
    Nonempty (SDMetricIso (unrootAt M hP e₀) (unrootAtMetric M e₀ θ) (unrootAt M hP e₁)
      (unrootAtMetric M e₁ θ)) := by
  have := hP.finite_arcs
  by_cases h01 : e₀ = e₁
  · subst h01
    exact ⟨⟨⟨Equiv.refl _, Equiv.refl _, fun _ => Iff.rfl, fun _ => Or.inl ⟨rfl, rfl⟩,
      fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl⟩, fun _ => rfl, fun _ _ => rfl⟩⟩
  -- the arcs at the root are `e₀` and `e₁`
  have hother : ∀ e, M.graph.source e = M.root → e = e₀ ∨ e = e₁ := by
    intro e he
    by_contra hne
    push Not at hne
    have h3 : ({e₀, e₁, e} : Set E).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨e₀, e₁, e, h01, Ne.symm hne.1, Ne.symm hne.2, rfl⟩
    have hsub : ({e₀, e₁, e} : Set E) ⊆ {f | M.graph.source f = M.root} := by
      rintro f (rfl | rfl | rfl)
      · exact h₀
      · exact h₁
      · exact he
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    unfold DirectedMultigraph.outdegree at h2
    omega
  let σ : {e // e ≠ e₀} ≃ {e // e ≠ e₁} :=
    (Equiv.swap e₀ e₁).subtypeEquiv fun e => by
      rw [Ne, Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  have hσ₁ : ∀ e : {e // e ≠ e₀}, e.1 = e₁ → (σ e).1 = e₀ := fun e he => by
    show Equiv.swap e₀ e₁ e.1 = e₀
    rw [he, Equiv.swap_apply_right]
  have hσ : ∀ e : {e // e ≠ e₀}, e.1 ≠ e₁ → (σ e).1 = e.1 := fun e he =>
    Equiv.swap_apply_of_ne_of_ne e.2 he
  have hsrc : ∀ e : {e // e ≠ e₀}, e.1 ≠ e₁ → M.graph.source e.1 ≠ M.root := fun e he hs =>
    ((hother e.1 hs).elim e.2 he)
  refine ⟨⟨⟨Equiv.refl _, σ, fun e => ?_, fun e => ?_, fun e hd => ?_, fun _ => rfl⟩,
    fun e => ?_, fun e hd => ?_⟩⟩
  · by_cases he : e.1 = e₁
    · change M.IsHybridArc (σ e).1 ↔ M.IsHybridArc e.1
      rw [hσ₁ e he, he]
      exact iff_of_false ht₀ ht₁
    · change M.IsHybridArc (σ e).1 ↔ M.IsHybridArc e.1
      rw [hσ e he]
  · by_cases he : e.1 = e₁
    · right
      refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
      · simp only [unrootAt, hσ₁ e he, h₀, he, ↓reduceDIte, Equiv.refl_apply]
      · simp only [unrootAt, hσ₁ e he, he, h₁, ↓reduceDIte, Equiv.refl_apply]
    · left
      refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
      · simp only [unrootAt, hσ e he, hsrc e he, ↓reduceDIte, Equiv.refl_apply]
      · simp only [unrootAt, hσ e he, Equiv.refl_apply]
  · have he : e.1 ≠ e₁ := fun h' => ht₁ (h' ▸ hd)
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · simp only [unrootAt, hσ e he, hsrc e he, ↓reduceDIte, Equiv.refl_apply]
    · simp only [unrootAt, hσ e he, Equiv.refl_apply]
  · by_cases he : e.1 = e₁
    · simp only [unrootAtMetric, hσ₁ e he, h₀, he, h₁, ↓reduceIte]
      exact add_comm _ _
    · simp only [unrootAtMetric, hσ e he, hsrc e he, ↓reduceIte]
  · have he : e.1 ≠ e₁ := fun h' => ht₁ (h' ▸ hd)
    simp only [unrootAtMetric, hσ e he]

/-- **With a root of outdegree one, suppressing the root removes it with its arc.** -/
theorem nonempty_sdMetricIso_unrootAt_keepRootSD {e₀ : E} (h₀ : M.graph.source e₀ = M.root)
    (h1 : M.graph.outdegree M.root = 1) :
    Nonempty (SDMetricIso (unrootAt M hP e₀) (unrootAtMetric M e₀ θ) (keepRootSD M hP)
      (restrictMetric θ _)) := by
  have := hP.finite_arcs
  obtain ⟨e₁, he₁⟩ := (M.graph.outdegree_eq_one_iff _).mp h1
  have huniq : ∀ e, M.graph.source e = M.root ↔ e = e₀ := fun e =>
    (he₁ e).trans ⟨fun h => h.trans ((he₁ e₀).1 h₀).symm, fun h => h ▸ (he₁ e₀).1 h₀⟩
  have hsrc : ∀ e : {e // e ≠ e₀}, M.graph.source e.1 ≠ M.root := fun e h => e.2 ((huniq _).1 h)
  let vert : {v // v ≠ M.root} ≃ {v // ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)} :=
    Equiv.subtypeEquivRight fun v => by simp [h1]
  let edge : {e // e ≠ e₀} ≃ {e // ¬ (M.graph.source e = M.root ∧ M.graph.outdegree M.root = 1)} :=
    Equiv.subtypeEquivRight fun e => by rw [huniq e]; simp [h1]
  refine ⟨⟨⟨vert, edge, fun e => Iff.rfl, fun e => Or.inl ⟨Subtype.ext ?_, Subtype.ext rfl⟩,
    fun e _ => ⟨Subtype.ext ?_, Subtype.ext rfl⟩, fun _ => rfl⟩, fun e => ?_, fun _ _ => rfl⟩⟩
  · simp [unrootAt, keepRootSD, vert, edge, hsrc e]
  · simp [unrootAt, keepRootSD, vert, edge, hsrc e]
  · simp [unrootAtMetric, restrictMetric, edge, hsrc e]

end Swap

section Delete

variable {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q) (hX : Nontrivial X)

/-- **The unrooted network of `Q₁⊕` is `Q⁻` without the hybrid edge `h`, with its nodes of degree
two suppressed.** -/
theorem nonempty_sdMetricIso_suppress_deleteHybridEdge [Fintype V] [Fintype E] [Fintype X]
    (h1 : IsLevelOne Q.graph) (hlsa : Q.IsLSANetwork) {θ : MetricData E} (hθ : IsMetricNetwork Q θ)
    {h : SemidirectedArc hQ.1 hQ.2 hX} (hh : (semidirected hQ.1 hQ.2 hX).IsDirected h)
    (hP : (deleteArc Q (sdArc hQ.1 hQ.2 hX h)).IsPhylogenetic)
    (hb : IsBinaryRootedNetwork (reduceNet _ hP)) :
    Nonempty (SDMetricIso (suppress (deleteHybridEdge (semidirected hQ.1 hQ.2 hX) h))
      (suppressMetric (deleteHybridEdge (semidirected hQ.1 hQ.2 hX) h)
        (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _))
      (unrooted _ hb hX)
      (unrootedMetric _ hb hX (reduceMetric _ hP
          (deleteArcMetric Q (sdArc hQ.1 hQ.2 hX h) θ)))) := by
  have := hQ.1.finite_arcs
  have hr := lsa_univ_eq_root hQ.1 hX hlsa
  have htwo : ∃ x y : X, x ≠ y := exists_pair_ne X
  set hE := sdArc hQ.1 hQ.2 hX h with hE_def
  set M := deleteArc Q hE
  have hhyb : Q.IsHybridArc hE := (semidirected_isDirected_iff hQ.1 hQ.2 hX h).1 hh
  -- the cycle of the hybrid edge
  have hv2 : Q.graph.indegree (Q.graph.target hE) = 2 :=
    le_antisymm (hQ.indegree_le_two _) hhyb
  obtain ⟨h', hne', hh'⟩ : ∃ h', h' ≠ hE ∧ Q.graph.target h' = Q.graph.target hE := by
    obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 hv2
    have hx : Q.graph.target x = Q.graph.target hE := (Set.ext_iff.1 hs x).2 (Or.inl rfl)
    have hy : Q.graph.target y = Q.graph.target hE := (Set.ext_iff.1 hs y).2 (Or.inr rfl)
    by_cases hxh : x = hE
    · exact ⟨y, fun hyh => hxy (hxh.trans hyh.symm), hy⟩
    · exact ⟨x, hxh, hx⟩
  obtain ⟨C, hC, hEC, -⟩ := exists_isCycle_of_target_eq hQ h1 hne'.symm hh'.symm
  have hIC : InducesCycleType Q C (Q.graph.target hE)
      (C.ncard - (if Q.root ∈ cycleNodes Q.graph C then 1 else 0))
      {x | Q.graph.Reaches (Q.graph.target hE) (Q.leaf x)}.ncard :=
    ⟨hC, ⟨hE, hEC, Or.inr rfl⟩, hv2, rfl, rfl⟩
  have hn2 := (add_le_of_inducesCycleType hQ h1 hlsa hIC).2.2
  have hM := isReducible_deleteArc hQ h1 hIC rfl hθ htwo hn2
  have hl : (reduceNet M hM.phylo).IsLSANetwork := hM.isLSANetwork fun D w k' hD => by
    obtain ⟨D', w', -, hD', -⟩ := (deleteArc_exists_inducesCycleType_iff hQ h1 hIC rfl 1 k' _).1
      ⟨D, w, hD, rfl⟩
    have := (add_le_of_inducesCycleType hQ h1 hlsa hD').2.2
    omega
  have hθM : M.IsNormalized (deleteArcMetric Q hE θ) := hM.metric.isNormalized
  -- the arc of `Q` that `Q⁻` merges
  set er : {e // e ≠ hE} := ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩
  have her : M.graph.source er = M.root := (sdRootArc_spec hQ.1 hQ.2 hX).1.trans hr
  have hter : ¬ M.IsHybridArc er := by
    have hin : M.graph.indegree (Q.graph.target er.1) +
        (if Q.graph.target hE = Q.graph.target er.1 then 1 else 0) =
          Q.graph.indegree (Q.graph.target er.1) := deleteArc_indegree _
    have ht : Q.graph.indegree (Q.graph.target er.1) = 1 := (sdRootArc_spec hQ.1 hQ.2 hX).2
    have hle : M.graph.indegree (Q.graph.target er.1) ≤ 1 := by
      split_ifs at hin <;> omega
    unfold IsHybridArc
    change ¬ 2 ≤ M.graph.indegree (Q.graph.target er.1)
    omega
  obtain ⟨ιS⟩ := nonempty_sdMetricIso_deleteHybridEdge_unrootAt hQ hX hr θ hh hP
  rcases hM.root with h1r | h2r
  · -- the root of `deleteArc Q h` has outdegree one: its child is the top node
    have hc : ∀ e, M.graph.source e = M.root → M.graph.outdegree M.root = 1 →
        ¬ M.IsChainVertex (M.graph.target e) := by
      intro e he _ hch
      obtain ⟨e₁, he₁⟩ := (M.graph.outdegree_eq_one_iff _).mp h1r
      have hee : e = er := ((he₁ e).1 he).trans ((he₁ er).1 her).symm
      rw [hee] at hch
      have hcr : Q.graph.target er.1 ≠ Q.root := hQ.1.target_ne_root _
      have hinQ : Q.graph.indegree (Q.graph.target er.1) = 1 := (sdRootArc_spec hQ.1 hQ.2 hX).2
      -- the deleted arc leaves the root
      have hsE : Q.graph.source hE = Q.root := by
        have hout : M.graph.outdegree Q.root + (if Q.graph.source hE = Q.root then 1 else 0) =
            Q.graph.outdegree Q.root := deleteArc_outdegree _
        have hM1 : M.graph.outdegree Q.root = 1 := h1r
        rw [hQ.2.1, hM1] at hout
        split_ifs at hout with hs
        · exact hs
        · omega
      have houtM : M.graph.outdegree (Q.graph.target er.1) =
          Q.graph.outdegree (Q.graph.target er.1) := by
        have hout : M.graph.outdegree (Q.graph.target er.1) +
            (if Q.graph.source hE = Q.graph.target er.1 then 1 else 0) =
              Q.graph.outdegree (Q.graph.target er.1) := deleteArc_outdegree _
        rw [ite_eq_right (fun h' => hcr (h'.symm.trans hsE))] at hout
        omega
      have hv : Q.graph.target hE ≠ Q.graph.target er.1 := fun h' => by
        rw [h', hinQ] at hv2
        omega
      -- the child of the root is not a leaf: the target of `h` is reached through it
      have h0 : Q.graph.outdegree (Q.graph.target er.1) ≠ 0 := by
        intro h0
        rcases Relation.ReflTransGen.cases_head (hP.root_reaches (Q.graph.target hE)) with
          h' | ⟨b, ⟨f, hfs, hft⟩, hb⟩
        · have h0r := hQ.1.root_indegree
          change Q.root = Q.graph.target hE at h'
          rw [h', hv2] at h0r
          omega
        · have hf : f = er := ((he₁ f).1 hfs).trans ((he₁ er).1 her).symm
          rw [hf] at hft
          rw [← hft] at hb
          rcases Relation.ReflTransGen.cases_head hb with h'' | ⟨b', ⟨f', hfs', -⟩, -⟩
          · exact hv h''.symm
          · have hne0 : M.graph.outdegree (Q.graph.target er.1) ≠ 0 := fun h' =>
              (M.graph.outdegree_eq_zero_iff _).1 h' f' hfs'
            exact hne0 (houtM.trans h0)
      have h3 := hQ.2.2 _ hcr h0
      have hch2 : M.graph.outdegree (Q.graph.target er.1) = 1 := hch.2
      omega
    obtain ⟨ιK⟩ := nonempty_sdMetricIso_unrootAt_keepRootSD hP (deleteArcMetric Q hE θ) her h1r
    obtain ⟨ι₁⟩ := nonempty_sdMetricIso_suppress_keepRootSD hM hb hX hl hc
    exact ⟨(ιS.trans ιK).suppress.trans ι₁⟩
  · -- the root has outdegree two: merging either arc at the root
    have he₀ := source_reduceRootArc hM hb hX h2r hl
    have ht₀ : ¬ M.IsHybridArc (reduceRootArc hM hb hX) :=
      not_isHybridArc_of_isOnChain_reduceRootArc hM hb hX (Or.inl rfl)
    obtain ⟨ιU⟩ := nonempty_sdMetricIso_unrootAt_swap hP (deleteArcMetric Q hE θ) her he₀ h2r hter
      ht₀
    obtain ⟨ι₁⟩ := nonempty_sdMetricIso_suppress_unrootAt hM hb hX h2r hl hθM
    exact ⟨(ιS.trans ιU).suppress.trans ι₁⟩

end Delete

section Contract

variable [Fintype V] [Fintype E] {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q)
  (h1 : IsLevelOne Q.graph) (hX : Nontrivial X)

/-- **The unrooted network of `Q₀⊕` is `Q⁻` with the 2-cycle `D` contracted and its nodes of degree
two suppressed.** -/
theorem nonempty_sdMetricIso_suppress_contractCycles [Fintype X] (hlsa : Q.IsLSANetwork)
    (hX4 : Fintype.card X = 4) {θ : MetricData E} (hθ : IsMetricNetwork Q θ)
    {D : Set (SemidirectedArc hQ.1 hQ.2 hX)} (hD : IsCycle (semidirected hQ.1 hQ.2 hX).graph D)
    (hD2 : D.ncard = 2)
    (hb : IsBinaryRootedNetwork (contractNet Q hQ h1 (· = liftEdges hQ.1 hQ.2 hX D))) :
    Nonempty (SDMetricIso (suppress (contractCycles (semidirected hQ.1 hQ.2 hX) (· = D)))
      (suppressMetric (contractCycles (semidirected hQ.1 hQ.2 hX) (· = D))
        (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _))
      (unrooted _ hb hX)
      (unrootedMetric _ hb hX (contractNetMetric Q hQ h1 (· = liftEdges hQ.1 hQ.2 hX D) θ))) := by
  have := hQ.1.finite_arcs
  have hr := lsa_univ_eq_root hQ.1 hX hlsa
  have htwo : ∃ x y : X, x ≠ y := exists_pair_ne X
  set C := liftEdges hQ.1 hQ.2 hX D with hC_def
  have hn : ∀ C', IsCycle Q.graph C' → C' = C →
      C'.ncard - (if Q.root ∈ cycleNodes Q.graph C' then 1 else 0) = 2 := by
    rintro C' - rfl
    have h := card_cycleNodesOffRoot_liftEdges hQ.1 hQ.2 hX hr hD
    rw [card_cycleNodesOffRoot (isCycle_liftEdges _ _ _ hD), hD2] at h
    exact h
  have hM := isReducible_contractSet hQ h1 hθ htwo hn
  obtain ⟨-, -, hl, -⟩ := contractNet_spec hQ h1 hlsa hX4 hθ hn
  have hθM := hM.metric.isNormalized
  have h2 : (contractRooted Q (· = C)).graph.outdegree (contractRooted Q (· = C)).root = 2 :=
    contractSet_outdegree_root hQ h1 hn
  by_cases hρ : Q.root ∈ cycleNodes Q.graph C
  · -- the cycle passes through the root: the node of the contracted cycle is the root
    obtain ⟨ιS⟩ := nonempty_sdMetricIso_contractCycles_keepRootSD hQ h1 hX hr θ hD hD2 hρ
    obtain ⟨ι₁⟩ := nonempty_sdMetricIso_suppress_keepRootSD hM hb hX hl
      fun _ _ h1' => absurd (h2.symm.trans h1') (by norm_num)
    exact ⟨ιS.suppress.trans ι₁⟩
  · -- the cycle avoids the root: merging either arc at the root
    obtain ⟨ιS⟩ := nonempty_sdMetricIso_contractCycles_unrootAt hQ h1 hX hr θ hD hρ
    set er : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'} :=
      ⟨sdRootArc hQ.1 hQ.2 hX, sdRootArc_notMem_of_root_notMem hQ hX hr hρ⟩
    have her : (contractRooted Q (· = C)).graph.source er = (contractRooted Q (· = C)).root := by
      change Quot.mk _ (Q.graph.source (sdRootArc hQ.1 hQ.2 hX)) = Quot.mk _ Q.root
      rw [(sdRootArc_spec hQ.1 hQ.2 hX).1, hr]
    have hter : ¬ (contractRooted Q (· = C)).IsHybridArc er := by
      rw [contractRooted_isHybridArc_iff hQ h1]
      have ht := (sdRootArc_spec hQ.1 hQ.2 hX).2
      unfold IsTreeArc at ht
      unfold IsHybridArc
      change ¬ 2 ≤ Q.graph.indegree (Q.graph.target (sdRootArc hQ.1 hQ.2 hX))
      omega
    have he₀ := source_reduceRootArc hM hb hX h2 hl
    have ht₀ := not_isHybridArc_of_isOnChain_reduceRootArc hM hb hX (Or.inl rfl)
    obtain ⟨ιU⟩ := nonempty_sdMetricIso_unrootAt_swap (contractSet_isPhylogenetic hQ h1)
      (contractMetric Q (· = C) θ) her he₀ h2 hter ht₀
    obtain ⟨ι₁⟩ := nonempty_sdMetricIso_suppress_unrootAt hM hb hX h2 hl hθM
    exact ⟨(ιS.trans ιU).suppress.trans ι₁⟩

end Contract

end Banos2019
