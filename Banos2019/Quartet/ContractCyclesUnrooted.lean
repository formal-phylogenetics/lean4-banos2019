module

public import Banos2019.Quartet.ReduceUnrootedKeep
public import Banos2019.Quartet.ContractSet

/-!
# `Q⁻` with a 2-cycle contracted

For a binary level-1 network `Q` whose root is the LSA of its taxa and a cycle `D` of `Q⁻`,
`contractCycles Q⁻ (· = D)` is, when the cycle `liftEdges D` of `Q` avoids the root, `unrootAt` of
`contractRooted Q (· = liftEdges D)` at the arc of `Q` that `Q⁻` merges
(`nonempty_sdMetricIso_contractCycles_unrootAt`), and, when it passes through the root, the
contracted network with its root kept (`nonempty_sdMetricIso_contractCycles_keepRootSD`): the node
of the contracted cycle of `Q⁻` is the root of the contracted network.

* `contractCyclesSdVert`, `contractCyclesSdArc`: the node and the arc of the contracted network of a
  node and an edge of `Q⁻` with `D` contracted, both injective.
* `contractRooted_isHybridArc_iff`: the hybrid arcs of the contracted network are the hybrid arcs of
  `Q` off the contracted cycles.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Maps

variable {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q) (hX : Nontrivial X)

/-- The node of `contractRooted Q (· = liftEdges D)` of a node of `Q⁻` with `D` contracted: the
class of its node of `Q`. -/
def contractCyclesSdVert (D : Set (SemidirectedArc hQ.1 hQ.2 hX)) :
    Quot (ContractRel (semidirected hQ.1 hQ.2 hX).graph (· = D)) →
      Quot (RootedContractRel Q (· = liftEdges hQ.1 hQ.2 hX D)) :=
  Quot.lift (fun u => Quot.mk _ (sdVert hQ.1 hX u)) fun u w ⟨C', hC', hP, hu, hw⟩ => by
    obtain rfl : C' = D := hP
    exact Quot.sound ⟨_, isCycle_liftEdges hQ.1 hQ.2 hX hC', rfl,
      (sdVert_mem_cycleNodes_liftEdges_iff hQ.1 hQ.2 hX C' u).2 hu,
      (sdVert_mem_cycleNodes_liftEdges_iff hQ.1 hQ.2 hX C' w).2 hw⟩

/-- The arc of `contractRooted Q (· = liftEdges D)` of an edge of `Q⁻` off `D`. -/
def contractCyclesSdArc {D : Set (SemidirectedArc hQ.1 hQ.2 hX)}
    (hD : IsCycle (semidirected hQ.1 hQ.2 hX).graph D)
    (g : {g // ∀ C, IsCycle (semidirected hQ.1 hQ.2 hX).graph C → C = D → g ∉ C}) :
    {e // ∀ C, IsCycle Q.graph C → C = liftEdges hQ.1 hQ.2 hX D → e ∉ C} :=
  ⟨sdArc hQ.1 hQ.2 hX g.1, fun _ _ hCD he =>
    g.2 D hD rfl ((sdArc_mem_liftEdges_iff hQ.1 hQ.2 hX D g.1).1 (hCD ▸ he))⟩

theorem contractCyclesSdVert_injective [Finite E] (h1 : IsLevelOne Q.graph)
    {D : Set (SemidirectedArc hQ.1 hQ.2 hX)} (hD : IsCycle (semidirected hQ.1 hQ.2 hX).graph D) :
    Function.Injective (contractCyclesSdVert hQ hX D) := by
  have := Fintype.ofFinite E
  intro U W h
  induction U using Quot.ind with
  | mk u =>
  induction W using Quot.ind with
  | mk w =>
  change Quot.mk _ (sdVert hQ.1 hX u) = Quot.mk _ (sdVert hQ.1 hX w) at h
  rcases (contractSet_mk_eq_mk_iff hQ h1).1 h with h' | ⟨C', -, hP, hu, hw⟩
  · rw [sdVert_injective hQ.1 hX h']
  · obtain rfl : C' = liftEdges hQ.1 hQ.2 hX D := hP
    exact Quot.sound ⟨D, hD, rfl, (sdVert_mem_cycleNodes_liftEdges_iff hQ.1 hQ.2 hX D u).1 hu,
      (sdVert_mem_cycleNodes_liftEdges_iff hQ.1 hQ.2 hX D w).1 hw⟩

theorem contractCyclesSdArc_injective {D : Set (SemidirectedArc hQ.1 hQ.2 hX)}
    (hD : IsCycle (semidirected hQ.1 hQ.2 hX).graph D) :
    Function.Injective (contractCyclesSdArc hQ hX hD) := by
  intro g g' h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (sdArc_injective hQ.1 hQ.2 hX h')

include hQ in
/-- **The hybrid arcs of the contracted network are the hybrid arcs of `Q` off the contracted
cycles**: the target of an arc has the indegree of its node of `Q`. -/
theorem contractRooted_isHybridArc_iff [Fintype V] [Fintype E] (h1 : IsLevelOne Q.graph)
    {P : Set E → Prop} (e : {e // ∀ C, IsCycle Q.graph C → P C → e ∉ C}) :
    (contractRooted Q P).IsHybridArc e ↔ Q.IsHybridArc e.1 := by
  unfold RootedNetwork.IsHybridArc
  rw [contractSet_indegree hQ h1, contractSetRep_target]

end Maps

section Contract

variable [Fintype V] [Fintype E] {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q)
  (h1 : IsLevelOne Q.graph) (hX : Nontrivial X)

omit [Fintype V] [Fintype E] in
/-- The arc of `Q` that `Q⁻` merges is off a cycle of `Q` avoiding the root. -/
theorem sdRootArc_notMem_of_root_notMem {D : Set (SemidirectedArc hQ.1 hQ.2 hX)}
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root)
    (hρ : Q.root ∉ cycleNodes Q.graph (liftEdges hQ.1 hQ.2 hX D)) :
    ∀ C, IsCycle Q.graph C → C = liftEdges hQ.1 hQ.2 hX D → sdRootArc hQ.1 hQ.2 hX ∉ C := by
  rintro C - rfl hC
  exact hρ ⟨_, hC, Or.inl ((sdRootArc_spec hQ.1 hQ.2 hX).1.trans hr)⟩

/-- **Contracting a 2-cycle of `Q⁻` off the root is `unrootAt` of the contracted network** at the
arc of `Q` that `Q⁻` merges. -/
theorem nonempty_sdMetricIso_contractCycles_unrootAt
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root) (θ : MetricData E)
    {D : Set (SemidirectedArc hQ.1 hQ.2 hX)} (hD : IsCycle (semidirected hQ.1 hQ.2 hX).graph D)
    (hρ : Q.root ∉ cycleNodes Q.graph (liftEdges hQ.1 hQ.2 hX D)) :
    Nonempty (SDMetricIso (contractCycles (semidirected hQ.1 hQ.2 hX) (· = D))
      (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _)
      (unrootAt (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D))
        (contractSet_isPhylogenetic hQ h1)
        ⟨sdRootArc hQ.1 hQ.2 hX, sdRootArc_notMem_of_root_notMem hQ hX hr hρ⟩)
      (unrootAtMetric (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D))
        ⟨sdRootArc hQ.1 hQ.2 hX, sdRootArc_notMem_of_root_notMem hQ hX hr hρ⟩
        (contractMetric Q (· = liftEdges hQ.1 hQ.2 hX D) θ))) := by
  have hC : IsCycle Q.graph (liftEdges hQ.1 hQ.2 hX D) := isCycle_liftEdges hQ.1 hQ.2 hX hD
  have hnot : ¬ InPCycle Q (· = liftEdges hQ.1 hQ.2 hX D) Q.root := fun ⟨C', _, hP, hρ'⟩ =>
    hρ (hP ▸ hρ')
  -- the class of the root is the root alone
  have hroot : ∀ a, Quot.mk (RootedContractRel Q (· = liftEdges hQ.1 hQ.2 hX D)) a =
      Quot.mk _ Q.root ↔ a = Q.root := fun a => contractSet_mk_eq_mk_iff_of_not' hQ h1 hnot
  -- the nodes
  have hv : ∀ U, contractCyclesSdVert hQ hX D U ≠
      (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).root := by
    intro U
    induction U using Quot.ind with
    | mk u =>
      intro h
      exact sdVert_ne_lsa hQ.1 hX u (((hroot _).1 h).trans hr.symm)
  let fv : Quot (ContractRel (semidirected hQ.1 hQ.2 hX).graph (· = D)) →
      {W // W ≠ (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).root} :=
    fun U => ⟨contractCyclesSdVert hQ hX D U, hv U⟩
  have hfv : Function.Bijective fv := by
    refine ⟨fun U W h => contractCyclesSdVert_injective hQ hX h1 hD (congrArg Subtype.val h), ?_⟩
    rintro ⟨W, hW⟩
    induction W using Quot.ind with
    | mk x =>
      have hx : x ≠ Q.root := fun h => hW (by rw [h]; rfl)
      obtain ⟨u, hu⟩ := exists_sdVert_of_ne hQ.1 hX hr hx
      refine ⟨Quot.mk _ u, Subtype.ext ?_⟩
      change Quot.mk _ (sdVert hQ.1 hX u) = _
      rw [hu]
  -- the edges
  let e₀ : {e // ∀ C, IsCycle Q.graph C → C = liftEdges hQ.1 hQ.2 hX D → e ∉ C} :=
    ⟨sdRootArc hQ.1 hQ.2 hX, sdRootArc_notMem_of_root_notMem hQ hX hr hρ⟩
  let fe : {g // ∀ C, IsCycle (semidirected hQ.1 hQ.2 hX).graph C → C = D → g ∉ C} →
      {e // e ≠ e₀} := fun g => ⟨contractCyclesSdArc hQ hX hD g, fun h =>
        have h' := congrArg Subtype.val h
        sdArc_ne_sdRootArc hQ.1 hQ.2 hX g.1 h'⟩
  have hfe : Function.Bijective fe := by
    refine ⟨fun g g' h => contractCyclesSdArc_injective hQ hX hD (congrArg Subtype.val h), ?_⟩
    rintro ⟨⟨e, he⟩, he₀⟩
    have hne : e ≠ sdRootArc hQ.1 hQ.2 hX := fun h => he₀ (Subtype.ext h)
    obtain ⟨g, rfl⟩ := (mem_range_sdArc hQ.1 hQ.2 hX e).2
      ⟨by rw [hr]; exact hQ.1.root_reaches _, hne⟩
    have hgD : g ∉ D := fun hg => he _ hC rfl ((sdArc_mem_liftEdges_iff hQ.1 hQ.2 hX D g).2 hg)
    exact ⟨⟨g, fun C' _ hC'D => hC'D ▸ hgD⟩, rfl⟩
  -- the source of an edge
  have hsrc : ∀ g, ((unrootAt (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D))
      (contractSet_isPhylogenetic hQ h1) e₀).graph.source (fe g)).1 =
      Quot.mk _ (sdVert hQ.1 hX ((semidirected hQ.1 hQ.2 hX).graph.source g.1)) := by
    intro g
    rcases sdVert_source_cases hQ.1 hQ.2 hX g.1 with ⟨hne, hs⟩ | ⟨heq, hs⟩
    · rw [hs]
      exact unrootAt_source_of_ne (contractSet_isPhylogenetic hQ h1)
        (fun h => hne (((hroot _).1 h).trans hr.symm))
    · rw [hs]
      have h' : (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).graph.source (fe g).1 =
          (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).root := (hroot _).2 (heq.trans hr)
      simp only [unrootAt, h', ↓reduceDIte]
      rfl
  refine ⟨⟨⟨Equiv.ofBijective fv hfv, Equiv.ofBijective fe hfe, fun g => ?_, fun g => ?_,
    fun g _ => ?_, fun x => ?_⟩, fun g => ?_, fun g _ => rfl⟩⟩
  · change (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).IsHybridArc
      (contractCyclesSdArc hQ hX hD g) ↔ (semidirected hQ.1 hQ.2 hX).IsDirected g.1
    rw [contractRooted_isHybridArc_iff hQ h1, semidirected_isDirected_iff]
    rfl
  · exact Or.inl ⟨Subtype.ext (hsrc g), Subtype.ext rfl⟩
  · exact ⟨Subtype.ext (hsrc g), Subtype.ext rfl⟩
  · exact Subtype.ext rfl
  · change (if Quot.mk (RootedContractRel Q (· = liftEdges hQ.1 hQ.2 hX D))
        (Q.graph.source (sdArc hQ.1 hQ.2 hX g.1)) = Quot.mk _ Q.root then
        θ.length (sdArc hQ.1 hQ.2 hX g.1) + θ.length (sdRootArc hQ.1 hQ.2 hX)
        else θ.length (sdArc hQ.1 hQ.2 hX g.1)) = (semidirectedMetric hQ.1 hQ.2 hX θ).length g.1
    rw [semidirectedMetric_length]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd (((hroot _).1 h₁).trans hr.symm) h₂
    · exact absurd ((hroot _).2 (h₂.trans hr)) h₁
    · rfl

/-- **Contracting a 2-cycle of `Q⁻` through the merged edge is the contracted network with its root
kept**: the node of the contracted cycle of `Q⁻` is the root of the contracted network. -/
theorem nonempty_sdMetricIso_contractCycles_keepRootSD
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root) (θ : MetricData E)
    {D : Set (SemidirectedArc hQ.1 hQ.2 hX)} (hD : IsCycle (semidirected hQ.1 hQ.2 hX).graph D)
    (hD2 : D.ncard = 2) (hρ : Q.root ∈ cycleNodes Q.graph (liftEdges hQ.1 hQ.2 hX D)) :
    Nonempty (SDMetricIso (contractCycles (semidirected hQ.1 hQ.2 hX) (· = D))
      (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _)
      (keepRootSD (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D))
        (contractSet_isPhylogenetic hQ h1))
      (restrictMetric (contractMetric Q (· = liftEdges hQ.1 hQ.2 hX D) θ) _)) := by
  have hC : IsCycle Q.graph (liftEdges hQ.1 hQ.2 hX D) := isCycle_liftEdges hQ.1 hQ.2 hX hD
  -- the edge of `D` merged at the root
  obtain ⟨g₀, hg₀, hs₀⟩ := (lsa_mem_cycleNodes_liftEdges_iff hQ.1 hQ.2 hX hr D).1
    (by rw [hr]; exact hρ)
  have hr₀ : sdRootArc hQ.1 hQ.2 hX ∈ liftEdges hQ.1 hQ.2 hX D := ⟨g₀, hg₀, Or.inr ⟨hs₀, rfl⟩⟩
  -- the root of the contracted network has outdegree two
  have hout : (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).graph.outdegree
      (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).root ≠ 1 := by
    have h₁ := contractSet_outdegree_of_mem (P := (· = liftEdges hQ.1 hQ.2 hX D)) hQ h1 hC rfl hρ
    have h₂ := ncard_liftEdges hQ.1 hQ.2 hX D
    rw [ite_eq_left ⟨g₀, hg₀, hs₀⟩, hD2] at h₂
    change (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).graph.outdegree (Quot.mk _ Q.root) ≠ 1
    rw [h₁, h₂]
    omega
  -- the nodes
  let fv : Quot (ContractRel (semidirected hQ.1 hQ.2 hX).graph (· = D)) →
      {W // ¬ (W = (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).root ∧
        (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).graph.outdegree
          (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).root = 1)} :=
    fun U => ⟨contractCyclesSdVert hQ hX D U, fun h => hout h.2⟩
  have hfv : Function.Bijective fv := by
    refine ⟨fun U W h => contractCyclesSdVert_injective hQ hX h1 hD (congrArg Subtype.val h), ?_⟩
    rintro ⟨W, hW⟩
    induction W using Quot.ind with
    | mk x =>
      by_cases hx : x = Q.root
      · subst hx
        have hu := (sdVert_mem_cycleNodes_liftEdges_iff hQ.1 hQ.2 hX D
          ((semidirected hQ.1 hQ.2 hX).graph.target g₀)).2 (target_mem_cycleNodes hg₀)
        exact ⟨Quot.mk _ ((semidirected hQ.1 hQ.2 hX).graph.target g₀),
          Subtype.ext (Quot.sound ⟨_, hC, rfl, hu, hρ⟩)⟩
      · obtain ⟨u, hu⟩ := exists_sdVert_of_ne hQ.1 hX hr hx
        refine ⟨Quot.mk _ u, Subtype.ext ?_⟩
        change Quot.mk _ (sdVert hQ.1 hX u) = _
        rw [hu]
  -- the edges
  let fe : {g // ∀ C, IsCycle (semidirected hQ.1 hQ.2 hX).graph C → C = D → g ∉ C} →
      {e // ¬ ((contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).graph.source e =
        (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).root ∧
        (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).graph.outdegree
          (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).root = 1)} :=
    fun g => ⟨contractCyclesSdArc hQ hX hD g, fun h => hout h.2⟩
  have hfe : Function.Bijective fe := by
    refine ⟨fun g g' h => contractCyclesSdArc_injective hQ hX hD (congrArg Subtype.val h), ?_⟩
    rintro ⟨⟨e, he⟩, -⟩
    have hne : e ≠ sdRootArc hQ.1 hQ.2 hX := fun h => he _ hC rfl (h ▸ hr₀)
    obtain ⟨g, rfl⟩ := (mem_range_sdArc hQ.1 hQ.2 hX e).2
      ⟨by rw [hr]; exact hQ.1.root_reaches _, hne⟩
    have hgD : g ∉ D := fun hg => he _ hC rfl ((sdArc_mem_liftEdges_iff hQ.1 hQ.2 hX D g).2 hg)
    exact ⟨⟨g, fun C' _ hC'D => hC'D ▸ hgD⟩, rfl⟩
  -- an edge off `D` does not leave the root
  have hns : ∀ g : {g // ∀ C, IsCycle (semidirected hQ.1 hQ.2 hX).graph C → C = D → g ∉ C},
      Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) ≠ lsa hQ.1 Set.univ Set.univ_nonempty :=
    fun g hs => g.2 D hD rfl (eq_of_source_sdArc_eq_lsa hQ.1 hQ.2 hX hs hs₀ ▸ hg₀)
  have hsrc : ∀ g, ((keepRootSD (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D))
      (contractSet_isPhylogenetic hQ h1)).graph.source (fe g)).1 =
      Quot.mk _ (sdVert hQ.1 hX ((semidirected hQ.1 hQ.2 hX).graph.source g.1)) := by
    intro g
    rcases sdVert_source_cases hQ.1 hQ.2 hX g.1 with ⟨-, hs⟩ | ⟨heq, -⟩
    · rw [hs]
      rfl
    · exact absurd heq (hns g)
  refine ⟨⟨⟨Equiv.ofBijective fv hfv, Equiv.ofBijective fe hfe, fun g => ?_, fun g => ?_,
    fun g _ => ?_, fun x => ?_⟩, fun g => ?_, fun g _ => rfl⟩⟩
  · change (contractRooted Q (· = liftEdges hQ.1 hQ.2 hX D)).IsHybridArc
      (contractCyclesSdArc hQ hX hD g) ↔ (semidirected hQ.1 hQ.2 hX).IsDirected g.1
    rw [contractRooted_isHybridArc_iff hQ h1, semidirected_isDirected_iff]
    rfl
  · exact Or.inl ⟨Subtype.ext (hsrc g), Subtype.ext rfl⟩
  · exact ⟨Subtype.ext (hsrc g), Subtype.ext rfl⟩
  · exact Subtype.ext rfl
  · change θ.length (sdArc hQ.1 hQ.2 hX g.1) = (semidirectedMetric hQ.1 hQ.2 hX θ).length g.1
    rw [semidirectedMetric_length, ite_eq_right (hns g)]

end Contract

end Banos2019
