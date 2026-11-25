module

public import Banos2019.Quartet.RootedIso
public import Banos2019.Quartet.SemidirectedCycles
public import Banos2019.Network.Suppress

/-!
# Isomorphic rooted networks have isomorphic unrooted networks

An isomorphism `φ` of rooted networks keeps binarity, level-1, the LSA network property and the
metrics. When the two networks are binary and their roots are the LSAs of their taxa, it gives an
isomorphism of their metric unrooted networks (`RootedNetworkIso.nonempty_sdMetricIso`): the nodes
and edges of `N⁻` are those of `N` but the root and the arc `e₀` merged at the root, and `φ` maps them
to those of `N'⁻`, after exchanging the two arcs at the root of `N'` when `φ e₀` is not the arc that
`N'⁻` merges (`unrootedArcMap`). Renaming the nodes and arcs by `Fin` (`finCopy`) gives such an
isomorphism onto a network on `Type`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E V' E' X : Type*}

theorem sdVert_sdVertEquiv_symm {M : RootedNetwork V E X} (hM : M.IsPhylogenetic)
    (hX : Nontrivial X) (b : {v : V // M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) v ∧
      v ≠ lsa hM Set.univ Set.univ_nonempty}) :
    sdVert hM hX ((sdVertEquiv hM hX).symm b) = b.1 := by
  unfold sdVertEquiv
  exact Equiv.ofInjectiveSubtype_symm_apply _ _ _ _ b

theorem sdArc_sdArcEquiv_symm {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) (hB : M.IsBinary)
    (hX : Nontrivial X) (b : {e : E // M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty)
      (M.graph.source e) ∧ e ≠ sdRootArc hM hB hX}) :
    sdArc hM hB hX ((sdArcEquiv hM hB hX).symm b) = b.1 := by
  unfold sdArcEquiv
  exact Equiv.ofInjectiveSubtype_symm_apply _ _ _ _ b

namespace RootedNetworkIso

variable {N : RootedNetwork V E X} {N' : RootedNetwork V' E' X} (φ : RootedNetworkIso N N')

include φ in
theorem isBinary (hB : N.IsBinary) : N'.IsBinary := by
  refine ⟨by rw [φ.root, φ.outdegree_eq]; exact hB.1, fun v' hv' h0 => ?_⟩
  obtain ⟨v, rfl⟩ := φ.vert.surjective v'
  rw [φ.outdegree_eq] at h0
  rw [φ.indegree_eq, φ.outdegree_eq]
  exact hB.2 v (fun h => hv' (by rw [h, φ.root])) h0

include φ in
theorem isBinaryRootedNetwork (hN : IsBinaryRootedNetwork N) : IsBinaryRootedNetwork N' :=
  ⟨φ.isPhylogenetic hN.1, φ.isBinary hN.2⟩

theorem source_symm (e' : E') : N.graph.source (φ.arc.symm e') = φ.vert.symm (N'.graph.source e') := by
  rw [Equiv.eq_symm_apply, ← φ.source, Equiv.apply_symm_apply]

theorem target_symm (e' : E') : N.graph.target (φ.arc.symm e') = φ.vert.symm (N'.graph.target e') := by
  rw [Equiv.eq_symm_apply, ← φ.target, Equiv.apply_symm_apply]

include φ in
theorem isLevelOne (h1 : IsLevelOne N.graph) : IsLevelOne N'.graph :=
  IsLevelOne.of_injective h1 φ.vert.symm φ.arc.symm φ.vert.symm.injective φ.arc.symm.injective
    φ.source_symm φ.target_symm

theorem hasPathAvoiding {u w t : V} (h : N.HasPathAvoiding u w t) :
    N'.HasPathAvoiding (φ.vert u) (φ.vert w) (φ.vert t) := by
  obtain ⟨hu, hw, hp⟩ := h
  refine ⟨fun h => hu (φ.vert.injective h), fun h => hw (φ.vert.injective h), ?_⟩
  clear hu hw
  induction hp with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨hadj, hb, hc⟩ := hbc
    exact ih.tail ⟨(φ.adj_iff b c).2 hadj, fun h => hb (φ.vert.injective h),
      fun h => hc (φ.vert.injective h)⟩

theorem isStableAncestor_iff {Y : Set X} (v : V) :
    N'.IsStableAncestor Y (φ.vert v) ↔ N.IsStableAncestor Y v := by
  constructor
  · intro h x hx hp
    have := φ.hasPathAvoiding hp
    rw [← φ.root, ← φ.leaf] at this
    exact h x hx this
  · intro h x hx hp
    have := φ.symm.hasPathAvoiding hp
    rw [← φ.symm.root, ← φ.symm.leaf] at this
    exact h x hx (by simpa [symm] using this)

include φ in
theorem isLSANetwork (hl : N.IsLSANetwork) : N'.IsLSANetwork := by
  refine ⟨root_isStableAncestor _ _, fun w' hw' => ?_⟩
  obtain ⟨w, rfl⟩ := φ.vert.surjective w'
  rw [φ.root, φ.reaches_iff]
  exact hl.2 w ((φ.isStableAncestor_iff w).1 hw')

theorem isTreeArc_iff (e : E) : N'.IsTreeArc (φ.arc e) ↔ N.IsTreeArc e := by
  unfold IsTreeArc
  rw [φ.target, φ.indegree_eq]

variable [Fintype E] [Fintype E']

include φ in
theorem isMetricNetwork {θ : MetricData E} {θ' : MetricData E'}
    (hlen : ∀ e, θ'.length (φ.arc e) = θ.length e)
    (hinh : ∀ e, θ'.inheritance (φ.arc e) = θ.inheritance e) (hθ : IsMetricNetwork N θ) :
    IsMetricNetwork N' θ' := by
  have hall : ∀ P : E' → Prop, (∀ e, P (φ.arc e)) → ∀ e', P e' := fun P h e' => by
    obtain ⟨e, rfl⟩ := φ.arc.surjective e'
    exact h e
  refine ⟨⟨hall _ fun e he => ?_, hall _ fun e he => ?_, hall _ fun e he => ?_,
    hall _ fun e he => ?_, fun v' hv' => ?_⟩, hall _ fun e => by rw [hlen]; exact hθ.2 e⟩
  · rw [hlen]; exact hθ.1.1 e ((φ.isTreeArc_iff e).1 he)
  · rw [hlen]; exact hθ.1.2.1 e ((φ.isHybridArc_iff e).1 he)
  · rw [hinh]; exact hθ.1.2.2.1 e ((φ.isTreeArc_iff e).1 he)
  · rw [hinh]; exact hθ.1.2.2.2.1 e ((φ.isHybridArc_iff e).1 he)
  · obtain ⟨v, rfl⟩ := φ.vert.surjective v'
    rw [φ.indegree_eq] at hv'
    rw [← hθ.1.2.2.2.2 v hv', ← φ.arc.sum_comp]
    refine sum_congr rfl fun e _ => ?_
    rw [φ.target, φ.vert.injective.eq_iff, hinh]

/-! ### The unrooted networks -/

variable (hN : IsBinaryRootedNetwork N) (hN' : IsBinaryRootedNetwork N') (hl : N.IsLSANetwork)
  (hl' : N'.IsLSANetwork) (hX : Nontrivial X)

/-- The arcs of `N'` of the arcs of `N`, with the two arcs at the root of `N'` exchanged when `φ`
does not map the arc `e₀` that `N⁻` merges onto the one that `N'⁻` merges. -/
def unrootedArcMap : E ≃ E' :=
  φ.arc.trans (Equiv.swap (φ.arc (sdRootArc hN.1 hN.2 hX)) (sdRootArc hN'.1 hN'.2 hX))

omit [Fintype E] [Fintype E'] in
/-- The arcs at the root of `N'` are the images of those at the root of `N`. -/
theorem eq_or_eq_of_source_root (e : E) (he : N.graph.source e = N.root) {e' : E'}
    (he' : N'.graph.source e' = N'.root) (hne : e' ≠ φ.arc e) :
    ∃ f, f ≠ e ∧ N.graph.source f = N.root ∧ e' = φ.arc f := by
  refine ⟨φ.arc.symm e', fun h => hne (by rw [← h, Equiv.apply_symm_apply]), ?_,
    (Equiv.apply_symm_apply _ _).symm⟩
  rw [φ.source_symm, he', φ.root, Equiv.symm_apply_apply]

omit [Fintype E] [Fintype E'] in
include hl hl' in
/-- **Isomorphic rooted networks have isomorphic unrooted networks**: binary networks whose roots
are the LSAs of their taxa, isomorphic by `φ` with the same lengths and inheritance probabilities,
have isomorphic metric unrooted networks, through `φ` on the nodes and `unrootedArcMap` on the
edges. -/
theorem nonempty_sdMetricIso {θ : MetricData E} {θ' : MetricData E'}
    (hlen : ∀ e, θ'.length (φ.arc e) = θ.length e)
    (hinh : ∀ e, θ'.inheritance (φ.arc e) = θ.inheritance e) :
    Nonempty (SDMetricIso (unrooted N hN hX) (unrootedMetric N hN hX θ) (unrooted N' hN' hX)
      (unrootedMetric N' hN' hX θ')) := by
  have := hN.1.finite_arcs
  have hr := lsa_univ_eq_root hN.1 hX hl
  have hr' := lsa_univ_eq_root hN'.1 hX hl'
  set G := unrooted N hN hX
  set G' := unrooted N' hN' hX
  set e₀ := sdRootArc hN.1 hN.2 hX with he₀_def
  set e₀' := sdRootArc hN'.1 hN'.2 hX with he₀'_def
  have he₀ : N.graph.source e₀ = N.root := (sdRootArc_spec hN.1 hN.2 hX).1.trans hr
  have he₀' : N'.graph.source e₀' = N'.root := (sdRootArc_spec hN'.1 hN'.2 hX).1.trans hr'
  have ht₀ : N.IsTreeArc e₀ := (sdRootArc_spec hN.1 hN.2 hX).2
  have ht₀' : N'.IsTreeArc e₀' := (sdRootArc_spec hN'.1 hN'.2 hX).2
  have hnh : ∀ {f : E}, N.IsTreeArc f → ¬ N.IsHybridArc f := fun h h' => by
    unfold IsTreeArc at h
    unfold IsHybridArc at h'
    omega
  have hnh' : ∀ {f : E'}, N'.IsTreeArc f → ¬ N'.IsHybridArc f := fun h h' => by
    unfold IsTreeArc at h
    unfold IsHybridArc at h'
    omega
  -- the arcs at the root
  have hroot2 : ∀ f g, f ≠ g → N.graph.source f = N.root → N.graph.source g = N.root →
      ∀ k, N.graph.source k = N.root → k = f ∨ k = g := by
    intro f g hfg hf hg k hk
    obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 hN.2.1
    have m : ∀ z, N.graph.source z = N.root → z = x ∨ z = y := fun z hz => by
      have : z ∈ {e | N.graph.source e = N.root} := hz
      rw [hs] at this
      simpa using this
    rcases m f hf with r1 | r1 <;> rcases m g hg with r2 | r2 <;> rcases m k hk with r3 | r3 <;>
      subst_vars <;> simp_all
  -- the map of the edges
  set τ := φ.unrootedArcMap hN hN' hX with hτ_def
  have hτ₀ : τ e₀ = e₀' := Equiv.swap_apply_left _ _
  have hτ : ∀ e, e ≠ e₀ → τ e = if φ.arc e = e₀' then φ.arc e₀ else φ.arc e := by
    intro e he
    show Equiv.swap (φ.arc e₀) e₀' (φ.arc e) = _
    rw [Equiv.swap_apply_def, ite_eq_right (fun h => he (φ.arc.injective h))]
  have hφr : φ.vert N.root = N'.root := φ.root.symm
  -- the three kinds of edges
  have hA : ∀ e, e ≠ e₀ → N.graph.source e ≠ N.root →
      τ e = φ.arc e ∧ N'.graph.source (φ.arc e) ≠ N'.root := by
    intro e he hs
    have hs' : N'.graph.source (φ.arc e) ≠ N'.root := by
      rw [φ.source, ← hφr]
      exact fun h => hs (φ.vert.injective h)
    refine ⟨?_, hs'⟩
    rw [hτ e he, ite_eq_right]
    intro h
    exact hs' (h ▸ he₀')
  have hB : ∀ e, e ≠ e₀ → N.graph.source e = N.root → φ.arc e ≠ e₀' →
      τ e = φ.arc e ∧ e₀' = φ.arc e₀ := by
    intro e he hs hne
    refine ⟨by rw [hτ e he, ite_eq_right hne], ?_⟩
    have hs₀ : N.graph.source (φ.arc.symm e₀') = N.root := by
      rw [φ.source_symm, he₀', ← hφr, Equiv.symm_apply_apply]
    rcases hroot2 e₀ e (Ne.symm he) he₀ hs _ hs₀ with h | h
    · rw [← h, Equiv.apply_symm_apply]
    · exact absurd (by rw [← h, Equiv.apply_symm_apply]) hne
  have hC : ∀ e, e ≠ e₀ → φ.arc e = e₀' → τ e = φ.arc e₀ ∧ N.graph.source e = N.root := by
    intro e he heq
    refine ⟨by rw [hτ e he, ite_eq_left heq], φ.vert.injective ?_⟩
    rw [← φ.source, heq, he₀', hφr]
  -- the nodes and the edges
  have hV : ∀ v, (N.graph.Reaches (lsa hN.1 Set.univ Set.univ_nonempty) v ∧
      v ≠ lsa hN.1 Set.univ Set.univ_nonempty) ↔
      (N'.graph.Reaches (lsa hN'.1 Set.univ Set.univ_nonempty) (φ.vert v) ∧
        φ.vert v ≠ lsa hN'.1 Set.univ Set.univ_nonempty) := by
    intro v
    rw [hr, hr', ← hφr, φ.reaches_iff, φ.vert.injective.ne_iff]
  have hE : ∀ e, (N.graph.Reaches (lsa hN.1 Set.univ Set.univ_nonempty) (N.graph.source e) ∧
      e ≠ e₀) ↔ (N'.graph.Reaches (lsa hN'.1 Set.univ Set.univ_nonempty) (N'.graph.source (τ e)) ∧
        τ e ≠ e₀') := by
    intro e
    rw [hr, hr']
    refine and_congr ⟨fun _ => hN'.1.root_reaches _, fun _ => hN.1.root_reaches _⟩ ?_
    rw [← hτ₀]
    exact τ.injective.ne_iff.symm
  let vert : SemidirectedVertex hN.1 hX ≃ SemidirectedVertex hN'.1 hX :=
    (sdVertEquiv hN.1 hX).trans ((φ.vert.subtypeEquiv hV).trans (sdVertEquiv hN'.1 hX).symm)
  let edge : SemidirectedArc hN.1 hN.2 hX ≃ SemidirectedArc hN'.1 hN'.2 hX :=
    (sdArcEquiv hN.1 hN.2 hX).trans ((τ.subtypeEquiv hE).trans (sdArcEquiv hN'.1 hN'.2 hX).symm)
  have hvert : ∀ w, sdVert hN'.1 hX (vert w) = φ.vert (sdVert hN.1 hX w) := fun w =>
    sdVert_sdVertEquiv_symm hN'.1 hX _
  have hedge : ∀ g, sdArc hN'.1 hN'.2 hX (edge g) = τ (sdArc hN.1 hN.2 hX g) := fun g =>
    sdArc_sdArcEquiv_symm hN'.1 hN'.2 hX _
  have hsv := sdVert_source hN.1 hN.2 hX
  have hsv' := sdVert_source hN'.1 hN'.2 hX
  have hne₀ : ∀ g, sdArc hN.1 hN.2 hX g ≠ e₀ := sdArc_ne_sdRootArc hN.1 hN.2 hX
  -- the ends of the edges
  have hends : ∀ g,
      (sdVert hN'.1 hX (G'.graph.source (edge g)) = φ.vert (sdVert hN.1 hX (G.graph.source g)) ∧
        sdVert hN'.1 hX (G'.graph.target (edge g)) = φ.vert (sdVert hN.1 hX (G.graph.target g)) ∧
        τ (sdArc hN.1 hN.2 hX g) = φ.arc (sdArc hN.1 hN.2 hX g)) ∨
      (sdVert hN'.1 hX (G'.graph.source (edge g)) = φ.vert (sdVert hN.1 hX (G.graph.target g)) ∧
        sdVert hN'.1 hX (G'.graph.target (edge g)) = φ.vert (sdVert hN.1 hX (G.graph.source g)) ∧
        φ.arc (sdArc hN.1 hN.2 hX g) = e₀') := by
    intro g
    set e := sdArc hN.1 hN.2 hX g
    have htg : sdVert hN'.1 hX (G'.graph.target (edge g)) = N'.graph.target (τ e) := by
      rw [sdVert_target, hedge]
    rw [hsv' (edge g), hedge, hsv g, sdVert_target hN.1 hN.2 hX g, htg, hr, hr']
    by_cases hs : N.graph.source e = N.root
    · by_cases hne : φ.arc e = e₀'
      · obtain ⟨hτe, -⟩ := hC e (hne₀ g) hne
        refine Or.inr ⟨?_, ?_, hne⟩
        · rw [hτe, ite_eq_left (by rw [φ.source, he₀, hφr])]
          show N'.graph.target e₀' = _
          rw [← hne, φ.target]
        · rw [ite_eq_left hs, hτe, φ.target]
      · obtain ⟨hτe, h₀⟩ := hB e (hne₀ g) hs hne
        refine Or.inl ⟨?_, ?_, hτe⟩
        · rw [hτe, ite_eq_left (by rw [φ.source, hs, hφr]), ite_eq_left hs]
          show N'.graph.target e₀' = _
          rw [h₀, φ.target]
        · rw [hτe, φ.target]
    · obtain ⟨hτe, hs'⟩ := hA e (hne₀ g) hs
      refine Or.inl ⟨?_, ?_, hτe⟩
      · rw [hτe, ite_eq_right hs', ite_eq_right hs, φ.source]
      · rw [hτe, φ.target]
  have hdir : ∀ g, G'.IsDirected (edge g) ↔ G.IsDirected g := by
    intro g
    rw [semidirected_isDirected_iff, semidirected_isDirected_iff, hedge]
    rcases hends g with ⟨-, -, h⟩ | ⟨-, -, h⟩
    · rw [h, φ.isHybridArc_iff]
    · obtain ⟨hτe, -⟩ := hC _ (hne₀ g) h
      rw [hτe, φ.isHybridArc_iff]
      constructor
      · exact fun h' => absurd h' (hnh ht₀)
      · intro h'
        rw [← φ.isHybridArc_iff, h] at h'
        exact absurd h' (hnh' ht₀')
  have hdirτ : ∀ g, G.IsDirected g → τ (sdArc hN.1 hN.2 hX g) = φ.arc (sdArc hN.1 hN.2 hX g) ∧
      sdVert hN'.1 hX (G'.graph.source (edge g)) = φ.vert (sdVert hN.1 hX (G.graph.source g)) ∧
      sdVert hN'.1 hX (G'.graph.target (edge g)) = φ.vert (sdVert hN.1 hX (G.graph.target g)) := by
    intro g hd
    rcases hends g with ⟨h₁, h₂, h₃⟩ | ⟨-, -, h⟩
    · exact ⟨h₃, h₁, h₂⟩
    · exfalso
      rw [semidirected_isDirected_iff, ← φ.isHybridArc_iff, h] at hd
      exact hnh' ht₀' hd
  refine ⟨⟨⟨vert, edge, hdir, fun g => ?_, fun g hd => ?_, fun x => ?_⟩, fun g => ?_,
    fun g hd => ?_⟩⟩
  · rcases hends g with ⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩
    · refine Or.inl ⟨sdVert_injective hN'.1 hX ?_, sdVert_injective hN'.1 hX ?_⟩
      · rw [h₁, hvert]
      · rw [h₂, hvert]
    · refine Or.inr ⟨sdVert_injective hN'.1 hX ?_, sdVert_injective hN'.1 hX ?_⟩
      · rw [h₁, hvert]
      · rw [h₂, hvert]
  · obtain ⟨-, h₁, h₂⟩ := hdirτ g hd
    exact ⟨sdVert_injective hN'.1 hX (by rw [h₁, hvert]),
      sdVert_injective hN'.1 hX (by rw [h₂, hvert])⟩
  · apply sdVert_injective hN'.1 hX
    rw [hvert, sdVert_leaf, sdVert_leaf, φ.leaf]
  · rw [semidirectedMetric_length, semidirectedMetric_length, hedge, hr, hr']
    set e := sdArc hN.1 hN.2 hX g
    by_cases hs : N.graph.source e = N.root
    · by_cases hne : φ.arc e = e₀'
      · obtain ⟨hτe, -⟩ := hC e (hne₀ g) hne
        rw [hτe, ite_eq_left (by rw [φ.source, he₀, hφr]), ite_eq_left hs, hlen]
        show θ.length e₀ + θ'.length e₀' = θ.length e + θ.length e₀
        rw [← hne, hlen, add_comm]
      · obtain ⟨hτe, h₀⟩ := hB e (hne₀ g) hs hne
        rw [hτe, ite_eq_left (by rw [φ.source, hs, hφr]), ite_eq_left hs]
        show θ'.length (φ.arc e) + θ'.length e₀' = θ.length e + θ.length e₀
        rw [h₀, hlen, hlen]
    · obtain ⟨hτe, hs'⟩ := hA e (hne₀ g) hs
      rw [hτe, ite_eq_right hs', ite_eq_right hs, hlen]
  · rw [semidirectedMetric_inheritance, semidirectedMetric_inheritance, hedge, (hdirτ g hd).1,
      hinh]

end RootedNetworkIso

/-! ### Renaming by `Fin` -/

section FinCopy

variable [Fintype V] [Fintype E]

/-- The network `N` with its nodes and arcs renamed by `Fin`. -/
def finCopy (N : RootedNetwork V E X) :
    RootedNetwork (Fin (Fintype.card V)) (Fin (Fintype.card E)) X where
  graph :=
    { source := fun e => Fintype.equivFin V (N.graph.source ((Fintype.equivFin E).symm e))
      target := fun e => Fintype.equivFin V (N.graph.target ((Fintype.equivFin E).symm e)) }
  root := Fintype.equivFin V N.root
  leaf x := Fintype.equivFin V (N.leaf x)

/-- The parameters of `finCopy N`. -/
def finCopyMetric (θ : MetricData E) : MetricData (Fin (Fintype.card E)) :=
  ⟨fun e => θ.length ((Fintype.equivFin E).symm e),
    fun e => θ.inheritance ((Fintype.equivFin E).symm e)⟩

/-- `N` and `finCopy N` are isomorphic. -/
def finCopyIso (N : RootedNetwork V E X) : RootedNetworkIso N (finCopy N) where
  vert := Fintype.equivFin V
  arc := Fintype.equivFin E
  source e := by simp [finCopy]
  target e := by simp [finCopy]
  root := rfl
  leaf _ := rfl

end FinCopy

end Banos2019
