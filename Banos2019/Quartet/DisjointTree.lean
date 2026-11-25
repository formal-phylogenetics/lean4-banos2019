module

public import Banos2019.Quartet.DisjointNet
public import Banos2019.Quartet.LSARoot
public import Banos2019.Network.CycleMap

/-!
# `Q_a⊕` of a single `3₂`-cycle is a tree (in the proof of Proposition 5)

When `C` is the only cycle of a binary level-1 network `Q`, its hybrid node `v` is the only node with
two parents, and `disjointNet Q v h₁ h₂ a b` has no node with two parents (`disjointNet_arc_eq`)
and no cycle (`disjointNet_not_isCycle`): a cycle would map to a cycle of `Q` avoiding `v`. It is a
binary network whose root is the LSA of its taxa, and the parameters of `Q` give it a metric
(`disjointNet_spec`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] {Q : RootedNetwork V E X} {v : V}
  {h₁ h₂ : E} {a b : X}

section Disjoint

variable (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph) {C : Set E}
  (hone : ∀ C', IsCycle Q.graph C' → C' = C)
  (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2)
  (hne : h₁ ≠ h₂) (hh₁ : Q.graph.target h₁ = v) (hh₂ : Q.graph.target h₂ = v) (hab : a ≠ b)
  (hbelow : ∀ x, Q.graph.Reaches v (Q.leaf x) ↔ x = a ∨ x = b)
include hQ h1 hone hv h2 hne hh₁ hh₂

omit [Fintype V] [Fintype E] [Fintype X] hne hh₁ hh₂ in
/-- The hybrid node of the only cycle is the only node with two parents. -/
theorem eq_hybrid_of_target_eq_of_single_cycle {e f : E} (hef : e ≠ f)
    (ht : Q.graph.target e = Q.graph.target f) : Q.graph.target e = v := by
  have := hQ.1.finite_arcs
  obtain ⟨C', hC', heC', -⟩ := exists_isCycle_of_target_eq hQ h1 hef ht
  have hCC := hone C' hC'
  subst hCC
  exact (lemma3 hQ h1 hC').1.unique ⟨target_mem_cycleNodes heC',
    le_antisymm (hQ.indegree_le_two _) (two_le_indegree_of_two_targets hQ hef rfl ht.symm)⟩ ⟨hv, h2⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **No node of `Q_a⊕` has two parents.** -/
theorem disjointNet_arc_eq {e f : {e // ¬ Q.graph.Reaches v (Q.graph.source e)}}
    (ht : (disjointNet Q v h₁ h₂ a b).graph.target e = (disjointNet Q v h₁ h₂ a b).graph.target f) :
    e = f := by
  have hel := disjointNet_target_elim hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) e
  have hfl := disjointNet_target_elim hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) f
  rcases hte : (disjointNet Q v h₁ h₂ a b).graph.target e with w | i
  · -- a node off the part below `v`
    rw [hte] at hel ht
    rw [← ht] at hfl
    by_contra hnef
    have hne' : e.1 ≠ f.1 := fun h => hnef (Subtype.ext h)
    have := eq_hybrid_of_target_eq_of_single_cycle hQ h1 hone hv h2 hne'
      (hel.symm.trans hfl)
    have hw : w.1 = v := (show w.1 = Q.graph.target e.1 from hel).trans this
    exact w.2 (by rw [hw]; exact .refl)
  · -- a new leaf
    have key : ∀ g : {e // ¬ Q.graph.Reaches v (Q.graph.source e)},
        (disjointNet Q v h₁ h₂ a b).graph.target g = .inr i → (i = 0 ∧ g.1 = h₁) ∨
          (i = 1 ∧ g.1 = h₂) := by
      intro g hg
      by_cases hg₁ : g.1 = h₁
      · rw [disjointNet_target_h₁ g hg₁] at hg
        exact Or.inl ⟨(Sum.inr_injective hg).symm, hg₁⟩
      by_cases hg₂ : g.1 = h₂
      · rw [disjointNet_target_h₂ hne g hg₂] at hg
        exact Or.inr ⟨(Sum.inr_injective hg).symm, hg₂⟩
      obtain ⟨_, h'⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) g hg₁ hg₂
      rw [h'] at hg
      exact absurd hg Sum.inl_ne_inr
    rcases key e hte with ⟨rfl, he⟩ | ⟨rfl, he⟩ <;>
      rcases key f (ht ▸ hte) with ⟨hi, hf⟩ | ⟨hi, hf⟩
    · exact Subtype.ext (he.trans hf.symm)
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact Subtype.ext (he.trans hf.symm)

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **`Q_a⊕` has no cycle**: a new leaf is on one arc only, so it is on no cycle, and a cycle of
`Q_a⊕` off the new leaves is a cycle of `Q` avoiding `v`, while the only cycle of `Q` passes through
`v`. -/
theorem disjointNet_not_isCycle (D : Set {e // ¬ Q.graph.Reaches v (Q.graph.source e)}) :
    ¬ IsCycle (disjointNet Q v h₁ h₂ a b).graph D := by
  intro hD
  set G := (disjointNet Q v h₁ h₂ a b).graph
  have hsrc : ∀ g : {e // ¬ Q.graph.Reaches v (Q.graph.source e)},
      G.source g = .inl ⟨Q.graph.source g.1, g.2⟩ := fun _ => rfl
  have hloop : ∀ f ∈ D, G.source f ≠ G.target f := fun f _ h => by
    have := disjointNet_target_elim hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) f
    rw [← h, hsrc] at this
    exact hQ.1.acyclic _ (.single ⟨f.1, rfl, this.symm⟩)
  -- the new leaves are on no cycle
  have hinr : ∀ i, (.inr i : {u // ¬ Q.graph.Reaches v u} ⊕ Fin 2) ∉ cycleNodes G D := by
    intro i hi
    obtain ⟨f₁, -, f₂, -, hf, hf₁, hf₂⟩ := hD.exists_ne_of_mem hloop hi
    rw [hsrc] at hf₁ hf₂
    have hf₁' : G.target f₁ = .inr i := hf₁.resolve_left Sum.inl_ne_inr
    have hf₂' : G.target f₂ = .inr i := hf₂.resolve_left Sum.inl_ne_inr
    exact hf (disjointNet_arc_eq hQ h1 hone hv h2 hne hh₁ hh₂ (hf₁'.trans hf₂'.symm))
  -- the image in `Q`
  set φ : {u // ¬ Q.graph.Reaches v u} ⊕ Fin 2 → V := Sum.elim Subtype.val (fun _ => v)
  have hs : ∀ e ∈ D, Q.graph.source e.1 = φ (G.source e) := fun e _ => rfl
  have ht : ∀ e ∈ D, Q.graph.target e.1 = φ (G.target e) := fun e _ =>
    (disjointNet_target_elim hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) e).symm
  have hφ : Set.InjOn φ (cycleNodes G D) := by
    rintro (x | i) hx (y | j) hy hxy
    · exact congrArg Sum.inl (Subtype.ext hxy)
    · exact absurd hy (hinr j)
    · exact absurd hx (hinr i)
    · exact absurd hx (hinr i)
  have hD' := IsCycle.image φ Subtype.val hD hφ Subtype.val_injective.injOn hs ht
  have hCD := hone _ hD'
  have hvD : v ∈ cycleNodes Q.graph (Subtype.val '' D) := hCD ▸ hv
  rw [cycleNodes_image φ Subtype.val hs ht] at hvD
  obtain ⟨x | i, hx, hxv⟩ := hvD
  · exact x.2 (by rw [show x.1 = v from hxv]; exact .refl)
  · exact hinr i hx

omit [Fintype V] [Fintype E] [Fintype X] hQ h1 hone hv h2 hne hh₁ hh₂ in
/-- The arcs of `Q_a⊕` out of a node `inl w` are those of `Q` out of `w`. -/
theorem disjointNet_outdegree_inl (w : {u // ¬ Q.graph.Reaches v u}) :
    (disjointNet Q v h₁ h₂ a b).graph.outdegree (.inl w) = Q.graph.outdegree w.1 := by
  unfold DirectedMultigraph.outdegree
  refine Set.ncard_congr (fun e _ => e.1)
    (fun e (he : (disjointNet Q v h₁ h₂ a b).graph.source e = .inl w) =>
      congrArg Subtype.val (Sum.inl_injective he))
    (fun e f _ _ h => Subtype.ext h) fun e (he : Q.graph.source e = w.1) => ?_
  refine ⟨⟨e, by rw [he]; exact w.2⟩, ?_, rfl⟩
  show Sum.inl _ = Sum.inl w
  exact congrArg Sum.inl (Subtype.ext he)

omit [Fintype V] [Fintype E] [Fintype X] hQ h1 hone hv h2 hne hh₁ hh₂ in
/-- The new leaves of `Q_a⊕` have no child. -/
theorem disjointNet_outdegree_inr (i : Fin 2) :
    (disjointNet Q v h₁ h₂ a b).graph.outdegree (.inr i) = 0 := by
  unfold DirectedMultigraph.outdegree
  have : {e | (disjointNet Q v h₁ h₂ a b).graph.source e = .inr i} = ∅ :=
    Set.eq_empty_of_forall_notMem fun e he => Sum.inl_ne_inr he
  rw [this, Set.ncard_empty]

omit [Fintype V] [Fintype X] in
include hab hbelow in
/-- **`Q_a⊕` is a binary network whose root is the LSA of its taxa, with a metric**, when `C` is the
only cycle of `Q`. -/
theorem disjointNet_spec {θ : MetricData E} (hθ : IsMetricNetwork Q θ) :
    IsBinaryRootedNetwork (disjointNet Q v h₁ h₂ a b) ∧ (disjointNet Q v h₁ h₂ a b).IsLSANetwork ∧
      IsMetricNetwork (disjointNet Q v h₁ h₂ a b) (disjointMetric Q v h₁ h₂ θ) := by
  have := hQ.1.finite_arcs
  set D := disjointNet Q v h₁ h₂ a b
  have hD := disjointNet_isPhylogenetic hQ h1 h2 hne hh₁ hh₂ hab hbelow
  have hvr : v ≠ Q.root := fun h => by
    have := hQ.1.root_indegree
    rw [← h, h2] at this
    omega
  have hr : ¬ Q.graph.Reaches v Q.root := fun h =>
    hvr (eq_of_reaches_of_reaches hQ.1.acyclic h (hQ.1.root_reaches v))
  have hroot : D.root = .inl ⟨Q.root, hr⟩ := disjointNet_root hr
  have hin : ∀ u, D.graph.indegree u ≤ 1 := fun u => by
    unfold DirectedMultigraph.indegree
    rw [Set.ncard_le_one (Set.toFinite _)]
    exact fun e he f hf => disjointNet_arc_eq hQ h1 hone hv h2 hne hh₁ hh₂ (he.trans hf.symm)
  -- binary
  have hB : D.IsBinary := by
    refine ⟨by rw [hroot, disjointNet_outdegree_inl]; exact hQ.2.1, fun u hu h0 => ?_⟩
    rcases u with w | i
    · rw [disjointNet_outdegree_inl] at h0 ⊢
      rw [disjointNet_indegree_inl hQ h1 h2 hne hh₁ hh₂ w]
      exact hQ.2.2 w.1 (fun h => hu (by rw [hroot]; exact congrArg Sum.inl (Subtype.ext h))) h0
    · exact absurd (disjointNet_outdegree_inr (h₁ := h₁) (h₂ := h₂) (a := a) (b := b) i) h0
  have hbin : IsBinaryRootedNetwork D := ⟨hD, hB⟩
  have h0 : ∀ C', ¬ IsCycle D.graph C' := disjointNet_not_isCycle hQ h1 hone hv h2 hne hh₁ hh₂
  have h1D : IsLevelOne D.graph := fun C₁ _ hC₁ => absurd hC₁ (h0 C₁)
  refine ⟨hbin, isLSANetwork_of_target_ne hbin h1D fun a₁ a₂ hne' _ _ ht =>
    hne' (disjointNet_arc_eq hQ h1 hone hv h2 hne hh₁ hh₂ ht), ?_, fun e => hθ.2 e.1⟩
  -- the parameters: no arc is hybrid, and the tree arcs of `Q` keep inheritance `1`
  have hnh : ∀ e, ¬ D.IsHybridArc e := fun e he => by
    have := hin (D.graph.target e)
    unfold IsHybridArc at he
    omega
  refine ⟨fun e _ => hθ.2 e.1, fun e _ => (hθ.2 e.1).le, fun e _ => ?_, fun e he => absurd he (hnh e),
    fun u hu => absurd hu (by have := hin u; omega)⟩
  show (if e.1 = h₁ ∨ e.1 = h₂ then 1 else θ.inheritance e.1) = 1
  split_ifs with he
  · rfl
  · push Not at he
    obtain ⟨hte, ht⟩ := disjointNet_target_of_ne hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b) e he.1 he.2
    refine hθ.1.2.2.1 e.1 ?_
    unfold IsTreeArc
    refine le_antisymm ?_ (hQ.1.nonroot_indegree _ (hQ.1.target_ne_root e.1))
    have h' := disjointNet_indegree_inl hQ h1 h2 hne hh₁ hh₂ (a := a) (b := b)
      ⟨Q.graph.target e.1, hte⟩
    rw [← h']
    exact hin _

end Disjoint

end Banos2019
