module

public import Banos2019.Quartet.Conditioning
public import Banos2019.Network.CycleFacts

/-!
# Contracting one cycle (Baños 2019, Section 5)

`Q₀⊕ = contractRooted Q (· = C)` identifies the nodes of the cycle `C` and removes its edges. This
module describes it for a single cycle:

* `mk_eq_mk_iff`: two nodes are identified exactly when they are equal or both nodes of `C`.
* `reaches_contract_iff`: below a vertex `z` none of whose descendants is a node of `C`, the paths of
  `Q₀⊕` are those of `Q⊕`, so `Q₀⊕` and `Q⊕` have isomorphic parts below `z`
  (`isCut_contract`, `rootDist_cutLower_contract`): the law of the forest arriving at `z` is the same.
* The same for `deleteArc` (`isCut_deleteArc`, `rootDist_cutLower_deleteArc`), when the deleted arc
  does not enter a vertex below `z`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

section Contract

variable {Q : RootedNetwork V E X} {C : Set E}

omit [Fintype V] [Fintype E] [Fintype X] in
theorem rootedContractRel_iff (hC : IsCycle Q.graph C) {a b : V} :
    RootedContractRel Q (· = C) a b ↔ a ∈ cycleNodes Q.graph C ∧ b ∈ cycleNodes Q.graph C := by
  constructor
  · rintro ⟨C', -, rfl, ha, hb⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨C, hC, rfl, ha, hb⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **The nodes identified by contracting `C`**: equal nodes, or two nodes of `C`. -/
theorem mk_eq_mk_iff (hC : IsCycle Q.graph C) {a b : V} :
    (Quot.mk (RootedContractRel Q (· = C)) a = Quot.mk _ b) ↔
      a = b ∨ (a ∈ cycleNodes Q.graph C ∧ b ∈ cycleNodes Q.graph C) := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel x y hxy => exact Or.inr ((rootedContractRel_iff hC).1 hxy)
    | refl => exact Or.inl rfl
    | symm x y _ ih => exact ih.elim (fun h => Or.inl h.symm) fun h => Or.inr ⟨h.2, h.1⟩
    | trans x y z _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨hx, hy⟩
      · exact ih₂
      · rcases ih₂ with rfl | ⟨-, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · exact Quot.sound ((rootedContractRel_iff hC).2 ⟨ha, hb⟩)

omit [Fintype V] [Fintype E] [Fintype X] in
theorem mk_eq_mk_iff_of_notMem (hC : IsCycle Q.graph C) {a b : V}
    (ha : a ∉ cycleNodes Q.graph C) :
    (Quot.mk (RootedContractRel Q (· = C)) a = Quot.mk _ b) ↔ a = b := by
  rw [mk_eq_mk_iff hC]
  exact ⟨fun h => h.resolve_right fun h' => ha h'.1, Or.inl⟩

omit [Fintype V] [Fintype E] [Fintype X] in
theorem mk_eq_mk_iff_of_notMem' (hC : IsCycle Q.graph C) {a b : V}
    (hb : b ∉ cycleNodes Q.graph C) :
    (Quot.mk (RootedContractRel Q (· = C)) a = Quot.mk _ b) ↔ a = b := by
  rw [mk_eq_mk_iff hC]
  exact ⟨fun h => h.resolve_right fun h' => hb h'.2, Or.inl⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The arcs of `Q₀⊕` are the arcs off `C`. -/
theorem notMem_of_contract {e : E} (he : ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C') (hC : IsCycle Q.graph C) :
    e ∉ C :=
  he C hC rfl

omit [Fintype V] [Fintype E] [Fintype X] in
theorem source_mem_cycleNodes {e : E} (he : e ∈ C) : Q.graph.source e ∈ cycleNodes Q.graph C :=
  ⟨e, he, Or.inl rfl⟩

omit [Fintype V] [Fintype E] [Fintype X] in
theorem target_mem_cycleNodes {e : E} (he : e ∈ C) : Q.graph.target e ∈ cycleNodes Q.graph C :=
  ⟨e, he, Or.inr rfl⟩

/-! ### Below a vertex whose descendants avoid the cycle -/

variable {z : V}

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A path of `Q⊕` below `z` is a path of `Q₀⊕`. -/
theorem reaches_contract_of_reaches (hS : ∀ w, Q.graph.Reaches z w → w ∉ cycleNodes Q.graph C)
    {w : V} (h : Q.graph.Reaches z w) :
    (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ z) (Quot.mk _ w) := by
  induction h with
  | refl => exact .refl
  | @tail a b hza hab ih =>
    obtain ⟨e, rfl, rfl⟩ := hab
    have he : e ∉ C := fun he => hS _ hza (source_mem_cycleNodes he)
    exact ih.tail ⟨⟨e, fun C' _ hC' => hC' ▸ he⟩, rfl, rfl⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A path of `Q₀⊕` from `z` is a path of `Q⊕` from `z`. -/
theorem exists_of_reaches_contract (hC : IsCycle Q.graph C)
    (hS : ∀ w, Q.graph.Reaches z w → w ∉ cycleNodes Q.graph C)
    {W : Quot (RootedContractRel Q (· = C))}
    (h : (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ z) W) :
    ∃ w, Q.graph.Reaches z w ∧ Quot.mk _ w = W := by
  induction h with
  | refl => exact ⟨z, .refl, rfl⟩
  | @tail A B _ hAB ih =>
    obtain ⟨w, hw, rfl⟩ := ih
    obtain ⟨e, hs, rfl⟩ := hAB
    have hsw : Q.graph.source e.1 = w := (mk_eq_mk_iff_of_notMem' hC (hS w hw)).1 hs
    exact ⟨Q.graph.target e.1, hw.tail ⟨e.1, hsw, rfl⟩, rfl⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **Below `z`, the paths of `Q₀⊕` are those of `Q⊕`.** -/
theorem reaches_contract_iff (hC : IsCycle Q.graph C)
    (hS : ∀ w, Q.graph.Reaches z w → w ∉ cycleNodes Q.graph C) (w : V) :
    (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ z) (Quot.mk _ w) ↔ Q.graph.Reaches z w := by
  refine ⟨fun h => ?_, reaches_contract_of_reaches hS⟩
  obtain ⟨w', hw', he⟩ := exists_of_reaches_contract hC hS h
  rwa [← (mk_eq_mk_iff_of_notMem hC (hS w' hw')).1 he]

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A cut vertex whose descendants avoid `C` is a cut vertex of `Q₀⊕`. -/
theorem isCut_contract (hC : IsCycle Q.graph C) (hc : IsCut Q z)
    (hS : ∀ w, Q.graph.Reaches z w → w ∉ cycleNodes Q.graph C) :
    IsCut (contractRooted Q (· = C)) (Quot.mk _ z) := by
  refine ⟨fun h => ?_, fun e he hne => ?_⟩
  · exact hc.not_reaches_root ((reaches_contract_iff hC hS Q.root).1 h)
  · have ht : Q.graph.Reaches z (Q.graph.target e.1) := (reaches_contract_iff hC hS _).1 he
    have hne' : Q.graph.target e.1 ≠ z := fun h => hne (by
      change Quot.mk _ (Q.graph.target e.1) = Quot.mk _ z
      rw [h])
    exact (reaches_contract_iff hC hS _).2 (hc.entry e.1 ht hne')

/-- The vertices below `z` in `Q⊕` and in `Q₀⊕`. -/
def belowContractEquiv (hC : IsCycle Q.graph C)
    (hS : ∀ w, Q.graph.Reaches z w → w ∉ cycleNodes Q.graph C) :
    {w // Q.graph.Reaches z w} ≃
      {W // (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ z) W} :=
  Equiv.ofBijective (fun w => ⟨Quot.mk _ w.1, reaches_contract_of_reaches hS w.2⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext ((mk_eq_mk_iff_of_notMem hC (hS a.1 a.2)).1 (congrArg Subtype.val h))
    · rintro ⟨W, hW⟩
      obtain ⟨w, hw, rfl⟩ := exists_of_reaches_contract hC hS hW
      exact ⟨⟨w, hw⟩, rfl⟩)

/-- The arcs below `z` in `Q⊕` and in `Q₀⊕`. -/
def belowArcsContractEquiv (hC : IsCycle Q.graph C)
    (hS : ∀ w, Q.graph.Reaches z w → w ∉ cycleNodes Q.graph C) :
    {e // Q.graph.Reaches z (Q.graph.target e) ∧ Q.graph.target e ≠ z} ≃
      {e // (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ z)
          ((contractRooted Q (· = C)).graph.target e) ∧
        (contractRooted Q (· = C)).graph.target e ≠ Quot.mk _ z} :=
  Equiv.ofBijective (fun e => ⟨⟨e.1, fun C' _ hC' he => hS _ e.2.1
      (hC' ▸ target_mem_cycleNodes he)⟩,
    reaches_contract_of_reaches hS e.2.1,
    fun h => e.2.2 ((mk_eq_mk_iff_of_notMem hC (hS _ e.2.1)).1 h)⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (congrArg (fun e => e.1.1) h)
    · rintro ⟨e, he, hne⟩
      have ht : Q.graph.Reaches z (Q.graph.target e.1) := (reaches_contract_iff hC hS _).1 he
      refine ⟨⟨e.1, ht, fun h => hne (by
        change Quot.mk _ (Q.graph.target e.1) = Quot.mk _ z
        rw [h])⟩, rfl⟩)

/-- **The law of the forest arriving at `z` is the same in `Q⊕` and in `Q₀⊕`**, when no descendant of
`z` is a node of `C`. -/
theorem rootDist_cutLower_contract (hC : IsCycle Q.graph C) (hc : IsCut Q z)
    (hS : ∀ w, Q.graph.Reaches z w → w ∉ cycleNodes Q.graph C) (θ : MetricData E) (ρ : ℝ)
    (F : Finset (Finset X)) :
    rootDist (cutLower (contractRooted Q (· = C)) (Quot.mk _ z) (isCut_contract hC hc hS))
        (cutLowerMetric (contractRooted Q (· = C)) (Quot.mk _ z) (contractMetric Q (· = C) θ)) ρ
        (lowerInj (cutVertices (contractRooted Q (· = C)) (Quot.mk _ z))
          (taxaInj (contractRooted Q (· = C)) univ)) F =
      rootDist (cutLower Q z hc) (cutLowerMetric Q z θ) ρ
        (lowerInj (cutVertices Q z) (taxaInj Q univ)) F := by
  rw [rootDist_congr (N := cutLower Q z hc) (N' := cutLower (contractRooted Q (· = C))
      (Quot.mk _ z) (isCut_contract hC hc hS)) (θ := cutLowerMetric Q z θ)
    (θ' := cutLowerMetric (contractRooted Q (· = C)) (Quot.mk _ z) (contractMetric Q (· = C) θ))
    (belowContractEquiv hC hS) (belowArcsContractEquiv hC hS) (fun _ => rfl)
    (fun _ => rfl) rfl (fun _ => rfl) (fun _ => rfl)]
  congr 1
  funext w
  unfold lowerInj taxaInj
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, cutVertices_inr]
  change Quot.mk _ (Q.leaf x) = Quot.mk _ w.1 ↔ Q.leaf x = w.1
  exact mk_eq_mk_iff_of_notMem' hC (hS w.1 w.2)

/-! ### The contracted network is a phylogenetic network -/

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A path from outside a set into it enters it by an arc. -/
theorem exists_arc_enter {p : V → Prop} {a b : V} (h : Q.graph.Reaches a b) (ha : ¬ p a)
    (hb : p b) : ∃ e, ¬ p (Q.graph.source e) ∧ p (Q.graph.target e) := by
  induction h with
  | refl => exact absurd hb ha
  | @tail b c _ hbc ih =>
    obtain ⟨e, rfl, rfl⟩ := hbc
    by_cases hs : p (Q.graph.source e)
    · exact ih hs
    · exact ⟨e, hs, hb⟩


/-- The hypotheses on a cycle `C` under which `Q₀⊕` is a metric phylogenetic network: no taxon is a
node of `C`; a node `t` of `C` above all its nodes receives every arc into a node of `C` that is not
an edge of `C`, and no edge of `C` enters `t`; and an arc leaves a node of `C` off `C`. -/
structure IsContractible (Q : RootedNetwork V E X) (C : Set E) (t : V) : Prop where
  cycle : IsCycle Q.graph C
  leaf_notMem : ∀ x, Q.leaf x ∉ cycleNodes Q.graph C
  top_mem : t ∈ cycleNodes Q.graph C
  top_reaches : ∀ s ∈ cycleNodes Q.graph C, Q.graph.Reaches t s
  entry : ∀ e, e ∉ C → Q.graph.target e ∈ cycleNodes Q.graph C → Q.graph.target e = t
  top_entry : ∀ e, Q.graph.target e = t → e ∉ C
  exit : ∃ e, e ∉ C ∧ Q.graph.source e ∈ cycleNodes Q.graph C

namespace IsContractible

variable {t : V} (hK : IsContractible Q C t)
include hK

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The representative of a node of `Q₀⊕`: `t` for the node of `C`. -/
def rep : Quot (RootedContractRel Q (· = C)) → V :=
  Quot.lift (fun w => if w ∈ cycleNodes Q.graph C then t else w) fun a b hab => by
    obtain ⟨ha, hb⟩ := (rootedContractRel_iff hK.cycle).1 hab
    simp [ha, hb]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem rep_mk_of_notMem {w : V} (hw : w ∉ cycleNodes Q.graph C) : hK.rep (Quot.mk _ w) = w := by
  simp [rep, hw]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem rep_mk_of_mem {w : V} (hw : w ∈ cycleNodes Q.graph C) : hK.rep (Quot.mk _ w) = t := by
  simp [rep, hw]

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The target of an arc of `Q₀⊕` is represented by the target of the arc. -/
theorem rep_target (e : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'}) :
    hK.rep ((contractRooted Q (· = C)).graph.target e) = Q.graph.target e.1 := by
  change hK.rep (Quot.mk _ (Q.graph.target e.1)) = _
  by_cases h : Q.graph.target e.1 ∈ cycleNodes Q.graph C
  · rw [hK.rep_mk_of_mem h, hK.entry e.1 (e.2 C hK.cycle rfl) h]
  · rw [hK.rep_mk_of_notMem h]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem mk_rep (W : Quot (RootedContractRel Q (· = C))) : Quot.mk _ (hK.rep W) = W := by
  induction W using Quot.ind with
  | mk w =>
    by_cases h : w ∈ cycleNodes Q.graph C
    · rw [hK.rep_mk_of_mem h]
      exact (mk_eq_mk_iff hK.cycle).2 (Or.inr ⟨hK.top_mem, h⟩)
    · rw [hK.rep_mk_of_notMem h]

omit [Fintype V] [Fintype E] [Fintype X] in
/-- An arc of `Q₀⊕` goes down in `Q⊕` between the representatives. -/
theorem transGen_rep_of_adj {W W' : Quot (RootedContractRel Q (· = C))}
    (h : (contractRooted Q (· = C)).graph.Adj W W') :
    Relation.TransGen Q.graph.Adj (hK.rep W) (hK.rep W') := by
  obtain ⟨e, rfl, rfl⟩ := h
  rw [hK.rep_target]
  change Relation.TransGen Q.graph.Adj (hK.rep (Quot.mk _ (Q.graph.source e.1))) _
  by_cases hs : Q.graph.source e.1 ∈ cycleNodes Q.graph C
  · rw [hK.rep_mk_of_mem hs]
    exact Relation.TransGen.tail' (hK.top_reaches _ hs) ⟨e.1, rfl, rfl⟩
  · rw [hK.rep_mk_of_notMem hs]
    exact .single ⟨e.1, rfl, rfl⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The arcs of `Q₀⊕` into a node are the arcs of `Q⊕` into its representative. -/
theorem target_eq_iff (e : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'})
    (W : Quot (RootedContractRel Q (· = C))) :
    (contractRooted Q (· = C)).graph.target e = W ↔ Q.graph.target e.1 = hK.rep W := by
  constructor
  · rintro rfl
    exact (hK.rep_target e).symm
  · intro h
    rw [← hK.mk_rep W, ← h]
    rfl

omit [Fintype V] [Fintype E] [Fintype X] in
/-- An arc of `Q⊕` into a representative is off `C`. -/
theorem notMem_of_target_eq_rep {e : E} {W : Quot (RootedContractRel Q (· = C))}
    (h : Q.graph.target e = hK.rep W) : e ∉ C := by
  induction W using Quot.ind with
  | mk w =>
    by_cases hw : w ∈ cycleNodes Q.graph C
    · rw [hK.rep_mk_of_mem hw] at h
      exact hK.top_entry e h
    · rw [hK.rep_mk_of_notMem hw] at h
      exact fun he => hw (h ▸ target_mem_cycleNodes he)

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The arcs into a node of `Q₀⊕` and into its representative. -/
theorem indegree_contract (W : Quot (RootedContractRel Q (· = C))) :
    (contractRooted Q (· = C)).graph.indegree W = Q.graph.indegree (hK.rep W) := by
  unfold DirectedMultigraph.indegree
  refine Set.ncard_congr (fun e _ => e.1) (fun e he => (hK.target_eq_iff e W).1 he)
    (fun a b _ _ h => Subtype.ext h) fun e he => ?_
  exact ⟨⟨e, fun C' _ hC' => hC' ▸ hK.notMem_of_target_eq_rep he⟩, (hK.target_eq_iff _ W).2 he, rfl⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A path of `Q⊕` is a path of `Q₀⊕`. -/
theorem reaches_contract {a b : V} (h : Q.graph.Reaches a b) :
    (contractRooted Q (· = C)).graph.Reaches (Quot.mk _ a) (Quot.mk _ b) := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨e, rfl, rfl⟩ := hbc
    by_cases he : e ∈ C
    · have : Quot.mk (RootedContractRel Q (· = C)) (Q.graph.source e) =
          Quot.mk _ (Q.graph.target e) :=
        (mk_eq_mk_iff hK.cycle).2 (Or.inr ⟨source_mem_cycleNodes he, target_mem_cycleNodes he⟩)
      rwa [← this]
    · exact ih.tail ⟨⟨e, fun C' _ hC' => hC' ▸ he⟩, rfl, rfl⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **`Q₀⊕` is a phylogenetic network.** -/
theorem isPhylogenetic (hQ : Q.IsPhylogenetic) : (contractRooted Q (· = C)).IsPhylogenetic := by
  have : Finite E := hQ.finite_arcs
  have : Finite V := hQ.finite_vertices
  have : Finite X := hQ.finite_taxa
  have hleafeq : ∀ x (W : Quot (RootedContractRel Q (· = C))),
      (contractRooted Q (· = C)).leaf x = W ↔ Q.leaf x = hK.rep W := by
    intro x W
    constructor
    · rintro rfl
      exact (hK.rep_mk_of_notMem (hK.leaf_notMem x)).symm
    · intro h
      rw [← hK.mk_rep W, ← h]
      rfl
  refine
    { finite_vertices := inferInstance
      finite_arcs := inferInstance
      finite_taxa := inferInstance
      acyclic := fun W hW => ?_
      root_reaches := fun W => ?_
      root_indegree := ?_
      nonroot_indegree := fun W hW => ?_
      leaf_injective := fun x y h => ?_
      leaf_indegree := fun x => ?_
      leaves := fun W => ?_ }
  · have hl : ∀ A B, Relation.TransGen (contractRooted Q (· = C)).graph.Adj A B →
        Relation.TransGen Q.graph.Adj (hK.rep A) (hK.rep B) := by
      intro A B h
      induction h with
      | single h => exact hK.transGen_rep_of_adj h
      | tail _ h ih => exact ih.trans (hK.transGen_rep_of_adj h)
    exact hQ.acyclic _ (hl W W hW)
  · rw [← hK.mk_rep W]
    exact hK.reaches_contract (hQ.root_reaches _)
  · rw [hK.indegree_contract]
    by_cases hr : Q.root ∈ cycleNodes Q.graph C
    · change Q.graph.indegree (hK.rep (Quot.mk _ Q.root)) = 0
      rw [hK.rep_mk_of_mem hr]
      have ht : t = Q.root := by
        have hrt := hK.top_reaches _ hr
        by_contra hne
        obtain ⟨e, -, he⟩ := exists_arc_enter (p := fun w => w = Q.root) hrt hne rfl
        exact (Q.graph.indegree_eq_zero_iff _).1 hQ.root_indegree e he
      rw [ht]
      exact hQ.root_indegree
    · change Q.graph.indegree (hK.rep (Quot.mk _ Q.root)) = 0
      rw [hK.rep_mk_of_notMem hr]
      exact hQ.root_indegree
  · rw [hK.indegree_contract]
    refine hQ.nonroot_indegree _ fun h => hW ?_
    rw [← hK.mk_rep W, h]
    rfl
  · exact hQ.leaf_injective ((mk_eq_mk_iff_of_notMem hK.cycle (hK.leaf_notMem x)).1 h)
  · rw [hK.indegree_contract, ← (hleafeq x _).1 rfl]
    exact hQ.leaf_indegree x
  · rw [(contractRooted Q (· = C)).graph.outdegree_eq_zero_iff]
    induction W using Quot.ind with
    | mk w =>
      by_cases hw : w ∈ cycleNodes Q.graph C
      · constructor
        · intro h0
          obtain ⟨e, he, hs⟩ := hK.exit
          exact absurd ((mk_eq_mk_iff hK.cycle).2 (Or.inr ⟨hs, hw⟩))
            (h0 ⟨e, fun C' _ hC' => hC' ▸ he⟩)
        · rintro ⟨x, hx⟩
          exact absurd ((mk_eq_mk_iff_of_notMem hK.cycle (hK.leaf_notMem x)).1 hx ▸ hw)
            (hK.leaf_notMem x)
      · have hiff : (∃ x, (contractRooted Q (· = C)).leaf x = Quot.mk _ w) ↔ ∃ x, Q.leaf x = w :=
          exists_congr fun x => mk_eq_mk_iff_of_notMem hK.cycle (hK.leaf_notMem x)
        rw [hiff, ← hQ.leaves, Q.graph.outdegree_eq_zero_iff]
        constructor
        · intro h e he
          exact h ⟨e, fun C' _ hC' hC => hw (he ▸ hC' ▸ source_mem_cycleNodes hC)⟩ (by
            change Quot.mk _ (Q.graph.source e) = _
            rw [he])
        · intro h e he
          exact h e.1 ((mk_eq_mk_iff_of_notMem' hK.cycle hw).1 he)

omit [Fintype V] [Fintype X] in
/-- **`Q₀⊕` with the parameters of the remaining edges is a metric network.** -/
theorem isMetric {θ : MetricData E} (hθ : Q.IsMetric θ) :
    (contractRooted Q (· = C)).IsMetric (contractMetric Q (· = C) θ) := by
  have htree : ∀ e : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'},
      (contractRooted Q (· = C)).IsTreeArc e ↔ Q.IsTreeArc e.1 := by
    intro e
    unfold RootedNetwork.IsTreeArc
    rw [hK.indegree_contract, hK.rep_target]
  have hhyb : ∀ e : {e // ∀ C', IsCycle Q.graph C' → C' = C → e ∉ C'},
      (contractRooted Q (· = C)).IsHybridArc e ↔ Q.IsHybridArc e.1 := by
    intro e
    unfold RootedNetwork.IsHybridArc
    rw [hK.indegree_contract, hK.rep_target]
  refine ⟨fun e he => hθ.1 e.1 ((htree e).1 he), fun e he => hθ.2.1 e.1 ((hhyb e).1 he),
    fun e he => hθ.2.2.1 e.1 ((htree e).1 he), fun e he => hθ.2.2.2.1 e.1 ((hhyb e).1 he),
    fun W hW => ?_⟩
  rw [hK.indegree_contract] at hW
  rw [← hθ.2.2.2.2 _ hW, ← sum_filter, ← sum_filter]
  refine sum_bij (fun e _ => e.1) (fun e he => ?_) (fun a _ b _ h => Subtype.ext h)
    (fun e he => ?_) fun e _ => rfl
  · exact mem_filter.2 ⟨mem_univ _, (hK.target_eq_iff e W).1 (mem_filter.1 he).2⟩
  · have hne := hK.notMem_of_target_eq_rep (mem_filter.1 he).2
    exact ⟨⟨e, fun C' _ hC' => hC' ▸ hne⟩,
      mem_filter.2 ⟨mem_univ _, (hK.target_eq_iff _ W).2 (mem_filter.1 he).2⟩, rfl⟩

end IsContractible

omit [Fintype X] in
/-- **Every cycle of a binary level-1 network can be contracted**: its top `t` receives every arc
into the cycle off it (Lemma 3 and the orientation of the cycle). -/
theorem isContractible_of_cycle (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
    (hC : IsCycle Q.graph C) {v : V} (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2) :
    ∃ t, IsContractible Q C t := by
  have := hQ.1.finite_arcs
  obtain ⟨t, ⟨htS, ht0⟩, htu⟩ := existsUnique_top hQ h1 hC hv h2
  have hnz : ∀ s ∈ cycleNodes Q.graph C, s ≠ t → ∃ e ∈ C, Q.graph.target e = s := by
    intro s hs hst
    have h0 : inCycle (N := Q) C s ≠ 0 := fun h0 => hst (htu s ⟨hs, h0⟩)
    obtain ⟨e, he⟩ := card_pos.1 (Nat.pos_of_ne_zero h0)
    exact ⟨e, (mem_filter.1 he).2.1, (mem_filter.1 he).2.2⟩
  have hnotC : ∀ e, Q.graph.target e = t → e ∉ C := fun e he hC' => by
    have : e ∈ univ.filter fun e => e ∈ C ∧ Q.graph.target e = t :=
      mem_filter.2 ⟨mem_univ _, hC', he⟩
    have hpos := card_pos.2 ⟨e, this⟩
    unfold inCycle at ht0
    omega
  refine ⟨t, ⟨hC, fun x hx => ?_, htS, fun s hs => ?_, fun e he hs => ?_, hnotC, ?_⟩⟩
  · -- a taxon has one incident arc
    have hinc := hC.ncard_incident (source_ne_target_of_binary hQ) hx
    have hout := (hQ.1.leaves (Q.leaf x)).2 ⟨x, rfl⟩
    have hsub : {e | e ∈ C ∧ (Q.graph.source e = Q.leaf x ∨ Q.graph.target e = Q.leaf x)} ⊆
        {e | Q.graph.target e = Q.leaf x} := fun e he =>
      he.2.resolve_left fun h => (Q.graph.outdegree_eq_zero_iff _).1 hout e h
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h1x := hQ.1.leaf_indegree x
    unfold DirectedMultigraph.indegree at h1x
    omega
  · have := hQ.1.finite_vertices
    let rel : V → V → Prop := fun a c => Relation.TransGen Q.graph.Adj a c
    have : IsTrans V rel := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
    have : Std.Irrefl rel := ⟨fun a ha => hQ.1.acyclic a ha⟩
    have hwf : WellFounded rel := Finite.wellFounded_of_trans_of_irrefl rel
    induction s using hwf.induction with
    | _ s ih =>
      by_cases hst : s = t
      · rw [hst]
        exact .refl
      · obtain ⟨e, he, het⟩ := hnz s hs hst
        exact (ih _ (.single ⟨e, rfl, het⟩) (source_mem_cycleNodes he)).tail ⟨e, rfl, het⟩
  · by_contra hst
    obtain ⟨e', he', he't⟩ := hnz _ hs hst
    by_cases hsv : Q.graph.target e = v
    · exact he (mem_of_target_eq_hybrid hQ h1 hC hv h2 hsv)
    · have hle := indegree_le_one_of_mem hQ h1 hC hv h2 hs hsv
      have hne : e ≠ e' := fun h => he (h ▸ he')
      have := two_le_indegree_of_two_targets hQ hne rfl he't
      omega
  · obtain ⟨c, hc, -⟩ := existsUnique_child_of_hybrid hQ h2
    exact ⟨c, notMem_of_source_eq_hybrid hQ h1 hC hv h2 hc, hc ▸ hv⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **The child of a hybrid node is a cut vertex**, entered only by the child arc `c` of the hybrid
node. -/
theorem isCut_child_of_hybrid (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph) {v : V}
    (h2 : Q.graph.indegree v = 2) {c : E} (hc : Q.graph.source c = v)
    (huniq : ∀ g, Q.graph.source g = v → g = c) :
    IsCut Q (Q.graph.target c) ∧ ∀ g, Q.graph.target g = Q.graph.target c → g = c := by
  have hvz : Q.graph.Reaches v (Q.graph.target c) := .single ⟨c, hc, rfl⟩
  have hzv : Q.graph.target c ≠ v := fun h => hQ.1.acyclic v (.single ⟨c, hc, h⟩)
  have := hQ.1.finite_arcs
  have hnot : ∀ w, Q.graph.Reaches (Q.graph.target c) w → w ≠ v := fun w hw hwv =>
    hQ.1.acyclic v (Relation.TransGen.head' ⟨c, hc, rfl⟩ (hwv ▸ hw))
  have hsrc : ∀ g, Q.graph.Reaches (Q.graph.target c) (Q.graph.target g) →
      Q.graph.source g = v ∨ Q.graph.Reaches (Q.graph.target c) (Q.graph.source g) := by
    intro g hg
    have hs := reaches_source_of_below_hybrid hQ h1 h2 (hvz.trans hg) (hnot _ hg)
    exact eq_or_reaches_of_unique_child huniq hs
  refine ⟨⟨fun hr => ?_, fun g hg hne => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨g, -, hg⟩ := exists_arc_enter (p := fun w => w = Q.root) hr
      (fun h => (Q.graph.indegree_eq_zero_iff _ |>.1 hQ.1.root_indegree) c h) rfl
    exact (Q.graph.indegree_eq_zero_iff _ |>.1 hQ.1.root_indegree) g hg
  · rcases hsrc g hg with hs | hs
    · exact absurd (congrArg Q.graph.target (huniq g hs)) hne
    · exact hs
  · rcases hsrc g (hg ▸ .refl) with hs | hs
    · exact huniq g hs
    · exact absurd (Relation.TransGen.tail' hs ⟨g, rfl, hg⟩) (hQ.1.acyclic _)

end Contract

/-! ### Deleting an arc away from the part below a vertex -/

section Delete

variable {Q : RootedNetwork V E X} {h : E} {z : V}

omit [Fintype V] [Fintype E] [Fintype X] in
/-- Below `z`, when `h` leaves no vertex below `z`, the paths without `h` are those of `Q⊕`. -/
theorem reaches_deleteArc_iff (hS : ∀ w, Q.graph.Reaches z w → Q.graph.source h ≠ w) (w : V) :
    (deleteArc Q h).graph.Reaches z w ↔ Q.graph.Reaches z w := by
  constructor
  · intro hr
    induction hr with
    | refl => exact .refl
    | tail _ hab ih =>
      obtain ⟨e, rfl, rfl⟩ := hab
      exact ih.tail ⟨e.1, rfl, rfl⟩
  · intro hr
    induction hr with
    | refl => exact .refl
    | @tail a b hza hab ih =>
      obtain ⟨e, rfl, rfl⟩ := hab
      have he : e ≠ h := fun he => hS _ hza (he ▸ rfl)
      exact ih.tail ⟨⟨e, he⟩, rfl, rfl⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A cut vertex below which `h` leaves no vertex is a cut vertex without `h`. -/
theorem isCut_deleteArc (hc : IsCut Q z) (hS : ∀ w, Q.graph.Reaches z w → Q.graph.source h ≠ w) :
    IsCut (deleteArc Q h) z := by
  refine ⟨fun hr => hc.not_reaches_root ((reaches_deleteArc_iff hS _).1 hr), fun e he hne => ?_⟩
  exact (reaches_deleteArc_iff hS _).2 (hc.entry e.1 ((reaches_deleteArc_iff hS _).1 he) hne)

/-- The arcs below `z` with and without `h`. -/
def belowArcsDeleteEquiv (hc : IsCut Q z) (hS : ∀ w, Q.graph.Reaches z w → Q.graph.source h ≠ w) :
    {e // Q.graph.Reaches z (Q.graph.target e) ∧ Q.graph.target e ≠ z} ≃
      {e // (deleteArc Q h).graph.Reaches z ((deleteArc Q h).graph.target e) ∧
        (deleteArc Q h).graph.target e ≠ z} where
  toFun e := ⟨⟨e.1, fun he => hS _ (hc.entry e.1 e.2.1 e.2.2) (he ▸ rfl)⟩,
    (reaches_deleteArc_iff hS _).2 e.2.1, e.2.2⟩
  invFun e := ⟨e.1.1, (reaches_deleteArc_iff hS _).1 e.2.1, e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The law of the forest arriving at `z` is the same without `h`**, when `h` leaves no vertex below
`z`. -/
theorem rootDist_cutLower_deleteArc (hc : IsCut Q z)
    (hS : ∀ w, Q.graph.Reaches z w → Q.graph.source h ≠ w) (θ : MetricData E) (ρ : ℝ)
    (F : Finset (Finset X)) :
    rootDist (cutLower (deleteArc Q h) z (isCut_deleteArc hc hS))
        (cutLowerMetric (deleteArc Q h) z (deleteArcMetric Q h θ)) ρ
        (lowerInj (cutVertices (deleteArc Q h) z) (taxaInj (deleteArc Q h) univ)) F =
      rootDist (cutLower Q z hc) (cutLowerMetric Q z θ) ρ
        (lowerInj (cutVertices Q z) (taxaInj Q univ)) F := by
  have hinh : ∀ e : {e // Q.graph.Reaches z (Q.graph.target e) ∧ Q.graph.target e ≠ z},
      (cutLowerMetric (deleteArc Q h) z (deleteArcMetric Q h θ)).inheritance
        (belowArcsDeleteEquiv hc hS e) = (cutLowerMetric Q z θ).inheritance e := by
    intro e
    simp only [cutLowerMetric, deleteArcMetric, belowArcsDeleteEquiv, Equiv.coe_fn_mk]
    have hne : Q.graph.target e.1 ≠ Q.graph.target h := by
      intro heq
      have hth : Q.graph.Reaches z (Q.graph.target h) := heq ▸ e.2.1
      exact hS _ (hc.entry h hth (heq ▸ e.2.2)) rfl
    rw [ite_eq_right hne]
  rw [rootDist_congr (N := cutLower Q z hc) (N' := cutLower (deleteArc Q h) z (isCut_deleteArc hc hS))
    (θ := cutLowerMetric Q z θ) (θ' := cutLowerMetric (deleteArc Q h) z (deleteArcMetric Q h θ))
    (Equiv.subtypeEquivRight fun w => (reaches_deleteArc_iff hS w).symm)
    (belowArcsDeleteEquiv hc hS) (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl) hinh]
  rfl

end Delete

end Banos2019
