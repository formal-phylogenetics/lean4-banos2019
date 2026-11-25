module

public import Banos2019.Quartet.Reduce
public import Banos2019.Quartet.CutSplits

/-!
# The network without a hybrid edge (`Q₁⊕`, `Q₂⊕` of Lemmas 9 and 10)

For a hybrid edge `h` of a cycle `C` of a binary level-1 network `Q`, `deleteArc Q h` has two nodes
of indegree one and outdegree one, the source of `h` (unless it is the root) and the hybrid node `v`
of `C`; both are on `C` only. It satisfies `IsReducible`, its cycles are those of `Q` other than
`C`, with the same types, and, for a cycle inducing a `2₂`- or a `3₁`-cycle, it has the cut edges of
`Q` between two pairs of taxa.

* `deleteArc_reaches_of_notMem`: from a node off `C`, the paths of `Q` can avoid `h`: they enter `C`
  at its top, from which `v` is reached along the other side of `C`.
* `isReducible_deleteArc`, `deleteArc_exists_inducesCycleType_iff`,
  `ncard_setOf_isCycle_deleteArc_lt`, `deleteArc_hasCutSplit_iff`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-- The elements of a subtype `{e // e ≠ h}` satisfying `p`, and `h` if it satisfies `p`, are the
elements satisfying `p`. -/
theorem ncard_subtype_ne_add [Finite E] (h : E) (p : E → Prop) :
    {e : {e // e ≠ h} | p e.1}.ncard + (if p h then 1 else 0) = {e | p e}.ncard := by
  have himg : Subtype.val '' {e : {e // e ≠ h} | p e.1} = {e | p e} \ {h} := by
    ext e
    constructor
    · rintro ⟨e', he', rfl⟩
      exact ⟨he', e'.2⟩
    · rintro ⟨he, hne⟩
      exact ⟨⟨e, hne⟩, he, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
  split_ifs with hp
  · exact Set.ncard_sdiff_singleton_add_one hp (Set.toFinite _)
  · rw [Set.sdiff_singleton_eq_self hp, add_zero]

variable {Q : RootedNetwork V E X} {h : E}

theorem deleteArc_indegree [Finite E] (w : V) :
    (deleteArc Q h).graph.indegree w + (if Q.graph.target h = w then 1 else 0) =
      Q.graph.indegree w :=
  ncard_subtype_ne_add h (fun e => Q.graph.target e = w)

theorem deleteArc_outdegree [Finite E] (w : V) :
    (deleteArc Q h).graph.outdegree w + (if Q.graph.source h = w then 1 else 0) =
      Q.graph.outdegree w :=
  ncard_subtype_ne_add h (fun e => Q.graph.source e = w)

/-- A path without `h` is a path of `Q`. -/
theorem reaches_of_deleteArc {a b : V} (hr : (deleteArc Q h).graph.Reaches a b) :
    Q.graph.Reaches a b := by
  induction hr with
  | refl => exact .refl
  | tail _ hab ih =>
    obtain ⟨e, rfl, rfl⟩ := hab
    exact ih.tail ⟨e.1, rfl, rfl⟩

/-- A path of `Q` avoids `h`, or goes to the source of `h` and from its target without it. -/
theorem deleteArc_reaches_or {a b : V} (hr : Q.graph.Reaches a b) :
    (deleteArc Q h).graph.Reaches a b ∨ ((deleteArc Q h).graph.Reaches a (Q.graph.source h) ∧
      (deleteArc Q h).graph.Reaches (Q.graph.target h) b) := by
  induction hr with
  | refl => exact Or.inl .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, rfl, rfl⟩ := hbc
    by_cases hf : f = h
    · subst hf
      rcases ih with ih | ih
      · exact Or.inr ⟨ih, .refl⟩
      · exact Or.inr ⟨ih.1, .refl⟩
    · rcases ih with ih | ih
      · exact Or.inl (ih.tail ⟨⟨f, hf⟩, rfl, rfl⟩)
      · exact Or.inr ⟨ih.1, ih.2.tail ⟨⟨f, hf⟩, rfl, rfl⟩⟩

/-- **From a node off the cycle `C` of `h`, the paths of `Q` can avoid `h`**: a path through `h`
enters `C` at its top `t`, from which the target of `h` is reached along the other hybrid edge `h'`.
-/
theorem deleteArc_reaches_of_notMem (hA : Q.graph.IsAcyclic) {C : Set E} {t : V}
    (hK : IsContractible Q C t) (hhC : h ∈ C) {h' : E} (hne : h' ≠ h) (hh'C : h' ∈ C)
    (ht : Q.graph.target h' = Q.graph.target h) {u z : V} (hu : u ∉ cycleNodes Q.graph C)
    (hr : Q.graph.Reaches u z) : (deleteArc Q h).graph.Reaches u z := by
  have htv : t ≠ Q.graph.target h := fun he => hK.top_entry h he.symm hhC
  -- from the top to the target of `h` without `h`
  have hR2 : (deleteArc Q h).graph.Reaches t (Q.graph.target h) := by
    rcases deleteArc_reaches_or (h := h)
      (hK.top_reaches _ (source_mem_cycleNodes hh'C)) with h₁ | h₁
    · exact h₁.tail ⟨⟨h', hne⟩, rfl, ht⟩
    · exact absurd (Relation.TransGen.tail' (reaches_of_deleteArc h₁.2) ⟨h', rfl, ht⟩) (hA _)
  -- from `u` to a node of `C`, through the top
  have hR3 : ∀ w ∈ cycleNodes Q.graph C, Q.graph.Reaches u w → Q.graph.Reaches u t := by
    intro w hw huw
    obtain ⟨e, he, hs, het⟩ := exists_arc_enter' (p := (· ∈ cycleNodes Q.graph C)) huw hu hw
    have heC : e ∉ C := fun h => hs (source_mem_cycleNodes h)
    exact he.tail ⟨e, rfl, hK.entry e heC het⟩
  have hR4 : Q.graph.Reaches u t → (deleteArc Q h).graph.Reaches u t := by
    intro hut
    rcases deleteArc_reaches_or (h := h) hut with h₁ | h₁
    · exact h₁
    · exact absurd (eq_of_reaches_of_reaches hA (hK.top_reaches _ (target_mem_cycleNodes hhC))
        (reaches_of_deleteArc h₁.2)) htv
  rcases deleteArc_reaches_or (h := h) hr with h₁ | h₁
  · exact h₁
  · exact ((hR4 (hR3 _ (source_mem_cycleNodes hhC) (reaches_of_deleteArc h₁.1))).trans hR2).trans
      h₁.2

/-! ### The network without `h` -/

section Delete

variable {C : Set E} {v : V} {n k : ℕ}

theorem deleteArc_graph_source (e : {e // e ≠ h}) :
    (deleteArc Q h).graph.source e = Q.graph.source e.1 := rfl

theorem deleteArc_graph_target (e : {e // e ≠ h}) :
    (deleteArc Q h).graph.target e = Q.graph.target e.1 := rfl

/-- The cycles of `deleteArc Q h` are cycles of `Q`, with the same nodes. -/
theorem deleteArc_isCycle_image {D : Set {e // e ≠ h}} (hD : IsCycle (deleteArc Q h).graph D) :
    IsCycle Q.graph (Subtype.val '' D) ∧
      cycleNodes Q.graph (Subtype.val '' D) = cycleNodes (deleteArc Q h).graph D := by
  have hs : ∀ e : {e // e ≠ h}, e ∈ D →
      Q.graph.source e.1 = id ((deleteArc Q h).graph.source e) := fun _ _ => rfl
  have ht : ∀ e : {e // e ≠ h}, e ∈ D →
      Q.graph.target e.1 = id ((deleteArc Q h).graph.target e) := fun _ _ => rfl
  refine ⟨hD.image id Subtype.val Function.injective_id.injOn Subtype.val_injective.injOn hs ht, ?_⟩
  rw [cycleNodes_image id Subtype.val hs ht, Set.image_id]

/-- A cycle of `Q` without `h` is a cycle of `deleteArc Q h`. -/
theorem deleteArc_exists_isCycle {D : Set E} (hD : IsCycle Q.graph D) (hhD : h ∉ D) :
    ∃ D', IsCycle (deleteArc Q h).graph D' ∧ Subtype.val '' D' = D := by
  have hDψ : D ⊆ Set.range (Subtype.val : {e // e ≠ h} → E) :=
    fun f hf => ⟨⟨f, fun hfh => hhD (hfh ▸ hf)⟩, rfl⟩
  exact ⟨_, hD.preimage (G' := (deleteArc Q h).graph) id Subtype.val Function.injective_id
    Subtype.val_injective hDψ (fun w _ => ⟨w, rfl⟩)
    (fun (e : {e // e ≠ h}) _ => show Q.graph.source e.1 = id (Q.graph.source e.1) from rfl)
    (fun (e : {e // e ≠ h}) _ => show Q.graph.target e.1 = id (Q.graph.target e.1) from rfl),
    Set.image_preimage_eq_of_subset hDψ⟩

variable (hQ : IsBinaryRootedNetwork Q) (h1 : IsLevelOne Q.graph)
  (hC : InducesCycleType Q C v n k) (hhv : Q.graph.target h = v)
include hQ h1 hC hhv

omit hQ h1 hhv in
/-- The other hybrid edge of `v`. -/
theorem exists_other_hybrid : ∃ h', h' ≠ h ∧ Q.graph.target h' = v := by
  obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 hC.2.2.1
  have hx : Q.graph.target x = v := (Set.ext_iff.1 hs x).2 (Or.inl rfl)
  have hy : Q.graph.target y = v := (Set.ext_iff.1 hs y).2 (Or.inr rfl)
  by_cases hxh : x = h
  · exact ⟨y, fun hyh => hxy (hxh.trans hyh.symm), hy⟩
  · exact ⟨x, hxh, hx⟩

theorem hybrid_mem_cycle : h ∈ C := by
  have := hQ.1.finite_arcs
  exact mem_of_target_eq_hybrid hQ h1 hC.1 hC.2.1 hC.2.2.1 hhv

/-- The source of `h` has outdegree two and indegree one unless it is the root. -/
theorem source_hybrid_degrees :
    Q.graph.outdegree (Q.graph.source h) = 2 ∧
      (Q.graph.source h ≠ Q.root → Q.graph.indegree (Q.graph.source h) = 1) := by
  have := hQ.1.finite_arcs
  have hhC := hybrid_mem_cycle hQ h1 hC hhv
  have hsv : Q.graph.source h ≠ v := fun he => hQ.1.acyclic _ (.single ⟨h, he, hhv⟩)
  by_cases hsr : Q.graph.source h = Q.root
  · exact ⟨hsr ▸ hQ.2.1, fun h' => absurd hsr h'⟩
  · have hle := indegree_le_one_of_mem hQ h1 hC.1 hC.2.1 hC.2.2.1 (source_mem_cycleNodes hhC) hsv
    have h1' := hQ.1.nonroot_indegree _ hsr
    have h0 : Q.graph.outdegree (Q.graph.source h) ≠ 0 := fun h0 =>
      (Q.graph.outdegree_eq_zero_iff _).1 h0 h rfl
    have := hQ.2.2 _ hsr h0
    exact ⟨by omega, fun _ => by omega⟩

omit h1 hC in
/-- **The chain nodes of `deleteArc Q h` are the source of `h` and `v`.** -/
theorem eq_of_isChainVertex_deleteArc {w : V} (hw : (deleteArc Q h).IsChainVertex w) :
    w = Q.graph.source h ∨ w = v := by
  have := hQ.1.finite_arcs
  by_contra hne
  push Not at hne
  have hin := deleteArc_indegree (Q := Q) (h := h) w
  have hout := deleteArc_outdegree (Q := Q) (h := h) w
  rw [ite_eq_right (fun h' => hne.2 (hhv ▸ h'.symm)), hw.1] at hin
  rw [ite_eq_right (fun h' => hne.1 h'.symm), hw.2] at hout
  have hwr : w ≠ Q.root := fun h' => by
    rw [h', hQ.1.root_indegree] at hin
    omega
  have := hQ.2.2 w hwr (by omega)
  omega

/-- **The nodes of the cycles of `deleteArc Q h` are off `C`.** -/
theorem notMem_cycleNodes_of_deleteArc {D : Set {e // e ≠ h}}
    (hD : IsCycle (deleteArc Q h).graph D) {w : V} (hw : w ∈ cycleNodes (deleteArc Q h).graph D) :
    w ∉ cycleNodes Q.graph C := by
  have := hQ.1.finite_arcs
  intro hwC
  obtain ⟨hD', hnodes⟩ := deleteArc_isCycle_image hD
  have heq := (lemma3 hQ h1 hC.1).2.2 _ hD' ⟨w, hwC, hnodes ▸ hw⟩
  obtain ⟨e, -, he⟩ := (heq ▸ hybrid_mem_cycle hQ h1 hC hhv : h ∈ Subtype.val '' D)
  exact e.2 he

/-- **The network without `h` satisfies the hypotheses of `IsReducible`.** -/
theorem isReducible_deleteArc [Fintype E] {θ : MetricData E} (hθ : IsMetricNetwork Q θ)
    (htwo : ∃ x y : X, x ≠ y) (hn : 2 ≤ n) :
    IsReducible (deleteArc Q h) (deleteArcMetric Q h θ) := by
  have hhC := hybrid_mem_cycle hQ h1 hC hhv
  obtain ⟨h', hne, hh'⟩ := exists_other_hybrid (h := h) hC
  obtain ⟨hout2, hin1⟩ := source_hybrid_degrees hQ h1 hC hhv
  obtain ⟨g, hgh, hgs⟩ : ∃ g, g ≠ h ∧ Q.graph.source g = Q.graph.source h := by
    obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 hout2
    have hx : Q.graph.source x = Q.graph.source h := (Set.ext_iff.1 hs x).2 (Or.inl rfl)
    have hy : Q.graph.source y = Q.graph.source h := (Set.ext_iff.1 hs y).2 (Or.inr rfl)
    by_cases hxh : x = h
    · exact ⟨y, fun hyh => hxy (hxh.trans hyh.symm), hy⟩
    · exact ⟨x, hxh, hx⟩
  have hM := isPhylogenetic_deleteArc hQ.1 hne (hh'.trans hhv.symm) hgh hgs
  have hsv : Q.graph.source h ≠ v := fun he => hQ.1.acyclic _ (.single ⟨h, he, hhv⟩)
  have hv1 : Q.graph.outdegree v = 1 := by
    have hvr : v ≠ Q.root := fun he => by
      have := hQ.1.root_indegree
      rw [← he, hC.2.2.1] at this
      omega
    have h0 : Q.graph.outdegree v ≠ 0 := fun h0 => by
      obtain ⟨x, hx⟩ := (hQ.1.leaves v).1 h0
      have := hQ.1.leaf_indegree x
      rw [hx, hC.2.2.1] at this
      omega
    have := hQ.2.2 v hvr h0
    rw [hC.2.2.1] at this
    omega
  have hchainC : ∀ D, IsCycle (deleteArc Q h).graph D → ∀ w ∈ cycleNodes (deleteArc Q h).graph D,
      ¬ (deleteArc Q h).IsChainVertex w := by
    intro D hD w hw hc
    rcases eq_of_isChainVertex_deleteArc hQ hhv hc with rfl | rfl
    · exact notMem_cycleNodes_of_deleteArc hQ h1 hC hhv hD hw (source_mem_cycleNodes hhC)
    · exact notMem_cycleNodes_of_deleteArc hQ h1 hC hhv hD hw hC.2.1
  have hrootdeg : (deleteArc Q h).graph.outdegree Q.root +
    (if Q.graph.source h = Q.root then 1 else 0)
      = 2 := (deleteArc_outdegree (Q := Q) (h := h) Q.root).trans hQ.2.1
  refine
    { phylo := hM
      deg := fun w hwr h0 hnc => ?_
      root := ?_
      levelOne := IsLevelOne.of_injective h1 id Subtype.val Function.injective_id
        Subtype.val_injective (fun _ => rfl) (fun _ => rfl)
      chain := hchainC
      child := fun h1' e he D hD => ?_
      metric := isMetric_deleteArc hQ.1 hθ.1 hθ.2 hne (hh'.trans hhv.symm) (hhv ▸ hC.2.2.1)
      length := fun e => hθ.2 e.1
      two := htwo }
  · have hin := deleteArc_indegree (Q := Q) (h := h) w
    have hout := deleteArc_outdegree (Q := Q) (h := h) w
    have hwr' : w ≠ Q.root := hwr
    by_cases hwv : w = v
    · rw [hwv] at hin hout hnc
      rw [ite_eq_left hhv, hC.2.2.1] at hin
      rw [ite_eq_right (fun h' => hsv h'), hv1] at hout
      exact absurd ⟨by omega, by omega⟩ hnc
    by_cases hws : w = Q.graph.source h
    · rw [hws] at hin hout hnc hwr'
      rw [ite_eq_right (fun h' => hsv (h'.symm.trans hhv)), hin1 hwr'] at hin
      rw [ite_eq_left rfl, hout2] at hout
      exact absurd ⟨by omega, by omega⟩ hnc
    rw [ite_eq_right (fun h' => hwv (hhv ▸ h'.symm)), add_zero] at hin
    rw [ite_eq_right (fun h' => hws h'.symm), add_zero] at hout
    rw [hin, hout]
    exact hQ.2.2 w hwr' (by rw [← hout]; exact h0)
  · change (deleteArc Q h).graph.outdegree Q.root = 1 ∨ (deleteArc Q h).graph.outdegree Q.root = 2
    split_ifs at hrootdeg <;> omega
  · -- the root is the source of `h`, and its other child is a node of `C` other than `v`
    have hsr : Q.graph.source h = Q.root := by
      by_contra hsr
      rw [ite_eq_right hsr] at hrootdeg
      change (deleteArc Q h).graph.outdegree Q.root = 1 at h1'
      omega
    have he' : Q.graph.source e.1 = Q.root := he
    have heg : e.1 = g := by
      have := hQ.1.finite_arcs
      have hpair := eq_or_eq_of_outdegree_eq_two (N := Q) hQ.2.1 hgh (hgs.trans hsr) hsr
      have : e.1 ∈ {f | Q.graph.source f = Q.root} := he'
      rw [hpair] at this
      rcases this with h₁ | h₁
      · exact h₁
      · exact absurd h₁ e.2
    have hrC : Q.root ∈ cycleNodes Q.graph C := hsr ▸ source_mem_cycleNodes hhC
    have hgC : g ∈ C := mem_of_source_eq_root hQ hC.1 hrC (hgs.trans hsr)
    have hgv : Q.graph.target g ≠ v := by
      intro hgv
      -- `{g, h}` would be a cycle, hence `C`, of size two through the root
      have := hQ.1.finite_arcs
      obtain ⟨D, hD, hgD, hDsub⟩ := exists_isCycle_of_walks (G := Q.graph) (e := g) (F := {h})
        (fun h' => hgh (Set.mem_singleton_iff.1 h'))
        (.single ⟨h, rfl, Or.inr ⟨hsr.trans (hgs.trans hsr).symm, hhv.trans hgv.symm⟩⟩)
      have hDC := h1 D C hD hC.1 ⟨g, hgD, hgC⟩
      have hle : C.ncard ≤ 2 := by
        rw [← hDC]
        refine (Set.ncard_le_ncard (t := {g, h}) (fun f hf => ?_) (Set.toFinite _)).trans
          (Set.ncard_pair hgh).le
        rcases hDsub hf with rfl | hf
        · exact Or.inl rfl
        · exact Or.inr hf
      have hn' := hC.2.2.2.1
      rw [ite_eq_left hrC] at hn'
      omega
    have hnc : ¬ (deleteArc Q h).IsChainVertex (Q.graph.target g) := fun hc => by
      rcases eq_of_isChainVertex_deleteArc hQ hhv hc with h' | h'
      · exact hQ.1.target_ne_root g (h'.trans hsr)
      · exact hgv h'
    rw [deleteArc_graph_target, heg, chainEnd_eq_self hM hnc]
    exact fun hw => notMem_cycleNodes_of_deleteArc hQ h1 hC hhv hD hw (target_mem_cycleNodes hgC)

/-- **The cycles of `deleteArc Q h` are the cycles of `Q` other than `C`, with the same types**: the
taxa below a hybrid node off `C` are the same without `h` (`deleteArc_reaches_of_notMem`). -/
theorem deleteArc_exists_inducesCycleType_iff [Fintype V] [Fintype E] (n' k' : ℕ) (Dx : Set X) :
    (∃ D w, InducesCycleType (deleteArc Q h) D w n' k' ∧
        {x | (deleteArc Q h).graph.Reaches w ((deleteArc Q h).leaf x)} = Dx) ↔
      ∃ D w, D ≠ C ∧ InducesCycleType Q D w n' k' ∧ {x | Q.graph.Reaches w (Q.leaf x)} = Dx := by
  have := hQ.1.finite_arcs
  have hhC := hybrid_mem_cycle hQ h1 hC hhv
  obtain ⟨h', hne, hh'⟩ := exists_other_hybrid (h := h) hC
  have hh'C : h' ∈ C := mem_of_target_eq_hybrid hQ h1 hC.1 hC.2.1 hC.2.2.1 hh'
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ h1 hC.1 hC.2.1 hC.2.2.1
  -- the taxa below a node off `C`
  have hbelow : ∀ w, w ∉ cycleNodes Q.graph C →
      {x | (deleteArc Q h).graph.Reaches w ((deleteArc Q h).leaf x)} =
        {x | Q.graph.Reaches w (Q.leaf x)} := fun w hw => by
    ext x
    exact ⟨reaches_of_deleteArc, deleteArc_reaches_of_notMem hQ.1.acyclic hK hhC hne hh'C
      (hh'.trans hhv.symm) hw⟩
  -- the indegree of a node other than `v`
  have hin : ∀ w, w ≠ v → (deleteArc Q h).graph.indegree w = Q.graph.indegree w := fun w hw => by
    have := deleteArc_indegree (Q := Q) (h := h) w
    rwa [ite_eq_right (fun h' => hw (hhv ▸ h'.symm)), add_zero] at this
  -- the type of a cycle of `deleteArc Q h`
  have key : ∀ D' w, IsCycle (deleteArc Q h).graph D' →
      (InducesCycleType (deleteArc Q h) D' w n' k' ↔ InducesCycleType Q (Subtype.val '' D') w n' k')
        ∧ (w ∈ cycleNodes (deleteArc Q h).graph D' → w ∉ cycleNodes Q.graph C) := by
    intro D' w hD'
    obtain ⟨hD, hnodes⟩ := deleteArc_isCycle_image hD'
    have hwC := fun hw => notMem_cycleNodes_of_deleteArc hQ h1 hC hhv hD' (w := w) hw
    refine ⟨?_, hwC⟩
    unfold InducesCycleType
    rw [hnodes, Set.ncard_image_of_injective _ Subtype.val_injective]
    constructor
    · rintro ⟨-, h₂, h₃, h₄, h₅⟩
      have hwv : w ≠ v := fun he => hwC h₂ (he ▸ hC.2.1)
      refine ⟨hD, h₂, (hin w hwv) ▸ h₃, h₄, ?_⟩
      rw [← h₅, hbelow w (hwC h₂)]
    · rintro ⟨-, h₂, h₃, h₄, h₅⟩
      have hwv : w ≠ v := fun he => hwC h₂ (he ▸ hC.2.1)
      refine ⟨hD', h₂, (hin w hwv).symm ▸ h₃, h₄, ?_⟩
      rw [hbelow w (hwC h₂), h₅]
  constructor
  · rintro ⟨D', w, hD', rfl⟩
    obtain ⟨hD, -⟩ := deleteArc_isCycle_image hD'.1
    refine ⟨_, w, fun he => ?_, ((key D' w hD'.1).1).1 hD', ?_⟩
    · obtain ⟨e, -, he'⟩ := (he ▸ hhC : h ∈ Subtype.val '' D')
      exact e.2 he'
    · rw [hbelow w ((key D' w hD'.1).2 hD'.2.1)]
  · rintro ⟨D, w, hDC, hD, rfl⟩
    have hhD : h ∉ D := fun hh => hDC (h1 D C hD.1 hC.1 ⟨h, hh, hhC⟩)
    obtain ⟨D', hD', rfl⟩ := deleteArc_exists_isCycle hD.1 hhD
    have hD'' := ((key D' w hD').1).2 hD
    refine ⟨D', w, hD'', ?_⟩
    rw [hbelow w ((key D' w hD').2 hD''.2.1)]

/-- **`deleteArc Q h` has fewer cycles than `Q`**: its cycles are cycles of `Q`, and `C` is not one.
-/
theorem ncard_setOf_isCycle_deleteArc_lt [Finite E] :
    {D | IsCycle (deleteArc Q h).graph D}.ncard < {D | IsCycle Q.graph D}.ncard := by
  have hhC := hybrid_mem_cycle hQ h1 hC hhv
  rw [← Set.ncard_image_of_injective _ (Set.image_injective.2 Subtype.val_injective)]
  refine Set.ncard_lt_ncard ⟨fun D ⟨D', hD', hD⟩ => hD ▸ (deleteArc_isCycle_image hD').1,
    fun hsub => ?_⟩ (Set.toFinite _)
  obtain ⟨D', -, hD⟩ := hsub hC.1
  obtain ⟨e, -, he⟩ := (hD ▸ hhC : h ∈ Subtype.val '' D')
  exact e.2 he

/-- **`deleteArc Q h` has the cut edges of `Q` between two pairs of taxa**, for a cycle `C` inducing
a `2₂`- or a `3₁`-cycle. A cut edge of `Q` is off `C`, so it remains. A cut edge `e` of
`deleteArc Q h` whose side `T` is crossed by `h` in `Q` is on `C`, and each block of `C` is on one
side of `T`; with `v` on the other side of `T` than its two taxa, the two taxa of `T` are the block
of a node of `C` (of size two) or the complement of the two taxa below `v` (for a `2₂`-cycle): the
paper's "the edges of the cycle that remain are cut edges between one taxon and three, or between
the two pairs that the cycle already separates". -/
theorem deleteArc_hasCutSplit_iff [Fintype V] [Fintype E] [Fintype X] (hX : Fintype.card X = 4)
    (hnk : (n = 2 ∧ k = 2) ∨ (n = 3 ∧ k = 1)) {A : Set X}
    (hA : A.ncard = 2) : (deleteArc Q h).HasCutSplit A ↔ Q.HasCutSplit A := by
  have hhC := hybrid_mem_cycle hQ h1 hC hhv
  constructor
  swap
  · rintro ⟨e, T, hT, rfl⟩
    have heh : e ≠ h := fun he => notMem_of_crosses_iff hT hC.1 (he ▸ hhC)
    exact ⟨⟨e, heh⟩, T, fun f => (hT f.1).trans ⟨fun h' => Subtype.ext h',
      fun h' => congrArg Subtype.val h'⟩, rfl⟩
  rintro ⟨e', T, hT, rfl⟩
  set e := e'.1 with he_def
  have hM : ∀ f, f ≠ h → (Q.graph.Crosses f T ↔ f = e) := fun f hf =>
    (hT ⟨f, hf⟩).trans ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩
  by_cases hcr : Q.graph.Crosses h T
  swap
  · refine ⟨e, T, fun f => ?_, rfl⟩
    by_cases hf : f = h
    · subst hf
      exact ⟨fun hc => absurd hc hcr, fun he => absurd he.symm e'.2⟩
    · exact hM f hf
  -- `e` is on `C`, and each block of `C` is on one side of `T`
  have heC : e ∈ C := by
    by_contra heC
    have hw := hC.1.walks_sdiff_singleton hhC (target_mem_cycleNodes hhC)
      (source_mem_cycleNodes hhC)
    have := Q.graph.mem_iff_mem_of_walks (F := C \ {h}) (S := T) (fun f hf hc =>
      heC (((hM f hf.2).1 hc) ▸ hf.1)) hw
    unfold DirectedMultigraph.Crosses at hcr
    tauto
  have hblk : ∀ T' : Set V, (∀ f, Q.graph.Crosses f T' → f = e ∨ f = h) →
      ∀ x u, u ∈ cycleNodes Q.graph C → x ∈ nodeBlock Q.graph Q.leaf C u →
        (Q.leaf x ∈ T' ↔ u ∈ T') := by
    intro T' hT' x u _ hx
    refine (Q.graph.mem_iff_mem_of_walks (F := Cᶜ) (S := T') (fun f hf hc => ?_) hx).symm
    rcases hT' f hc with rfl | rfl
    · exact hf heC
    · exact hf hhC
  have hcrT : ∀ f, Q.graph.Crosses f T → f = e ∨ f = h := fun f hc => by
    by_cases hf : f = h
    · exact Or.inr hf
    · exact Or.inl ((hM f hf).1 hc)
  have hbelow := nodeBlock_hybrid hQ h1 hC.1 hC.2.1 hC.2.2.1
  -- the claim for the side of `T` without `v`
  have key : ∀ T' : Set V, (∀ x u, u ∈ cycleNodes Q.graph C → x ∈ nodeBlock Q.graph Q.leaf C u →
      (Q.leaf x ∈ T' ↔ u ∈ T')) → v ∉ T' → (Q.leaf ⁻¹' T').ncard = 2 →
      Q.HasCutSplit (Q.leaf ⁻¹' T') := by
    intro T' hb hvT hA'
    have hdisj : ∀ x, Q.graph.Reaches v (Q.leaf x) → Q.leaf x ∉ T' := fun x hx hxT =>
      hvT ((hb x v hC.2.1 (hbelow ▸ hx)).1 hxT)
    rcases hnk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- a `2₂`-cycle: the two taxa of `T'` are those not below `v`
      have hsub : Q.leaf ⁻¹' T' ⊆ {x | Q.graph.Reaches v (Q.leaf x)}ᶜ := fun x hx hxv =>
        hdisj x hxv hx
      have hc : {x | Q.graph.Reaches v (Q.leaf x)}ᶜ.ncard = 2 := by
        rw [Set.ncard_compl, Nat.card_eq_fintype_card, hX, hC.2.2.2.2]
      rw [Set.eq_of_subset_of_ncard_le hsub (by rw [hc, hA']) (Set.toFinite _),
        hasCutSplit_compl]
      exact hasCutSplit_below_hybrid hQ h1 hC.2.2.1
    · -- a `3₁`-cycle: the two taxa of `T'` are the block of a node of `C`
      obtain ⟨x₀, hx₀⟩ := Set.nonempty_of_ncard_ne_zero (s := Q.leaf ⁻¹' T') (by omega)
      have hnode : ∀ x, x ∈ Q.leaf ⁻¹' T' → ∃ u ∈ cycleNodes Q.graph C,
          x ∈ nodeBlock Q.graph Q.leaf C u ∧ u ∈ T' ∧ u ≠ v ∧ u ≠ Q.root ∧
            nodeBlock Q.graph Q.leaf C u ⊆ Q.leaf ⁻¹' T' := by
        intro x hx
        obtain ⟨u, hu, hxu⟩ := exists_mem_nodeBlock hQ.1 hC.1 x
        have huT := (hb x u hu hxu).1 hx
        refine ⟨u, hu, hxu, huT, fun h' => hvT (h' ▸ huT), fun h' => ?_,
          fun y hy => (hb y u hu hy).2 huT⟩
        rw [h'] at hu hxu
        rw [nodeBlock_root hQ hC.1 hu] at hxu
        exact hxu
      obtain ⟨w₀, hw₀, hx₀w, -, hw₀v, hw₀r, hsub₀⟩ := hnode x₀ hx₀
      have hle₀ : (nodeBlock Q.graph Q.leaf C w₀).ncard ≤ 2 :=
        hA' ▸ Set.ncard_le_ncard hsub₀ (Set.toFinite _)
      have hpos₀ : 1 ≤ (nodeBlock Q.graph Q.leaf C w₀).ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨x₀, hx₀w⟩
      by_cases h₀2 : (nodeBlock Q.graph Q.leaf C w₀).ncard = 2
      · rw [← Set.eq_of_subset_of_ncard_le hsub₀ (by rw [hA', h₀2]) (Set.toFinite _)]
        exact hasCutSplit_nodeBlock hQ h1 hC.1 hw₀ hw₀r
      exfalso
      obtain ⟨x₁, hx₁, hx₁w⟩ := Set.not_subset.1 fun h' : Q.leaf ⁻¹' T' ⊆
          nodeBlock Q.graph Q.leaf C w₀ => by
        have := Set.ncard_le_ncard h' (Set.toFinite _)
        omega
      obtain ⟨w₁, hw₁, hx₁w', -, hw₁v, hw₁r, hsub₁⟩ := hnode x₁ hx₁
      have hw₁₀ : w₁ ≠ w₀ := fun h' => hx₁w (h' ▸ hx₁w')
      have hdis := disjoint_nodeBlock_of_ne h1 hC.1 hw₀ hw₁ hw₁₀.symm
      have hpos₁ : 1 ≤ (nodeBlock Q.graph Q.leaf C w₁).ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨x₁, hx₁w'⟩
      have hsum : (nodeBlock Q.graph Q.leaf C w₀).ncard + (nodeBlock Q.graph Q.leaf C w₁).ncard
          ≤ 2 := by
        rw [← Set.ncard_union_eq hdis (Set.toFinite _) (Set.toFinite _), ← hA']
        exact Set.ncard_le_ncard (Set.union_subset hsub₀ hsub₁) (Set.toFinite _)
      -- the three nodes of `C` other than the root, with blocks of one taxon each
      have hvr : v ≠ Q.root := fun h' => by
        have := hQ.1.root_indegree
        rw [← h', hC.2.2.1] at this
        omega
      have hcard := card_cycleNodesOffRoot (N := Q) hC.1
      rw [hC.2.2.2.1] at hcard
      have hset : cycleNodesOffRoot Q C = {v, w₀, w₁} := by
        refine (Finset.eq_of_subset_of_card_le (fun u hu => ?_) ?_).symm
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact mem_cycleNodesOffRoot.2 ⟨hC.2.1, hvr⟩
          · exact mem_cycleNodesOffRoot.2 ⟨hw₀, hw₀r⟩
          · exact mem_cycleNodesOffRoot.2 ⟨hw₁, hw₁r⟩
        · rw [hcard, Finset.card_insert_of_notMem (by simp [Ne.symm hw₀v, Ne.symm hw₁v]),
            Finset.card_pair hw₁₀.symm]
      have htot := sum_ncard_nodeBlock_eq hQ h1 hC.1
      rw [hset, Finset.sum_insert (by simp [Ne.symm hw₀v, Ne.symm hw₁v]),
        Finset.sum_pair hw₁₀.symm, hbelow, hC.2.2.2.2, hX] at htot
      omega
  by_cases hvT : v ∈ T
  · rw [← hasCutSplit_compl, ← Set.preimage_compl]
    refine key Tᶜ (fun x u hu hx => not_congr (hblk T hcrT x u hu hx)) (fun h' => h' hvT) ?_
    rw [Set.preimage_compl, Set.ncard_compl, Nat.card_eq_fintype_card, hX]
    change 4 - ((deleteArc Q h).leaf ⁻¹' T).ncard = 2
    rw [hA]
  · exact key T (hblk T hcrT) hvT hA

end Delete

end Banos2019
