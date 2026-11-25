module

public import Banos2019.Network.SemidirectedDesc

/-!
# Contracting the edge at the root

`IsContraction S C ι κ`: the rooted network `C` is `S` with its root and the arc at the root removed
when the root has outdegree one (Definition 7, step 3), its nodes and arcs given by injective maps
`ι` and `κ` into those of `S`. Then `C` and `S` have the same paths between nodes of `C`
(`IsContraction.reaches_iff`), the same stable ancestors (`IsContraction.isStableAncestor_iff`), so
the same LSA (`IsContraction.lsa_eq`), and the same indegrees away from the root of `C`
(`IsContraction.indegree_eq`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {VS ES VC EC Y : Type*}

/-- `C` is `S` with the arc at the root contracted when the root has outdegree one: the nodes and
arcs of `C` are, through `ι` and `κ`, those of `S` other than the root and its arc in that case; the
ends of the arcs and the taxa are kept, and the root of `C` is that of `S`, or its child in that
case. -/
structure IsContraction (S : RootedNetwork VS ES Y) (C : RootedNetwork VC EC Y) (ι : VC → VS)
    (κ : EC → ES) : Prop where
  inj_v : Function.Injective ι
  inj_e : Function.Injective κ
  source : ∀ e, ι (C.graph.source e) = S.graph.source (κ e)
  target : ∀ e, ι (C.graph.target e) = S.graph.target (κ e)
  range_v : ∀ s, (∃ c, ι c = s) ↔ ¬ (s = S.root ∧ S.graph.outdegree S.root = 1)
  range_e : ∀ a, (∃ e, κ e = a) ↔ ¬ (S.graph.source a = S.root ∧ S.graph.outdegree S.root = 1)
  leaf : ∀ z, ι (C.leaf z) = S.leaf z
  root_one : S.graph.outdegree S.root = 1 → S.graph.Adj S.root (ι C.root)
  root_ne : S.graph.outdegree S.root ≠ 1 → ι C.root = S.root

namespace IsContraction

variable {S : RootedNetwork VS ES Y} {C : RootedNetwork VC EC Y} {ι : VC → VS} {κ : EC → ES}
  (hK : IsContraction S C ι κ) (hS : S.IsPhylogenetic)
include hK

/-- An arc of `S` out of a node of `C` is an arc of `C`. -/
theorem exists_arc {c : VC} {a : ES} (ha : S.graph.source a = ι c) : ∃ e, κ e = a := by
  refine (hK.range_e a).mpr fun h => ?_
  exact (hK.range_v (ι c)).mp ⟨c, rfl⟩ ⟨ha ▸ h.1, h.2⟩

include hS in
/-- The target of an arc of `S` is a node of `C`. -/
theorem exists_target (a : ES) : ∃ c, ι c = S.graph.target a :=
  (hK.range_v _).mpr fun h => hS.target_ne_root a h.1

theorem adj_iff {c c' : VC} : C.graph.Adj c c' ↔ S.graph.Adj (ι c) (ι c') := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    exact ⟨κ e, (hK.source e).symm, (hK.target e).symm⟩
  · rintro ⟨a, ha, ha'⟩
    obtain ⟨e, rfl⟩ := hK.exists_arc ha
    exact ⟨e, hK.inj_v ((hK.source e).trans ha), hK.inj_v ((hK.target e).trans ha')⟩

/-- Paths avoiding a node of `C` are the same in `C` and in `S`. -/
theorem avoiding_iff {c c' w : VC} :
    Relation.ReflTransGen (fun a b => C.graph.Adj a b ∧ a ≠ w ∧ b ≠ w) c c' ↔
      Relation.ReflTransGen (fun a b => S.graph.Adj a b ∧ a ≠ ι w ∧ b ≠ ι w) (ι c) (ι c') := by
  constructor
  · intro h
    refine Relation.ReflTransGen.lift ι (fun a b h => ⟨hK.adj_iff.mp h.1, fun h' => h.2.1
      (hK.inj_v h'), fun h' => h.2.2 (hK.inj_v h')⟩) c c' h
  · intro h
    generalize hs : ι c = s at h
    induction h using Relation.ReflTransGen.head_induction_on generalizing c with
    | refl =>
      obtain rfl := hK.inj_v hs
      exact .refl
    | @head a b hab _ ih =>
      obtain ⟨⟨f, hf, hf'⟩, ha, hb⟩ := hab
      obtain ⟨e, rfl⟩ := hK.exists_arc (hf.trans hs.symm)
      refine Relation.ReflTransGen.head ⟨⟨e, hK.inj_v ((hK.source e).trans (hf.trans hs.symm)),
        rfl⟩, fun h => ha (hs ▸ h ▸ rfl), fun h => hb (hf' ▸ (hK.target e).symm.trans
          (congrArg ι h))⟩ (ih ((hK.target e).trans hf'))

/-- **Paths of `C` are paths of `S`.** -/
theorem reaches_iff {c c' : VC} : C.graph.Reaches c c' ↔ S.graph.Reaches (ι c) (ι c') := by
  constructor
  · intro h
    exact Relation.ReflTransGen.lift ι (fun a b h => hK.adj_iff.mp h) c c' h
  · intro h
    generalize hs : ι c = s at h
    induction h using Relation.ReflTransGen.head_induction_on generalizing c with
    | refl =>
      obtain rfl := hK.inj_v hs
      exact .refl
    | @head a b hab _ ih =>
      obtain ⟨f, hf, hf'⟩ := hab
      obtain ⟨e, rfl⟩ := hK.exists_arc (hf.trans hs.symm)
      exact Relation.ReflTransGen.head ⟨e, hK.inj_v ((hK.source e).trans (hf.trans hs.symm)), rfl⟩
        (ih ((hK.target e).trans hf'))

include hS in
/-- **A path of `C` from its root avoiding a node is a path of `S` from its root avoiding it.** -/
theorem hasPathAvoiding_iff {c : VC} {z : Y} :
    C.HasPathAvoiding C.root (C.leaf z) c ↔ S.HasPathAvoiding S.root (S.leaf z) (ι c) := by
  by_cases h1 : S.graph.outdegree S.root = 1
  · have hr := hK.root_one h1
    have hroot : S.root ≠ ι c := fun h => (hK.range_v (ι c)).mp ⟨c, rfl⟩ ⟨h.symm, h1⟩
    constructor
    · rintro ⟨hrc, hzc, hp⟩
      have hp' := hK.avoiding_iff.mp hp
      rw [hK.leaf] at hp'
      refine ⟨hroot, fun h => hzc (hK.inj_v (by rw [hK.leaf z, h])), hp'.head ⟨hr, hroot,
        fun h => hrc (hK.inj_v h)⟩⟩
    · rintro ⟨-, hzc, hp⟩
      -- the path leaves the root of `S` by its only arc, to the root of `C`
      rcases Relation.ReflTransGen.cases_head hp with h | ⟨b, ⟨⟨f, hf, hf'⟩, -, hb⟩, hbz⟩
      · exact absurd h.symm (S.leaf_ne_root hS z)
      · obtain ⟨a, ha, ha'⟩ := hr
        obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h1
        have : f = a := ((he₀ f).mp hf).trans ((he₀ a).mp ha).symm
        subst this
        have hb' : b = ι C.root := hf'.symm.trans ha'
        subst hb'
        refine ⟨fun h => hb (congrArg ι h), fun h => hzc (by rw [← hK.leaf z, h]), ?_⟩
        have := hK.avoiding_iff (c := C.root) (c' := C.leaf z) (w := c)
        rw [hK.leaf] at this
        exact this.mpr hbz
  · have hr := hK.root_ne h1
    constructor
    · rintro ⟨hrc, hzc, hp⟩
      have hp' := hK.avoiding_iff.mp hp
      rw [hK.leaf, hr] at hp'
      exact ⟨fun h => hrc (hK.inj_v (hr.trans h)), fun h => hzc (hK.inj_v (by rw [hK.leaf z, h])),
        hp'⟩
    · rintro ⟨hrc, hzc, hp⟩
      refine ⟨fun h => hrc (hr ▸ congrArg ι h), fun h => hzc (by rw [← hK.leaf z, h]), ?_⟩
      have := hK.avoiding_iff (c := C.root) (c' := C.leaf z) (w := c)
      rw [hK.leaf, hr] at this
      exact this.mpr hp

include hS in
theorem isStableAncestor_iff {Y' : Set Y} {c : VC} :
    C.IsStableAncestor Y' c ↔ S.IsStableAncestor Y' (ι c) :=
  forall₂_congr fun _ _ => not_congr (hK.hasPathAvoiding_iff hS)

include hS in
/-- When the root of `S` has outdegree one, its child is on every path from the root. -/
theorem isStableAncestor_root (h1 : S.graph.outdegree S.root = 1) (Y' : Set Y) :
    S.IsStableAncestor Y' (ι C.root) := by
  rintro z - ⟨hr, hz, hp⟩
  rcases Relation.ReflTransGen.cases_head hp with h | ⟨b, ⟨⟨f, hf, hf'⟩, hne, hb⟩, -⟩
  · exact S.leaf_ne_root hS z h.symm
  · obtain ⟨a, ha, ha'⟩ := hK.root_one h1
    obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h1
    have : f = a := ((he₀ f).mp hf).trans ((he₀ a).mp ha).symm
    subst this
    exact hb (hf'.symm.trans ha')

include hS in
/-- **The LSA of `S` is a node of `C`**, and it is the LSA of `C`. -/
theorem isLeastStableAncestor_iff {Y' : Set Y} {c : VC} :
    C.IsLeastStableAncestor Y' c ↔ S.IsLeastStableAncestor Y' (ι c) := by
  constructor
  · rintro ⟨hst, hleast⟩
    refine ⟨(hK.isStableAncestor_iff hS).mp hst, fun s hs => ?_⟩
    by_cases hsr : ∃ c', ι c' = s
    · obtain ⟨c', rfl⟩ := hsr
      exact (hK.reaches_iff).mp (hleast c' ((hK.isStableAncestor_iff hS).mpr hs))
    · have : s = S.root := by
        by_contra h
        exact hsr ((hK.range_v s).mpr fun h' => h h'.1)
      rw [this]
      exact hS.root_reaches _
  · rintro ⟨hst, hleast⟩
    exact ⟨(hK.isStableAncestor_iff hS).mpr hst, fun c' hc' =>
      (hK.reaches_iff).mpr (hleast _ ((hK.isStableAncestor_iff hS).mp hc'))⟩

include hS in
theorem lsa_mem_range {Y' : Set Y} (hY : Y'.Nonempty) :
    ∃ c, ι c = lsa hS Y' hY := by
  refine (hK.range_v _).mpr fun ⟨h, h1⟩ => ?_
  have h₁ := (lsa_spec hS Y' hY).2 _ (hK.isStableAncestor_root hS h1 Y')
  rw [h] at h₁
  obtain ⟨a, ha, ha'⟩ := hK.root_one h1
  exact hS.acyclic _ (Relation.TransGen.head' ⟨a, ha, ha'⟩ h₁)

include hS in
/-- **The LSA of `C` is that of `S`.** -/
theorem lsa_eq (hC : C.IsPhylogenetic) {Y' : Set Y} (hY : Y'.Nonempty) :
    ι (lsa hC Y' hY) = lsa hS Y' hY := by
  obtain ⟨c, hc⟩ := hK.lsa_mem_range hS hY
  have h := (hK.isLeastStableAncestor_iff hS).mpr (hc ▸ lsa_spec hS Y' hY)
  rw [IsLeastStableAncestor.unique hC (lsa_spec hC Y' hY) h, hc]

/-- **The indegree of a node of `C` other than its root is that in `S`.** -/
theorem indegree_eq {c : VC} (hc : c ≠ C.root) :
    C.graph.indegree c = S.graph.indegree (ι c) := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_image_of_injective _ hK.inj_e]
  congr 1
  ext a
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (hK.target e).symm.trans (congrArg ι he)
  · intro ha
    by_cases hae : ∃ e, κ e = a
    · obtain ⟨e, rfl⟩ := hae
      exact ⟨e, hK.inj_v ((hK.target e).trans ha), rfl⟩
    · exfalso
      have h := not_not.mp (mt (hK.range_e a).mpr hae)
      obtain ⟨a', ha', ha''⟩ := hK.root_one h.2
      obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h.2
      have : a = a' := ((he₀ a).mp h.1).trans ((he₀ a').mp ha').symm
      subst this
      exact hc (hK.inj_v (ha.symm.trans ha''))

theorem isHybridArc_iff (hC : C.IsPhylogenetic) (e : EC) :
    C.IsHybridArc e ↔ S.IsHybridArc (κ e) := by
  unfold IsHybridArc
  rw [hK.indegree_eq (hC.target_ne_root e), hK.target]

theorem isTreeArc_iff (hC : C.IsPhylogenetic) (e : EC) :
    C.IsTreeArc e ↔ S.IsTreeArc (κ e) := by
  unfold IsTreeArc
  rw [hK.indegree_eq (hC.target_ne_root e), hK.target]

end IsContraction

end Banos2019
