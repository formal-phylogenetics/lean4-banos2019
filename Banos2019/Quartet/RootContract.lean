module

public import Banos2019.Network.Contraction
public import Banos2019.Network.Induced
public import Banos2019.Network.CycleMap
public import Banos2019.Network.Suppress
public import Banos2019.Quartet.Defs
public import Banos2019.Quartet.Trees

/-!
# Contracting the arc at the root, and renaming the nodes and arcs

`IsContraction S C ι κ` says that `C` is `S` with the arc at the root contracted when the root has
outdegree one, and otherwise `S` itself, through the injective maps `ι`, `κ` of the nodes and arcs.
This module gives the properties of `S` that `C` keeps.

* `IsContraction.outdegree_eq`, `IsContraction.isPhylogenetic`, `IsContraction.isBinary`,
  `IsContraction.isLevelOne`, `IsContraction.isMetric`: the network laws and the parameters.
* `IsContraction.geneTreeDist_eq`: the gene tree distribution is the same. With the root of
  outdegree one, the forest at the child of the root goes up the arc at the root, and the population on
  that arc does not change the gene tree (`kingmanTransition_mul_kingmanAbsorption`).
* `IsContraction.hasCutSplit_iff`: the cut edges between two nonempty sets of taxa are the same.
* `IsContraction.isCycle_image`, `IsContraction.exists_eq_image`, `IsContraction.inducesCycleType_iff`:
  the cycles, with their types, are the same, when the child of a root of outdegree one is on no
  cycle.
* `finContract`: `S` with the arc at the root contracted, its nodes and arcs renamed by `Fin`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {VS ES VC EC Y : Type*}

namespace IsContraction

variable {S : RootedNetwork VS ES Y} {C : RootedNetwork VC EC Y} {ι : VC → VS} {κ : EC → ES}
  (hK : IsContraction S C ι κ)
include hK

/-- **The outdegree of a node of `C` is that in `S`.** -/
theorem outdegree_eq (c : VC) : C.graph.outdegree c = S.graph.outdegree (ι c) := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_image_of_injective _ hK.inj_e]
  congr 1
  ext a
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (hK.source e).symm.trans (congrArg ι he)
  · intro ha
    obtain ⟨e, rfl⟩ := hK.exists_arc ha
    exact ⟨e, hK.inj_v ((hK.source e).trans ha), rfl⟩

/-- A node of `C` other than its root is not the root of `S`. -/
theorem ne_root {c : VC} (hc : c ≠ C.root) : ι c ≠ S.root := by
  intro h
  by_cases h1 : S.graph.outdegree S.root = 1
  · exact (hK.range_v (ι c)).mp ⟨c, rfl⟩ ⟨h, h1⟩
  · exact hc (hK.inj_v (h.trans (hK.root_ne h1).symm))

variable (hS : S.IsPhylogenetic)
include hS

/-- With a root of outdegree one in `S`, every node of `S` but the root is below its child, the root
of `C`. -/
theorem reaches_of_ne_root (h1 : S.graph.outdegree S.root = 1) {w : VS} (hw : w ≠ S.root) :
    S.graph.Reaches (ι C.root) w := by
  obtain ⟨a, ha, ha'⟩ := hK.root_one h1
  obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h1
  rcases Relation.ReflTransGen.cases_head (hS.root_reaches w) with h | ⟨b, ⟨f, hf, rfl⟩, hb⟩
  · exact absurd h.symm hw
  · have hfa : f = a := ((he₀ f).mp hf).trans ((he₀ a).mp ha).symm
    subst hfa
    rwa [ha'] at hb

/-- With a root of outdegree one in `S`, the only arc into its child is the arc at the root. -/
theorem eq_of_target_eq_root (h1 : S.graph.outdegree S.root = 1) {f : ES}
    (hf : S.graph.target f = ι C.root) : S.graph.source f = S.root := by
  by_contra hne
  exact hS.acyclic _ (Relation.TransGen.tail' (hK.reaches_of_ne_root hS h1 hne) ⟨f, rfl, hf⟩)

/-- No arc of `C` enters its root. -/
theorem target_ne_root (e : EC) : C.graph.target e ≠ C.root := by
  intro he
  have ht : S.graph.target (κ e) = ι C.root := (hK.target e).symm.trans (congrArg ι he)
  have := hS.finite_arcs
  by_cases h1 : S.graph.outdegree S.root = 1
  · exact (hK.range_e (κ e)).mp ⟨e, rfl⟩ ⟨hK.eq_of_target_eq_root hS h1 ht, h1⟩
  · exact (S.graph.indegree_eq_zero_iff _).1 hS.root_indegree (κ e)
      (ht.trans (hK.root_ne h1))

variable (htwo : ∃ z₁ z₂ : Y, z₁ ≠ z₂)
include htwo

/-- A taxon is not the root of `C`: when the root of `S` has outdegree one, its child is above the
two taxa. -/
theorem leaf_ne_root (x : Y) : C.leaf x ≠ C.root := by
  intro h
  have hx : S.leaf x = ι C.root := (hK.leaf x).symm.trans (congrArg ι h)
  by_cases h1 : S.graph.outdegree S.root = 1
  · obtain ⟨z₁, z₂, hz⟩ := htwo
    have h0 := (hS.leaves (S.leaf x)).2 ⟨x, rfl⟩
    have hz' : ∀ z, S.leaf z = S.leaf x := fun z => by
      have hr := hK.reaches_of_ne_root hS h1 (S.leaf_ne_root hS z)
      rw [← hx] at hr
      have := hS.finite_arcs
      exact S.graph.eq_of_reaches_of_outdegree_eq_zero hr h0
    exact hz (hS.leaf_injective ((hz' z₁).trans (hz' z₂).symm))
  · exact S.leaf_ne_root hS x (hx.trans (hK.root_ne h1))

/-- **`C` is a phylogenetic network.** -/
theorem isPhylogenetic : C.IsPhylogenetic := by
  have := hS.finite_vertices
  have := hS.finite_arcs
  have hroot : ∀ c, C.graph.Reaches C.root c := fun c => by
    rw [hK.reaches_iff]
    by_cases h1 : S.graph.outdegree S.root = 1
    · by_cases hc : c = C.root
      · rw [hc]
        exact .refl
      · exact hK.reaches_of_ne_root hS h1 (hK.ne_root hc)
    · rw [hK.root_ne h1]
      exact hS.root_reaches _
  refine
    { finite_vertices := Finite.of_injective ι hK.inj_v
      finite_arcs := Finite.of_injective κ hK.inj_e
      finite_taxa := hS.finite_taxa
      acyclic := fun c h => hS.acyclic (ι c) (Relation.TransGen.lift ι
        (fun a b hab => hK.adj_iff.mp hab) c c h)
      root_reaches := hroot
      root_indegree := ?_
      nonroot_indegree := fun c hc => ?_
      leaf_injective := fun x y h => hS.leaf_injective (by rw [← hK.leaf, ← hK.leaf, h])
      leaf_indegree := fun x => ?_
      leaves := fun c => ?_ }
  · have : Finite EC := Finite.of_injective κ hK.inj_e
    exact (C.graph.indegree_eq_zero_iff _).2 (hK.target_ne_root hS)
  · rw [hK.indegree_eq hc]
    exact hS.nonroot_indegree _ (hK.ne_root hc)
  · rw [hK.indegree_eq (hK.leaf_ne_root hS htwo x), hK.leaf]
    exact hS.leaf_indegree x
  · rw [hK.outdegree_eq, hS.leaves]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, hK.inj_v ((hK.leaf x).trans hx)⟩,
      fun ⟨x, hx⟩ => ⟨x, (hK.leaf x).symm.trans (congrArg ι hx)⟩⟩

/-- **`C` is binary** when `S` is binary but for a root of outdegree one. -/
theorem isBinary
    (hdeg : ∀ v, v ≠ S.root → S.graph.outdegree v ≠ 0 →
      S.graph.indegree v + S.graph.outdegree v = 3)
    (hroot : S.graph.outdegree S.root = 1 ∨ S.graph.outdegree S.root = 2) : C.IsBinary := by
  have hC := hK.isPhylogenetic hS htwo
  refine ⟨?_, fun c hc h0 => ?_⟩
  · rw [hK.outdegree_eq]
    rcases hroot with h1 | h2
    · have hne := hK.ne_root (c := C.root)
      have hr : ι C.root ≠ S.root := fun h => (hK.range_v _).mp ⟨C.root, rfl⟩ ⟨h, h1⟩
      have h0 : S.graph.outdegree (ι C.root) ≠ 0 := fun h0 => by
        obtain ⟨x, hx⟩ := (hS.leaves _).1 h0
        exact hK.leaf_ne_root hS htwo x (hK.inj_v ((hK.leaf x).trans hx))
      have h3 := hdeg _ hr h0
      have hin : S.graph.indegree (ι C.root) = 1 := by
        obtain ⟨a, ha, ha'⟩ := hK.root_one h1
        obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h1
        refine (S.graph.indegree_eq_one_iff _).2 ⟨a, fun f => ⟨fun hf => ?_, fun h => h ▸ ha'⟩⟩
        exact ((he₀ f).mp (hK.eq_of_target_eq_root hS h1 hf)).trans ((he₀ a).mp ha).symm
      omega
    · rwa [hK.root_ne (by omega)]
  · rw [hK.indegree_eq hc, hK.outdegree_eq]
    rw [hK.outdegree_eq] at h0
    exact hdeg _ (hK.ne_root hc) h0

omit hS htwo in
/-- **`C` is level-1** when `S` is: its cycles are cycles of `S`. -/
theorem isLevelOne (h1 : IsLevelOne S.graph) : IsLevelOne C.graph :=
  IsLevelOne.of_injective h1 ι κ hK.inj_v hK.inj_e (fun e => (hK.source e).symm)
    (fun e => (hK.target e).symm)

omit hK htwo in
/-- With a root of outdegree one in `S`, the root is on no cycle: it is on a single arc. -/
theorem root_notMem_cycleNodes (h1 : S.graph.outdegree S.root = 1) {D : Set ES}
    (hD : IsCycle S.graph D) : S.root ∉ cycleNodes S.graph D := by
  have := hS.finite_arcs
  intro hr
  obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h1
  have hloop : ∀ f, S.graph.source f ≠ S.graph.target f := fun f h =>
    hS.acyclic _ (.single ⟨f, rfl, h.symm⟩)
  obtain ⟨f₁, -, f₂, -, hne, h₁, h₂⟩ := hD.exists_ne_of_mem (fun f _ => hloop f) hr
  have key : ∀ f, (S.graph.source f = S.root ∨ S.graph.target f = S.root) → f = e₀ := by
    rintro f (hf | hf)
    · exact (he₀ f).mp hf
    · exact absurd hf ((S.graph.indegree_eq_zero_iff _).1 hS.root_indegree f)
  exact hne ((key f₁ h₁).trans (key f₂ h₂).symm)

omit hS htwo in
/-- An arc of `S` into a node of `C` other than its root is an arc of `C`. -/
theorem exists_arc_of_target {c : VC} (hc : c ≠ C.root) {a : ES} (ha : S.graph.target a = ι c) :
    ∃ e, κ e = a := by
  refine (hK.range_e a).mpr fun ⟨hs, h1⟩ => hc ?_
  obtain ⟨b, hb, hb'⟩ := hK.root_one h1
  obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h1
  have hab : a = b := ((he₀ a).mp hs).trans ((he₀ b).mp hb).symm
  subst hab
  exact hK.inj_v (ha.symm.trans hb')

/-- **The parameters of `C`**: those of the arcs of `S` that remain form a metric. -/
theorem isMetric [Fintype EC] [Fintype ES] {θ : MetricData ES} (hθ : S.IsMetric θ) :
    C.IsMetric ⟨fun e => θ.length (κ e), fun e => θ.inheritance (κ e)⟩ := by
  have hC := hK.isPhylogenetic hS htwo
  refine ⟨fun e he => hθ.1 _ ((hK.isTreeArc_iff hC e).1 he),
    fun e he => hθ.2.1 _ ((hK.isHybridArc_iff hC e).1 he),
    fun e he => hθ.2.2.1 _ ((hK.isTreeArc_iff hC e).1 he),
    fun e he => hθ.2.2.2.1 _ ((hK.isHybridArc_iff hC e).1 he), fun c hc => ?_⟩
  have hcr : c ≠ C.root := fun h => by
    rw [h, hC.root_indegree] at hc
    omega
  rw [hK.indegree_eq hcr] at hc
  rw [← hθ.2.2.2.2 _ hc, ← sum_filter, ← sum_filter]
  refine sum_bij (fun e _ => κ e) (fun e he => ?_) (fun a _ b _ h => hK.inj_e h)
    (fun a ha => ?_) fun e _ => rfl
  · exact mem_filter.2 ⟨mem_univ _, (hK.target e).symm.trans (congrArg ι (mem_filter.1 he).2)⟩
  · obtain ⟨e, rfl⟩ := hK.exists_arc_of_target hcr (mem_filter.1 ha).2
    exact ⟨e, mem_filter.2 ⟨mem_univ _, hK.inj_v ((hK.target e).trans (mem_filter.1 ha).2)⟩, rfl⟩

/-- **The gene tree distribution of `C` is that of `S`**, when the arc at a root of outdegree one has
inheritance `1`: with a root of outdegree one, `S` is `C` glued below one arc from a single node, and
the population on that arc does not change the gene tree. -/
theorem geneTreeDist_eq [Fintype VS] [Fintype ES] [Fintype VC] [Fintype EC] [Fintype Y]
    (θ : MetricData ES)
    (hθ : ∀ a, S.graph.source a = S.root → S.graph.outdegree S.root = 1 → θ.inheritance a = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (G : Finset (Finset Y)) :
    geneTreeDist S θ ρ G =
      geneTreeDist C ⟨fun e => θ.length (κ e), fun e => θ.inheritance (κ e)⟩ ρ G := by
  have hC := hK.isPhylogenetic hS htwo
  have hleaf : ∀ x, S.leaf x = ι (C.leaf x) := fun x => (hK.leaf x).symm
  rw [NMSC.geneTreeDist_eq_injDist hS, NMSC.geneTreeDist_eq_injDist hC,
    NMSC.injDist_eq_sum_rootDist, NMSC.injDist_eq_sum_rootDist]
  by_cases h1 : S.graph.outdegree S.root = 1
  · obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h1
    have he₀s : S.graph.source e₀ = S.root := (he₀ e₀).mpr rfl
    have he₀t : S.graph.target e₀ = ι C.root := by
      obtain ⟨b, hb, hb'⟩ := hK.root_one h1
      rwa [(he₀ b).mp hb] at hb'
    have hιr : ∀ c, ι c ≠ S.root := fun c h => (hK.range_v _).mp ⟨c, rfl⟩ ⟨h, h1⟩
    have hκ₀ : ∀ e, κ e ≠ e₀ := fun e h => (hK.range_e _).mp ⟨e, rfl⟩ ⟨h ▸ he₀s, h1⟩
    let ψ : Unit ⊕ VC → VS := Sum.elim (fun _ => S.root) ι
    have hψ : Function.Bijective ψ := by
      refine ⟨?_, fun s => ?_⟩
      · rintro (⟨⟩ | c) (⟨⟩ | c') h
        · rfl
        · exact absurd h.symm (hιr c')
        · exact absurd h (hιr c)
        · exact congrArg Sum.inr (hK.inj_v h)
      · by_cases hs : s = S.root
        · exact ⟨.inl (), hs.symm⟩
        · obtain ⟨c, rfl⟩ := (hK.range_v s).mpr fun h => hs h.1
          exact ⟨.inr c, rfl⟩
    let φ : Empty ⊕ Unit ⊕ EC → ES := Sum.elim Empty.elim (Sum.elim (fun _ => e₀) κ)
    have hφ : Function.Bijective φ := by
      refine ⟨?_, fun a => ?_⟩
      · rintro (e | ⟨⟩ | e) (e' | ⟨⟩ | e') h <;> first
          | exact e.elim
          | exact e'.elim
          | rfl
          | exact absurd h.symm (hκ₀ _)
          | exact absurd h (hκ₀ _)
          | exact congrArg (fun x => Sum.inr (Sum.inr x)) (hK.inj_e h)
      · by_cases ha : S.graph.source a = S.root
        · exact ⟨.inr (.inl ()), ((he₀ a).mp ha).symm⟩
        · obtain ⟨e, rfl⟩ := (hK.range_e a).mpr fun h => ha h.1
          exact ⟨.inr (.inr e), rfl⟩
    let fV := Equiv.ofBijective ψ hψ
    let fE := Equiv.ofBijective φ hφ
    have hg : NMSC.IsGlued S θ (pointNetwork Y) pointMetric C
        ⟨fun e => θ.length (κ e), fun e => θ.inheritance (κ e)⟩ fV fE (fun _ => ())
        (fun _ => θ.length e₀) :=
      { source₀ := fun e => e.elim
        target₀ := fun e => e.elim
        sourceP := fun _ => he₀s
        targetP := fun _ => he₀t
        source₁ := fun e => (hK.source e).symm
        target₁ := fun e => (hK.target e).symm
        root := rfl
        not_target_root := hK.target_ne_root hS
        length₀ := fun e => e.elim
        lengthP := fun _ => rfl
        length₁ := fun _ => rfl
        inheritance₀ := fun e => e.elim
        inheritance₁ := fun _ => rfl }
    have hlow : NMSC.lowerInj fV (NMSC.taxaInj S univ) = NMSC.taxaInj C univ := by
      funext v
      exact taxaInj_congr (f := fun v => fV (.inr v)) (fV.injective.comp Sum.inr_injective)
        hleaf v
    have hup : ∀ t : Finset (Finset Y),
        NMSC.upperInj fV (fun _ : Unit => ()) (NMSC.taxaInj S univ) (fun _ : Unit => t) () = t := by
      intro t
      unfold NMSC.upperInj NMSC.taxaInj
      have h0 : (univ.filter fun x => x ∈ (univ : Finset Y) ∧ S.leaf x = fV (.inl ())) = ∅ :=
        filter_eq_empty_iff.2 fun x _ h => S.leaf_ne_root hS x h.2
      rw [h0, image_empty, empty_union]
      simp
    have h1' : θ.inheritance (fE (.inr (.inl ()))) = 1 := hθ e₀ he₀s h1
    simp only [hg.rootDist_eq_unit hρ h1', rootDist_pointNetwork, hup, hlow, mul_ite, mul_one,
      mul_zero, sum_ite_eq', mem_univ, ite_true]
    simp only [sum_mul, mul_assoc]
    rw [sum_comm]
    refine sum_congr rfl fun F₁ _ => ?_
    rw [← mul_sum]
    by_cases hR : NMSC.rootDist C ⟨fun e => θ.length (κ e), fun e => θ.inheritance (κ e)⟩ ρ
        (NMSC.taxaInj C univ) F₁ = 0
    · rw [hR, zero_mul, zero_mul]
    · rw [kingmanTransition_mul_kingmanAbsorption
        (isForest_of_rootDist_ne_zero hC (NMSC.validInj_taxaInj univ) hR)]
  · have hι : Function.Bijective ι :=
      ⟨hK.inj_v, fun s => (hK.range_v s).mpr fun h => h1 h.2⟩
    have hκ : Function.Bijective κ :=
      ⟨hK.inj_e, fun a => (hK.range_e a).mpr fun h => h1 h.2⟩
    let fV := Equiv.ofBijective ι hι
    let fE := Equiv.ofBijective κ hκ
    refine sum_congr rfl fun F _ => ?_
    rw [NMSC.rootDist_congr (θ := ⟨fun e => θ.length (κ e), fun e => θ.inheritance (κ e)⟩)
      fV fE (fun e => (hK.source e).symm) (fun e => (hK.target e).symm)
      (hK.root_ne h1).symm (fun _ => rfl) (fun _ => rfl) (NMSC.taxaInj S univ) F]
    congr 2
    funext v
    exact taxaInj_congr hK.inj_v hleaf v

/-- **The concordance factors of `C` are those of `S`.** -/
theorem nmscCF_eq [Fintype VS] [Fintype ES] [Fintype VC] [Fintype EC] [Fintype Y]
    (θ : MetricData ES)
    (hθ : ∀ a, S.graph.source a = S.root → S.graph.outdegree S.root = 1 → θ.inheritance a = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (q : QuartetTree Y) :
    nmscCF C ⟨fun e => θ.length (κ e), fun e => θ.inheritance (κ e)⟩ ρ q = nmscCF S θ ρ q := by
  unfold nmscCF
  simp only [hK.geneTreeDist_eq hS htwo θ hθ hρ]

omit htwo in
/-- **The cut edges of `C` and `S` between two nonempty sets of taxa are the same.** The arc at a root
of outdegree one is not one of them: every taxon is below its target. -/
theorem hasCutSplit_iff {A : Set Y} (hA : ∃ x, x ∈ A) (hA' : ∃ x, x ∉ A) :
    C.HasCutSplit A ↔ S.HasCutSplit A := by
  have := hS.finite_arcs
  -- a node of `C` is in a set of nodes of `S` exactly when it is in its preimage
  constructor
  · rintro ⟨e, T, hT, rfl⟩
    let T' : Set VS := ι '' T ∪ {s | s = S.root ∧ C.root ∈ T}
    have hmem : ∀ c, ι c ∈ T' ↔ c ∈ T := fun c => by
      constructor
      · rintro (⟨c', hc', h⟩ | ⟨h, hr⟩)
        · rwa [← hK.inj_v h]
        · by_cases h1 : S.graph.outdegree S.root = 1
          · exact absurd ⟨h, h1⟩ ((hK.range_v _).mp ⟨c, rfl⟩)
          · rwa [hK.inj_v (h.trans (hK.root_ne h1).symm)]
      · exact fun hc => Or.inl ⟨c, hc, rfl⟩
    refine ⟨κ e, T', fun a => ?_, ?_⟩
    · by_cases ha : ∃ f, κ f = a
      · obtain ⟨f, rfl⟩ := ha
        rw [hK.inj_e.eq_iff, ← hT f]
        unfold DirectedMultigraph.Crosses
        rw [← hK.source, ← hK.target, hmem, hmem]
      · have h := not_not.mp (mt (hK.range_e a).mpr ha)
        obtain ⟨b, hb, hb'⟩ := hK.root_one h.2
        obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h.2
        have hab : a = b := ((he₀ a).mp h.1).trans ((he₀ b).mp hb).symm
        subst hab
        have hroot : S.root ∈ T' ↔ C.root ∈ T := by
          constructor
          · rintro (⟨c, -, hc⟩ | ⟨-, hr⟩)
            · exact absurd ⟨hc, h.2⟩ ((hK.range_v _).mp ⟨c, rfl⟩)
            · exact hr
          · exact fun hr => Or.inr ⟨rfl, hr⟩
        refine ⟨fun hc => ?_, fun h' => absurd ⟨e, h'.symm⟩ ha⟩
        unfold DirectedMultigraph.Crosses at hc
        rw [h.1, hb', hmem, hroot] at hc
        tauto
    · ext x
      simp only [Set.mem_preimage, ← hK.leaf, hmem]
  · rintro ⟨a, T', hT', rfl⟩
    by_cases ha : ∃ e, κ e = a
    · obtain ⟨e, rfl⟩ := ha
      refine ⟨e, ι ⁻¹' T', fun f => ?_, ?_⟩
      · rw [← hK.inj_e.eq_iff, ← hT' (κ f)]
        unfold DirectedMultigraph.Crosses
        rw [← hK.source, ← hK.target]
        rfl
      · ext x
        simp only [Set.mem_preimage, hK.leaf]
    · -- the arc at the root: every taxon is on the side of its target
      exfalso
      have h := not_not.mp (mt (hK.range_e a).mpr ha)
      obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h.2
      have hae : a = e₀ := (he₀ a).mp h.1
      have hside : ∀ x, S.leaf x ∈ T' ↔ S.graph.target a ∈ T' := by
        intro x
        have hr : S.graph.Reaches (S.graph.target a) (S.leaf x) := by
          obtain ⟨b, hb, hb'⟩ := hK.root_one h.2
          rw [hae, ← (he₀ b).mp hb, hb']
          exact hK.reaches_of_ne_root hS h.2 (S.leaf_ne_root hS x)
        refine (S.graph.mem_iff_mem_of_walks (F := {a}ᶜ) (fun f hf hc => hf ((hT' f).mp hc))
          (walks_of_reaches_of_forall hr fun f hf _ hfa => ?_)).symm
        rw [Set.mem_singleton_iff] at hfa
        subst hfa
        exact hS.acyclic _ (Relation.TransGen.tail' hf ⟨f, rfl, rfl⟩)
      obtain ⟨x, hx⟩ := hA
      obtain ⟨y, hy⟩ := hA'
      exact hy ((hside y).mpr ((hside x).mp hx))

omit hS htwo in
/-- A cycle of `C` gives a cycle of `S`, with the same arcs. -/
theorem isCycle_image {D : Set EC} (hD : IsCycle C.graph D) : IsCycle S.graph (κ '' D) :=
  hD.image ι κ hK.inj_v.injOn hK.inj_e.injOn (fun e _ => (hK.source e).symm)
    (fun e _ => (hK.target e).symm)

omit hS htwo in
theorem cycleNodes_image (D : Set EC) :
    cycleNodes S.graph (κ '' D) = ι '' cycleNodes C.graph D :=
  Banos2019.cycleNodes_image ι κ (fun e _ => (hK.source e).symm) (fun e _ => (hK.target e).symm)

omit htwo in
/-- **Every cycle of `S` comes from a cycle of `C`**: with a root of outdegree one, it does not pass
through the root. -/
theorem exists_eq_image {D : Set ES} (hD : IsCycle S.graph D) :
    ∃ D', IsCycle C.graph D' ∧ κ '' D' = D := by
  have hrange : D ⊆ Set.range κ ∧ cycleNodes S.graph D ⊆ Set.range ι := by
    by_cases h1 : S.graph.outdegree S.root = 1
    · have hr := root_notMem_cycleNodes hS h1 hD
      refine ⟨fun a ha => (hK.range_e a).mpr fun h => hr (h.1 ▸ source_mem_cycleNodes ha),
        fun s hs => (hK.range_v s).mpr fun h => hr (h.1 ▸ hs)⟩
    · exact ⟨fun a _ => (hK.range_e a).mpr fun h => h1 h.2,
        fun s _ => (hK.range_v s).mpr fun h => h1 h.2⟩
  refine ⟨κ ⁻¹' D, hD.preimage ι κ hK.inj_v hK.inj_e hrange.1 hrange.2
    (fun e _ => (hK.source e).symm) (fun e _ => (hK.target e).symm),
    Set.image_preimage_eq_of_subset hrange.1⟩

omit htwo in
/-- The cycles of `C` and of `S` are as many. -/
theorem ncard_setOf_isCycle :
    {D | IsCycle C.graph D}.ncard = {D | IsCycle S.graph D}.ncard := by
  rw [← Set.ncard_image_of_injective _ (Set.image_injective.2 hK.inj_e)]
  congr 1
  ext D
  constructor
  · rintro ⟨D', hD', rfl⟩
    exact hK.isCycle_image hD'
  · intro hD
    obtain ⟨D', hD', rfl⟩ := hK.exists_eq_image hS hD
    exact ⟨D', hD', rfl⟩

omit htwo in
/-- **The cycles of `C` and of `S` have the same types**, when the child of a root of outdegree one
is on no cycle: a cycle of `C` passes through its root exactly when the cycle of `S` passes through
the root of `S`. -/
theorem inducesCycleType_iff
    (hchild : S.graph.outdegree S.root = 1 → ∀ D, IsCycle S.graph D →
      ι C.root ∉ cycleNodes S.graph D) {D : Set EC} {v : VC} {n k : ℕ} :
    InducesCycleType C D v n k ↔ InducesCycleType S (κ '' D) (ι v) n k := by
  have := hS.finite_arcs
  have hnodes : ∀ c, ι c ∈ cycleNodes S.graph (κ '' D) ↔ c ∈ cycleNodes C.graph D := fun c => by
    rw [hK.cycleNodes_image]
    exact hK.inj_v.mem_set_image
  have hcyc : IsCycle C.graph D ↔ IsCycle S.graph (κ '' D) := by
    refine ⟨hK.isCycle_image, fun hD => ?_⟩
    obtain ⟨D', hD', he⟩ := hK.exists_eq_image hS hD
    rwa [← Set.image_injective.2 hK.inj_e he]
  have hin : C.graph.indegree v = 2 ↔ S.graph.indegree (ι v) = 2 := by
    by_cases hv : v = C.root
    · subst hv
      have hC0 : C.graph.indegree C.root = 0 := by
        have : Finite EC := Finite.of_injective κ hK.inj_e
        exact (C.graph.indegree_eq_zero_iff _).2 (hK.target_ne_root hS)
      rw [hC0]
      refine ⟨fun h => absurd h (by norm_num), fun h => ?_⟩
      exfalso
      by_cases h1 : S.graph.outdegree S.root = 1
      · obtain ⟨b, hb, hb'⟩ := hK.root_one h1
        obtain ⟨e₀, he₀⟩ := (S.graph.outdegree_eq_one_iff _).mp h1
        have : S.graph.indegree (ι C.root) = 1 :=
          (S.graph.indegree_eq_one_iff _).2 ⟨b, fun f => ⟨fun hf =>
            ((he₀ f).mp (hK.eq_of_target_eq_root hS h1 hf)).trans ((he₀ b).mp hb).symm,
            fun h => h ▸ hb'⟩⟩
        omega
      · rw [hK.root_ne h1, hS.root_indegree] at h
        omega
    · rw [hK.indegree_eq hv]
  have hroot : IsCycle C.graph D →
      (C.root ∈ cycleNodes C.graph D ↔ S.root ∈ cycleNodes S.graph (κ '' D)) := by
    intro hD
    by_cases h1 : S.graph.outdegree S.root = 1
    · constructor
      · intro h
        exact absurd ((hnodes _).mpr h) (hchild h1 _ (hK.isCycle_image hD))
      · intro h
        exact absurd h (root_notMem_cycleNodes hS h1 (hK.isCycle_image hD))
    · rw [← hK.root_ne h1, hnodes]
  have hbelow : {x | C.graph.Reaches v (C.leaf x)} = {x | S.graph.Reaches (ι v) (S.leaf x)} := by
    ext x
    simp only [Set.mem_ofPred_eq, hK.reaches_iff, hK.leaf]
  unfold InducesCycleType
  rw [hcyc, hnodes, hin, Set.ncard_image_of_injective _ hK.inj_e, hbelow]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨h₁, h₂, h₃, ?_, h₅⟩
    rw [← h₄]
    congr 2
    exact propext (hroot (hcyc.mpr h₁)).symm
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨h₁, h₂, h₃, ?_, h₅⟩
    rw [← h₄]
    congr 2
    exact propext (hroot (hcyc.mpr h₁))

end IsContraction

/-! ### Renaming by `Fin` -/

section Fin

variable (S : RootedNetwork VS ES Y) (hS : S.IsPhylogenetic) [Fintype VS] [Fintype ES]

/-- The nodes of `S` that remain when the arc at a root of outdegree one is contracted. -/
abbrev ContractRootVertex := {v : VS // ¬ (v = S.root ∧ S.graph.outdegree S.root = 1)}

/-- The arcs of `S` that remain when the arc at a root of outdegree one is contracted. -/
abbrev ContractRootArc := {e : ES // ¬ (S.graph.source e = S.root ∧ S.graph.outdegree S.root = 1)}

/-- The nodes of `finContract S hS`. -/
abbrev FinContractVertex := Fin (Fintype.card (ContractRootVertex S))

/-- The arcs of `finContract S hS`. -/
abbrev FinContractArc := Fin (Fintype.card (ContractRootArc S))

/-- **`S` with the arc at a root of outdegree one contracted, its nodes and arcs renamed by `Fin`.** -/
def finContract : RootedNetwork (FinContractVertex S) (FinContractArc S) Y where
  graph :=
    { source := fun e => Fintype.equivFin _
        ((contractRoot S hS).graph.source ((Fintype.equivFin _).symm e))
      target := fun e => Fintype.equivFin _
        ((contractRoot S hS).graph.target ((Fintype.equivFin _).symm e)) }
  root := Fintype.equivFin _ (contractRoot S hS).root
  leaf x := Fintype.equivFin _ ((contractRoot S hS).leaf x)

/-- The node of `S` of a node of `finContract S hS`. -/
def finContractVertex (c : FinContractVertex S) : VS :=
  ((Fintype.equivFin (ContractRootVertex S)).symm c).1

/-- The arc of `S` of an arc of `finContract S hS`. -/
def finContractArc (e : FinContractArc S) : ES :=
  ((Fintype.equivFin (ContractRootArc S)).symm e).1

/-- The parameters of `finContract S hS`: those of the arcs of `S`. -/
def finContractMetric (θ : MetricData ES) : MetricData (FinContractArc S) :=
  ⟨fun e => θ.length (finContractArc S e), fun e => θ.inheritance (finContractArc S e)⟩

/-- `finContract S hS` is `S` with the arc at a root of outdegree one contracted. -/
theorem isContraction_finContract :
    IsContraction S (finContract S hS) (finContractVertex S) (finContractArc S) := by
  have hK := isContraction_contractRoot S hS
  refine
    { inj_v := fun a b h => (Fintype.equivFin _).symm.injective (Subtype.ext h)
      inj_e := fun a b h => (Fintype.equivFin _).symm.injective (Subtype.ext h)
      source := fun e => by simp [finContractVertex, finContractArc, finContract, contractRoot]
      target := fun e => by simp [finContractVertex, finContractArc, finContract, contractRoot]
      range_v := fun v => ⟨fun ⟨c, hc⟩ => hc ▸ ((Fintype.equivFin _).symm c).2,
        fun h => ⟨Fintype.equivFin _ ⟨v, h⟩, by simp [finContractVertex]⟩⟩
      range_e := fun a => ⟨fun ⟨e, he⟩ => he ▸ ((Fintype.equivFin _).symm e).2,
        fun h => ⟨Fintype.equivFin _ ⟨a, h⟩, by simp [finContractArc]⟩⟩
      leaf := fun z => by simp [finContractVertex, finContract, contractRoot]
      root_one := fun h => by
        have := hK.root_one h
        simpa [finContractVertex, finContract] using this
      root_ne := fun h => by
        have := hK.root_ne h
        simpa [finContractVertex, finContract] using this }

end Fin

end Banos2019
