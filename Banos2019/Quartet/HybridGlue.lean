module

public import Banos2019.Quartet.Contract

/-!
# The lineages at a hybrid node (Baños 2019, Section 5, Lemmas 9 and 11)

At a hybrid node `v` that is a cut vertex, with hybrid arcs `h₁`, `h₂` of inheritance `γ`, `1 - γ`,
the forest `G` arriving at `v` is split: each of its roots takes `h₁` with probability `γ` and `h₂`
otherwise (at inheritance correlation `0`), and the two parts go up `h₁` and `h₂` by Kingman's
coalescent. The process is then that of the network with the forests `t₁`, `t₂` at the tops of `h₁`
and `h₂` injected at their sources, and nothing at or below `v` (`hybInj`).

* `cherryMass_cutInj_hybrid`: this decomposition, from `NMSC.IsGlued.rootDist_eq_bool` at the cut
  vertex `v`.
* `cherryMass_hybInj_withPair`: the process with nothing at `v` does not depend on the inheritance
  probabilities of `h₁`, `h₂`.
* `cherryMass_eq_sum_arc`: the Markov property at an arc, for the mass of a quartet tree.
* `hybridPoly_eq`: with at most two roots in `G`, the mass is `γ² P(1) + (1 - γ)² P(0) + 2γ(1 - γ) Z`
  when the two ways of splitting two roots between `h₁` and `h₂` give `Z`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

section Cherry


/-- The mass of the quartet tree `q` for a law `R` of the forest arriving at the root. -/
def cherryOf (q : QuartetTree X) (R : Finset (Finset X) → ℝ) : ℝ :=
  ∑ H, if ∃ B ∈ q.val, B ∈ H then ∑ F, R F * kingmanAbsorption F H else 0

theorem cherryMass_eq_cherryOf (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ)
    (inj : V → Finset (Finset X)) (q : QuartetTree X) :
    cherryMass N θ ρ inj q = cherryOf q (rootDist N θ ρ inj) := by
  unfold cherryMass cherryOf
  simp only [injDist_eq_sum_rootDist]

omit [Fintype V] [Fintype E] in
theorem cherryOf_sum {ι : Type*} (q : QuartetTree X) (s : Finset ι)
    (R : ι → Finset (Finset X) → ℝ) :
    cherryOf q (fun F => ∑ i ∈ s, R i F) = ∑ i ∈ s, cherryOf q (R i) := by
  unfold cherryOf
  rw [sum_comm]
  refine sum_congr rfl fun H _ => ?_
  split_ifs
  · simp only [sum_mul]
    exact sum_comm
  · simp

omit [Fintype V] [Fintype E] in
theorem cherryOf_mul (q : QuartetTree X) (c : ℝ) (R : Finset (Finset X) → ℝ) :
    cherryOf q (fun F => c * R F) = c * cherryOf q R := by
  unfold cherryOf
  rw [mul_sum]
  refine sum_congr rfl fun H _ => ?_
  split_ifs
  · rw [mul_sum]
    exact sum_congr rfl fun F _ => by ring
  · simp

omit [Fintype V] [Fintype E] in
/-- `cherryOf` against the function `cherryPhi` of the forest arriving at the root. -/
theorem cherryOf_eq_sum (q : QuartetTree X) (R : Finset (Finset X) → ℝ) :
    cherryOf q R = ∑ F, R F * ∑ H, if ∃ B ∈ q.val, B ∈ H then kingmanAbsorption F H else 0 := by
  unfold cherryOf
  simp only [mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  refine sum_congr rfl fun H _ => ?_
  split_ifs <;> simp

/-- **The Markov property at an arc** `c` into a cut vertex, for the mass of a quartet tree. -/
theorem cherryMass_eq_sum_arc {N : RootedNetwork V E X} {r : V} {c : E} (hN : N.IsPhylogenetic)
    (hc : IsCut N r) (hcr : N.graph.target c = r) (huniq : ∀ g, N.graph.target g = r → g = c)
    {θ : MetricData E} (h1 : θ.inheritance c = 1) (inj : V → Finset (Finset X))
    (q : QuartetTree X) :
    cherryMass N θ 0 inj q =
      ∑ t, arcLaw N r hc θ 0 c inj t * cherryMass N θ 0 (liftInj N c inj t) q := by
  have h := sum_mul_arc hN hc hcr huniq h1 le_rfl inj (fun _ => 1)
    fun F => ∑ H, if ∃ B ∈ q.val, B ∈ H then kingmanAbsorption F H else 0
  simp only [one_mul] at h
  rw [cherryMass_eq_cherryOf, cherryOf_eq_sum, sum_rootDist_mul, h]
  refine sum_congr rfl fun t _ => ?_
  rw [cherryMass_eq_cherryOf, cherryOf_eq_sum]

end Cherry

section Hybrid

variable {N : RootedNetwork V E X} {v : V} {h₁ h₂ : E}

/-- The two arcs into `v`, indexed by `Bool`: `false` for `h₁`, `true` for `h₂`. -/
def boolArcs (hne : h₁ ≠ h₂) (hh₁ : N.graph.target h₁ = v) (hh₂ : N.graph.target h₂ = v)
    (hpar : ∀ f, N.graph.target f = v → f = h₁ ∨ f = h₂) : Bool ≃ {e // N.graph.target e = v} :=
  Equiv.ofBijective (fun b => cond b ⟨h₂, hh₂⟩ ⟨h₁, hh₁⟩) ⟨fun a b hab => by
    cases a <;> cases b
    · rfl
    · exact absurd (congrArg Subtype.val hab) hne
    · exact absurd (congrArg Subtype.val hab).symm hne
    · rfl, fun e => by
    rcases hpar e.1 e.2 with h | h
    · exact ⟨false, Subtype.ext h.symm⟩
    · exact ⟨true, Subtype.ext h.symm⟩⟩

variable (N v h₁ h₂) in
/-- The forests `t₁`, `t₂` at the sources of `h₁`, `h₂`, nothing at or below `v`, and `inj`
elsewhere. -/
def hybInj (inj : V → Finset (Finset X)) (t₁ t₂ : Finset (Finset X)) : V → Finset (Finset X) :=
  fun w => if N.graph.Reaches v w then ∅ else
    inj w ∪ ((if w = N.graph.source h₁ then t₁ else ∅) ∪ (if w = N.graph.source h₂ then t₂ else ∅))

/-- The law at the root of the part not below `v`, with `t₁`, `t₂` at the sources of `h₁`, `h₂`. -/
def hybridUpperLaw (hN : N.IsPhylogenetic) (hc : IsCut N v) (hne : h₁ ≠ h₂)
    (hh₁ : N.graph.target h₁ = v) (hh₂ : N.graph.target h₂ = v)
    (hpar : ∀ f, N.graph.target f = v → f = h₁ ∨ f = h₂) (θ : MetricData E)
    (inj : V → Finset (Finset X)) (t₁ t₂ F : Finset (Finset X)) : ℝ :=
  rootDist (cutUpper N v hc) (cutUpperMetric N v θ) 0
    (upperInj (cutVertices N v) (cutSource N v hN (boolArcs hne hh₁ hh₂ hpar)) inj
      fun p => cond p t₂ t₁) F

omit [Fintype V] [Fintype E] [Fintype X] in
theorem mem_upperInj_boolArcs (hN : N.IsPhylogenetic) (hne : h₁ ≠ h₂)
    (hh₁ : N.graph.target h₁ = v) (hh₂ : N.graph.target h₂ = v)
    (hpar : ∀ f, N.graph.target f = v → f = h₁ ∨ f = h₂) (inj : V → Finset (Finset X))
    (t₁ t₂ : Finset (Finset X)) (w : {w // ¬ N.graph.Reaches v w}) (A : Finset X) :
    A ∈ upperInj (cutVertices N v) (cutSource N v hN (boolArcs hne hh₁ hh₂ hpar)) inj
        (fun p => cond p t₂ t₁) w ↔
      A ∈ inj w.1 ∨ (w.1 = N.graph.source h₁ ∧ A ∈ t₁) ∨ (w.1 = N.graph.source h₂ ∧ A ∈ t₂) := by
  have h₁' : (cutSource N v hN (boolArcs hne hh₁ hh₂ hpar) false).1 = N.graph.source h₁ := rfl
  have h₂' : (cutSource N v hN (boolArcs hne hh₁ hh₂ hpar) true).1 = N.graph.source h₂ := rfl
  unfold upperInj
  simp only [mem_union, mem_biUnion, mem_filter, mem_univ, true_and, cutVertices_inl]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨p, hp, hA⟩
    cases p
    · exact Or.inl ⟨by rw [← hp, h₁'], hA⟩
    · exact Or.inr ⟨by rw [← hp, h₂'], hA⟩
  · rintro (⟨h, hA⟩ | ⟨h, hA⟩)
    · exact ⟨false, Subtype.ext (h₁'.trans h.symm), hA⟩
    · exact ⟨true, Subtype.ext (h₂'.trans h.symm), hA⟩

variable (hN : N.IsPhylogenetic) (hc : IsCut N v) (hne : h₁ ≠ h₂) (hh₁ : N.graph.target h₁ = v)
  (hh₂ : N.graph.target h₂ = v) (hpar : ∀ f, N.graph.target f = v → f = h₁ ∨ f = h₂)
include hN hc hne hh₁ hh₂ hpar

/-- **The split of the forest at a hybrid node**, for the law at the root: the forest `G` at `v`
(with nothing below `v`) splits between `h₁` and `h₂`, each root taking `h₁` with probability `γ`. -/
theorem rootDist_cutInj_hybrid {θ : MetricData E} {γ : ℝ} (hγ₁ : θ.inheritance h₁ = γ)
    (hγ₂ : θ.inheritance h₂ = 1 - γ) (inj : V → Finset (Finset X)) (G F : Finset (Finset X)) :
    rootDist N θ 0 (cutInj N v inj G) F =
      ∑ A ∈ (roots G).powerset, γ ^ #A * (1 - γ) ^ #(roots G \ A) * ∑ t₁, ∑ t₂,
        kingmanTransition (θ.length h₁) (forestBelow G A) t₁ *
          kingmanTransition (θ.length h₂) (forestBelow G (roots G \ A)) t₂ *
            hybridUpperLaw hN hc hne hh₁ hh₂ hpar θ inj t₁ t₂ F := by
  have hg := isGlued_cut N v hN hc θ (boolArcs hne hh₁ hh₂ hpar)
  rw [hg.rootDist_eq_bool (γ := γ) hγ₁ hγ₂ (cutInj N v inj G) F]
  have hlow : lowerInj (cutVertices N v) (cutInj N v inj G) = atRoot (cutLower N v hc) G := by
    funext w
    unfold lowerInj atRoot
    by_cases hw : w = (cutLower N v hc).root
    · rw [ite_eq_left hw, hw]
      exact cutInj_self N v inj G
    · rw [ite_eq_right hw]
      exact cutInj_of_reaches_of_ne N v inj G w.2 fun h => hw (Subtype.ext h)
  have hup : ∀ t, upperInj (cutVertices N v) (cutSource N v hN (boolArcs hne hh₁ hh₂ hpar))
      (cutInj N v inj G) t =
      upperInj (cutVertices N v) (cutSource N v hN (boolArcs hne hh₁ hh₂ hpar)) inj t := by
    intro t
    funext w
    unfold upperInj
    rw [cutVertices_inl, cutInj_of_not_reaches N v inj G w.2]
  simp only [hlow, hup]
  rw [Finset.sum_eq_single G]
  · rw [rootDist_atRoot (cutLower_acyclic N v hN hc) (fun e h => e.2.2 (congrArg Subtype.val h)),
      ite_eq_left rfl, one_mul]
    rfl
  · intro F' _ hF'
    rw [rootDist_atRoot (cutLower_acyclic N v hN hc) (fun e h => e.2.2 (congrArg Subtype.val h)),
      ite_eq_right hF', zero_mul]
  · simp

omit [Fintype V] [Fintype E] [Fintype X] hN hc hne hh₁ hh₂ hpar in
theorem cutInj_hybInj (inj : V → Finset (Finset X)) (t₁ t₂ : Finset (Finset X)) :
    cutInj N v (hybInj N v h₁ h₂ inj t₁ t₂) ∅ = hybInj N v h₁ h₂ inj t₁ t₂ := by
  funext w
  unfold cutInj hybInj
  split_ifs <;> rfl

/-- **With nothing at or below `v`**, the process is that of the part not below `v` with the forests
at the sources of `h₁`, `h₂`. -/
theorem rootDist_hybInj {θ : MetricData E} {γ : ℝ} (hγ₁ : θ.inheritance h₁ = γ)
    (hγ₂ : θ.inheritance h₂ = 1 - γ) (inj : V → Finset (Finset X)) (t₁ t₂ F : Finset (Finset X)) :
    rootDist N θ 0 (hybInj N v h₁ h₂ inj t₁ t₂) F =
      hybridUpperLaw hN hc hne hh₁ hh₂ hpar θ inj t₁ t₂ F := by
  rw [← cutInj_hybInj inj t₁ t₂,
    rootDist_cutInj_hybrid hN hc hne hh₁ hh₂ hpar hγ₁ hγ₂ _ ∅ F]
  have hr : roots (∅ : Finset (Finset X)) = ∅ := by simp [roots]
  have hfb : forestBelow (∅ : Finset (Finset X)) ∅ = ∅ := by simp [forestBelow]
  have hK : ∀ ℓ (t : Finset (Finset X)), kingmanTransition ℓ ∅ t = if t = ∅ then 1 else 0 :=
    fun ℓ t => kingmanTransition_of_card_roots_le_one isForest_empty (by simp [hr]) ℓ t
  rw [hr, powerset_empty, sum_singleton, empty_sdiff, card_empty, pow_zero, pow_zero, one_mul,
    one_mul, hfb]
  rw [Finset.sum_eq_single ∅ (fun b _ hb => by
      refine sum_eq_zero fun b₂ _ => ?_
      rw [hK, ite_eq_right hb, zero_mul, zero_mul]) (by simp)]
  rw [Finset.sum_eq_single ∅ (fun b _ hb => by rw [hK, hK, ite_eq_right hb, mul_zero, zero_mul])
    (by simp)]
  rw [hK, hK, ite_eq_left rfl, one_mul, one_mul]
  unfold hybridUpperLaw
  congr 1
  funext w
  ext A
  rw [mem_upperInj_boolArcs, mem_upperInj_boolArcs]
  simp only [hybInj, w.2, ite_false, mem_union, notMem_empty, and_false, or_false]
  refine or_congr_right (or_congr ?_ ?_) <;> split_ifs <;> simp_all


/-- **The split of the forest at a hybrid node**, for the mass of a quartet tree. -/
theorem cherryMass_cutInj_hybrid {θ : MetricData E} {γ : ℝ} (hγ₁ : θ.inheritance h₁ = γ)
    (hγ₂ : θ.inheritance h₂ = 1 - γ) (inj : V → Finset (Finset X)) (G : Finset (Finset X))
    (q : QuartetTree X) :
    cherryMass N θ 0 (cutInj N v inj G) q =
      ∑ A ∈ (roots G).powerset, γ ^ #A * (1 - γ) ^ #(roots G \ A) * ∑ t₁, ∑ t₂,
        kingmanTransition (θ.length h₁) (forestBelow G A) t₁ *
          kingmanTransition (θ.length h₂) (forestBelow G (roots G \ A)) t₂ *
            cherryMass N θ 0 (hybInj N v h₁ h₂ inj t₁ t₂) q := by
  rw [cherryMass_eq_cherryOf]
  have hR : rootDist N θ 0 (cutInj N v inj G) = fun F =>
      ∑ A ∈ (roots G).powerset, γ ^ #A * (1 - γ) ^ #(roots G \ A) * ∑ t₁, ∑ t₂,
        kingmanTransition (θ.length h₁) (forestBelow G A) t₁ *
          kingmanTransition (θ.length h₂) (forestBelow G (roots G \ A)) t₂ *
            rootDist N θ 0 (hybInj N v h₁ h₂ inj t₁ t₂) F := by
    funext F
    rw [rootDist_cutInj_hybrid hN hc hne hh₁ hh₂ hpar hγ₁ hγ₂]
    simp only [rootDist_hybInj hN hc hne hh₁ hh₂ hpar hγ₁ hγ₂]
  rw [hR, cherryOf_sum]
  refine sum_congr rfl fun A _ => ?_
  rw [cherryOf_mul, cherryOf_sum]
  congr 1
  refine sum_congr rfl fun t₁ _ => ?_
  rw [cherryOf_sum]
  refine sum_congr rfl fun t₂ _ => ?_
  rw [cherryOf_mul, cherryMass_eq_cherryOf]

/-- **With nothing at `v`, the inheritance probabilities of `h₁`, `h₂` do not matter.** -/
theorem cherryMass_hybInj_withPair {θ : MetricData E} {γ : ℝ} (hγ₁ : θ.inheritance h₁ = γ)
    (hγ₂ : θ.inheritance h₂ = 1 - γ) (γ' : ℝ) (inj : V → Finset (Finset X))
    (t₁ t₂ : Finset (Finset X)) (q : QuartetTree X) :
    cherryMass N (θ.withPair h₁ h₂ γ') 0 (hybInj N v h₁ h₂ inj t₁ t₂) q =
      cherryMass N θ 0 (hybInj N v h₁ h₂ inj t₁ t₂) q := by
  have hm : cutUpperMetric N v (θ.withPair h₁ h₂ γ') = cutUpperMetric N v θ := by
    have hv : ∀ (e : {e // ¬ N.graph.Reaches v (N.graph.target e)}) h, N.graph.target h = v →
        e.1 ≠ h := fun e h hh he => e.2 (by rw [he, hh]; exact .refl)
    simp only [cutUpperMetric, MetricData.mk.injEq, withPair_length, true_and]
    funext e
    exact withPair_inheritance_of_ne (hv e h₁ hh₁) (hv e h₂ hh₂) γ'
  have h : ∀ F, rootDist N (θ.withPair h₁ h₂ γ') 0 (hybInj N v h₁ h₂ inj t₁ t₂) F =
      rootDist N θ 0 (hybInj N v h₁ h₂ inj t₁ t₂) F := by
    intro F
    rw [rootDist_hybInj hN hc hne hh₁ hh₂ hpar (withPair_inheritance_left h₁ h₂ γ')
        (withPair_inheritance_right hne γ'), rootDist_hybInj hN hc hne hh₁ hh₂ hpar hγ₁ hγ₂]
    unfold hybridUpperLaw
    rw [hm]
  rw [cherryMass_eq_cherryOf, cherryMass_eq_cherryOf, funext h]

end Hybrid

section Poly


/-- The part of a forest below one of its roots has one root. -/
theorem card_roots_forestBelow_singleton_le {F : Finset (Finset X)} {R : Finset X}
    (hR : R ∈ roots F) : #(roots (forestBelow F {R})) ≤ 1 := by
  refine card_le_one.2 fun B hB C hC => ?_
  have key : ∀ B ∈ roots (forestBelow F {R}), B = R := by
    intro B hB
    obtain ⟨hBF, hmax⟩ := mem_roots.1 hB
    obtain ⟨-, D, hD, hBD⟩ := mem_forestBelow.1 hBF
    rw [mem_singleton.1 hD] at hBD
    exact (hmax R (mem_forestBelow.2 ⟨(mem_roots.1 hR).1, R, mem_singleton_self R, subset_rfl⟩)
      hBD).symm
  rw [key B hB, key C hC]

omit [Fintype X] in
theorem forestBelow_empty_right (F : Finset (Finset X)) : forestBelow F ∅ = ∅ := by
  simp [forestBelow]

/-- The polynomial in `γ` of the split of a forest `G` between two arcs `h₁`, `h₂`. -/
def hybridPoly (G : Finset (Finset X)) (ℓ₁ ℓ₂ : ℝ) (W : Finset (Finset X) → Finset (Finset X) → ℝ)
    (γ : ℝ) : ℝ :=
  ∑ A ∈ (roots G).powerset, γ ^ #A * (1 - γ) ^ #(roots G \ A) * ∑ t₁, ∑ t₂,
    kingmanTransition ℓ₁ (forestBelow G A) t₁ * kingmanTransition ℓ₂ (forestBelow G (roots G \ A)) t₂ *
      W t₁ t₂

theorem kingmanTransition_forestBelow_singleton {G : Finset (Finset X)} (hG : IsGoodForest G)
    {R : Finset X} (hR : R ∈ roots G) (ℓ : ℝ) (t : Finset (Finset X)) :
    kingmanTransition ℓ (forestBelow G {R}) t = if t = forestBelow G {R} then 1 else 0 :=
  kingmanTransition_of_card_roots_le_one (isGoodForest_forestBelow hG).1
    (card_roots_forestBelow_singleton_le hR) ℓ t

/-- **The split of a forest with at most two roots** (Lemmas 9 and 11): if a single root, kept or not,
gives `Z` either way, and the two ways of sending two roots to different arcs give `Z`, then the
polynomial is `γ² P(1) + (1 - γ)² P(0) + 2γ(1 - γ) Z`. -/
theorem hybridPoly_eq {G : Finset (Finset X)} (hG : IsGoodForest G) (h2 : #(roots G) ≤ 2)
    (ℓ₁ ℓ₂ : ℝ) (W : Finset (Finset X) → Finset (Finset X) → ℝ) (Z : ℝ)
    (h0 : G = ∅ → W ∅ ∅ = Z) (h1 : #(roots G) = 1 → W G ∅ = Z ∧ W ∅ G = Z)
    (h2' : ∀ R₁ R₂, R₁ ≠ R₂ → roots G = {R₁, R₂} →
      W (forestBelow G {R₁}) (forestBelow G {R₂}) = Z) (γ : ℝ) :
    hybridPoly G ℓ₁ ℓ₂ W γ =
      γ ^ 2 * hybridPoly G ℓ₁ ℓ₂ W 1 + (1 - γ) ^ 2 * hybridPoly G ℓ₁ ℓ₂ W 0 +
        2 * γ * (1 - γ) * Z := by
  have hK0 : ∀ ℓ (t : Finset (Finset X)), kingmanTransition ℓ ∅ t = if t = ∅ then 1 else 0 :=
    fun ℓ t => kingmanTransition_of_card_roots_le_one isForest_empty (by simp [roots]) ℓ t
  have hall : forestBelow G (roots G) = G := by
    have := (forestBelow_union hG (empty_subset (roots G))).1
    rwa [forestBelow_empty_right, empty_union, sdiff_empty] at this
  -- the sums over the forests at the tops of the arcs, when each part has at most one root
  have hsum : ∀ A B : Finset (Finset X), (∀ ℓ t, kingmanTransition ℓ A t = if t = A then 1 else 0) →
      (∀ ℓ t, kingmanTransition ℓ B t = if t = B then 1 else 0) →
      ∑ t₁, ∑ t₂, kingmanTransition ℓ₁ A t₁ * kingmanTransition ℓ₂ B t₂ * W t₁ t₂ = W A B := by
    intro A B hA hB
    rw [Finset.sum_eq_single A (fun b _ hb => sum_eq_zero fun b₂ _ => by
      rw [hA, ite_eq_right hb, zero_mul, zero_mul]) (by simp)]
    rw [Finset.sum_eq_single B (fun b _ hb => by rw [hA, hB, ite_eq_right hb, mul_zero, zero_mul])
      (by simp)]
    rw [hA, hB, ite_eq_left rfl, ite_eq_left rfl, one_mul, one_mul]
  have hsumL : ∀ B : Finset (Finset X), ∑ t₁, ∑ t₂, kingmanTransition ℓ₁ ∅ t₁ *
      kingmanTransition ℓ₂ B t₂ * W t₁ t₂ = ∑ t₂, kingmanTransition ℓ₂ B t₂ * W ∅ t₂ := by
    intro B
    rw [Finset.sum_eq_single ∅ (fun b _ hb => sum_eq_zero fun b₂ _ => by
      rw [hK0, ite_eq_right hb, zero_mul, zero_mul]) (by simp)]
    simp only [hK0, ite_eq_left, one_mul]
  have hsumR : ∀ A : Finset (Finset X), ∑ t₁, ∑ t₂, kingmanTransition ℓ₁ A t₁ *
      kingmanTransition ℓ₂ ∅ t₂ * W t₁ t₂ = ∑ t₁, kingmanTransition ℓ₁ A t₁ * W t₁ ∅ := by
    intro A
    refine sum_congr rfl fun t₁ _ => ?_
    rw [Finset.sum_eq_single ∅ (fun b _ hb => by rw [hK0, ite_eq_right hb, mul_zero, zero_mul])
      (by simp)]
    rw [hK0, ite_eq_left rfl, mul_one]
  have hps : ∀ R : Finset X, ({R} : Finset (Finset X)).powerset = {∅, {R}} := by
    intro R
    ext A
    simp only [mem_powerset, mem_insert, mem_singleton, subset_singleton_iff]
  have hroots : #(roots G) = 0 ∨ #(roots G) = 1 ∨ #(roots G) = 2 := by omega
  rcases hroots with h | h | h
  · -- no root
    have hG0 : G = ∅ := card_roots_eq_zero_iff.1 h
    have hr : roots G = ∅ := card_eq_zero.1 h
    have hP : ∀ γ, hybridPoly G ℓ₁ ℓ₂ W γ = W ∅ ∅ := by
      intro γ
      unfold hybridPoly
      rw [hr, powerset_empty, sum_singleton, empty_sdiff, card_empty, pow_zero, pow_zero, one_mul,
        one_mul, forestBelow_empty_right, hsum ∅ ∅ hK0 hK0]
    rw [hP, hP, hP, h0 hG0]
    ring
  · -- one root
    obtain ⟨R, hR⟩ := card_eq_one.1 h
    have hRm : R ∈ roots G := hR ▸ mem_singleton_self R
    have hGR : forestBelow G {R} = G := by rw [← hR, hall]
    have hK1 : ∀ ℓ t, kingmanTransition ℓ G t = if t = G then 1 else 0 := fun ℓ t => by
      rw [← hGR]
      exact kingmanTransition_forestBelow_singleton hG hRm ℓ t
    have hP : ∀ γ, hybridPoly G ℓ₁ ℓ₂ W γ = γ * W G ∅ + (1 - γ) * W ∅ G := by
      intro γ
      unfold hybridPoly
      rw [hR, hps R, sum_pair (by simp), sdiff_empty, Finset.sdiff_self, card_empty,
        card_singleton, forestBelow_empty_right, hGR, hsum ∅ G hK0 hK1, hsum G ∅ hK1 hK0]
      ring
    rw [hP, hP, hP, (h1 h).1, (h1 h).2]
    ring
  · -- two roots
    obtain ⟨R₁, R₂, hne, hR⟩ := card_eq_two.1 h
    have hR₁ : R₁ ∈ roots G := hR ▸ mem_insert_self _ _
    have hR₂ : R₂ ∈ roots G := hR ▸ mem_insert_of_mem (mem_singleton_self _)
    have hd₁ : ({R₁, R₂} : Finset (Finset X)) \ {R₁} = {R₂} := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h'⟩
        · exact absurd rfl h'
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, fun h' => hne h'.symm⟩
    have hd₂ : ({R₁, R₂} : Finset (Finset X)) \ {R₂} = {R₁} := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h'⟩
        · rfl
        · exact absurd rfl h'
      · rintro rfl
        exact ⟨Or.inl rfl, hne⟩
    have hK₁ := kingmanTransition_forestBelow_singleton hG hR₁
    have hK₂ := kingmanTransition_forestBelow_singleton hG hR₂
    have hP : ∀ γ, hybridPoly G ℓ₁ ℓ₂ W γ =
        (1 - γ) ^ 2 * (∑ t₂, kingmanTransition ℓ₂ G t₂ * W ∅ t₂) +
          γ * (1 - γ) * W (forestBelow G {R₂}) (forestBelow G {R₁}) +
          (γ * (1 - γ) * W (forestBelow G {R₁}) (forestBelow G {R₂}) +
          γ ^ 2 * (∑ t₁, kingmanTransition ℓ₁ G t₁ * W t₁ ∅)) := by
      intro γ
      unfold hybridPoly
      rw [hR, sum_powerset_insert (by simpa using hne), hps R₂, sum_pair (by simp),
        sum_pair (by simp)]
      rw [insert_empty, sdiff_empty, hd₁, hd₂, Finset.sdiff_self, card_empty, card_singleton,
        card_singleton, card_pair hne, forestBelow_empty_right, ← hR, hall, hsumL, hsumR,
        hsum _ _ (hK₂ · ·) (hK₁ · ·), hsum _ _ (hK₁ · ·) (hK₂ · ·)]
      ring
    rw [hP, hP, hP, h2' R₁ R₂ hne hR, h2' R₂ R₁ (Ne.symm hne) (by rw [hR, pair_comm])]
    ring

/-- The polynomial for a forest with one root: the root takes `h₁` or `h₂`. -/
theorem hybridPoly_one_root {G : Finset (Finset X)} (hG : IsGoodForest G) (h1 : #(roots G) = 1)
    (ℓ₁ ℓ₂ : ℝ) (W : Finset (Finset X) → Finset (Finset X) → ℝ) (γ : ℝ) :
    hybridPoly G ℓ₁ ℓ₂ W γ = γ * W G ∅ + (1 - γ) * W ∅ G := by
  have hK0 : ∀ ℓ (t : Finset (Finset X)), kingmanTransition ℓ ∅ t = if t = ∅ then 1 else 0 :=
    fun ℓ t => kingmanTransition_of_card_roots_le_one isForest_empty (by simp [roots]) ℓ t
  have hall : forestBelow G (roots G) = G := by
    have := (forestBelow_union hG (empty_subset (roots G))).1
    rwa [forestBelow_empty_right, empty_union, sdiff_empty] at this
  have hsum : ∀ A B : Finset (Finset X), (∀ ℓ t, kingmanTransition ℓ A t = if t = A then 1 else 0) →
      (∀ ℓ t, kingmanTransition ℓ B t = if t = B then 1 else 0) →
      ∑ t₁, ∑ t₂, kingmanTransition ℓ₁ A t₁ * kingmanTransition ℓ₂ B t₂ * W t₁ t₂ = W A B := by
    intro A B hA hB
    rw [Finset.sum_eq_single A (fun b _ hb => sum_eq_zero fun b₂ _ => by
      rw [hA, ite_eq_right hb, zero_mul, zero_mul]) (by simp)]
    rw [Finset.sum_eq_single B (fun b _ hb => by rw [hA, hB, ite_eq_right hb, mul_zero, zero_mul])
      (by simp)]
    rw [hA, hB, ite_eq_left rfl, ite_eq_left rfl, one_mul, one_mul]
  have hps : ∀ R : Finset X, ({R} : Finset (Finset X)).powerset = {∅, {R}} := by
    intro R
    ext A
    simp only [mem_powerset, mem_insert, mem_singleton, subset_singleton_iff]
  obtain ⟨R, hR⟩ := card_eq_one.1 h1
  have hRm : R ∈ roots G := hR ▸ mem_singleton_self R
  have hGR : forestBelow G {R} = G := by rw [← hR, hall]
  have hK1 : ∀ ℓ t, kingmanTransition ℓ G t = if t = G then 1 else 0 := fun ℓ t => by
    rw [← hGR]
    exact kingmanTransition_forestBelow_singleton hG hRm ℓ t
  unfold hybridPoly
  rw [hR, hps R, sum_pair (by simp), sdiff_empty, Finset.sdiff_self, card_empty,
    card_singleton, forestBelow_empty_right, hGR, hsum ∅ G hK0 hK1, hsum G ∅ hK1 hK0]
  ring

/-- The polynomial for a forest with two roots: both on `h₁`, both on `h₂`, or one on each. -/
theorem hybridPoly_two_roots {G : Finset (Finset X)} (hG : IsGoodForest G) {R₁ R₂ : Finset X}
    (hne : R₁ ≠ R₂) (hR : roots G = {R₁, R₂}) (ℓ₁ ℓ₂ : ℝ)
    (W : Finset (Finset X) → Finset (Finset X) → ℝ) (γ : ℝ) :
    hybridPoly G ℓ₁ ℓ₂ W γ = γ ^ 2 * hybridPoly G ℓ₁ ℓ₂ W 1 + (1 - γ) ^ 2 * hybridPoly G ℓ₁ ℓ₂ W 0 +
      γ * (1 - γ) * (W (forestBelow G {R₁}) (forestBelow G {R₂}) +
        W (forestBelow G {R₂}) (forestBelow G {R₁})) := by
  have hK0 : ∀ ℓ (t : Finset (Finset X)), kingmanTransition ℓ ∅ t = if t = ∅ then 1 else 0 :=
    fun ℓ t => kingmanTransition_of_card_roots_le_one isForest_empty (by simp [roots]) ℓ t
  have hall : forestBelow G (roots G) = G := by
    have := (forestBelow_union hG (empty_subset (roots G))).1
    rwa [forestBelow_empty_right, empty_union, sdiff_empty] at this
  have hsum : ∀ A B : Finset (Finset X), (∀ ℓ t, kingmanTransition ℓ A t = if t = A then 1 else 0) →
      (∀ ℓ t, kingmanTransition ℓ B t = if t = B then 1 else 0) →
      ∑ t₁, ∑ t₂, kingmanTransition ℓ₁ A t₁ * kingmanTransition ℓ₂ B t₂ * W t₁ t₂ = W A B := by
    intro A B hA hB
    rw [Finset.sum_eq_single A (fun b _ hb => sum_eq_zero fun b₂ _ => by
      rw [hA, ite_eq_right hb, zero_mul, zero_mul]) (by simp)]
    rw [Finset.sum_eq_single B (fun b _ hb => by rw [hA, hB, ite_eq_right hb, mul_zero, zero_mul])
      (by simp)]
    rw [hA, hB, ite_eq_left rfl, ite_eq_left rfl, one_mul, one_mul]
  have hsumL : ∀ B : Finset (Finset X), ∑ t₁, ∑ t₂, kingmanTransition ℓ₁ ∅ t₁ *
      kingmanTransition ℓ₂ B t₂ * W t₁ t₂ = ∑ t₂, kingmanTransition ℓ₂ B t₂ * W ∅ t₂ := by
    intro B
    rw [Finset.sum_eq_single ∅ (fun b _ hb => sum_eq_zero fun b₂ _ => by
      rw [hK0, ite_eq_right hb, zero_mul, zero_mul]) (by simp)]
    simp only [hK0, ite_eq_left, one_mul]
  have hsumR : ∀ A : Finset (Finset X), ∑ t₁, ∑ t₂, kingmanTransition ℓ₁ A t₁ *
      kingmanTransition ℓ₂ ∅ t₂ * W t₁ t₂ = ∑ t₁, kingmanTransition ℓ₁ A t₁ * W t₁ ∅ := by
    intro A
    refine sum_congr rfl fun t₁ _ => ?_
    rw [Finset.sum_eq_single ∅ (fun b _ hb => by rw [hK0, ite_eq_right hb, mul_zero, zero_mul])
      (by simp)]
    rw [hK0, ite_eq_left rfl, mul_one]
  have hps : ∀ R : Finset X, ({R} : Finset (Finset X)).powerset = {∅, {R}} := by
    intro R
    ext A
    simp only [mem_powerset, mem_insert, mem_singleton, subset_singleton_iff]
  have hR₁ : R₁ ∈ roots G := hR ▸ mem_insert_self _ _
  have hR₂ : R₂ ∈ roots G := hR ▸ mem_insert_of_mem (mem_singleton_self _)
  have hd₁ : ({R₁, R₂} : Finset (Finset X)) \ {R₁} = {R₂} := by
    ext x
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h'⟩
      · exact absurd rfl h'
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, fun h' => hne h'.symm⟩
  have hd₂ : ({R₁, R₂} : Finset (Finset X)) \ {R₂} = {R₁} := by
    ext x
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h'⟩
      · rfl
      · exact absurd rfl h'
    · rintro rfl
      exact ⟨Or.inl rfl, hne⟩
  have hK₁ := kingmanTransition_forestBelow_singleton hG hR₁
  have hK₂ := kingmanTransition_forestBelow_singleton hG hR₂
  have hP : ∀ γ, hybridPoly G ℓ₁ ℓ₂ W γ =
      (1 - γ) ^ 2 * (∑ t₂, kingmanTransition ℓ₂ G t₂ * W ∅ t₂) +
        γ * (1 - γ) * W (forestBelow G {R₂}) (forestBelow G {R₁}) +
        (γ * (1 - γ) * W (forestBelow G {R₁}) (forestBelow G {R₂}) +
        γ ^ 2 * (∑ t₁, kingmanTransition ℓ₁ G t₁ * W t₁ ∅)) := by
    intro γ
    unfold hybridPoly
    rw [hR, sum_powerset_insert (by simpa using hne), hps R₂, sum_pair (by simp),
      sum_pair (by simp)]
    rw [insert_empty, sdiff_empty, hd₁, hd₂, Finset.sdiff_self, card_empty, card_singleton,
      card_singleton, card_pair hne, forestBelow_empty_right, ← hR, hall, hsumL, hsumR,
      hsum _ _ (hK₂ · ·) (hK₁ · ·), hsum _ _ (hK₁ · ·) (hK₂ · ·)]
    ring
  rw [hP, hP, hP]
  ring

end Poly

section Upper

/-- **A forest injected at a cut vertex `r` with the only arc `p` into it**: it goes up `p`, and the
process above is that of the part above `r` (`upperLaw`). -/
theorem cherryMass_cutInj_eq_upperLaw {N : RootedNetwork V E X} {r : V} {p : E}
    (hN : N.IsPhylogenetic) (hc : IsCut N r) (hpr : N.graph.target p = r)
    (huniq : ∀ g, N.graph.target g = r → g = p) {θ : MetricData E} (h1 : θ.inheritance p = 1)
    (G : Finset (Finset X)) (q : QuartetTree X) :
    cherryMass N θ 0 (cutInj N r (taxaInj N univ) G) q =
      ∑ t, kingmanTransition (θ.length p) G t * cherryOf q (upperLaw N hN hc hpr huniq θ t) := by
  rw [cherryMass_eq_sum_arc hN hc hpr huniq h1]
  refine sum_congr rfl fun t _ => ?_
  have hlow : lowerInj (cutVertices N r) (cutInj N r (taxaInj N univ) G) =
      atRoot (cutLower N r hc) G := by
    funext w
    unfold lowerInj atRoot
    by_cases hw : w = (cutLower N r hc).root
    · rw [ite_eq_left hw, hw]
      exact cutInj_self N r _ G
    · rw [ite_eq_right hw]
      exact cutInj_of_reaches_of_ne N r _ G w.2 fun h => hw (Subtype.ext h)
  have hlaw : arcLaw N r hc θ 0 p (cutInj N r (taxaInj N univ) G) t =
      kingmanTransition (θ.length p) G t := by
    unfold arcLaw
    rw [hlow, Finset.sum_eq_single G]
    · rw [rootDist_atRoot (cutLower_acyclic N r hN hc) (fun e h => e.2.2 (congrArg Subtype.val h)),
        ite_eq_left rfl, one_mul]
    · intro F' _ hF'
      rw [rootDist_atRoot (cutLower_acyclic N r hN hc) (fun e h => e.2.2 (congrArg Subtype.val h)),
        ite_eq_right hF', zero_mul]
    · simp
  have hR : ∀ F₀, rootDist N θ 0 (liftInj N p (cutInj N r (taxaInj N univ) G) t) F₀ =
      upperLaw N hN hc hpr huniq θ t F₀ := by
    intro F₀
    have := sum_rootDist_liftInj hN hc hpr huniq h1 le_rfl (cutInj N r (taxaInj N univ) G) t
      (fun F => if F = F₀ then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at this
    rw [this]
    unfold upperLaw
    congr 1
    funext w
    unfold upperInj
    rw [cutVertices_inl, cutInj_of_not_reaches N r _ G w.2]
  rw [hlaw, cherryMass_eq_cherryOf, funext hR]

end Upper

section Valid

variable {N : RootedNetwork V E X} {v : V} {h₁ h₂ : E}

omit [Fintype V] [Fintype E] in
/-- **The forests at the sources of the hybrid arcs make a valid injection** when they are binary
forests on disjoint sets of lineages that no other vertex carries, at distinct vertices carrying
nothing else. -/
theorem validInj_hybInj {inj : V → Finset (Finset X)} (hinj : ValidInj inj)
    {t₁ t₂ : Finset (Finset X)} (hg₁ : IsGoodForest t₁) (hg₂ : IsGoodForest t₂)
    (hd : Disjoint (lineages t₁) (lineages t₂)) (hs : N.graph.source h₁ ≠ N.graph.source h₂)
    (he₁ : inj (N.graph.source h₁) = ∅) (he₂ : inj (N.graph.source h₂) = ∅)
    (hl : ∀ x, x ∈ lineages t₁ ∨ x ∈ lineages t₂ → ∀ u, ¬ N.graph.Reaches v u →
      x ∉ lineages (inj u)) :
    ValidInj (hybInj N v h₁ h₂ inj t₁ t₂) := by
  have hmem : ∀ u x, x ∈ lineages (hybInj N v h₁ h₂ inj t₁ t₂ u) ↔ ¬ N.graph.Reaches v u ∧
      (x ∈ lineages (inj u) ∨ (u = N.graph.source h₁ ∧ x ∈ lineages t₁) ∨
        (u = N.graph.source h₂ ∧ x ∈ lineages t₂)) := by
    intro u x
    unfold hybInj
    split_ifs with h hu₁ hu₂ hu₂ <;> simp_all
  refine ⟨fun u => ?_, fun u u' huu => disjoint_left.2 fun x hx hx' => ?_⟩
  · unfold hybInj
    split_ifs with h hu₁ hu₂ hu₂
    · exact isGoodForest_empty
    · exact absurd (hu₁.symm.trans hu₂) hs
    · rw [hu₁, he₁, empty_union, union_empty]
      exact hg₁
    · rw [hu₂, he₂, empty_union, empty_union]
      exact hg₂
    · rw [union_empty, union_empty]
      exact hinj.good u
  · rw [hmem] at hx hx'
    obtain ⟨hvu, hx⟩ := hx
    obtain ⟨hvu', hx'⟩ := hx'
    rcases hx with hx | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> rcases hx' with hx' | ⟨rfl, hx'⟩ | ⟨rfl, hx'⟩
    · exact disjoint_left.1 (hinj.disj u u' huu) hx hx'
    · exact hl x (Or.inl hx') u hvu hx
    · exact hl x (Or.inr hx') u hvu hx
    · exact hl x (Or.inl hx) u' hvu' hx'
    · exact huu rfl
    · exact disjoint_left.1 hd hx hx'
    · exact hl x (Or.inr hx) u' hvu' hx'
    · exact disjoint_left.1 hd hx' hx
    · exact huu rfl

end Valid

/-- **Singletons do not change `quartetValue`**: they are neither clusters of two lineages nor
cherries. -/
theorem quartetValue_union_of_card_eq_one (q : QuartetTree X) {S F : Finset (Finset X)}
    (hS : ∀ C ∈ S, #C = 1) : quartetValue q (S ∪ F) = quartetValue q F := by
  unfold quartetValue
  have h2 : (∃ C ∈ S ∪ F, #C = 2) ↔ ∃ C ∈ F, #C = 2 := by
    constructor
    · rintro ⟨C, hC, h⟩
      rcases mem_union.1 hC with hC | hC
      · rw [hS C hC] at h
        omega
      · exact ⟨C, hC, h⟩
    · rintro ⟨C, hC, h⟩
      exact ⟨C, mem_union_right _ hC, h⟩
  have hq : (∃ C ∈ S ∪ F, C ∈ q.val) ↔ ∃ C ∈ F, C ∈ q.val := by
    constructor
    · rintro ⟨C, hC, h⟩
      rcases mem_union.1 hC with hC | hC
      · have := q.card_of_mem h
        rw [hS C hC] at this
        omega
      · exact ⟨C, hC, h⟩
    · rintro ⟨C, hC, h⟩
      exact ⟨C, mem_union_right _ hC, h⟩
  simp only [h2, hq]

end Banos2019
