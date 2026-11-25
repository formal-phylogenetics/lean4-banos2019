module

public import Banos2019.Quartet.Defs
public import Phylogenetics.NMSC.Glue
public import Phylogenetics.NMSC.InducedAbove
public import Phylogenetics.NMSC.Symmetry
public import Phylogenetics.NMSC.Witness

/-!
# Conditioning on the lineages at a vertex (Baños 2019, Section 5)

The proofs of Lemmas 7–11 condition on the number of lineages at a node of a quartet network. This
module gives the network multispecies coalescent the corresponding decomposition, for any network.

A vertex `r` is a *cut vertex* (`IsCut`) when it is not above the root and the vertices below it are
entered only at `r`. The network is then glued (`NMSC.IsGlued`) from its part `cutUpper` not below
`r` and its part `cutLower` below `r`, rooted at `r`, along the arcs into `r` (`isGlued_cut`).

* `isGlued_sum_mul_eq`: gluing, with a function of the forests at the tops of the joining arcs.
* `rootDist_eq_sum_cut`, `cherryMass_eq_sum_cut`: the *Markov property at a cut vertex*: the process
  is the mixture, over the law of the forest `F` arriving at `r` (the law at the root of
  `cutLower`), of the process with `F` injected at `r` and nothing else below `r` (`cutInj`).
* `sum_mul_arc`, `rootDist_eq_sum_arc`: the *Markov property at the arc `c`* into a cut vertex: the
  law `arcLaw` of the forest at the top of `c`, and the process with that forest at the source of
  `c` (`NMSC.liftInj`), which is the process of `cutUpper` (`sum_rootDist_liftInj`).
* `good_of_rootDist_cutLower_ne_zero`, `good_of_arcLaw_ne_zero`, `sum_rootDist_cutLower`,
  `rootDist_cutLower_of_one`: the support and the mass of these laws.
* `cf_eq_sum_jointCF`, `jointCF_eq_sum_arc`, `probLineages_eq_sum_arc`: for the number `K` of
  lineages at the top of `c`, `CF = ∑ₖ P(K = k) CF(· | K = k)` (`jointCF`), and `P(K = k)` and
  `P(K = k) CF(· | K = k)` from `arcLaw`.
* Four taxa: `cf_eq_cherryMass`; `cherryMass_eq_quartetValue`, `cherryMass_liftInj`,
  `jointCF_eq_sum_quartetValue`: three lineages in a forest at a vertex and the fourth taxon
  elsewhere give `NMSC.quartetValue` (a cluster of two lineages decides the quartet tree, otherwise
  `1/3` by exchangeability); `cf_eq_of_one_below`: one taxon below a cut vertex.
* `geneTreeDist_deleteArc`, `cf_deleteArc`: deleting an arc of inheritance `0` (`Q₁⊕`, `Q₂⊕`);
  `cf_eq_mixture`: with a single taxon below a hybrid node, `CF = γ CF(Q₁⊕) + (1 - γ) CF(Q₂⊕)`.

The law at the root of `cutLower` depends only on the part below `r`, so two networks with
isomorphic parts below cut vertices have the same law there (`NMSC.rootDist_congr`;
`Banos2019.Quartet.Contract` for `Q₀⊕` and `Q₁⊕`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

/-! ### Histories with a forest at the root only -/

omit [Fintype V] [Fintype E] [Fintype X] in
theorem ne_zero_of_ite_ne_zero' {p : Prop} [Decidable p] {a : ℝ} (h : (if p then a else 0) ≠ 0) :
    p :=
  by_contra fun hp => h (ite_eq_right hp)

section AtRoot

variable {V' E' : Type*} [Fintype V'] [Fintype E'] (M : RootedNetwork V' E' X)

/-- The forest `F` injected at the root, and nothing elsewhere. -/
def atRoot (F : Finset (Finset X)) : V' → Finset (Finset X) := fun w => if w = M.root then F else ∅

omit [Fintype V'] [Fintype E'] [Fintype X] in
theorem atRoot_root (F : Finset (Finset X)) : atRoot M F M.root = F := ite_eq_left rfl

omit [Fintype V'] [Fintype E'] [Fintype X] in
theorem atRoot_of_ne (F : Finset (Finset X)) {w : V'} (hw : w ≠ M.root) : atRoot M F w = ∅ :=
  ite_eq_right hw

omit [Fintype V'] in
/-- An allocation of the empty forest puts the empty forest on every arc into the vertex. -/
theorem eq_empty_of_allocationFactor_empty_ne_zero {θ : MetricData E'} {ρ : ℝ} {v : V'}
    {b : E' → Finset (Finset X)} (h : allocationFactor M θ ρ (∅ : Finset (Finset X)) v b ≠ 0)
    {e : E'} (he : M.graph.target e = v) : b e = ∅ := by
  unfold allocationFactor at h
  obtain ⟨a, -, ha⟩ := exists_ne_zero_of_sum_ne_zero h
  have hc := (ne_zero_of_ite_ne_zero' ha) ⟨e, he⟩
  rw [hc]
  ext A
  simp [mem_forestBelow]

variable {M}

/-- **Only the root receives a forest**: in a finite acyclic network whose arcs do not enter the
root, a history of nonzero weight carries the empty forest on every arc. -/
theorem eq_empty_of_injWeight_atRoot_ne_zero (hacyc : ∀ v, ¬ Relation.TransGen M.graph.Adj v v)
    (hroot : ∀ e, M.graph.target e ≠ M.root) {θ : MetricData E'} {ρ : ℝ} {F : Finset (Finset X)}
    {b t : E' → Finset (Finset X)} (h : injWeight M θ ρ (atRoot M F) b t ≠ 0) (e : E') :
    b e = ∅ ∧ t e = ∅ := by
  let rel : V' → V' → Prop := fun a c => Relation.TransGen M.graph.Adj c a
  have : IsTrans V' rel := ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
  have : Std.Irrefl rel := ⟨fun a ha => hacyc a ha⟩
  have hwf : WellFounded rel := Finite.wellFounded_of_trans_of_irrefl rel
  suffices hall : ∀ w, ∀ e, M.graph.target e = w → b e = ∅ ∧ t e = ∅ from hall _ e rfl
  intro w
  induction w using hwf.induction with
  | _ w ih =>
    intro e he
    have hw : w ≠ M.root := he ▸ hroot e
    have hv : vertexWeight M θ ρ (atRoot M F) w b t ≠ 0 :=
      prod_ne_zero_iff.1 h w (mem_erase.2 ⟨hw, mem_univ _⟩)
    have harr : arriving M (atRoot M F) t w = ∅ := by
      unfold arriving
      rw [atRoot_of_ne M F hw, empty_union]
      refine eq_empty_of_forall_notMem fun A hA => ?_
      obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
      have hfw := (mem_filter.1 hf).2
      rw [(ih (M.graph.target f) (.single ⟨f, hfw, rfl⟩) f rfl).2] at hAf
      exact notMem_empty _ hAf
    unfold vertexWeight at hv
    rw [harr] at hv
    have hb : b e = ∅ := eq_empty_of_allocationFactor_empty_ne_zero M (left_ne_zero_of_mul hv) he
    have hk : kingmanTransition (θ.length e) (b e) (t e) ≠ 0 :=
      prod_ne_zero_iff.1 (right_ne_zero_of_mul hv) e (mem_arcsInto.2 he)
    rw [hb, kingmanTransition_of_card_roots_le_one isForest_empty (by simp)] at hk
    exact ⟨hb, ne_zero_of_ite_ne_zero' hk⟩

/-- **The law at the root when only the root receives a forest** `F`: the forest `F` itself. -/
theorem rootDist_atRoot (hacyc : ∀ v, ¬ Relation.TransGen M.graph.Adj v v)
    (hroot : ∀ e, M.graph.target e ≠ M.root) (θ : MetricData E') (ρ : ℝ)
    (F F' : Finset (Finset X)) :
    rootDist M θ ρ (atRoot M F) F' = if F' = F then 1 else 0 := by
  have hz : ∀ b t : E' → Finset (Finset X), (b ≠ fun _ => ∅) ∨ (t ≠ fun _ => ∅) →
      injWeight M θ ρ (atRoot M F) b t = 0 := by
    intro b t hbt
    by_contra hne
    rcases hbt with hb | ht
    · exact hb (funext fun e => (eq_empty_of_injWeight_atRoot_ne_zero hacyc hroot hne e).1)
    · exact ht (funext fun e => (eq_empty_of_injWeight_atRoot_ne_zero hacyc hroot hne e).2)
  unfold rootDist
  rw [Finset.sum_eq_single (fun _ => ∅), Finset.sum_eq_single (fun _ => ∅)]
  · have harr : arriving M (atRoot M F) (fun _ => ∅) M.root = F := by
      unfold arriving
      rw [atRoot_root]
      simp
    have hw : injWeight M θ ρ (atRoot M F) (fun _ => ∅) (fun _ => ∅) = 1 := by
      unfold injWeight
      refine prod_eq_one fun w hw => ?_
      have hwr : w ≠ M.root := ne_of_mem_erase hw
      unfold vertexWeight
      have harrw : arriving M (atRoot M F) (fun _ => ∅) w = ∅ := by
        unfold arriving
        rw [atRoot_of_ne M F hwr, empty_union]
        ext A
        simp
      rw [harrw, allocationFactor_empty_eq_one fun _ _ => rfl, one_mul]
      refine prod_eq_one fun e _ => ?_
      rw [kingmanTransition_of_card_roots_le_one isForest_empty (by simp), ite_eq_left rfl]
    rw [harr, hw, one_mul]
    by_cases h : F' = F
    · rw [ite_eq_left h.symm, ite_eq_left h]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
  · intro t _ ht
    rw [hz _ t (Or.inr ht), zero_mul]
  · simp
  · intro b _ hb
    exact sum_eq_zero fun t _ => by rw [hz b t (Or.inl hb), zero_mul]
  · simp

end AtRoot

/-! ### Gluing, with a function of the forests at the tops of the joining arcs -/

section GlueSum

variable {V E L V₀ E₀ V₁ E₁ P : Type*} [Fintype V] [Fintype E] [Fintype L]
  [Fintype V₀] [Fintype E₀] [Fintype V₁] [Fintype E₁] [Fintype P]
  {N : RootedNetwork V E L} {N₀ : RootedNetwork V₀ E₀ L} {N₁ : RootedNetwork V₁ E₁ L}
  {θ : MetricData E} {θ₀ : MetricData E₀} {θ₁ : MetricData E₁} {ρ : ℝ}
  {fV : V₀ ⊕ V₁ ≃ V} {fE : E₀ ⊕ P ⊕ E₁ ≃ E} {s : P → V₀} {ℓ : P → ℝ}

/-- **Gluing**, for a function `Ψ` of the forests at the tops of the joining arcs and a function `Φ`
of the forest arriving at the root: the history of the lower part gives the law of the forest
arriving at its root, the allocation there and the coalescent along the joining arcs give the
forests at their tops, and the upper part is the process with those forests injected. -/
theorem isGlued_sum_mul_eq (hg : IsGlued N θ N₀ θ₀ N₁ θ₁ fV fE s ℓ)
    (inj : V → Finset (Finset L)) {AF : Finset (Finset L) → (P → Finset (Finset L)) → ℝ}
    (hAF : ∀ F bot, allocationFactor N θ ρ F (fV (.inr N₁.root)) bot =
      AF F fun p => bot (fE (.inr (.inl p))))
    (Ψ : (P → Finset (Finset L)) → ℝ) (Φ : Finset (Finset L) → ℝ) :
    ∑ bot : E → Finset (Finset L), ∑ top : E → Finset (Finset L),
      injWeight N θ ρ inj bot top *
        (Ψ (fun p => top (fE (.inr (.inl p)))) * Φ (arriving N inj top N.root)) =
      ∑ F₁, rootDist N₁ θ₁ ρ (lowerInj fV inj) F₁ *
        ∑ bP : P → Finset (Finset L), AF F₁ bP * ∑ tP : P → Finset (Finset L),
          (∏ p, kingmanTransition (ℓ p) (bP p) (tP p)) *
            (Ψ tP * ∑ F, rootDist N₀ θ₀ ρ (upperInj fV s inj tP) F * Φ F) := by
  rw [sum_rootDist_mul N₁ θ₁ ρ (lowerInj fV inj) fun F₁ => ∑ bP : P → Finset (Finset L),
    AF F₁ bP * ∑ tP : P → Finset (Finset L), (∏ p, kingmanTransition (ℓ p) (bP p) (tP p)) *
      (Ψ tP * ∑ F, rootDist N₀ θ₀ ρ (upperInj fV s inj tP) F * Φ F)]
  simp only [sum_rootDist_mul]
  rw [sum_arcs fE]
  simp only [sum_arcs fE (α := Finset (Finset L)) (fun top => _ * _)]
  have hshuffle := sum_shuffle (A := E₀ → Finset (Finset L)) (B := P → Finset (Finset L))
    (C := E₁ → Finset (Finset L)) (D := E₀ → Finset (Finset L)) (F := P → Finset (Finset L))
    (G := E₁ → Finset (Finset L)) fun b₀ bP b₁ t₀ tP t₁ =>
      injWeight N θ ρ inj (joinArcs fE b₀ bP b₁) (joinArcs fE t₀ tP t₁) *
        (Ψ (fun p => joinArcs fE t₀ tP t₁ (fE (.inr (.inl p)))) *
          Φ (arriving N inj (joinArcs fE t₀ tP t₁) N.root))
  rw [hshuffle]
  refine sum_congr rfl fun b₁ _ => sum_congr rfl fun t₁ _ => ?_
  simp only [mul_sum]
  refine sum_congr rfl fun bP _ => sum_congr rfl fun tP _ => sum_congr rfl fun b₀ _ =>
    sum_congr rfl fun t₀ _ => ?_
  rw [hg.injWeight_eq inj b₀ t₀ bP tP b₁ t₁ hAF, hg.root, hg.arriving_upper]
  simp only [joinArcs_inrl]
  ring

end GlueSum

/-! ### The cut at a vertex -/

section Cut

variable (N : RootedNetwork V E X) (r : V)

/-- `r` is a *cut vertex*: it is not above the root, and the vertices below it are entered only at
`r`, so that every arc into a vertex below `r` other than `r` leaves a vertex below `r`. -/
structure IsCut : Prop where
  not_reaches_root : ¬ N.graph.Reaches r N.root
  entry : ∀ e, N.graph.Reaches r (N.graph.target e) → N.graph.target e ≠ r →
    N.graph.Reaches r (N.graph.source e)

variable {N r}

omit [Fintype V] [Fintype E] [Fintype X] in
theorem not_reaches_source_of_not_reaches_target {e : E}
    (he : ¬ N.graph.Reaches r (N.graph.target e)) : ¬ N.graph.Reaches r (N.graph.source e) :=
  fun hs => he (hs.tail ⟨e, rfl, rfl⟩)

omit [Fintype V] [Fintype E] [Fintype X] in
theorem not_reaches_source_of_target_eq (hN : N.IsPhylogenetic) {e : E}
    (he : N.graph.target e = r) : ¬ N.graph.Reaches r (N.graph.source e) := fun hs =>
  hN.acyclic r (Relation.TransGen.tail' hs ⟨e, rfl, he⟩)

variable (N r)

/-- The part of the network not below the cut vertex `r`. Only its graph and root matter; its leaves
are put at the root. -/
def cutUpper (hc : IsCut N r) :
    RootedNetwork {w // ¬ N.graph.Reaches r w} {e // ¬ N.graph.Reaches r (N.graph.target e)} X where
  graph :=
    { source := fun e => ⟨N.graph.source e.1, not_reaches_source_of_not_reaches_target e.2⟩
      target := fun e => ⟨N.graph.target e.1, e.2⟩ }
  root := ⟨N.root, hc.not_reaches_root⟩
  leaf _ := ⟨N.root, hc.not_reaches_root⟩

/-- The part of the network below the cut vertex `r`, rooted at `r`: the vertices below `r` and the
arcs into them other than those into `r`. Only its graph and root matter; its leaves are put at the
root. -/
def cutLower (hc : IsCut N r) :
    RootedNetwork {w // N.graph.Reaches r w}
      {e // N.graph.Reaches r (N.graph.target e) ∧ N.graph.target e ≠ r} X where
  graph :=
    { source := fun e => ⟨N.graph.source e.1, hc.entry e.1 e.2.1 e.2.2⟩
      target := fun e => ⟨N.graph.target e.1, e.2.1⟩ }
  root := ⟨r, .refl⟩
  leaf _ := ⟨r, .refl⟩

/-- The parameters of `cutUpper`. -/
def cutUpperMetric (θ : MetricData E) : MetricData {e // ¬ N.graph.Reaches r (N.graph.target e)} :=
  ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩

/-- The parameters of `cutLower`. -/
def cutLowerMetric (θ : MetricData E) :
    MetricData {e // N.graph.Reaches r (N.graph.target e) ∧ N.graph.target e ≠ r} :=
  ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩

/-- The vertices: those not below `r`, and those below `r`. -/
def cutVertices : {w // ¬ N.graph.Reaches r w} ⊕ {w // N.graph.Reaches r w} ≃ V :=
  (Equiv.sumComm _ _).trans (Equiv.sumCompl fun w => N.graph.Reaches r w)

omit [Fintype V] [Fintype E] [Fintype X] in
@[simp] theorem cutVertices_inl (w : {w // ¬ N.graph.Reaches r w}) :
    cutVertices N r (.inl w) = w.1 := rfl

omit [Fintype V] [Fintype E] [Fintype X] in
@[simp] theorem cutVertices_inr (w : {w // N.graph.Reaches r w}) :
    cutVertices N r (.inr w) = w.1 := rfl

variable {P : Type*} [Fintype P]

/-- The arcs: those into a vertex not below `r`, those into `r` (indexed by `P`), and those into a
vertex below `r` other than `r`. -/
def cutArcs (ι : P ≃ {e // N.graph.target e = r}) :
    {e // ¬ N.graph.Reaches r (N.graph.target e)} ⊕ P ⊕
      {e // N.graph.Reaches r (N.graph.target e) ∧ N.graph.target e ≠ r} ≃ E where
  toFun := Sum.elim Subtype.val (Sum.elim (fun p => (ι p).1) Subtype.val)
  invFun e :=
    if h : N.graph.Reaches r (N.graph.target e) then
      if h' : N.graph.target e = r then .inr (.inl (ι.symm ⟨e, h'⟩)) else .inr (.inr ⟨e, h, h'⟩)
    else .inl ⟨e, h⟩
  left_inv := by
    rintro (e | p | e)
    · simp [e.2]
    · have h1 : N.graph.Reaches r (N.graph.target (ι p).1) := by rw [(ι p).2]; exact .refl
      dsimp only [Sum.elim_inr, Sum.elim_inl]
      rw [dite_eq_left h1, dite_eq_left (ι p).2]
      simp
    · simp [e.2.1, e.2.2]
  right_inv e := by
    by_cases h : N.graph.Reaches r (N.graph.target e)
    · by_cases h' : N.graph.target e = r
      · change Sum.elim Subtype.val (Sum.elim (fun p => (ι p).1) Subtype.val)
          (if h : N.graph.Reaches r (N.graph.target e) then
            if h' : N.graph.target e = r then .inr (.inl
              (ι.symm ⟨e, h'⟩)) else .inr (.inr ⟨e, h, h'⟩)
          else .inl ⟨e, h⟩) = e
        rw [dite_eq_left h, dite_eq_left h']
        simp
      · simp [h, h']
    · simp [h]

omit [Fintype V] [Fintype E] [Fintype X] [Fintype P] in
@[simp] theorem cutArcs_inl (ι : P ≃ {e // N.graph.target e = r})
    (e : {e // ¬ N.graph.Reaches r (N.graph.target e)}) : cutArcs N r ι (.inl e) = e.1 := rfl

omit [Fintype V] [Fintype E] [Fintype X] [Fintype P] in
@[simp] theorem cutArcs_inrl (ι : P ≃ {e // N.graph.target e = r}) (p : P) :
    cutArcs N r ι (.inr (.inl p)) = (ι p).1 := rfl

omit [Fintype V] [Fintype E] [Fintype X] [Fintype P] in
@[simp] theorem cutArcs_inrr (ι : P ≃ {e // N.graph.target e = r})
    (e : {e // N.graph.Reaches r (N.graph.target e) ∧ N.graph.target e ≠ r}) :
    cutArcs N r ι (.inr (.inr e)) = e.1 := rfl

/-- The sources of the arcs into `r`, in `cutUpper`. -/
def cutSource (hN : N.IsPhylogenetic) (ι : P ≃ {e // N.graph.target e = r}) (p : P) :
    {w // ¬ N.graph.Reaches r w} :=
  ⟨N.graph.source (ι p).1, not_reaches_source_of_target_eq hN (ι p).2⟩

omit [Fintype V] [Fintype E] [Fintype X] [Fintype P] in
/-- **The network is glued from its parts above and below a cut vertex.** -/
theorem isGlued_cut (hN : N.IsPhylogenetic) (hc : IsCut N r) (θ : MetricData E)
    (ι : P ≃ {e // N.graph.target e = r}) :
    IsGlued N θ (cutUpper N r hc) (cutUpperMetric N r θ) (cutLower N r hc) (cutLowerMetric N r θ)
      (cutVertices N r) (cutArcs N r ι) (cutSource N r hN ι) (fun p => θ.length (ι p).1) where
  source₀ _ := rfl
  target₀ _ := rfl
  sourceP _ := rfl
  targetP p := (ι p).2
  source₁ _ := rfl
  target₁ _ := rfl
  root := rfl
  not_target_root e h := e.2.2 (congrArg Subtype.val h)
  length₀ _ := rfl
  lengthP _ := rfl
  length₁ _ := rfl
  inheritance₀ _ := rfl
  inheritance₁ _ := rfl

/-- The injected forests with the forest `F` at the cut vertex `r` and nothing else below `r`. -/
def cutInj (inj : V → Finset (Finset X)) (F : Finset (Finset X)) : V → Finset (Finset X) :=
  fun w => if N.graph.Reaches r w then (if w = r then F else ∅) else inj w

omit [Fintype V] [Fintype E] [Fintype X] in
theorem cutInj_self (inj : V → Finset (Finset X)) (F : Finset (Finset X)) :
    cutInj N r inj F r = F := by
  unfold cutInj
  have h : N.graph.Reaches r r := Relation.ReflTransGen.refl
  rw [ite_eq_left h, ite_eq_left rfl]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem cutInj_of_not_reaches (inj : V → Finset (Finset X)) (F : Finset (Finset X)) {w : V}
    (hw : ¬ N.graph.Reaches r w) : cutInj N r inj F w = inj w := by
  simp [cutInj, hw]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem cutInj_of_reaches_of_ne (inj : V → Finset (Finset X)) (F : Finset (Finset X)) {w : V}
    (hw : N.graph.Reaches r w) (hne : w ≠ r) : cutInj N r inj F w = ∅ := by
  simp [cutInj, hw, hne]

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The part below `r` is acyclic. -/
theorem cutLower_acyclic (hN : N.IsPhylogenetic) (hc : IsCut N r) (v : {w // N.graph.Reaches r w}) :
    ¬ Relation.TransGen (cutLower N r hc).graph.Adj v v := by
  have hl : ∀ u w : {w // N.graph.Reaches r w}, Relation.TransGen (cutLower N r hc).graph.Adj u w →
      Relation.TransGen N.graph.Adj u.1 w.1 := by
    intro u w h
    induction h with
    | single h =>
      obtain ⟨f, rfl, rfl⟩ := h
      exact .single ⟨f.1, rfl, rfl⟩
    | tail _ h ih =>
      obtain ⟨f, rfl, rfl⟩ := h
      exact ih.tail ⟨f.1, rfl, rfl⟩
  exact fun h => hN.acyclic v.1 (hl v v h)

variable {N r}

/-- **The Markov property at a cut vertex.** The law at the root is the mixture, over the law of the
forest `F` arriving at the cut vertex `r` (the law at the root of `cutLower`), of the law at the
root when `F` is injected at `r` and nothing else below `r`. -/
theorem rootDist_eq_sum_cut (hN : N.IsPhylogenetic) (hc : IsCut N r) (θ : MetricData E) (ρ : ℝ)
    (inj : V → Finset (Finset X)) (F : Finset (Finset X)) :
    rootDist N θ ρ inj F =
      ∑ F₁, rootDist (cutLower N r hc) (cutLowerMetric N r θ) ρ
        (lowerInj (cutVertices N r) inj) F₁ *
        rootDist N θ ρ (cutInj N r inj F₁) F := by
  let ι : {e // N.graph.target e = r} ≃ {e // N.graph.target e = r} := Equiv.refl _
  have hg := isGlued_cut N r hN hc θ ι
  let AF : Finset (Finset X) → ({e // N.graph.target e = r} → Finset (Finset X)) → ℝ :=
    fun F b => allocationFactor N θ ρ F r fun e => if h : N.graph.target e = r then b ⟨e, h⟩ else ∅
  have hAF : ∀ F bot, allocationFactor N θ ρ F
    ((cutVertices N r) (.inr (cutLower N r hc).root)) bot =
      AF F fun p => bot (cutArcs N r ι (.inr (.inl p))) := by
    intro F bot
    refine allocationFactor_congr fun e he => ?_
    simp only [cutVertices_inr, cutLower] at he
    simp [he, ι]
  rw [hg.rootDist_eq inj hAF F]
  refine sum_congr rfl fun F₁ _ => ?_
  congr 1
  rw [hg.rootDist_eq (cutInj N r inj F₁) hAF F]
  have hlow : lowerInj (cutVertices N r) (cutInj N r inj F₁) = atRoot (cutLower N r hc) F₁ := by
    funext w
    unfold lowerInj atRoot
    by_cases hw : w = (cutLower N r hc).root
    · rw [ite_eq_left hw, hw]
      exact cutInj_self N r inj F₁
    · rw [ite_eq_right hw]
      refine cutInj_of_reaches_of_ne N r inj F₁ w.2 fun h => hw (Subtype.ext h)
  have hup : ∀ t, upperInj (cutVertices N r) (cutSource N r hN ι) (cutInj N r inj F₁) t =
      upperInj (cutVertices N r) (cutSource N r hN ι) inj t := by
    intro t
    funext w
    unfold upperInj
    rw [cutVertices_inl, cutInj_of_not_reaches N r inj F₁ w.2]
  simp only [hlow, hup]
  rw [Finset.sum_eq_single F₁]
  · rw [rootDist_atRoot (cutLower_acyclic N r hN hc) (fun e h => e.2.2 (congrArg Subtype.val h)),
      ite_eq_left rfl, one_mul]
  · intro F' _ hF'
    rw [rootDist_atRoot (cutLower_acyclic N r hN hc) (fun e h => e.2.2 (congrArg Subtype.val h)),
      ite_eq_right hF', zero_mul]
  · simp

/-- **The Markov property at a cut vertex**, for the mass of a quartet tree. -/
theorem cherryMass_eq_sum_cut (hN : N.IsPhylogenetic) (hc : IsCut N r) (θ : MetricData E) (ρ : ℝ)
    (inj : V → Finset (Finset X)) (q : QuartetTree X) :
    cherryMass N θ ρ inj q =
      ∑ F₁, rootDist (cutLower N r hc) (cutLowerMetric N r θ) ρ
        (lowerInj (cutVertices N r) inj) F₁ *
        cherryMass N θ ρ (cutInj N r inj F₁) q := by
  unfold cherryMass
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun H _ => ?_
  split_ifs
  · rw [injDist_eq_sum_rootDist]
    simp only [rootDist_eq_sum_cut hN hc θ ρ inj, sum_mul, injDist_eq_sum_rootDist, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun F₁ _ => sum_congr rfl fun F _ => ?_
    ring
  · simp

omit [Fintype E] [Fintype X] in
theorem target_mem_strictBelow_of_source (hN : N.IsPhylogenetic) {e : E}
    (he : N.graph.source e = r) : N.graph.target e ∈ strictBelow N r :=
  mem_strictBelow.2 ⟨.single ⟨e, he, rfl⟩, fun h => hN.acyclic r (.single ⟨e, he, h⟩)⟩

/-- **The forest arriving at a cut vertex**: in the support of its law it is a binary forest on the
lineages injected below `r`. -/
theorem good_of_rootDist_cutLower_ne_zero (hN : N.IsPhylogenetic) (hc : IsCut N r)
    {θ : MetricData E} {ρ : ℝ} {inj : V → Finset (Finset X)} (hinj : ValidInj inj)
    {F₁ : Finset (Finset X)}
    (h : rootDist (cutLower N r hc) (cutLowerMetric N r θ) ρ
        (lowerInj (cutVertices N r) inj) F₁ ≠ 0) :
    IsGoodForest F₁ ∧ ∀ x, x ∈ lineages F₁ ↔ ∃ u, N.graph.Reaches r u ∧ x ∈ lineages (inj u) := by
  unfold rootDist at h
  obtain ⟨b₁, -, hb⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨t₁, -, ht⟩ := exists_ne_zero_of_sum_ne_zero hb
  have hw := left_ne_zero_of_mul ht
  have harr : arriving (cutLower N r hc) (lowerInj (cutVertices N r) inj) t₁
    (cutLower N r hc).root =
      F₁ := by
    by_contra hne
    rw [ite_eq_right hne, mul_zero] at ht
    exact ht rfl
  let ι : {e // N.graph.target e = r} ≃ {e // N.graph.target e = r} := Equiv.refl _
  have hg := isGlued_cut N r hN hc θ ι
  let bot := joinArcs (cutArcs N r ι) (fun _ => ∅) (fun _ => ∅) b₁
  let top := joinArcs (cutArcs N r ι) (fun _ => ∅) (fun _ => ∅) t₁
  have hset : strictBelow N r = ((univ : Finset {w // N.graph.Reaches r w}).erase
      (cutLower N r hc).root).map (Function.Embedding.subtype _) := by
    ext w
    simp only [mem_strictBelow, mem_map, mem_erase, mem_univ, and_true,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨hw, hne⟩
      exact ⟨⟨w, hw⟩, fun h => hne (congrArg Subtype.val h), rfl⟩
    · rintro ⟨w', hne, rfl⟩
      exact ⟨w'.2, fun h => hne (Subtype.ext h)⟩
  have hprod : ∏ w ∈ strictBelow N r, vertexWeight N θ ρ inj w bot top ≠ 0 := by
    rw [hset, prod_map]
    refine ne_of_eq_of_ne (prod_congr rfl fun w hw' =>
      hg.vertexWeight_lower inj (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) b₁ t₁
        (ne_of_mem_erase hw')) (by unfold injWeight at hw; convert hw)
  have hF := frontier_of_prod_ne_zero hN hinj (downClosed_strictBelow hN r) hprod
  have harr' : arriving N inj top r = F₁ := by
    rw [← harr]
    exact hg.arriving_lower inj (fun _ => ∅) (fun _ => ∅) t₁ (cutLower N r hc).root
  have hrD : r ∉ strictBelow N r := fun h => (mem_strictBelow.1 h).2 rfl
  refine ⟨harr' ▸ hF.good_arriving hinj hrD fun e he => target_mem_strictBelow_of_source hN he,
    fun x => ?_⟩
  rw [← harr', mem_lineages_arriving]
  constructor
  · rintro (hx | ⟨e, he, hx⟩)
    · exact ⟨r, .refl, hx⟩
    · obtain ⟨u, hu, hxu⟩ := hF.below e (target_mem_strictBelow_of_source hN he) x hx
      exact ⟨u, (Relation.ReflTransGen.single ⟨e, he, rfl⟩).trans hu, hxu⟩
  · rintro ⟨u, hu, hxu⟩
    by_cases hur : u = r
    · exact Or.inl (hur ▸ hxu)
    · obtain ⟨e, heD, hsD, hxe⟩ := (hF.mem x).2 ⟨u, mem_strictBelow.2 ⟨hu, hur⟩, hxu⟩
      have hs := hc.entry e (mem_strictBelow.1 heD).1 (mem_strictBelow.1 heD).2
      have hsr : N.graph.source e = r := by
        by_contra hne
        exact hsD (mem_strictBelow.2 ⟨hs, hne⟩)
      exact Or.inr ⟨e, hsr, hxe⟩

/-! ### The Markov property at an arc -/

variable {c : E}

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The arcs into `r` are `c` alone, indexed by `Unit`. -/
def unitArc (hcr : N.graph.target c = r) (huniq : ∀ g, N.graph.target g = r → g = c) :
    Unit ≃ {e // N.graph.target e = r} where
  toFun _ := ⟨c, hcr⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv e := Subtype.ext (huniq e.1 e.2).symm

variable (N r) in
/-- The law of the forest at the top of an arc `c` into the cut vertex `r`: the law of the forest
arriving at `r`, followed by the coalescent along `c`. -/
def arcLaw (hc : IsCut N r) (θ : MetricData E) (ρ : ℝ) (c : E) (inj : V → Finset (Finset X))
    (t : Finset (Finset X)) : ℝ :=
  ∑ F₁, rootDist (cutLower N r hc) (cutLowerMetric N r θ) ρ (lowerInj (cutVertices N r) inj) F₁ *
    kingmanTransition (θ.length c) F₁ t

/-- With the forest `t` at the top of `c` and nothing below `c`, the process is that of `cutUpper`
with `t` at the source of `c`. -/
theorem sum_rootDist_liftInj (hN : N.IsPhylogenetic) (hc : IsCut N r) (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) {θ : MetricData E} (h1 : θ.inheritance c = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (inj : V → Finset (Finset X)) (t : Finset (Finset X))
    (Φ : Finset (Finset X) → ℝ) :
    ∑ F, rootDist N θ ρ (liftInj N c inj t) F * Φ F =
      ∑ F, rootDist (cutUpper N r hc) (cutUpperMetric N r θ) ρ
        (upperInj (cutVertices N r) (cutSource N r hN (unitArc hcr huniq)) inj fun _ => t) F *
          Φ F := by
  have hg := isGlued_cut N r hN hc θ (unitArc hcr huniq)
  have hAF : ∀ F bot, allocationFactor N θ ρ F
    ((cutVertices N r) (.inr (cutLower N r hc).root)) bot =
      (fun F (b : Unit → Finset (Finset X)) => if b () = F then (1 : ℝ) else 0) F
        fun p => bot (cutArcs N r (unitArc hcr huniq) (.inr (.inl p))) :=
    fun F bot => allocationFactor_of_unique_arc hρ hcr huniq h1 F bot
  have h := isGlued_sum_mul_eq hg (ρ := ρ) (liftInj N c inj t)
    (AF := fun F b => if b () = F then (1 : ℝ) else 0) hAF (fun _ => 1) Φ
  simp only [one_mul] at h
  rw [sum_rootDist_mul, h]
  have hlow : lowerInj (cutVertices N r) (liftInj N c inj t) = atRoot (cutLower N r hc) ∅ := by
    funext w
    unfold lowerInj atRoot
    rw [cutVertices_inr]
    have hw : w.1 ∈ belowSet N c := mem_belowSet.2 (by rw [hcr]; exact w.2)
    rw [liftInj_of_mem hN hw]
    split_ifs <;> rfl
  rw [hlow, Finset.sum_eq_single ∅]
  · rw [rootDist_atRoot (cutLower_acyclic N r hN hc) (fun e h => e.2.2 (congrArg Subtype.val h)),
      ite_eq_left rfl, one_mul, sum_fun_unit, Finset.sum_eq_single ∅]
    · rw [ite_eq_left rfl, one_mul, sum_fun_unit, Finset.sum_eq_single ∅]
      · rw [Fintype.prod_unique, kingmanTransition_of_card_roots_le_one isForest_empty (by simp),
          ite_eq_left rfl, one_mul]
        refine sum_congr rfl fun F _ => ?_
        congr 2
        funext w
        have hw : w.1 ∉ belowSet N c := fun h => w.2 (by
          have := mem_belowSet.1 h
          rwa [hcr] at this)
        ext A
        simp only [upperInj, cutVertices_inl, liftInj, hw, ite_false, mem_union, mem_biUnion,
          mem_filter, mem_univ, true_and, notMem_empty, exists_const, and_false, or_false]
        by_cases hs : w.1 = N.graph.source c
        · have hw' : cutSource N r hN (unitArc hcr huniq) () = w := Subtype.ext hs.symm
          simp [hs, hw']
        · have hw' : cutSource N r hN (unitArc hcr huniq) () ≠ w := fun h' =>
            hs (congrArg Subtype.val h').symm
          simp [hs, hw']
      · intro t' _ ht'
        rw [Fintype.prod_unique, kingmanTransition_of_card_roots_le_one isForest_empty (by simp),
          ite_eq_right ht', zero_mul]
      · simp
    · intro b _ hb
      rw [ite_eq_right hb, zero_mul]
    · simp
  · intro F₁ _ hF₁
    rw [rootDist_atRoot (cutLower_acyclic N r hN hc) (fun e h => e.2.2 (congrArg Subtype.val h)),
      ite_eq_right hF₁, zero_mul]
  · simp

/-- **The Markov property at an arc** `c`, the only arc into the cut vertex `r`: the process is the
mixture, over the law of the forest `t` at the top of `c` (`arcLaw`), of the process with `t` at the
source of `c` and nothing below `c` (`NMSC.liftInj`), with a function `Ψ` of that forest carried
along. -/
theorem sum_mul_arc (hN : N.IsPhylogenetic) (hc : IsCut N r) (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) {θ : MetricData E} (h1 : θ.inheritance c = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (inj : V → Finset (Finset X)) (Ψ Φ : Finset (Finset X) → ℝ) :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      injWeight N θ ρ inj bot top * (Ψ (top c) * Φ (arriving N inj top N.root)) =
      ∑ t, arcLaw N r hc θ ρ c inj t * (Ψ t * ∑ F, rootDist N θ ρ (liftInj N c inj t) F * Φ F) := by
  have hg := isGlued_cut N r hN hc θ (unitArc hcr huniq)
  have hAF : ∀ F bot, allocationFactor N θ ρ F
    ((cutVertices N r) (.inr (cutLower N r hc).root)) bot =
      (fun F (b : Unit → Finset (Finset X)) => if b () = F then (1 : ℝ) else 0) F
        fun p => bot (cutArcs N r (unitArc hcr huniq) (.inr (.inl p))) :=
    fun F bot => allocationFactor_of_unique_arc hρ hcr huniq h1 F bot
  have h := isGlued_sum_mul_eq hg (ρ := ρ) inj (AF := fun F b => if b () = F then (1 : ℝ) else 0)
    hAF (fun tP => Ψ (tP ())) Φ
  refine h.trans ?_
  simp only [sum_rootDist_liftInj hN hc hcr huniq h1 hρ]
  unfold arcLaw
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun F₁ _ => ?_
  rw [sum_fun_unit, Finset.sum_eq_single F₁]
  · rw [ite_eq_left rfl, one_mul, sum_fun_unit, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [Fintype.prod_unique]
    have hl : θ.length ((unitArc hcr huniq) default).1 = θ.length c := rfl
    rw [hl]
    ring
  · intro b _ hb
    rw [ite_eq_right hb, zero_mul]
  · simp

/-- **The Markov property at an arc**, for the law at the root. -/
theorem rootDist_eq_sum_arc (hN : N.IsPhylogenetic) (hc : IsCut N r) (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) {θ : MetricData E} (h1 : θ.inheritance c = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (inj : V → Finset (Finset X)) (F : Finset (Finset X)) :
    rootDist N θ ρ inj F = ∑ t, arcLaw N r hc θ ρ c inj t * rootDist N θ ρ
      (liftInj N c inj t) F := by
  have h := sum_mul_arc hN hc hcr huniq h1 hρ inj (fun _ => 1) fun F' => if F' = F then 1 else 0
  simp only [one_mul] at h
  unfold rootDist
  rw [h]
  refine sum_congr rfl fun t _ => ?_
  congr 1
  rw [sum_rootDist_mul]

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The only arc into a vertex is a tree arc. -/
theorem isTreeArc_of_unique (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) : N.IsTreeArc c :=
  (N.graph.indegree_eq_one_iff _).2 ⟨c, fun f => ⟨fun h => huniq f (h.trans hcr), fun h => h ▸ rfl⟩⟩

/-- In the support of `arcLaw`, the forest at the top of `c` is a binary forest on the lineages
injected below `r`. -/
theorem good_of_arcLaw_ne_zero (hN : N.IsPhylogenetic) (hc : IsCut N r) {θ : MetricData E} {ρ : ℝ}
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {t : Finset (Finset X)}
    (h : arcLaw N r hc θ ρ c inj t ≠ 0) :
    IsGoodForest t ∧ ∀ x, x ∈ lineages t ↔ ∃ u, N.graph.Reaches r u ∧ x ∈ lineages (inj u) := by
  unfold arcLaw at h
  obtain ⟨F₁, -, hF⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨hg, hl⟩ := good_of_rootDist_cutLower_ne_zero hN hc hinj (left_ne_zero_of_mul hF)
  obtain ⟨hg', -, hl'⟩ := kingmanTransition_support_good hg (right_ne_zero_of_mul hF)
  exact ⟨hg', fun x => by rw [hl']; exact hl x⟩

/-- In the support of `arcLaw`, lifting the forest to the source of `c` gives valid injections. -/
theorem validInj_of_arcLaw_ne_zero (hN : N.IsPhylogenetic) (hc : IsCut N r)
    (hcr : N.graph.target c = r) {θ : MetricData E} {ρ : ℝ} {inj : V → Finset (Finset X)}
    (hinj : ValidInj inj) {t : Finset (Finset X)} (h : arcLaw N r hc θ ρ c inj t ≠ 0) :
    ValidInj (liftInj N c inj t) := by
  obtain ⟨hg, hl⟩ := good_of_arcLaw_ne_zero hN hc hinj h
  refine validInj_liftInj hinj hg fun x hx => ?_
  obtain ⟨u, hu, hxu⟩ := (hl x).1 hx
  exact ⟨u, mem_belowSet.2 (by rw [hcr]; exact hu), hxu⟩

/-- The law at the root is a probability distribution. -/
theorem sum_rootDist_eq_one (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {inj : V → Finset (Finset X)} (hinj : ValidInj inj) :
    ∑ F, rootDist N θ ρ inj F = 1 := by
  have h := sum_rootDist_mul N θ ρ inj fun _ => 1
  simp only [mul_one] at h
  rw [h]
  exact sum_sum_injWeight hN hθ hρ hinj

/-- The law of the forest arriving at a cut vertex is a probability distribution. -/
theorem sum_rootDist_cutLower (hN : N.IsPhylogenetic) (hc : IsCut N r) {θ : MetricData E}
    (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {inj : V → Finset (Finset X)}
    (hinj : ValidInj inj) :
    ∑ F₁, rootDist (cutLower N r hc) (cutLowerMetric N r θ) ρ
      (lowerInj (cutVertices N r) inj) F₁ = 1 := by
  have h := congrArg (fun f => ∑ F, f F) (funext (rootDist_eq_sum_cut hN hc θ ρ inj))
  simp only at h
  rw [sum_rootDist_eq_one hN hθ hρ hinj, sum_comm] at h
  rw [h]
  refine sum_congr rfl fun F₁ _ => ?_
  rw [← mul_sum]
  by_cases h0 : rootDist (cutLower N r hc) (cutLowerMetric N r θ) ρ
      (lowerInj (cutVertices N r) inj) F₁ = 0
  · rw [h0, zero_mul]
  · obtain ⟨hg, hl⟩ := good_of_rootDist_cutLower_ne_zero hN hc hinj h0
    have hv : ValidInj (cutInj N r inj F₁) := by
      refine ⟨fun w => ?_, fun u w huw => ?_⟩
      · unfold cutInj
        split_ifs
        · exact hg
        · exact isGoodForest_empty
        · exact hinj.good w
      · refine disjoint_left.2 fun x hxu hxw => ?_
        have key : ∀ a, x ∈ lineages (cutInj N r inj F₁ a) →
            (a = r ∧ ∃ u', N.graph.Reaches r u' ∧ x ∈ lineages (inj u')) ∨
              (¬ N.graph.Reaches r a ∧ x ∈ lineages (inj a)) := by
          intro a ha
          unfold cutInj at ha
          split_ifs at ha with h₁ h₂
          · exact Or.inl ⟨h₂, (hl x).1 ha⟩
          · simp at ha
          · exact Or.inr ⟨h₁, ha⟩
        rcases key u hxu with ⟨rfl, u', hu', hx'⟩ | ⟨hu, hx⟩ <;>
          rcases key w hxw with ⟨rfl, w', hw', hy'⟩ | ⟨hw, hy⟩
        · exact huw rfl
        · exact hw (hu'.trans (by
            by_contra hne
            exact disjoint_left.1 (hinj.disj u' w (fun h => hw (h ▸ hu'))) hx' hy))
        · exact hu (hw'.trans (by
            by_contra hne
            exact disjoint_left.1 (hinj.disj w' u (fun h => hu (h ▸ hw'))) hy' hx))
        · exact disjoint_left.1 (hinj.disj u w huw) hx hy
    rw [sum_rootDist_eq_one hN hθ hρ hv, mul_one]

/-- **One taxon below a cut vertex**: the forest arriving there is its single lineage. -/
theorem rootDist_cutLower_of_one (hN : N.IsPhylogenetic) (hc : IsCut N r) {θ : MetricData E}
    (hθ : N.IsMetric θ) {d : X} (hd : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = d)
    (F₁ : Finset (Finset X)) :
    rootDist (cutLower N r hc) (cutLowerMetric N r θ) 0
      (lowerInj (cutVertices N r) (taxaInj N univ)) F₁ = if F₁ = {{d}} then 1 else 0 := by
  have hsupp : ∀ F, rootDist (cutLower N r hc) (cutLowerMetric N r θ) 0
      (lowerInj (cutVertices N r) (taxaInj N univ)) F ≠ 0 → F = {{d}} := by
    intro F hF
    obtain ⟨hg, hl⟩ := good_of_rootDist_cutLower_ne_zero hN hc (validInj_taxaInj univ) hF
    have hlin : ∀ x, x ∈ lineages F ↔ x = d := fun x => by
      rw [hl x]
      constructor
      · rintro ⟨u, hu, hxu⟩
        obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
        exact (hd x).1 hu
      · intro hx
        exact ⟨N.leaf x, (hd x).2 hx, mem_lineages_taxaInj.2 ⟨mem_univ _, rfl⟩⟩
    ext A
    rw [mem_singleton]
    constructor
    · intro hA
      obtain ⟨x, hx⟩ := hg.1.1 A hA
      have hxd := (hlin x).1 (mem_lineages.2 ⟨A, hA, hx⟩)
      rw [hxd] at hx
      exact Subset.antisymm (fun y hy => mem_singleton.2 ((hlin y).1 (mem_lineages.2 ⟨A, hA, hy⟩)))
        (singleton_subset_iff.2 hx)
    · rintro rfl
      obtain ⟨A, hA, hdA⟩ := mem_lineages.1 ((hlin d).2 rfl)
      exact hg.singleton_mem hA hdA
  have hsum := sum_rootDist_cutLower hN hc hθ ⟨le_rfl, zero_le_one⟩ (validInj_taxaInj (N := N) univ)
  rw [Finset.sum_eq_single {{d}} (fun F _ hF => by_contra fun h => hF (hsupp F h))
    (by simp)] at hsum
  split_ifs with h
  · rw [h, hsum]
  · by_contra h'
    exact h (hsupp F₁ h')

/-! ### The number of lineages at the top of an arc -/

/-- **The concordance factors as a sum over the number `K` of lineages at the top of `c`**:
`CF(N) = ∑ₖ P(K = k) CF(N | K = k)`. -/
theorem cf_eq_sum_jointCF (N : RootedNetwork V E X) (θ : MetricData E) (c : E) (q : QuartetTree X) :
    cf N θ q = ∑ k ∈ range (Fintype.card (Finset X) + 1), jointCF N θ c k q := by
  have hk : ∀ top : E → Finset (Finset X), #(roots (top c)) ∈ range (Fintype.card (Finset X) + 1) :=
    fun top => mem_range.2 (Nat.lt_succ_of_le ((card_le_card (filter_subset _ _)).trans
      (card_le_univ _)))
  unfold jointCF
  calc cf N θ q = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        historyWeight N θ 0 bot top * ∑ G, (if Displays (unroot G) q then
          kingmanAbsorption (arrivingForest N top N.root) G else 0) := by
        unfold cf nmscCF geneTreeDist
        have e1 : ∀ G : Finset (Finset X), (if Displays (unroot G) q then
            ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
              historyWeight N θ 0 bot top * kingmanAbsorption (arrivingForest N top N.root) G
            else 0) = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
              (if Displays (unroot G) q then historyWeight N θ 0 bot top *
                kingmanAbsorption (arrivingForest N top N.root) G else 0) := fun G => by
          split_ifs <;> simp
        simp only [e1, mul_sum, mul_ite, mul_zero]
        rw [sum_comm]
        exact sum_congr rfl fun bot _ => sum_comm
    _ = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        ∑ k ∈ range (Fintype.card (Finset X) + 1), (if #(roots (top c)) = k then
          historyWeight N θ 0 bot top * ∑ G, (if Displays (unroot G) q then
            kingmanAbsorption (arrivingForest N top N.root) G else 0) else 0) := by
        refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
        rw [sum_ite_eq, ite_eq_left (hk top)]
    _ = ∑ bot : E → Finset (Finset X), ∑ k ∈ range (Fintype.card (Finset X) + 1),
        ∑ top : E → Finset (Finset X), (if #(roots (top c)) = k then
          historyWeight N θ 0 bot top * ∑ G, (if Displays (unroot G) q then
            kingmanAbsorption (arrivingForest N top N.root) G else 0) else 0) :=
        sum_congr rfl fun bot _ => sum_comm
    _ = _ := sum_comm

/-- `P(K = k) · CF(N | K = k)` for the number `K` of lineages at the top of the only arc `c` into a
cut vertex: the law of the forest at the top of `c`, and the process with that forest at the source
of `c`. -/
theorem jointCF_eq_sum_arc (hN : N.IsPhylogenetic) (hc : IsCut N r) (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) {θ : MetricData E} (h1 : θ.inheritance c = 1)
    (k : ℕ) (q : QuartetTree X) :
    jointCF N θ c k q = ∑ t, if #(roots t) = k then arcLaw N r hc θ 0 c (taxaInj N univ) t *
      ∑ G, (if Displays (unroot G) q then injDist N θ 0 (liftInj N c (taxaInj N univ) t) G else 0)
      else 0 := by
  have h := sum_mul_arc hN hc hcr huniq h1 le_rfl (taxaInj N univ)
    (fun t => if #(roots t) = k then 1 else 0)
    fun F => ∑ G, (if Displays (unroot G) q then kingmanAbsorption F G else 0)
  unfold jointCF
  simp only [historyWeight_eq_injWeight hN, arrivingForest_eq]
  have hl : ∀ bot top : E → Finset (Finset X),
      (if #(roots (top c)) = k then injWeight N θ 0 (taxaInj N univ) bot top *
        ∑ G, (if Displays (unroot G) q then
          kingmanAbsorption (arriving N (taxaInj N univ) top N.root) G else 0) else 0) =
      injWeight N θ 0 (taxaInj N univ) bot top * ((if #(roots (top c)) = k then 1 else 0) *
        ∑ G, (if Displays (unroot G) q then
          kingmanAbsorption (arriving N (taxaInj N univ) top N.root) G else 0)) := by
    intro bot top
    split_ifs <;> ring
  simp only [hl]
  rw [h]
  refine sum_congr rfl fun t _ => ?_
  split_ifs
  · rw [one_mul]
    congr 1
    simp only [mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    refine sum_congr rfl fun G _ => ?_
    split_ifs
    · rw [injDist_eq_sum_rootDist]
    · rw [sum_const_zero]
  · rw [zero_mul, mul_zero]

/-- `P(K = k)` for the number `K` of lineages at the top of the only arc `c` into a cut vertex. -/
theorem probLineages_eq_sum_arc (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ)
    (hc : IsCut N r) (hcr : N.graph.target c = r) (huniq : ∀ g, N.graph.target g = r → g = c)
    (k : ℕ) :
    probLineages N θ c k =
      ∑ t, if #(roots t) = k then arcLaw N r hc θ 0 c (taxaInj N univ) t else 0 := by
  have h1 : θ.inheritance c = 1 := hθ.2.2.1 c (isTreeArc_of_unique hcr huniq)
  have h := sum_mul_arc hN hc hcr huniq h1 le_rfl (taxaInj N univ)
    (fun t => if #(roots t) = k then 1 else 0) fun _ => 1
  unfold probLineages
  simp only [historyWeight_eq_injWeight hN]
  have hl : ∀ bot top : E → Finset (Finset X),
      (if #(roots (top c)) = k then injWeight N θ 0 (taxaInj N univ) bot top else 0) =
      injWeight N θ 0 (taxaInj N univ) bot top * ((if #(roots (top c)) = k then 1 else 0) * 1) := by
    intro bot top
    split_ifs <;> ring
  simp only [hl]
  rw [h]
  refine sum_congr rfl fun t _ => ?_
  by_cases ht : arcLaw N r hc θ 0 c (taxaInj N univ) t = 0
  · simp [ht]
  · have hv := validInj_of_arcLaw_ne_zero hN hc hcr (validInj_taxaInj univ) ht
    simp only [mul_one]
    rw [sum_rootDist_eq_one hN hθ ⟨le_rfl, zero_le_one⟩ hv]
    split_ifs <;> ring

end Cut

/-! ### Four taxa -/

section FourTaxa

variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

omit [Fintype V] [Fintype E] in
theorem taxa_eq_univ (hX : Fintype.card X = 4) (q : QuartetTree X) : q.taxa = univ :=
  eq_univ_of_card _ (by rw [q.card_taxa, hX])

omit [Fintype V] [Fintype E] in
/-- On four taxa, a rooted tree displays the quartet tree `q` when a cherry of `q` is a cluster. -/
theorem displays_unroot_iff_of_four (hX : Fintype.card X = 4) (q : QuartetTree X)
    (G : Finset (Finset X)) : Displays (unroot G) q ↔ ∃ B ∈ q.val, B ∈ G := by
  rw [displays_unroot_iff, taxa_eq_univ hX]
  refine exists_congr fun B => and_congr_right fun hB => ?_
  simp only [traceForest, inter_univ, mem_image, mem_filter]
  constructor
  · rintro ⟨A, ⟨hA, -⟩, rfl⟩
    exact hA
  · intro h
    exact ⟨B, ⟨h, card_pos.1 (by rw [q.card_of_mem hB]; omega)⟩, rfl⟩

/-- On four taxa, the probability that the gene tree displays `q` is the mass of `q`. -/
theorem sum_displays_injDist (hX : Fintype.card X = 4) (inj : V → Finset (Finset X))
    (q : QuartetTree X) :
    ∑ G, (if Displays (unroot G) q then injDist N θ ρ inj G else 0) = cherryMass N θ ρ inj q := by
  unfold cherryMass
  simp only [displays_unroot_iff_of_four hX]

/-- On four taxa, the concordance factor of `q` is the mass of `q` for the lineages of all taxa. -/
theorem cf_eq_cherryMass (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hX : Fintype.card X = 4)
    (q : QuartetTree X) : cf N θ q = cherryMass N θ 0 (taxaInj N univ) q := by
  rw [cf, nmscCF_eq_cherryMass hN hθ ⟨le_rfl, zero_le_one⟩, taxa_eq_univ hX]

/-- **Three lineages in a forest at a vertex, the fourth taxon elsewhere**: a cluster of two
lineages of the forest decides the quartet tree; without one, the three quartet trees are equally
likely, by exchangeability of the three lineages. -/
theorem cherryMass_eq_quartetValue (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hX : Fintype.card X = 4) {inj : V → Finset (Finset X)}
    (hinj : ValidInj inj) {w : V} {d : X} (hlin : lineages (inj w) = univ.erase d)
    (hother : ∀ u, u ≠ w → ∀ A ∈ inj u, A = {d}) (hd : ∃ u, d ∈ lineages (inj u))
    (q : QuartetTree X) : cherryMass N θ ρ inj q = quartetValue q (inj w) := by
  have hqt := taxa_eq_univ hX q
  unfold quartetValue
  by_cases h : ∃ C ∈ inj w, #C = 2
  · rw [ite_eq_left h]
    have hval : ∀ C ∈ inj w, #C = 2 → cherryMass N θ ρ inj q = if C ∈ q.val then 1 else 0 :=
      fun C hC hC2 => cherryMass_of_mem hN hθ hρ hinj hC hC2 (by rw [hqt]; exact subset_univ _)
    by_cases h2 : ∃ C ∈ inj w, C ∈ q.val
    · obtain ⟨C, hC, hCs⟩ := h2
      rw [hval C hC (q.card_of_mem hCs), ite_eq_left hCs, ite_eq_left ⟨C, hC, hCs⟩]
    · obtain ⟨C, hC, hC2⟩ := h
      rw [hval C hC hC2, ite_eq_right fun h' => h2 ⟨C, hC, h'⟩, ite_eq_right h2]
  · rw [ite_eq_right h]
    have hsing := (hinj.good w).eq_singletons h
    rw [hlin] at hsing
    refine cherryMass_eq_third hN hθ hρ hinj (Y := univ) (by rw [card_univ, hX]) (fun x => ?_)
      (mem_univ d) (fun x _ y _ hx hy => ?_) (mem_treesOn.2 hqt)
    · simp only [mem_univ, iff_true]
      by_cases hxd : x = d
      · subst hxd
        exact hd
      · exact ⟨w, by rw [hlin]; exact mem_erase.2 ⟨hxd, mem_univ _⟩⟩
    · funext u
      unfold relabelInj
      by_cases huw : u = w
      · subst huw
        rw [hsing]
        exact relabelFamily_swap_singletons (mem_erase.2 ⟨hx, mem_univ _⟩)
          (mem_erase.2 ⟨hy, mem_univ _⟩)
      · refine relabelFamily_eq_self fun A hA => ?_
        rw [hother u huw A hA, map_singleton]
        simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hx) (Ne.symm hy)]

omit [Fintype V] [Fintype X] in
/-- No taxon is at the source of an arc. -/
theorem leaf_ne_source (hN : N.IsPhylogenetic) (x : X) (e : E) : N.leaf x ≠ N.graph.source e := by
  intro h
  have h0 := (hN.leaves (N.leaf x)).2 ⟨x, rfl⟩
  exact (N.graph.outdegree_eq_zero_iff _).1 h0 e h.symm

/-- **The forest at the top of an arc into a cut vertex below which lie three of the four taxa**
decides the mass of a quartet tree by `quartetValue`. -/
theorem cherryMass_liftInj (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hX : Fintype.card X = 4) {r : V} (hc : IsCut N r) {c : E} (hcr : N.graph.target c = r)
    {d : X} (hd : ¬ N.graph.Reaches r (N.leaf d))
    (hbelow : ∀ x, x ≠ d → N.graph.Reaches r (N.leaf x)) {t : Finset (Finset X)}
    (ht : arcLaw N r hc θ ρ c (taxaInj N univ) t ≠ 0) (q : QuartetTree X) :
    cherryMass N θ ρ (liftInj N c (taxaInj N univ) t) q = quartetValue q t := by
  have hv := validInj_of_arcLaw_ne_zero hN hc hcr (validInj_taxaInj univ) ht
  obtain ⟨-, hl⟩ := good_of_arcLaw_ne_zero hN hc (validInj_taxaInj univ) ht
  have hsrc : N.graph.source c ∉ belowSet N c := source_notMem_belowSet hN c
  have hw : liftInj N c (taxaInj N univ) t (N.graph.source c) = t := by
    have h0 : taxaInj N univ (N.graph.source c) = ∅ := by
      refine eq_empty_of_forall_notMem fun A hA => ?_
      obtain ⟨x, hx, -⟩ := mem_image.1 hA
      exact leaf_ne_source hN x c (mem_filter.1 hx).2.2
    simp [liftInj, hsrc, h0]
  have hbz : ∀ u, u ∈ belowSet N c ↔ N.graph.Reaches r u := fun u => by
    rw [mem_belowSet, hcr]
  rw [cherryMass_eq_quartetValue hN hθ hρ hX hv (w := N.graph.source c) (d := d), hw]
  · rw [hw]
    ext x
    rw [mem_erase, hl x]
    simp only [mem_univ, and_true]
    constructor
    · rintro ⟨u, hu, hxu⟩
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
      exact fun h => hd (h ▸ hu)
    · intro hxd
      exact ⟨N.leaf x, hbelow x hxd, mem_lineages_taxaInj.2 ⟨mem_univ _, rfl⟩⟩
  · intro u hu A hA
    simp only [liftInj, hu, ite_false, union_empty] at hA
    split_ifs at hA with hub
    · exact absurd hA (notMem_empty _)
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hA
      have hxu := (mem_filter.1 hx).2.2
      by_contra hxd
      exact hub ((hbz u).2 (hxu ▸ hbelow x fun h => hxd (h ▸ rfl)))
  · refine ⟨N.leaf d, ?_⟩
    have hnb : N.leaf d ∉ belowSet N c := fun h => hd ((hbz _).1 h)
    have hns : N.leaf d ≠ N.graph.source c := leaf_ne_source hN d c
    simp only [liftInj, hnb, hns, ite_false, union_empty]
    exact mem_lineages_taxaInj.2 ⟨mem_univ _, rfl⟩

/-- **`P(K = k) · CF(N | K = k)` when three of the four taxa are below the cut vertex**: by the law
of the forest at the top of `c` and `quartetValue`. -/
theorem jointCF_eq_sum_quartetValue (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hX : Fintype.card X = 4) {r : V} (hc : IsCut N r) {c : E} (hcr : N.graph.target c = r)
    (huniq : ∀ g, N.graph.target g = r → g = c) {d : X} (hd : ¬ N.graph.Reaches r (N.leaf d))
    (hbelow : ∀ x, x ≠ d → N.graph.Reaches r (N.leaf x)) (k : ℕ) (q : QuartetTree X) :
    jointCF N θ c k q = ∑ t, if #(roots t) = k then
      arcLaw N r hc θ 0 c (taxaInj N univ) t * quartetValue q t else 0 := by
  have h1 : θ.inheritance c = 1 := hθ.2.2.1 c (isTreeArc_of_unique hcr huniq)
  rw [jointCF_eq_sum_arc hN hc hcr huniq h1 k q]
  refine sum_congr rfl fun t _ => ?_
  split_ifs
  · by_cases ht : arcLaw N r hc θ 0 c (taxaInj N univ) t = 0
    · simp [ht]
    · rw [sum_displays_injDist hX,
        cherryMass_liftInj hN hθ ⟨le_rfl, zero_le_one⟩ hX hc hcr hd hbelow ht]
  · rfl

variable (N) in
/-- The law at the root of the part above a cut vertex `r` with the only arc `p` into `r`, when the
forest `t` is at the top of `p`. -/
def upperLaw (hN : N.IsPhylogenetic) {r : V} (hc : IsCut N r) {p : E} (hpr : N.graph.target p = r)
    (huniq : ∀ g, N.graph.target g = r → g = p) (θ : MetricData E) (t F : Finset (Finset X)) : ℝ :=
  rootDist (cutUpper N r hc) (cutUpperMetric N r θ) 0
    (upperInj (cutVertices N r) (cutSource N r hN (unitArc hpr huniq))
      (taxaInj N univ) fun _ => t) F

/-- **One taxon `d` below a cut vertex `r` with the only arc `p` into it**: the concordance factors
are those of the part above `r`, with the single lineage of `d` at the top of `p` after the
coalescent along `p`. -/
theorem cf_eq_of_one_below (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hX : Fintype.card X = 4)
    {r : V} (hc : IsCut N r) {p : E} (hpr : N.graph.target p = r)
    (huniq : ∀ g, N.graph.target g = r → g = p) {d : X}
    (hd : ∀ x, N.graph.Reaches r (N.leaf x) ↔ x = d) (q : QuartetTree X) :
    cf N θ q = ∑ H, if ∃ B ∈ q.val, B ∈ H then ∑ F, (∑ t, kingmanTransition (θ.length p) {{d}} t *
      upperLaw N hN hc hpr huniq θ t F) * kingmanAbsorption F H else 0 := by
  have h1 : θ.inheritance p = 1 := hθ.2.2.1 p (isTreeArc_of_unique hpr huniq)
  rw [cf_eq_cherryMass hN hθ hX]
  unfold cherryMass
  refine sum_congr rfl fun H _ => ?_
  split_ifs
  · rw [injDist_eq_sum_rootDist]
    refine sum_congr rfl fun F _ => ?_
    congr 1
    rw [rootDist_eq_sum_arc hN hc hpr huniq h1 le_rfl]
    refine sum_congr rfl fun t _ => ?_
    have hlaw : arcLaw N r hc θ 0 p (taxaInj N univ) t =
      kingmanTransition (θ.length p) {{d}} t := by
      unfold arcLaw
      simp only [rootDist_cutLower_of_one hN hc hθ hd, ite_mul, one_mul, zero_mul, sum_ite_eq',
        mem_univ, ite_true]
    rw [hlaw]
    congr 1
    have := sum_rootDist_liftInj hN hc hpr huniq h1 le_rfl (taxaInj N univ) t
      fun F' => if F' = F then 1 else 0
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at this
    exact this
  · rfl

end FourTaxa

/-! ### Deleting an arc of inheritance zero -/

section Deletion

variable {N : RootedNetwork V E X} {h : E}

omit [Fintype V] [Fintype E] [Fintype X] in
/-- `Finset.mem_univ`, for an instance given by unification. -/
theorem mem_univ_of' {α : Type*} (i : Fintype α) (x : α) : x ∈ @Finset.univ α i :=
  @Finset.mem_univ α i x

/-- The forests of the network without `h`, extended by the empty forest at `h`. -/
def deleteExt (h : E) (b : {e // e ≠ h} → Finset (Finset X)) : E → Finset (Finset X) :=
  fun e => if he : e = h then ∅ else b ⟨e, he⟩

omit [Fintype V] [Fintype E] [Fintype X] in
theorem deleteExt_self (b : {e // e ≠ h} → Finset (Finset X)) : deleteExt h b h = ∅ :=
  dite_eq_left rfl

omit [Fintype V] [Fintype E] [Fintype X] in
theorem deleteExt_val (b : {e // e ≠ h} → Finset (Finset X)) (e : {e // e ≠ h}) :
    deleteExt h b e.1 = b e :=
  dite_eq_right e.2

omit [Fintype V] [Fintype E] [Fintype X] in
theorem deleteExt_injective : Function.Injective (deleteExt (X := X) h) := fun b b' hb =>
  funext fun e => by rw [← deleteExt_val b e, hb, deleteExt_val]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem eq_deleteExt {b : E → Finset (Finset X)} (hb : b h = ∅) :
    b = deleteExt h fun e => b e.1 := by
  funext e
  by_cases he : e = h
  · rw [he, hb, deleteExt_self]
  · exact (deleteExt_val (fun e => b e.1) ⟨e, he⟩).symm

omit [Fintype V] in
/-- The forest arriving at a vertex is the same without `h`. -/
theorem arrivingForest_deleteExt (t : {e // e ≠ h} → Finset (Finset X)) (v : V) :
    arrivingForest N (deleteExt h t) v = arrivingForest (deleteArc N h) t v := by
  unfold arrivingForest
  congr 1
  ext A
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hA⟩
    by_cases heh : e = h
    · rw [heh, deleteExt_self] at hA
      exact absurd hA (notMem_empty _)
    · exact ⟨⟨e, heh⟩, he, by rwa [← deleteExt_val t ⟨e, heh⟩]⟩
  · rintro ⟨e, he, hA⟩
    exact ⟨e.1, he, by rwa [deleteExt_val]⟩

omit [Fintype V] in
/-- At inheritance correlation `0`, the allocation at a vertex is the same without an arc of
inheritance `0`: no lineage takes it. -/
theorem allocationFactor_deleteExt {θ : MetricData E} (h0 : θ.inheritance h = 0)
    {θ' : MetricData {e // e ≠ h}} (hinh : ∀ e, θ'.inheritance e = θ.inheritance e.1)
    (F : Finset (Finset X)) (v : V) (b : {e // e ≠ h} → Finset (Finset X)) :
    allocationFactor N θ 0 F v (deleteExt h b) = allocationFactor (deleteArc N h) θ' 0 F v b := by
  unfold allocationFactor
  symm
  let φ : ({A // A ∈ roots F} → {e : {e // e ≠ h} // (deleteArc N h).graph.target e = v}) →
      ({A // A ∈ roots F} → {e // N.graph.target e = v}) := fun a r => ⟨(a r).1.1, (a r).2⟩
  have hφ : Function.Injective φ := fun a a' haa => funext fun r => by
    have h' : (φ a r).1 = (φ a' r).1 := by rw [haa]
    exact Subtype.ext (Subtype.ext h')
  refine Finset.sum_of_injOn φ hφ.injOn (fun _ _ => mem_coe.2 (mem_univ _)) (fun a _ ha => ?_)
    fun a _ => ?_
  · -- an assignment through `h` has weight zero
    have hex : ∃ r, (a r).1 = h := by
      by_contra hne
      push Not at hne
      exact ha ⟨fun r => ⟨⟨(a r).1, hne r⟩, (a r).2⟩, mem_coe.2 (mem_univ _), rfl⟩
    obtain ⟨r, hr⟩ := hex
    rw [allocationWeight_rho_zero]
    split_ifs
    · exact prod_eq_zero (mem_univ r) (by rw [hr, h0])
    · rfl
  · simp only [allocationWeight_rho_zero]
    have hw : ∏ r, θ'.inheritance (a r).1 = ∏ r, θ.inheritance (φ a r).1 :=
      prod_congr rfl fun r _ => hinh _
    refine if_congr ?_ hw rfl
    constructor
    · intro hb e
      by_cases heh : e.1 = h
      · rw [heh, deleteExt_self]
        refine (eq_empty_of_forall_notMem fun B hB => ?_).symm
        obtain ⟨-, C, hC, -⟩ := mem_forestBelow.1 hB
        obtain ⟨r, hr, -⟩ := mem_image.1 hC
        have := congrArg Subtype.val (mem_filter.1 hr).2
        exact (a r).1.2 (this.trans heh)
      · have := hb ⟨⟨e.1, heh⟩, e.2⟩
        rw [deleteExt_val b ⟨e.1, heh⟩, this]
        congr 2
        ext r
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro hr
          exact Subtype.ext (by simp [φ, hr])
        · intro hr
          have h' : (φ a r).1 = e.1 := by rw [hr]
          exact Subtype.ext (Subtype.ext h')
    · intro hb e
      have := hb ⟨e.1.1, e.2⟩
      rw [deleteExt_val] at this
      rw [this]
      congr 2
      ext r
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hr
        have h' : (φ a r).1 = e.1.1 := by rw [hr]
        exact Subtype.ext (Subtype.ext h')
      · intro hr
        exact Subtype.ext (by simp [φ, hr])

/-- A history of nonzero weight carries nothing on an arc of inheritance `0`, at correlation `0`. -/
theorem eq_empty_of_historyWeight_ne_zero_of_inheritance_eq_zero (hN : N.IsPhylogenetic)
    {θ : MetricData E} (h0 : θ.inheritance h = 0) {bot top : E → Finset (Finset X)}
    (hw : historyWeight N θ 0 bot top ≠ 0) : bot h = ∅ ∧ top h = ∅ := by
  unfold historyWeight at hw
  have hv : N.graph.target h ∈ univ.erase N.root := mem_erase.2 ⟨target_ne_root hN h, mem_univ _⟩
  have ha := prod_ne_zero_iff.1 (left_ne_zero_of_mul hw) _ hv
  have hk := prod_ne_zero_iff.1 (right_ne_zero_of_mul hw) h (mem_univ _)
  have hb : bot h = ∅ := by
    unfold allocationFactor at ha
    obtain ⟨a, -, ha'⟩ := exists_ne_zero_of_sum_ne_zero ha
    have hP := ne_zero_of_ite_ne_zero' ha'
    have hW := ha'
    rw [ite_eq_left hP] at hW
    simp only [allocationWeight_rho_zero] at hW
    rw [hP ⟨h, rfl⟩]
    refine eq_empty_of_forall_notMem fun B hB => ?_
    obtain ⟨-, C, hC, -⟩ := mem_forestBelow.1 hB
    obtain ⟨r, hr, -⟩ := mem_image.1 hC
    have har : (a r).1 = h := congrArg Subtype.val (mem_filter.1 hr).2
    exact prod_ne_zero_iff.1 hW r (mem_univ _) (by rw [har, h0])
  refine ⟨hb, ?_⟩
  rw [hb, kingmanTransition_of_card_roots_le_one isForest_empty (by simp)] at hk
  exact (ne_zero_of_ite_ne_zero' hk)

/-- **Deleting an arc of inheritance `0`** does not change the gene tree distribution, at
correlation `0`: no lineage takes the arc. -/
theorem geneTreeDist_deleteArc (hN : N.IsPhylogenetic) {θ : MetricData E} (h0 : θ.inheritance h = 0)
    {θ' : MetricData {e // e ≠ h}} (hlen : ∀ e, θ'.length e = θ.length e.1)
    (hinh : ∀ e, θ'.inheritance e = θ.inheritance e.1) (G : Finset (Finset X)) :
    geneTreeDist (deleteArc N h) θ' 0 G = geneTreeDist N θ 0 G := by
  have hhw : ∀ b t : {e // e ≠ h} → Finset (Finset X),
      historyWeight N θ 0 (deleteExt h b) (deleteExt h t) =
        historyWeight (deleteArc N h) θ' 0 b t := by
    intro b t
    unfold historyWeight
    congr 1
    · refine prod_congr rfl fun v _ => ?_
      rw [arrivingForest_deleteExt t v]
      exact allocationFactor_deleteExt h0 hinh _ v b
    · symm
      refine Fintype.prod_of_injective Subtype.val Subtype.val_injective _ _ (fun e he => ?_)
        fun e => ?_
      · have heh : e = h := by
          by_contra hne
          exact he ⟨⟨e, hne⟩, rfl⟩
        rw [heh, deleteExt_self, deleteExt_self,
          kingmanTransition_of_card_roots_le_one isForest_empty (by simp), ite_eq_left rfl]
      · rw [deleteExt_val, deleteExt_val, hlen]
  unfold geneTreeDist
  refine Finset.sum_of_injOn (deleteExt h) deleteExt_injective.injOn
    (fun _ _ => mem_coe.2 (mem_univ _)) (fun bot _ hbot => ?_) fun b _ => ?_
  · refine sum_eq_zero fun top _ => ?_
    by_contra hne
    have hw := left_ne_zero_of_mul hne
    exact hbot ⟨_, mem_coe.2 (mem_univ_of' _ _),
      (eq_deleteExt (eq_empty_of_historyWeight_ne_zero_of_inheritance_eq_zero hN h0 hw).1).symm⟩
  · refine Finset.sum_of_injOn (deleteExt h) deleteExt_injective.injOn
      (fun _ _ => mem_coe.2 (mem_univ _)) (fun top _ htop => ?_) fun t _ => ?_
    · by_contra hne
      have hw := left_ne_zero_of_mul hne
      exact htop ⟨_, mem_coe.2 (mem_univ_of' _ _),
        (eq_deleteExt (eq_empty_of_historyWeight_ne_zero_of_inheritance_eq_zero hN h0 hw).2).symm⟩
    · rw [← hhw b t, arrivingForest_deleteExt]
      rfl

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The arcs into a vertex of indegree two are its two hybrid arcs. -/
theorem mem_pair_of_target_of_indegree_eq_two {v : V} (h2 : N.graph.indegree v = 2) {h₁ h₂ : E}
    (hne : h₁ ≠ h₂) (hh₁ : N.graph.target h₁ = v) (hh₂ : N.graph.target h₂ = v) (f : E)
    (hf : N.graph.target f = v) : f = h₁ ∨ f = h₂ := by
  obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 h2
  have m : ∀ g, N.graph.target g = v → g = x ∨ g = y := fun g hg => by
    have : g ∈ {e | N.graph.target e = v} := hg
    rw [hs] at this
    simpa using this
  rcases m h₁ hh₁ with r1 | r1 <;> rcases m h₂ hh₂ with r2 | r2 <;> rcases m f hf with r3 | r3 <;>
    subst_vars <;> simp_all

omit [Fintype V] [Fintype X] in
/-- The inheritance probabilities of the two hybrid arcs of a vertex sum to one. -/
theorem inheritance_add_eq_one {θ : MetricData E} (hθ : N.IsMetric θ) {v : V}
    (h2 : N.graph.indegree v = 2) {h₁ h₂ : E} (hne : h₁ ≠ h₂) (hh₁ : N.graph.target h₁ = v)
    (hh₂ : N.graph.target h₂ = v) : θ.inheritance h₁ + θ.inheritance h₂ = 1 := by
  have h := hθ.2.2.2.2 v (by omega)
  rw [← sum_filter] at h
  have hs : univ.filter (fun e => N.graph.target e = v) = {h₁, h₂} := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact ⟨mem_pair_of_target_of_indegree_eq_two h2 hne hh₁ hh₂
      f, by rintro (rfl | rfl) <;> assumption⟩
  rw [hs, sum_pair hne] at h
  exact h

/-- **`Q₁⊕`**: the network without `h₂` has the concordance factors of the network in which `h₁`
has inheritance `1` and `h₂` inheritance `0`, when `h₁` and `h₂` are the arcs into their target. -/
theorem cf_deleteArc (hN : N.IsPhylogenetic) (θ : MetricData E) {h₁ h₂ : E}
    (ht : N.graph.target h₁ = N.graph.target h₂)
    (hpar : ∀ f, N.graph.target f = N.graph.target h₂ → f = h₁ ∨ f = h₂) (hne : h₁ ≠ h₂)
    (q : QuartetTree X) :
    cf (deleteArc N h₂) (deleteArcMetric N h₂ θ) q = nmscCF N (θ.withPair h₁ h₂ 1) 0 q := by
  unfold cf nmscCF
  refine sum_congr rfl fun G _ => ?_
  congr 1
  refine geneTreeDist_deleteArc hN (withPair_inheritance_right hne 1 |>.trans (sub_self 1))
    (fun _ => rfl) (fun e => ?_) G
  simp only [deleteArcMetric, RootedNetwork.MetricData.withPair]
  by_cases he : N.graph.target e.1 = N.graph.target h₂
  · rcases hpar e.1 he with h | h
    · simp [h, ht]
    · exact absurd h e.2
  · have h1 : e.1 ≠ h₁ := fun h => he (h ▸ ht)
    simp [he, h1, e.2]

/-- **The mixture over the hybrid edge of a single lineage** (Lemma 10's argument): if at most one
taxon is below the hybrid node `v` with hybrid edges `h₁, h₂`, then
`CF(N) = γ CF(N₁) + (1 - γ) CF(N₂)`, `N₁` and `N₂` the networks without `h₂` and without `h₁`. -/
theorem cf_eq_mixture (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) {h₁ h₂ : E}
    (hne : h₁ ≠ h₂) (ht : N.graph.target h₁ = N.graph.target h₂)
    (hpar : ∀ f, N.graph.target f = N.graph.target h₂ → f = h₁ ∨ f = h₂)
    (hsum : θ.inheritance h₁ + θ.inheritance h₂ = 1)
    (hone : ∀ x y, N.graph.Reaches (N.graph.target h₁) (N.leaf x) →
      N.graph.Reaches (N.graph.target h₁) (N.leaf y) → x = y) (q : QuartetTree X) :
    cf N θ q = θ.inheritance h₁ * cf (deleteArc N h₂) (deleteArcMetric N h₂ θ) q +
      (1 - θ.inheritance h₁) * cf (deleteArc N h₁) (deleteArcMetric N h₁ θ) q := by
  have hpar₁ : ∀ f, N.graph.target f = N.graph.target h₁ → f = h₂ ∨ f = h₁ := fun f hf =>
    (hpar f (hf.trans ht)).symm
  rw [cf_deleteArc hN θ ht hpar hne, cf_deleteArc hN θ ht.symm hpar₁ hne.symm]
  have hθ' : θ.withPair h₁ h₂ (θ.inheritance h₁) = θ :=
    withPair_eq_self rfl fun _ => by linarith
  have hswap : θ.withPair h₂ h₁ 1 = θ.withPair h₁ h₂ 0 := by
    simp only [RootedNetwork.MetricData.withPair, RootedNetwork.MetricData.mk.injEq, true_and]
    funext f
    by_cases h2 : f = h₂
    · simp [h2, hne.symm]
    · by_cases h1 : f = h₁
      · simp [h1, hne]
      · simp [h1, h2]
  rw [hswap]
  by_cases hx : ∃ a, N.graph.Reaches (N.graph.target h₁) (N.leaf a)
  · obtain ⟨a, ha⟩ := hx
    have h := nmscCF_withPair (D := ∅) hN hθ.isNormalized le_rfl (fun _ hf => absurd hf (by simp))
      hne ht.symm (fun f hf _ => (hpar f (hf.trans ht)).imp id id) q a
      (fun x _ hxa hr => hxa (hone x a (reachesOff_empty_iff.1 hr) ha)) (θ.inheritance h₁)
    rw [hθ'] at h
    exact h
  · push Not at hx
    have : Nonempty X := ⟨(card_pos.1 (by rw [q.card_taxa]; omega) : q.taxa.Nonempty).choose⟩
    have h := nmscCF_withPair (D := ∅) hN hθ.isNormalized le_rfl (fun _ hf => absurd hf (by simp))
      hne ht.symm (fun f hf _ => (hpar f (hf.trans ht)).imp id id) q (Classical.arbitrary X)
      (fun x _ _ hr => hx x (reachesOff_empty_iff.1 hr)) (θ.inheritance h₁)
    rw [hθ'] at h
    exact h

end Deletion

end Banos2019

