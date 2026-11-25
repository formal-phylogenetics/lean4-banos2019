module

public import Banos2019.Quartet.Defs
public import Phylogenetics.NMSC.Glue
public import Phylogenetics.NMSC.InducedAbove

/-!
# Conditioning on the lineages at a vertex (Baños 2019, Section 5)

The proofs of Lemmas 7–11 condition on the number of lineages at a node of a quartet network. This
module gives the network multispecies coalescent the corresponding decomposition.

A vertex `r` other than the root is a *cut vertex* (`IsCut`) when the vertices below it are entered
only at `r`. The network is then glued (`NMSC.IsGlued`) from its part `cutUpper` not below `r` and its
part `cutLower` below `r`, rooted at `r`, along the arcs into `r` (`isGlued_cut`). So:

* `rootDist_eq_sum_cut`, `cherryMass_eq_sum_cut`: the *Markov property at `r`*. The process is the
  mixture, over the law of the forest `F` arriving at `r` (the law at the root of `cutLower`), of the
  process in which `F` is injected at `r` and nothing below `r` (`cutInj`).
* `rootDist_atRoot`: a network in which only the root receives a forest keeps it there.

The law of the forest arriving at `r` depends only on `cutLower`, so two networks with isomorphic
parts below cut vertices have the same law there (`NMSC.rootDist_congr`).
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

/-- **Only the root receives a forest**: in a finite acyclic network whose arcs do not enter the root,
a history of nonzero weight carries the empty forest on every arc. -/
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
            if h' : N.graph.target e = r then .inr (.inl (ι.symm ⟨e, h'⟩)) else .inr (.inr ⟨e, h, h'⟩)
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
forest `F` arriving at the cut vertex `r` (the law at the root of `cutLower`), of the law at the root
when `F` is injected at `r` and nothing else below `r`. -/
theorem rootDist_eq_sum_cut (hN : N.IsPhylogenetic) (hc : IsCut N r) (θ : MetricData E) (ρ : ℝ)
    (inj : V → Finset (Finset X)) (F : Finset (Finset X)) :
    rootDist N θ ρ inj F =
      ∑ F₁, rootDist (cutLower N r hc) (cutLowerMetric N r θ) ρ (lowerInj (cutVertices N r) inj) F₁ *
        rootDist N θ ρ (cutInj N r inj F₁) F := by
  let ι : {e // N.graph.target e = r} ≃ {e // N.graph.target e = r} := Equiv.refl _
  have hg := isGlued_cut N r hN hc θ ι
  let AF : Finset (Finset X) → ({e // N.graph.target e = r} → Finset (Finset X)) → ℝ :=
    fun F b => allocationFactor N θ ρ F r fun e => if h : N.graph.target e = r then b ⟨e, h⟩ else ∅
  have hAF : ∀ F bot, allocationFactor N θ ρ F ((cutVertices N r) (.inr (cutLower N r hc).root)) bot =
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
      ∑ F₁, rootDist (cutLower N r hc) (cutLowerMetric N r θ) ρ (lowerInj (cutVertices N r) inj) F₁ *
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
    (h : rootDist (cutLower N r hc) (cutLowerMetric N r θ) ρ (lowerInj (cutVertices N r) inj) F₁ ≠ 0) :
    IsGoodForest F₁ ∧ ∀ x, x ∈ lineages F₁ ↔ ∃ u, N.graph.Reaches r u ∧ x ∈ lineages (inj u) := by
  unfold rootDist at h
  obtain ⟨b₁, -, hb⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨t₁, -, ht⟩ := exists_ne_zero_of_sum_ne_zero hb
  have hw := left_ne_zero_of_mul ht
  have harr : arriving (cutLower N r hc) (lowerInj (cutVertices N r) inj) t₁ (cutLower N r hc).root =
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
  have hAF : ∀ F bot, allocationFactor N θ ρ F ((cutVertices N r) (.inr (cutLower N r hc).root)) bot =
      (fun F (b : Unit → Finset (Finset X)) => if b () = F then (1 : ℝ) else 0) F
        fun p => bot (cutArcs N r (unitArc hcr huniq) (.inr (.inl p))) :=
    fun F bot => allocationFactor_of_unique_arc hρ hcr huniq h1 F bot
  have h := isGlued_sum_mul_eq hg (ρ := ρ) (liftInj N c inj t) (AF := fun F b => if b () = F then (1 : ℝ) else 0) hAF (fun _ => 1) Φ
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
  have hAF : ∀ F bot, allocationFactor N θ ρ F ((cutVertices N r) (.inr (cutLower N r hc).root)) bot =
      (fun F (b : Unit → Finset (Finset X)) => if b () = F then (1 : ℝ) else 0) F
        fun p => bot (cutArcs N r (unitArc hcr huniq) (.inr (.inl p))) :=
    fun F bot => allocationFactor_of_unique_arc hρ hcr huniq h1 F bot
  have h := isGlued_sum_mul_eq hg (ρ := ρ) inj (AF := fun F b => if b () = F then (1 : ℝ) else 0) hAF (fun tP => Ψ (tP ())) Φ
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
    rootDist N θ ρ inj F = ∑ t, arcLaw N r hc θ ρ c inj t * rootDist N θ ρ (liftInj N c inj t) F := by
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
cut vertex: the law of the forest at the top of `c`, and the process with that forest at the source of
`c`. -/
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

end Banos2019
