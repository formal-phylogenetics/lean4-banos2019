module

public import Banos2019.Quartet.Concrete
public import Banos2019.Quartet.CherryArc
public import Banos2019.Quartet.RootedIso

/-!
# Figure 18 as an LSA quartet network (Proposition 7)

The `3₂`-cycle of Figure 18 is the unrooted network of the LSA quartet network `q18 a b c`: the nodes
`0, 1, 2, 3` are the leaves `a, b, c, d`; `4` is the parent of `a` and `b`, `5` the hybrid node above
`4`, `6` the node of `c`, `7` that of `d`, and the root `8` has the hybrid edge `8 → 5` and the tree
edge `8 → 7`, which the unrooted network merges into the hybrid edge `7 → 5` of Figure 18.

* `figLeaf`: the leaves `a, b, c, d` at the nodes `0, 1, 2, 3` of a figure.
* `isLSAQuartet_q18`, `inducesCycleType_q18`: `q18 a b c` with the parameters `q18Metric len γ` is
  an LSA quartet network with a `3₂`-cycle. Its metric unrooted network is Figure 18 with the
  parameters `figMetric len γ` (`inducesNetwork_q18`, in `Banos2019.Quartet.Examples`).
* The terms of Lemma 11 for `q18` (Example 5): the trees `Q₁⊕`, `Q₂⊕` without one hybrid edge
  (`cf_deleteArc_q18_seven`, `cf_deleteArc_q18_six`); the trees `Q_a⊕`, `Q_b⊕` with the hybrid edges
  disjointed from the hybrid node, isomorphic to `qDisj` (`disjointNetQ18Iso`, `cf_disjointNet_q18`,
  `cf_qDisj`); `P(K = 1) = 1 - x₁`, `P(K = 2) = x₁` (`probLineages_q18`); and
  `CF(Q₀⊕ | K = 1) = (1, 0, 0)` (`condCF_contract_q18`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace Banos2019

/-- The tails of the edges of `q18`. -/
def q18Src : Fin 9 → Fin 9 := ![4, 4, 6, 7, 5, 7, 8, 6, 8]

/-- The heads of the edges of `q18`. -/
def q18Tgt : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 6, 5, 5, 7]

variable {X : Type*} [DecidableEq X]

/-- The leaves `a, b, c, d` at the nodes `0, 1, 2, 3`. -/
def figLeaf (a b c : X) (x : X) : Fin 8 := if x = a then 0 else if x = b then 1 else if x = c then 2 else 3

/-- **Figure 18 as a rooted network**, with the root on the hybrid edge from the node of `d`. -/
def q18 (a b c : X) : RootedNetwork (Fin 9) (Fin 9) X :=
  ⟨⟨q18Src, q18Tgt⟩, 8, fun x => (figLeaf a b c x).castSucc⟩

/-- The parameters of `q18`: those of Figure 18, the length `len 6` of the merged hybrid edge shared by
the two edges at the root. -/
def q18Metric (len : Fin 8 → ℝ) (γ : ℝ) : MetricData (Fin 9) :=
  ⟨![len 0, len 1, len 2, len 3, len 4, len 5, len 6 / 2, len 7, len 6 / 2],
    ![1, 1, 1, 1, 1, 1, γ, 1 - γ, 1]⟩

section Degrees

variable (a b c : X)

theorem q18_indegree (v : Fin 9) :
    (q18 a b c).graph.indegree v = (univ.filter fun e => q18Tgt e = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [q18]

theorem q18_outdegree (v : Fin 9) :
    (q18 a b c).graph.outdegree v = (univ.filter fun e => q18Src e = v).card := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [q18]

end Degrees

variable {a b c d : X}

theorem figLeaf_a : figLeaf a b c a = 0 := by simp [figLeaf]
theorem figLeaf_b (h : Distinct4 a b c d) : figLeaf a b c b = 1 := by simp [figLeaf, h.1.symm]
theorem figLeaf_c (h : Distinct4 a b c d) : figLeaf a b c c = 2 := by
  simp [figLeaf, h.2.1.symm, h.2.2.2.1.symm]
theorem figLeaf_d (h : Distinct4 a b c d) : figLeaf a b c d = 3 := by
  simp [figLeaf, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm]

variable [Fintype X]

theorem figLeaf_injective (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    Function.Injective (figLeaf a b c) := by
  intro x y hxy
  rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;>
    rcases eq_or_of_distinct4_of_card_eq hX h y with rfl | rfl | rfl | rfl <;>
    simp only [figLeaf_a, figLeaf_b h, figLeaf_c h, figLeaf_d h] at hxy <;>
    first | rfl | exact absurd hxy (by decide)

omit [Fintype X] in
/-- The leaves of `q18` are `0, 1, 2, 3`. -/
theorem q18_leaf_mem (x : X) : (q18 a b c).leaf x ∈ ({0, 1, 2, 3} : Finset (Fin 9)) := by
  simp only [q18, figLeaf]
  split_ifs <;> decide

theorem q18_isPhylogenetic (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    (q18 a b c).IsPhylogenetic where
  finite_vertices := inferInstance
  finite_arcs := inferInstance
  finite_taxa := inferInstance
  acyclic := DirectedMultigraph.isAcyclic_of_rank _ (fun v : Fin 9 => ![5, 5, 5, 5, 4, 3, 2, 1, 0] v)
    (by show ∀ e, ![5, 5, 5, 5, 4, 3, 2, 1, 0] (q18Src e) < ![5, 5, 5, 5, 4, 3, 2, 1, 0] (q18Tgt e)
        decide)
  root_reaches v := by
    have h85 : (q18 a b c).graph.Adj 8 5 := ⟨6, rfl, rfl⟩
    have h87 : (q18 a b c).graph.Adj 8 7 := ⟨8, rfl, rfl⟩
    have h76 : (q18 a b c).graph.Adj 7 6 := ⟨5, rfl, rfl⟩
    have h54 : (q18 a b c).graph.Adj 5 4 := ⟨4, rfl, rfl⟩
    have h40 : (q18 a b c).graph.Adj 4 0 := ⟨0, rfl, rfl⟩
    have h41 : (q18 a b c).graph.Adj 4 1 := ⟨1, rfl, rfl⟩
    have h62 : (q18 a b c).graph.Adj 6 2 := ⟨2, rfl, rfl⟩
    have h73 : (q18 a b c).graph.Adj 7 3 := ⟨3, rfl, rfl⟩
    show Relation.ReflTransGen _ 8 v
    fin_cases v
    · exact ((Relation.ReflTransGen.single h85).tail h54).tail h40
    · exact ((Relation.ReflTransGen.single h85).tail h54).tail h41
    · exact ((Relation.ReflTransGen.single h87).tail h76).tail h62
    · exact (Relation.ReflTransGen.single h87).tail h73
    · exact (Relation.ReflTransGen.single h85).tail h54
    · exact Relation.ReflTransGen.single h85
    · exact (Relation.ReflTransGen.single h87).tail h76
    · exact Relation.ReflTransGen.single h87
    · exact .refl
  root_indegree := by
    rw [q18_indegree]
    show #(univ.filter fun e => q18Tgt e = 8) = 0
    decide
  nonroot_indegree v hv := by
    rw [q18_indegree]
    fin_cases v <;> first | decide | exact absurd rfl hv
  leaf_injective := fun x y hxy => figLeaf_injective hX h (Fin.castSucc_injective _ hxy)
  leaf_indegree x := by
    rw [q18_indegree]
    have := q18_leaf_mem (a := a) (b := b) (c := c) x
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide
  leaves v := by
    rw [q18_outdegree]
    constructor
    · intro h0
      fin_cases v
      · exact ⟨a, by simp [q18, figLeaf_a]⟩
      · exact ⟨b, by simp [q18, figLeaf_b h]⟩
      · exact ⟨c, by simp [q18, figLeaf_c h]⟩
      · exact ⟨d, by simp [q18, figLeaf_d h]⟩
      all_goals exact absurd h0 (by decide)
    · rintro ⟨x, rfl⟩
      have := q18_leaf_mem (a := a) (b := b) (c := c) x
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide

omit [Fintype X] in
theorem q18_isBinary (a b c : X) : (q18 a b c).IsBinary := by
  refine ⟨by rw [q18_outdegree]; show #(univ.filter fun e => q18Src e = 8) = 2; decide,
    fun v hv h0 => ?_⟩
  rw [q18_indegree, q18_outdegree]
  rw [q18_outdegree] at h0
  fin_cases v <;> first | decide | exact absurd rfl hv | exact absurd (by decide) h0

theorem q18_isBinaryRootedNetwork (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    IsBinaryRootedNetwork (q18 a b c) :=
  ⟨q18_isPhylogenetic hX h, q18_isBinary a b c⟩

/-! ### Cycles -/

/-- A node of a cycle without loops meets two distinct edges of the cycle. -/
theorem IsCycleOf.exists_two_incident {V' E' : Type*} {G : DirectedMultigraph V' E'} {k : ℕ}
    {v : Fin k → V'} {e : Fin k → E'} (hc : IsCycleOf G k v e)
    (hloop : ∀ f, G.source f ≠ G.target f) (i : Fin k) :
    ∃ j j', j ≠ j' ∧ (G.source (e j) = v i ∨ G.target (e j) = v i) ∧
      (G.source (e j') = v i ∨ G.target (e j') = v i) := by
  refine ⟨i, (finRotate k).symm i, fun h => ?_, ?_, ?_⟩
  · have hj := hc.joins i
    have : finRotate k i = i := by
      conv_lhs => rw [h]
      exact (finRotate k).apply_symm_apply i
    rw [this] at hj
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> exact hloop _ (h₁.trans h₂.symm)
  · rcases hc.joins i with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact Or.inl h₁
    · exact Or.inr h₂
  · have hj := hc.joins ((finRotate k).symm i)
    rw [(finRotate k).apply_symm_apply] at hj
    rcases hj with ⟨-, h₂⟩ | ⟨h₁, -⟩
    · exact Or.inr h₂
    · exact Or.inl h₁

/-- The edges `8 → 5`, `6 → 5`, `7 → 6`, `8 → 7` of the cycle of `q18`. -/
def q18Cycle : Finset (Fin 9) := {5, 6, 7, 8}

omit [Fintype X] in
/-- **The only cycle of `q18`**: leaves and the node `4` above two leaves are on no cycle, and the
four edges left form one cycle. -/
theorem q18_cycle_eq {C : Set (Fin 9)} (hC : IsCycle (q18 a b c).graph C) : C = ↑q18Cycle := by
  obtain ⟨k, v, e, hc, hrange⟩ := hC
  have hloop : ∀ f, (q18 a b c).graph.source f ≠ (q18 a b c).graph.target f := by
    show ∀ f, q18Src f ≠ q18Tgt f
    decide
  have htwo := hc.exists_two_incident hloop
  -- the ends of the edges of the cycle are nodes of the cycle
  have hends : ∀ j, (∃ i, v i = q18Src (e j)) ∧ ∃ i, v i = q18Tgt (e j) := by
    intro j
    rcases hc.joins j with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨⟨j, h₁.symm⟩, ⟨_, h₂.symm⟩⟩
    · exact ⟨⟨_, h₁.symm⟩, ⟨j, h₂.symm⟩⟩
  -- no leaf is on the cycle: a leaf meets one edge
  have hleaf : ∀ i, v i ≠ 0 ∧ v i ≠ 1 ∧ v i ≠ 2 ∧ v i ≠ 3 := by
    intro i
    obtain ⟨j, j', hjj, hj, hj'⟩ := htwo i
    have key : ∀ p : Fin 9, p.val < 4 → ∀ f, (q18Src f = p ∨ q18Tgt f = p) → f = p := by decide
    have hp : ∀ p : Fin 9, p.val < 4 → v i = p → False := fun p hp hv => by
      rw [hv] at hj hj'
      exact hjj (hc.injective_edge ((key p hp _ hj).trans (key p hp _ hj').symm))
    exact ⟨fun h => hp 0 (by decide) h, fun h => hp 1 (by decide) h, fun h => hp 2 (by decide) h,
      fun h => hp 3 (by decide) h⟩
  have hnotleaf : ∀ j, q18Src (e j) ∉ ({0, 1, 2, 3} : Finset (Fin 9)) ∧
      q18Tgt (e j) ∉ ({0, 1, 2, 3} : Finset (Fin 9)) := by
    intro j
    obtain ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩ := hends j
    have h₁ := hleaf i
    have h₂ := hleaf i'
    rw [hi] at h₁
    rw [hi'] at h₂
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨h₁, h₂⟩
  -- the node `4` is not on the cycle: of its edges, two lead to leaves
  have h4 : ∀ i, v i ≠ 4 := by
    intro i hv
    obtain ⟨j, j', hjj, hj, hj'⟩ := htwo i
    rw [hv] at hj hj'
    have key : ∀ f, (q18Src f = 4 ∨ q18Tgt f = 4) →
        q18Src f ∉ ({0, 1, 2, 3} : Finset (Fin 9)) → q18Tgt f ∉ ({0, 1, 2, 3} : Finset (Fin 9)) →
        f = 4 := by decide
    exact hjj (hc.injective_edge ((key _ hj (hnotleaf j).1 (hnotleaf j).2).trans
      (key _ hj' (hnotleaf j').1 (hnotleaf j').2).symm))
  -- so the edges of the cycle are among `5, 6, 7, 8`
  have hsub : ∀ j, e j ∈ q18Cycle := by
    intro j
    obtain ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩ := hends j
    have key : ∀ f, q18Src f ∉ ({0, 1, 2, 3, 4} : Finset (Fin 9)) →
        q18Tgt f ∉ ({0, 1, 2, 3, 4} : Finset (Fin 9)) → f ∈ q18Cycle := by decide
    refine key _ ?_ ?_
    · rw [← hi]
      have := hleaf i
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2, h4 i⟩
    · rw [← hi']
      have := hleaf i'
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2, h4 i'⟩
  -- each node of the cycle meets exactly two of these edges, so the cycle has all four
  have hstep : ∀ j g, g ∈ q18Cycle →
      (q18Src g = q18Src (e j) ∨ q18Tgt g = q18Src (e j) ∨ q18Src g = q18Tgt (e j) ∨
        q18Tgt g = q18Tgt (e j)) → ∃ m, e m = g := by
    intro j g hg hshare
    have hnode : ∃ i, v i = q18Src (e j) ∧ (q18Src g = v i ∨ q18Tgt g = v i) ∨
        v i = q18Tgt (e j) ∧ (q18Src g = v i ∨ q18Tgt g = v i) := by
      obtain ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩ := hends j
      rcases hshare with h | h | h | h
      · exact ⟨i, Or.inl ⟨hi, Or.inl (h.trans hi.symm)⟩⟩
      · exact ⟨i, Or.inl ⟨hi, Or.inr (h.trans hi.symm)⟩⟩
      · exact ⟨i', Or.inr ⟨hi', Or.inl (h.trans hi'.symm)⟩⟩
      · exact ⟨i', Or.inr ⟨hi', Or.inr (h.trans hi'.symm)⟩⟩
    obtain ⟨i, hi⟩ := hnode
    have hgi : q18Src g = v i ∨ q18Tgt g = v i := by rcases hi with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h
    obtain ⟨m, m', hmm, hm, hm'⟩ := htwo i
    have key : ∀ p f₁ f₂ f, f₁ ≠ f₂ → f₁ ∈ q18Cycle → f₂ ∈ q18Cycle → f ∈ q18Cycle →
        (q18Src f₁ = p ∨ q18Tgt f₁ = p) → (q18Src f₂ = p ∨ q18Tgt f₂ = p) →
        (q18Src f = p ∨ q18Tgt f = p) → f = f₁ ∨ f = f₂ := by decide
    rcases key (v i) (e m) (e m') g (fun h => hmm (hc.injective_edge h)) (hsub m) (hsub m') hg hm hm'
      hgi with h | h
    · exact ⟨m, h.symm⟩
    · exact ⟨m', h.symm⟩
  have hk := hc.pos
  have hall : ∀ g ∈ q18Cycle, ∃ m, e m = g := by
    have h₀ := hsub ⟨0, hk⟩
    have reach : ∀ g ∈ q18Cycle, ∀ f ∈ q18Cycle, (∃ m, e m = f) → ∃ m, e m = g := by
      intro g hg f hf ⟨m, hm⟩
      have hm' : e m ∈ q18Cycle := hsub m
      -- the edges `5 — 7 — 8 — 6 — 5` share ends in turn
      have adj : ∀ f₁ ∈ q18Cycle, ∀ f₂ ∈ q18Cycle, (∃ m, e m = f₁) →
          (q18Src f₂ = q18Src f₁ ∨ q18Tgt f₂ = q18Src f₁ ∨ q18Src f₂ = q18Tgt f₁ ∨
            q18Tgt f₂ = q18Tgt f₁) → ∃ m, e m = f₂ := by
        rintro f₁ - f₂ hf₂ ⟨m₁, rfl⟩ hsh
        exact hstep m₁ f₂ hf₂ hsh
      have chain : ∀ f₁ ∈ q18Cycle, ∀ f₂ ∈ q18Cycle, ∃ f₃ ∈ q18Cycle,
          (q18Src f₃ = q18Src f₁ ∨ q18Tgt f₃ = q18Src f₁ ∨ q18Src f₃ = q18Tgt f₁ ∨
            q18Tgt f₃ = q18Tgt f₁) ∧
          (q18Src f₂ = q18Src f₃ ∨ q18Tgt f₂ = q18Src f₃ ∨ q18Src f₂ = q18Tgt f₃ ∨
            q18Tgt f₂ = q18Tgt f₃) := by decide
      obtain ⟨f₃, hf₃, h₁, h₂⟩ := chain f hf g hg
      exact adj f₃ hf₃ g hg (adj f hf f₃ hf₃ ⟨m, hm⟩ h₁) h₂
    exact fun g hg => reach g hg _ h₀ ⟨⟨0, hk⟩, rfl⟩
  rw [← hrange]
  ext f
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    have := hsub j
    simpa [q18Cycle] using this
  · intro hf
    exact hall f (by simpa [q18Cycle] using hf)

omit [Fintype X] in
theorem q18_isLevelOne : IsLevelOne (q18 a b c).graph := fun _ _ hC hC' _ =>
  (q18_cycle_eq hC).trans (q18_cycle_eq hC').symm

/-! ### The root is the LSA -/

omit [Fintype X] in
/-- The path `8 → u₁ → u₂ → t` of `q18`, along the edges `e₁, e₂, e₃`, avoids every other node. -/
theorem q18_hasPathAvoiding {e₁ e₂ e₃ : Fin 9} (h₁ : q18Src e₁ = 8) (h₂ : q18Tgt e₁ = q18Src e₂)
    (h₃ : q18Tgt e₂ = q18Src e₃) {w : Fin 9}
    (hw : w ∉ ({8, q18Tgt e₁, q18Tgt e₂, q18Tgt e₃} : Finset (Fin 9))) :
    (q18 a b c).HasPathAvoiding 8 (q18Tgt e₃) w := by
  simp only [mem_insert, mem_singleton, not_or] at hw
  obtain ⟨hw₀, hw₁, hw₂, hw₃⟩ := hw
  refine ⟨Ne.symm hw₀, Ne.symm hw₃, ?_⟩
  refine ((Relation.ReflTransGen.single ⟨⟨e₁, h₁, rfl⟩, Ne.symm hw₀, Ne.symm hw₁⟩).tail
    ⟨⟨e₂, h₂.symm, rfl⟩, Ne.symm hw₁, Ne.symm hw₂⟩).tail ⟨⟨e₃, h₃.symm, rfl⟩, Ne.symm hw₂, Ne.symm hw₃⟩

omit [Fintype X] in
theorem q18_isLSANetwork (h : Distinct4 a b c d) : (q18 a b c).IsLSANetwork := by
  refine ⟨root_isStableAncestor _ _, fun w hw => ?_⟩
  suffices hw8 : w = 8 by rw [hw8]; exact .refl
  by_contra hne
  have hla : (q18 a b c).leaf a = q18Tgt 0 := by simp [q18, figLeaf_a]; rfl
  have hlb : (q18 a b c).leaf b = q18Tgt 1 := by simp [q18, figLeaf_b h]; rfl
  have hlc : (q18 a b c).leaf c = q18Tgt 2 := by simp [q18, figLeaf_c h]; rfl
  by_cases h₁ : w ∈ ({8, q18Tgt 6, q18Tgt 4, q18Tgt 1} : Finset (Fin 9))
  · by_cases h₀ : w ∈ ({8, q18Tgt 6, q18Tgt 4, q18Tgt 0} : Finset (Fin 9))
    · -- `w` is `5` or `4`: the path to `c` avoids it
      have key : ∀ w : Fin 9, w ≠ 8 → w ∈ ({8, q18Tgt 6, q18Tgt 4, q18Tgt 1} : Finset (Fin 9)) →
          w ∈ ({8, q18Tgt 6, q18Tgt 4, q18Tgt 0} : Finset (Fin 9)) →
          w ∉ ({8, q18Tgt 8, q18Tgt 5, q18Tgt 2} : Finset (Fin 9)) := by decide
      have h₂ := key w hne h₁ h₀
      exact hw c (Set.mem_univ _) (hlc ▸ q18_hasPathAvoiding rfl rfl rfl h₂)
    · exact hw a (Set.mem_univ _) (hla ▸ q18_hasPathAvoiding rfl rfl rfl h₀)
  · exact hw b (Set.mem_univ _) (hlb ▸ q18_hasPathAvoiding rfl rfl rfl h₁)

/-! ### The parameters -/

omit [Fintype X] in
theorem q18_isHybridArc_iff (e : Fin 9) : (q18 a b c).IsHybridArc e ↔ e = 6 ∨ e = 7 := by
  unfold IsHybridArc
  rw [q18_indegree]
  show 2 ≤ #(univ.filter fun f => q18Tgt f = q18Tgt e) ↔ e = 6 ∨ e = 7
  revert e
  decide

omit [Fintype X] in
theorem q18_isTreeArc_iff (e : Fin 9) : (q18 a b c).IsTreeArc e ↔ ¬ (e = 6 ∨ e = 7) := by
  unfold IsTreeArc
  rw [q18_indegree]
  show #(univ.filter fun f => q18Tgt f = q18Tgt e) = 1 ↔ ¬ (e = 6 ∨ e = 7)
  revert e
  decide

omit [Fintype X] in
theorem q18Metric_isMetricNetwork {len : Fin 8 → ℝ} (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ)
    (hγ₁ : γ < 1) : IsMetricNetwork (q18 a b c) (q18Metric len γ) := by
  have hpos : ∀ e, 0 < (q18Metric len γ).length e := by
    intro e
    fin_cases e <;> simp [q18Metric, hlen]
  refine ⟨⟨fun e _ => hpos e, fun e _ => (hpos e).le, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩,
    hpos⟩
  · rw [q18_isTreeArc_iff] at he
    fin_cases e <;> simp_all [q18Metric]
  · rw [q18_isHybridArc_iff] at he
    rcases he with rfl | rfl
    · simpa [q18Metric] using hγ₀
    · simpa [q18Metric] using hγ₁
  · rw [q18_indegree] at hv
    have hv5 : v = 5 := by revert v; decide
    subst hv5
    simp [Fin.sum_univ_succ, q18Metric, q18, q18Tgt]

/-! ### The `3₂`-cycle -/

omit [Fintype X] in
theorem q18_reaches_five {w : Fin 9} (hw : (q18 a b c).graph.Reaches 5 w) :
    w ∈ ({5, 4, 0, 1} : Finset (Fin 9)) := by
  induction hw with
  | refl => decide
  | @tail p q _ hpq ih =>
    obtain ⟨e, rfl, rfl⟩ := hpq
    have key : ∀ e, q18Src e ∈ ({5, 4, 0, 1} : Finset (Fin 9)) →
        q18Tgt e ∈ ({5, 4, 0, 1} : Finset (Fin 9)) := by decide
    exact key e ih

omit [Fintype X] in
/-- The edges `5, 6, 7, 8` form a cycle of `q18`. -/
theorem q18_isCycle : IsCycle (q18 a b c).graph ↑q18Cycle := by
  refine ⟨4, ![8, 5, 6, 7], ![6, 7, 5, 8], ⟨by decide, ?_, by decide, by decide⟩, ?_⟩
  · show ∀ i : Fin 4, (q18Src (![6, 7, 5, 8] i) = ![8, 5, 6, 7] i ∧
        q18Tgt (![6, 7, 5, 8] i) = ![8, 5, 6, 7] (finRotate 4 i)) ∨
      (q18Src (![6, 7, 5, 8] i) = ![8, 5, 6, 7] (finRotate 4 i) ∧
        q18Tgt (![6, 7, 5, 8] i) = ![8, 5, 6, 7] i)
    decide
  · ext f
    simp only [Set.mem_range, q18Cycle, coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨2, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩, ⟨3, rfl⟩]

/-- **The cycle of `q18` induces a `3₂`-cycle**, with hybrid node `5`. -/
theorem inducesCycleType_q18 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    InducesCycleType (q18 a b c) ↑q18Cycle 5 3 2 := by
  have hcyc := q18_isCycle (a := a) (b := b) (c := c)
  have hla : (q18 a b c).leaf a = 0 := by simp [q18, figLeaf_a]
  have hlb : (q18 a b c).leaf b = 1 := by simp [q18, figLeaf_b h]
  have hlc : (q18 a b c).leaf c = 2 := by simp [q18, figLeaf_c h]
  have hld : (q18 a b c).leaf d = 3 := by simp [q18, figLeaf_d h]
  refine ⟨hcyc, ⟨6, by decide, Or.inr rfl⟩, by rw [q18_indegree]; decide, ?_, ?_⟩
  · have h8 : (q18 a b c).root ∈ cycleNodes (q18 a b c).graph ↑q18Cycle :=
      ⟨6, by decide, Or.inl rfl⟩
    rw [ite_eq_left h8, Set.ncard_coe_finset]
    decide
  · have hset : {x | (q18 a b c).graph.Reaches 5 ((q18 a b c).leaf x)} = {a, b} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hx
        have := q18_reaches_five hx
        rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · rw [hlc] at this; exact absurd this (by decide)
        · rw [hld] at this; exact absurd this (by decide)
      · rintro (rfl | rfl)
        · rw [hla]
          exact (Relation.ReflTransGen.single ⟨4, rfl, rfl⟩).tail ⟨0, rfl, rfl⟩
        · rw [hlb]
          exact (Relation.ReflTransGen.single ⟨4, rfl, rfl⟩).tail ⟨1, rfl, rfl⟩
    rw [hset, Set.ncard_pair h.1]

theorem exists_inducesCycleType_q18 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    ∃ C v, InducesCycleType (q18 a b c) C v 3 2 :=
  ⟨_, _, inducesCycleType_q18 hX h⟩

/-! ### `q18` is an LSA quartet network -/

theorem isLSAQuartet_q18 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    IsLSAQuartet (q18 a b c) (q18Metric len γ) :=
  ⟨q18_isBinaryRootedNetwork hX h, q18_isLevelOne, q18_isLSANetwork h, hX,
    q18Metric_isMetricNetwork hlen hγ₀ hγ₁⟩

/-! ### The trees `Q₁⊕`, `Q₂⊕` of Lemma 11 -/

section Trees

omit [Fintype X] in
/-- The leaves of `q18` are those of `quartetLeaf9`. -/
theorem q18_leaf_eq : (q18 a b c).leaf = quartetLeaf9 a b c := by
  funext x
  simp only [q18, figLeaf, quartetLeaf9]
  split_ifs <;> rfl

omit [Fintype X] in
/-- The indegrees of `q18` without the edge `h`. -/
theorem deleteArc_q18_indegree (h v : Fin 9) :
    (deleteArc (q18 a b c) h).graph.indegree v =
      (univ.filter fun e : {e : Fin 9 // e ≠ h} => q18Tgt e.1 = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [deleteArc, q18]

/-- The descendants of the nodes of `q18` without the hybrid edge `7`. -/
def q18DescSeven : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {4, 0, 1}, {5, 4, 0, 1}, {6, 2}, {7, 3, 6, 2}, univ]

/-- The descendants of the nodes of `q18`, with or without the hybrid edge `6`. -/
def q18Desc : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {4, 0, 1}, {5, 4, 0, 1}, {6, 2, 5, 4, 0, 1}, {7, 3, 6, 2, 5, 4, 0, 1}, univ]

/-- The edges of the split `ab|cd` of `q18` without the hybrid edge `7`: `5 → 4`, `8 → 5`, `8 → 7`. -/
def q18ArcsSeven : Finset {e : Fin 9 // e ≠ 7} := {⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩}

/-- The edges of the split `ab|cd` of `q18` without the hybrid edge `6`: `5 → 4`, `6 → 5`. -/
def q18ArcsSix : Finset {e : Fin 9 // e ≠ 6} := {⟨4, by decide⟩, ⟨7, by decide⟩}

/-- The taxa of the leaves `0, 1` of `q18` are `a, b`, those of `2, 3` are `c, d`. -/
theorem leafSet_q18 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    leafSet (quartetLeaf9 a b c) {0, 1} = {a, b} ∧ leafSet (quartetLeaf9 a b c) {2, 3} = {a, b}ᶜ := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  constructor
  · ext x
    rw [leafSet_quartetLeaf9 hX h]
    simp only [mem_insert, mem_singleton]
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]
  · ext x
    rw [leafSet_quartetLeaf9 hX h]
    simp only [mem_compl, mem_insert, mem_singleton]
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]

/-- **`q18` without the hybrid edge `7` (`Q₁⊕`) is a tree with the split `ab|cd`**, of length
`t₁ + t₄`: the concordance factor of `ab|cd` is `1 - ⅔x₁x₄`, those of `ac|bd` and `ad|bc` are
`⅓x₁x₄` (equation (1)). -/
theorem cf_deleteArc_q18_seven (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    cf (deleteArc (q18 a b c) 7) (deleteArcMetric (q18 a b c) 7 (q18Metric len γ))
        (quartetTree a b c d h) = 1 - 2 / 3 * (Real.exp (-len 4) * Real.exp (-len 6)) ∧
      cf (deleteArc (q18 a b c) 7) (deleteArcMetric (q18 a b c) 7 (q18Metric len γ))
        (quartetTree a c b d (distinct4_acbd h)) = 1 / 3 * (Real.exp (-len 4) * Real.exp (-len 6)) ∧
      cf (deleteArc (q18 a b c) 7) (deleteArcMetric (q18 a b c) 7 (q18Metric len γ))
        (quartetTree a d b c (distinct4_adbc h)) = 1 / 3 * (Real.exp (-len 4) * Real.exp (-len 6)) := by
  have hQ := isLSAQuartet_q18 hX h hlen hγ₀ hγ₁
  have hN : (deleteArc (q18 a b c) 7).IsPhylogenetic :=
    isPhylogenetic_deleteArc hQ.binary.1 (h' := 6) (g := 2) (by decide) rfl (by decide) rfl
  have ht : ∀ e, ¬ (deleteArc (q18 a b c) 7).IsHybridArc e := by
    intro e
    unfold IsHybridArc
    rw [deleteArc_q18_indegree]
    show ¬ 2 ≤ #(univ.filter fun f : {e : Fin 9 // e ≠ 7} => q18Tgt f.1 = q18Tgt e.1)
    revert e
    decide
  have hθ : (deleteArc (q18 a b c) 7).IsMetric (deleteArcMetric (q18 a b c) 7 (q18Metric len γ)) := by
    convert isMetric_deleteArc hQ.binary.1 hQ.metric.1 hQ.metric.2 (h := 7) (h' := 6) (by decide)
      rfl (by rw [q18_indegree]; show #(univ.filter fun e => q18Tgt e = 5) = 2; decide)
  have hD : ∀ u w, (deleteArc (q18 a b c) 7).graph.Reaches u w ↔ w ∈ q18DescSeven u :=
    reaches_iff_mem_of_desc q18DescSeven (by decide)
      (by show ∀ u (e : {e : Fin 9 // e ≠ 7}), q18Src e.1 ∈ q18DescSeven u →
            q18Tgt e.1 ∈ q18DescSeven u
          decide)
      (by show ∀ u, ∀ w ∈ q18DescSeven u, w ≠ u → ∃ e : {e : Fin 9 // e ≠ 7}, q18Src e.1 = u ∧
            w ∈ q18DescSeven (q18Tgt e.1) ∧ #(q18DescSeven (q18Tgt e.1)) < #(q18DescSeven u)
          decide)
  have hl : (deleteArc (q18 a b c) 7).leaf = quartetLeaf9 a b c := q18_leaf_eq
  obtain ⟨hS, hSc⟩ := leafSet_q18 hX h
  obtain ⟨e₁, e₂, e₃⟩ := cf_eq_of_desc hN ht hθ hX h q18DescSeven hD
    (L := {0, 1, 2, 3}) (hl ▸ quartetLeaf9_mem) (hl ▸ quartetLeaf9_surj h) (hl ▸ hS) (hl ▸ hSc)
    (v := 5) (by decide) q18ArcsSeven (by
      show ∀ e : {e : Fin 9 // e ≠ 7}, e ∈ q18ArcsSeven ↔
        (q18DescSeven (q18Tgt e.1) ∩ {0, 1, 2, 3} ≠ {0, 1, 2, 3} ∧
          (q18DescSeven (q18Tgt e.1) ∩ {0, 1, 2, 3} = {0, 1} ∩ {0, 1, 2, 3} ∨
            q18DescSeven (q18Tgt e.1) ∩ {0, 1, 2, 3} = {2, 3} ∩ {0, 1, 2, 3}))
      decide)
  have hsum : ∑ e ∈ q18ArcsSeven,
      (deleteArcMetric (q18 a b c) 7 (q18Metric len γ)).length e = len 4 + len 6 := by
    rw [q18ArcsSeven, sum_insert (by decide), sum_insert (by decide), sum_singleton]
    simp only [deleteArcMetric, q18Metric]
    simp
  rw [hsum, neg_add, Real.exp_add] at e₁ e₂ e₃
  exact ⟨e₁, e₂, e₃⟩

/-- **`q18` without the hybrid edge `6` (`Q₂⊕`) is a tree with the split `ab|cd`**, of length
`t₁ + t₂`: the concordance factor of `ab|cd` is `1 - ⅔x₁x₂`, those of `ac|bd` and `ad|bc` are
`⅓x₁x₂` (equation (1)). -/
theorem cf_deleteArc_q18_six (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    cf (deleteArc (q18 a b c) 6) (deleteArcMetric (q18 a b c) 6 (q18Metric len γ))
        (quartetTree a b c d h) = 1 - 2 / 3 * (Real.exp (-len 4) * Real.exp (-len 7)) ∧
      cf (deleteArc (q18 a b c) 6) (deleteArcMetric (q18 a b c) 6 (q18Metric len γ))
        (quartetTree a c b d (distinct4_acbd h)) = 1 / 3 * (Real.exp (-len 4) * Real.exp (-len 7)) ∧
      cf (deleteArc (q18 a b c) 6) (deleteArcMetric (q18 a b c) 6 (q18Metric len γ))
        (quartetTree a d b c (distinct4_adbc h)) = 1 / 3 * (Real.exp (-len 4) * Real.exp (-len 7)) := by
  have hQ := isLSAQuartet_q18 hX h hlen hγ₀ hγ₁
  have hN : (deleteArc (q18 a b c) 6).IsPhylogenetic :=
    isPhylogenetic_deleteArc hQ.binary.1 (h' := 7) (g := 8) (by decide) rfl (by decide) rfl
  have ht : ∀ e, ¬ (deleteArc (q18 a b c) 6).IsHybridArc e := by
    intro e
    unfold IsHybridArc
    rw [deleteArc_q18_indegree]
    show ¬ 2 ≤ #(univ.filter fun f : {e : Fin 9 // e ≠ 6} => q18Tgt f.1 = q18Tgt e.1)
    revert e
    decide
  have hθ : (deleteArc (q18 a b c) 6).IsMetric (deleteArcMetric (q18 a b c) 6 (q18Metric len γ)) := by
    convert isMetric_deleteArc hQ.binary.1 hQ.metric.1 hQ.metric.2 (h := 6) (h' := 7) (by decide)
      rfl (by rw [q18_indegree]; show #(univ.filter fun e => q18Tgt e = 5) = 2; decide)
  have hD : ∀ u w, (deleteArc (q18 a b c) 6).graph.Reaches u w ↔ w ∈ q18Desc u :=
    reaches_iff_mem_of_desc q18Desc (by decide)
      (by show ∀ u (e : {e : Fin 9 // e ≠ 6}), q18Src e.1 ∈ q18Desc u →
            q18Tgt e.1 ∈ q18Desc u
          decide)
      (by show ∀ u, ∀ w ∈ q18Desc u, w ≠ u → ∃ e : {e : Fin 9 // e ≠ 6}, q18Src e.1 = u ∧
            w ∈ q18Desc (q18Tgt e.1) ∧ #(q18Desc (q18Tgt e.1)) < #(q18Desc u)
          decide)
  have hl : (deleteArc (q18 a b c) 6).leaf = quartetLeaf9 a b c := q18_leaf_eq
  obtain ⟨hS, hSc⟩ := leafSet_q18 hX h
  obtain ⟨e₁, e₂, e₃⟩ := cf_eq_of_desc hN ht hθ hX h q18Desc hD
    (L := {0, 1, 2, 3}) (hl ▸ quartetLeaf9_mem) (hl ▸ quartetLeaf9_surj h) (hl ▸ hS) (hl ▸ hSc)
    (v := 5) (by decide) q18ArcsSix (by
      show ∀ e : {e : Fin 9 // e ≠ 6}, e ∈ q18ArcsSix ↔
        (q18Desc (q18Tgt e.1) ∩ {0, 1, 2, 3} ≠ {0, 1, 2, 3} ∧
          (q18Desc (q18Tgt e.1) ∩ {0, 1, 2, 3} = {0, 1} ∩ {0, 1, 2, 3} ∨
            q18Desc (q18Tgt e.1) ∩ {0, 1, 2, 3} = {2, 3} ∩ {0, 1, 2, 3}))
      decide)
  have hsum : ∑ e ∈ q18ArcsSix,
      (deleteArcMetric (q18 a b c) 6 (q18Metric len γ)).length e = len 4 + len 7 := by
    rw [q18ArcsSix, sum_insert (by decide), sum_singleton]
    rfl
  rw [hsum, neg_add, Real.exp_add] at e₁ e₂ e₃
  exact ⟨e₁, e₂, e₃⟩

/-! ### The trees `Q_a⊕`, `Q_b⊕` of Lemma 11 -/

/-- The tails of the edges of `qDisj`. -/
def qDisjSrc : Fin 6 → Fin 7 := ![2, 3, 3, 4, 2, 4]

/-- The heads of the edges of `qDisj`. -/
def qDisjTgt : Fin 6 → Fin 7 := ![0, 1, 2, 5, 6, 3]

/-- **`q18` with its hybrid edges disjointed from the hybrid node**: the nodes `6`, `7`, `8` of `q18`
are `2`, `3`, `4`, the leaves of `c` and `d` are `0` and `1`, and the hybrid edges `8 → 5` and `6 → 5`
end at the new leaves `5`, of `u₁`, and `6`, of `u₂`. -/
def qDisj (u₁ u₂ u₃ : X) : RootedNetwork (Fin 7) (Fin 6) X :=
  ⟨⟨qDisjSrc, qDisjTgt⟩, 4,
    fun x => if x = u₁ then 5 else if x = u₂ then 6 else if x = u₃ then 0 else 1⟩

/-- The parameters of `qDisj`: those of the edges `2, 3, 5, 6, 7, 8` of `q18`. -/
def qDisjMetric (len : Fin 8 → ℝ) : MetricData (Fin 6) :=
  ⟨![len 2, len 3, len 5, len 6 / 2, len 7, len 6 / 2], fun _ => 1⟩

/-- The descendants of the nodes of `qDisj`. -/
def qDisjDesc : Fin 7 → Finset (Fin 7) := ![{0}, {1}, {2, 0, 6}, {3, 1, 2, 0, 6}, univ, {5}, {6}]

section QDisj

variable {u₁ u₂ u₃ u₄ : X}

omit [Fintype X] in
theorem qDisj_indegree (u₁ u₂ u₃ : X) (v : Fin 7) :
    (qDisj u₁ u₂ u₃).graph.indegree v = (univ.filter fun e => qDisjTgt e = v).card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [qDisj]

omit [Fintype X] in
theorem qDisj_outdegree (u₁ u₂ u₃ : X) (v : Fin 7) :
    (qDisj u₁ u₂ u₃).graph.outdegree v = (univ.filter fun e => qDisjSrc e = v).card := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [qDisj]

omit [Fintype X] in
theorem qDisj_reaches_iff (u₁ u₂ u₃ : X) (u w : Fin 7) :
    (qDisj u₁ u₂ u₃).graph.Reaches u w ↔ w ∈ qDisjDesc u :=
  reaches_iff_mem_of_desc (G := (qDisj u₁ u₂ u₃).graph) qDisjDesc (by decide)
    (by show ∀ u (e : Fin 6), qDisjSrc e ∈ qDisjDesc u → qDisjTgt e ∈ qDisjDesc u
        decide)
    (by show ∀ u, ∀ w ∈ qDisjDesc u, w ≠ u → ∃ e : Fin 6, qDisjSrc e = u ∧
          w ∈ qDisjDesc (qDisjTgt e) ∧ #(qDisjDesc (qDisjTgt e)) < #(qDisjDesc u)
        decide) u w

omit [Fintype X] in
theorem qDisj_leaf_of (h : Distinct4 u₁ u₂ u₃ u₄) :
    (qDisj u₁ u₂ u₃).leaf u₁ = 5 ∧ (qDisj u₁ u₂ u₃).leaf u₂ = 6 ∧ (qDisj u₁ u₂ u₃).leaf u₃ = 0 ∧
      (qDisj u₁ u₂ u₃).leaf u₄ = 1 := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := h
  refine ⟨by simp [qDisj], by simp [qDisj, Ne.symm h12], by simp [qDisj, Ne.symm h13, Ne.symm h23],
    by simp [qDisj, Ne.symm h14, Ne.symm h24, Ne.symm h34]⟩

omit [Fintype X] in
theorem qDisj_leaf_mem (x : X) : (qDisj u₁ u₂ u₃).leaf x ∈ ({0, 1, 5, 6} : Finset (Fin 7)) := by
  simp only [qDisj]
  split_ifs <;> decide

theorem qDisj_isPhylogenetic (hX : Fintype.card X = 4) (h : Distinct4 u₁ u₂ u₃ u₄) :
    (qDisj u₁ u₂ u₃).IsPhylogenetic where
  finite_vertices := inferInstance
  finite_arcs := inferInstance
  finite_taxa := inferInstance
  acyclic := DirectedMultigraph.isAcyclic_of_rank _ (fun v : Fin 7 => ![3, 3, 2, 1, 0, 3, 3] v)
    (by show ∀ e, ![3, 3, 2, 1, 0, 3, 3] (qDisjSrc e) < ![3, 3, 2, 1, 0, 3, 3] (qDisjTgt e)
        decide)
  root_reaches v := (qDisj_reaches_iff u₁ u₂ u₃ 4 v).2 (by simp [qDisjDesc])
  root_indegree := by
    rw [qDisj_indegree]
    show #(univ.filter fun e => qDisjTgt e = 4) = 0
    decide
  nonroot_indegree v hv := by
    rw [qDisj_indegree]
    fin_cases v <;> first | decide | exact absurd rfl hv
  leaf_injective := by
    obtain ⟨l₁, l₂, l₃, l₄⟩ := qDisj_leaf_of (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) h
    intro x y hxy
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl <;>
      rcases eq_or_of_distinct4_of_card_eq hX h y with rfl | rfl | rfl | rfl <;>
      simp only [l₁, l₂, l₃, l₄] at hxy <;> first | rfl | exact absurd hxy (by decide)
  leaf_indegree x := by
    rw [qDisj_indegree]
    have := qDisj_leaf_mem (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) x
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide
  leaves v := by
    obtain ⟨l₁, l₂, l₃, l₄⟩ := qDisj_leaf_of (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) h
    rw [qDisj_outdegree]
    constructor
    · intro h0
      fin_cases v
      · exact ⟨u₃, l₃⟩
      · exact ⟨u₄, l₄⟩
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
      · exact ⟨u₁, l₁⟩
      · exact ⟨u₂, l₂⟩
    · rintro ⟨x, rfl⟩
      have := qDisj_leaf_mem (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) x
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h' | h' <;> rw [h'] <;> decide

omit [Fintype X] in
theorem qDisj_not_isHybridArc (e : Fin 6) : ¬ (qDisj u₁ u₂ u₃).IsHybridArc e := by
  unfold IsHybridArc
  rw [qDisj_indegree]
  show ¬ 2 ≤ #(univ.filter fun f => qDisjTgt f = qDisjTgt e)
  revert e
  decide

omit [Fintype X] in
theorem qDisjMetric_isMetric {len : Fin 8 → ℝ} (hlen : ∀ i, 0 < len i) :
    (qDisj u₁ u₂ u₃).IsMetric (qDisjMetric len) := by
  refine ⟨fun e _ => ?_, fun e he => absurd he (qDisj_not_isHybridArc e), fun e _ => rfl,
    fun e he => absurd he (qDisj_not_isHybridArc e), fun v hv => ?_⟩
  · fin_cases e <;> simp [qDisjMetric, hlen]
  · rw [qDisj_indegree] at hv
    exact absurd hv (by revert v; decide)

/-- **`qDisj u₁ u₂ u₃` is a tree with the split `u₂u₃|u₁u₄`**, of length `t₃`: the concordance factor
of `u₂u₃|u₁u₄` is `1 - ⅔x₃`, those of the two others are `⅓x₃` (equation (1)). -/
theorem cf_qDisj (hX : Fintype.card X = 4) (h : Distinct4 u₁ u₂ u₃ u₄) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) (h' : Distinct4 u₂ u₃ u₁ u₄) :
    cf (qDisj u₁ u₂ u₃) (qDisjMetric len) (quartetTree u₂ u₃ u₁ u₄ h') =
        1 - 2 / 3 * Real.exp (-len 5) ∧
      cf (qDisj u₁ u₂ u₃) (qDisjMetric len) (quartetTree u₂ u₁ u₃ u₄ (distinct4_acbd h')) =
        1 / 3 * Real.exp (-len 5) ∧
      cf (qDisj u₁ u₂ u₃) (qDisjMetric len) (quartetTree u₂ u₄ u₃ u₁ (distinct4_adbc h')) =
        1 / 3 * Real.exp (-len 5) := by
  obtain ⟨l₁, l₂, l₃, l₄⟩ := qDisj_leaf_of (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) h
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := id h
  have hleaf : ∀ x, x = u₁ ∨ x = u₂ ∨ x = u₃ ∨ x = u₄ := eq_or_of_distinct4_of_card_eq hX h
  have hS : leafSet (qDisj u₁ u₂ u₃).leaf {6, 0} = {u₂, u₃} := by
    ext x
    simp only [leafSet, mem_filter, mem_univ, true_and]
    rcases hleaf x with rfl | rfl | rfl | rfl
    · rw [l₁]; simp [h12, h13]
    · rw [l₂]; simp
    · rw [l₃]; simp
    · rw [l₄]; simp [Ne.symm h24, Ne.symm h34]
  have hSc : leafSet (qDisj u₁ u₂ u₃).leaf {5, 1} = {u₂, u₃}ᶜ := by
    ext x
    simp only [leafSet, mem_filter, mem_univ, true_and, mem_compl]
    rcases hleaf x with rfl | rfl | rfl | rfl
    · rw [l₁]; simp [h12, h13]
    · rw [l₂]; simp
    · rw [l₃]; simp
    · rw [l₄]; simp [Ne.symm h24, Ne.symm h34]
  have hsurj : ∀ i ∈ ({0, 1, 5, 6} : Finset (Fin 7)), ∃ x, (qDisj u₁ u₂ u₃).leaf x = i := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    exacts [⟨u₃, l₃⟩, ⟨u₄, l₄⟩, ⟨u₁, l₁⟩, ⟨u₂, l₂⟩]
  obtain ⟨e₁, e₂, e₃⟩ := cf_eq_of_desc (qDisj_isPhylogenetic hX h) (fun e => qDisj_not_isHybridArc e)
    (qDisjMetric_isMetric hlen) hX h' qDisjDesc (qDisj_reaches_iff u₁ u₂ u₃) (L := {0, 1, 5, 6})
    qDisj_leaf_mem hsurj hS hSc (v := 2) (by decide) {2} (by
      show ∀ e : Fin 6, e ∈ ({2} : Finset (Fin 6)) ↔
        (qDisjDesc (qDisjTgt e) ∩ {0, 1, 5, 6} ≠ {0, 1, 5, 6} ∧
          (qDisjDesc (qDisjTgt e) ∩ {0, 1, 5, 6} = {6, 0} ∩ {0, 1, 5, 6} ∨
            qDisjDesc (qDisjTgt e) ∩ {0, 1, 5, 6} = {5, 1} ∩ {0, 1, 5, 6}))
      decide)
  have hsum : ∑ e ∈ ({2} : Finset (Fin 6)), (qDisjMetric len).length e = len 5 := by
    rw [sum_singleton]
    rfl
  rw [hsum] at e₁ e₂ e₃
  exact ⟨e₁, e₂, e₃⟩

end QDisj

omit [Fintype X] in
theorem q18_reaches_iff (u w : Fin 9) : (q18 a b c).graph.Reaches u w ↔ w ∈ q18Desc u :=
  reaches_iff_mem_of_desc (G := (q18 a b c).graph) q18Desc (by decide)
    (by show ∀ u (e : Fin 9), q18Src e ∈ q18Desc u → q18Tgt e ∈ q18Desc u
        decide)
    (by show ∀ u, ∀ w ∈ q18Desc u, w ≠ u → ∃ e : Fin 9, q18Src e = u ∧
          w ∈ q18Desc (q18Tgt e) ∧ #(q18Desc (q18Tgt e)) < #(q18Desc u)
        decide) u w

/-- The nodes of `qDisj` of the nodes `2, 3, 6, 7, 8` of `q18`. -/
def q18DisjVert : Fin 9 → Fin 7 := ![0, 0, 0, 1, 0, 0, 2, 3, 4]

/-- The edges of `qDisj` of the edges `2, 3, 5, 6, 7, 8` of `q18`. -/
def q18DisjArc : Fin 9 → Fin 6 := ![0, 0, 0, 1, 0, 2, 3, 4, 5]

/-- The new leaves `5`, `6` of `qDisj`. -/
def qDisjNewLeaf : Fin 2 → Fin 7 := ![5, 6]

omit [Fintype X] in
theorem q18_not_reaches_five_iff (u : Fin 9) :
    ¬ (q18 a b c).graph.Reaches 5 u ↔ u ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)) := by
  rw [q18_reaches_iff]
  revert u
  decide

open scoped Classical in
/-- **`Q_a⊕` of `q18` is `qDisj`**: for `{u₁, u₂} = {a, b}`, `disjointNet (q18 a b c) 5 6 7 u₁ u₂` is
`qDisj u₁ u₂ c`. -/
def disjointNetQ18Iso (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {u₁ u₂ : X}
    (hu : u₁ = a ∧ u₂ = b ∨ u₁ = b ∧ u₂ = a) :
    RootedNetworkIso (disjointNet (q18 a b c) 5 6 7 u₁ u₂) (qDisj u₁ u₂ c) where
  vert := Equiv.ofBijective (Sum.elim (fun u => q18DisjVert u.1) qDisjNewLeaf) (by
    have hR := q18_not_reaches_five_iff (a := a) (b := b) (c := c)
    constructor
    · rintro (⟨u, hu⟩ | j) (⟨u', hu'⟩ | j') huu
      · rw [hR] at hu hu'
        have key : ∀ p ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)), ∀ q ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)),
            q18DisjVert p = q18DisjVert q → p = q := by decide
        exact congrArg Sum.inl (Subtype.ext (key u hu u' hu' huu))
      · rw [hR] at hu
        have key : ∀ p ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)), ∀ j, q18DisjVert p ≠ qDisjNewLeaf j := by
          decide
        exact absurd huu (key u hu j')
      · rw [hR] at hu'
        have key : ∀ p ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)), ∀ j, q18DisjVert p ≠ qDisjNewLeaf j := by
          decide
        exact absurd huu.symm (key u' hu' j)
      · have key : ∀ j j', qDisjNewLeaf j = qDisjNewLeaf j' → j = j' := by decide
        exact congrArg Sum.inr (key j j' huu)
    · intro i
      have h2 : ¬ (q18 a b c).graph.Reaches 5 2 := (hR 2).2 (by decide)
      have h3 : ¬ (q18 a b c).graph.Reaches 5 3 := (hR 3).2 (by decide)
      have h6 : ¬ (q18 a b c).graph.Reaches 5 6 := (hR 6).2 (by decide)
      have h7 : ¬ (q18 a b c).graph.Reaches 5 7 := (hR 7).2 (by decide)
      have h8 : ¬ (q18 a b c).graph.Reaches 5 8 := (hR 8).2 (by decide)
      fin_cases i
      exacts [⟨.inl ⟨2, h2⟩, rfl⟩, ⟨.inl ⟨3, h3⟩, rfl⟩, ⟨.inl ⟨6, h6⟩, rfl⟩, ⟨.inl ⟨7, h7⟩, rfl⟩,
        ⟨.inl ⟨8, h8⟩, rfl⟩, ⟨.inr 0, rfl⟩, ⟨.inr 1, rfl⟩])
  arc := Equiv.ofBijective (fun e => q18DisjArc e.1) (by
    have hR := q18_not_reaches_five_iff (a := a) (b := b) (c := c)
    constructor
    · rintro ⟨e, he⟩ ⟨e', he'⟩ hee
      change ¬ (q18 a b c).graph.Reaches 5 (q18Src e) at he
      change ¬ (q18 a b c).graph.Reaches 5 (q18Src e') at he'
      rw [hR] at he he'
      have key : ∀ p q : Fin 9, q18Src p ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)) →
          q18Src q ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)) → q18DisjArc p = q18DisjArc q → p = q := by
        decide
      exact Subtype.ext (key e e' he he' hee)
    · intro i
      have hs : ∀ e : Fin 9, q18Src e ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)) →
          ¬ (q18 a b c).graph.Reaches 5 ((q18 a b c).graph.source e) := fun e he => (hR _).2 he
      fin_cases i
      exacts [⟨⟨2, hs 2 (by decide)⟩, rfl⟩, ⟨⟨3, hs 3 (by decide)⟩, rfl⟩, ⟨⟨5, hs 5 (by decide)⟩, rfl⟩,
        ⟨⟨6, hs 6 (by decide)⟩, rfl⟩, ⟨⟨7, hs 7 (by decide)⟩, rfl⟩, ⟨⟨8, hs 8 (by decide)⟩, rfl⟩])
  source e := by
    obtain ⟨e, he⟩ := e
    show qDisjSrc (q18DisjArc e) = q18DisjVert (q18Src e)
    have hR := q18_not_reaches_five_iff (a := a) (b := b) (c := c)
    change ¬ (q18 a b c).graph.Reaches 5 (q18Src e) at he
    rw [hR] at he
    revert e
    decide
  target e := by
    obtain ⟨e, he⟩ := e
    have hR := q18_not_reaches_five_iff (a := a) (b := b) (c := c)
    have he' : q18Src e ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)) := (hR _).1 he
    show qDisjTgt (q18DisjArc e) = Sum.elim (fun u : {u // ¬ (q18 a b c).graph.Reaches 5 u} =>
        q18DisjVert u.1) qDisjNewLeaf ((disjointNet (q18 a b c) 5 6 7 u₁ u₂).graph.target ⟨e, he⟩)
    dsimp only [disjointNet]
    split_ifs with h6 h7 hr
    · subst h6; rfl
    · subst h7; rfl
    · exfalso
      have hr' : q18Tgt e ∉ ({2, 3, 6, 7, 8} : Finset (Fin 9)) := fun hm => (hR _).2 hm hr
      clear hr he
      revert e
      decide
    · show qDisjTgt (q18DisjArc e) = q18DisjVert (q18Tgt e)
      clear hr he
      revert e
      decide
  root := by
    have h8 : ¬ (q18 a b c).graph.Reaches 5 8 := (q18_not_reaches_five_iff 8).2 (by decide)
    show (4 : Fin 7) = Sum.elim (fun u : {u // ¬ (q18 a b c).graph.Reaches 5 u} =>
        q18DisjVert u.1) qDisjNewLeaf
      (if hr : (q18 a b c).graph.Reaches 5 8 then .inr 0 else .inl ⟨8, hr⟩)
    simp only [h8, dite_false, Sum.elim_inl]
    rfl
  leaf x := by
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
    have hR := q18_not_reaches_five_iff (a := a) (b := b) (c := c)
    show (if x = u₁ then 5 else if x = u₂ then 6 else if x = c then 0 else 1 : Fin 7) =
      Sum.elim (fun u : {u // ¬ (q18 a b c).graph.Reaches 5 u} => q18DisjVert u.1) qDisjNewLeaf
        ((disjointNet (q18 a b c) 5 6 7 u₁ u₂).leaf x)
    dsimp only [disjointNet]
    have h21 : u₂ ≠ u₁ := by rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    by_cases h₁ : x = u₁
    · subst h₁
      simp only [ite_true]
      rfl
    by_cases h₂ : x = u₂
    · subst h₂
      simp only [h₁, ite_true, ite_false]
      rfl
    simp only [h₁, h₂, ite_false]
    have hxab : x ≠ a ∧ x ≠ b := by
      rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by tauto, by tauto⟩
    rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl
    · exact absurd rfl hxab.1
    · exact absurd rfl hxab.2
    · have hl : (q18 a b x).leaf x = 2 := by rw [q18_leaf_eq, quartetLeaf9_c h]
      have hn : ¬ (q18 a b x).graph.Reaches 5 2 := (hR 2).2 (by decide)
      simp only [hl, hn, dite_false, ite_true, Sum.elim_inl]
      rfl
    · have hl : (q18 a b c).leaf x = 3 := by rw [q18_leaf_eq, quartetLeaf9_d h]
      have hn : ¬ (q18 a b c).graph.Reaches 5 3 := (hR 3).2 (by decide)
      simp only [hl, hn, dite_false, Ne.symm hcd, ite_false, Sum.elim_inl]
      rfl

open scoped Classical in
/-- **The concordance factors of `Q_a⊕` and `Q_b⊕` of `q18`** are those of `qDisj`. -/
theorem cf_disjointNet_q18 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {u₁ u₂ : X}
    (hu : u₁ = a ∧ u₂ = b ∨ u₁ = b ∧ u₂ = a) {len : Fin 8 → ℝ} (γ : ℝ) :
    cf (disjointNet (q18 a b c) 5 6 7 u₁ u₂) (disjointMetric (q18 a b c) 5 6 7 (q18Metric len γ)) =
      cf (qDisj u₁ u₂ c) (qDisjMetric len) := by
  have hd : Distinct4 u₁ u₂ c d := by
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
    rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hab, hac, had, hbc, hbd, hcd⟩
    · exact ⟨Ne.symm hab, hbc, hbd, hac, had, hcd⟩
  have hR := q18_not_reaches_five_iff (a := a) (b := b) (c := c)
  refine (disjointNetQ18Iso hX h hu).cf_eq_of_isPhylogenetic (qDisj_isPhylogenetic hX hd)
    (fun e => ?_) (fun e => ?_)
  · obtain ⟨e, he⟩ := e
    have he' : q18Src e ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)) := (hR _).1 he
    show (qDisjMetric len).length (q18DisjArc e) = (q18Metric len γ).length e
    clear he
    fin_cases e <;> first | exact absurd he' (by decide) | rfl
  · obtain ⟨e, he⟩ := e
    have he' : q18Src e ∈ ({2, 3, 6, 7, 8} : Finset (Fin 9)) := (hR _).1 he
    show (1 : ℝ) = (disjointMetric (q18 a b c) 5 6 7 (q18Metric len γ)).inheritance ⟨e, he⟩
    simp only [disjointMetric]
    split_ifs with h67
    · rfl
    · clear he
      fin_cases e <;> first | exact absurd he' (by decide) | simp_all [q18Metric]

/-! ### The lineages of `a` and `b` at the hybrid node -/

omit [Fintype X] in
/-- The node `4` above `a` and `b` is a cut vertex of `q18`. -/
theorem q18_isCut_four : IsCut (q18 a b c) 4 := by
  refine ⟨by rw [q18_reaches_iff]; show (8 : Fin 9) ∉ q18Desc 4; decide, fun e he hne => ?_⟩
  rw [q18_reaches_iff] at he ⊢
  change q18Tgt e ∈ q18Desc 4 at he
  change q18Tgt e ≠ 4 at hne
  show q18Src e ∈ q18Desc 4
  revert e
  decide

omit [Fintype X] in
/-- The nodes of `q18` below `4` are not on its cycle. -/
theorem q18_notMem_cycleNodes {w : Fin 9} (hw : (q18 a b c).graph.Reaches 4 w) :
    w ∉ cycleNodes (q18 a b c).graph ↑q18Cycle := by
  rw [q18_reaches_iff] at hw
  rintro ⟨f, hf, hfw⟩
  have key : ∀ f ∈ q18Cycle, ∀ w ∈ q18Desc 4, q18Src f ≠ w ∧ q18Tgt f ≠ w := by decide
  rcases hfw with h' | h'
  · exact (key f hf w hw).1 h'
  · exact (key f hf w hw).2 h'

/-- The taxa below `4` are `a` and `b`. -/
theorem q18_reaches_four_leaf_iff (hX : Fintype.card X = 4) (h : Distinct4 a b c d) (x : X) :
    (q18 a b c).graph.Reaches 4 ((q18 a b c).leaf x) ↔ x = a ∨ x = b := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := id h
  rw [q18_reaches_iff, q18_leaf_eq]
  rcases eq_or_of_distinct4_of_card_eq hX h x with rfl | rfl | rfl | rfl
  · rw [quartetLeaf9_a]; simp [q18Desc]
  · rw [quartetLeaf9_b h]; simp [q18Desc]
  · rw [quartetLeaf9_c h]; simp [q18Desc, Ne.symm hac, Ne.symm hbc]
  · rw [quartetLeaf9_d h]; simp [q18Desc, Ne.symm had, Ne.symm hbd]

/-- **`P(K = 1) = 1 - x₁` and `P(K = 2) = x₁`** for the lineages of `a` and `b` at the top of the edge
`5 → 4` of `q18`, of length `t₁`. -/
theorem probLineages_q18 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    probLineages (q18 a b c) (q18Metric len γ) 4 1 = 1 - Real.exp (-len 4) ∧
      probLineages (q18 a b c) (q18Metric len γ) 4 2 = Real.exp (-len 4) := by
  have hQ := isLSAQuartet_q18 hX h hlen hγ₀ hγ₁
  have hr : ∀ x, (q18 a b c).leaf x ≠ 4 := fun x hx => by
    have := quartetLeaf9_mem (a := a) (b := b) (c := c) x
    rw [← q18_leaf_eq, hx] at this
    exact absurd this (by decide)
  have harcs : ∀ e, (q18 a b c).graph.source e = 4 →
      (q18 a b c).graph.target e = (q18 a b c).leaf a ∨
        (q18 a b c).graph.target e = (q18 a b c).leaf b := by
    intro e he
    rw [q18_leaf_eq, quartetLeaf9_a, quartetLeaf9_b h]
    change q18Src e = 4 at he
    show q18Tgt e = 0 ∨ q18Tgt e = 1
    revert e
    decide
  have huniq : ∀ g, (q18 a b c).graph.target g = 4 → g = 4 := by
    intro g hg
    change q18Tgt g = 4 at hg
    revert g
    decide
  exact ⟨probLineages_cherry_one hQ.binary.1 q18_isCut_four hQ.metric.1 rfl huniq h.1
      (q18_reaches_four_leaf_iff hX h) hr harcs,
    probLineages_cherry_two hQ.binary.1 q18_isCut_four hQ.metric.1 rfl huniq h.1
      (q18_reaches_four_leaf_iff hX h) hr harcs⟩

open scoped Classical in
/-- **`CF(Q₀⊕ | K = 1) = (1, 0, 0)`**: in the network `Q₀⊕` of `q18`, its cycle contracted, given one
lineage at the top of the edge `5 → 4`, the cherry `{a, b}` decides the quartet tree. -/
theorem condCF_contract_q18 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (c₀ : {e // ∀ C', IsCycle (q18 a b c).graph C' → C' = ↑q18Cycle → e ∉ C'}) (hc₀ : c₀.1 = 4)
    (q : QuartetTree X) :
    condCF (contractRooted (q18 a b c) (· = ↑q18Cycle))
        (contractMetric (q18 a b c) (· = ↑q18Cycle) (q18Metric len γ)) c₀ 1 q =
      if ({a, b} : Finset X) ∈ q.val then 1 else 0 := by
  have hQ := isLSAQuartet_q18 hX h hlen hγ₀ hγ₁
  have hC := q18_isCycle (a := a) (b := b) (c := c)
  have hT := inducesCycleType_q18 hX h
  obtain ⟨t, hK⟩ := isContractible_of_cycle hQ.binary hQ.levelOne hC hT.2.1 hT.2.2.1
  have hS : ∀ w, (q18 a b c).graph.Reaches 4 w → w ∉ cycleNodes (q18 a b c).graph ↑q18Cycle :=
    fun w hw => q18_notMem_cycleNodes hw
  have h4 : (4 : Fin 9) ∉ cycleNodes (q18 a b c).graph ↑q18Cycle := hS 4 .refl
  set Q₀ := contractRooted (q18 a b c) (· = ↑q18Cycle)
  have hr : ∀ x, Q₀.leaf x ≠ Quot.mk _ 4 := fun x hx => by
    have hx' := (mk_eq_mk_iff_of_notMem' hC h4).1 hx
    have := quartetLeaf9_mem (a := a) (b := b) (c := c) x
    rw [← q18_leaf_eq, hx'] at this
    exact absurd this (by decide)
  have hbelow : ∀ x, Q₀.graph.Reaches (Quot.mk _ 4) (Q₀.leaf x) ↔ x = a ∨ x = b := fun x =>
    (reaches_contract_iff hC hS _).trans (q18_reaches_four_leaf_iff hX h x)
  have huniq : ∀ g, Q₀.graph.target g = Quot.mk _ 4 → g = c₀ := by
    intro g hg
    have hg' : q18Tgt g.1 = 4 := (mk_eq_mk_iff_of_notMem' hC h4).1 hg
    refine Subtype.ext (hc₀ ▸ ?_)
    revert hg'
    generalize g.1 = e
    revert e
    decide
  have harcs : ∀ e, Q₀.graph.source e = Quot.mk _ 4 →
      Q₀.graph.target e = Q₀.leaf a ∨ Q₀.graph.target e = Q₀.leaf b := by
    intro e he
    have he' : q18Src e.1 = 4 := (mk_eq_mk_iff_of_notMem' hC h4).1 he
    have key : ∀ f : Fin 9, q18Src f = 4 → q18Tgt f = 0 ∨ q18Tgt f = 1 := by decide
    have hla : (q18 a b c).leaf a = 0 := by rw [q18_leaf_eq, quartetLeaf9_a]
    have hlb : (q18 a b c).leaf b = 1 := by rw [q18_leaf_eq, quartetLeaf9_b h]
    rcases key e.1 he' with h' | h'
    · left
      show Quot.mk _ (q18Tgt e.1) = Quot.mk _ ((q18 a b c).leaf a)
      rw [h', hla]
    · right
      show Quot.mk _ (q18Tgt e.1) = Quot.mk _ ((q18 a b c).leaf b)
      rw [h', hlb]
  have hcr : Q₀.graph.target c₀ = Quot.mk _ 4 := by
    show Quot.mk _ (q18Tgt c₀.1) = Quot.mk _ 4
    rw [hc₀]
    rfl
  have e := condCF_cherry_one (hK.isPhylogenetic hQ.binary.1) (isCut_contract hC q18_isCut_four hS)
    (hK.isMetric hQ.metric.1) hX hcr huniq h.1 hbelow hr harcs q
  rw [e]
  congr 2
  exact congrArg (fun i => @insert X (Finset X) (@instInsert X i) a {b}) (Subsingleton.elim _ _)

end Trees

end Banos2019
