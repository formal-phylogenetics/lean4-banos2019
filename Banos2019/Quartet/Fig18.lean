module

public import Banos2019.Quartet.Normal

/-!
# Figure 18 as an LSA quartet network (Proposition 7)

The `3₂`-cycle of Figure 18 is the unrooted network of the LSA quartet network `q18 a b c`: the nodes
`0, 1, 2, 3` are the leaves `a, b, c, d`; `4` is the parent of `a` and `b`, `5` the hybrid node above
`4`, `6` the node of `c`, `7` that of `d`, and the root `8` has the hybrid edge `8 → 5` and the tree
edge `8 → 7`, which the unrooted network merges into the hybrid edge `7 → 5` of Figure 18.

* `isLSAQuartet_q18`, `inducesNetwork_q18`, `exists_inducesCycleType_q18`: `q18 a b c` with the
  parameters `q18Metric len γ` is an LSA quartet network with a `3₂`-cycle, whose metric unrooted
  network is Figure 18 with the parameters `figMetric len γ`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace Banos2019

/-- The tails of the edges of `q18`. -/
def q18Src : Fin 9 → Fin 9 := ![4, 4, 6, 7, 5, 7, 8, 6, 8]

/-- The heads of the edges of `q18`. -/
def q18Tgt : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 6, 5, 5, 7]

variable {X : Type*} [DecidableEq X]

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

theorem exists_inducesCycleType_q18 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) :
    ∃ C v, InducesCycleType (q18 a b c) C v 3 2 := by
  have hcyc : IsCycle (q18 a b c).graph ↑q18Cycle := by
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
  have hla : (q18 a b c).leaf a = 0 := by simp [q18, figLeaf_a]
  have hlb : (q18 a b c).leaf b = 1 := by simp [q18, figLeaf_b h]
  have hlc : (q18 a b c).leaf c = 2 := by simp [q18, figLeaf_c h]
  have hld : (q18 a b c).leaf d = 3 := by simp [q18, figLeaf_d h]
  refine ⟨↑q18Cycle, 5, hcyc, ⟨6, by decide, Or.inr rfl⟩, by rw [q18_indegree]; decide, ?_, ?_⟩
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

/-! ### The unrooted network is Figure 18 -/

theorem isLSAQuartet_q18 (hX : Fintype.card X = 4) (h : Distinct4 a b c d) {len : Fin 8 → ℝ}
    (hlen : ∀ i, 0 < len i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    IsLSAQuartet (q18 a b c) (q18Metric len γ) :=
  ⟨q18_isBinaryRootedNetwork hX h, q18_isLevelOne, q18_isLSANetwork h, hX,
    q18Metric_isMetricNetwork hlen hγ₀ hγ₁⟩

/-- **The metric unrooted network of `q18` is Figure 18.** -/
theorem inducesNetwork_q18 (h : Distinct4 a b c d) {len : Fin 8 → ℝ} {γ : ℝ}
    (hQ : IsLSAQuartet (q18 a b c) (q18Metric len γ)) :
    InducesNetwork hQ (fig18 a b c) (figMetric len γ) := by
  have hP := hQ.binary.1
  have hB := hQ.binary.2
  have hXn := hQ.nontrivial
  have hl : lsa hP Set.univ Set.univ_nonempty = 8 :=
    IsLeastStableAncestor.unique hP (lsa_spec hP _ _) (q18_isLSANetwork h)
  have hr : (rootTreeArc hP hB hXn).1 = 8 := by
    obtain ⟨hs, ht⟩ := rootTreeArc_spec hP hB hXn
    have hs' : q18Src (rootTreeArc hP hB hXn).1 = 8 := by
      rw [← hl]
      exact congrArg Subtype.val hs
    have ht' : (q18 a b c).IsTreeArc (rootTreeArc hP hB hXn).1 :=
      (belowNetwork_isTreeArc_iff (hl := lsa_mem_ancestralVertices hP Set.univ_nonempty)
        (hleaf := fun _ hx => (lsa_spec hP Set.univ Set.univ_nonempty).1.reaches_leaf hP hx)
        hP (lsa_spec hP _ _).1 _).1 ht
    rw [q18_isTreeArc_iff] at ht'
    have key : ∀ r : Fin 9, q18Src r = 8 → ¬ (r = 6 ∨ r = 7) → r = 8 := by decide
    exact key _ hs' ht'
  -- the nodes and the edges of `Q⁻`: those of `q18` but the root and the edge `8`
  have hv : ∀ v : SemidirectedVertex hP hXn, v.1.1 ≠ Fin.last 8 := fun v hv => v.2 (Subtype.ext
    (show v.1.1 = lsa hP Set.univ Set.univ_nonempty by rw [hv]; exact hl.symm))
  have he : ∀ e : SemidirectedArc hP hB hXn, e.1.1 ≠ Fin.last 8 := fun e he =>
    e.2 (Subtype.ext (by rw [he]; exact hr.symm))
  let vert : SemidirectedVertex hP hXn ≃ Fin 8 :=
    { toFun := fun v => v.1.1.castPred (hv v)
      invFun := fun i => ⟨⟨i.castSucc, hl ▸ hP.root_reaches _, mem_ancestralVertices_univ hP _⟩,
        fun hi => Fin.castSucc_ne_last i (by
          have := congrArg (fun v => v.1) hi
          simp only at this
          rw [this]
          exact hl)⟩
      left_inv := fun v => Subtype.ext (Subtype.ext (Fin.castSucc_castPred _ _))
      right_inv := fun i => by simp }
  let edge : SemidirectedArc hP hB hXn ≃ Fin 8 :=
    { toFun := fun e => e.1.1.castPred (he e)
      invFun := fun i => ⟨⟨i.castSucc, hl ▸ hP.root_reaches _, mem_ancestralVertices_univ hP _⟩,
        fun hi => Fin.castSucc_ne_last i (by
          have := congrArg (fun e => e.1) hi
          simp only at this
          rw [this]
          exact hr)⟩
      left_inv := fun e => Subtype.ext (Subtype.ext (Fin.castSucc_castPred _ _))
      right_inv := fun i => by simp }
  have hvert : ∀ v, (vert v).castSucc = v.1.1 := fun v => Fin.castSucc_castPred _ (hv v)
  have hedge : ∀ e, (edge e).castSucc = e.1.1 := fun e => Fin.castSucc_castPred _ (he e)
  -- the ends of the edges of `Q⁻`: the edge `6` from the root is merged into one from `7`
  have hroot : ∀ e : SemidirectedArc hP hB hXn,
      (lsaPlus hP hXn).graph.source e.1 = (lsaPlus hP hXn).root ↔ q18Src e.1.1 = 8 := by
    intro e
    rw [← hl]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hsrc : ∀ e, (hQ.unrooted.graph.source e).1.1 = if q18Src e.1.1 = 8 then 7 else q18Src e.1.1 := by
    intro e
    show ((unrootAt (lsaPlus hP hXn) (lsaPlus_isPhylogenetic hP hXn)
      (rootTreeArc hP hB hXn)).graph.source e).1.1 = _
    simp only [unrootAt]
    by_cases h8 : q18Src e.1.1 = 8
    · rw [dite_eq_left ((hroot e).2 h8), ite_eq_left h8]
      show q18Tgt (rootTreeArc hP hB hXn).1 = 7
      rw [hr]
      rfl
    · rw [dite_eq_right (fun h' => h8 ((hroot e).1 h')), ite_eq_right h8]
      rfl
  have htgt : ∀ e, (hQ.unrooted.graph.target e).1.1 = q18Tgt e.1.1 := fun e => rfl
  have hdir : ∀ e, hQ.unrooted.IsDirected e ↔ e.1.1 = 6 ∨ e.1.1 = 7 := fun e =>
    ((belowNetwork_isHybridArc_iff (hl := lsa_mem_ancestralVertices hP Set.univ_nonempty)
      (hleaf := fun _ hx => (lsa_spec hP Set.univ Set.univ_nonempty).1.reaches_leaf hP hx)
      hP (lsa_spec hP _ _).1 e.1).trans (q18_isHybridArc_iff e.1.1))
  have fsrc : ∀ j : Fin 8, ((fig18 a b c).graph.source j).castSucc =
      if q18Src j.castSucc = 8 then 7 else q18Src j.castSucc := by
    show ∀ j : Fin 8, ((![4, 4, 6, 7, 5, 7, 7, 6] : Fin 8 → Fin 8) j).castSucc =
      if q18Src j.castSucc = 8 then 7 else q18Src j.castSucc
    decide
  have ftgt : ∀ j : Fin 8, ((fig18 a b c).graph.target j).castSucc = q18Tgt j.castSucc := by
    show ∀ j : Fin 8, ((![0, 1, 2, 3, 4, 6, 5, 5] : Fin 8 → Fin 8) j).castSucc = q18Tgt j.castSucc
    decide
  have hjs : ∀ e, (fig18 a b c).graph.source (edge e) = vert (hQ.unrooted.graph.source e) := fun e =>
    Fin.castSucc_injective _ (by rw [hvert, hsrc, fsrc, hedge])
  have hjt : ∀ e, (fig18 a b c).graph.target (edge e) = vert (hQ.unrooted.graph.target e) := fun e =>
    Fin.castSucc_injective _ (by rw [hvert, htgt, ftgt, hedge])
  refine ⟨⟨⟨vert, edge, fun e => ?_, fun e => Or.inl ⟨hjs e, hjt e⟩, fun e _ => ⟨hjs e, hjt e⟩,
    fun x => ?_⟩, fun e => ?_, fun e _ => ?_⟩⟩
  · rw [hdir, ← hedge e]
    show edge e = 6 ∨ edge e = 7 ↔ _
    generalize edge e = j
    revert j
    decide
  · apply Fin.castSucc_injective
    rw [hvert]
    rfl
  · simp only [figMetric, unrootedMetric, semidirectedMetric]
    rw [hr, ← hedge e]
    split_ifs with h8
    · have h8' : q18Src (edge e).castSucc = 8 := by rw [hedge e]; exact (hroot e).1 h8
      have h6 : edge e = 6 := by
        have key : ∀ j : Fin 8, q18Src j.castSucc = 8 → j = 6 := by decide
        exact key _ h8'
      rw [h6]
      simp [q18Metric]
    · have h8' : q18Src (edge e).castSucc ≠ 8 := fun h' => h8 ((hroot e).2 (by rwa [← hedge e]))
      generalize edge e = j at h8'
      fin_cases j <;> first | exact absurd (by decide) h8' | simp [q18Metric]
  · show (figMetric len γ).inheritance (edge e) = (q18Metric len γ).inheritance e.1.1
    rw [← hedge e]
    generalize edge e = j
    fin_cases j <;> simp [figMetric, q18Metric]

end Banos2019
