module

public import Banos2019.Network.Induced

/-!
# The structure of level-1 networks (Baños 2019, Section 3)

* `proposition2`: above `LSA(X)`, a level-1 rooted network is a chain of 2-cycles joined by edges.
* Blocks. Removing the edges of a cycle `C_v` partitions the taxa by the connected components of
  what is left: the *`v`-blocks*. `SameBlock G ℓ D x y`: the taxa `x, y` (at the nodes `ℓ x`, `ℓ y`)
  are joined by a walk avoiding the edges `D`; with `D` the edges of `C_v` these are the `v`-blocks,
  with `D` the edges of a family of cycles the *network blocks* induced by the family. `nodeBlock`
  is the block `B_u` associated with a node `u` of the cycle.
* `lemma4`, `corollary1`: the network partition of a family of cycles is the common refinement of
  their partitions.
* `contractCycles`, `undirectEdges`: contracting cycles (removing their edges and identifying their
  nodes), and forgetting the direction of some hybrid edges, on semidirected networks; they build
  the network `Ñ` of Theorem 4.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

/-- **Proposition 2** (`prop::structureabove`): in a level-1 binary rooted network, the nodes and
edges above `m = LSA(X)` form a (possibly empty) chain of 2-cycles joined by edges: nodes
`t 0 = r, h 0, t 1, h 1, …, t n = m`, where `t i` has exactly two out-edges, both to `h i`, and
`h i` has exactly one out-edge, to `t (i + 1)`; these are all the edges above `m` (Definition 3:
their child is above or equal to `m`).

The proof is the paper's induction, carried out on the top node `u` of the chain (a stable ancestor
of `X` above `m`) in place of the network below it. The two out-edges of `u ≠ m` cannot lead to
distinct children `x`, `y`: neither is `m` (Lemma 1 (i)); they are not both hybrid nodes; and if `x`
has two out-edges `e₁`, `e₂`, there are three paths from `u` to `m`, through `e₁`, `e₂` and `y`. The
paper states that these three paths contradict the level-1 condition (TeX l. 365–369) without saying
how; this gap is filled along the paper's lines. The paths give two cycles through the edge
`(u, x)`, one from the paths through `e₁` and `y`, one from those through `e₂` and `y`
(`exists_isCycle_of_walks`). By the level-1 condition they are one cycle; its other edge at `x` is
`e₁` or `e₂`, which lies on only one of them, as the path through `y` cannot enter the tree node
`x`. So the out-edges of `u` form a 2-cycle at a hybrid node other than `m` (Lemma 1 (i)), whose
child is `m` or a tree node, and the chain continues from that child. -/
theorem proposition2 [Nonempty X] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) :
    ∃ (n : ℕ) (t : Fin (n + 1) → V) (h : Fin n → V),
      t 0 = N.root ∧ t (Fin.last n) = lsa hN.1 Set.univ Set.univ_nonempty ∧
      (∀ i : Fin n, ∀ e, N.graph.source e = t i.castSucc ↔ N.graph.target e = h i) ∧
      (∀ i : Fin n, ∀ e, N.graph.source e = h i →
        N.graph.target e = t i.succ ∧ ∀ f, N.graph.source f = h i → f = e) ∧
      ∀ e, N.graph.Reaches (N.graph.target e) (lsa hN.1 Set.univ Set.univ_nonempty) →
        (∃ i : Fin n, N.graph.source e = t i.castSucc) ∨ ∃ i : Fin n, N.graph.source e = h i := by
  classical
  have : Finite V := hN.1.finite_vertices
  have : Finite E := hN.1.finite_arcs
  set m := lsa hN.1 Set.univ Set.univ_nonempty with hm_def
  obtain ⟨hst, hleast⟩ := lsa_spec hN.1 Set.univ Set.univ_nonempty
  rw [← hm_def] at hst hleast
  have hcyc : ∀ {a b}, N.graph.Reaches a b → N.graph.Adj b a → False := fun h hab =>
    hN.1.acyclic _ (Relation.TransGen.tail' h hab)
  have hloop : ∀ f, N.graph.source f ≠ N.graph.target f := fun f h =>
    hN.1.acyclic _ (.single ⟨f, rfl, h.symm⟩)
  -- Lemma 1 (i): `m` has indegree at most one
  have hm_in : N.graph.indegree m ≤ 1 := (lemma1 hN Set.univ_nonempty subset_rfl).1
  have htwo_in : ∀ {c : V} {g₁ g₂ : E}, g₁ ≠ g₂ → N.graph.target g₁ = c → N.graph.target g₂ = c →
      2 ≤ N.graph.indegree c := fun hne h₁ h₂ => by
    rw [← Set.ncard_pair hne]
    exact Set.ncard_le_ncard (by rintro f (rfl | rfl) <;> assumption) (Set.toFinite _)
  -- a directed path from `c` is a walk on the arcs leaving nodes below `c`
  have hwalkR : ∀ {c d : V}, N.graph.Reaches c d →
      N.graph.Walks {f | N.graph.Reaches c (N.graph.source f)} c d := by
    intro c d h
    induction h with
    | refl => exact .refl
    | @tail s d hcs hsd ih =>
      obtain ⟨f, hfs, hft⟩ := hsd
      exact ih.tail ⟨f, by rw [Set.mem_ofPred_eq, hfs]; exact hcs, Or.inl ⟨hfs, hft⟩⟩
  -- the claim for the part below a stable ancestor `u` above `m`, by induction on `u`
  suffices key : ∀ u, N.IsStableAncestor Set.univ u → (u = m ∨ N.graph.outdegree u = 2) →
      ∃ (n : ℕ) (t : Fin (n + 1) → V) (h : Fin n → V), t 0 = u ∧ t (Fin.last n) = m ∧
        (∀ i : Fin n, ∀ e, N.graph.source e = t i.castSucc ↔ N.graph.target e = h i) ∧
        (∀ i : Fin n, ∀ e, N.graph.source e = h i →
          N.graph.target e = t i.succ ∧ ∀ f, N.graph.source f = h i → f = e) ∧
        ∀ e, N.graph.Reaches u (N.graph.source e) → N.graph.Reaches (N.graph.target e) m →
          (∃ i : Fin n, N.graph.source e = t i.castSucc) ∨ ∃ i : Fin n, N.graph.source e = h i by
    obtain ⟨n, t, h, h0, hl, hb, hc, hd⟩ :=
      key N.root (N.root_isStableAncestor _) (Or.inr hN.2.1)
    exact ⟨n, t, h, h0, hl, hb, hc, fun e he => hd e (hN.1.root_reaches _) he⟩
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hN.1.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  intro u
  induction u using hwf.induction with
  | _ u ih =>
  intro hu hu2
  have hum : N.graph.Reaches u m := hleast u hu
  -- no edge above `m`: `u = m`
  by_cases humeq : u = m
  · refine ⟨0, fun _ => u, Fin.elim0, rfl, humeq, fun i => i.elim0, fun i => i.elim0,
      fun e he he' => absurd ?_ id⟩
    rw [humeq] at he
    exact (hcyc (he'.trans he) ⟨e, rfl, rfl⟩).elim
  have hout : N.graph.outdegree u = 2 := hu2.resolve_left humeq
  obtain ⟨a₁, a₂, hne, hs⟩ := Set.ncard_eq_two.mp hout
  have ha₁ : N.graph.source a₁ = u := by
    have : a₁ ∈ {f | N.graph.source f = u} := by rw [hs]; exact Or.inl rfl
    exact this
  have ha₂ : N.graph.source a₂ = u := by
    have : a₂ ∈ {f | N.graph.source f = u} := by rw [hs]; exact Or.inr rfl
    exact this
  have hout' : ∀ g, N.graph.source g = u → g = a₁ ∨ g = a₂ := fun g hg => by
    have : g ∈ {f | N.graph.source f = u} := hg
    rw [hs] at this
    exact this
  have hadj : ∀ c, N.graph.Adj u c → c = N.graph.target a₁ ∨ c = N.graph.target a₂ := by
    rintro c ⟨g, hg, rfl⟩
    rcases hout' g hg with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- every path from `u` to a taxon passes through `m`
  have hpass : ∀ z, ¬ N.HasPathAvoiding u (N.leaf z) m := fun z hp => by
    have hru : N.HasPathAvoiding N.root u m :=
      hasPathAvoiding_of_not_reaches_reaches (hN.1.root_reaches u) fun h =>
        humeq (eq_of_reaches_of_reaches hN.1.acyclic hum h.2)
    exact hst z trivial (hasPathAvoiding_trans hru hp)
  -- so a node reached from `u` avoiding `m` is above `m`
  have habove : ∀ c, N.HasPathAvoiding u c m → N.graph.Reaches c m := fun c hc => by
    obtain ⟨z, hz⟩ := exists_reaches_leaf hN.1 c
    by_contra hcm
    exact hpass z (hasPathAvoiding_trans hc
      (hasPathAvoiding_of_not_reaches_reaches hz fun h => hcm h.1))
  have hchild : ∀ c, N.graph.Adj u c → N.graph.Reaches c m := fun c hc => by
    by_cases hcm : c = m
    · rw [hcm]
      exact .refl
    · exact habove c ⟨humeq, hcm, .single ⟨hc, humeq, hcm⟩⟩
  -- a child `c'` of `u` above the child `c` of the arc `g₀` gives `c` a second parent
  have hsecond : ∀ (g₀ : E) (c' : V), N.graph.source g₀ = u → N.graph.Adj u c' →
      c' ≠ N.graph.target g₀ → N.graph.Reaches c' (N.graph.target g₀) →
      ∃ g, N.graph.target g = N.graph.target g₀ ∧ g ≠ g₀ := by
    intro g₀ c' hg₀ hc' hne' hreach
    rcases Relation.ReflTransGen.cases_tail hreach with h | ⟨s, hs, g, hgs, hgt⟩
    · exact absurd h.symm hne'
    · refine ⟨g, hgt, fun hgg => ?_⟩
      rw [hgg, hg₀] at hgs
      exact hcyc (hgs ▸ hs) hc'
  have hxu : N.graph.target a₁ ≠ u := fun h => hloop a₁ (ha₁.trans h.symm)
  have hyu : N.graph.target a₂ ≠ u := fun h => hloop a₂ (ha₂.trans h.symm)
  by_cases hxy : N.graph.target a₁ = N.graph.target a₂
  · -- the two edges leaving `u` form a 2-cycle with a hybrid node `x`, whose child is `w`
    set x := N.graph.target a₁ with hx_def
    have hx2 : 2 ≤ N.graph.indegree x := htwo_in hne rfl hxy.symm
    have hxm : x ≠ m := fun h => by rw [h] at hx2; omega
    have hxin : N.graph.indegree x = 2 := le_antisymm (hN.indegree_le_two x) hx2
    have hxr : x ≠ N.root := hN.1.target_ne_root a₁
    have hxout0 : N.graph.outdegree x ≠ 0 := fun h => by
      obtain ⟨z, hz⟩ := (hN.1.leaves x).mp h
      rw [← hz, hN.1.leaf_indegree] at hxin
      exact absurd hxin (by norm_num)
    have := hN.2.2 x hxr hxout0
    obtain ⟨b, hb⟩ := (N.graph.outdegree_eq_one_iff x).mp (by omega)
    set w := N.graph.target b with hw_def
    have hxin' : ∀ g, N.graph.target g = x → g = a₁ ∨ g = a₂ := fun g hg => by
      have := Set.ext_iff.mp (eq_or_eq_of_indegree_eq_two hxin hne rfl hxy.symm) g
      simpa using this.mp hg
    have hleaf_u : ∀ z ∈ (Set.univ : Set X), N.leaf z ≠ u := fun z _ h => by
      have := (hN.1.leaves u).mpr ⟨z, h⟩
      omega
    have hxst : N.IsStableAncestor Set.univ x :=
      isStableAncestor_of_forall_adj hu hleaf_u fun c hc hcx => by
        rcases hadj c hc with rfl | rfl
        · exact absurd rfl hcx
        · exact absurd hxy.symm hcx
    have hleaf_x : ∀ z ∈ (Set.univ : Set X), N.leaf z ≠ x := fun z _ h => by
      rw [← h, hN.1.leaf_indegree] at hxin
      exact absurd hxin (by norm_num)
    have hwst : N.IsStableAncestor Set.univ w :=
      isStableAncestor_of_forall_adj hxst hleaf_x fun c ⟨g, hgs, hgt⟩ hcw => by
        rw [(hb g).mp hgs] at hgt
        exact absurd hgt.symm hcw
    -- `w` is `m` or a tree node
    have hw2 : w = m ∨ N.graph.outdegree w = 2 := by
      by_cases hwm : w = m
      · exact Or.inl hwm
      right
      have hwin : ∀ g, N.graph.target g = w → g = b := fun g hg => by
        by_contra hgb
        obtain ⟨z, hz⟩ := exists_reaches_leaf hN.1 w
        have hxp : N.graph.Reaches x (N.graph.source g) :=
          IsStableAncestor.reaches_source hN.1 hxst (Set.mem_univ z) (by rw [hg]; exact hz)
            fun h => hcyc h (by rw [hg]; exact ⟨b, (hb b).mpr rfl, rfl⟩)
        rcases Relation.ReflTransGen.cases_head hxp with h | ⟨c, ⟨g', hg's, rfl⟩, hcp⟩
        · exact hgb ((hb g).mp h.symm)
        · rw [(hb g').mp hg's] at hcp
          exact hcyc hcp ⟨g, rfl, hg⟩
      have hwin1 : N.graph.indegree w = 1 :=
        (N.graph.indegree_eq_one_iff w).mpr ⟨b, fun g => ⟨hwin g, fun h => h ▸ rfl⟩⟩
      have hwr : w ≠ N.root := hN.1.target_ne_root b
      have hwout0 : N.graph.outdegree w ≠ 0 := fun h => hwm
        (N.graph.eq_of_reaches_of_outdegree_eq_zero (hleast w hwst) h).symm
      have := hN.2.2 w hwr hwout0
      omega
    have hrw : r w u := (Relation.TransGen.single ⟨a₁, ha₁, rfl⟩).tail ⟨b, (hb b).mpr rfl, rfl⟩
    obtain ⟨n, t, h, h0, hl, hbt, hct, hdt⟩ := ih w hrw hwst hw2
    refine ⟨n + 1, Fin.cons u t, Fin.cons x h, Fin.cons_zero .., ?_, fun i e => ?_, fun i e => ?_,
      fun e he he' => ?_⟩
    · rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl, Fin.cons_succ, hl]
    · induction i using Fin.cases with
      | zero =>
        rw [show (0 : Fin (n + 1)).castSucc = 0 from rfl, Fin.cons_zero, Fin.cons_zero]
        constructor
        · intro he
          rcases hout' e he with rfl | rfl
          · rfl
          · exact hxy.symm
        · intro he
          rcases hxin' e he with rfl | rfl
          · exact ha₁
          · exact ha₂
      | succ j =>
        rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hbt j e
    · induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        intro he
        rw [h0, (hb e).mp he]
        exact ⟨rfl, fun f hf => (hb f).mp hf⟩
      | succ j =>
        rw [Fin.cons_succ, Fin.cons_succ]
        exact hct j e
    · rcases Relation.ReflTransGen.cases_head he with hue | ⟨c, hc, hcs⟩
      · exact Or.inl ⟨0, by rw [show (0 : Fin (n + 1)).castSucc = 0 from rfl, Fin.cons_zero, hue]⟩
      rcases hadj c hc with rfl | rfl
      · rcases Relation.ReflTransGen.cases_head hcs with hxe | ⟨c', ⟨g, hgs, rfl⟩, hc's⟩
        · exact Or.inr ⟨0, by rw [Fin.cons_zero, hxe]⟩
        · rw [(hb g).mp hgs] at hc's
          rcases hdt e hc's he' with ⟨i, hi⟩ | ⟨i, hi⟩
          · exact Or.inl ⟨i.succ, by rw [← Fin.succ_castSucc, Fin.cons_succ, hi]⟩
          · exact Or.inr ⟨i.succ, by rw [Fin.cons_succ, hi]⟩
      · rcases Relation.ReflTransGen.cases_head hcs with hxe | ⟨c', ⟨g, hgs, rfl⟩, hc's⟩
        · exact Or.inr ⟨0, by rw [Fin.cons_zero, ← hxe, ← hxy]⟩
        · rw [(hb g).mp (hgs.trans hxy.symm)] at hc's
          rcases hdt e hc's he' with ⟨i, hi⟩ | ⟨i, hi⟩
          · exact Or.inl ⟨i.succ, by rw [← Fin.succ_castSucc, Fin.cons_succ, hi]⟩
          · exact Or.inr ⟨i.succ, by rw [Fin.cons_succ, hi]⟩
  · -- distinct children `x`, `y` of `u`: impossible
    exfalso
    -- neither child is `m` (Lemma 1 (i)): the other child is above it
    have hnotm : ∀ g₀ g₁ : E, N.graph.source g₀ = u → N.graph.source g₁ = u →
        N.graph.target g₀ ≠ N.graph.target g₁ → N.graph.target g₀ ≠ m := by
      intro g₀ g₁ hg₀ hg₁ hne' hm'
      have hy' : N.graph.Reaches (N.graph.target g₁) (N.graph.target g₀) :=
        hm' ▸ hchild _ ⟨g₁, hg₁, rfl⟩
      obtain ⟨g, hgt, hgne⟩ := hsecond g₀ _ hg₀ ⟨g₁, hg₁, rfl⟩ hne'.symm hy'
      have := htwo_in hgne hgt rfl
      rw [hm'] at this
      omega
    have hxm := hnotm a₁ a₂ ha₁ ha₂ hxy
    have hym := hnotm a₂ a₁ ha₂ ha₁ (Ne.symm hxy)
    -- each child is a tree node or a hybrid node
    have hdeg : ∀ g₀, N.graph.source g₀ = u → N.graph.target g₀ ≠ m →
        N.graph.indegree (N.graph.target g₀) + N.graph.outdegree (N.graph.target g₀) = 3 ∧
          1 ≤ N.graph.indegree (N.graph.target g₀) := by
      intro g₀ hg₀ hm'
      have hr := hN.1.target_ne_root g₀
      have h0 : N.graph.outdegree (N.graph.target g₀) ≠ 0 := fun h => hm'
        (N.graph.eq_of_reaches_of_outdegree_eq_zero (hchild _ ⟨g₀, hg₀, rfl⟩) h).symm
      exact ⟨hN.2.2 _ hr h0, hN.1.nonroot_indegree _ hr⟩
    -- a hybrid child has its other parent below the other child
    have hhyb : ∀ g₀ g₁ : E, N.graph.source g₀ = u → N.graph.source g₁ = u →
        (∀ g, N.graph.source g = u → g = g₀ ∨ g = g₁) → N.graph.target g₀ ≠ N.graph.target g₁ →
        N.graph.indegree (N.graph.target g₀) = 2 →
        N.graph.Reaches (N.graph.target g₁) (N.graph.target g₀) := by
      intro g₀ g₁ hg₀ hg₁ hg01 hne' h2
      obtain ⟨g, hgt, hgne⟩ := Set.exists_ne_of_one_lt_ncard
        (s := {g | N.graph.target g = N.graph.target g₀})
        (by unfold DirectedMultigraph.indegree at h2; omega) g₀
      have hgt : N.graph.target g = N.graph.target g₀ := hgt
      have hpu : N.graph.source g ≠ u := fun h => by
        rcases hg01 g h with rfl | rfl
        · exact hgne rfl
        · exact hne' hgt.symm
      obtain ⟨z, hz⟩ := exists_reaches_leaf hN.1 (N.graph.target g₀)
      have hup : N.graph.Reaches u (N.graph.source g) :=
        IsStableAncestor.reaches_source hN.1 hu (Set.mem_univ z) (by rw [hgt]; exact hz)
          fun h => hcyc (hgt ▸ h) ⟨g₀, hg₀, rfl⟩
      rcases Relation.ReflTransGen.cases_head hup with h | ⟨c, ⟨g', hg's, rfl⟩, hcp⟩
      · exact absurd h.symm hpu
      · rcases hg01 g' hg's with rfl | rfl
        · exact (hcyc hcp ⟨g, rfl, hgt⟩).elim
        · exact hcp.tail ⟨g, rfl, hgt⟩
    -- three paths from `u` to `m`, two through a tree child `x`, close two cycles through the
    -- edge from `u` to `x`; they are the same cycle, which cannot leave `x`
    have key : ∀ g₀ g₁ : E, N.graph.source g₀ = u → N.graph.source g₁ = u → g₀ ≠ g₁ →
        N.graph.target g₀ ≠ N.graph.target g₁ → N.graph.target g₀ ≠ m →
        N.graph.outdegree (N.graph.target g₀) = 2 → False := by
      intro g₀ g₁ hg₀ hg₁ hne₀₁ hne' hm₀ hout₀
      set x := N.graph.target g₀ with hx_def
      set y := N.graph.target g₁ with hy_def
      have hux : x ≠ u := fun h => hloop g₀ (hg₀.trans h.symm)
      have hx1 : N.graph.indegree x = 1 := by
        have h3 := hdeg g₀ hg₀ hm₀
        rw [← hx_def] at h3
        omega
      have hin1 : ∀ g, N.graph.target g = x → g = g₀ := fun g hg => by
        obtain ⟨g', hg'⟩ := (N.graph.indegree_eq_one_iff x).mp hx1
        exact ((hg' g).mp hg).trans ((hg' g₀).mp rfl).symm
      have hyx : ¬ N.graph.Reaches y x := fun h => by
        obtain ⟨g, hgt, hgne⟩ := hsecond g₀ y hg₀ ⟨g₁, hg₁, rfl⟩ (Ne.symm hne') h
        exact hgne (hin1 g hgt)
      obtain ⟨e₁, e₂, hne₁₂, hse⟩ := Set.ncard_eq_two.mp hout₀
      have he₁ : N.graph.source e₁ = x := by
        have : e₁ ∈ {f | N.graph.source f = x} := by rw [hse]; exact Or.inl rfl
        exact this
      have he₂ : N.graph.source e₂ = x := by
        have : e₂ ∈ {f | N.graph.source f = x} := by rw [hse]; exact Or.inr rfl
        exact this
      have hxout : ∀ g, N.graph.source g = x → g = e₁ ∨ g = e₂ := fun g hg => by
        have : g ∈ {f | N.graph.source f = x} := hg
        rw [hse] at this
        exact this
      have hym : N.graph.Reaches y m := hchild y ⟨g₁, hg₁, rfl⟩
      -- the paths `u, x, xᵢ, …, m, …, y, u`, as walks avoiding the edge from `u` to `x`
      have hcycle : ∀ eᵢ, N.graph.source eᵢ = x → ∃ C, IsCycle N.graph C ∧ g₀ ∈ C ∧
          C ⊆ insert g₀ {f | f = eᵢ ∨ f = g₁ ∨
            N.graph.Reaches (N.graph.target eᵢ) (N.graph.source f) ∨
              N.graph.Reaches y (N.graph.source f)} := by
        intro eᵢ heᵢ
        have hxim : N.graph.Reaches (N.graph.target eᵢ) m := by
          by_cases him : N.graph.target eᵢ = m
          · rw [him]
            exact .refl
          · exact habove _ ⟨humeq, him,
              (Relation.ReflTransGen.single ⟨⟨g₀, hg₀, rfl⟩, humeq, hm₀⟩).tail
                ⟨⟨eᵢ, heᵢ, rfl⟩, hm₀, him⟩⟩
        refine exists_isCycle_of_walks ?_ ?_
        · rintro (h | h | h | h)
          · exact hux (by rw [← heᵢ, ← h, hg₀])
          · exact hne₀₁ h
          · rw [hg₀] at h
            exact hcyc (h.head ⟨eᵢ, heᵢ, rfl⟩) ⟨g₀, hg₀, rfl⟩
          · rw [hg₀] at h
            exact hcyc h ⟨g₁, hg₁, rfl⟩
        · rw [hg₀]
          refine Relation.ReflTransGen.head ⟨eᵢ, Or.inl rfl, Or.inl ⟨heᵢ, rfl⟩⟩ ?_
          refine (walks_mono (fun f hf => Or.inr (Or.inr (Or.inl hf))) (hwalkR hxim)).trans ?_
          refine (N.graph.walks_symm (walks_mono (fun f hf => Or.inr (Or.inr (Or.inr hf)))
            (hwalkR hym))).tail ⟨g₁, Or.inr (Or.inl rfl), Or.inr ⟨hg₁, rfl⟩⟩
      obtain ⟨C₁, hC₁, hg₀C₁, hsub₁⟩ := hcycle e₁ he₁
      obtain ⟨C₂, hC₂, hg₀C₂, hsub₂⟩ := hcycle e₂ he₂
      have hC := h1 C₁ C₂ hC₁ hC₂ ⟨g₀, hg₀C₁, hg₀C₂⟩
      -- the other edge of the cycle at `x` leaves `x`
      obtain ⟨g, hgC, hgne, hgx⟩ : ∃ g ∈ C₁, g ≠ g₀ ∧ N.graph.source g = x := by
        obtain ⟨f, hf, f', hf', hff', hu₁, hu₂⟩ :=
          hC₁.exists_ne_of_mem (fun f _ => hloop f) (target_mem_cycleNodes hg₀C₁)
        have hleave : ∀ f, f ≠ g₀ → (N.graph.source f = x ∨ N.graph.target f = x) →
            N.graph.source f = x := fun f hf h => h.resolve_right fun h' => hf (hin1 f h')
        by_cases hfg : f = g₀
        · have hf'g : f' ≠ g₀ := fun h => hff' (hfg.trans h.symm)
          exact ⟨f', hf', hf'g, hleave f' hf'g hu₂⟩
        · exact ⟨f, hf, hfg, hleave f hfg hu₁⟩
      -- it is `e₁` or `e₂`, which is on only one of the two cycles
      have hnot : ∀ eᵢ eⱼ, N.graph.source eᵢ = x → N.graph.source eⱼ = x → eᵢ ≠ eⱼ →
          eᵢ ∉ insert g₀ {f | f = eⱼ ∨ f = g₁ ∨
            N.graph.Reaches (N.graph.target eⱼ) (N.graph.source f) ∨
              N.graph.Reaches y (N.graph.source f)} := by
        intro eᵢ eⱼ heᵢ heⱼ hij
        rintro (h | h | h | h | h)
        · exact hux (by rw [← heᵢ, h, hg₀])
        · exact hij h
        · exact hux (by rw [← heᵢ, h, hg₁])
        · rw [heᵢ] at h
          exact hcyc h ⟨eⱼ, heⱼ, rfl⟩
        · rw [heᵢ] at h
          exact hyx h
      rcases hxout g hgx with rfl | rfl
      · exact hnot g e₂ he₁ he₂ hne₁₂ (hsub₂ (hC ▸ hgC))
      · exact hnot g e₁ he₂ he₁ (Ne.symm hne₁₂) (hsub₁ hgC)
    -- one of the children is a tree node
    have hx3 := hdeg a₁ ha₁ hxm
    have hy3 := hdeg a₂ ha₂ hym
    by_cases hx2 : N.graph.outdegree (N.graph.target a₁) = 2
    · exact key a₁ a₂ ha₁ ha₂ hne hxy hxm hx2
    by_cases hy2 : N.graph.outdegree (N.graph.target a₂) = 2
    · exact key a₂ a₁ ha₂ ha₁ (Ne.symm hne) (Ne.symm hxy) hym hy2
    have hyx := hhyb a₁ a₂ ha₁ ha₂ hout' hxy
      (by have := hN.indegree_le_two (N.graph.target a₁); omega)
    have hxy' := hhyb a₂ a₁ ha₂ ha₁ (fun g hg => (hout' g hg).symm) (Ne.symm hxy)
      (by have := hN.indegree_le_two (N.graph.target a₂); omega)
    exact hxy (eq_of_reaches_of_reaches hN.1.acyclic hxy' hyx)

section Blocks

variable (G : DirectedMultigraph V E) (ℓ : X → V)

/-- The taxa `x` and `y` are in the same block of the edge set `D`: a walk avoiding `D` joins them.
For `D` the edges of the cycle `C_v` these are the `v`-blocks; for the edges of a family `𝒟` of
cycles, the network blocks induced by `𝒟`. -/
def SameBlock (D : Set E) (x y : X) : Prop := G.Walks Dᶜ (ℓ x) (ℓ y)

/-- The block `B_u` associated with the node `u` of a cycle with edges `D`: the taxa joined to `u`
by a walk avoiding `D`. The paper defines `B_u` as the side of the partition `{B_u, X ∖ B_u}`
obtained by removing `u`; in a binary level-1 network the component of `u` without the edges of its
cycle is what hangs from `u`, so the two agree. -/
def nodeBlock (D : Set E) (u : V) : Set X := {x | G.Walks Dᶜ u (ℓ x)}

/-- The edges of the cycles of the family `𝒟`. -/
def familyEdges (𝒟 : Set (Set E)) : Set E := ⋃₀ 𝒟

/-- The cycles of size at least `k`: their network blocks are the `k`-network blocks. -/
def cyclesOfSizeAtLeast (k : ℕ) : Set (Set E) := {C | IsCycle G C ∧ k ≤ C.ncard}

end Blocks

/-- **Lemma 4** (`2taxnetblo`): in a connected level-1 network, two taxa in different network blocks
of a family `𝒟` of cycles are in different blocks of some cycle of `𝒟` (that is, different
`v`-blocks for its hybrid node `v`). It holds for the graph of a rooted network and of an unrooted
one.

The published version gives no proof; the proof is that of arXiv v1, left in a comment of its source
(TeX l. 403–409). Some edge `e` of a path from `a` to `b` is on a cycle `C` of `𝒟`. A walk from `a`
to `b` avoiding the edges of `C` and the path give a cycle `C'` through `e`
(`exists_isCycle_of_walks`). arXiv v1 concludes with "this cycle contains some edges not in `C_v`,
and at least one in `C_v`", which it does not justify (TeX l. 406); this gap is filled along its
lines: `C' = C` by the level-1 condition, so all the edges of `C` lie on the path, which a cycle
does not (`IsPathOf.not_subset_of_isCycle`). -/
theorem lemma4 {G : DirectedMultigraph V E} (ℓ : X → V) (hG : G.IsConnected) (h1 : IsLevelOne G)
    {𝒟 : Set (Set E)} (h𝒟 : ∀ C ∈ 𝒟, IsCycle G C) {a b : X}
    (hab : ¬ SameBlock G ℓ (familyEdges 𝒟) a b) : ∃ C ∈ 𝒟, ¬ SameBlock G ℓ C a b := by
  classical
  -- a path `P` from `a` to `b`
  obtain ⟨n, p, q, hP, hp0, hpn⟩ := exists_isPathOf_of_walks (hG (ℓ a) (ℓ b))
  -- some edge `e` of `P` is on a cycle `C` of `𝒟`, else `a` and `b` are in the same network block
  obtain ⟨i, hi⟩ : ∃ i, q i ∈ familyEdges 𝒟 := by
    by_contra hno
    push Not at hno
    have hP' : IsPathOf G (familyEdges 𝒟)ᶜ n p q := ⟨hno, hP.link, hP.injective⟩
    have hw := hP'.walks
    rw [hp0, hpn] at hw
    exact hab hw
  obtain ⟨C, hC𝒟, hiC⟩ := hi
  refine ⟨C, hC𝒟, fun hQ => ?_⟩
  -- a walk `Q` from `a` to `b` avoiding `C`, with the parts of `P` before and after `e`, joins the
  -- ends of `e` avoiding `e`
  let F : Set E := {f | f ∈ Set.range q ∧ f ≠ q i} ∪ Cᶜ
  have hpre : G.Walks F (p 0) (p i.castSucc) := by
    refine walks_mono (fun f hf => ?_) (hP.walks_of_le (Fin.zero_le _))
    obtain ⟨l, -, hl, rfl⟩ := hf
    refine Or.inl ⟨⟨l, rfl⟩, fun h => ?_⟩
    have := congrArg Fin.val (hP.injective_edge h)
    simp only [Fin.val_castSucc] at hl
    omega
  have hsuf : G.Walks F (p i.succ) (p (Fin.last n)) := by
    refine walks_mono (fun f hf => ?_) (hP.walks_of_le (Fin.le_last _))
    obtain ⟨l, hl, -, rfl⟩ := hf
    refine Or.inl ⟨⟨l, rfl⟩, fun h => ?_⟩
    have := congrArg Fin.val (hP.injective_edge h)
    simp only [Fin.val_succ] at hl
    omega
  have hQ' : G.Walks F (p 0) (p (Fin.last n)) := by
    rw [hp0, hpn]
    exact walks_mono Set.subset_union_right hQ
  have hwalk : G.Walks F (p i.castSucc) (p i.succ) :=
    ((G.walks_symm hpre).trans hQ').trans (G.walks_symm hsuf)
  have hei : q i ∉ F := by
    rintro (⟨-, h⟩ | h)
    · exact h rfl
    · exact h hiC
  -- so `e` is on a cycle `C'` whose other edges are edges of `P` or avoid `C`
  obtain ⟨C', hC', heC', hsub⟩ := exists_isCycle_of_walks hei (by
    rcases hP.link i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
      exact G.walks_symm hwalk
    · rw [h₁, h₂]
      exact hwalk)
  -- `C'` shares `e` with `C`, so it is `C`; then the edges of `C` would all be on `P`
  have hCC' := h1 C' C hC' (h𝒟 C hC𝒟) ⟨q i, heC', hiC⟩
  refine hP.not_subset_of_isCycle (h𝒟 C hC𝒟) fun f hf => ?_
  rcases hsub (hCC' ▸ hf) with rfl | ⟨hfq, -⟩ | hfC
  · exact ⟨i, rfl⟩
  · exact hfq
  · exact absurd hf hfC

/-- **Corollary 1** (`cor:partiofparti`): the network partition induced by a family `𝒟` of cycles is
the common refinement of the partitions of its cycles: a walk avoiding the edges of all the cycles
of `𝒟` avoids those of each, and Lemma 4 gives the converse. -/
theorem corollary1 {G : DirectedMultigraph V E} (ℓ : X → V) (hG : G.IsConnected)
    (h1 : IsLevelOne G) {𝒟 : Set (Set E)} (h𝒟 : ∀ C ∈ 𝒟, IsCycle G C) (a b : X) :
    SameBlock G ℓ (familyEdges 𝒟) a b ↔ ∀ C ∈ 𝒟, SameBlock G ℓ C a b := by
  refine ⟨fun h C hC => walks_mono (Set.compl_subset_compl.mpr (Set.subset_sUnion_of_mem hC)) h,
    fun h => ?_⟩
  by_contra hn
  obtain ⟨C, hC, hnC⟩ := lemma4 ℓ hG h1 h𝒟 hn
  exact hnC (h C hC)

section Contract

/-- Two nodes are identified by contracting the cycles satisfying `P`: they lie on one such cycle.
-/
def ContractRel (G : DirectedMultigraph V E) (P : Set E → Prop) (u w : V) : Prop :=
  ∃ C, IsCycle G C ∧ P C ∧ u ∈ cycleNodes G C ∧ w ∈ cycleNodes G C

/-- **Contracting the cycles satisfying `P`** (Section 2.5): remove their edges and identify the
nodes of each. -/
def contractCycles (G : SemidirectedNetwork V E X) (P : Set E → Prop) :
    SemidirectedNetwork (Quot (ContractRel G.graph P))
      {e // ∀ C, IsCycle G.graph C → P C → e ∉ C} X where
  graph :=
    { source := fun e => Quot.mk _ (G.graph.source e.1)
      target := fun e => Quot.mk _ (G.graph.target e.1) }
  IsDirected e := G.IsDirected e.1
  leaf x := Quot.mk _ (G.leaf x)

/-- Forgetting the direction of the hybrid edges in `D`. -/
def undirectEdges {V' E' : Type*} (G : SemidirectedNetwork V' E' X) (D : Set E') :
    SemidirectedNetwork V' E' X :=
  ⟨G.graph, fun e => G.IsDirected e ∧ e ∉ D, G.leaf⟩

/-- **The network `Ñ` of Theorem 4**: from `N⁻`, contract the 2- and 3-cycles, forget the directions
of the hybrid edges in 4-cycles, and suppress the nodes of degree two that this leaves. The paper's
statement does not mention the last step; contracting a 2-cycle leaves a node of degree two, whose
place on an edge no quartet concordance factor can detect, and the proof of Theorem 4 builds the
network without such nodes. -/
def tildeNetwork (G : SemidirectedNetwork V E X) :=
  suppress (undirectEdges (contractCycles G fun C => C.ncard ≤ 3)
    {e | ∃ C, IsCycle G.graph C ∧ C.ncard = 4 ∧ e.1 ∈ C})

/-- The edges left by removing pendant edges repeatedly until none remains: the largest set of edges
in which every node of an edge has at least two edges of the set. -/
def pendantCore (G : DirectedMultigraph V E) : Set E :=
  ⋃₀ {K | ∀ e ∈ K, ∀ u, (G.source e = u ∨ G.target e = u) →
    2 ≤ {f | f ∈ K ∧ G.source f = u}.ncard + {f | f ∈ K ∧ G.target f = u}.ncard}

/-- **Definition 13** (`treeofcycles`): the *tree of cycles* of `N⁻`: 1) remove pendant edges
repeatedly until none remains; 2) suppress the nodes of degree two that are not on a cycle; 3)
contract each cycle of the result. -/
def treeOfCycles (G : SemidirectedNetwork V E X) :=
  let H := restrict G (pendantCore G.graph) ∅
  contractCycles (suppressExcept H {u | ∃ C, IsCycle G.graph C ∧ u.1 ∈ cycleNodes G.graph C})
    fun _ => True

end Contract

end Banos2019
