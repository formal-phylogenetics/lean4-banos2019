module

public import Banos2019.Bridge.Invariance

/-!
# The Challenge's unrooted network is the library's

The Challenge defines `N⁻` (Definition 5) as the part of `N` below `LSA(X)` with its tree edges
undirected (`Model.Network.belowLSA`), all its nodes of degree two suppressed. The library's `N⁻`
(`RootedNetwork.semidirected`) removes the LSA and merges its two edges into one (`unrootAt`, at the
tree edge `rootTreeArc`). Below the LSA every node keeps its degree, one or three, so the LSA is the one
node that suppression removes, and the chains are the edges not at the LSA, each alone, and the two
edges at the LSA together (`exists_sdIso_suppressExcept`). The metrics agree: a chain has the sum of the
lengths of its edges and the inheritance probability of its hybrid edge (Definition 6).

* `Model.Network.nonempty_sdIso_unrooted`, `Model.Network.nonempty_sdMetricIso_unrooted`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019.Model.Network

variable {V E X : Type*} (N : Network V E X) (hb : IsBinaryRootedNetwork N.toRooted)
  [hX : Nontrivial X]

/-- The library's LSA of all the taxa. -/
abbrev lsaL : V := RootedNetwork.lsa hb.1 Set.univ Set.univ_nonempty

include hb

theorem lsa_eq_lsaL : N.lsa = N.lsaL hb := N.lsa_eq (N.isBinaryNetwork_iff.mpr hb)

/-- The nodes of `belowLSA` are the nodes below the LSA. -/
theorem mem_belowLSA_iff (v : V) :
    (N.graph.Reaches N.lsa v ∨ ∃ x, N.leaf x = v) ↔ N.toRooted.graph.Reaches (N.lsaL hb) v := by
  rw [N.lsa_eq_lsaL hb]
  refine ⟨fun h => h.elim id ?_, Or.inl⟩
  rintro ⟨x, rfl⟩
  exact (lsa_spec hb.1 Set.univ Set.univ_nonempty).1.reaches_leaf hb.1 (Set.mem_univ x)

theorem reaches_lsaL_source_iff (e : E) :
    N.graph.Reaches N.lsa (N.graph.source e) ↔
      N.toRooted.graph.Reaches (N.lsaL hb) (N.toRooted.graph.source e) := by
  rw [N.lsa_eq_lsaL hb]
  rfl

theorem lsaL_ne_leaf (x : X) : N.leaf x ≠ N.lsaL hb :=
  (lsa_spec hb.1 Set.univ Set.univ_nonempty).1.leaf_ne hb.1 Set.nontrivial_univ x

theorem target_ne_lsaL {e : E} (he : N.toRooted.graph.Reaches (N.lsaL hb) (N.toRooted.graph.source e)) :
    N.toRooted.graph.target e ≠ N.lsaL hb := fun h =>
  not_reaches_target_source hb.1.acyclic e (by rw [h]; exact he)

/-- An edge entering a node strictly below the LSA leaves a node below the LSA. -/
theorem reaches_source_of_target {e : E} (hv : N.toRooted.graph.Reaches (N.lsaL hb) (N.graph.target e))
    (hne : N.graph.target e ≠ N.lsaL hb) :
    N.toRooted.graph.Reaches (N.lsaL hb) (N.toRooted.graph.source e) := by
  obtain ⟨x, hx⟩ := exists_reaches_leaf hb.1 (N.toRooted.graph.target e)
  exact (lsa_spec hb.1 Set.univ Set.univ_nonempty).1.reaches_source hb.1 (Set.mem_univ x) hx
    fun h => hne (eq_of_reaches_of_reaches hb.1.acyclic h hv)

/-! ### The degrees of `belowLSA` -/

open Classical in
theorem belowLSA_indegree (u : {v // N.graph.Reaches N.lsa v ∨ ∃ x, N.leaf x = v}) :
    N.belowLSA.toSD.graph.indegree u =
      if u.1 = N.lsaL hb then 0 else N.toRooted.graph.indegree u.1 := by
  have hu := (N.mem_belowLSA_iff hb u.1).mp u.2
  split_ifs with h
  · have := hb.1.finite_arcs
    refine (N.belowLSA.toSD.graph.indegree_eq_zero_iff u).mpr fun e he => ?_
    have he' : N.graph.target e.1 = N.lsaL hb := (congrArg Subtype.val he).trans h
    exact N.target_ne_lsaL hb ((N.reaches_lsaL_source_iff hb e.1).mp e.2) he'
  · refine Set.ncard_congr' ?_
    exact
      { toFun := fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩
        invFun := fun g => ⟨⟨g.1, (N.reaches_lsaL_source_iff hb g.1).mpr
          (N.reaches_source_of_target hb (by rw [show N.graph.target g.1 = u.1 from g.2]; exact hu)
            (by rw [show N.graph.target g.1 = u.1 from g.2]; exact h))⟩, Subtype.ext g.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

theorem belowLSA_outdegree (u : {v // N.graph.Reaches N.lsa v ∨ ∃ x, N.leaf x = v}) :
    N.belowLSA.toSD.graph.outdegree u = N.toRooted.graph.outdegree u.1 := by
  have hu := (N.mem_belowLSA_iff hb u.1).mp u.2
  refine Set.ncard_congr' ?_
  exact
    { toFun := fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩
      invFun := fun g => ⟨⟨g.1, (N.reaches_lsaL_source_iff hb g.1).mpr
        (by rw [show N.toRooted.graph.source g.1 = u.1 from g.2]; exact hu)⟩, Subtype.ext g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **The LSA is the one node of `belowLSA` that suppression removes.** -/
theorem isBranch_belowLSA_iff (u : {v // N.graph.Reaches N.lsa v ∨ ∃ x, N.leaf x = v}) :
    Banos2019.IsBranch N.belowLSA.toSD ∅ u ↔ u.1 ≠ N.lsaL hb := by
  have := hb.1.finite_arcs
  unfold Banos2019.IsBranch degree
  rw [N.belowLSA_indegree hb, N.belowLSA_outdegree hb]
  have hleaf : (∃ x, N.belowLSA.toSD.leaf x = u) ↔ ∃ x, N.leaf x = u.1 :=
    ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩, fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
  rw [hleaf]
  simp only [Set.mem_empty_iff_false, or_false]
  split_ifs with h
  · rw [h, lsa_univ_outdegree hb.1 hb.2]
    simp only [zero_add, ne_eq, not_true_eq_false, false_or]
    exact iff_false_intro fun ⟨x, hx⟩ => N.lsaL_ne_leaf hb x hx
  · simp only [ne_eq, h, not_false_eq_true, iff_true]
    have hu := (N.mem_belowLSA_iff hb u.1).mp u.2
    have hr : u.1 ≠ N.root := fun hr => h (hr.trans (eq_of_reaches_of_reaches hb.1.acyclic
      (hb.1.root_reaches _) (hr ▸ hu)))
    by_cases h0 : N.toRooted.graph.outdegree u.1 = 0
    · obtain ⟨x, hx⟩ := (hb.1.leaves _).mp h0
      exact Or.inr ⟨x, hx⟩
    · have := hb.2.2 u.1 hr h0
      left
      omega

/-! ### The isomorphism -/

/-- The library's `N⁻` as nodes and edges of `belowLSA`. -/
def unrootedVertEquiv :
    {u : {v // N.graph.Reaches N.lsa v ∨ ∃ x, N.leaf x = v} //
      Banos2019.IsBranch N.belowLSA.toSD ∅ u} ≃ SemidirectedVertex hb.1 hX where
  toFun u := ⟨⟨u.1.1, (N.mem_belowLSA_iff hb u.1.1).mp u.1.2,
    mem_ancestralVertices_univ hb.1 _⟩, fun h => (N.isBranch_belowLSA_iff hb u.1).mp u.2
      (congrArg Subtype.val h)⟩
  invFun v := ⟨⟨v.1.1, (N.mem_belowLSA_iff hb v.1.1).mpr v.1.2.1⟩,
    (N.isBranch_belowLSA_iff hb _).mpr fun h => v.2 (Subtype.ext h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The edge of `belowLSA` of an edge of the library's `N⁻`. -/
def toBE (g : SemidirectedArc hb.1 hb.2 hX) : {e // N.graph.Reaches N.lsa (N.graph.source e)} :=
  ⟨sdArc hb.1 hb.2 hX g, (N.reaches_lsaL_source_iff hb _).mpr g.1.2.1⟩

/-- The edge of `belowLSA` merged at the LSA. -/
def rootBE : {e // N.graph.Reaches N.lsa (N.graph.source e)} :=
  ⟨sdRootArc hb.1 hb.2 hX, (N.reaches_lsaL_source_iff hb _).mpr
    (by rw [(sdRootArc_spec hb.1 hb.2 hX).1]; exact .refl)⟩

theorem toBE_ne_rootBE (g : SemidirectedArc hb.1 hb.2 hX) : N.toBE hb g ≠ N.rootBE hb := fun h => by
  have h' := congrArg Subtype.val h
  exact g.2 (Subtype.ext h')

open Classical in
/-- The chain of `belowLSA` of an edge of the library's `N⁻`. -/
def unrootedChainOf (g : SemidirectedArc hb.1 hb.2 hX) :
    Set {e // N.graph.Reaches N.lsa (N.graph.source e)} :=
  if N.toRooted.graph.source (sdArc hb.1 hb.2 hX g) = N.lsaL hb then {N.toBE hb g, N.rootBE hb}
  else {N.toBE hb g}

/-- The other arc out of the LSA. -/
theorem exists_otherArc : ∃ b : SemidirectedArc hb.1 hb.2 hX,
    N.toRooted.graph.source (sdArc hb.1 hb.2 hX b) = N.lsaL hb ∧
      ∀ e, N.toRooted.graph.source e = N.lsaL hb → e ≠ sdRootArc hb.1 hb.2 hX →
        e = sdArc hb.1 hb.2 hX b := by
  obtain ⟨b, hbs, hbne, -, huniq⟩ := exists_other_arc_lsa hb (Z := Set.univ) Set.nontrivial_univ
    (sdRootArc_spec hb.1 hb.2 hX).1
  obtain ⟨g, hg⟩ := (mem_range_sdArc hb.1 hb.2 hX b).mpr ⟨by rw [hbs]; exact .refl, hbne⟩
  exact ⟨g, hg ▸ hbs, fun e he hne => hg ▸ huniq e he hne⟩

open Classical in
/-- The edge of the library's `N⁻` of an edge of `belowLSA`. -/
def unrootedPsi (e : {e // N.graph.Reaches N.lsa (N.graph.source e)}) : SemidirectedArc hb.1 hb.2 hX :=
  if h : e.1 = sdRootArc hb.1 hb.2 hX then (N.exists_otherArc hb).choose
  else ⟨⟨e.1, (N.reaches_lsaL_source_iff hb e.1).mp e.2, mem_ancestralVertices_univ hb.1 _⟩,
    fun h' => h (congrArg Subtype.val h')⟩

theorem rootBE_ne_toBE_source (g : SemidirectedArc hb.1 hb.2 hX) :
    N.toRooted.graph.target (sdRootArc hb.1 hb.2 hX) ≠ N.toRooted.graph.target (sdArc hb.1 hb.2 hX g) :=
  fun h => sdArc_target_ne hb hX g h.symm

theorem isChain_unrootedChainOf (g : SemidirectedArc hb.1 hb.2 hX) :
    Banos2019.IsChain N.belowLSA.toSD ∅ (N.unrootedChainOf hb g) ∧
      chainEnds N.belowLSA.toSD ∅ (N.unrootedChainOf hb g) =
        {((N.unrootedVertEquiv hb).symm ((semidirected hb.1 hb.2 hX).graph.source g)).1,
          ((N.unrootedVertEquiv hb).symm ((semidirected hb.1 hb.2 hX).graph.target g)).1} := by
  have hgs : N.toRooted.graph.Reaches (N.lsaL hb) (N.toRooted.graph.source (sdArc hb.1 hb.2 hX g)) :=
    g.1.2.1
  have htne := N.target_ne_lsaL hb hgs
  -- the nodes of `belowLSA`
  let bv : ∀ v, N.toRooted.graph.Reaches (N.lsaL hb) v →
      {v // N.graph.Reaches N.lsa v ∨ ∃ x, N.leaf x = v} :=
    fun v hv => ⟨v, (N.mem_belowLSA_iff hb v).mpr hv⟩
  have hbr : ∀ v hv, v ≠ N.lsaL hb → Banos2019.IsBranch N.belowLSA.toSD ∅ (bv v hv) :=
    fun v hv hne => (N.isBranch_belowLSA_iff hb _).mpr hne
  have ht : N.toRooted.graph.Reaches (N.lsaL hb) (N.toRooted.graph.target (sdArc hb.1 hb.2 hX g)) :=
    hgs.tail ⟨_, rfl, rfl⟩
  have hsrc : ((N.unrootedVertEquiv hb).symm ((semidirected hb.1 hb.2 hX).graph.source g)).1 =
      bv _ ((semidirected hb.1 hb.2 hX).graph.source g).1.2.1 := rfl
  have htgt : ((N.unrootedVertEquiv hb).symm ((semidirected hb.1 hb.2 hX).graph.target g)).1 =
      bv _ ht := rfl
  have hsv := sdVert_source hb.1 hb.2 hX g
  unfold unrootedChainOf
  split_ifs with hm
  · -- the chain through the LSA
    have hr := sdRootArc_spec hb.1 hb.2 hX
    have hr0 : N.toRooted.graph.Reaches (N.lsaL hb)
        (N.toRooted.graph.target (sdRootArc hb.1 hb.2 hX)) := by
      have := Relation.ReflTransGen.single (r := N.toRooted.graph.Adj)
        ⟨sdRootArc hb.1 hb.2 hX, rfl, rfl⟩
      rwa [hr.1] at this
    have hne := N.rootBE_ne_toBE_source hb g
    have hr0ne := N.target_ne_lsaL hb (by rw [hr.1]; exact .refl)
    set a := bv _ hr0
    set m := bv (N.lsaL hb) .refl
    set b := bv _ ht
    have ham : a ≠ m := fun h => hr0ne (congrArg Subtype.val h)
    have hbm : b ≠ m := fun h => htne (congrArg Subtype.val h)
    have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
    have hj₁ : Joins N.belowLSA.toSD.graph (N.rootBE hb) a m := Or.inr ⟨Subtype.ext hr.1, rfl⟩
    have hj₂ : Joins N.belowLSA.toSD.graph (N.toBE hb g) m b := Or.inl ⟨Subtype.ext hm, rfl⟩
    have htr := IsUTrail.cons hj₁ (by
      rintro (h | h)
      · exact ham h
      · exact hab h) (IsUTrail.single hj₂ hbm.symm)
    have hQ : ({N.toBE hb g, N.rootBE hb} : Set _) = insert (N.rootBE hb) {N.toBE hb g} :=
      Set.pair_comm _ _
    have hin : ∀ s ∈ insert a ({m, b} : Set _), s ≠ a → s ≠ b →
        ¬ Banos2019.IsBranch N.belowLSA.toSD ∅ s := by
      rintro s (rfl | rfl | rfl) h₁ h₂
      · exact absurd rfl h₁
      · exact fun h => ((N.isBranch_belowLSA_iff hb _).mp h) rfl
      · exact absurd rfl h₂
    rw [hQ]
    refine ⟨htr.isChain (Set.insert_nonempty _ _) (hbr _ hr0 hr0ne) (hbr _ ht htne) hin, ?_⟩
    rw [htr.chainEnds_eq (Set.insert_nonempty _ _) (hbr _ hr0 hr0ne) (hbr _ ht htne) hin, hsrc, htgt]
    congr 1
    refine Subtype.ext ?_
    change _ = sdVert hb.1 hX ((semidirected hb.1 hb.2 hX).graph.source g)
    rw [hsv, ite_eq_left_of_eq_true _ _ (eq_true hm)]
  · -- an edge not at the LSA
    have hsne : N.toRooted.graph.source (sdArc hb.1 hb.2 hX g) ≠
        N.toRooted.graph.target (sdArc hb.1 hb.2 hX g) := fun h =>
      not_reaches_target_source hb.1.acyclic _ (by rw [h]; exact Relation.ReflTransGen.refl)
    set a := bv _ hgs
    set b := bv _ ht
    have hab : a ≠ b := fun h => hsne (congrArg Subtype.val h)
    have hj : Joins N.belowLSA.toSD.graph (N.toBE hb g) a b := Or.inl ⟨rfl, rfl⟩
    have htr := IsUTrail.single hj hab
    have hin : ∀ s ∈ ({a, b} : Set _), s ≠ a → s ≠ b → ¬ Banos2019.IsBranch N.belowLSA.toSD ∅ s := by
      rintro s (rfl | rfl) h₁ h₂
      · exact absurd rfl h₁
      · exact absurd rfl h₂
    refine ⟨htr.isChain (Set.singleton_nonempty _) (hbr _ hgs hm) (hbr _ ht htne) hin, ?_⟩
    rw [htr.chainEnds_eq (Set.singleton_nonempty _) (hbr _ hgs hm) (hbr _ ht htne) hin, hsrc, htgt]
    congr 1
    refine Subtype.ext ?_
    change _ = sdVert hb.1 hX ((semidirected hb.1 hb.2 hX).graph.source g)
    rw [hsv, ite_eq_right_of_eq_false _ _ (eq_false hm)]

theorem mem_unrootedChainOf_psi (e : {e // N.graph.Reaches N.lsa (N.graph.source e)}) :
    e ∈ N.unrootedChainOf hb (N.unrootedPsi hb e) := by
  unfold unrootedPsi
  split_ifs with h
  · obtain ⟨hs, -⟩ := (N.exists_otherArc hb).choose_spec
    unfold unrootedChainOf
    simp only [hs, ↓reduceIte]
    exact Or.inr (Subtype.ext h)
  · unfold unrootedChainOf
    split_ifs
    · exact Or.inl rfl
    · exact rfl

theorem psi_eq_of_mem (g : SemidirectedArc hb.1 hb.2 hX)
    (e : {e // N.graph.Reaches N.lsa (N.graph.source e)}) (he : e ∈ N.unrootedChainOf hb g) : N.unrootedPsi hb e = g := by
  have hg : sdArc hb.1 hb.2 hX g ≠ sdRootArc hb.1 hb.2 hX := fun h =>
    ((mem_range_sdArc hb.1 hb.2 hX _).mp ⟨g, rfl⟩).2 h
  have hto : N.unrootedPsi hb (N.toBE hb g) = g := by
    unfold unrootedPsi
    rw [dite_eq_right_of_eq_false (eq_false (show ¬ (N.toBE hb g).1 = sdRootArc hb.1 hb.2 hX from hg))]
    rfl
  unfold unrootedChainOf at he
  split_ifs at he with hm
  · rcases he with rfl | rfl
    · exact hto
    · unfold unrootedPsi
      rw [dite_eq_left_of_eq_true (eq_true (show (N.rootBE hb).1 = sdRootArc hb.1 hb.2 hX from rfl))]
      obtain ⟨-, huniq⟩ := (N.exists_otherArc hb).choose_spec
      exact sdArc_injective hb.1 hb.2 hX (huniq _ hm hg).symm
  · rw [Set.mem_singleton_iff] at he
    rw [he]
    exact hto

theorem rootBE_not_isDirected : ¬ N.belowLSA.toSD.IsDirected (N.rootBE hb) := by
  have hbn := N.isBinaryNetwork_iff.mpr hb
  change ¬ N.IsHybridEdge _
  rw [N.isHybridEdge_iff hbn]
  have := (sdRootArc_spec hb.1 hb.2 hX).2
  unfold IsTreeArc at this
  change ¬ 2 ≤ N.toRooted.graph.indegree (N.toRooted.graph.target (sdRootArc hb.1 hb.2 hX))
  omega

theorem unrooted_isDirected_iff (g : SemidirectedArc hb.1 hb.2 hX) :
    (semidirected hb.1 hb.2 hX).IsDirected g ↔
      ∃ e ∈ N.unrootedChainOf hb g, N.belowLSA.toSD.IsDirected e := by
  have hbn := N.isBinaryNetwork_iff.mpr hb
  rw [semidirected_isDirected_iff]
  have hr := N.rootBE_not_isDirected hb
  unfold unrootedChainOf
  split_ifs
  · constructor
    · intro h
      exact ⟨_, Or.inl rfl, (N.isHybridEdge_iff hbn _).mpr h⟩
    · rintro ⟨e, rfl | rfl, he⟩
      · exact (N.isHybridEdge_iff hbn _).mp he
      · exact absurd he hr
  · constructor
    · intro h
      exact ⟨_, rfl, (N.isHybridEdge_iff hbn _).mpr h⟩
    · rintro ⟨e, rfl, he⟩
      exact (N.isHybridEdge_iff hbn _).mp he

theorem unrooted_target_of_directed (g : SemidirectedArc hb.1 hb.2 hX)
    (e : {e // N.graph.Reaches N.lsa (N.graph.source e)}) (he : e ∈ N.unrootedChainOf hb g)
    (hd : N.belowLSA.toSD.IsDirected e) :
    N.belowLSA.toSD.graph.target e =
      ((N.unrootedVertEquiv hb).symm ((semidirected hb.1 hb.2 hX).graph.target g)).1 := by
  have hbn := N.isBinaryNetwork_iff.mpr hb
  have hr := N.rootBE_not_isDirected hb
  have : e = N.toBE hb g := by
    unfold unrootedChainOf at he
    split_ifs at he
    · rcases he with rfl | rfl
      · rfl
      · exact absurd hd hr
    · exact he
  subst this
  rfl

theorem unrooted_source_ne_target (g : SemidirectedArc hb.1 hb.2 hX) :
    (semidirected hb.1 hb.2 hX).graph.source g ≠ (semidirected hb.1 hb.2 hX).graph.target g := by
  intro h
  have h' := congrArg (sdVert hb.1 hX) h
  rw [sdVert_source, sdVert_target] at h'
  split_ifs at h' with hm
  · exact N.rootBE_ne_toBE_source hb g h'
  · exact not_reaches_target_source hb.1.acyclic _ (by rw [h']; exact Relation.ReflTransGen.refl)

/-- **The Challenge's `N⁻` is the library's** (Definition 5). -/
theorem nonempty_sdIso_unrooted : Nonempty (Banos2019.SDIso N.unrooted.toSD (Banos2019.unrooted N.toRooted hb hX)) := by
  have := hb.1.finite_arcs
  obtain ⟨ι, -⟩ := exists_sdIso_suppressExcept (N.unrootedVertEquiv hb) (N.unrootedChainOf hb)
    (fun g => (N.isChain_unrootedChainOf hb g).1) (N.unrootedPsi hb) (N.mem_unrootedChainOf_psi hb)
    (N.psi_eq_of_mem hb) (fun g => (N.isChain_unrootedChainOf hb g).2)
    (N.unrooted_source_ne_target hb) (N.unrooted_isDirected_iff hb)
    (N.unrooted_target_of_directed hb) fun _ => rfl
  exact ⟨(N.belowLSA.suppressIso ∅).trans ι⟩

/-- **The Challenge's metric `N⁻` is the library's** (Definitions 5 and 6). -/
theorem nonempty_sdMetricIso_unrooted [Fintype E] (θ : Params E) :
    Nonempty (Banos2019.SDMetricIso N.unrooted.toSD (N.unrootedParams θ).toMetric
      (Banos2019.unrooted N.toRooted hb hX) (Banos2019.unrootedMetric N.toRooted hb hX θ.toMetric)) := by
  have hbn := N.isBinaryNetwork_iff.mpr hb
  let θ' : Params {e // N.graph.Reaches N.lsa (N.graph.source e)} :=
    ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩
  have hr := N.rootBE_not_isDirected hb
  obtain ⟨ι⟩ := nonempty_sdMetricIso_suppress θ'.toMetric
    (semidirectedMetric hb.1 hb.2 hX θ.toMetric) (N.unrootedVertEquiv hb) (N.unrootedChainOf hb)
    (fun g => (N.isChain_unrootedChainOf hb g).1) (N.unrootedPsi hb) (N.mem_unrootedChainOf_psi hb)
    (N.psi_eq_of_mem hb) (fun g => (N.isChain_unrootedChainOf hb g).2)
    (N.unrooted_source_ne_target hb) (N.unrooted_isDirected_iff hb)
    (N.unrooted_target_of_directed hb) (fun _ => rfl)
    (fun g => by
      rw [semidirectedMetric_length]
      unfold unrootedChainOf
      split_ifs
      · rw [finsum_mem_pair (N.toBE_ne_rootBE hb g)]
        rfl
      · rw [finsum_mem_singleton]
        rfl)
    (fun g hg => by
      rw [semidirectedMetric_inheritance]
      have hd : N.belowLSA.toSD.IsDirected (N.toBE hb g) := by
        change N.IsHybridEdge _
        rw [N.isHybridEdge_iff hbn]
        exact (semidirected_isDirected_iff hb.1 hb.2 hX g).mp hg
      have : {e | e ∈ N.unrootedChainOf hb g ∧ N.belowLSA.toSD.IsDirected e} = {N.toBE hb g} := by
        ext e
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        unfold unrootedChainOf
        split_ifs
        · constructor
          · rintro ⟨rfl | rfl, he⟩
            · rfl
            · exact absurd he hr
          · rintro rfl
            exact ⟨Or.inl rfl, hd⟩
        · constructor
          · rintro ⟨rfl, -⟩
            rfl
          · rintro rfl
            exact ⟨rfl, hd⟩
      rw [this, finprod_mem_singleton]
      rfl)
  exact ⟨(N.belowLSA.suppressMetricIso θ').trans ι⟩

end Banos2019.Model.Network
