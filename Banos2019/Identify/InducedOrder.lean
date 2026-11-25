module

public import Banos2019.Identify.InducedCycles

/-!
# The order of the blocks of a cycle of `(N⊕_Y)⁻` (Baños 2019, proof of Theorem 4)

The nodes of a cycle of `(N⊕_Y)⁻` are the nodes of the cycle of `N⁻` with the same hybrid node whose
blocks contain taxa of `Y`, in the same order around the cycle. Two blocks of the cycle of `(N⊕_Y)⁻`
are adjacent exactly when, in the cycle of `N⁻`, the blocks of their taxa are distinct and joined
avoiding the blocks of the other taxa of `Y` (`adjacentBlocks_induced_iff`).
`adjacentBlocks_quartetUnrooted_iff` is the case of a set of four taxa that the cycle separates.

* `IsCycleOf.reflTransGen_of_le`: the nodes of a cycle read in order from one node to another are
  joined along the cycle through these nodes.
* `reflTransGen_unrooted_of_joins_induced`, `reflTransGen_unrooted_of_reflTransGen_induced`: an
  edge, and so a walk, along the cycle of `(N⊕_Y)⁻` is a walk along the cycle of `N⁻` with the same
  hybrid node, through nodes that are not nodes of `(N⊕_Y)⁻` besides those of the first walk.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

/-! ### Walks along a cycle read in order -/

section CycleWalk

variable {V' E' : Type*} {G : DirectedMultigraph V' E'}

/-- **The nodes `v i, …, v j` of a cycle are joined along it through these nodes.** -/
theorem IsCycleOf.reflTransGen_of_le {n : ℕ} {v : Fin (n + 1) → V'} {e : Fin (n + 1) → E'}
    (hC : IsCycleOf G (n + 1) v e) {P : V' → Prop} {i j : Fin (n + 1)} (hij : i ≤ j)
    (hP : ∀ l : Fin (n + 1), i ≤ l → l ≤ j → P (v l)) :
    Relation.ReflTransGen (fun a b => G.AdjOn (Set.range e) a b ∧ P a ∧ P b) (v i) (v j) := by
  suffices ∀ d : ℕ, ∀ j : Fin (n + 1), (j : ℕ) = i + d →
      (∀ l : Fin (n + 1), i ≤ l → l ≤ j → P (v l)) →
      Relation.ReflTransGen (fun a b => G.AdjOn (Set.range e) a b ∧ P a ∧ P b) (v i) (v j) from
    this (j - i) j (by rw [Fin.le_def] at hij; omega) hP
  intro d
  induction d with
  | zero =>
    intro j hj _
    rw [show j = i from Fin.ext (by simpa using hj)]
  | succ d ih =>
    intro j hj hPj
    have hjn := j.isLt
    set j' : Fin (n + 1) := ⟨i + d, by omega⟩ with hj'
    have hj'j : j' ≤ j := by rw [Fin.le_def]; simp only [j']; omega
    have hrot : finRotate (n + 1) j' = j := by
      refine Fin.ext ?_
      rw [coe_finRotate_of_ne_last (fun h => by
        have := congrArg Fin.val h
        simp only [Fin.val_last, j'] at this
        omega)]
      simp only [j']
      omega
    refine (ih j' rfl fun l h₁ h₂ => hPj l h₁ (h₂.trans hj'j)).tail
      ⟨⟨e j', ⟨j', rfl⟩, ?_⟩, hPj j' (by rw [Fin.le_def]; simp only [j']; omega) hj'j,
        hPj j (by rw [Fin.le_def]; omega) le_rfl⟩
    have := hC.joins j'
    rwa [hrot] at this

end CycleWalk

/-! ### The cycles of `(N⊕_Y)⁻` along the cycles of `N⁻` -/

section InducedOrder

variable {V E X : Type*} {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
  (h1 : IsLevelOne N.graph) (hX : Nontrivial X) {Y : Set X} (hY : Y.Nontrivial)

/-- A node of `(N⊕_Y)⁻` is a node of `N⁻`. -/
theorem exists_unrooted_node_eq_inducedNode
    (u : SemidirectedVertex (inducedLSA_isBinaryRootedNetwork hN hY).1 hY.coe_sort) :
    ∃ n : SemidirectedVertex hN.1 hX, n.1.1 = inducedNode hN hY u :=
  (exists_unrooted_node_of_induced hN hX hY (z := u.1.1)
    fun h => unrooted_node_ne_lsa u (h.trans (lsa_univ_inducedLSA hN hY _).symm)).2

include h1 in
/-- **An edge of a cycle of `(N⊕_Y)⁻` is a path along the cycle of `N⁻` with the same hybrid
node**, through nodes that are not nodes of `(N⊕_Y)⁻`: the chain of its arc of `N⊕_Y`, or, for the
edge merged at the root of `N⊕_Y`, the chains of the two arcs leaving `LSA(Y)`, joined at `LSA(Y)`
or, when `LSA(Y) = LSA(X)`, by the edge of `N⁻` merged there. So a set `F` of nodes of `N⁻` that are
nodes of `(N⊕_Y)⁻` is avoided when the two ends are not in it. -/
theorem reflTransGen_unrooted_of_joins_induced {C' : Set _}
    (hC' : IsCycle (inducedLSAUnrooted N hN Y hY).graph C') {w}
    (hw : IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : inducedNode hN hY w = v.1.1)
    {F : Set (SemidirectedVertex hN.1 hX)}
    (hF : ∀ n ∈ F, ∃ z : {v // ¬ (inducedBelow N hN.1 Y hY).IsChainVertex v},
      z ≠ (inducedLSA N hN.1 Y hY).root ∧ z.1.1 = n.1.1)
    {e} (he : e ∈ C') {u₁ u₂} (hj : Joins (inducedLSAUnrooted N hN Y hY).graph e u₁ u₂)
    {n₁ n₂ : SemidirectedVertex hN.1 hX} (hn₁ : n₁.1.1 = inducedNode hN hY u₁)
    (hn₂ : n₂.1.1 = inducedNode hN hY u₂) (hn₁F : n₁ ∉ F) (hn₂F : n₂ ∉ F) :
    Relation.ReflTransGen (fun a b => (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F) n₁
      n₂ := by
  have := hN.1.finite_arcs
  have hQb := inducedLSA_isBinaryRootedNetwork hN hY
  have hL := lsaNetwork_isPhylogenetic hN.1 hY
  have : Nontrivial Y := hY.coe_sort
  set Q := inducedLSA N hN.1 Y hY with hQ_def
  set L := inducedBelow N hN.1 Y hY with hL_def
  set D := unrootedCycleArcs hQb C' with hD_def
  set Ĉ := unrootedCycleArcs hN C with hĈ_def
  have hcorr : Ĉ = Subtype.val '' suppressChainArcs L D :=
    unrootedCycleArcs_eq_image_induced hN h1 hX hY hC' hw hC hv hwv
  -- the vertices of `N` that are not nodes of `F`
  let P : V → Prop := fun z => ∀ n ∈ F, n.1.1 ≠ z
  have hPF : ∀ n : SemidirectedVertex hN.1 hX, P n.1.1 → n ∉ F := fun n hn hnF => hn n hnF rfl
  have hFP : ∀ n : SemidirectedVertex hN.1 hX, n ∉ F → P n.1.1 := fun n hn n' hn' h =>
    hn (unrooted_node_ext h ▸ hn')
  have hPchain : ∀ z, L.IsChainVertex z → P z.1 := fun z hz n hn h => by
    obtain ⟨y, -, hy⟩ := hF n hn
    exact y.2 (Subtype.ext (hy.trans h) ▸ hz)
  have hProot : P (lsa hN.1 Y hY.nonempty) := fun n hn h => by
    obtain ⟨y, hyr, hy⟩ := hF n hn
    exact hyr (Subtype.ext (Subtype.ext (hy.trans h)))
  have hmemĈ : ∀ f ∈ D, ∀ g, L.IsOnChain f.1 g → g.1 ∈ Ĉ := fun f hf g hg => by
    rw [hcorr]
    exact ⟨g, ⟨f, hf, hg⟩, rfl⟩
  -- directed steps along `Ĉ` to vertices that are not nodes of `F`
  let R : V → V → Prop := fun x y => ∃ g ∈ Ĉ, N.graph.source g = x ∧ N.graph.target g = y ∧ P y
  -- along the chain of an arc of `D`
  have hchain : ∀ f ∈ D, P (Q.graph.target f).1.1 → P (N.graph.target f.1.1) ∧
      Relation.ReflTransGen R (N.graph.target f.1.1) (Q.graph.target f).1.1 := by
    intro f hf hPf
    have h₁ := reflTransGen_chain_targets f (P := fun z => P z.1) (fun z hz => hPchain z hz)
      (chainReach_chainEnd hL _) hPf
    refine ⟨?_, Relation.ReflTransGen.lift Subtype.val ?_ _ _ h₁⟩
    · by_cases hc : L.IsChainVertex (L.graph.target f.1)
      · exact hPchain _ hc
      · have : chainEnd hL (L.graph.target f.1) = L.graph.target f.1 := chainEnd_eq_self hL hc
        change P (L.graph.target f.1).1
        rw [← this]
        exact hPf
    · rintro x y ⟨g, hg, hgs, hgt, hPy⟩
      exact ⟨g.1, hmemĈ f hf g hg, congrArg Subtype.val hgs, congrArg Subtype.val hgt, hPy⟩
  -- directed paths along `Ĉ` are walks of `N⁻` along `C`
  have hlift : ∀ (a : SemidirectedVertex hN.1 hX) {b : V}, P a.1.1 →
      Relation.ReflTransGen R a.1.1 b → ∀ b' : SemidirectedVertex hN.1 hX, b'.1.1 = b →
        Relation.ReflTransGen (fun a b => (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F)
          a b' := by
    intro a b ha hab b' hb'
    obtain ⟨b'', hb'', h⟩ := exists_unrooted_reflTransGen hN C a ha hab
    obtain rfl : b'' = b' := unrooted_node_ext (hb''.trans hb'.symm)
    refine Relation.ReflTransGen.mono ?_ _ _ h
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy, hPF x hx, hPF y hy⟩
  have hsymm : ∀ a b, (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F →
      (unrooted N hN hX).graph.AdjOn C b a ∧ b ∉ F ∧ a ∉ F := fun a b ⟨h, ha, hb⟩ =>
    ⟨(unrooted N hN hX).graph.adjOn_symm h, hb, ha⟩
  -- from the source of `e` to its target
  have core : ∀ n₁ n₂ : SemidirectedVertex hN.1 hX,
      n₁.1.1 = inducedNode hN hY ((inducedLSAUnrooted N hN Y hY).graph.source e) →
      n₂.1.1 = inducedNode hN hY ((inducedLSAUnrooted N hN Y hY).graph.target e) → n₁ ∉ F → n₂ ∉ F →
      Relation.ReflTransGen (fun a b => (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F)
        n₁ n₂ := by
    intro n₁ n₂ hn₁ hn₂ hn₁F hn₂F
    have heD : e.1.1 ∈ D := ⟨e, he, Or.inl rfl⟩
    have hP₂ : P (Q.graph.target e.1.1).1.1 := by
      have : (Q.graph.target e.1.1).1.1 = n₂.1.1 := hn₂.symm
      rw [this]
      exact hFP n₂ hn₂F
    obtain ⟨hPt, hpath⟩ := hchain _ heD hP₂
    have heĈ : e.1.1.1.1 ∈ Ĉ := hmemĈ _ heD _ (Or.inl rfl)
    by_cases hr : Q.graph.source e.1.1 = Q.root
    · -- the edge merged at the root of `N⊕_Y`: the two arcs leaving `LSA(Y)`
      have hr' := hr.trans (lsa_univ_inducedLSA hN hY Set.univ_nonempty).symm
      have hs₁ := unrooted_source_val_of_eq hQb e hr'
      have hrD : (rootTreeArc hQb.1 hQb.2 hY.coe_sort).1 ∈ D := ⟨e, he, Or.inr ⟨hr', rfl⟩⟩
      have hn₁' : n₁.1.1 = (Q.graph.target (rootTreeArc hQb.1 hQb.2 hY.coe_sort).1).1.1 :=
        hn₁.trans (congrArg (fun z => z.1.1) hs₁)
      have hP₁ : P (Q.graph.target (rootTreeArc hQb.1 hQb.2 hY.coe_sort).1).1.1 := by
        rw [← hn₁']
        exact hFP n₁ hn₁F
      obtain ⟨hPr, hpathr⟩ := hchain _ hrD hP₁
      have hrĈ : (rootTreeArc hQb.1 hQb.2 hY.coe_sort).1.1.1 ∈ Ĉ := hmemĈ _ hrD _ (Or.inl rfl)
      have hrN : N.graph.source (rootTreeArc hQb.1 hQb.2 hY.coe_sort).1.1.1 =
          lsa hN.1 Y hY.nonempty :=
        congrArg (fun z => z.1.1) ((source_rootTreeArc_val hQb).trans (lsa_univ_inducedLSA hN hY _))
      have heN : N.graph.source e.1.1.1.1 =
          lsa hN.1 Y hY.nonempty :=
        congrArg (fun z => z.1.1) hr
      have hne : (rootTreeArc hQb.1 hQb.2 hY.coe_sort).1.1.1 ≠ e.1.1.1.1 := fun h =>
        e.2 (Subtype.ext (Subtype.ext (Subtype.ext h.symm)))
      by_cases hm :
          lsa hN.1 Y hY.nonempty =
            lsa hN.1 Set.univ Set.univ_nonempty
      · -- `LSA(Y) = LSA(X)`: the edge of `N⁻` merged at `LSA(X)` joins the two children
        have hrm := hrN.trans hm
        have hem := heN.trans hm
        -- the nodes of `N⁻` of the two children
        have hchild : ∀ g : E, N.graph.source g = lsa hN.1 Set.univ Set.univ_nonempty →
            ∃ a : SemidirectedVertex hN.1 hX, a.1.1 = N.graph.target g := fun g hg =>
          exists_unrooted_node hN.1 (Relation.ReflTransGen.single ⟨g, hg, rfl⟩) fun h =>
            hN.1.acyclic _ (.single ⟨g, hg, h ▸ rfl⟩)
        obtain ⟨a₁, ha₁⟩ := hchild _ hrm
        obtain ⟨a₂, ha₂⟩ := hchild _ hem
        have w₁ := hlift a₁ (by rw [ha₁]; exact hPr) (by rw [ha₁]; exact hpathr) n₁ hn₁'
        have w₂ := hlift a₂ (by rw [ha₂]; exact hPt) (by rw [ha₂]; exact hpath) n₂ hn₂
        -- `rootTreeArc` of `N` is one of the two arcs leaving `LSA(X)`
        have hout : N.graph.outdegree (lsa hN.1 Set.univ Set.univ_nonempty) = 2 :=
          le_antisymm (hN.outdegree_le_two _) (by
            unfold DirectedMultigraph.outdegree
            rw [← Set.ncard_pair hne]
            refine Set.ncard_le_ncard ?_ (Set.toFinite _)
            rintro g (rfl | rfl)
            exacts [hrm, hem])
        have he₀ : (rootTreeArc hN.1 hN.2 hX).1 ∈ ({(rootTreeArc hQb.1 hQb.2 hY.coe_sort).1.1.1,
            e.1.1.1.1} : Set E) := by
          rw [← eq_or_eq_of_outdegree_eq_two hout hne hrm hem]
          exact source_rootTreeArc_val hN
        -- the edge of `N⁻` of the other arc
        have hstep : ∀ o : E, o ∈ Ĉ → N.graph.source o = lsa hN.1 Set.univ Set.univ_nonempty →
            o ≠ (rootTreeArc hN.1 hN.2 hX).1 → ∀ a b : SemidirectedVertex hN.1 hX,
            a.1.1 = N.graph.target (rootTreeArc hN.1 hN.2 hX).1 → b.1.1 = N.graph.target o →
            P a.1.1 → P b.1.1 →
            (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F := by
          intro o hoĈ hos ho a b ha hb hPa hPb
          have hoB : o ∈ N.belowArcs (lsa hN.1 Set.univ Set.univ_nonempty) Set.univ :=
            ⟨by rw [hos]; exact .refl, mem_ancestralVertices_univ hN.1 _⟩
          let c : SemidirectedArc hN.1 hN.2 hX := ⟨⟨o, hoB⟩, fun h => ho (congrArg Subtype.val h)⟩
          have hcC : c ∈ C := (mem_unrootedCycleArcs_iff hN C c).1 hoĈ
          refine ⟨⟨c, hcC, Or.inl ⟨unrooted_node_ext ?_, unrooted_node_ext hb.symm⟩⟩, hPF a hPa,
            hPF b hPb⟩
          rw [unrooted_source_val_of_eq hN c hos, ha]
        rcases he₀ with h₀ | h₀
        · have hst := hstep _ heĈ hem (fun h => hne (h.trans h₀).symm) a₁ a₂
            (by rw [ha₁, ← h₀]) ha₂ (by rw [ha₁]; exact hPr) (by rw [ha₂]; exact hPt)
          exact (reflTransGen_symm_of_symm hsymm w₁).trans (Relation.ReflTransGen.head hst w₂)
        · have hst := hstep _ hrĈ hrm (fun h => hne (h.trans h₀)) a₂ a₁
            (by rw [ha₂, ← h₀]) ha₁ (by rw [ha₂]; exact hPt) (by rw [ha₁]; exact hPr)
          exact (reflTransGen_symm_of_symm hsymm w₁).trans
            (Relation.ReflTransGen.head (hsymm _ _ hst) w₂)
      · -- `LSA(Y)` is a node of `N⁻`
        obtain ⟨nl, hnl⟩ := exists_unrooted_node (hX := hX) hN.1 (reaches_lsa_induced hN hY _) hm
        have hPl : P nl.1.1 := by rw [hnl]; exact hProot
        have w₁ := hlift nl hPl (Relation.ReflTransGen.head ⟨_, hrĈ, hrN.trans hnl.symm, rfl, hPr⟩
          hpathr) n₁ hn₁'
        have w₂ := hlift nl hPl (Relation.ReflTransGen.head ⟨_, heĈ, heN.trans hnl.symm, rfl, hPt⟩
          hpath) n₂ hn₂
        exact (reflTransGen_symm_of_symm hsymm w₁).trans w₂
    · -- an arc of `N⊕_Y`
      have hs₁ := unrooted_source_val_of_ne hQb e
        (fun h => hr (h.trans (lsa_univ_inducedLSA hN hY Set.univ_nonempty)))
      have hn₁' : n₁.1.1 = N.graph.source e.1.1.1.1 := hn₁.trans (congrArg (fun z => z.1.1) hs₁)
      exact hlift n₁ (hFP n₁ hn₁F)
        (Relation.ReflTransGen.head ⟨_, heĈ, hn₁'.symm, rfl, hPt⟩ hpath) n₂ hn₂
  rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact core n₁ n₂ (by rw [h₁]; exact hn₁) (by rw [h₂]; exact hn₂) hn₁F hn₂F
  · exact reflTransGen_symm_of_symm hsymm
      (core n₂ n₁ (by rw [h₁]; exact hn₂) (by rw [h₂]; exact hn₁) hn₂F hn₁F)

include h1 in
/-- **A walk along a cycle of `(N⊕_Y)⁻` is a walk along the cycle of `N⁻` with the same hybrid
node** (`reflTransGen_unrooted_of_joins_induced` for each edge), avoiding a set `F` of nodes of `N⁻`
that are nodes of `(N⊕_Y)⁻` when the first walk does. -/
theorem reflTransGen_unrooted_of_reflTransGen_induced {C' : Set _}
    (hC' : IsCycle (inducedLSAUnrooted N hN Y hY).graph C') {w}
    (hw : IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : inducedNode hN hY w = v.1.1)
    {F : Set (SemidirectedVertex hN.1 hX)}
    (hF : ∀ n ∈ F, ∃ z : {v // ¬ (inducedBelow N hN.1 Y hY).IsChainVertex v},
      z ≠ (inducedLSA N hN.1 Y hY).root ∧ z.1.1 = n.1.1)
    {a b} (hab : Relation.ReflTransGen (fun p q =>
      (inducedLSAUnrooted N hN Y hY).graph.AdjOn C' p q ∧ (∀ n ∈ F, n.1.1 ≠ inducedNode hN hY p) ∧
        (∀ n ∈ F, n.1.1 ≠ inducedNode hN hY q)) a b)
    {n₁ n₂ : SemidirectedVertex hN.1 hX} (hn₁ : n₁.1.1 = inducedNode hN hY a)
    (hn₂ : n₂.1.1 = inducedNode hN hY b) :
    Relation.ReflTransGen (fun a b => (unrooted N hN hX).graph.AdjOn C a b ∧ a ∉ F ∧ b ∉ F) n₁
      n₂ := by
  induction hab generalizing n₂ with
  | refl =>
    obtain rfl : n₁ = n₂ := unrooted_node_ext (hn₁.trans hn₂.symm)
    exact .refl
  | @tail p q _ hpq ih =>
    obtain ⟨⟨e, he, hj⟩, hp, hq⟩ := hpq
    obtain ⟨np, hnp⟩ := exists_unrooted_node_eq_inducedNode hN hX hY p
    exact (ih hnp).trans (reflTransGen_unrooted_of_joins_induced hN h1 hX hY hC' hw hC hv hwv hF he
      hj hnp hn₂ (fun h => hp _ h hnp) (fun h => hq _ h hn₂))

include h1 in
/-- **The order of the blocks of a cycle of `(N⊕_Y)⁻`** is that of the blocks of the cycle of `N⁻`
with the same hybrid node that contain taxa of `Y`: the blocks of `x` and `y` are adjacent in the
first exactly when, in the second, they are distinct and joined avoiding the blocks of the other taxa
of `Y`. An edge of the first is a path along the second through nodes whose blocks have no taxon of
`Y` (`reflTransGen_unrooted_of_joins_induced`). Conversely, if the blocks of `x` and `y` are not
adjacent in the first, read it from the node `u 0` of `x`: the node of `y` is some `u m` with
`2 ≤ m < n`, and `u 1`, `u n` are on the two arcs between them. The walks `u 0, u 1` and
`u 1, …, u m` along the first are walks along the second
(`reflTransGen_unrooted_of_reflTransGen_induced`), and with the given walk from the node of `x` to
that of `y` they join the three pairs of nodes of `x`, `u 1`, `y` in the second, each avoiding the
other two of these four nodes, which no four nodes of a cycle allow (`IsCycle.not_joined_three`). -/
theorem adjacentBlocks_induced_iff {C' : Set _}
    (hC' : IsCycle (inducedLSAUnrooted N hN Y hY).graph C') (hC'2 : 2 ≤ C'.ncard) {w}
    (hw : IsHybridNodeOf (inducedLSAUnrooted N hN Y hY) C' w) {C : Set _}
    (hC : IsCycle (unrooted N hN hX).graph C) {v : SemidirectedVertex hN.1 hX}
    (hv : IsHybridNodeOf (unrooted N hN hX) C v) (hwv : inducedNode hN hY w = v.1.1) (x y : Y) :
    AdjacentBlocks (inducedLSAUnrooted N hN Y hY) C' x y ↔
      ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x y ∧
        JoinedAvoiding (unrooted N hN hX) C
          {t | t ∈ Y ∧ ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x t ∧
            ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C y t} x y := by
  have := hN.1.finite_arcs
  have hQb := inducedLSA_isBinaryRootedNetwork hN hY
  have := hQb.1.finite_arcs
  have h1Q := isLevelOne_inducedLSA_graph hN.1 h1 hY
  -- the nodes of the blocks of the taxa of `Y` in `(N⊕_Y)⁻` and in `N⁻`
  have hι : ∀ a : Y, inducedNode hN hY (blockNode (inducedLSAUnrooted N hN Y hY) C' a) =
      (blockNode (unrooted N hN hX) C a).1.1 := fun a =>
    inducedNode_blockNode hN h1 hX hY hC' hw hC hv hwv a a.2
  have hββ : ∀ a b : Y, blockNode (unrooted N hN hX) C a = blockNode (unrooted N hN hX) C b ↔
      blockNode (inducedLSAUnrooted N hN Y hY) C' a =
        blockNode (inducedLSAUnrooted N hN Y hY) C' b := fun a b =>
    blockNode_eq_iff_induced hN h1 hX hY hC' hw hC hv hwv a.2 b.2
  have hsb : ∀ a b : X, SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C a b ↔
      blockNode (unrooted N hN hX) C a = blockNode (unrooted N hN hX) C b :=
    sameBlock_iff_blockNode_eq h1 hC
  -- the node of `N⁻` of the block of a taxon of `Y` is a node of `(N⊕_Y)⁻`
  have hFY : ∀ (t : X) (ht : t ∈ Y), ∃ z : {v // ¬ (inducedBelow N hN.1 Y hY).IsChainVertex v},
      z ≠ (inducedLSA N hN.1 Y hY).root ∧ z.1.1 = (blockNode (unrooted N hN hX) C t).1.1 :=
    fun t ht => ⟨(blockNode (inducedLSAUnrooted N hN Y hY) C' ⟨t, ht⟩).1.1, fun h =>
      unrooted_node_ne_lsa _ (h.trans (lsa_univ_inducedLSA hN hY _).symm), hι ⟨t, ht⟩⟩
  constructor
  · -- an edge of the cycle of `(N⊕_Y)⁻` is a path along the cycle of `N⁻`
    rintro ⟨e, he, u₁, u₂, hj, hxu, hyu⟩
    have hu₁ : u₁ ∈ cycleNodes (inducedLSAUnrooted N hN Y hY).graph C' := by
      rcases hj with ⟨h, -⟩ | ⟨-, h⟩
      exacts [⟨e, he, Or.inl h⟩, ⟨e, he, Or.inr h⟩]
    have hu₂ : u₂ ∈ cycleNodes (inducedLSAUnrooted N hN Y hY).graph C' := by
      rcases hj with ⟨-, h⟩ | ⟨h, -⟩
      exacts [⟨e, he, Or.inr h⟩, ⟨e, he, Or.inl h⟩]
    obtain rfl := eq_blockNode h1Q hC' hu₁ hxu
    obtain rfl := eq_blockNode h1Q hC' hu₂ hyu
    obtain ⟨k, u, f, hcyc, hrange⟩ := id hC'
    have hk : C'.ncard = k := by
      rw [← hrange, Set.ncard_range_of_injective hcyc.injective_edge, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have he' := he
    rw [← hrange] at he'
    obtain ⟨l, rfl⟩ := he'
    have hne := hcyc.ne_of_joins (by omega) hj
    refine ⟨fun h => hne ((hββ x y).1 ((hsb x y).1 h)), ?_⟩
    rw [joinedAvoiding_iff_reflTransGen hN h1 hC]
    refine reflTransGen_unrooted_of_joins_induced hN h1 hX hY hC' hw hC hv hwv ?_ he hj
      (hι x).symm (hι y).symm ?_ ?_
    · intro n hn
      obtain ⟨t, ht, rfl⟩ := (mem_blockNodes_iff_blockNode hN h1 hC).1 hn
      exact hFY t ht.1
    · intro hn
      obtain ⟨t, ht, h⟩ := (mem_blockNodes_iff_blockNode hN h1 hC).1 hn
      exact ht.2.1 ((hsb _ _).2 h.symm)
    · intro hn
      obtain ⟨t, ht, h⟩ := (mem_blockNodes_iff_blockNode hN h1 hC).1 hn
      exact ht.2.2 ((hsb _ _).2 h.symm)
  · rintro ⟨hxy, hJ⟩
    rw [hsb] at hxy
    have hxy' := fun h => hxy ((hββ x y).2 h)
    by_contra hadj
    have hnj : ∀ f ∈ C', ¬ Joins (inducedLSAUnrooted N hN Y hY).graph f
        (blockNode (inducedLSAUnrooted N hN Y hY) C' x)
        (blockNode (inducedLSAUnrooted N hN Y hY) C' y) := fun f hf hj =>
      hadj ⟨f, hf, _, _, hj, (blockNode_spec hC' x).2, (blockNode_spec hC' y).2⟩
    -- the nodes `u 0, …, u n` of the cycle of `(N⊕_Y)⁻`, starting from the node of `x`
    obtain ⟨n, u, f, hcyc, hrange, h0⟩ := hC'.exists_isCycleOf_apply_zero (blockNode_mem hC' x)
    have hnodes : cycleNodes (inducedLSAUnrooted N hN Y hY).graph C' = Set.range u := by
      rw [← hrange]
      exact hcyc.cycleNodes_eq
    have hf : ∀ i, f i ∈ C' := fun i => by
      rw [← hrange]
      exact ⟨i, rfl⟩
    obtain ⟨m, hm⟩ : blockNode (inducedLSAUnrooted N hN Y hY) C' y ∈ Set.range u :=
      hnodes ▸ blockNode_mem hC' y
    -- the node of `y` is neither `u 0`, nor next to it
    have hm0 : (m : ℕ) ≠ 0 := fun hm0 => hxy' (by
      rw [← h0, ← hm, show m = 0 from Fin.ext (by rw [hm0, Fin.val_zero])])
    have hm1 : (m : ℕ) ≠ 1 := by
      intro hm1
      apply hnj _ (hf 0)
      have hj := hcyc.joins 0
      have hr : finRotate (n + 1) 0 = m := Fin.ext (by
        rw [coe_finRotate_of_ne_last (by rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega),
          Fin.val_zero, hm1])
      rwa [hr, h0, hm] at hj
    have hmn : (m : ℕ) ≠ n := by
      intro hmn
      obtain rfl : m = Fin.last n := Fin.ext hmn
      apply hnj _ (hf (Fin.last n))
      have hj := hcyc.joins (Fin.last n)
      rw [finRotate_last, h0, hm] at hj
      exact Or.symm hj
    have hmlt := m.isLt
    -- taxa `c` and `d` in the blocks of `u 1` and `u n`
    have hmemu : ∀ i, u i ∈ cycleNodes (inducedLSAUnrooted N hN Y hY).graph C' := fun i => by
      rw [hnodes]
      exact ⟨i, rfl⟩
    set i₁ : Fin (n + 1) := ⟨1, by omega⟩ with hi₁
    obtain ⟨c, hc⟩ := exists_blockNode_eq h1Q hC' (hmemu i₁)
    obtain ⟨d, hd⟩ := exists_blockNode_eq h1Q hC' (hmemu (Fin.last n))
    -- nodes of the first cycle at distinct positions
    have hdist : ∀ (a b : Y) (i j : Fin (n + 1)),
        blockNode (inducedLSAUnrooted N hN Y hY) C' a = u i →
        blockNode (inducedLSAUnrooted N hN Y hY) C' b = u j → (i : ℕ) ≠ j →
        blockNode (unrooted N hN hX) C a ≠ blockNode (unrooted N hN hX) C b :=
      fun a b i j ha hb hij h =>
        hij (congrArg Fin.val (hcyc.injective_node (ha.symm.trans (((hββ a b).1 h).trans hb))))
    have hιne : ∀ (a : Y) (k l : Fin (n + 1)), blockNode (inducedLSAUnrooted N hN Y hY) C' a = u k →
        (k : ℕ) ≠ l → (blockNode (unrooted N hN hX) C a).1.1 ≠ inducedNode hN hY (u l) :=
      fun a k l ha hkl h => hkl (congrArg Fin.val (hcyc.injective_node
        (ha.symm.trans (inducedNode_injective hN hY ((hι a).trans h)))))
    have hx0 : blockNode (inducedLSAUnrooted N hN Y hY) C' x = u 0 := h0.symm
    have hy0 : blockNode (inducedLSAUnrooted N hN Y hY) C' y = u m := hm.symm
    have hc0 : blockNode (inducedLSAUnrooted N hN Y hY) C' c = u i₁ := hc
    have hd0 : blockNode (inducedLSAUnrooted N hN Y hY) C' d = u (Fin.last n) := hd
    have hi₁v : (i₁ : ℕ) = 1 := rfl
    -- the walk `u 0, u 1`, avoiding the nodes of `y` and `d`
    have J₁₂ : Relation.ReflTransGen (fun a b => (unrooted N hN hX).graph.AdjOn C a b ∧
        a ∉ ({blockNode (unrooted N hN hX) C y, blockNode (unrooted N hN hX) C d} : Set _) ∧
        b ∉ ({blockNode (unrooted N hN hX) C y, blockNode (unrooted N hN hX) C d} : Set _))
        (blockNode (unrooted N hN hX) C x) (blockNode (unrooted N hN hX) C c) := by
      have hW := hcyc.reflTransGen_of_le (P := fun p =>
        ∀ n' ∈ ({blockNode (unrooted N hN hX) C y, blockNode (unrooted N hN hX) C d} : Set _),
          n'.1.1 ≠ inducedNode hN hY p) (i := 0) (j := i₁) (Fin.zero_le _) (by
        intro l _ hl
        rw [Fin.le_def, hi₁v] at hl
        rintro _ (rfl | rfl)
        · exact hιne y m l hy0 (by omega)
        · exact hιne d (Fin.last n) l hd0 (by rw [Fin.val_last]; omega))
      rw [hrange] at hW
      refine reflTransGen_unrooted_of_reflTransGen_induced hN h1 hX hY hC' hw hC hv hwv ?_ hW
        (by rw [← hx0]; exact (hι x).symm) (by rw [← hc0]; exact (hι c).symm)
      rintro _ (rfl | rfl)
      exacts [hFY y y.2, hFY d d.2]
    -- the walk `u 1, …, u m`, avoiding the nodes of `x` and `d`
    have J₂₃ : Relation.ReflTransGen (fun a b => (unrooted N hN hX).graph.AdjOn C a b ∧
        a ∉ ({blockNode (unrooted N hN hX) C x, blockNode (unrooted N hN hX) C d} : Set _) ∧
        b ∉ ({blockNode (unrooted N hN hX) C x, blockNode (unrooted N hN hX) C d} : Set _))
        (blockNode (unrooted N hN hX) C c) (blockNode (unrooted N hN hX) C y) := by
      have hW := hcyc.reflTransGen_of_le (P := fun p =>
        ∀ n' ∈ ({blockNode (unrooted N hN hX) C x, blockNode (unrooted N hN hX) C d} : Set _),
          n'.1.1 ≠ inducedNode hN hY p) (i := i₁) (j := m) (by rw [Fin.le_def, hi₁v]; omega) (by
        intro l hl₁ hl
        rw [Fin.le_def, hi₁v] at hl₁
        rw [Fin.le_def] at hl
        rintro _ (rfl | rfl)
        · exact hιne x 0 l hx0 (by rw [Fin.val_zero]; omega)
        · exact hιne d (Fin.last n) l hd0 (by rw [Fin.val_last]; omega))
      rw [hrange] at hW
      refine reflTransGen_unrooted_of_reflTransGen_induced hN h1 hX hY hC' hw hC hv hwv ?_ hW
        (by rw [← hc0]; exact (hι c).symm) (by rw [← hy0]; exact (hι y).symm)
      rintro _ (rfl | rfl)
      exacts [hFY x x.2, hFY d d.2]
    -- the given walk from the node of `x` to that of `y`
    rw [joinedAvoiding_iff_reflTransGen hN h1 hC] at hJ
    have hxc := hdist x c 0 i₁ hx0 hc0 (by rw [Fin.val_zero, hi₁v]; omega)
    have hxy₂ := hdist x y 0 m hx0 hy0 (by rw [Fin.val_zero]; omega)
    have hxd := hdist x d 0 (Fin.last n) hx0 hd0 (by rw [Fin.val_zero, Fin.val_last]; omega)
    have hcy := hdist c y i₁ m hc0 hy0 (by rw [hi₁v]; omega)
    have hcd := hdist c d i₁ (Fin.last n) hc0 hd0 (by rw [hi₁v, Fin.val_last]; omega)
    have hyd := hdist y d m (Fin.last n) hy0 hd0 (by rw [Fin.val_last]; omega)
    have hmemT : ∀ t : Y, blockNode (unrooted N hN hX) C x ≠ blockNode (unrooted N hN hX) C t →
        blockNode (unrooted N hN hX) C y ≠ blockNode (unrooted N hN hX) C t →
        blockNode (unrooted N hN hX) C t ∈ blockNodes (unrooted N hN hX) C
          {t | t ∈ Y ∧ ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C x t ∧
            ¬ SameBlock (unrooted N hN hX).graph (unrooted N hN hX).leaf C y t} :=
      fun t hxt hyt => (mem_blockNodes_iff_blockNode hN h1 hC).2
        ⟨t, ⟨t.2, fun h => hxt ((hsb _ _).1 h), fun h => hyt ((hsb _ _).1 h)⟩, rfl⟩
    exact hC.not_joined_three (blockNode_mem hC x) (blockNode_mem hC c) (blockNode_mem hC y)
      (blockNode_mem hC d) hxc hxy₂ hxd hcy hcd hyd (by simp) (by simp)
      ⟨hmemT c hxc (Ne.symm hcy), hmemT d hxd hyd⟩ J₁₂ J₂₃ hJ

end InducedOrder

end Banos2019
