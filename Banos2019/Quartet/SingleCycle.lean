module

public import Banos2019.Quartet.Concrete
public import Banos2019.Quartet.RootedIso

/-!
# LSA quartet networks with a single cycle (proofs of Propositions 7, 10 and 11)

An LSA quartet network `Q⊕` whose only cycle is `C`, with hybrid node `v`, has one hybrid node, so
nine nodes and nine arcs (`card_eq_nine_of_single_hybrid`, counting the arcs by their ends). Its
nodes are then located one by one, and `Q⊕` is isomorphic to an explicit network on `Fin 9`
(`RootedNetworkIso.ofNine`).

* `eq_of_two_le_indegree_of_single_cycle`: the hybrid node of the only cycle is the only hybrid
  node.
* `card_eq_nine_of_single_hybrid`: nine nodes and nine arcs.
* `RootedNetworkIso.ofNine`: nine nodes and nine arcs of `Q⊕` with the incidences of a network on
  `Fin 9` give an isomorphism.
* `exists_rootedIso_threeTwo`: with a single cycle, inducing a `3₂`-cycle with `a`, `b` below its
  hybrid node, `Q⊕` is one of four networks on `Fin 9`, one for each position of its root.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

section SingleCycle

variable {Q : RootedNetwork V E X} {θ : MetricData E}

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **The hybrid node of the only cycle is the only hybrid node**: two arcs into a node lie on a
cycle (`exists_isCycle_of_target_eq`), which is `C`, and `C` has one hybrid node (Lemma 3). -/
theorem eq_of_two_le_indegree_of_single_cycle (hQ : IsBinaryRootedNetwork Q)
    (h1 : IsLevelOne Q.graph) {C : Set E} (hone : ∀ C', IsCycle Q.graph C' → C' = C) {v : V}
    (hv : v ∈ cycleNodes Q.graph C) (h2 : Q.graph.indegree v = 2) {w : V}
    (hw : 2 ≤ Q.graph.indegree w) : w = v := by
  have := hQ.1.finite_arcs
  obtain ⟨f₁, hf₁, f₂, hf₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).1
    (show 1 < {e | Q.graph.target e = w}.ncard by unfold DirectedMultigraph.indegree at hw; omega)
  obtain ⟨C', hC', hf₁C, -⟩ := exists_isCycle_of_target_eq hQ h1 hne
    ((show Q.graph.target f₁ = w from hf₁).trans (show Q.graph.target f₂ = w from hf₂).symm)
  have hCC := hone C' hC'
  subst hCC
  have hwC := (show Q.graph.target f₁ = w from hf₁) ▸ target_mem_cycleNodes (G := Q.graph) hf₁C
  exact (lemma3 hQ h1 hC').1.unique ⟨hwC, indegree_eq_two_of_two_le hQ hw⟩ ⟨hv, h2⟩

/-- **A binary network on four taxa with a single hybrid node has nine nodes and nine arcs**:
counting the arcs by their targets, `|E| + 1 = |V| + 1`; by their sources, `|E| + 2·4 + 1 = 2|V|`.
-/
theorem card_eq_nine_of_single_hybrid (hQ : IsBinaryRootedNetwork Q) (hX : Fintype.card X = 4)
    {v : V} (hv2 : Q.graph.indegree v = 2) (huniq : ∀ w, 2 ≤ Q.graph.indegree w → w = v) :
    Fintype.card V = 9 ∧ Fintype.card E = 9 := by
  obtain ⟨-, -, -, -, -, hr0, hr2, hleaf, hinj, hother⟩ := (isBinaryRootedNetwork_iff Q).1 hQ
  have hvr : v ≠ Q.root := fun h => by rw [h, hr0] at hv2; omega
  have hvl : v ∉ Set.range Q.leaf := by
    rintro ⟨x, rfl⟩
    rw [(hleaf x).1] at hv2
    omega
  have hrl : Q.root ∉ Set.range Q.leaf := by
    rintro ⟨x, hx⟩
    have := (hleaf x).1
    rw [hx, hr0] at this
    omega
  have hin : ∀ w, Q.graph.indegree w + (if w = Q.root then 1 else 0) =
      1 + (if w = v then 1 else 0) := by
    intro w
    by_cases hw : w = Q.root
    · subst hw
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm hvr), hr0]
    rw [ite_eq_right hw]
    by_cases hl : w ∈ Set.range Q.leaf
    · obtain ⟨x, rfl⟩ := hl
      rw [ite_eq_right (fun h : Q.leaf x = v => hvl ⟨x, h⟩), (hleaf x).1]
    rcases hother w hw hl with h | h
    · rw [ite_eq_right (fun h' => by rw [h', hv2] at h; omega), h.1]
    · rw [ite_eq_left (huniq w (by omega)), h.1]
  have hout : ∀ w, Q.graph.outdegree w + 2 * (if w ∈ Set.range Q.leaf then 1 else 0) +
      (if w = v then 1 else 0) = 2 := by
    intro w
    by_cases hw : w = Q.root
    · subst hw
      rw [ite_eq_right hrl, ite_eq_right (Ne.symm hvr), hr2]
    by_cases hl : w ∈ Set.range Q.leaf
    · rw [ite_eq_left hl]
      obtain ⟨x, rfl⟩ := hl
      rw [ite_eq_right (fun h : Q.leaf x = v => hvl ⟨x, h⟩), (hleaf x).2]
    rw [ite_eq_right hl]
    rcases hother w hw hl with h | h
    · rw [ite_eq_right (fun h' => by rw [h', hv2] at h; omega), h.2]
    · rw [ite_eq_left (huniq w (by omega)), h.2]
  have hE₁ : Fintype.card E = ∑ w, Q.graph.indegree w := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := Q.graph.target)
      (t := univ) (fun _ _ => mem_univ _)]
    exact sum_congr rfl fun w _ => (indegree_eq_card_filter_target _ w).symm
  have hE₂ : Fintype.card E = ∑ w, Q.graph.outdegree w := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := Q.graph.source)
      (t := univ) (fun _ _ => mem_univ _)]
    exact sum_congr rfl fun w _ => (outdegree_eq_card_filter_source _ w).symm
  have hs₁ := Finset.sum_congr rfl (fun w (_ : w ∈ (univ : Finset V)) => hin w)
  have hs₂ := Finset.sum_congr rfl (fun w (_ : w ∈ (univ : Finset V)) => hout w)
  rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq', ite_eq_left (mem_univ _),
    ite_eq_left (mem_univ _), sum_const, card_univ, smul_eq_mul, mul_one] at hs₁
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_ite_eq', ite_eq_left (mem_univ _), sum_const,
    card_univ, smul_eq_mul] at hs₂
  have hL : ∑ w : V, (if w ∈ Set.range Q.leaf then 1 else 0) = 4 := by
    rw [sum_boole]
    have : (univ.filter fun w => w ∈ Set.range Q.leaf) = univ.image Q.leaf := by
      ext w
      simp [eq_comm]
    rw [Nat.cast_id, this, card_image_of_injective _ hinj, card_univ, hX]
  rw [hL] at hs₂
  omega

/-- **Nine nodes and nine arcs with the incidences of a network on `Fin 9`** give an isomorphism,
when every node and every arc of `Q` is one of them and `Q` has nine of each. -/
def RootedNetworkIso.ofNine {qs qt : Fin 9 → Fin 9} {a b c : X} [DecidableEq X] (n : Fin 9 → V)
    (α : Fin 9 → E) (hn : ∀ y, ∃ i, n i = y) (hα : ∀ g, ∃ j, α j = g) (hV : Fintype.card V = 9)
    (hE : Fintype.card E = 9) (hs : ∀ j, Q.graph.source (α j) = n (qs j))
    (ht : ∀ j, Q.graph.target (α j) = n (qt j)) (hroot : Q.root = n 8)
    (hleaf : ∀ x, Q.leaf x = n (quartetLeaf9 a b c x)) :
    RootedNetworkIso (⟨⟨qs, qt⟩, 8, quartetLeaf9 a b c⟩ : RootedNetwork (Fin 9) (Fin 9) X) Q where
  vert := Equiv.ofBijective n ((Fintype.bijective_iff_surjective_and_card n).2
    ⟨hn, by rw [Fintype.card_fin, hV]⟩)
  arc := Equiv.ofBijective α ((Fintype.bijective_iff_surjective_and_card α).2
    ⟨hα, by rw [Fintype.card_fin, hE]⟩)
  source := hs
  target := ht
  root := hroot
  leaf := hleaf

omit [Fintype V] [Fintype E] [Fintype X] in
/-- Two parallel arcs form a cycle. -/
theorem isCycle_pair_of_parallel {G : DirectedMultigraph V E} {f₁ f₂ : E} (hne : f₁ ≠ f₂)
    (hst : G.source f₁ ≠ G.target f₁) (hs : G.source f₁ = G.source f₂)
    (ht : G.target f₁ = G.target f₂) : IsCycle G {f₁, f₂} := by
  refine ⟨2, ![G.source f₁, G.target f₁], ![f₁, f₂], ⟨by norm_num, fun i => ?_, fun i j h => ?_,
    fun i j h => ?_⟩, ?_⟩
  · fin_cases i
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨by simp [← hs], by simp [← ht]⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · ext f
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- The four rootings of Figure 18 on `Fin 9`: the leaves `a, b, c, d` at `0, 1, 2, 3`, the node `4`
above `a, b`, the hybrid node `5`, the nodes `6`, `7` of `c`, `d`, the root `8`, and the edges
`0, …, 7` of the figure, the edge `8` being the arc of the root that the unrooted network merges
into the other arc of the root, the edge `6`, `5` or `3` of the figure. -/
def fig18RootSrc : Fin 4 → Fin 9 → Fin 9 :=
  ![![4, 4, 6, 7, 5, 7, 8, 6, 8], ![4, 4, 6, 7, 5, 8, 7, 6, 8], ![4, 4, 6, 8, 5, 7, 7, 6, 8],
    ![4, 4, 6, 8, 5, 7, 7, 6, 8]]

/-- The heads of the edges of the four rootings of Figure 18. -/
def fig18RootTgt : Fin 4 → Fin 9 → Fin 9 :=
  ![![0, 1, 2, 3, 4, 6, 5, 5, 7], ![0, 1, 2, 3, 4, 6, 5, 5, 7], ![0, 1, 2, 3, 4, 6, 5, 5, 7],
    ![0, 1, 2, 7, 4, 6, 5, 5, 3]]

variable [DecidableEq X]

/-- **An LSA quartet network whose only cycle induces a `3₂`-cycle is a rooting of Figure 18**, with
the arc that its unrooted network merges at the root as the edge `8`. The node `u` below the hybrid
node `v` is the parent of `a` and `b`; the other nodes of the cycle are tree nodes, and with the
root they are the parents of the other arcs. When the root is on the cycle, it is the parent of `v`
(the first rooting) or of the two other nodes of the cycle (the second); otherwise it is the parent
of the top of the cycle and of a taxon (the third and the fourth rootings, by the arc that the
unrooted network merges). -/
theorem exists_rootedIso_threeTwo (hQ : IsLSAQuartet Q θ) {C : Set E} {v : V}
    (hC : InducesCycleType Q C v 3 2) (hone : ∀ C', IsCycle Q.graph C' → C' = C) {a b : X}
    (hab : a ≠ b) (hD : {x | Q.graph.Reaches v (Q.leaf x)} = {a, b}) :
    ∃ (c d : X) (_ : Distinct4 a b c d) (s : Fin 4)
      (φ : RootedNetworkIso (⟨⟨fig18RootSrc s, fig18RootTgt s⟩, 8, quartetLeaf9 a b c⟩ :
        RootedNetwork (Fin 9) (Fin 9) X) Q),
      (rootTreeArc hQ.binary.1 hQ.binary.2 hQ.nontrivial).1 = φ.arc 8 := by
  have hB := hQ.binary
  have hP := hB.1
  have h1 := hQ.levelOne
  have hX := hQ.card_taxa
  obtain ⟨hcyc, hvC, hv2, hsz, -⟩ := hC
  have huniq : ∀ w, 2 ≤ Q.graph.indegree w → w = v := fun w hw =>
    eq_of_two_le_indegree_of_single_cycle hB h1 hone hvC hv2 hw
  obtain ⟨hV, hE⟩ := card_eq_nine_of_single_hybrid hB hX hv2 huniq
  obtain ⟨-, -, -, -, -, hr0, hr2, hleafdeg, hinj, hother⟩ := (isBinaryRootedNetwork_iff Q).1 hB
  set r := Q.root with hr_def
  have hcy : ∀ {x y}, Q.graph.Reaches x y → Q.graph.Adj y x → False := fun h hab =>
    hP.acyclic _ (Relation.TransGen.tail' h hab)
  have hloop : ∀ g, Q.graph.source g ≠ Q.graph.target g := source_ne_target_of_binary hB
  have hnotr : ∀ g, Q.graph.target g ≠ r := hP.target_ne_root
  have hreach_r : ∀ y, Q.graph.Reaches y r → y = r := fun y h =>
    eq_of_reaches_of_reaches hP.acyclic h (hP.root_reaches y)
  have hleafsrc : ∀ x g, Q.graph.source g ≠ Q.leaf x := fun x g h =>
    (Q.graph.outdegree_eq_zero_iff _).1 (hleafdeg x).2 g h
  have hin1 : ∀ y, Q.graph.indegree y = 1 → ∀ g g', Q.graph.target g = y →
      Q.graph.target g' = y → g = g' := by
    intro y hy g g' hg hg'
    obtain ⟨e, he⟩ := (Q.graph.indegree_eq_one_iff y).1 hy
    exact ((he g).1 hg).trans ((he g').1 hg').symm
  have hex_in : ∀ y, Q.graph.indegree y = 1 → ∃ g, Q.graph.target g = y := fun y hy => by
    obtain ⟨e, he⟩ := (Q.graph.indegree_eq_one_iff y).1 hy
    exact ⟨e, (he e).2 rfl⟩
  have hout2 : ∀ y, Q.graph.outdegree y = 2 → ∀ g₁ g₂, g₁ ≠ g₂ → Q.graph.source g₁ = y →
      Q.graph.source g₂ = y → ∀ g, Q.graph.source g = y → g = g₁ ∨ g = g₂ :=
    fun y hy g₁ g₂ hne h₁ h₂ g hg => mem_pair_of_source_of_outdegree_eq_two hy hne h₁ h₂ g hg
  have hother_out : ∀ y, Q.graph.outdegree y = 2 → ∀ g₁, Q.graph.source g₁ = y →
      ∃ g₂, g₂ ≠ g₁ ∧ Q.graph.source g₂ = y := by
    intro y hy g₁ hg₁
    obtain ⟨x₁, x₂, hx, hs⟩ := Set.ncard_eq_two.1 hy
    have m₁ : x₁ ∈ {e | Q.graph.source e = y} := hs ▸ Set.mem_insert _ _
    have m₂ : x₂ ∈ {e | Q.graph.source e = y} := hs ▸ Set.mem_insert_of_mem _ rfl
    by_cases h : x₁ = g₁
    · exact ⟨x₂, fun h' => hx (h.trans h'.symm), m₂⟩
    · exact ⟨x₁, h, m₁⟩
  have hparallel : ∀ f₁ f₂, f₁ ≠ f₂ → Q.graph.source f₁ = Q.graph.source f₂ →
      Q.graph.target f₁ = Q.graph.target f₂ → False := by
    intro f₁ f₂ hne hs ht
    have hCe := hone _ (isCycle_pair_of_parallel hne (hloop f₁) hs ht)
    have h2 : C.ncard = 2 := by rw [← hCe, Set.ncard_pair hne]
    rw [h2] at hsz
    split_ifs at hsz <;> omega
  -- the hybrid node `v`, its arcs `h₁`, `h₂` and its child `u`
  have hvr : v ≠ r := fun h => by rw [h, hr0] at hv2; omega
  have hvl : ∀ x, Q.leaf x ≠ v := fun x h => by rw [← h, (hleafdeg x).1] at hv2; omega
  have hrl : ∀ x, Q.leaf x ≠ r := fun x h => by
    have := (hleafdeg x).1; rw [h, hr0] at this; omega
  obtain ⟨h₁, h₂, hh₁₂, hhs⟩ := Set.ncard_eq_two.1 hv2
  have hth₁ : Q.graph.target h₁ = v := (Set.ext_iff.1 hhs h₁).2 (Set.mem_insert _ _)
  have hth₂ : Q.graph.target h₂ = v := (Set.ext_iff.1 hhs h₂).2 (Set.mem_insert_of_mem _ rfl)
  have hvin : ∀ g, Q.graph.target g = v → g = h₁ ∨ g = h₂ := fun g hg =>
    mem_pair_of_target_of_indegree_eq_two hv2 hh₁₂ hth₁ hth₂ g hg
  have hh₁C := mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 hth₁
  have hh₂C := mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 hth₂
  have hsh : Q.graph.source h₁ ≠ Q.graph.source h₂ := fun h =>
    hparallel h₁ h₂ hh₁₂ h (hth₁.trans hth₂.symm)
  obtain ⟨cv, hcvs, hcvu⟩ := existsUnique_child_of_hybrid hB hv2
  set u := Q.graph.target cv with hu_def
  have hvu : Q.graph.Reaches v u := .single ⟨cv, hcvs, rfl⟩
  have hur : u ≠ r := hnotr cv
  have huv : u ≠ v := fun h => hloop cv (hcvs.trans h.symm)
  have huC : u ∉ cycleNodes Q.graph C := fun h =>
    hcy (reaches_hybrid hB h1 hcyc hvC hv2 u h) ⟨cv, hcvs, rfl⟩
  have hul : ∀ x, Q.leaf x ≠ u := by
    intro x hx
    have key : ∀ y, Q.graph.Reaches v (Q.leaf y) → y = x := by
      intro y hy
      rcases Relation.ReflTransGen.cases_head hy with h | ⟨z, ⟨g, hgs, hgt⟩, hz⟩
      · exact absurd h.symm (hvl y)
      · rw [← hgt, hcvu g hgs] at hz
        have hz' : Q.graph.Reaches (Q.leaf x) (Q.leaf y) := hx ▸ hz
        exact hinj (Q.graph.eq_of_reaches_of_outdegree_eq_zero hz' (hleafdeg x).2)
    have ha : a ∈ ({a, b} : Set X) := Set.mem_insert _ _
    have hb : b ∈ ({a, b} : Set X) := Set.mem_insert_of_mem _ rfl
    rw [← hD] at ha hb
    exact hab ((key a ha).trans (key b hb).symm)
  have hu1 : Q.graph.indegree u = 1 ∧ Q.graph.outdegree u = 2 := by
    rcases hother u hur (fun ⟨x, hx⟩ => hul x hx) with h | h
    · exact h
    · exact absurd (huniq u (by omega)) huv
  -- the two other nodes `w`, `w'` of the cycle, tree nodes
  obtain ⟨t, hK⟩ := isContractible_of_cycle hB h1 hcyc hvC hv2
  have hcard3 : #(cycleNodesOffRoot Q C) = 3 := by
    rw [card_cycleNodesOffRoot hcyc]; exact hsz
  have hvoff : v ∈ cycleNodesOffRoot Q C := mem_cycleNodesOffRoot.2 ⟨hvC, hvr⟩
  obtain ⟨w, w', hww', hWs⟩ := Finset.card_eq_two.1
    (show #((cycleNodesOffRoot Q C).erase v) = 2 by rw [card_erase_of_mem hvoff, hcard3])
  have hwm : w ∈ (cycleNodesOffRoot Q C).erase v := hWs ▸ mem_insert_self _ _
  have hw'm : w' ∈ (cycleNodesOffRoot Q C).erase v := hWs ▸ mem_insert_of_mem (mem_singleton_self _)
  obtain ⟨hwv, hwoff⟩ := mem_erase.1 hwm
  obtain ⟨hw'v, hw'off⟩ := mem_erase.1 hw'm
  obtain ⟨hwC, hwr⟩ := mem_cycleNodesOffRoot.1 hwoff
  obtain ⟨hw'C, hw'r⟩ := mem_cycleNodesOffRoot.1 hw'off
  have hCnodes : ∀ y ∈ cycleNodes Q.graph C, y ≠ r → y = v ∨ y = w ∨ y = w' := by
    intro y hy hyr
    by_cases hyv : y = v
    · exact Or.inl hyv
    have : y ∈ (cycleNodesOffRoot Q C).erase v :=
      mem_erase.2 ⟨hyv, mem_cycleNodesOffRoot.2 ⟨hy, hyr⟩⟩
    rw [hWs] at this
    simp only [mem_insert, mem_singleton] at this
    exact Or.inr this
  have hwl : ∀ x, Q.leaf x ≠ w := fun x h => hK.leaf_notMem x (h ▸ hwC)
  have hw'l : ∀ x, Q.leaf x ≠ w' := fun x h => hK.leaf_notMem x (h ▸ hw'C)
  have htreeW : ∀ y, y ≠ r → y ≠ v → (∀ x, Q.leaf x ≠ y) →
      Q.graph.indegree y = 1 ∧ Q.graph.outdegree y = 2 := by
    intro y hyr hyv hyl
    rcases hother y hyr (fun ⟨x, hx⟩ => hyl x hx) with h | h
    · exact h
    · exact absurd (huniq y (by omega)) hyv
  have hw1 := htreeW w hwr hwv hwl
  have hw'1 := htreeW w' hw'r hw'v hw'l
  have huw : u ≠ w := fun h => huC (h ▸ hwC)
  have huw' : u ≠ w' := fun h => huC (h ▸ hw'C)
  -- every node is the root, a leaf, `v`, `u`, `w` or `w'`
  have hNC : ∀ y, y = r ∨ (∃ x, Q.leaf x = y) ∨ y = v ∨ y = u ∨ y = w ∨ y = w' := by
    set S : Finset V := insert r (insert v (insert u (insert w (insert w' (univ.image Q.leaf)))))
    have hnl : ∀ y, (∀ x, Q.leaf x ≠ y) → y ∉ univ.image Q.leaf := fun y hy hm => by
      obtain ⟨x, -, hx⟩ := mem_image.1 hm
      exact hy x hx
    have hcS : #S = 9 := by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
        card_insert_of_notMem,
        card_insert_of_notMem (hnl w' hw'l), card_image_of_injective _ hinj, card_univ, hX]
      · simp only [mem_insert, not_or]; exact ⟨hww', hnl w hwl⟩
      · simp only [mem_insert, not_or]; exact ⟨huw, huw', hnl u hul⟩
      · simp only [mem_insert, not_or]; exact ⟨Ne.symm huv, Ne.symm hwv, Ne.symm hw'v, hnl v hvl⟩
      · simp only [mem_insert, not_or]
        exact ⟨Ne.symm hvr, Ne.symm hur, Ne.symm hwr, Ne.symm hw'r, hnl r hrl⟩
    have hSu : S = univ := eq_univ_of_card _ (by rw [hcS, hV])
    intro y
    have hy : y ∈ S := hSu ▸ mem_univ y
    simp only [S, mem_insert, mem_image, mem_univ, true_and] at hy
    rcases hy with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inl h)
  -- the parents of `a` and `b` are `u`
  have hbelow_src : ∀ g, Q.graph.Reaches v (Q.graph.target g) → Q.graph.target g ≠ v →
      Q.graph.target g ≠ u → Q.graph.source g = u := by
    intro g hg hgv hgu
    have hs := reaches_source_of_below_hybrid hB h1 hv2 hg hgv
    rcases hNC (Q.graph.source g) with h | ⟨x, hx⟩ | h | h | h | h
    · exact absurd (hreach_r v (h ▸ hs)) hvr
    · exact absurd hx.symm (hleafsrc x g)
    · exact absurd (by rw [hcvu g h]) hgu
    · exact h
    · exact absurd (h.symm.trans (eq_of_reaches_of_reaches hP.acyclic hs
        (reaches_hybrid hB h1 hcyc hvC hv2 _ (h ▸ hwC))).symm) hwv
    · exact absurd (h.symm.trans (eq_of_reaches_of_reaches hP.acyclic hs
        (reaches_hybrid hB h1 hcyc hvC hv2 _ (h ▸ hw'C))).symm) hw'v
  have hleafbelow : ∀ x, (x = a ∨ x = b) → Q.graph.Reaches v (Q.leaf x) := by
    rintro x hx
    have : x ∈ ({a, b} : Set X) := by rcases hx with rfl | rfl <;> simp
    rw [← hD] at this
    exact this
  obtain ⟨pa, hpa⟩ := hex_in _ (hleafdeg a).1
  obtain ⟨pb, hpb⟩ := hex_in _ (hleafdeg b).1
  have hpas : Q.graph.source pa = u := hbelow_src pa (hpa ▸ hleafbelow a (Or.inl rfl))
    (hpa ▸ hvl a) (hpa ▸ hul a)
  have hpbs : Q.graph.source pb = u := hbelow_src pb (hpb ▸ hleafbelow b (Or.inr rfl))
    (hpb ▸ hvl b) (hpb ▸ hul b)
  have hpapb : pa ≠ pb := fun h => hab (hinj (hpa.symm.trans (h ▸ hpb)))
  have hu_out : ∀ g, Q.graph.source g = u → g = pa ∨ g = pb := hout2 u hu1.2 pa pb hpapb hpas hpbs
  -- the two other taxa
  obtain ⟨c₀, d₀, hcd₀, hcd⟩ := Finset.card_eq_two.1
    (show #({a, b}ᶜ : Finset X) = 2 by rw [card_compl, card_pair hab, hX])
  have hc₀ : c₀ ∈ ({a, b}ᶜ : Finset X) := hcd ▸ mem_insert_self _ _
  have hd₀ : d₀ ∈ ({a, b}ᶜ : Finset X) := hcd ▸ mem_insert_of_mem (mem_singleton_self _)
  simp only [mem_compl, mem_insert, mem_singleton, not_or] at hc₀ hd₀
  have htaxa : ∀ x, x = a ∨ x = b ∨ x = c₀ ∨ x = d₀ := by
    intro x
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    have : x ∈ ({a, b}ᶜ : Finset X) := by simp [hxa, hxb]
    rw [hcd] at this
    simp only [mem_insert, mem_singleton] at this
    exact Or.inr (Or.inr this)
  -- the arcs into the leaves of the other taxa leave the root, `w` or `w'`
  have hleaf_src : ∀ x, x ≠ a → x ≠ b → ∀ g, Q.graph.target g = Q.leaf x →
      Q.graph.source g = r ∨ Q.graph.source g = w ∨ Q.graph.source g = w' := by
    intro x hxa hxb g hg
    rcases hNC (Q.graph.source g) with h | ⟨y, hy⟩ | h | h | h | h
    · exact Or.inl h
    · exact absurd hy.symm (hleafsrc y g)
    · exact absurd (hg.symm.trans (by rw [hcvu g h])) (hul x)
    · rcases hu_out g h with rfl | rfl
      · exact absurd (hinj (hg.symm.trans hpa)) hxa
      · exact absurd (hinj (hg.symm.trans hpb)) hxb
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- the arcs into the nodes
  have hXn := hQ.nontrivial
  have hrta := sdRootArc_spec hP hB.2 hXn
  rw [lsa_univ_eq_root hP hXn hQ.isLSA] at hrta
  have hin_v : ∀ g, Q.graph.target g = v → g = h₁ ∨ g = h₂ := hvin
  have hcv_in : ∀ g, Q.graph.target g = u → g = cv := fun g hg => hin1 u hu1.1 g cv hg rfl
  have hu_tgt : ∀ g, Q.graph.source g = u → ∃ x, Q.graph.target g = Q.leaf x ∧ (x = a ∨ x = b) :=
    fun g hg => by
      rcases hu_out g hg with rfl | rfl
      · exact ⟨a, hpa, Or.inl rfl⟩
      · exact ⟨b, hpb, Or.inr rfl⟩
  have hentry' : ∀ y ∈ cycleNodes Q.graph C, y ≠ t → ∀ g, Q.graph.target g = y → g ∈ C :=
    fun y hy hyt g hg => by
      by_contra hgC
      exact hyt (hg ▸ hK.entry g hgC (hg ▸ hy))
  have htv : t ≠ v := fun h => hK.top_entry h₁ (hth₁.trans h.symm) hh₁C
  -- **the isomorphism**, from the incidences of the arcs `α`
  have finish : ∀ (s : Fin 4) (c d : X) (Z Y : V) (α : Fin 9 → E),
      ((c = c₀ ∧ d = d₀) ∨ (c = d₀ ∧ d = c₀)) → ((Z = w ∧ Y = w') ∨ (Z = w' ∧ Y = w)) →
      (∀ j, Q.graph.source (α j) =
        (![Q.leaf a, Q.leaf b, Q.leaf c, Q.leaf d, u, v, Z, Y, r] : Fin 9 → V) (fig18RootSrc s j)) →
      (∀ j, Q.graph.target (α j) =
        (![Q.leaf a, Q.leaf b, Q.leaf c, Q.leaf d, u, v, Z, Y, r] : Fin 9 → V) (fig18RootTgt s j)) →
      α 6 ≠ α 7 → sdRootArc hP hB.2 hXn = α 8 →
      ∃ (c d : X) (_ : Distinct4 a b c d) (s : Fin 4)
        (φ : RootedNetworkIso (⟨⟨fig18RootSrc s, fig18RootTgt s⟩, 8, quartetLeaf9 a b c⟩ :
          RootedNetwork (Fin 9) (Fin 9) X) Q),
        (rootTreeArc hQ.binary.1 hQ.binary.2 hQ.nontrivial).1 = φ.arc 8 := by
    intro s c d Z Y α hcd' hZY hs ht h67 h8
    set n : Fin 9 → V := ![Q.leaf a, Q.leaf b, Q.leaf c, Q.leaf d, u, v, Z, Y, r] with hn_def
    have hd4 : Distinct4 a b c d := by
      rcases hcd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hab, Ne.symm hc₀.1, Ne.symm hd₀.1, Ne.symm hc₀.2, Ne.symm hd₀.2, hcd₀⟩
      · exact ⟨hab, Ne.symm hd₀.1, Ne.symm hc₀.1, Ne.symm hd₀.2, Ne.symm hc₀.2, Ne.symm hcd₀⟩
    have hleaf9 : ∀ x, Q.leaf x = n (quartetLeaf9 a b c x) := by
      intro x
      rcases htaxa x with rfl | rfl | rfl | rfl
      · rw [quartetLeaf9_a]; rfl
      · rw [quartetLeaf9_b hd4]; rfl
      · rcases hcd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [quartetLeaf9_c hd4]; rfl
        · rw [quartetLeaf9_d hd4]; rfl
      · rcases hcd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [quartetLeaf9_d hd4]; rfl
        · rw [quartetLeaf9_c hd4]; rfl
    have hn : ∀ y, ∃ i, n i = y := by
      intro y
      rcases hNC y with h | ⟨x, rfl⟩ | h | h | h | h
      · exact ⟨8, h.symm⟩
      · exact ⟨_, (hleaf9 x).symm⟩
      · exact ⟨5, h.symm⟩
      · exact ⟨4, h.symm⟩
      · rcases hZY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨6, h.symm⟩
        · exact ⟨7, h.symm⟩
      · rcases hZY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨7, h.symm⟩
        · exact ⟨6, h.symm⟩
    have hind : ∀ i : Fin 9, i ≠ 5 → i ≠ 8 → Q.graph.indegree (n i) = 1 := by
      have hZ1 : Q.graph.indegree Z = 1 := by
        rcases hZY with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact hw1.1
        · exact hw'1.1
      have hY1 : Q.graph.indegree Y = 1 := by
        rcases hZY with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact hw'1.1
        · exact hw1.1
      intro i h5 h8
      fin_cases i
      exacts [(hleafdeg a).1, (hleafdeg b).1, (hleafdeg c).1, (hleafdeg d).1, hu1.1,
        absurd rfl h5, hZ1, hY1, absurd rfl h8]
    have hα : ∀ g, ∃ j, α j = g := by
      intro g
      obtain ⟨i, hi⟩ := hn (Q.graph.target g)
      by_cases h5 : i = 5
      · subst h5
        have h6 : Q.graph.target (α 6) = v := by rw [ht]; fin_cases s <;> rfl
        have h7 : Q.graph.target (α 7) = v := by rw [ht]; fin_cases s <;> rfl
        rcases mem_pair_of_target_of_indegree_eq_two hv2 h67 h6 h7 g hi.symm with h | h
        · exact ⟨6, h.symm⟩
        · exact ⟨7, h.symm⟩
      by_cases h8' : i = 8
      · subst h8'
        exact absurd hi.symm (hnotr g)
      have key : ∀ s : Fin 4, ∀ i : Fin 9, i ≠ 5 → i ≠ 8 → ∃ j, fig18RootTgt s j = i := by decide
      obtain ⟨j, hj⟩ := key s i h5 h8'
      exact ⟨j, hin1 _ (hind i h5 h8') _ _ (by rw [ht, hj]) hi.symm⟩
    exact ⟨c, d, hd4, s, RootedNetworkIso.ofNine n α hn hα hV hE hs ht rfl hleaf9, h8⟩
  -- the arcs into leaves, and the taxa of the leaves
  have hleafT : ∀ g, Q.graph.target g ≠ v → Q.graph.target g ≠ u → Q.graph.target g ≠ w →
      Q.graph.target g ≠ w' → ∃ x, Q.graph.target g = Q.leaf x := by
    intro g h₁' h₂' h₃' h₄'
    rcases hNC (Q.graph.target g) with h | ⟨x, hx⟩ | h | h | h | h
    · exact absurd h (hnotr g)
    · exact ⟨x, hx.symm⟩
    all_goals contradiction
  have hnotab : ∀ g x, Q.graph.target g = Q.leaf x → Q.graph.source g ≠ u → x ≠ a ∧ x ≠ b := by
    intro g x hg hgs
    refine ⟨fun hxa => hgs ?_, fun hxb => hgs ?_⟩
    · subst hxa; rw [hin1 _ (hleafdeg x).1 g pa hg hpa]; exact hpas
    · subst hxb; rw [hin1 _ (hleafdeg x).1 g pb hg hpb]; exact hpbs
  have hcd_pair : ∀ c d, c ≠ d → c ≠ a → c ≠ b → d ≠ a → d ≠ b →
      (c = c₀ ∧ d = d₀) ∨ (c = d₀ ∧ d = c₀) := by
    intro c d hcd' hca hcb hda hdb
    rcases htaxa c with h | h | h | h
    · exact absurd h hca
    · exact absurd h hcb
    · rcases htaxa d with h' | h' | h' | h'
      · exact absurd h' hda
      · exact absurd h' hdb
      · exact absurd (h.trans h'.symm) hcd'
      · exact Or.inl ⟨h, h'⟩
    · rcases htaxa d with h' | h' | h' | h'
      · exact absurd h' hda
      · exact absurd h' hdb
      · exact Or.inr ⟨h, h'⟩
      · exact absurd (h.trans h'.symm) hcd'
  -- the facts on the two nodes `Z`, `Y` of the cycle other than `v` and the root
  have hZYfacts : ∀ Z Y, ((Z = w ∧ Y = w') ∨ (Z = w' ∧ Y = w)) →
      Z ≠ Y ∧ Z ∈ cycleNodes Q.graph C ∧ Y ∈ cycleNodes Q.graph C ∧ Z ≠ r ∧ Y ≠ r ∧ Z ≠ v ∧
        Y ≠ v ∧ Z ≠ u ∧ Y ≠ u ∧ (Q.graph.indegree Z = 1 ∧ Q.graph.outdegree Z = 2) ∧
        (Q.graph.indegree Y = 1 ∧ Q.graph.outdegree Y = 2) ∧
        (∀ y, (y = w ∨ y = w') ↔ (y = Z ∨ y = Y)) := by
    rintro Z Y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hww', hwC, hw'C, hwr, hw'r, hwv, hw'v, Ne.symm huw, Ne.symm huw', hw1, hw'1,
        fun y => Iff.rfl⟩
    · exact ⟨Ne.symm hww', hw'C, hwC, hw'r, hwr, hw'v, hwv, Ne.symm huw', Ne.symm huw, hw'1, hw1,
        fun y => or_comm⟩
  have hleafT' : ∀ Z Y, ((Z = w ∧ Y = w') ∨ (Z = w' ∧ Y = w)) → ∀ g, Q.graph.target g ≠ v →
      Q.graph.target g ≠ u → Q.graph.target g ≠ Z → Q.graph.target g ≠ Y →
      ∃ x, Q.graph.target g = Q.leaf x := by
    rintro Z Y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) g h₁' h₂' h₃' h₄'
    · exact hleafT g h₁' h₂' h₃' h₄'
    · exact hleafT g h₁' h₂' h₄' h₃'
  by_cases htr : t = r
  · -- the root is the top of the cycle
    have hrC : r ∈ cycleNodes Q.graph C := htr ▸ hK.top_mem
    have hrarc : ∀ g, Q.graph.source g = r → g ∈ C := fun g hg =>
      mem_of_source_eq_root hB hcyc hrC hg
    by_cases hA1 : Q.graph.source h₁ = r ∨ Q.graph.source h₂ = r
    · -- the root is a parent of `v`: the first rooting
      obtain ⟨hR, hO, hRO, hRt, hOt, hRs, hvRO⟩ : ∃ hR hO, hR ≠ hO ∧ Q.graph.target hR = v ∧
          Q.graph.target hO = v ∧ Q.graph.source hR = r ∧
          ∀ g, Q.graph.target g = v → g = hR ∨ g = hO := by
        rcases hA1 with h | h
        · exact ⟨h₁, h₂, hh₁₂, hth₁, hth₂, h, hvin⟩
        · exact ⟨h₂, h₁, Ne.symm hh₁₂, hth₂, hth₁, h, fun g hg => (hvin g hg).symm⟩
      have hOC : hO ∈ C := mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 hOt
      have hOs : Q.graph.source hO ≠ r := fun h =>
        hparallel hR hO hRO (hRs.trans h.symm) (hRt.trans hOt.symm)
      obtain ⟨g, hgR, hgs⟩ := hother_out r hr2 hR hRs
      have hrout : ∀ e, Q.graph.source e = r → e = hR ∨ e = g :=
        hout2 r hr2 hR g (Ne.symm hgR) hRs hgs
      have hgC := hrarc g hgs
      have hgv : Q.graph.target g ≠ v := fun h => by
        rcases hvRO g h with h' | h'
        · exact hgR h'
        · exact hOs (h' ▸ hgs)
      obtain ⟨Z, Y, hZY, hgY⟩ : ∃ Z Y, ((Z = w ∧ Y = w') ∨ (Z = w' ∧ Y = w)) ∧
          Q.graph.target g = Y := by
        rcases hCnodes _ (target_mem_cycleNodes hgC) (hnotr g) with h | h | h
        · exact absurd h hgv
        · exact ⟨w', w, Or.inr ⟨rfl, rfl⟩, h⟩
        · exact ⟨w, w', Or.inl ⟨rfl, rfl⟩, h⟩
      obtain ⟨hZY', hZC, hYC, hZr, hYr, hZv, hYv, hZu, hYu, hZ1, hY1, hW⟩ := hZYfacts Z Y hZY
      obtain ⟨pZ, hpZ⟩ := hex_in Z hZ1.1
      have hpZC := hentry' Z hZC (htr ▸ hZr) pZ hpZ
      have hpZs : Q.graph.source pZ = Y := by
        have hne : Q.graph.source pZ ≠ r := fun h => by
          rcases hrout pZ h with rfl | rfl
          · exact hZv (hpZ.symm.trans hRt)
          · exact hZY' (hpZ.symm.trans hgY)
        rcases hCnodes _ (source_mem_cycleNodes hpZC) hne with h | h | h
        · exact absurd (hpZ.symm.trans (by rw [hcvu pZ h])) hZu
        all_goals
          rcases (hW (Q.graph.source pZ)).1 (by first | exact Or.inl h | exact Or.inr h)
            with h' | h'
          · exact absurd (h'.trans hpZ.symm) (hloop pZ)
          · exact h'
      have hOs' : Q.graph.source hO = Z := by
        have hcase : Q.graph.source hO = Z ∨ Q.graph.source hO = Y := by
          rcases hCnodes _ (source_mem_cycleNodes hOC) hOs with h | h | h
          · exact absurd (h.trans hOt.symm) (hloop hO)
          all_goals exact (hW (Q.graph.source hO)).1 (by first | exact Or.inl h | exact Or.inr h)
        rcases hcase with h | h
        · exact h
        exfalso
        have hall : ∀ f ∈ C, (Q.graph.source f = Z ∨ Q.graph.target f = Z) → f = pZ := by
          intro f hfC hf
          rcases hf with hf | hf
          · rcases hCnodes _ (target_mem_cycleNodes hfC) (hnotr f) with h' | h' | h'
            · rcases hvRO f h' with rfl | rfl
              · exact absurd (hRs.symm.trans hf) (Ne.symm hZr)
              · exact absurd (h.symm.trans hf) (Ne.symm hZY')
            all_goals
              rcases (hW (Q.graph.target f)).1 (by first | exact Or.inl h' | exact Or.inr h')
                with h'' | h''
              · exact absurd (hf.trans h''.symm) (hloop f)
              · have := hin1 Y hY1.1 f g h'' hgY
                subst this
                exact absurd (hgs.symm.trans hf) (Ne.symm hZr)
          · exact hin1 Z hZ1.1 f pZ hf hpZ
        obtain ⟨f₁, hf₁, f₂, hf₂, hf12, hz₁, hz₂⟩ := hcyc.exists_ne_of_mem (fun g _ => hloop g) hZC
        exact hf12 ((hall f₁ hf₁ hz₁).trans (hall f₂ hf₂ hz₂).symm)
      obtain ⟨gY, hgYne, hgYs⟩ := hother_out Y hY1.2 pZ hpZs
      have hgYv : Q.graph.target gY ≠ v := fun h => by
        rcases hvRO gY h with rfl | rfl
        · exact hYr (hgYs.symm.trans hRs)
        · exact hZY' (hOs'.symm.trans hgYs)
      obtain ⟨d, hgYt⟩ := hleafT' Z Y hZY gY hgYv
        (fun h => hYv (hgYs.symm.trans (by rw [hcv_in gY h]; exact hcvs)))
        (fun h => hgYne (hin1 Z hZ1.1 gY pZ h hpZ)) (fun h => hloop gY (hgYs.trans h.symm))
      obtain ⟨hda, hdb⟩ := hnotab gY d hgYt (fun h => hYu (hgYs.symm.trans h))
      obtain ⟨gZ, hgZne, hgZs⟩ := hother_out Z hZ1.2 hO hOs'
      have hgZv : Q.graph.target gZ ≠ v := fun h => by
        rcases hvRO gZ h with rfl | rfl
        · exact hZr (hgZs.symm.trans hRs)
        · exact hgZne rfl
      obtain ⟨c, hgZt⟩ := hleafT' Z Y hZY gZ hgZv
        (fun h => hZv (hgZs.symm.trans (by rw [hcv_in gZ h]; exact hcvs)))
        (fun h => hloop gZ (hgZs.trans h.symm))
        (fun h => hZr (hgZs.symm.trans (by rw [hin1 Y hY1.1 gZ g h hgY]; exact hgs)))
      obtain ⟨hca, hcb⟩ := hnotab gZ c hgZt (fun h => hZu (hgZs.symm.trans h))
      have hcd' : c ≠ d := fun h => hZY' (hgZs.symm.trans (by
        rw [hin1 _ (hleafdeg d).1 gZ gY (h ▸ hgZt) hgYt]; exact hgYs))
      have h8 : sdRootArc hP hB.2 hXn = g := by
        rcases hrout _ hrta.1 with h | h
        · have ht1 := hrta.2
          unfold IsTreeArc at ht1
          rw [h, hRt, hv2] at ht1
          omega
        · exact h
      refine finish 0 c d Z Y ![pa, pb, gZ, gY, cv, pZ, hR, hO, g]
        (hcd_pair c d hcd' hca hcb hda hdb) hZY (fun j => ?_) (fun j => ?_) hRO h8
      · fin_cases j
        exacts [hpas, hpbs, hgZs, hgYs, hcvs, hpZs, hRs, hOs', hgs]
      · fin_cases j
        exacts [hpa, hpb, hgZt, hgYt, rfl, hpZ, hRt, hOt, hgY]
    · -- the root is not a parent of `v`: the second rooting
      push Not at hA1
      obtain ⟨g₁, g₂, hg12, hgs12⟩ := Set.ncard_eq_two.1 hr2
      have hg₁s : Q.graph.source g₁ = r := (Set.ext_iff.1 hgs12 g₁).2 (Set.mem_insert _ _)
      have hg₂s : Q.graph.source g₂ = r :=
        (Set.ext_iff.1 hgs12 g₂).2 (Set.mem_insert_of_mem _ rfl)
      have hrout : ∀ e, Q.graph.source e = r → e = g₁ ∨ e = g₂ := hout2 r hr2 g₁ g₂ hg12 hg₁s hg₂s
      -- the arc `g` of the root that the unrooted network merges, and the other one `g'`
      obtain ⟨g, g', hgg', hgs, hg's, hg8⟩ : ∃ g g', g ≠ g' ∧ Q.graph.source g = r ∧
          Q.graph.source g' = r ∧ sdRootArc hP hB.2 hXn = g := by
        rcases hrout _ hrta.1 with h | h
        · exact ⟨g₁, g₂, hg12, hg₁s, hg₂s, h⟩
        · exact ⟨g₂, g₁, Ne.symm hg12, hg₂s, hg₁s, h⟩
      have hrW : ∀ e, Q.graph.source e = r → Q.graph.target e = w ∨ Q.graph.target e = w' := by
        intro e he
        rcases hCnodes _ (target_mem_cycleNodes (hrarc e he)) (hnotr e) with h | h | h
        · rcases hvin e h with rfl | rfl
          · exact absurd he hA1.1
          · exact absurd he hA1.2
        · exact Or.inl h
        · exact Or.inr h
      have hgt : Q.graph.target g ≠ Q.graph.target g' := by
        intro h
        rcases hrW g hgs with h' | h'
        · exact hgg' (hin1 w hw1.1 g g' h' (h ▸ h'))
        · exact hgg' (hin1 w' hw'1.1 g g' h' (h ▸ h'))
      obtain ⟨Z, Y, hZY, hgY, hg'Z⟩ : ∃ Z Y, ((Z = w ∧ Y = w') ∨ (Z = w' ∧ Y = w)) ∧
          Q.graph.target g = Y ∧ Q.graph.target g' = Z := by
        rcases hrW g hgs with h | h <;> rcases hrW g' hg's with h' | h'
        · exact absurd (h.trans h'.symm) hgt
        · exact ⟨w', w, Or.inr ⟨rfl, rfl⟩, h, h'⟩
        · exact ⟨w, w', Or.inl ⟨rfl, rfl⟩, h, h'⟩
        · exact absurd (h.trans h'.symm) hgt
      obtain ⟨hZY', hZC, hYC, hZr, hYr, hZv, hYv, hZu, hYu, hZ1, hY1, hW⟩ := hZYfacts Z Y hZY
      have hsrcW : ∀ e, Q.graph.target e = v → Q.graph.source e = Z ∨ Q.graph.source e = Y := by
        intro e he
        have hne : Q.graph.source e ≠ r := by
          rcases hvin e he with rfl | rfl
          · exact hA1.1
          · exact hA1.2
        rcases hCnodes _ (source_mem_cycleNodes
          (mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 he)) hne with h | h | h
        · exact absurd (h.trans he.symm) (hloop e)
        all_goals exact (hW (Q.graph.source e)).1 (by first | exact Or.inl h | exact Or.inr h)
      obtain ⟨hY, hZ, hYZne, hYs, hZs, hYt, hZt, hvYZ⟩ : ∃ hY hZ, hY ≠ hZ ∧
          Q.graph.source hY = Y ∧ Q.graph.source hZ = Z ∧ Q.graph.target hY = v ∧
          Q.graph.target hZ = v ∧ ∀ e, Q.graph.target e = v → e = hY ∨ e = hZ := by
        rcases hsrcW h₁ hth₁ with h | h <;> rcases hsrcW h₂ hth₂ with h' | h'
        · exact absurd (h.trans h'.symm) hsh
        · exact ⟨h₂, h₁, Ne.symm hh₁₂, h', h, hth₂, hth₁, fun e he => (hvin e he).symm⟩
        · exact ⟨h₁, h₂, hh₁₂, h, h', hth₁, hth₂, hvin⟩
        · exact absurd (h.trans h'.symm) hsh
      obtain ⟨gY, hgYne, hgYs⟩ := hother_out Y hY1.2 hY hYs
      have hgYv : Q.graph.target gY ≠ v := fun h => by
        rcases hvYZ gY h with rfl | rfl
        · exact hgYne rfl
        · exact hZY' (hZs.symm.trans hgYs)
      obtain ⟨d, hgYt⟩ := hleafT' Z Y hZY gY hgYv
        (fun h => hYv (hgYs.symm.trans (by rw [hcv_in gY h]; exact hcvs)))
        (fun h => hYr (hgYs.symm.trans (by rw [hin1 Z hZ1.1 gY g' h hg'Z]; exact hg's)))
        (fun h => hloop gY (hgYs.trans h.symm))
      obtain ⟨hda, hdb⟩ := hnotab gY d hgYt (fun h => hYu (hgYs.symm.trans h))
      obtain ⟨gZ, hgZne, hgZs⟩ := hother_out Z hZ1.2 hZ hZs
      have hgZv : Q.graph.target gZ ≠ v := fun h => by
        rcases hvYZ gZ h with rfl | rfl
        · exact hZY' (hgZs.symm.trans hYs)
        · exact hgZne rfl
      obtain ⟨c, hgZt⟩ := hleafT' Z Y hZY gZ hgZv
        (fun h => hZv (hgZs.symm.trans (by rw [hcv_in gZ h]; exact hcvs)))
        (fun h => hloop gZ (hgZs.trans h.symm))
        (fun h => hZr (hgZs.symm.trans (by rw [hin1 Y hY1.1 gZ g h hgY]; exact hgs)))
      obtain ⟨hca, hcb⟩ := hnotab gZ c hgZt (fun h => hZu (hgZs.symm.trans h))
      have hcd' : c ≠ d := fun h => hZY' (hgZs.symm.trans (by
        rw [hin1 _ (hleafdeg d).1 gZ gY (h ▸ hgZt) hgYt]; exact hgYs))
      refine finish 1 c d Z Y ![pa, pb, gZ, gY, cv, g', hY, hZ, g]
        (hcd_pair c d hcd' hca hcb hda hdb) hZY (fun j => ?_) (fun j => ?_) hYZne hg8
      · fin_cases j
        exacts [hpas, hpbs, hgZs, hgYs, hcvs, hg's, hYs, hZs, hgs]
      · fin_cases j
        exacts [hpa, hpb, hgZt, hgYt, rfl, hg'Z, hYt, hZt, hgY]
  · -- the root is off the cycle: the third and the fourth rootings
    have hrC : r ∉ cycleNodes Q.graph C := fun h => htr (hreach_r t (hK.top_reaches r h))
    obtain ⟨Z, Y, hZY, htY⟩ : ∃ Z Y, ((Z = w ∧ Y = w') ∨ (Z = w' ∧ Y = w)) ∧ t = Y := by
      rcases hCnodes t hK.top_mem htr with h | h | h
      · exact absurd h htv
      · exact ⟨w', w, Or.inr ⟨rfl, rfl⟩, h⟩
      · exact ⟨w, w', Or.inl ⟨rfl, rfl⟩, h⟩
    subst htY
    obtain ⟨hZY', hZC, hYC, hZr, hYr, hZv, hYv, hZu, hYu, hZ1, hY1, hW⟩ := hZYfacts Z t hZY
    have hCr : ∀ y ∈ cycleNodes Q.graph C, y = v ∨ y = Z ∨ y = t := fun y hy => by
      rcases hCnodes y hy (fun h => hrC (h ▸ hy)) with h | h | h
      · exact Or.inl h
      all_goals exact Or.inr ((hW y).1 (by first | exact Or.inl h | exact Or.inr h))
    obtain ⟨pT, hpT⟩ := hex_in t hY1.1
    have hpTC : pT ∉ C := hK.top_entry pT hpT
    have hpTs : Q.graph.source pT = r := by
      rcases hNC (Q.graph.source pT) with h | ⟨x, hx⟩ | h | h | h | h
      · exact h
      · exact absurd hx.symm (hleafsrc x pT)
      · exact absurd (hpT.symm.trans (by rw [hcvu pT h])) hYu
      · obtain ⟨x, hx, -⟩ := hu_tgt pT h
        exact (hK.leaf_notMem x (by rw [← hx, hpT]; exact hK.top_mem)).elim
      all_goals
        rcases (hW (Q.graph.source pT)).1 (by first | exact Or.inl h | exact Or.inr h)
          with h' | h'
        · exact (hcy (hK.top_reaches Z hZC) ⟨pT, h', hpT⟩).elim
        · exact absurd (h'.trans hpT.symm) (hloop pT)
    obtain ⟨pX, hpX⟩ := hex_in Z hZ1.1
    have hpXC := hentry' Z hZC hZY' pX hpX
    have hpXs : Q.graph.source pX = t := by
      rcases hCr _ (source_mem_cycleNodes hpXC) with h | h | h
      · exact absurd (hpX.symm.trans (by rw [hcvu pX h])) hZu
      · exact absurd (h.trans hpX.symm) (hloop pX)
      · exact h
    obtain ⟨hT, hX', hTX, hTs, hXs, hTt, hXt, hvTX⟩ : ∃ hT hX', hT ≠ hX' ∧
        Q.graph.source hT = t ∧ Q.graph.source hX' = Z ∧ Q.graph.target hT = v ∧
        Q.graph.target hX' = v ∧ ∀ e, Q.graph.target e = v → e = hT ∨ e = hX' := by
      have hsrc : ∀ e, Q.graph.target e = v → Q.graph.source e = Z ∨ Q.graph.source e = t := by
        intro e he
        rcases hCr _ (source_mem_cycleNodes (mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 he))
          with h | h | h
        · exact absurd (h.trans he.symm) (hloop e)
        · exact Or.inl h
        · exact Or.inr h
      rcases hsrc h₁ hth₁ with h | h <;> rcases hsrc h₂ hth₂ with h' | h'
      · exact absurd (h.trans h'.symm) hsh
      · exact ⟨h₂, h₁, Ne.symm hh₁₂, h', h, hth₂, hth₁, fun e he => (hvin e he).symm⟩
      · exact ⟨h₁, h₂, hh₁₂, h, h', hth₁, hth₂, hvin⟩
      · exact absurd (h.trans h'.symm) hsh
    obtain ⟨gr, hgrne, hgrs⟩ := hother_out r hr2 pT hpTs
    have hrout : ∀ e, Q.graph.source e = r → e = pT ∨ e = gr :=
      hout2 r hr2 pT gr (Ne.symm hgrne) hpTs hgrs
    have hgrv : Q.graph.target gr ≠ v := fun h => by
      rcases hvTX gr h with rfl | rfl
      · exact hYr (hTs.symm.trans hgrs)
      · exact hZr (hXs.symm.trans hgrs)
    obtain ⟨d, hgrt⟩ := hleafT' Z t hZY gr hgrv
      (fun h => hvr (hcvs.symm.trans (by rw [← hcv_in gr h]; exact hgrs)))
      (fun h => hYr (hpXs.symm.trans (by rw [← hin1 Z hZ1.1 gr pX h hpX]; exact hgrs)))
      (fun h => hgrne (hin1 t hY1.1 gr pT h hpT))
    obtain ⟨hda, hdb⟩ := hnotab gr d hgrt (fun h => hur (h.symm.trans hgrs))
    obtain ⟨gX, hgXne, hgXs⟩ := hother_out Z hZ1.2 hX' hXs
    have hgXv : Q.graph.target gX ≠ v := fun h => by
      rcases hvTX gX h with rfl | rfl
      · exact hZY' (hgXs.symm.trans hTs)
      · exact hgXne rfl
    obtain ⟨c, hgXt⟩ := hleafT' Z t hZY gX hgXv
      (fun h => hZv (hgXs.symm.trans (by rw [hcv_in gX h]; exact hcvs)))
      (fun h => hloop gX (hgXs.trans h.symm))
      (fun h => hZr (hgXs.symm.trans (by rw [hin1 t hY1.1 gX pT h hpT]; exact hpTs)))
    obtain ⟨hca, hcb⟩ := hnotab gX c hgXt (fun h => hZu (hgXs.symm.trans h))
    have hcd' : c ≠ d := fun h => hZr (hgXs.symm.trans (by
      rw [hin1 _ (hleafdeg d).1 gX gr (h ▸ hgXt) hgrt]; exact hgrs))
    rcases hrout _ hrta.1 with h8 | h8
    · refine finish 2 c d Z t ![pa, pb, gX, gr, cv, pX, hT, hX', pT]
        (hcd_pair c d hcd' hca hcb hda hdb) hZY (fun j => ?_) (fun j => ?_) hTX h8
      · fin_cases j
        exacts [hpas, hpbs, hgXs, hgrs, hcvs, hpXs, hTs, hXs, hpTs]
      · fin_cases j
        exacts [hpa, hpb, hgXt, hgrt, rfl, hpX, hTt, hXt, hpT]
    · refine finish 3 c d Z t ![pa, pb, gX, pT, cv, pX, hT, hX', gr]
        (hcd_pair c d hcd' hca hcb hda hdb) hZY (fun j => ?_) (fun j => ?_) hTX h8
      · fin_cases j
        exacts [hpas, hpbs, hgXs, hpTs, hcvs, hpXs, hTs, hXs, hgrs]
      · fin_cases j
        exacts [hpa, hpb, hgXt, hpT, rfl, hpX, hTt, hXt, hgrt]

end SingleCycle

end Banos2019
