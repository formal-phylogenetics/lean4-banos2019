module

public import Banos2019.Quartet.SingleCycle

/-!
# LSA quartet networks with a single 4-cycle (proofs of Propositions 10 and 11)

An LSA quartet network `Q⊕` whose only cycle induces a `4₁`-cycle has nine nodes and nine arcs
(`card_eq_nine_of_single_hybrid`): the root, the four leaves, the hybrid node `v` and the three other
nodes of the cycle off the root. The child of `v` is the leaf of the taxon below `v`. Locating the arcs
from the top of the cycle shows that `Q⊕` is one of seven networks on `Fin 9`, the rootings of
Figure 17.

* `fig17RootSrc`, `fig17RootTgt`: the seven rootings of Figure 17 on `Fin 9`.
* `exists_rootedIso_fourOne`: with a single cycle, inducing a `4₁`-cycle, `Q⊕` is isomorphic to one of
  them, the arc of the root that the unrooted network merges being the edge `8`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

/-- The seven rootings of Figure 17 on `Fin 9`: the leaves `a, b, c, d` at `0, 1, 2, 3`, the nodes
`4, 5, 6, 7` of the cycle with `a, b, c, d`, `6` the hybrid node, the root `8`, and the edges `0, …, 7`
of the figure, the edge `8` being the arc of the root that the unrooted network merges into the other
arc of the root. The root is on the edge of `a` (the first two rootings), on the edge of `b` (the next
two), on the edge `t₂` from `4` to `5` (the next two), or on the hybrid edge from `5` to `6` (the last
one). -/
def fig17RootSrc : Fin 7 → Fin 9 → Fin 9 :=
  ![![8, 5, 6, 7, 4, 4, 5, 7, 8], ![8, 5, 6, 7, 4, 4, 5, 7, 8], ![4, 8, 6, 7, 4, 5, 5, 7, 8],
    ![4, 8, 6, 7, 4, 5, 5, 7, 8], ![4, 5, 6, 7, 4, 8, 5, 7, 8], ![4, 5, 6, 7, 4, 8, 5, 7, 8],
    ![4, 5, 6, 7, 4, 5, 8, 7, 8]]

/-- The heads of the edges of the seven rootings of Figure 17. -/
def fig17RootTgt : Fin 7 → Fin 9 → Fin 9 :=
  ![![0, 1, 2, 3, 7, 5, 6, 6, 4], ![4, 1, 2, 3, 7, 5, 6, 6, 0], ![0, 1, 2, 3, 7, 4, 6, 6, 5],
    ![0, 5, 2, 3, 7, 4, 6, 6, 1], ![0, 1, 2, 3, 7, 4, 6, 6, 5], ![0, 1, 2, 3, 7, 5, 6, 6, 4],
    ![0, 1, 2, 3, 7, 4, 6, 6, 5]]

section SingleFourCycle

variable {Q : RootedNetwork V E X} {θ : MetricData E} [DecidableEq X]

/-- **An LSA quartet network whose only cycle induces a `4₁`-cycle is a rooting of Figure 17**, with
the arc that its unrooted network merges at the root as the edge `8`. The child of the hybrid node `v`
is the leaf of the taxon `c` below it; the other nodes of the cycle are tree nodes, each the parent of a
leaf, but for the top of the cycle when the root is its parent. When the root is off the cycle, it is
the parent of the top and of a leaf, and the top is a parent of `v` or not; when it is on the cycle, it
is a parent of `v` or not. -/
theorem exists_rootedIso_fourOne (hQ : IsLSAQuartet Q θ) {C : Set E} {v : V}
    (hC : InducesCycleType Q C v 4 1) (hone : ∀ C', IsCycle Q.graph C' → C' = C) :
    ∃ (a b c d : X) (_ : Distinct4 a b c d) (s : Fin 7)
      (φ : RootedNetworkIso (⟨⟨fig17RootSrc s, fig17RootTgt s⟩, 8, quartetLeaf9 a b c⟩ :
        RootedNetwork (Fin 9) (Fin 9) X) Q),
      (rootTreeArc hQ.binary.1 hQ.binary.2 hQ.nontrivial).1 = φ.arc 8 := by
  have hB := hQ.binary
  have hP := hB.1
  have h1 := hQ.levelOne
  have hX := hQ.card_taxa
  obtain ⟨hcyc, hvC, hv2, hsz, hk⟩ := hC
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
  obtain ⟨t, hK⟩ := isContractible_of_cycle hB h1 hcyc hvC hv2
  have hentry' : ∀ y ∈ cycleNodes Q.graph C, y ≠ t → ∀ g, Q.graph.target g = y → g ∈ C :=
    fun y hy hyt g hg => by
      by_contra hgC
      exact hyt (hg ▸ hK.entry g hgC (hg ▸ hy))
  -- the nodes `W` of the cycle other than the root and `v`: three tree nodes
  set W : V → Prop := fun y => y ∈ cycleNodes Q.graph C ∧ y ≠ r ∧ y ≠ v with hW_def
  have hcard4 : #(cycleNodesOffRoot Q C) = 4 := by
    rw [card_cycleNodesOffRoot hcyc]; exact hsz
  have hvoff : v ∈ cycleNodesOffRoot Q C := mem_cycleNodesOffRoot.2 ⟨hvC, hvr⟩
  have hW3 : #((cycleNodesOffRoot Q C).erase v) = 3 := by
    rw [card_erase_of_mem hvoff, hcard4]
  have hmemW : ∀ y, W y → y ∈ (cycleNodesOffRoot Q C).erase v := fun y hy =>
    mem_erase.2 ⟨hy.2.2, mem_cycleNodesOffRoot.2 ⟨hy.1, hy.2.1⟩⟩
  have hWof : ∀ y ∈ (cycleNodesOffRoot Q C).erase v, W y := fun y hy => by
    obtain ⟨hyv, hy'⟩ := mem_erase.1 hy
    obtain ⟨hyC, hyr⟩ := mem_cycleNodesOffRoot.1 hy'
    exact ⟨hyC, hyr, hyv⟩
  have hWn3 : ∀ n₁ n₂ n₃, W n₁ → W n₂ → W n₃ → n₁ ≠ n₂ → n₁ ≠ n₃ → n₂ ≠ n₃ →
      ∀ y, W y → y = n₁ ∨ y = n₂ ∨ y = n₃ := by
    intro n₁ n₂ n₃ w₁ w₂ w₃ h12 h13 h23 y hy
    by_contra hne
    push Not at hne
    have hsub : ({y, n₁, n₂, n₃} : Finset V) ⊆ (cycleNodesOffRoot Q C).erase v := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      exacts [hmemW _ hy, hmemW _ w₁, hmemW _ w₂, hmemW _ w₃]
    have := card_le_card hsub
    rw [hW3, card_insert_of_notMem (by simp [hne.1, hne.2.1, hne.2.2]),
      card_insert_of_notMem (by simp [h12, h13]), card_pair h23] at this
    omega
  have hWthird : ∀ n₁ n₂, ∃ z, W z ∧ z ≠ n₁ ∧ z ≠ n₂ := by
    intro n₁ n₂
    obtain ⟨z, hz⟩ : ((((cycleNodesOffRoot Q C).erase v).erase n₁).erase n₂).Nonempty := by
      rw [← card_pos]
      have := pred_card_le_card_erase (s := (cycleNodesOffRoot Q C).erase v) (a := n₁)
      have := pred_card_le_card_erase (s := ((cycleNodesOffRoot Q C).erase v).erase n₁) (a := n₂)
      omega
    exact ⟨z, hWof z (mem_of_mem_erase (mem_of_mem_erase hz)),
      ne_of_mem_erase (mem_of_mem_erase hz), ne_of_mem_erase hz⟩
  have hWl : ∀ y, W y → ∀ x, Q.leaf x ≠ y := fun y hy x h => hK.leaf_notMem x (h ▸ hy.1)
  have hWdeg : ∀ y, W y → Q.graph.indegree y = 1 ∧ Q.graph.outdegree y = 2 := by
    intro y hy
    rcases hother y hy.2.1 (fun ⟨x, hx⟩ => hWl y hy x hx) with h | h
    · exact h
    · exact absurd (huniq y (by omega)) hy.2.2
  -- every node is the root, a leaf, `v` or a node of `W`
  have hNC : ∀ y, y = r ∨ (∃ x, Q.leaf x = y) ∨ y = v ∨ W y := by
    set S : Finset V := insert r (insert v ((cycleNodesOffRoot Q C).erase v ∪ univ.image Q.leaf))
    have hdisj : Disjoint ((cycleNodesOffRoot Q C).erase v) (univ.image Q.leaf) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hy'
      exact hWl _ (hWof _ hy) x rfl
    have hvS : v ∉ (cycleNodesOffRoot Q C).erase v ∪ univ.image Q.leaf := by
      rw [mem_union, not_or]
      refine ⟨fun h => (mem_erase.1 h).1 rfl, fun h => ?_⟩
      obtain ⟨x, -, hx⟩ := mem_image.1 h
      exact hvl x hx
    have hrS : r ∉ insert v ((cycleNodesOffRoot Q C).erase v ∪ univ.image Q.leaf) := by
      rw [mem_insert, mem_union, not_or, not_or]
      refine ⟨Ne.symm hvr, fun h => (mem_cycleNodesOffRoot.1 (mem_of_mem_erase h)).2 rfl,
        fun h => ?_⟩
      obtain ⟨x, -, hx⟩ := mem_image.1 h
      exact hrl x hx
    have hcS : #S = 9 := by
      rw [card_insert_of_notMem hrS, card_insert_of_notMem hvS, card_union_of_disjoint hdisj, hW3,
        card_image_of_injective _ hinj, card_univ, hX]
    have hSu : S = univ := eq_univ_of_card _ (by rw [hcS, hV])
    intro y
    have hy : y ∈ S := hSu ▸ mem_univ y
    rcases mem_insert.1 hy with h | hy
    · exact Or.inl h
    rcases mem_insert.1 hy with h | hy
    · exact Or.inr (Or.inr (Or.inl h))
    rcases mem_union.1 hy with h | h
    · exact Or.inr (Or.inr (Or.inr (hWof y h)))
    · obtain ⟨x, -, hx⟩ := mem_image.1 h
      exact Or.inr (Or.inl ⟨x, hx⟩)
  -- the child of `v` is the leaf of the taxon `c` below `v`
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 hk
  have hcvt : Q.graph.target cv = Q.leaf c := by
    have huC : Q.graph.target cv ∉ cycleNodes Q.graph C := fun h =>
      hcy (reaches_hybrid hB h1 hcyc hvC hv2 _ h) ⟨cv, hcvs, rfl⟩
    rcases hNC (Q.graph.target cv) with h | ⟨x, hx⟩ | h | h
    · exact absurd h (hnotr cv)
    · have hx' : x ∈ {x | Q.graph.Reaches v (Q.leaf x)} := by
        show Q.graph.Reaches v (Q.leaf x)
        rw [hx]
        exact .single ⟨cv, hcvs, rfl⟩
      rw [hc, Set.mem_singleton_iff] at hx'
      rw [← hx, hx']
    · exact absurd (hcvs.trans h.symm) (hloop cv)
    · exact absurd h.1 huC
  have hcin : ∀ g, Q.graph.target g = Q.leaf c → g = cv := fun g hg =>
    hin1 _ (hleafdeg c).1 g cv hg hcvt
  have hne_taxa : ∀ g g' x x', Q.graph.target g = Q.leaf x → Q.graph.target g' = Q.leaf x' →
      Q.graph.source g ≠ Q.graph.source g' → x ≠ x' := fun g g' x x' hg hg' hne hxx =>
    hne (by rw [hin1 _ (hleafdeg x).1 g g' hg (hxx ▸ hg')])
  have hne_c : ∀ g x, Q.graph.target g = Q.leaf x → Q.graph.source g ≠ v → x ≠ c :=
    fun g x hg hs hxc => hs (by rw [hcin g (hxc ▸ hg)]; exact hcvs)
  -- the arcs of the cycle at a node: two
  have htwoC : ∀ y e₁ e₂ e₃, e₁ ∈ C → e₂ ∈ C → e₃ ∈ C → e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
      (Q.graph.source e₁ = y ∨ Q.graph.target e₁ = y) →
      (Q.graph.source e₂ = y ∨ Q.graph.target e₂ = y) →
      (Q.graph.source e₃ = y ∨ Q.graph.target e₃ = y) → False := by
    intro y e₁ e₂ e₃ m₁ m₂ m₃ h12 h13 h23 i₁ i₂ i₃
    have h2 := hcyc.ncard_incident hloop ⟨e₁, m₁, i₁⟩
    have hsub : ({e₁, e₂, e₃} : Set E) ⊆
        {e | e ∈ C ∧ (Q.graph.source e = y ∨ Q.graph.target e = y)} := by
      rintro e (rfl | rfl | rfl)
      exacts [⟨m₁, i₁⟩, ⟨m₂, i₂⟩, ⟨m₃, i₃⟩]
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem (by simp [h12, h13]), Set.ncard_pair h23, h2] at h3
    omega
  -- an arc of the cycle out of a node of `W` other than the top
  have houtC : ∀ y, W y → y ≠ t → ∃ k ∈ C, Q.graph.source k = y := by
    intro y hy hyt
    obtain ⟨f₁, hf₁, f₂, hf₂, hne, i₁, i₂⟩ := hcyc.exists_ne_of_mem (fun g _ => hloop g) hy.1
    rcases i₁ with i₁ | i₁
    · exact ⟨f₁, hf₁, i₁⟩
    rcases i₂ with i₂ | i₂
    · exact ⟨f₂, hf₂, i₂⟩
    exact absurd (hin1 y (hWdeg y hy).1 f₁ f₂ i₁ i₂) hne
  -- the source of the arc into a node of `W` other than the top
  have hWin : ∀ y, W y → y ≠ t → ∀ k, Q.graph.target k = y →
      k ∈ C ∧ (Q.graph.source k = r ∨ W (Q.graph.source k)) := by
    intro y hy hyt k hk
    have hkC := hentry' y hy.1 hyt k hk
    refine ⟨hkC, ?_⟩
    by_cases hsr : Q.graph.source k = r
    · exact Or.inl hsr
    refine Or.inr ⟨source_mem_cycleNodes hkC, hsr, fun hsv => ?_⟩
    rw [hcvu k hsv, hcvt] at hk
    exact hWl y hy c hk
  -- the target of an arc of the cycle
  have hCtgt : ∀ k ∈ C, Q.graph.target k = v ∨ W (Q.graph.target k) := fun k hk => by
    by_cases h : Q.graph.target k = v
    · exact Or.inl h
    · exact Or.inr ⟨target_mem_cycleNodes hk, hnotr k, h⟩
  -- an arc into a node that is not `v` nor in `W` enters a leaf
  have hleaf3 : ∀ n₁ n₂ n₃, W n₁ → W n₂ → W n₃ → n₁ ≠ n₂ → n₁ ≠ n₃ → n₂ ≠ n₃ → ∀ g,
      Q.graph.target g ≠ v → Q.graph.target g ≠ n₁ → Q.graph.target g ≠ n₂ →
      Q.graph.target g ≠ n₃ → ∃ x, Q.graph.target g = Q.leaf x := by
    intro n₁ n₂ n₃ w₁ w₂ w₃ h12 h13 h23 g hv' h₁' h₂' h₃'
    rcases hNC (Q.graph.target g) with h | ⟨x, hx⟩ | h | h
    · exact absurd h (hnotr g)
    · exact ⟨x, hx.symm⟩
    · exact absurd h hv'
    · rcases hWn3 n₁ n₂ n₃ w₁ w₂ w₃ h12 h13 h23 _ h with h' | h' | h'
      exacts [absurd h' h₁', absurd h' h₂', absurd h' h₃']
  have hXn := hQ.nontrivial
  have hrta := sdRootArc_spec hP hB.2 hXn
  rw [lsa_univ_eq_root hP hXn hQ.isLSA] at hrta
  -- **the isomorphism**, from the incidences of the arcs `α`
  have finish : ∀ (s : Fin 7) (a b d : X) (n₄ n₅ n₇ : V) (α : Fin 9 → E),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      W n₄ → W n₅ → W n₇ → n₄ ≠ n₅ → n₄ ≠ n₇ → n₅ ≠ n₇ →
      (∀ j, Q.graph.source (α j) =
        (![Q.leaf a, Q.leaf b, Q.leaf c, Q.leaf d, n₄, n₅, v, n₇, r] : Fin 9 → V)
          (fig17RootSrc s j)) →
      (∀ j, Q.graph.target (α j) =
        (![Q.leaf a, Q.leaf b, Q.leaf c, Q.leaf d, n₄, n₅, v, n₇, r] : Fin 9 → V)
          (fig17RootTgt s j)) →
      α 6 ≠ α 7 → sdRootArc hP hB.2 hXn = α 8 →
      ∃ (a b c d : X) (_ : Distinct4 a b c d) (s : Fin 7)
        (φ : RootedNetworkIso (⟨⟨fig17RootSrc s, fig17RootTgt s⟩, 8, quartetLeaf9 a b c⟩ :
          RootedNetwork (Fin 9) (Fin 9) X) Q),
        (rootTreeArc hQ.binary.1 hQ.binary.2 hQ.nontrivial).1 = φ.arc 8 := by
    intro s a b d n₄ n₅ n₇ α hab hac had hbc hbd hcd w₄ w₅ w₇ h45 h47 h57 hs ht h67 h8
    set n : Fin 9 → V := ![Q.leaf a, Q.leaf b, Q.leaf c, Q.leaf d, n₄, n₅, v, n₇, r] with hn_def
    have hd4 : Distinct4 a b c d := ⟨hab, hac, had, hbc, hbd, hcd⟩
    have htaxa : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d := by
      intro x
      by_contra hx
      push Not at hx
      have h5 : #({x, a, b, c, d} : Finset X) = 5 := by
        rw [card_insert_of_notMem (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]),
          card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
          card_pair hcd]
      have := card_le_univ ({x, a, b, c, d} : Finset X)
      omega
    have hleaf9 : ∀ x, Q.leaf x = n (quartetLeaf9 a b c x) := by
      intro x
      rcases htaxa x with rfl | rfl | rfl | rfl
      · rw [quartetLeaf9_a]; rfl
      · rw [quartetLeaf9_b hd4]; rfl
      · rw [quartetLeaf9_c hd4]; rfl
      · rw [quartetLeaf9_d hd4]; rfl
    have hn : ∀ y, ∃ i, n i = y := by
      intro y
      rcases hNC y with h | ⟨x, rfl⟩ | h | h
      · exact ⟨8, h.symm⟩
      · exact ⟨_, (hleaf9 x).symm⟩
      · exact ⟨6, h.symm⟩
      · rcases hWn3 n₄ n₅ n₇ w₄ w₅ w₇ h45 h47 h57 y h with h' | h' | h'
        · exact ⟨4, h'.symm⟩
        · exact ⟨5, h'.symm⟩
        · exact ⟨7, h'.symm⟩
    have hind : ∀ i : Fin 9, i ≠ 6 → i ≠ 8 → Q.graph.indegree (n i) = 1 := by
      intro i h6 h8
      fin_cases i
      exacts [(hleafdeg a).1, (hleafdeg b).1, (hleafdeg c).1, (hleafdeg d).1, (hWdeg _ w₄).1,
        (hWdeg _ w₅).1, absurd rfl h6, (hWdeg _ w₇).1, absurd rfl h8]
    have hα : ∀ g, ∃ j, α j = g := by
      intro g
      obtain ⟨i, hi⟩ := hn (Q.graph.target g)
      by_cases h6 : i = 6
      · subst h6
        have h6' : Q.graph.target (α 6) = v := by rw [ht]; fin_cases s <;> rfl
        have h7' : Q.graph.target (α 7) = v := by rw [ht]; fin_cases s <;> rfl
        rcases mem_pair_of_target_of_indegree_eq_two hv2 h67 h6' h7' g hi.symm with h | h
        · exact ⟨6, h.symm⟩
        · exact ⟨7, h.symm⟩
      by_cases h8' : i = 8
      · subst h8'
        exact absurd hi.symm (hnotr g)
      have key : ∀ s : Fin 7, ∀ i : Fin 9, i ≠ 6 → i ≠ 8 → ∃ j, fig17RootTgt s j = i := by decide
      obtain ⟨j, hj⟩ := key s i h6 h8'
      exact ⟨j, hin1 _ (hind i h6 h8') _ _ (by rw [ht, hj]) hi.symm⟩
    exact ⟨a, b, c, d, hd4, s, RootedNetworkIso.ofNine n α hn hα hV hE hs ht rfl hleaf9, h8⟩
  by_cases hpr : Q.graph.source h₁ = r ∨ Q.graph.source h₂ = r
  · -- the root is a parent of `v`: the last rooting
    obtain ⟨hR, hO, hRO, hRt, hOt, hRs, hvRO⟩ : ∃ hR hO, hR ≠ hO ∧ Q.graph.target hR = v ∧
        Q.graph.target hO = v ∧ Q.graph.source hR = r ∧
        ∀ g, Q.graph.target g = v → g = hR ∨ g = hO := by
      rcases hpr with h | h
      · exact ⟨h₁, h₂, hh₁₂, hth₁, hth₂, h, hvin⟩
      · exact ⟨h₂, h₁, Ne.symm hh₁₂, hth₂, hth₁, h, fun g hg => (hvin g hg).symm⟩
    have hRC : hR ∈ C := mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 hRt
    have hOC : hO ∈ C := mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 hOt
    set pO := Q.graph.source hO with hpO
    have hOs : pO ≠ r := fun h => hparallel hR hO hRO (hRs.trans h.symm) (hRt.trans hOt.symm)
    have hrC : r ∈ cycleNodes Q.graph C := ⟨hR, hRC, Or.inl hRs⟩
    have htr : t = r := hreach_r t (hK.top_reaches r hrC)
    have hWt : ∀ y, W y → y ≠ t := fun y hy h => hy.2.1 (h.trans htr)
    have hWO : W pO := ⟨source_mem_cycleNodes hOC, hOs, fun h => hloop hO (h.trans hOt.symm)⟩
    obtain ⟨g, hgR, hgs⟩ := hother_out r hr2 hR hRs
    have hrout : ∀ e, Q.graph.source e = r → e = hR ∨ e = g :=
      hout2 r hr2 hR g (Ne.symm hgR) hRs hgs
    have hgC : g ∈ C := mem_of_source_eq_root hB hcyc hrC hgs
    set z₁ := Q.graph.target g with hz₁
    have hgv : z₁ ≠ v := fun h => by
      rcases hvRO g h with h' | h'
      · exact hgR h'
      · exact hOs (by rw [hpO, ← h']; exact hgs)
    have hW₁ : W z₁ := ⟨target_mem_cycleNodes hgC, hnotr g, hgv⟩
    -- the source of an arc of the cycle into a node of `W` other than `z₁`
    have hsrcW : ∀ y, W y → y ≠ z₁ → ∀ k, Q.graph.target k = y → k ∈ C ∧ W (Q.graph.source k) := by
      intro y hy hyz k hk
      obtain ⟨hkC, h | h⟩ := hWin y hy (hWt y hy) k hk
      · rcases hrout k h with rfl | rfl
        · exact absurd (hk.symm.trans hRt) hy.2.2
        · exact absurd hk.symm hyz
      · exact ⟨hkC, h⟩
    -- `z₁` is not `pO`: otherwise the two other nodes of `W` would be each other's parents
    have hz₁O : z₁ ≠ pO := by
      intro hzO
      obtain ⟨x, hWx, hxO, -⟩ := hWthird pO pO
      obtain ⟨kx, hkx⟩ := hex_in x (hWdeg x hWx).1
      obtain ⟨hkxC, hWy⟩ := hsrcW x hWx (hzO ▸ hxO) kx hkx
      set y := Q.graph.source kx
      have hyO : y ≠ pO := fun h => htwoC pO g hO kx hgC hOC hkxC
        (fun h' => hOs (by rw [hpO, ← h']; exact hgs))
        (fun h' => hxO (by rw [← hkx, ← h', ← hz₁, hzO]))
        (fun h' => hWx.2.2 (by rw [← hkx, ← h', hOt])) (Or.inr hzO) (Or.inl rfl) (Or.inl h)
      have hyx : y ≠ x := fun h => hloop kx (h.trans hkx.symm)
      obtain ⟨ky, hky⟩ := hex_in y (hWdeg y hWy).1
      obtain ⟨hkyC, hWy'⟩ := hsrcW y hWy (hzO ▸ hyO) ky hky
      have hy'O : Q.graph.source ky ≠ pO := fun h => htwoC pO g hO ky hgC hOC hkyC
        (fun h' => hOs (by rw [hpO, ← h']; exact hgs))
        (fun h' => hyO (by rw [← hky, ← h', ← hz₁, hzO]))
        (fun h' => hWy.2.2 (by rw [← hky, ← h', hOt])) (Or.inr hzO) (Or.inl rfl) (Or.inl h)
      rcases hWn3 pO x y hWO hWx hWy (Ne.symm hxO) (Ne.symm hyO) (Ne.symm hyx) _ hWy'
        with h | h | h
      · exact hy'O h
      · exact hcy (.single ⟨ky, h, hky⟩) ⟨kx, rfl, hkx⟩
      · exact hloop ky (h.trans hky.symm)
    obtain ⟨z₂, hW₂, hz₂O, hz₂₁⟩ := hWthird pO z₁
    -- the arc of the cycle out of `z₁` enters `z₂`
    obtain ⟨k₁, hk₁C, hk₁s⟩ := houtC z₁ hW₁ (hWt z₁ hW₁)
    have hk₁t : Q.graph.target k₁ = z₂ := by
      rcases hCtgt k₁ hk₁C with h | h
      · rcases hvRO k₁ h with rfl | rfl
        · exact absurd (hk₁s.symm.trans hRs) hW₁.2.1
        · exact absurd hk₁s.symm hz₁O
      rcases hWn3 pO z₁ z₂ hWO hW₁ hW₂ (Ne.symm hz₁O) (Ne.symm hz₂O) (Ne.symm hz₂₁) _ h
        with h' | h' | h'
      · exfalso
        -- then the arc into `z₂` leaves no node
        obtain ⟨k, hk⟩ := hex_in z₂ (hWdeg z₂ hW₂).1
        obtain ⟨hkC, hWk⟩ := hsrcW z₂ hW₂ hz₂₁ k hk
        rcases hWn3 pO z₁ z₂ hWO hW₁ hW₂ (Ne.symm hz₁O) (Ne.symm hz₂O) (Ne.symm hz₂₁) _ hWk
          with h'' | h'' | h''
        · exact htwoC pO k₁ hO k hk₁C hOC hkC
            (fun he => hz₁O (by rw [← hk₁s, he]))
            (fun he => hz₂O (by rw [← hk, ← he, h']))
            (fun he => hW₂.2.2 (by rw [← hk, ← he, hOt])) (Or.inr h') (Or.inl rfl) (Or.inl h'')
        · exact htwoC z₁ g k₁ k hgC hk₁C hkC
            (fun he => hW₁.2.1 (by rw [← hk₁s, ← he, hgs]))
            (fun he => hW₁.2.1 (by rw [← h'', ← he, hgs]))
            (fun he => hz₂O (by rw [← hk, ← he, h']))
            (Or.inr rfl) (Or.inl hk₁s) (Or.inl h'')
        · exact hloop k (h''.trans hk.symm)
      · exact absurd (hk₁s.trans h'.symm) (hloop k₁)
      · exact h'
    -- the arc of the cycle out of `z₂` enters `pO`
    obtain ⟨k₂, hk₂C, hk₂s⟩ := houtC z₂ hW₂ (hWt z₂ hW₂)
    have hk₂t : Q.graph.target k₂ = pO := by
      rcases hCtgt k₂ hk₂C with h | h
      · rcases hvRO k₂ h with rfl | rfl
        · exact absurd (hk₂s.symm.trans hRs) hW₂.2.1
        · exact absurd hk₂s.symm hz₂O
      rcases hWn3 pO z₁ z₂ hWO hW₁ hW₂ (Ne.symm hz₁O) (Ne.symm hz₂O) (Ne.symm hz₂₁) _ h
        with h' | h' | h'
      · exact h'
      · have := hin1 z₁ (hWdeg z₁ hW₁).1 k₂ g h' rfl
        subst this
        exact absurd (hk₂s.symm.trans hgs) hW₂.2.1
      · exact absurd (hk₂s.trans h'.symm) (hloop k₂)
    -- the leaves
    have hinO : ∀ e, Q.graph.target e = pO → e = k₂ := fun e he =>
      hin1 pO (hWdeg pO hWO).1 e k₂ he hk₂t
    have hin₁ : ∀ e, Q.graph.target e = z₁ → e = g := fun e he =>
      hin1 z₁ (hWdeg z₁ hW₁).1 e g he rfl
    have hin₂ : ∀ e, Q.graph.target e = z₂ → e = k₁ := fun e he =>
      hin1 z₂ (hWdeg z₂ hW₂).1 e k₁ he hk₁t
    obtain ⟨ga, hgak, hgas⟩ := hother_out z₂ (hWdeg z₂ hW₂).2 k₂ hk₂s
    obtain ⟨a, hgat⟩ := hleaf3 pO z₁ z₂ hWO hW₁ hW₂ (Ne.symm hz₁O) (Ne.symm hz₂O) (Ne.symm hz₂₁) ga
      (fun h => by
        rcases hvRO ga h with rfl | rfl
        · exact hW₂.2.1 (hgas.symm.trans hRs)
        · exact hz₂O hgas.symm)
      (fun h => hgak (hinO ga h))
      (fun h => hW₂.2.1 (by rw [← hgas, hin₁ ga h, hgs]))
      (fun h => hloop ga (hgas.trans h.symm))
    obtain ⟨gb, hgbk, hgbs⟩ := hother_out z₁ (hWdeg z₁ hW₁).2 k₁ hk₁s
    obtain ⟨b, hgbt⟩ := hleaf3 pO z₁ z₂ hWO hW₁ hW₂ (Ne.symm hz₁O) (Ne.symm hz₂O) (Ne.symm hz₂₁) gb
      (fun h => by
        rcases hvRO gb h with rfl | rfl
        · exact hW₁.2.1 (hgbs.symm.trans hRs)
        · exact hz₁O hgbs.symm)
      (fun h => hz₂₁ (by rw [← hk₂s, ← hinO gb h, hgbs]))
      (fun h => hloop gb (hgbs.trans h.symm))
      (fun h => hgbk (hin₂ gb h))
    obtain ⟨gd, hgdk, hgds⟩ := hother_out pO (hWdeg pO hWO).2 hO rfl
    obtain ⟨d, hgdt⟩ := hleaf3 pO z₁ z₂ hWO hW₁ hW₂ (Ne.symm hz₁O) (Ne.symm hz₂O) (Ne.symm hz₂₁) gd
      (fun h => by
        rcases hvRO gd h with rfl | rfl
        · exact hOs (hgds.symm.trans hRs)
        · exact hgdk rfl)
      (fun h => hloop gd (hgds.trans h.symm))
      (fun h => hOs (by rw [← hgds, hin₁ gd h, hgs]))
      (fun h => hz₁O (by rw [← hk₁s, ← hin₂ gd h, hgds]))
    have h8 : sdRootArc hP hB.2 hXn = g := by
      rcases hrout _ hrta.1 with h | h
      · have ht1 := hrta.2
        unfold IsTreeArc at ht1
        rw [h, hRt, hv2] at ht1
        omega
      · exact h
    refine finish 6 a b d z₂ z₁ pO ![ga, gb, cv, gd, k₂, k₁, hR, hO, g]
      (hne_taxa ga gb a b hgat hgbt (by rw [hgas, hgbs]; exact hz₂₁))
      (hne_c ga a hgat (by rw [hgas]; exact hW₂.2.2))
      (hne_taxa ga gd a d hgat hgdt (by rw [hgas, hgds]; exact hz₂O))
      (hne_c gb b hgbt (by rw [hgbs]; exact hW₁.2.2))
      (hne_taxa gb gd b d hgbt hgdt (by rw [hgbs, hgds]; exact hz₁O))
      (fun h => hne_c gd d hgdt (by rw [hgds]; exact hWO.2.2) h.symm)
      hW₂ hW₁ hWO hz₂₁ hz₂O hz₁O (fun j => ?_) (fun j => ?_) hRO h8
    · fin_cases j
      exacts [hgas, hgbs, hcvs, hgds, hk₂s, hk₁s, hRs, rfl, hgs]
    · fin_cases j
      exacts [hgat, hgbt, hcvt, hgdt, hk₂t, hk₁t, hRt, hOt, rfl]
  push Not at hpr
  obtain ⟨hp₁r, hp₂r⟩ := hpr
  have hWp₁ : W (Q.graph.source h₁) :=
    ⟨source_mem_cycleNodes hh₁C, hp₁r, fun h => hloop h₁ (h.trans hth₁.symm)⟩
  have hWp₂ : W (Q.graph.source h₂) :=
    ⟨source_mem_cycleNodes hh₂C, hp₂r, fun h => hloop h₂ (h.trans hth₂.symm)⟩
  by_cases htp : t = Q.graph.source h₁ ∨ t = Q.graph.source h₂
  · -- the top is a parent of `v`: the third and the fourth rootings
    obtain ⟨hT, hO, hTO, hTs, hTt, hOt, hvTO⟩ : ∃ hT hO, hT ≠ hO ∧ Q.graph.source hT = t ∧
        Q.graph.target hT = v ∧ Q.graph.target hO = v ∧
        ∀ g, Q.graph.target g = v → g = hT ∨ g = hO := by
      rcases htp with h | h
      · exact ⟨h₁, h₂, hh₁₂, h.symm, hth₁, hth₂, hvin⟩
      · exact ⟨h₂, h₁, Ne.symm hh₁₂, h.symm, hth₂, hth₁, fun g hg => (hvin g hg).symm⟩
    set pO := Q.graph.source hO with hpO
    have hWt : W t := by
      rcases htp with h | h
      · exact h ▸ hWp₁
      · exact h ▸ hWp₂
    have hWO : W pO := by
      rcases hvin hO hOt with h | h
      · rw [hpO, h]; exact hWp₁
      · rw [hpO, h]; exact hWp₂
    have hOC : hO ∈ C := mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 hOt
    have htO : t ≠ pO := fun h => hparallel hT hO hTO (hTs.trans h) (hTt.trans hOt.symm)
    have hrC : r ∉ cycleNodes Q.graph C := fun h => hWt.2.1 (hreach_r t (hK.top_reaches r h))
    -- the arc into the top leaves the root
    obtain ⟨pT, hpT⟩ := hex_in t (hWdeg t hWt).1
    have hpTs : Q.graph.source pT = r := by
      rcases hNC (Q.graph.source pT) with h | ⟨x, hx⟩ | h | h
      · exact h
      · exact absurd (hx ▸ (hleafdeg x).2) (by
          intro h0
          exact (Q.graph.outdegree_eq_zero_iff _).1 h0 pT rfl)
      · rw [hcvu pT h, hcvt] at hpT
        exact absurd hpT (hWl t hWt c)
      · exact (hcy (hK.top_reaches _ h.1) ⟨pT, rfl, hpT⟩).elim
    obtain ⟨gr, hgrne, hgrs⟩ := hother_out r hr2 pT hpTs
    have hrout : ∀ e, Q.graph.source e = r → e = pT ∨ e = gr :=
      hout2 r hr2 pT gr (Ne.symm hgrne) hpTs hgrs
    have hgrC : gr ∉ C := fun h => hrC (hgrs ▸ source_mem_cycleNodes h)
    -- the other arc out of the top, on the cycle, enters a node `o`
    obtain ⟨f, hfT, hfs⟩ := hother_out t (hWdeg t hWt).2 hT hTs
    have htout : ∀ e, Q.graph.source e = t → e = hT ∨ e = f :=
      hout2 t (hWdeg t hWt).2 hT f (Ne.symm hfT) hTs hfs
    have hfC : f ∈ C := by
      obtain ⟨f₁, hf₁, f₂, hf₂, hne, i₁, i₂⟩ :=
        hcyc.exists_ne_of_mem (fun g _ => hloop g) hK.top_mem
      have s₁ := i₁.resolve_right fun h => hK.top_entry f₁ h hf₁
      have s₂ := i₂.resolve_right fun h => hK.top_entry f₂ h hf₂
      rcases htout f₁ s₁ with rfl | rfl
      · rcases htout f₂ s₂ with rfl | rfl
        · exact absurd rfl hne
        · exact hf₂
      · exact hf₁
    set o := Q.graph.target f with ho
    have hWo : W o := by
      rcases hCtgt f hfC with h | h
      · rcases hvTO f h with h' | h'
        · exact absurd h' hfT
        · exact absurd (by rw [← hfs, h']) htO
      · exact h
    have hot : o ≠ t := fun h => hloop f (hfs.trans h.symm)
    have hoO : o ≠ pO := by
      intro hoO'
      obtain ⟨z, hWz, hzt, hzO⟩ := hWthird t pO
      obtain ⟨k, hk⟩ := hex_in z (hWdeg z hWz).1
      obtain ⟨hkC, hks⟩ := hWin z hWz hzt k hk
      rcases hks with h | h
      · exact hrC (h ▸ source_mem_cycleNodes hkC)
      rcases hWn3 t pO z hWt hWO hWz htO (Ne.symm hzt) (Ne.symm hzO) _ h with h' | h' | h'
      · rcases htout k h' with rfl | rfl
        · exact hWz.2.2 (hk.symm.trans hTt)
        · exact hzO (hk.symm.trans hoO')
      · exact htwoC pO f hO k hfC hOC hkC
          (fun he => htO (by rw [hpO, ← he, hfs]))
          (fun he => hzO (by rw [← hk, ← he]; exact hoO'))
          (fun he => hWz.2.2 (by rw [← hk, ← he, hOt])) (Or.inr hoO') (Or.inl rfl) (Or.inl h')
      · exact hloop k (h'.trans hk.symm)
    -- the arc of the cycle out of `o` enters `pO`
    obtain ⟨k, hkC, hks⟩ := houtC o hWo hot
    have hkt : Q.graph.target k = pO := by
      rcases hCtgt k hkC with h | h
      · rcases hvTO k h with rfl | rfl
        · exact absurd (hks.symm.trans hTs) hot
        · exact absurd hks.symm hoO
      rcases hWn3 t pO o hWt hWO hWo htO (Ne.symm hot) (Ne.symm hoO) _ h with h' | h' | h'
      · exact absurd hkC (hK.top_entry k h')
      · exact h'
      · exact absurd (hks.trans h'.symm) (hloop k)
    have hinT : ∀ e, Q.graph.target e = t → e = pT := fun e he =>
      hin1 t (hWdeg t hWt).1 e pT he hpT
    have hinO : ∀ e, Q.graph.target e = pO → e = k := fun e he =>
      hin1 pO (hWdeg pO hWO).1 e k he hkt
    have hino : ∀ e, Q.graph.target e = o → e = f := fun e he =>
      hin1 o (hWdeg o hWo).1 e f he rfl
    -- the leaves
    obtain ⟨ga, hgak, hgas⟩ := hother_out o (hWdeg o hWo).2 k hks
    obtain ⟨a, hgat⟩ := hleaf3 t pO o hWt hWO hWo htO (Ne.symm hot) (Ne.symm hoO) ga
      (fun h => by
        rcases hvTO ga h with rfl | rfl
        · exact hot (hgas.symm.trans hTs)
        · exact hoO hgas.symm)
      (fun h => hWo.2.1 (by rw [← hgas, hinT ga h, hpTs]))
      (fun h => hgak (hinO ga h))
      (fun h => hloop ga (hgas.trans h.symm))
    obtain ⟨b, hgrt⟩ := hleaf3 t pO o hWt hWO hWo htO (Ne.symm hot) (Ne.symm hoO) gr
      (fun h => hgrC (mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 h))
      (fun h => hgrne (hinT gr h))
      (fun h => hgrC (by rw [hinO gr h]; exact hkC))
      (fun h => hgrC (by rw [hino gr h]; exact hfC))
    obtain ⟨gd, hgdk, hgds⟩ := hother_out pO (hWdeg pO hWO).2 hO rfl
    obtain ⟨d, hgdt⟩ := hleaf3 t pO o hWt hWO hWo htO (Ne.symm hot) (Ne.symm hoO) gd
      (fun h => by
        rcases hvTO gd h with h' | h'
        · exact htO (by rw [← hTs, ← h']; exact hgds)
        · exact hgdk h')
      (fun h => hWO.2.1 (by rw [← hgds, hinT gd h, hpTs]))
      (fun h => hloop gd (hgds.trans h.symm))
      (fun h => htO (by rw [← hfs, ← hino gd h, hgds]))
    have hab := hne_taxa ga gr a b hgat hgrt (by rw [hgas, hgrs]; exact hWo.2.1)
    have hac := hne_c ga a hgat (by rw [hgas]; exact hWo.2.2)
    have had := hne_taxa ga gd a d hgat hgdt (by rw [hgas, hgds]; exact hoO)
    have hbc := hne_c gr b hgrt (by rw [hgrs]; exact Ne.symm hvr)
    have hbd := hne_taxa gr gd b d hgrt hgdt (by rw [hgrs, hgds]; exact Ne.symm hWO.2.1)
    have hcd : c ≠ d := fun h => hne_c gd d hgdt (by rw [hgds]; exact hWO.2.2) h.symm
    rcases hrout _ hrta.1 with h8 | h8
    · refine finish 2 a b d o t pO ![ga, gr, cv, gd, k, f, hT, hO, pT] hab hac had hbc hbd hcd
        hWo hWt hWO hot hoO htO (fun j => ?_) (fun j => ?_) hTO h8
      · fin_cases j
        exacts [hgas, hgrs, hcvs, hgds, hks, hfs, hTs, rfl, hpTs]
      · fin_cases j
        exacts [hgat, hgrt, hcvt, hgdt, hkt, rfl, hTt, hOt, hpT]
    · refine finish 3 a b d o t pO ![ga, pT, cv, gd, k, f, hT, hO, gr] hab hac had hbc hbd hcd
        hWo hWt hWO hot hoO htO (fun j => ?_) (fun j => ?_) hTO h8
      · fin_cases j
        exacts [hgas, hpTs, hcvs, hgds, hks, hfs, hTs, rfl, hgrs]
      · fin_cases j
        exacts [hgat, hpT, hcvt, hgdt, hkt, rfl, hTt, hOt, hgrt]
  push Not at htp
  obtain ⟨htp₁, htp₂⟩ := htp
  set p₁ := Q.graph.source h₁ with hp₁
  set p₂ := Q.graph.source h₂ with hp₂
  have hin₁₂ : ∀ y, W y → y ≠ t → y ≠ p₁ → y ≠ p₂ → ∀ k, Q.graph.target k = y →
      Q.graph.source k ≠ p₁ ∧ Q.graph.source k ≠ p₂ := by
    -- a parent of `v` other than the top has its two arcs of the cycle already
    intro y hy hyt hy₁ hy₂ k hk
    have hkC := hentry' y hy.1 hyt k hk
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨k₁, hk₁⟩ := hex_in p₁ (hWdeg p₁ hWp₁).1
      exact htwoC p₁ k₁ h₁ k (hentry' p₁ hWp₁.1 (Ne.symm htp₁) k₁ hk₁) hh₁C hkC
        (fun he => hWp₁.2.2 (by rw [← hk₁, he, hth₁]))
        (fun he => hy₁ (by rw [← hk, ← he, hk₁]))
        (fun he => hy.2.2 (by rw [← hk, ← he, hth₁])) (Or.inr hk₁) (Or.inl rfl) (Or.inl h)
    · obtain ⟨k₂, hk₂⟩ := hex_in p₂ (hWdeg p₂ hWp₂).1
      exact htwoC p₂ k₂ h₂ k (hentry' p₂ hWp₂.1 (Ne.symm htp₂) k₂ hk₂) hh₂C hkC
        (fun he => hWp₂.2.2 (by rw [← hk₂, he, hth₂]))
        (fun he => hy₂ (by rw [← hk, ← he, hk₂]))
        (fun he => hy.2.2 (by rw [← hk, ← he, hth₂])) (Or.inr hk₂) (Or.inl rfl) (Or.inl h)
  by_cases htr : t = r
  · -- the root is the top of the cycle, not a parent of `v`: the fifth and the sixth rootings
    have hrC : r ∈ cycleNodes Q.graph C := htr ▸ hK.top_mem
    have hWt : ∀ y, W y → y ≠ t := fun y hy h => hy.2.1 (h.trans htr)
    obtain ⟨o, hWo, ho₁, ho₂⟩ := hWthird p₁ p₂
    -- the arc into `o` leaves the root
    obtain ⟨ko, hko⟩ := hex_in o (hWdeg o hWo).1
    have hkos : Q.graph.source ko = r := by
      obtain ⟨-, h | h⟩ := hWin o hWo (hWt o hWo) ko hko
      · exact h
      obtain ⟨n₁, n₂⟩ := hin₁₂ o hWo (hWt o hWo) ho₁ ho₂ ko hko
      rcases hWn3 p₁ p₂ o hWp₁ hWp₂ hWo hsh (Ne.symm ho₁) (Ne.symm ho₂) _ h with h' | h' | h'
      · exact absurd h' n₁
      · exact absurd h' n₂
      · exact absurd (h'.trans hko.symm) (hloop ko)
    obtain ⟨g, hgk, hgs⟩ := hother_out r hr2 ko hkos
    have hrout : ∀ e, Q.graph.source e = r → e = ko ∨ e = g :=
      hout2 r hr2 ko g (Ne.symm hgk) hkos hgs
    have hgC : g ∈ C := mem_of_source_eq_root hB hcyc hrC hgs
    -- the other arc of the root enters a parent `Y` of `v`, and `o` is the parent of the other `Z`
    obtain ⟨hY, hZ, hYZ, hYt, hZt, hvYZ, hgY, hWY, hWZ, hYZs⟩ : ∃ hY hZ, hY ≠ hZ ∧
        Q.graph.target hY = v ∧ Q.graph.target hZ = v ∧
        (∀ e, Q.graph.target e = v → e = hY ∨ e = hZ) ∧ Q.graph.target g = Q.graph.source hY ∧
        W (Q.graph.source hY) ∧ W (Q.graph.source hZ) ∧ Q.graph.source hY ≠ Q.graph.source hZ := by
      rcases hCtgt g hgC with h | h
      · rcases hvin g h with rfl | rfl
        · exact absurd hgs hp₁r
        · exact absurd hgs hp₂r
      rcases hWn3 p₁ p₂ o hWp₁ hWp₂ hWo hsh (Ne.symm ho₁) (Ne.symm ho₂) _ h with h' | h' | h'
      · exact ⟨h₁, h₂, hh₁₂, hth₁, hth₂, hvin, h', hWp₁, hWp₂, hsh⟩
      · exact ⟨h₂, h₁, Ne.symm hh₁₂, hth₂, hth₁, fun e he => (hvin e he).symm, h', hWp₂, hWp₁,
          Ne.symm hsh⟩
      · exact absurd (hin1 o (hWdeg o hWo).1 g ko h' hko) hgk
    set Y := Q.graph.source hY with hY_def
    set Z := Q.graph.source hZ with hZ_def
    have hoY : o ≠ Y := by
      rcases hvin hY hYt with h | h
      · rw [hY_def, h]; exact ho₁
      · rw [hY_def, h]; exact ho₂
    have hoZ : o ≠ Z := by
      rcases hvin hZ hZt with h | h
      · rw [hZ_def, h]; exact ho₁
      · rw [hZ_def, h]; exact ho₂
    have hhYC : hY ∈ C := mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 hYt
    have hhZC : hZ ∈ C := mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 hZt
    obtain ⟨kZ, hkZ⟩ := hex_in Z (hWdeg Z hWZ).1
    have hkZs : Q.graph.source kZ = o := by
      obtain ⟨hkZC, h | h⟩ := hWin Z hWZ (hWt Z hWZ) kZ hkZ
      · rcases hrout kZ h with h' | h'
        · exact absurd (by rw [← hko, ← h', hkZ]) hoZ
        · exact absurd (by rw [← hgY, ← h', hkZ]) hYZs
      rcases hWn3 Y Z o hWY hWZ hWo hYZs (Ne.symm hoY) (Ne.symm hoZ) _ h with h' | h' | h'
      · exact (htwoC Y g hY kZ hgC hhYC hkZC
          (fun he => hWY.2.2 (by rw [← hgY, he, hYt]))
          (fun he => hYZs (by rw [← hgY, he, hkZ]))
          (fun he => hWZ.2.2 (by rw [← hkZ, ← he, hYt])) (Or.inr hgY) (Or.inl rfl)
          (Or.inl h')).elim
      · exact absurd (h'.trans hkZ.symm) (hloop kZ)
      · exact h'
    have hinY : ∀ e, Q.graph.target e = Y → e = g := fun e he =>
      hin1 Y (hWdeg Y hWY).1 e g he hgY
    have hinZ : ∀ e, Q.graph.target e = Z → e = kZ := fun e he =>
      hin1 Z (hWdeg Z hWZ).1 e kZ he hkZ
    have hino : ∀ e, Q.graph.target e = o → e = ko := fun e he =>
      hin1 o (hWdeg o hWo).1 e ko he hko
    -- the leaves
    obtain ⟨ga, hgak, hgas⟩ := hother_out o (hWdeg o hWo).2 kZ hkZs
    obtain ⟨a, hgat⟩ := hleaf3 Y Z o hWY hWZ hWo hYZs (Ne.symm hoY) (Ne.symm hoZ) ga
      (fun h => by
        rcases hvYZ ga h with rfl | rfl
        · exact hoY hgas.symm
        · exact hoZ hgas.symm)
      (fun h => hWo.2.1 (by rw [← hgas, hinY ga h, hgs]))
      (fun h => hgak (hinZ ga h))
      (fun h => hloop ga (hgas.trans h.symm))
    obtain ⟨gb, hgbk, hgbs⟩ := hother_out Y (hWdeg Y hWY).2 hY rfl
    obtain ⟨b, hgbt⟩ := hleaf3 Y Z o hWY hWZ hWo hYZs (Ne.symm hoY) (Ne.symm hoZ) gb
      (fun h => by
        rcases hvYZ gb h with rfl | rfl
        · exact hgbk rfl
        · exact hYZs hgbs.symm)
      (fun h => hloop gb (hgbs.trans h.symm))
      (fun h => hoY (by rw [← hkZs, ← hinZ gb h, hgbs]))
      (fun h => hWY.2.1 (by rw [← hgbs, hino gb h, hkos]))
    obtain ⟨gd, hgdk, hgds⟩ := hother_out Z (hWdeg Z hWZ).2 hZ rfl
    obtain ⟨d, hgdt⟩ := hleaf3 Y Z o hWY hWZ hWo hYZs (Ne.symm hoY) (Ne.symm hoZ) gd
      (fun h => by
        rcases hvYZ gd h with rfl | rfl
        · exact hYZs hgds
        · exact hgdk rfl)
      (fun h => hWZ.2.1 (by rw [← hgds, hinY gd h, hgs]))
      (fun h => hloop gd (hgds.trans h.symm))
      (fun h => hWZ.2.1 (by rw [← hgds, hino gd h, hkos]))
    have hab := hne_taxa ga gb a b hgat hgbt (by rw [hgas, hgbs]; exact hoY)
    have hac := hne_c ga a hgat (by rw [hgas]; exact hWo.2.2)
    have had := hne_taxa ga gd a d hgat hgdt (by rw [hgas, hgds]; exact hoZ)
    have hbc := hne_c gb b hgbt (by rw [hgbs]; exact hWY.2.2)
    have hbd := hne_taxa gb gd b d hgbt hgdt (by rw [hgbs, hgds]; exact hYZs)
    have hcd : c ≠ d := fun h => hne_c gd d hgdt (by rw [hgds]; exact hWZ.2.2) h.symm
    rcases hrout _ hrta.1 with h8 | h8
    · refine finish 5 a b d o Y Z ![ga, gb, cv, gd, kZ, g, hY, hZ, ko] hab hac had hbc hbd hcd
        hWo hWY hWZ hoY hoZ hYZs (fun j => ?_) (fun j => ?_) hYZ h8
      · fin_cases j
        exacts [hgas, hgbs, hcvs, hgds, hkZs, hgs, rfl, rfl, hkos]
      · fin_cases j
        exacts [hgat, hgbt, hcvt, hgdt, hkZ, hgY, hYt, hZt, hko]
    · refine finish 4 a b d o Y Z ![ga, gb, cv, gd, kZ, ko, hY, hZ, g] hab hac had hbc hbd hcd
        hWo hWY hWZ hoY hoZ hYZs (fun j => ?_) (fun j => ?_) hYZ h8
      · fin_cases j
        exacts [hgas, hgbs, hcvs, hgds, hkZs, hkos, rfl, rfl, hgs]
      · fin_cases j
        exacts [hgat, hgbt, hcvt, hgdt, hkZ, hko, hYt, hZt, hgY]
  · -- the root is off the cycle and the top is not a parent of `v`: the first two rootings
    have hWt : W t := ⟨hK.top_mem, htr, fun h => htp₁ (by
      exfalso
      exact hK.top_entry h₁ (hth₁.trans h.symm) hh₁C)⟩
    have hrC : r ∉ cycleNodes Q.graph C := fun h => htr (hreach_r t (hK.top_reaches r h))
    obtain ⟨pT, hpT⟩ := hex_in t (hWdeg t hWt).1
    have hpTs : Q.graph.source pT = r := by
      rcases hNC (Q.graph.source pT) with h | ⟨x, hx⟩ | h | h
      · exact h
      · exact absurd (hx ▸ (hleafdeg x).2) (by
          intro h0
          exact (Q.graph.outdegree_eq_zero_iff _).1 h0 pT rfl)
      · rw [hcvu pT h, hcvt] at hpT
        exact absurd hpT (hWl t hWt c)
      · exact (hcy (hK.top_reaches _ h.1) ⟨pT, rfl, hpT⟩).elim
    obtain ⟨gr, hgrne, hgrs⟩ := hother_out r hr2 pT hpTs
    have hrout : ∀ e, Q.graph.source e = r → e = pT ∨ e = gr :=
      hout2 r hr2 pT gr (Ne.symm hgrne) hpTs hgrs
    have hgrC : gr ∉ C := fun h => hrC (hgrs ▸ source_mem_cycleNodes h)
    -- the arcs into `p₁` and `p₂` leave the top
    have hfromT : ∀ y, W y → y ≠ t → (y = p₁ ∨ y = p₂) → ∀ k, Q.graph.target k = y →
        Q.graph.source k = t := by
      intro y hy hyt hyp k hk
      obtain ⟨hkC, h | h⟩ := hWin y hy hyt k hk
      · exact absurd (h ▸ source_mem_cycleNodes hkC) hrC
      rcases hWn3 t p₁ p₂ hWt hWp₁ hWp₂ htp₁ htp₂ hsh _ h with h' | h' | h'
      · exact h'
      · exfalso
        rcases hyp with rfl | rfl
        · exact hloop k (h'.trans hk.symm)
        · obtain ⟨k₁, hk₁⟩ := hex_in p₁ (hWdeg p₁ hWp₁).1
          exact htwoC p₁ k₁ h₁ k (hentry' p₁ hWp₁.1 (Ne.symm htp₁) k₁ hk₁) hh₁C hkC
            (fun he => hWp₁.2.2 (by rw [← hk₁, he, hth₁]))
            (fun he => hsh (by rw [← hk₁, he, hk]))
            (fun he => hWp₂.2.2 (by rw [← hk, ← he, hth₁])) (Or.inr hk₁) (Or.inl rfl) (Or.inl h')
      · exfalso
        rcases hyp with rfl | rfl
        · obtain ⟨k₂, hk₂⟩ := hex_in p₂ (hWdeg p₂ hWp₂).1
          exact htwoC p₂ k₂ h₂ k (hentry' p₂ hWp₂.1 (Ne.symm htp₂) k₂ hk₂) hh₂C hkC
            (fun he => hWp₂.2.2 (by rw [← hk₂, he, hth₂]))
            (fun he => hsh (by rw [← hk, ← he, hk₂]))
            (fun he => hWp₁.2.2 (by rw [← hk, ← he, hth₂])) (Or.inr hk₂) (Or.inl rfl) (Or.inl h')
        · exact hloop k (h'.trans hk.symm)
    obtain ⟨tp₁, htp₁t⟩ := hex_in p₁ (hWdeg p₁ hWp₁).1
    obtain ⟨tp₂, htp₂t⟩ := hex_in p₂ (hWdeg p₂ hWp₂).1
    have htp₁s := hfromT p₁ hWp₁ (Ne.symm htp₁) (Or.inl rfl) tp₁ htp₁t
    have htp₂s := hfromT p₂ hWp₂ (Ne.symm htp₂) (Or.inr rfl) tp₂ htp₂t
    have hinT : ∀ e, Q.graph.target e = t → e = pT := fun e he =>
      hin1 t (hWdeg t hWt).1 e pT he hpT
    have hin₁ : ∀ e, Q.graph.target e = p₁ → e = tp₁ := fun e he =>
      hin1 p₁ (hWdeg p₁ hWp₁).1 e tp₁ he htp₁t
    have hin₂ : ∀ e, Q.graph.target e = p₂ → e = tp₂ := fun e he =>
      hin1 p₂ (hWdeg p₂ hWp₂).1 e tp₂ he htp₂t
    -- the leaves
    obtain ⟨a, hgrt⟩ := hleaf3 t p₁ p₂ hWt hWp₁ hWp₂ htp₁ htp₂ hsh gr
      (fun h => hgrC (mem_of_target_eq_hybrid hB h1 hcyc hvC hv2 h))
      (fun h => hgrne (hinT gr h))
      (fun h => htr (by rw [← htp₁s, ← hin₁ gr h, hgrs]))
      (fun h => htr (by rw [← htp₂s, ← hin₂ gr h, hgrs]))
    obtain ⟨gb, hgbk, hgbs⟩ := hother_out p₁ (hWdeg p₁ hWp₁).2 h₁ rfl
    obtain ⟨b, hgbt⟩ := hleaf3 t p₁ p₂ hWt hWp₁ hWp₂ htp₁ htp₂ hsh gb
      (fun h => by
        rcases hvin gb h with rfl | rfl
        · exact hgbk rfl
        · exact hsh hgbs.symm)
      (fun h => hWp₁.2.1 (by rw [← hgbs, hinT gb h, hpTs]))
      (fun h => hloop gb (hgbs.trans h.symm))
      (fun h => htp₁ (by rw [← htp₂s, ← hin₂ gb h, hgbs]))
    obtain ⟨gd, hgdk, hgds⟩ := hother_out p₂ (hWdeg p₂ hWp₂).2 h₂ rfl
    obtain ⟨d, hgdt⟩ := hleaf3 t p₁ p₂ hWt hWp₁ hWp₂ htp₁ htp₂ hsh gd
      (fun h => by
        rcases hvin gd h with rfl | rfl
        · exact hsh hgds
        · exact hgdk rfl)
      (fun h => hWp₂.2.1 (by rw [← hgds, hinT gd h, hpTs]))
      (fun h => htp₂ (by rw [← htp₁s, ← hin₁ gd h, hgds]))
      (fun h => hloop gd (hgds.trans h.symm))
    have hab := hne_taxa gr gb a b hgrt hgbt (by rw [hgrs, hgbs]; exact Ne.symm hWp₁.2.1)
    have hac := hne_c gr a hgrt (by rw [hgrs]; exact Ne.symm hvr)
    have had := hne_taxa gr gd a d hgrt hgdt (by rw [hgrs, hgds]; exact Ne.symm hWp₂.2.1)
    have hbc := hne_c gb b hgbt (by rw [hgbs]; exact hWp₁.2.2)
    have hbd := hne_taxa gb gd b d hgbt hgdt (by rw [hgbs, hgds]; exact hsh)
    have hcd : c ≠ d := fun h => hne_c gd d hgdt (by rw [hgds]; exact hWp₂.2.2) h.symm
    rcases hrout _ hrta.1 with h8 | h8
    · refine finish 0 a b d t p₁ p₂ ![gr, gb, cv, gd, tp₂, tp₁, h₁, h₂, pT] hab hac had hbc hbd hcd
        hWt hWp₁ hWp₂ htp₁ htp₂ hsh (fun j => ?_) (fun j => ?_) hh₁₂ h8
      · fin_cases j
        exacts [hgrs, hgbs, hcvs, hgds, htp₂s, htp₁s, rfl, rfl, hpTs]
      · fin_cases j
        exacts [hgrt, hgbt, hcvt, hgdt, htp₂t, htp₁t, hth₁, hth₂, hpT]
    · refine finish 1 a b d t p₁ p₂ ![pT, gb, cv, gd, tp₂, tp₁, h₁, h₂, gr] hab hac had hbc hbd hcd
        hWt hWp₁ hWp₂ htp₁ htp₂ hsh (fun j => ?_) (fun j => ?_) hh₁₂ h8
      · fin_cases j
        exacts [hpTs, hgbs, hcvs, hgds, htp₂s, htp₁s, rfl, rfl, hgrs]
      · fin_cases j
        exacts [hpT, hgbt, hcvt, hgdt, htp₂t, htp₁t, hth₁, hth₂, hgrt]

end SingleFourCycle

end Banos2019
