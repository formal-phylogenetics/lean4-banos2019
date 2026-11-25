module

public import Banos2019.External.SempleSteel2003.Quartets
public import Banos2019.Identify.TildeDefs
public import Banos2019.Identify.TreeIso
public import Phylogenetics.Network.CutHierarchy

/-!
# Theorem 4 without cycles of size at least four (Baños 2019, Section 8)

The base case of the induction of Theorem 4 (`tildeDetermined_zero`): when `N₁⁻` has no cycle of
size at least four, neither has `N₂⁻`; then `Ñ₁` and `Ñ₂` are trees, the orderings of the
concordance factors give the quartet trees they display, and these determine the trees (Semple and
Steel 2003, `External.SempleSteel2003.exists_iso_of_quartets_eq`).

* `unrooted_degree`, `unrooted_mem_cycle_of_isDirected`, `unrooted_side_separates`: the nodes of
  `N⁻` have their degrees in `N`, the hybrid edges of `N⁻` lie on cycles, and the bridges of `N⁻`
  are cut arcs of `N`.
* `tildeNetwork_facts`: without cycles of size at least four, `Ñ` is an `X`-tree whose leaves are
  the taxa and whose other nodes have degree three, and each side of each of its edges is a side of
  a cut arc of `N`.
* `cf_eq_of_not_mem_of_hasCutSplit`: in an LSA quartet network without a 4-cycle, the two quartet
  trees other than that of a cut edge have equal concordance factors, by Proposition 6 without a
  `3₂`-cycle and by Proposition 7 with one (`onSegmentOfI_below_hybrid_of_threeTwo`: the segment of
  `I` of the two taxa below its hybrid node, which are a side of the cut edge or of its complement,
  `cutSplit_pair_eq_or_eq_compl`).
* `not_hasFourCycle_of_ncard_le_three`, `quartetLSA_hasCutSplit_of_separates`: without cycles of
  size at least four in `N⁻`, no `Q⁻_s` has a 4-cycle, and a cut arc of `N` splitting `s` into two
  pairs gives a cut edge of `Q⊕_s`.
* `alternatives_eq_of_displays`: a quartet tree displayed by `Ñ` is that of a cut edge of `Q⊕_s`,
  so its two alternatives have equal concordance factors.
* `displays_iff_of_alternatives_eq`: two such trees for concordance factors with the same ordering,
  not all equal on any set of four taxa, display the same quartet trees.
* `ncard_le_three_of_sameOrdering`: the orderings and Lemma 12 exclude a cycle of size at least
  four from `N₂⁻`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

section Unrooted

variable {V E X : Type*}

/-- A vertex below the LSA of the taxa, other than the LSA, has all its parents below the LSA: a
parent elsewhere would give a path from the root to a taxon avoiding the LSA. -/
theorem reaches_lsa_source [Nonempty X] {N : RootedNetwork V E X} (hP : N.IsPhylogenetic) {f : E}
    (hm : N.graph.Reaches (lsa hP Set.univ Set.univ_nonempty) (N.graph.target f))
    (hne : N.graph.target f ≠ lsa hP Set.univ Set.univ_nonempty) :
    N.graph.Reaches (lsa hP Set.univ Set.univ_nonempty) (N.graph.source f) := by
  set m := lsa hP Set.univ Set.univ_nonempty
  by_contra hs
  obtain ⟨x, hx⟩ := exists_reaches_leaf hP (N.graph.target f)
  have hsm : N.graph.source f ≠ m := fun h => hs (h ▸ .refl)
  apply (lsa_spec hP Set.univ Set.univ_nonempty).1 x (Set.mem_univ x)
  have h₁ : N.HasPathAvoiding N.root (N.graph.source f) m :=
    hasPathAvoiding_of_not_reaches_reaches (hP.root_reaches _) (fun h => hs h.2)
  have h₂ : N.HasPathAvoiding (N.graph.source f) (N.graph.target f) m :=
    ⟨hsm, hne, .single ⟨⟨f, rfl, rfl⟩, hsm, hne⟩⟩
  have h₃ : N.HasPathAvoiding (N.graph.target f) (N.leaf x) m :=
    hasPathAvoiding_of_not_reaches_reaches hx
      (fun h => hne (eq_of_reaches_of_reaches hP.acyclic h.1 hm))
  exact hasPathAvoiding_trans (hasPathAvoiding_trans h₁ h₂) h₃

/-- The vertices of `N` below the LSA, other than the LSA, keep their degrees in `𝒩⊕`. -/
theorem lsaPlus_degree [Finite E] [Nonempty X] {N : RootedNetwork V E X} (hP : N.IsPhylogenetic)
    (hX : Nontrivial X) (w : N.belowVertices (lsa hP Set.univ Set.univ_nonempty) Set.univ)
    (hw : w.1 ≠ lsa hP Set.univ Set.univ_nonempty) :
    degree (lsaPlus hP hX).graph w = degree N.graph w.1 := by
  unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree
  congr 1
  · refine Set.ncard_congr (fun e _ => e.1) (fun e he => congrArg Subtype.val he)
      (fun e e' _ _ h => Subtype.ext h) fun f hf => ?_
    have hf' : N.graph.target f = w.1 := hf
    refine ⟨⟨f, reaches_lsa_source hP (hf' ▸ w.2.1) (hf' ▸ hw),
      mem_ancestralVertices_univ hP _⟩, Subtype.ext hf', rfl⟩
  · refine Set.ncard_congr (fun e _ => e.1) (fun e he => congrArg Subtype.val he)
      (fun e e' _ _ h => Subtype.ext h) fun f hf => ?_
    have hf' : N.graph.source f = w.1 := hf
    exact ⟨⟨f, hf' ▸ w.2.1, mem_ancestralVertices_univ hP _⟩, Subtype.ext hf', rfl⟩

/-- **Suppressing the root keeps the degrees of the other vertices**: the child of `e₀` loses `e₀`
and gains the merged edge. -/
theorem unrootAt_degree [Finite E] {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) {e₀ : E}
    (he₀ : M.graph.source e₀ = M.root) (hout : M.graph.outdegree M.root = 2)
    (w : {v // v ≠ M.root}) : degree (M.unrootAt hM e₀).graph w = degree M.graph w.1 := by
  have htgt : ∀ e, (M.unrootAt hM e₀).graph.target e = w ↔ M.graph.target e.1 = w.1 := fun e =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hsrc : ∀ e, (M.unrootAt hM e₀).graph.source e = w ↔
      (M.graph.source e.1 = M.root ∧ M.graph.target e₀ = w.1) ∨ M.graph.source e.1 = w.1 := by
    intro e
    simp only [unrootAt]
    split_ifs with h
    · constructor
      · intro h'
        exact Or.inl ⟨h, congrArg Subtype.val h'⟩
      · rintro (⟨-, h'⟩ | h')
        · exact Subtype.ext h'
        · exact absurd (h'.symm.trans h) w.2
    · constructor
      · intro h'
        exact Or.inr (congrArg Subtype.val h')
      · rintro (⟨h', -⟩ | h')
        · exact absurd h' h
        · exact Subtype.ext h'
  unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree
  have hin : {e : {e // e ≠ e₀} | (M.unrootAt hM e₀).graph.target e = w}.ncard =
      ({e | M.graph.target e = w.1} \ {e₀}).ncard := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext f
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨(htgt e).1 he, e.2⟩
    · rintro ⟨hf, hne⟩
      exact ⟨⟨f, hne⟩, (htgt _).2 hf, rfl⟩
  have hout' : {e : {e // e ≠ e₀} | (M.unrootAt hM e₀).graph.source e = w}.ncard =
      {e | e ≠ e₀ ∧ ((M.graph.source e = M.root ∧ M.graph.target e₀ = w.1) ∨
        M.graph.source e = w.1)}.ncard := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext f
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.2, (hsrc e).1 he⟩
    · rintro ⟨hne, hf⟩
      exact ⟨⟨f, hne⟩, (hsrc _).2 hf, rfl⟩
  rw [hin, hout']
  have hwr : w.1 ≠ M.root := w.2
  by_cases ht : M.graph.target e₀ = w.1
  · have hmem : e₀ ∈ {e | M.graph.target e = w.1} := ht
    have h1 := Set.ncard_sdiff_singleton_add_one hmem (Set.toFinite _)
    have hset : {e | e ≠ e₀ ∧ ((M.graph.source e = M.root ∧ M.graph.target e₀ = w.1) ∨
        M.graph.source e = w.1)} =
        ({e | M.graph.source e = M.root} \ {e₀}) ∪ {e | M.graph.source e = w.1} := by
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, ht,
        and_true]
      constructor
      · rintro ⟨hne, h | h⟩
        · exact Or.inl ⟨h, hne⟩
        · exact Or.inr h
      · rintro (⟨h, hne⟩ | h)
        · exact ⟨hne, Or.inl h⟩
        · exact ⟨fun he => hwr (h.symm.trans (he ▸ he₀)), Or.inr h⟩
    rw [hset, Set.ncard_union_eq, Set.ncard_sdiff_singleton_of_mem (show e₀ ∈
      {e | M.graph.source e = M.root} from he₀)]
    · have : {e | M.graph.source e = M.root}.ncard = 2 := hout
      omega
    · rw [Set.disjoint_left]
      rintro e ⟨h, -⟩ h'
      exact hwr (h'.symm.trans h)
  · have hset₁ : {e | M.graph.target e = w.1} \ {e₀} = {e | M.graph.target e = w.1} := by
      ext e
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, and_iff_left_iff_imp]
      rintro h rfl
      exact ht h
    have hset₂ : {e | e ≠ e₀ ∧ ((M.graph.source e = M.root ∧ M.graph.target e₀ = w.1) ∨
        M.graph.source e = w.1)} = {e | M.graph.source e = w.1} := by
      ext e
      simp only [Set.mem_ofPred_eq, ht, and_false, false_or]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        exact hwr (h.symm.trans he₀)
    rw [hset₁, hset₂]

/-- A directed path from a vertex that does not reach the source of `f₀` does not use `f₀`. -/
theorem avoidingReach_of_reaches {N : RootedNetwork V E X} {a b : V} {f₀ : E}
    (h : N.graph.Reaches a b) (hf : ¬ N.graph.Reaches a (N.graph.source f₀)) :
    N.AvoidingReach f₀ a b := by
  induction h with
  | refl => exact .refl
  | @tail c d hac hcd ih =>
    obtain ⟨f, hfs, hft⟩ := hcd
    refine ih.tail ⟨f, ?_, hfs, hft⟩
    rintro rfl
    exact hf (hfs ▸ hac)

/-- A directed path to a vertex that the target of `f₀` does not reach does not use `f₀`. -/
theorem avoidingReach_of_not_reaches_target {N : RootedNetwork V E X} {a b : V} {f₀ : E}
    (h : N.graph.Reaches a b) (hf : ¬ N.graph.Reaches (N.graph.target f₀) b) :
    N.AvoidingReach f₀ a b := by
  induction h with
  | refl => exact .refl
  | @tail c d hac hcd ih =>
    obtain ⟨f, hfs, hft⟩ := hcd
    refine (ih fun h => hf (h.tail ⟨f, hfs, hft⟩)).tail ⟨f, ?_, hfs, hft⟩
    rintro rfl
    exact hf (hft ▸ .refl)

/-- A path from the root to a taxon avoiding `f₀` passes the LSA, and from there still avoids
`f₀`. -/
theorem avoidingReach_lsa_of_root [Nonempty X] {N : RootedNetwork V E X} (hP : N.IsPhylogenetic)
    {f₀ : E} {x : X} (h : N.AvoidingReach f₀ N.root (N.leaf x)) :
    N.AvoidingReach f₀ (lsa hP Set.univ Set.univ_nonempty) (N.leaf x) := by
  set m := lsa hP Set.univ Set.univ_nonempty
  by_cases hr : N.root = m
  · rw [← hr]
    exact h
  suffices key : ∀ b, N.AvoidingReach f₀ N.root b → N.AvoidingReach f₀ m b ∨
      (b ≠ m ∧ Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ m ∧ b ≠ m) N.root b) by
    rcases key _ h with h' | ⟨hb, hp⟩
    · exact h'
    · exact absurd ⟨hr, hb, hp⟩ ((lsa_spec hP Set.univ Set.univ_nonempty).1 x (Set.mem_univ x))
  intro b hb
  induction hb with
  | refl => exact Or.inr ⟨hr, .refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨f, hf, hfs, hft⟩ := hcd
    rcases ih with ih | ⟨hc, hp⟩
    · exact Or.inl (ih.tail ⟨f, hf, hfs, hft⟩)
    · by_cases hd : d = m
      · exact Or.inl (hd ▸ .refl)
      · exact Or.inr ⟨hd, hp.tail ⟨⟨f, hfs, hft⟩, hc, hd⟩⟩

end Unrooted

section UnrootedNet

variable {V E X : Type*} {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
  {hX : Nontrivial X}
include hN

/-- A node of `N⁻` is not the root of `N`. -/
theorem unrooted_node_ne_root (w : SemidirectedVertex hN.1 hX) : w.1.1 ≠ N.root := by
  intro h
  apply unrooted_node_ne_lsa w
  exact eq_of_reaches_of_reaches hN.1.acyclic (by rw [h]; exact hN.1.root_reaches _) w.1.2.1

/-- **The degrees of `N⁻`** are those of `N`. -/
theorem unrooted_degree [Finite E] (w : SemidirectedVertex hN.1 hX) :
    degree (unrooted N hN hX).graph w = degree N.graph w.1.1 :=
  (unrootAt_degree (lsaPlus_isPhylogenetic hN.1 hX) (rootTreeArc_spec hN.1 hN.2 hX).1
    (lsaPlus_outdegree_root hN.1 hN.2 hX) w).trans
    (lsaPlus_degree hN.1 hX w.1 (unrooted_node_ne_lsa w))

/-- A taxon of `N⁻` has degree one. -/
theorem unrooted_degree_leaf [Finite E] (x : X) :
    degree (unrooted N hN hX).graph ((unrooted N hN hX).leaf x) = 1 := by
  rw [unrooted_degree hN]
  show N.graph.indegree (N.leaf x) + N.graph.outdegree (N.leaf x) = 1
  rw [hN.1.leaf_indegree x, (hN.1.leaves _).2 ⟨x, rfl⟩]

/-- A node of `N⁻` other than a taxon has degree three. -/
theorem unrooted_degree_of_not_leaf [Finite E] (w : SemidirectedVertex hN.1 hX)
    (hw : ¬ ∃ x, (unrooted N hN hX).leaf x = w) : degree (unrooted N hN hX).graph w = 3 := by
  rw [unrooted_degree hN]
  have hl : ¬ ∃ x, N.leaf x = w.1.1 := fun ⟨x, hx⟩ => hw ⟨x, unrooted_node_ext hx⟩
  exact hN.2.2 _ (unrooted_node_ne_root hN w) fun h => hl ((hN.1.leaves _).1 h)

/-- The taxa of `N⁻` are labelled injectively. -/
theorem unrooted_leaf_injective : Function.Injective (unrooted N hN hX).leaf := fun _ _ h =>
  hN.1.leaf_injective (congrArg (fun w => w.1.1) h)

/-- **A hybrid edge of `N⁻` lies on a cycle**: its target has two parents in `N`, so it is the
hybrid node of a cycle of `N⁻`, which has the hybrid edges entering it. -/
theorem unrooted_mem_cycle_of_isDirected [Finite E] (h1 : IsLevelOne N.graph)
    (c : SemidirectedArc hN.1 hN.2 hX) (hc : (unrooted N hN hX).IsDirected c) :
    ∃ C, IsCycle (unrooted N hN hX).graph C ∧ c ∈ C := by
  have h2 : N.graph.indegree ((unrooted N hN hX).graph.target c).1.1 = 2 := by
    refine le_antisymm (hN.indegree_le_two _) (le_trans hc ?_)
    exact Set.ncard_le_ncard_of_injOn (fun e => e.1) (fun e he => congrArg Subtype.val he)
      (fun _ _ _ _ h => Subtype.ext h) (Set.toFinite _)
  obtain ⟨C, hC, hv⟩ := exists_isHybridNodeOf_of_indegree_eq_two hN h1 _ h2
  obtain ⟨h, hhC, -, hh⟩ := hv.exists_mem_of_target (f := c.1.1) rfl
  exact ⟨C, hC, unrooted_edge_ext hh ▸ hhC⟩

/-- An arc path of `N` from a node of `N⁻` avoiding the arc of the edge `g` is a walk of `N⁻`
avoiding `g`. -/
theorem unrooted_walks_of_avoidingReach (g : SemidirectedArc hN.1 hN.2 hX)
    (w : SemidirectedVertex hN.1 hX) {b : V} (h : N.AvoidingReach g.1.1 w.1.1 b) :
    ∃ w' : SemidirectedVertex hN.1 hX, w'.1.1 = b ∧ (unrooted N hN hX).graph.Walks {g}ᶜ w w' := by
  induction h with
  | refl => exact ⟨w, rfl, .refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨w', rfl, hw'⟩ := ih
    obtain ⟨f, hfg, hfs, hft⟩ := hcd
    obtain ⟨c', hc'f, hc's, hc't⟩ := exists_unrooted_edge hN w' hfs
    refine ⟨(unrooted N hN hX).graph.target c', hc't.trans hft,
      hw'.tail ⟨c', ?_, Or.inl ⟨hc's, rfl⟩⟩⟩
    intro h
    rw [Set.mem_singleton_iff] at h
    exact hfg (hc'f ▸ congrArg (fun c => c.1.1) h)

/-- An arc path of `N` from the LSA avoiding the arc of `g`, to a vertex other than the LSA, is a
walk of `N⁻` avoiding `g` from the child of `rootTreeArc`: its first arc is `rootTreeArc` or the
edge merged with it. -/
theorem unrooted_walks_of_avoidingReach_lsa (g : SemidirectedArc hN.1 hN.2 hX) {b : V}
    (h : N.AvoidingReach g.1.1 (lsa hN.1 Set.univ Set.univ_nonempty) b)
    (hb : b ≠ lsa hN.1 Set.univ Set.univ_nonempty) :
    ∃ w' : SemidirectedVertex hN.1 hX, w'.1.1 = b ∧ (unrooted N hN hX).graph.Walks {g}ᶜ
      ⟨(lsaPlus hN.1 hX).graph.target (rootTreeArc hN.1 hN.2 hX),
        (lsaPlus_isPhylogenetic hN.1 hX).target_ne_root _⟩ w' := by
  set m := lsa hN.1 Set.univ Set.univ_nonempty
  set t₀ : SemidirectedVertex hN.1 hX := ⟨(lsaPlus hN.1 hX).graph.target (rootTreeArc hN.1 hN.2 hX),
    (lsaPlus_isPhylogenetic hN.1 hX).target_ne_root _⟩
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨v₁, ⟨f₁, hf₁g, hf₁s, hf₁t⟩, hrest⟩
  · exact absurd h'.symm hb
  have hv₁ : v₁ ≠ m := by
    rintro rfl
    exact hN.1.acyclic _ (.single ⟨f₁, hf₁s, hf₁t⟩)
  obtain ⟨w₁, hw₁⟩ := exists_unrooted_node (hX := hX) hN.1 (.single ⟨f₁, hf₁s, hf₁t⟩) hv₁
  obtain ⟨w', hw'b, hw'⟩ := unrooted_walks_of_avoidingReach hN g w₁ (hw₁ ▸ hrest)
  refine ⟨w', hw'b, Relation.ReflTransGen.trans ?_ hw'⟩
  have hmem : f₁ ∈ N.belowArcs m Set.univ := ⟨hf₁s ▸ .refl, mem_ancestralVertices_univ hN.1 _⟩
  by_cases hr : (⟨f₁, hmem⟩ : N.belowArcs m Set.univ) = rootTreeArc hN.1 hN.2 hX
  · have : t₀ = w₁ := unrooted_node_ext (by
      rw [hw₁, ← hf₁t]
      exact congrArg (fun e => N.graph.target e.1) hr.symm)
    rw [this]
  · refine .single ⟨⟨⟨f₁, hmem⟩, hr⟩, fun h => hf₁g ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [Set.mem_singleton_iff] at h
      exact congrArg (fun c => c.1.1) h
    · exact unrooted_node_ext (unrooted_source_val_of_eq hN _ hf₁s)
    · exact unrooted_node_ext (hf₁t.trans hw₁.symm)

/-- **A bridge of `N⁻` is a cut arc of `N`**: its arc dominates the taxa on the side of its target
and is above none of the others. -/
theorem unrooted_separates [Finite E] (g : SemidirectedArc hN.1 hN.2 hX)
    (hg : ¬ (unrooted N hN hX).graph.Walks {g}ᶜ ((unrooted N hN hX).graph.source g)
      ((unrooted N hN hX).graph.target g)) :
    N.Separates g.1.1
      {x | (unrooted N hN hX).graph.Walks {g}ᶜ ((unrooted N hN hX).graph.target g)
        ((unrooted N hN hX).leaf x)}
      {x | (unrooted N hN hX).graph.Walks {g}ᶜ ((unrooted N hN hX).graph.target g)
        ((unrooted N hN hX).leaf x)}ᶜ := by
  set G := unrooted N hN hX
  set m := lsa hN.1 Set.univ Set.univ_nonempty
  have hnr : ¬ N.graph.Reaches (N.graph.target g.1.1) (N.graph.source g.1.1) := fun h =>
    hN.1.acyclic _ (Relation.TransGen.head' ⟨g.1.1, rfl, rfl⟩ h)
  refine ⟨fun x hx hav => ?_, fun x hx hb => ?_⟩
  · -- the path from the root passes the LSA, and leads to `x` from the child of `rootTreeArc`
    have hm := avoidingReach_lsa_of_root hN.1 hav
    obtain ⟨w', hw'x, hw'⟩ := unrooted_walks_of_avoidingReach_lsa hN g hm
      ((lsa_spec hN.1 Set.univ Set.univ_nonempty).1.leaf_ne hN.1 Set.nontrivial_univ x)
    have hw'' : w' = G.leaf x := unrooted_node_ext (u := w') (w := G.leaf x) hw'x
    subst hw''
    -- the source of `g` is also reached from there
    have hs : G.graph.Walks {g}ᶜ ⟨(lsaPlus hN.1 hX).graph.target (rootTreeArc hN.1 hN.2 hX),
        (lsaPlus_isPhylogenetic hN.1 hX).target_ne_root _⟩ (G.graph.source g) := by
      by_cases hgm : N.graph.source g.1.1 = m
      · rw [show G.graph.source g = ⟨(lsaPlus hN.1 hX).graph.target (rootTreeArc hN.1 hN.2 hX),
          (lsaPlus_isPhylogenetic hN.1 hX).target_ne_root _⟩ from
            unrooted_node_ext (unrooted_source_val_of_eq hN g hgm)]
        exact .refl
      · obtain ⟨w, hw, hws⟩ := unrooted_walks_of_avoidingReach_lsa hN g
          (avoidingReach_of_not_reaches_target g.1.2.1 hnr) hgm
        rwa [show w = G.graph.source g from
          unrooted_node_ext (hw.trans (unrooted_source_val_of_ne hN g hgm).symm)] at hws
    exact hg ((G.graph.walks_symm hs).trans (hw'.trans (G.graph.walks_symm hx)))
  · -- a path from the target of `g` to `x` avoids `g`
    obtain ⟨w', hw'x, hw'⟩ := unrooted_walks_of_avoidingReach hN g (G.graph.target g)
      (avoidingReach_of_reaches hb hnr)
    have hw'' : w' = G.leaf x := unrooted_node_ext (u := w') (w := G.leaf x) hw'x
    subst hw''
    exact hx hw'

/-- **A bridge of `N⁻` is a cut arc of `N`**, for the side of either of its ends. -/
theorem unrooted_side_separates [Finite E] (g : SemidirectedArc hN.1 hN.2 hX)
    (hg : ¬ (unrooted N hN hX).graph.Walks {g}ᶜ ((unrooted N hN hX).graph.source g)
      ((unrooted N hN hX).graph.target g)) {a : SemidirectedVertex hN.1 hX}
    (ha : a = (unrooted N hN hX).graph.source g ∨ a = (unrooted N hN hX).graph.target g) :
    ∃ f, N.Separates f {x | (unrooted N hN hX).graph.Walks {g}ᶜ a ((unrooted N hN hX).leaf x)}
        {x | (unrooted N hN hX).graph.Walks {g}ᶜ a ((unrooted N hN hX).leaf x)}ᶜ ∨
      N.Separates f {x | (unrooted N hN hX).graph.Walks {g}ᶜ a ((unrooted N hN hX).leaf x)}ᶜ
        {x | (unrooted N hN hX).graph.Walks {g}ᶜ a ((unrooted N hN hX).leaf x)} := by
  set G := unrooted N hN hX
  rcases ha with rfl | rfl
  · -- the side of the source is the complement of that of the target
    have hc : {x | G.graph.Walks {g}ᶜ (G.graph.source g) (G.leaf x)} =
        {x | G.graph.Walks {g}ᶜ (G.graph.target g) (G.leaf x)}ᶜ := by
      ext x
      constructor
      · intro hs ht
        exact hg (hs.trans (G.graph.walks_symm ht))
      · intro ht
        exact (walks_compl_or_of_isConnected (unrooted_isConnected hN hX) g _).resolve_right ht
    rw [hc, compl_compl]
    exact ⟨g.1.1, Or.inr (unrooted_separates hN g hg)⟩
  · exact ⟨g.1.1, Or.inl (unrooted_separates hN g hg)⟩

end UnrootedNet

section Tilde

variable {V E X : Type*}

/-- Without cycles of size at least four, every cycle has size at most three. -/
theorem ncard_le_three_of_bigCycleCount_eq_zero [Finite E] {G : SemidirectedNetwork V E X}
    (h0 : bigCycleCount G = 0) {C : Set E} (hC : IsCycle G.graph C) : C.ncard ≤ 3 := by
  by_contra h
  have hmem : C ∈ cyclesOfSizeAtLeast G.graph 4 := ⟨hC, by omega⟩
  have := (Set.ncard_pos (Set.toFinite _)).2 ⟨C, hmem⟩
  unfold bigCycleCount at h0
  omega

variable [Finite V] [Finite E] {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N)
  {hX : Nontrivial X}

/-- **The network `Ñ` without cycles of size at least four** (Baños 2019, proof of Theorem 4): it is
a tree without hybrid edges, whose leaves are the taxa, labelled injectively, and whose other nodes
have degree three; each side of each of its edges is a side of a cut arc of `N`. Its graph is `N⁻`
with its 2- and 3-cycles contracted, which are all its cycles, and the nodes of degree two left by
the 2-cycles suppressed. -/
theorem tildeNetwork_facts (h1 : IsLevelOne N.graph)
    (hsize : ∀ C, IsCycle (unrooted N hN hX).graph C → C.ncard ≤ 3) :
    (tildeNetwork (unrooted N hN hX)).graph.IsTree ∧
      (∀ c, ¬ (tildeNetwork (unrooted N hN hX)).IsDirected c) ∧
      SplitsEquivalence.IsXTree (tildeNetwork (unrooted N hN hX)).graph.toSimpleGraph
        (tildeNetwork (unrooted N hN hX)).leaf ∧
      Function.Injective (tildeNetwork (unrooted N hN hX)).leaf ∧
      (∀ x, ((tildeNetwork (unrooted N hN hX)).graph.toSimpleGraph.neighborSet
        ((tildeNetwork (unrooted N hN hX)).leaf x)).ncard = 1) ∧
      (∀ v, v ∉ Set.range (tildeNetwork (unrooted N hN hX)).leaf →
        ((tildeNetwork (unrooted N hN hX)).graph.toSimpleGraph.neighborSet v).ncard = 3) ∧
      ∀ A ∈ SplitsEquivalence.splitSides (tildeNetwork (unrooted N hN hX)).graph.toSimpleGraph
        (tildeNetwork (unrooted N hN hX)).leaf, ∃ f, N.Separates f A Aᶜ ∨ N.Separates f Aᶜ A := by
  have : Nonempty X := hX.to_nonempty
  set G := unrooted N hN hX
  have hP : ∀ C, IsCycle G.graph C →
      (fun C : Set (SemidirectedArc hN.1 hN.2 hX) => C.ncard ≤ 3) C := hsize
  have hnd : ∀ C C', IsCycle G.graph C → IsCycle G.graph C' →
      (cycleNodes G.graph C ∩ cycleNodes G.graph C').Nonempty → C = C' :=
    fun C C' hC hC' h => (lemma3_unrooted hN h1 hX hC).2.2 C' hC' h
  have hconn := unrooted_isConnected hN hX
  have hK : (contractCycles G fun C => C.ncard ≤ 3).graph.IsTree := contract_isTree hP hconn
  set K := undirectEdges (contractCycles G fun C => C.ncard ≤ 3)
    {e | ∃ C, IsCycle G.graph C ∧ C.ncard = 4 ∧ e.1 ∈ C}
  have hK' : K.graph.IsTree := hK
  have hdir : ∀ e, ¬ K.IsDirected e := by
    rintro e ⟨he, -⟩
    obtain ⟨C, hC, heC⟩ := unrooted_mem_cycle_of_isDirected hN h1 e.1 he
    exact e.2 C hC (hP C hC) heC
  obtain ⟨hleaf, hdeg, hinj⟩ := contract_degrees hP hnd (unrooted_source_ne_target hN) hconn hsize
    (unrooted_degree_leaf hN) (unrooted_degree_of_not_leaf hN) (unrooted_leaf_injective hN)
  obtain ⟨hX', hinj', hleaf', h3⟩ := suppress_xTree (K := K) hdir hK' hleaf hdeg hinj
  refine ⟨suppress_isTree hdir hK', suppress_not_isDirected hdir, hX', hinj', hleaf', h3,
    fun A hA => ?_⟩
  obtain ⟨g, a, hga, hA'⟩ := suppress_splitSides hdir hK' hA
  have hbr : ¬ G.graph.Walks {g.1}ᶜ (G.graph.source g.1) (G.graph.target g.1) := fun h => by
    obtain ⟨C, hC, hgC, -⟩ := exists_isCycle_of_walks
      (show g.1 ∉ ({g.1}ᶜ : Set _) from fun h => h rfl) (G.graph.walks_symm h)
    exact g.2 C hC (hP C hC) hgC
  obtain ⟨a', ha', haa⟩ : ∃ a', (a' = G.graph.source g.1 ∨ a' = G.graph.target g.1) ∧
      Quot.mk _ a' = a := by
    rcases hga with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have hSK : {x | K.graph.Walks {g}ᶜ a (K.leaf x)} = {x | G.graph.Walks {g.1}ᶜ a' (G.leaf x)} := by
    ext x
    rw [← haa]
    exact contract_walks_compl_iff hP g a' (G.leaf x)
  rw [hSK] at hA'
  obtain ⟨f, hf⟩ := unrooted_side_separates hN g.1 hbr ha'
  rcases hA' with rfl | hA'
  · exact ⟨f, hf⟩
  · rw [← hA', compl_compl] at hf
    exact ⟨f, hf.symm⟩

end Tilde

section Quartet

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

/-- **The segment of `I` of a `3₂`-cycle** (proof of Proposition 7): if `Q⁻` has a `3₂`-cycle with
the taxa `a`, `b` below its hybrid node, `CF(Q)` lies on the open segment for the cherry `{a, b}`:
the quartet tree `ab|cd` has a concordance factor above `1/6`, and the two others are equal.
Corollary 2 suppresses the `2₁`- and `2₃`-cycles, and Lemmas 9 and 10 write the concordance factors
as a convex combination of those of networks with the same `3₂`-cycle and one cycle fewer
(`onSegmentOfI_of_threeTwo`). -/
theorem onSegmentOfI_below_hybrid_of_threeTwo {Q : RootedNetwork V E X} {θ : MetricData E}
    (hQ : IsLSAQuartet Q θ) {C : Set E} {v : V} (hC : InducesCycleType Q C v 3 2) {a b : X}
    (hab : a ≠ b) (hD : {x | Q.graph.Reaches v (Q.leaf x)} = {a, b}) :
    OnSegmentOfI (cf Q θ) {a, b} := by
  -- Corollary 2: suppress the `2₁`- and `2₃`-cycles
  obtain ⟨V', E', _, _, Q', θ', hQ', hcf', hsame, -⟩ := exists_lsaQuartet_of_corollary2 hQ
  have hnot : ∀ C' v', InducesCycleType Q C' v' 2 1 ∨ InducesCycleType Q C' v' 2 3 →
      IsTwoOneOrThree Q C' := fun C' v' h => ⟨v', h⟩
  have h32' : HasCycleWithBelow Q' 3 ↑({a, b} : Finset X) := by
    refine (hsame 3 _).2 ⟨C, v, ?_, ?_, ?_⟩
    · rintro ⟨v', h | h⟩ <;> have := h.2.2.2.1 <;> have := hC.2.2.2.1 <;> omega
    · rw [Finset.coe_pair, Set.ncard_pair hab]
      exact hC
    · rw [Finset.coe_pair]
      exact hD
  have h21 : ¬ ∃ C v, InducesCycleType Q' C v 2 1 := by
    rintro ⟨C', v', hC'⟩
    obtain ⟨C'', v'', hn, hC'', -⟩ := (hsame 2 _).1 (HasCycleWithBelow.of_inducesCycleType hC')
    rw [hC'.2.2.2.2] at hC''
    exact hn (hnot _ _ (Or.inl hC''))
  have h23 : ¬ ∃ C v, InducesCycleType Q' C v 2 3 := by
    rintro ⟨C', v', hC'⟩
    obtain ⟨C'', v'', hn, hC'', -⟩ := (hsame 2 _).1 (HasCycleWithBelow.of_inducesCycleType hC')
    rw [hC'.2.2.2.2] at hC''
    exact hn (hnot _ _ (Or.inr hC''))
  -- Lemmas 9 and 10, by induction
  have hseg := onSegmentOfI_of_threeTwo _ hQ' rfl _ (card_pair hab) h32' h21 h23
  rwa [hcf', ← corollary2 hQ] at hseg

omit [Fintype V] [Fintype E] in
/-- **Two cut splits of pairs of the four taxa are equal or complementary**: the sides of cut edges
avoiding a taxon are laminar (`cutSplits_laminar`). -/
theorem cutSplit_pair_eq_or_eq_compl {Q : RootedNetwork V E X} (hQ : Q.IsPhylogenetic)
    (hX : Fintype.card X = 4) {B D : Finset X} (hB : #B = 2) (hD : #D = 2)
    (hBc : Q.HasCutSplit ↑B) (hDc : Q.HasCutSplit ↑D) : B = D ∨ B = Dᶜ := by
  have hcompl : ∀ A : Finset X, #A = 2 → #Aᶜ = 2 := fun A hA => by
    rw [card_compl, hX, hA]
  -- a taxon off `D`
  obtain ⟨r, hrD⟩ : ∃ r, r ∉ D := by
    by_contra h
    push Not at h
    rw [eq_univ_of_forall h, card_univ, hX] at hD
    omega
  -- a cut split of a pair avoiding `r` is `D` or its complement
  have key : ∀ B' : Finset X, #B' = 2 → Q.HasCutSplit ↑B' → r ∉ B' → B' = D ∨ B' = Dᶜ := by
    intro B' hB' hB'c hrB'
    rcases Q.cutSplits_laminar (Q.graph_connected hQ) r hDc hB'c (by simpa using hrD)
      (by simpa using hrB') with h | h | h
    · exact Or.inl (eq_of_subset_of_card_le (coe_subset.1 h) (by omega)).symm
    · exact Or.inl (eq_of_subset_of_card_le (coe_subset.1 h) (by omega))
    · refine Or.inr (eq_of_subset_of_card_le (fun x hx => mem_compl.2 fun hxD => ?_)
        (by rw [hcompl D hD, hB']))
      exact Set.disjoint_left.1 h (mem_coe.2 hxD) (mem_coe.2 hx)
  by_cases hrB : r ∈ B
  · have hBc' : Q.HasCutSplit ↑Bᶜ := by
      rw [coe_compl, Q.hasCutSplit_compl]
      exact hBc
    rcases key Bᶜ (hcompl B hB) hBc' (fun h => mem_compl.1 h hrB) with h | h
    · exact Or.inr (by rw [← h, compl_compl])
    · exact Or.inl (compl_injective h)
  · exact key B hB hBc hrB

/-- **The two quartet trees other than that of a cut edge have equal concordance factors**, in an
LSA quartet network `Q⊕` without a 4-cycle. Without a `3₂`-cycle, the ordering of `CF(Q)` is that of
the network `Q'` with its 2-cycles and `3₁`-cycles contracted (Proposition 6), a tree whose
concordance factors are those of a species tree whose split of two pairs of taxa is that of the cut
edge (`exists_speciesTree_contractRooted`): its quartet tree has the largest, strictly, and the two
others are equal (equation (1)). With a `3₂`-cycle, `CF(Q)` lies on the segment of `I` for the two
taxa below its hybrid node (Proposition 7), which are a side of the cut edge out of the hybrid node
(`hasCutSplit_below_hybrid`), so a side of the given cut edge or its complement
(`cutSplit_pair_eq_or_eq_compl`): the two other quartet trees have equal concordance factors. -/
theorem cf_eq_of_not_mem_of_hasCutSplit [DecidableEq X] {Q : RootedNetwork V E X}
    {θ : MetricData E} (hQ : IsLSAQuartet Q θ) (h4 : ¬ ∃ C v k, InducesCycleType Q C v 4 k)
    {B : Finset X} (hB : #B = 2) (hcut : Q.HasCutSplit ↑B) {r r' : QuartetTree X} (hr : B ∉ r.val)
    (hr' : B ∉ r'.val) : cf Q θ r = cf Q θ r' := by
  -- the decidable equality of the statement is the classical one
  obtain rfl : ‹DecidableEq X› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have htaxa : ∀ q : QuartetTree X, q.taxa = univ := fun q =>
    eq_univ_of_card _ (by rw [q.card_taxa, hQ.card_taxa])
  by_cases h32 : ∃ C v, InducesCycleType Q C v 3 2
  · -- Proposition 7: the segment of the two taxa below the hybrid node of the `3₂`-cycle
    obtain ⟨C, v, hC⟩ := h32
    obtain ⟨a, b, hab, hD⟩ := Set.ncard_eq_two.1 hC.2.2.2.2
    have hseg := onSegmentOfI_below_hybrid_of_threeTwo hQ hC hab hD
    have hDc : Q.HasCutSplit ↑({a, b} : Finset X) := by
      rw [coe_pair, ← hD]
      exact hasCutSplit_below_hybrid hQ.binary hQ.levelOne hC.2.2.1
    have key : ∀ q : QuartetTree X, B ∉ q.val → ({a, b} : Finset X) ∉ q.val := by
      intro q hq hq'
      apply hq
      rcases cutSplit_pair_eq_or_eq_compl hQ.binary.1 hQ.card_taxa hB (card_pair hab) hcut hDc with
        rfl | rfl
      · exact hq'
      · have := q.sdiff_mem hq'
        rwa [htaxa q, ← compl_eq_univ_sdiff] at this
    exact hseg.2.1 r r' (key r hr) (key r' hr')
  · -- Proposition 6: the ordering of the species tree of the contracted network, equation (1)
    have hord := proposition6 hQ h32
    obtain ⟨σ, -, hσcut, hcf⟩ :=
      exists_speciesTree_contractRooted hQ h32 h4 (IsTwoOrThreeOne Q) rfl
    have ht := orderedAsQuartetTree_quartetProb hQ.card_taxa σ hB ((hσcut B hB).1 hcut)
    rw [← hcf] at ht
    have e := ht.2 r r' hr hr'
    have hrr : r.taxa = r'.taxa := (htaxa r).trans (htaxa r').symm
    exact le_antisymm ((hord r r' hrr).2 e.le) ((hord r' r hrr.symm).2 e.ge)

end Quartet

section Main

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Concordance factors with the same ordering have the same Big Cycle property. -/
theorem bigCycleOn_iff_of_sameOrdering {p p' : QuartetTree X → ℝ} (h : SameOrdering p p')
    (s : Finset X) : BigCycleOn p s ↔ BigCycleOn p' s := by
  have key : ∀ q r : QuartetTree X, q.taxa = r.taxa → (p q = p r ↔ p' q = p' r) := fun q r hqr => by
    rw [le_antisymm_iff, le_antisymm_iff, h q r hqr, h r q hqr.symm]
  constructor
  · intro hb q hq r hr hne heq
    exact hb q hq r hr hne ((key q r ((mem_treesOn.1 hq).trans (mem_treesOn.1 hr).symm)).2 heq)
  · intro hb q hq r hr hne heq
    exact hb q hq r hr hne ((key q r ((mem_treesOn.1 hq).trans (mem_treesOn.1 hr).symm)).1 heq)

omit [Fintype X] [DecidableEq X] in
/-- **Without a cycle of size at least four in `N⁻`, no `Q⁻_s` has a 4-cycle**: a 4-cycle of `Q⁻_s`
comes from a cycle of `N⁻` of size at least four (`exists_separates_of_fourCycle`). -/
theorem not_hasFourCycle_of_ncard_le_three {V E : Type*} [Fintype V] [Fintype E]
    {N : RootedNetwork V E X} (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hX : Nontrivial X) {θ : MetricData E} (hθ : IsMetricNetwork N θ)
    (hsize : ∀ C, IsCycle (unrooted N hN hX).graph C → C.ncard ≤ 3) {s : Finset X} (hs : #s = 4) :
    ¬ HasFourCycle N hN s hs := by
  rintro ⟨C₀, v₀, k, hC₀⟩
  obtain ⟨C, hC, hC4, w, hw, -⟩ :=
    (inducesCycleType_iff (isLSAQuartet_quartetLSA hN h1 hθ hs) 4 k).1 ⟨C₀, v₀, hC₀⟩
  obtain ⟨C', w', h4, hC', -⟩ := exists_separates_of_fourCycle hN h1 hX hs hC hC4 hw
  have := hsize C' hC'
  omega

omit [Fintype X] in
/-- **A cut arc of `N` gives a cut edge of `Q⊕_s`**: if the arc `f` separates `A` from its
complement, and both `A` and its complement meet the four taxa `s`, the taxa of `A` in `s` are a
side of a cut edge of `Q⊕_s` (`hasCutSplitOn_iff_separates`,
`hasCutSplitOn_iff_inducedNetwork_hasCutSplit`). -/
theorem quartetLSA_hasCutSplit_of_separates {V E : Type*} {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) {s : Finset X} (hs : #s = 4) {A : Finset X}
    (hA₁ : (A ∩ s).Nonempty) (hA₂ : (s \ A).Nonempty) {f : E}
    (hf : N.Separates f ↑A (↑A)ᶜ ∨ N.Separates f (↑A)ᶜ ↑A) :
    (quartetLSA N hN.1 s hs).HasCutSplit (Subtype.val ⁻¹' ↑A) := by
  have h₁ : ((↑s : Set X) ∩ ↑A).Nonempty := by
    obtain ⟨x, hx⟩ := hA₁
    rw [mem_inter] at hx
    exact ⟨x, hx.2, hx.1⟩
  have h₂ : ((↑s : Set X) \ ↑A).Nonempty := by
    obtain ⟨x, hx⟩ := hA₂
    rw [mem_sdiff] at hx
    exact ⟨x, hx.1, hx.2⟩
  refine (hasCutSplitOn_iff_inducedNetwork_hasCutSplit hN.1 _ h₁ h₂).1 ?_
  rw [hasCutSplitOn_iff_separates hN.1]
  rcases hf with hf | hf
  · exact ⟨f, Or.inl ⟨h₁, hf.mono Set.inter_subset_right fun x hx => hx.2⟩⟩
  · exact ⟨f, Or.inr ⟨h₂, hf.mono (fun x hx => hx.2) Set.inter_subset_right⟩⟩

/-- **A quartet tree displayed by `Ñ` has alternatives of equal concordance factors**, when `N⁻` has
no cycle of size at least four (Baños 2019, proof of Theorem 4): the side `A` of an edge of `Ñ` that
splits the four taxa of the quartet tree into its two cherries is a side of a cut arc of `N`
(`tildeNetwork_facts`), which gives a cut edge of `Q⊕_s` between the two cherries
(`quartetLSA_hasCutSplit_of_separates`); `Q⁻_s` has no 4-cycle
(`not_hasFourCycle_of_ncard_le_three`), so by Propositions 6 and 7 the two other quartet trees have
equal concordance factors in `Q⊕_s` (`cf_eq_of_not_mem_of_hasCutSplit`), which are those of `N`
(Theorem 2, `cf_quartetLSA`). -/
theorem alternatives_eq_of_displays {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph) (hX : Nontrivial X)
    {θ : MetricData E} (hθ : IsMetricNetwork N θ)
    (hsize : ∀ C, IsCycle (unrooted N hN hX).graph C → C.ncard ≤ 3) {F : Finset (Finset X)}
    (hF : ∀ A ∈ F, ∃ f, N.Separates f (↑A : Set X) (↑A)ᶜ ∨ N.Separates f (↑A)ᶜ ↑A)
    {s : QuartetTree X} (hs : Displays F s) :
    ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, cf N θ r = cf N θ r' := by
  -- the decidable equality of the statement is the classical one
  obtain rfl : ‹DecidableEq X› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  obtain ⟨A, hA, hAs⟩ := hs
  obtain ⟨f, hf⟩ := hF A hA
  set t := s.taxa with ht_def
  have ht : #t = 4 := s.card_taxa
  -- the cut edge of `Q⊕_t` between the two cherries of `s`
  have hA₁ : (A ∩ t).Nonempty := card_pos.1 (by rw [s.card_of_mem hAs]; norm_num)
  have hA₂ : (t \ A).Nonempty := by
    obtain ⟨y, hy⟩ := card_pos.1 (show 0 < #(t \ (A ∩ t)) by
      rw [s.card_of_mem (s.sdiff_mem hAs)]; norm_num)
    rw [mem_sdiff, mem_inter] at hy
    exact ⟨y, mem_sdiff.2 ⟨hy.1, fun h => hy.2 ⟨h, hy.1⟩⟩⟩
  have hcut := quartetLSA_hasCutSplit_of_separates hN ht hA₁ hA₂ hf
  set B : Finset (t : Set X) := univ.filter fun x => x.1 ∈ A with hB_def
  have hBcoe : (↑B : Set (t : Set X)) = Subtype.val ⁻¹' ↑A := by
    ext x
    simp [B]
  have hBimg : B.image Subtype.val = A ∩ t := by
    ext x
    simp only [B, mem_image, mem_filter, mem_univ, true_and, mem_inter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨hxA, hxt⟩
      exact ⟨⟨x, hxt⟩, hxA, rfl⟩
  have hB : #B = 2 := by
    rw [← card_image_of_injective B Subtype.val_injective, hBimg, s.card_of_mem hAs]
  -- each alternative of `s` is the image of a quartet tree on `t` without the cherry `B`
  have hlift : ∀ r ∈ s.alternatives, ∃ q : QuartetTree (t : Set X),
      q.map Subtype.val_injective = r ∧ B ∉ q.val := by
    intro r hr
    obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr
    obtain ⟨q, rfl⟩ := QuartetTree.exists_map_eq Subtype.val_injective r
      (by rw [hrt, image_val_univ_finsetCoe])
    refine ⟨q, rfl, fun hBq => hrs ?_⟩
    have hmem : A ∩ t ∈ (q.map Subtype.val_injective).val := by
      rw [QuartetTree.map_val, ← hBimg]
      exact mem_image_of_mem _ hBq
    exact quartetTree_eq_of_taxa_eq_of_mem hrt hmem hAs
  intro r hr r' hr'
  obtain ⟨q, rfl, hq⟩ := hlift r hr
  obtain ⟨q', rfl, hq'⟩ := hlift r' hr'
  have hcf := cf_quartetLSA hN h1 hθ ht
  rw [← congrFun hcf q, ← congrFun hcf q']
  exact cf_eq_of_not_mem_of_hasCutSplit (isLSAQuartet_quartetLSA hN h1 hθ ht)
    (not_hasFourCycle_of_ncard_le_three hN h1 hX hθ hsize ht) hB (hBcoe ▸ hcut) hq hq'

/-- **Trees with the same ordering of concordance factors display the same quartet trees** (Baños
2019, proof of Theorem 4): two trees, given by their splits, resolving every set of four taxa, each
displaying only quartet trees whose two alternatives have equal concordance factors, for concordance
factors with the same ordering and not all equal on any set of four taxa, display the same quartet
trees. On each set of four taxa the displayed quartet tree is the one whose concordance factor
differs from the two others, which the ordering tells. -/
theorem displays_iff_of_alternatives_eq {F₁ F₂ : Finset (Finset X)} {p₁ p₂ : QuartetTree X → ℝ}
    (hres₁ : ∀ q : Finset X, #q = 4 → ∃ s ∈ treesOn q, Displays F₁ s)
    (hres₂ : ∀ q : Finset X, #q = 4 → ∃ s ∈ treesOn q, Displays F₂ s)
    (halt₁ : ∀ s, Displays F₁ s → ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p₁ r = p₁ r')
    (halt₂ : ∀ s, Displays F₂ s → ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p₂ r = p₂ r')
    (hnd₁ : NonDegenerateCF p₁) (hnd₂ : NonDegenerateCF p₂) (hord : SameOrdering p₁ p₂)
    (s : QuartetTree X) : Displays F₁ s ↔ Displays F₂ s := by
  have key : ∀ {F F' : Finset (Finset X)} {p p' : QuartetTree X → ℝ},
      (∀ q : Finset X, #q = 4 → ∃ s ∈ treesOn q, Displays F' s) →
      (∀ s, Displays F s → ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p r = p r') →
      (∀ s, Displays F' s → ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p' r = p' r') →
      NonDegenerateCF p' → SameOrdering p p' → ∀ s, Displays F s → Displays F' s := by
    intro F F' p p' hres' halt halt' hnd' hord' s hs
    obtain ⟨s₂, hs₂, hd₂⟩ := hres' s.taxa s.card_taxa
    by_cases he : s₂ = s
    · exact he ▸ hd₂
    exfalso
    have hs₂alt : s₂ ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hs₂, he⟩
    obtain ⟨s₃, hs₃⟩ : ∃ s₃, s.alternatives.erase s₂ = {s₃} :=
      card_eq_one.1 (by rw [card_erase_of_mem hs₂alt, s.card_alternatives])
    have hs₃m : s₃ ∈ s.alternatives.erase s₂ := by rw [hs₃]; exact mem_singleton_self s₃
    have hs₃alt : s₃ ∈ s.alternatives := mem_of_mem_erase hs₃m
    have hs₃₂ : s₃ ≠ s₂ := ne_of_mem_erase hs₃m
    obtain ⟨hs₃t, hs₃s⟩ := QuartetTree.mem_alternatives.1 hs₃alt
    obtain ⟨hs₂t, -⟩ := QuartetTree.mem_alternatives.1 hs₂alt
    have e1 : p s₂ = p s₃ := halt s hs s₂ hs₂alt s₃ hs₃alt
    have e2 : p' s₂ = p' s₃ := le_antisymm ((hord' s₂ s₃ (hs₂t.trans hs₃t.symm)).1 e1.le)
      ((hord' s₃ s₂ (hs₃t.trans hs₂t.symm)).1 e1.ge)
    have e3 : p' s = p' s₃ := halt' s₂ hd₂ s
      (QuartetTree.mem_alternatives.2 ⟨hs₂t.symm, Ne.symm he⟩) s₃
      (QuartetTree.mem_alternatives.2 ⟨hs₃t.trans hs₂t.symm, hs₃₂⟩)
    have hall : ∀ r ∈ treesOn s.taxa, p' r = p' s := by
      intro r hr
      by_cases hrs : r = s
      · rw [hrs]
      have hra : r ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hr, hrs⟩
      by_cases hr₂ : r = s₂
      · rw [hr₂, e2, e3]
      · have : r ∈ s.alternatives.erase s₂ := mem_erase.2 ⟨hr₂, hra⟩
        rw [hs₃, mem_singleton] at this
        rw [this, e3]
    obtain ⟨a, ha, b, hb, hab⟩ := hnd' s.taxa s.card_taxa
    exact hab ((hall a ha).trans (hall b hb).symm)
  have hord' : SameOrdering p₂ p₁ := fun q r h => (hord q r h).symm
  exact ⟨key hres₂ halt₁ halt₂ hnd₂ hord s, key hres₁ halt₂ halt₁ hnd₁ hord' s⟩

/-- **No cycle of size at least four in `N₂⁻`** when there is none in `N₁⁻`: such a cycle separates
a set of four taxa, which then has the Big Cycle property for `N₂` (Lemma 12), so also for `N₁`,
whose `N₁⁻` would have a cycle of size at least four separating it (Lemma 12). -/
theorem ncard_le_three_of_sameOrdering {V₁ E₁ V₂ E₂ : Type*} [Fintype V₁] [Fintype E₁]
    [Fintype V₂] [Fintype E₂] (hX : Nontrivial X) {N₁ : RootedNetwork V₁ E₁ X}
    {N₂ : RootedNetwork V₂ E₂ X} (hN₁ : IsBinaryRootedNetwork N₁) (hN₂ : IsBinaryRootedNetwork N₂)
    (h1₂ : IsLevelOne N₂.graph) {θ₁ : MetricData E₁} {θ₂ : MetricData E₂}
    (hθ₁ : IsMetricNetwork N₁ θ₁) (hθ₂ : IsMetricNetwork N₂ θ₂) (hg₁ : GoodParams hX N₁ θ₁)
    (hg₂ : GoodParams hX N₂ θ₂) (hord : SameOrdering (cf N₁ θ₁) (cf N₂ θ₂))
    (h0 : bigCycleCount (unrooted N₁ hN₁ hX) = 0) {C : Set (SemidirectedArc hN₂.1 hN₂.2 hX)}
    (hC : IsCycle (unrooted N₂ hN₂ hX).graph C) : C.ncard ≤ 3 := by
  by_contra hlt
  have hC4 : 4 ≤ C.ncard := by omega
  obtain ⟨v, hv⟩ := exists_isHybridNodeOf h1₂ hC
  have hn : 1 < (cycleNodes (unrooted N₂ hN₂ hX).graph C).ncard := by
    rw [ncard_cycleNodes hC]
    omega
  obtain ⟨u₁, u₂, hu₁, hu₂, hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 hn
  obtain ⟨x, hx⟩ := exists_blockNode_eq h1₂ hC hu₁
  obtain ⟨y, hy⟩ := exists_blockNode_eq h1₂ hC hu₂
  have hxy : ¬ SameBlock (unrooted N₂ hN₂ hX).graph (unrooted N₂ hN₂ hX).leaf C x y := by
    rw [sameBlock_iff_blockNode_eq h1₂ hC, hx, hy]
    exact hne
  obtain ⟨c, d, h4, hsep⟩ := exists_separatesQuartet_of_not_sameBlock h1₂ hC hC4 hv hxy
  have hbc₂ : BigCycleOn (cf N₂ θ₂) {x, y, c, d} := ((hg₂ hθ₂ hN₂).1 _ h4).2 ⟨C, v, hC4, hsep⟩
  obtain ⟨C', v', hC'4, hsep'⟩ :=
    ((hg₁ hθ₁ hN₁).1 _ h4).1 ((bigCycleOn_iff_of_sameOrdering hord _).2 hbc₂)
  have := ncard_le_three_of_bigCycleCount_eq_zero h0 hsep'.1
  omega

end Main

/-- **Theorem 4, the base case of the induction**: networks without cycles of size at least four
(Baños 2019, proof of Theorem 4, TeX l. 1180). The cycles of `N₁⁻` have size at most three, and so
have those of `N₂⁻` (`ncard_le_three_of_sameOrdering`). Then `Ñ₁` and `Ñ₂` are phylogenetic
`X`-trees whose internal nodes have degree three (`tildeNetwork_facts`), and each displays a quartet
tree on every set `s` of four taxa. "Every induced quartet tree will have no cycle of size 4"
(`not_hasFourCycle_of_ncard_le_three`), "and the ordering of the concordance factors determines the
topology of the quartet tree obtained by suppressing all 2- and 3-cycles": when `Q⁻_s` has no
`3₂`-cycle, the concordance factors are ordered as those of that tree (Proposition 6), whose quartet
tree `ab|cd` has the largest, strictly, and the two others equal; when it has one, they lie on the
segment of `I` where `CF_{ac|bd} = CF_{ad|bc}`, for `a`, `b` the taxa below its hybrid node
(Proposition 7, `cf_eq_of_not_mem_of_hasCutSplit`).

The paper does not say that this quartet tree is the one `Ñ` displays, nor how the ordering tells
it. The first holds since an edge of `Ñ` between `{a, b}` and `{c, d}` comes from a cut arc of `N`,
which gives a cut edge of `Q⊕_s` between them: the edge of the tree with the split `ab|cd`, and,
with a `3₂`-cycle, the taxa below its hybrid node are `{a, b}` or `{c, d}`, a side of the cut edge
out of that node (`alternatives_eq_of_displays`). For the second, the reading that holds is the
quartet tree whose concordance factor differs from the two others, which needs the three not to be
all equal, as they can be with a `3₂`-cycle (Proposition 7); this is generic (`NonDegenerateCF`,
part of `GoodParams`). The quartet tree need not have the largest concordance factor: with a
`3₂`-cycle it can have the smallest (Example 6, `(32, 33, 33)/98`). So `Ñ₁` and `Ñ₂` display the
same quartet trees (`displays_iff_of_alternatives_eq`), and "these then determine the topology `Ñ`
by a standard result" (Semple and Steel 2003, `External.SempleSteel2003.exists_iso_of_quartets_eq`):
there is an isomorphism of the two trees fixing the taxa, which is an isomorphism of `Ñ₁` and `Ñ₂`
(`nonempty_sdIso_of_iso`). -/
theorem tildeDetermined_zero : TildeDetermined 0 := by
  intro X _ _ hX V₁ E₁ V₂ E₂ _ _ _ _ N₁ N₂ hN₁ hN₂ h1₁ h1₂ θ₁ θ₂ hθ₁ hθ₂ hg₁ hg₂ hord h0
  have hs₁ : ∀ C, IsCycle (unrooted N₁ hN₁ hX).graph C → C.ncard ≤ 3 := fun C hC =>
    ncard_le_three_of_bigCycleCount_eq_zero h0 hC
  have hs₂ : ∀ C, IsCycle (unrooted N₂ hN₂ hX).graph C → C.ncard ≤ 3 := fun C hC =>
    ncard_le_three_of_sameOrdering hX hN₁ hN₂ h1₂ hθ₁ hθ₂ hg₁ hg₂ hord h0 hC
  obtain ⟨hT₁, hd₁, hX₁, hi₁, hl₁, h3₁, hsep₁⟩ := tildeNetwork_facts hN₁ h1₁ hs₁
  obtain ⟨hT₂, hd₂, hX₂, hi₂, hl₂, h3₂, hsep₂⟩ := tildeNetwork_facts hN₂ h1₂ hs₂
  have hQ : External.SempleSteel2003.quartets
      (tildeNetwork (unrooted N₁ hN₁ hX)).graph.toSimpleGraph
      (tildeNetwork (unrooted N₁ hN₁ hX)).leaf =
      External.SempleSteel2003.quartets (tildeNetwork (unrooted N₂ hN₂ hX)).graph.toSimpleGraph
        (tildeNetwork (unrooted N₂ hN₂ hX)).leaf :=
    Set.ext fun s => displays_iff_of_alternatives_eq
      (fun q hq => exists_displays_splitFinset hX₁ hi₁ hl₁ (fun v hv => (h3₁ v hv).le) hq)
      (fun q hq => exists_displays_splitFinset hX₂ hi₂ hl₂ (fun v hv => (h3₂ v hv).le) hq)
      (fun s hs => alternatives_eq_of_displays hN₁ h1₁ hX hθ₁ hs₁
        (fun A hA => hsep₁ _ (External.SempleSteel2003.mem_splitFinset.1 hA)) hs)
      (fun s hs => alternatives_eq_of_displays hN₂ h1₂ hX hθ₂ hs₂
        (fun A hA => hsep₂ _ (External.SempleSteel2003.mem_splitFinset.1 hA)) hs)
      (hg₁ hθ₁ hN₁).2 (hg₂ hθ₂ hN₂).2 hord s
  obtain ⟨f, hf⟩ := External.SempleSteel2003.exists_iso_of_quartets_eq ⟨hX₁, hi₁, hl₁⟩
    ⟨hX₂, hi₂, hl₂⟩ hQ
  exact nonempty_sdIso_of_iso hT₁ hT₂ hd₁ hd₂ f hf

end Banos2019
