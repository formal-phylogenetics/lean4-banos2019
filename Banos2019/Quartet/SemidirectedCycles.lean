module

public import Banos2019.Network.SDPath
public import Banos2019.Quartet.CycleBlocks

/-!
# The cycles and the descendants of `N⁻` in the terms of `N` (Baños 2019, Section 5)

For a binary network `M` whose root is the LSA of its taxa, the nodes of `N⁻ = semidirected M` are the
nodes of `M` other than the root, and its edges the arcs of `M` other than the arc `e₀ = sdRootArc`
out of the root, which is merged into the other arc out of the root.

* `semidirected_graph_isAcyclic`: the edges of `N⁻`, oriented from source to target, form an acyclic
  graph: no edge enters the child of `e₀`.
* `descendsFrom_semidirected_iff`: the taxa descending from a hybrid node in `N⁻` are those below it
  in `M`: a semidirected path from a hybrid node never goes up a tree edge.
* `liftEdges`: the arcs of `M` of a set of edges of `N⁻`, with `e₀` when the merged edge is one of
  them. `isCycle_liftEdges`, `isCycle_iff_liftEdges`: the cycles of `N⁻` are the cycles of `M`, with
  `liftEdges`; `ncard_liftEdges`, `root_mem_cycleNodes_liftEdges_iff`: a cycle of `M` through the root
  has one edge more than the cycle of `N⁻`; `isHybridNodeOf_iff`: their hybrid nodes are the same.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section SemidirectedCycles

variable {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) (hB : M.IsBinary) (hX : Nontrivial X)

/-- No edge of `N⁻` enters the child of the arc `e₀` merged at the LSA: `e₀` is a tree arc. -/
theorem target_sdArc_ne (g : SemidirectedArc hM hB hX) :
    M.graph.target (sdArc hM hB hX g) ≠ M.graph.target (sdRootArc hM hB hX) := by
  have := hM.finite_arcs
  intro h
  have hne : sdArc hM hB hX g ≠ sdRootArc hM hB hX := fun h' => g.2 (Subtype.ext h')
  have h1 := (sdRootArc_spec hM hB hX).2
  unfold IsTreeArc DirectedMultigraph.indegree at h1
  have : 2 ≤ ({e | M.graph.target e = M.graph.target (sdRootArc hM hB hX)}).ncard := by
    rw [← Set.ncard_pair hne]
    exact Set.ncard_le_ncard (by rintro f (rfl | rfl) <;> simp [h]) (Set.toFinite _)
  omega

/-- A node of `N⁻` other than the child of `e₀`: the edges leaving it in `N⁻` leave it in `M`. -/
theorem sdVert_source_of_ne_target_sdRootArc (g : SemidirectedArc hM hB hX)
    (hg : sdVert hM hX ((semidirected hM hB hX).graph.source g) ≠
      M.graph.target (sdRootArc hM hB hX)) :
    sdVert hM hX ((semidirected hM hB hX).graph.source g) = M.graph.source (sdArc hM hB hX g) ∧
      M.graph.source (sdArc hM hB hX g) ≠ lsa hM Set.univ Set.univ_nonempty := by
  have h := sdVert_source hM hB hX g
  split_ifs at h with hs
  · exact absurd h hg
  · exact ⟨h, hs⟩

/-- **The graph of `N⁻` is acyclic**: a closed directed path would enter the child of `e₀` to use the
merged edge, so it is a closed directed path of `M`. -/
theorem semidirected_graph_isAcyclic : (semidirected hM hB hX).graph.IsAcyclic := by
  set G := semidirected hM hB hX
  have key : ∀ a b, Relation.TransGen G.graph.Adj a b →
      sdVert hM hX a ≠ M.graph.target (sdRootArc hM hB hX) →
      Relation.TransGen M.graph.Adj (sdVert hM hX a) (sdVert hM hX b) ∧
        sdVert hM hX b ≠ M.graph.target (sdRootArc hM hB hX) := by
    intro a b h ha
    induction h with
    | single hab =>
      obtain ⟨g, rfl, rfl⟩ := hab
      refine ⟨.single ⟨sdArc hM hB hX g, (sdVert_source_of_ne_target_sdRootArc hM hB hX g ha).1.symm, rfl⟩, ?_⟩
      rw [sdVert_target]
      exact target_sdArc_ne hM hB hX g
    | tail _ hbc ih =>
      obtain ⟨h₁, h₂⟩ := ih
      obtain ⟨g, hgs, rfl⟩ := hbc
      subst hgs
      refine ⟨h₁.tail ⟨sdArc hM hB hX g, (sdVert_source_of_ne_target_sdRootArc hM hB hX g h₂).1.symm, rfl⟩, ?_⟩
      rw [sdVert_target]
      exact target_sdArc_ne hM hB hX g
  intro u hu
  -- the last edge enters `u`, which is therefore not the child of `e₀`
  have hu' : sdVert hM hX u ≠ M.graph.target (sdRootArc hM hB hX) := by
    obtain ⟨c, -, g, -, hg⟩ := Relation.TransGen.tail'_iff.1 hu
    rw [← hg, sdVert_target]
    exact target_sdArc_ne hM hB hX g
  exact hM.acyclic _ (key u u hu hu').1

/-- **The taxa descending from a hybrid node of `N⁻` are those below it in `M`.** A semidirected path
from the hybrid node `v` never goes against a tree edge: the node it enters along an edge has no other
tree edge entering it, and that edge leads back to a node already on the path. So it follows the
arcs of `M`, never entering the child of `e₀` and so never using the merged edge. Conversely a path of
`M` from `v` stays below `v`, away from the root, and is a path of `N⁻`. -/
theorem descendsFrom_semidirected_iff (v : SemidirectedVertex hM hX)
    (h2 : M.graph.indegree (sdVert hM hX v) = 2) (x : X) :
    DescendsFrom (semidirected hM hB hX) v x ↔ M.graph.Reaches (sdVert hM hX v) (M.leaf x) := by
  have := hM.finite_arcs
  set G := semidirected hM hB hX
  -- two edges of `N⁻` entering a node: the first is hybrid
  have hH : ∀ g g', g ≠ g' → G.graph.target g = G.graph.target g' → G.IsDirected g := by
    intro g g' hne ht
    rw [semidirected_isDirected_iff]
    unfold IsHybridArc DirectedMultigraph.indegree
    rw [← Set.ncard_pair (fun h => hne (sdArc_injective hM hB hX h))]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro f (rfl | rfl)
    · rfl
    · have := congrArg (sdVert hM hX) ht
      rw [sdVert_target, sdVert_target] at this
      simp [this]
  have hv₀ : sdVert hM hX v ≠ M.graph.target (sdRootArc hM hB hX) := by
    intro h
    have h1 := (sdRootArc_spec hM hB hX).2
    unfold IsTreeArc at h1
    rw [← h, h2] at h1
    exact absurd h1 (by norm_num)
  constructor
  · rintro ⟨P, S, hP⟩
    -- the invariant: the tree edges entering the current node come from off the rest of the path
    have key : ∀ a w S P, IsSDP G a w S P →
        sdVert hM hX a ≠ M.graph.target (sdRootArc hM hB hX) →
        (∀ g, G.graph.target g = a → ¬ G.IsDirected g → G.graph.source g ∉ S) →
        M.graph.Reaches (sdVert hM hX a) (sdVert hM hX w) := by
      intro a w S P h
      induction h with
      | nil u => exact fun _ _ => .refl
      | @cons e a b w S P hs ha h ih =>
        intro ha₀ hinv
        rcases hs with ⟨hsa, htb⟩ | ⟨hnd, hta, hsb⟩
        · have hb₀ : sdVert hM hX b ≠ M.graph.target (sdRootArc hM hB hX) := by
            rw [← htb, sdVert_target]
            exact target_sdArc_ne hM hB hX e
          refine Relation.ReflTransGen.head ⟨sdArc hM hB hX e, ?_, ?_⟩ (ih hb₀ fun g hg hgd => ?_)
          · rw [← hsa]
            exact (sdVert_source_of_ne_target_sdRootArc hM hB hX e (hsa ▸ ha₀)).1.symm
          · rw [← htb, sdVert_target]
          · by_cases hge : g = e
            · rw [hge, hsa]
              exact ha
            · exact absurd (hH g e hge (hg.trans htb.symm)) hgd
        · have hbS : b ∈ S := by cases h <;> simp
          exact absurd (Set.mem_insert_of_mem a (hsb ▸ hbS)) (hinv e hta hnd)
    refine key _ _ _ _ hP.isSDP hv₀ fun g hg hgd => absurd ?_ hgd
    rw [semidirected_isDirected_iff]
    unfold IsHybridArc
    rw [← sdVert_target, hg, h2]
  · intro h
    obtain ⟨S, P, hp⟩ := IsDPath.of_reaches h
    have hvl : sdVert hM hX v ≠ lsa hM Set.univ Set.univ_nonempty :=
      ((mem_range_sdVert hM hX _).1 ⟨v, rfl⟩).2
    have hlv : M.graph.Reaches (lsa hM Set.univ Set.univ_nonempty) (sdVert hM hX v) :=
      ((mem_range_sdVert hM hX _).1 ⟨v, rfl⟩).1
    have hdp := hp.pullback (H' := G.graph) (sdVert hM hX) (sdArc hM hB hX)
      (sdVert_injective hM hX) (sdArc_injective hM hB hX) (fun e he => ?_) rfl (sdVert_leaf hM hB hX x)
    · exact ⟨_, _, IsDPath.isSDPath (semidirected_graph_isAcyclic hM hB hX) rfl hdp⟩
    · have hs := (hp.reaches_of_mem (hp.ends_mem he).1).1
      have hsl : M.graph.source e ≠ lsa hM Set.univ Set.univ_nonempty := fun h' =>
        hvl (eq_of_reaches_of_reaches hM.acyclic (h' ▸ hs) hlv)
      obtain ⟨g, rfl⟩ := (mem_range_sdArc hM hB hX e).2 ⟨hlv.trans hs, fun h' => hsl (by
        rw [h']; exact (sdRootArc_spec hM hB hX).1)⟩
      refine ⟨g, rfl, ?_, (sdVert_target hM hB hX g).symm⟩
      rw [sdVert_source]
      split_ifs with h'
      · exact absurd h' hsl
      · rfl

/-- The arcs of `M` of a set `D` of edges of `N⁻`, with `e₀` when the edge merged at the LSA is in
`D`. -/
def liftEdges (D : Set (SemidirectedArc hM hB hX)) : Set E :=
  {f | ∃ g ∈ D, f = sdArc hM hB hX g ∨
    (M.graph.source (sdArc hM hB hX g) = lsa hM Set.univ Set.univ_nonempty ∧
      f = sdRootArc hM hB hX)}

theorem sdArc_ne_sdRootArc (g : SemidirectedArc hM hB hX) :
    sdArc hM hB hX g ≠ sdRootArc hM hB hX := fun h => g.2 (Subtype.ext h)

theorem sdVert_ne_lsa (u : SemidirectedVertex hM hX) :
    sdVert hM hX u ≠ lsa hM Set.univ Set.univ_nonempty :=
  ((mem_range_sdVert hM hX _).1 ⟨u, rfl⟩).2

theorem sdArc_mem_liftEdges_iff (D : Set (SemidirectedArc hM hB hX)) (g : SemidirectedArc hM hB hX) :
    sdArc hM hB hX g ∈ liftEdges hM hB hX D ↔ g ∈ D := by
  constructor
  · rintro ⟨g', hg', h | ⟨-, h⟩⟩
    · exact sdArc_injective hM hB hX h ▸ hg'
    · exact absurd h (sdArc_ne_sdRootArc hM hB hX g)
  · exact fun hg => ⟨g, hg, Or.inl rfl⟩

/-- The two ends in `N⁻` of an edge, in the terms of `M`: the merged edge leaves the child of
`e₀`. -/
theorem sdVert_source_cases (g : SemidirectedArc hM hB hX) :
    (M.graph.source (sdArc hM hB hX g) ≠ lsa hM Set.univ Set.univ_nonempty ∧
      sdVert hM hX ((semidirected hM hB hX).graph.source g) = M.graph.source (sdArc hM hB hX g)) ∨
    (M.graph.source (sdArc hM hB hX g) = lsa hM Set.univ Set.univ_nonempty ∧
      sdVert hM hX ((semidirected hM hB hX).graph.source g) =
        M.graph.target (sdRootArc hM hB hX)) := by
  have h := sdVert_source hM hB hX g
  split_ifs at h with hs
  · exact Or.inr ⟨hs, h⟩
  · exact Or.inl ⟨hs, h⟩

/-- At most one edge of `N⁻` leaves the LSA in `M`: the LSA has outdegree two, and `e₀` is one of its
arcs. -/
theorem eq_of_source_sdArc_eq_lsa {g g' : SemidirectedArc hM hB hX}
    (hg : M.graph.source (sdArc hM hB hX g) = lsa hM Set.univ Set.univ_nonempty)
    (hg' : M.graph.source (sdArc hM hB hX g') = lsa hM Set.univ Set.univ_nonempty) : g = g' := by
  have := hM.finite_arcs
  by_contra hne
  have hne' : sdArc hM hB hX g ≠ sdArc hM hB hX g' := fun h => hne (sdArc_injective hM hB hX h)
  have hsub : ({sdRootArc hM hB hX, sdArc hM hB hX g, sdArc hM hB hX g'} : Set E) ⊆
      {f | M.graph.source f = lsa hM Set.univ Set.univ_nonempty} := by
    rintro f (rfl | rfl | rfl)
    · exact (sdRootArc_spec hM hB hX).1
    · exact hg
    · exact hg'
  have h3 : ({sdRootArc hM hB hX, sdArc hM hB hX g, sdArc hM hB hX g'} : Set E).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hne']
    rintro (h | h)
    · exact sdArc_ne_sdRootArc hM hB hX g h.symm
    · exact sdArc_ne_sdRootArc hM hB hX g' h.symm
  have := h3 ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
  have := @lsa_univ_outdegree _ _ _ _ hM hB hX
  unfold DirectedMultigraph.outdegree at *
  omega

/-- **A cycle of `N⁻` is a cycle of `M`**, through the LSA when it has the merged edge. -/
theorem isCycle_liftEdges {D : Set (SemidirectedArc hM hB hX)}
    (hD : IsCycle (semidirected hM hB hX).graph D) : IsCycle M.graph (liftEdges hM hB hX D) := by
  set G := semidirected hM hB hX
  set m := lsa hM Set.univ Set.univ_nonempty
  set ι := sdVert hM hX
  set κ := sdArc hM hB hX
  set e₀ := sdRootArc hM hB hX
  have hι : Function.Injective ι := sdVert_injective hM hX
  have hιm : ∀ u, ι u ≠ m := sdVert_ne_lsa hM hX
  have hκe₀ : ∀ c, κ c ≠ e₀ := sdArc_ne_sdRootArc hM hB hX
  have he₀s : M.graph.source e₀ = m := (sdRootArc_spec hM hB hX).1
  have hsrc := sdVert_source_cases hM hB hX
  have hjoin : ∀ c u w, M.graph.source (κ c) ≠ m → Joins G.graph c u w →
      Joins M.graph (κ c) (ι u) (ι w) := by
    intro c u w hcm h
    have hs : ι (G.graph.source c) = M.graph.source (κ c) :=
      ((hsrc c).resolve_right fun h => hcm h.1).2
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨hs.symm.trans (congrArg ι h₁), (sdVert_target hM hB hX c).symm.trans
        (congrArg ι h₂)⟩
    · exact Or.inr ⟨hs.symm.trans (congrArg ι h₁), (sdVert_target hM hB hX c).symm.trans
        (congrArg ι h₂)⟩
  obtain ⟨k, v, e, hD, rfl⟩ := hD
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hD.pos; omega⟩
  by_cases hj : ∃ j, M.graph.source (κ (e j)) = m
  · obtain ⟨j, hj⟩ := hj
    -- read the cycle so that the merged edge is last
    have hR := hD.rotate (j + 1)
    have hlast : e (Fin.last n + (j + 1)) = e j := by
      congr 1
      rw [add_comm j 1, ← add_assoc, Fin.last_add_one, zero_add]
    have hrange : Set.range (fun i => e (i + (j + 1))) = Set.range e :=
      (Equiv.addRight (j + 1)).surjective.range_comp e
    have hP := hR.isPathOf
    have hother : ∀ l : Fin n, M.graph.source (κ (e (l.castSucc + (j + 1)))) ≠ m := fun l h => by
      have h' := hR.injective_edge ((eq_of_source_sdArc_eq_lsa hM hB hX h hj).trans hlast.symm)
      exact (Fin.castSucc_lt_last l).ne h'
    have hPN : IsPathOf M.graph Set.univ n (fun i => ι (v (i + (j + 1))))
        (fun l => κ (e (l.castSucc + (j + 1)))) :=
      ⟨fun _ => trivial, fun l => hjoin _ _ _ (hother l) (hP.link l), hι.comp hP.injective⟩
    have hjl := hR.joins (Fin.last n)
    simp only [finRotate_last, hlast] at hjl
    have hs := ((hsrc (e j)).resolve_left fun h => h.1 hj).2
    have hz : m ∉ Set.range (fun i => ι (v (i + (j + 1)))) := fun ⟨i, hi⟩ => hιm _ hi
    have hnot₀ : e₀ ∉ Set.range (fun l : Fin n => κ (e (l.castSucc + (j + 1)))) :=
      fun ⟨l, hl⟩ => hκe₀ _ hl
    have hnotj : κ (e j) ∉ Set.range (fun l : Fin n => κ (e (l.castSucc + (j + 1)))) :=
      fun ⟨l, hl⟩ => hother l (by simp only at hl; rw [hl]; exact hj)
    have hne₀j : e₀ ≠ κ (e j) := fun h => hκe₀ _ h.symm
    have hcalc : liftEdges hM hB hX (Set.range e) = insert e₀ (insert (κ (e j))
        (Set.range fun l : Fin n => κ (e (l.castSucc + (j + 1))))) := by
      ext f
      constructor
      · rintro ⟨c, hc, rfl | ⟨-, rfl⟩⟩
        · rw [← hrange] at hc
          obtain ⟨i, rfl⟩ := hc
          induction i using Fin.lastCases with
          | last => exact Or.inr (Or.inl (by simp only; rw [hlast]))
          | cast l => exact Or.inr (Or.inr ⟨l, rfl⟩)
        · exact Or.inl rfl
      · rintro (rfl | rfl | ⟨l, rfl⟩)
        · exact ⟨e j, ⟨j, rfl⟩, Or.inr ⟨hj, rfl⟩⟩
        · exact ⟨e j, ⟨j, rfl⟩, Or.inl rfl⟩
        · exact ⟨_, ⟨_, rfl⟩, Or.inl rfl⟩
    rw [hcalc]
    rcases hjl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · -- the path ends at the child of `e₀`: close it by `e₀` and the merged edge
      have hend : ι (v (Fin.last n + (j + 1))) = M.graph.target e₀ := by rw [← h₁]; exact hs
      have h0 : ι (v (0 + (j + 1))) = M.graph.target (κ (e j)) := by rw [← h₂]; rfl
      exact hPN.isCycle_insert_insert hz hnotj hne₀j (Or.inr ⟨he₀s, hend.symm⟩)
        (Or.inl ⟨hj, h0.symm⟩)
    · -- the path starts at the child of `e₀`: close it by the merged edge and `e₀`
      have h0 : ι (v (0 + (j + 1))) = M.graph.target e₀ := by rw [← h₁]; exact hs
      have hend : ι (v (Fin.last n + (j + 1))) = M.graph.target (κ (e j)) := by rw [← h₂]; rfl
      rw [Set.insert_comm]
      exact hPN.isCycle_insert_insert hz hnot₀ hne₀j.symm (Or.inr ⟨hj, hend.symm⟩)
        (Or.inl ⟨he₀s, h0.symm⟩)
  · push Not at hj
    refine ⟨n + 1, fun i => ι (v i), fun i => κ (e i), ⟨hD.pos, fun i => hjoin _ _ _ (hj i)
      (hD.joins i), hι.comp hD.injective_node, (sdArc_injective hM hB hX).comp hD.injective_edge⟩,
      ?_⟩
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, ⟨i, rfl⟩, Or.inl rfl⟩
    · rintro ⟨c, ⟨i, rfl⟩, rfl | ⟨h, -⟩⟩
      · exact ⟨i, rfl⟩
      · exact absurd h (hj i)

/-- The nodes of a cycle of `N⁻` are nodes of the cycle of `M`. -/
theorem sdVert_mem_cycleNodes_liftEdges_iff (D : Set (SemidirectedArc hM hB hX))
    (u : SemidirectedVertex hM hX) :
    sdVert hM hX u ∈ cycleNodes M.graph (liftEdges hM hB hX D) ↔
      u ∈ cycleNodes (semidirected hM hB hX).graph D := by
  constructor
  · rintro ⟨f, ⟨g, hg, rfl | ⟨hgm, rfl⟩⟩, hu | hu⟩
    · refine ⟨g, hg, Or.inl (sdVert_injective hM hX ?_)⟩
      rcases sdVert_source_cases hM hB hX g with ⟨hne, h⟩ | ⟨hm, -⟩
      · rw [h, hu]
      · exact absurd (hm.symm.trans hu) (sdVert_ne_lsa hM hX u).symm
    · exact ⟨g, hg, Or.inr (sdVert_injective hM hX (by rw [sdVert_target, hu]))⟩
    · exact absurd (hu.symm.trans (sdRootArc_spec hM hB hX).1) (sdVert_ne_lsa hM hX u)
    · refine ⟨g, hg, Or.inl (sdVert_injective hM hX ?_)⟩
      rcases sdVert_source_cases hM hB hX g with ⟨hne, -⟩ | ⟨-, h⟩
      · exact absurd hgm hne
      · rw [h, hu]
  · rintro ⟨g, hg, hu | hu⟩
    · rcases sdVert_source_cases hM hB hX g with ⟨-, h⟩ | ⟨hm, h⟩
      · exact ⟨sdArc hM hB hX g, ⟨g, hg, Or.inl rfl⟩, Or.inl (h.symm.trans (congrArg _ hu))⟩
      · exact ⟨sdRootArc hM hB hX, ⟨g, hg, Or.inr ⟨hm, rfl⟩⟩,
          Or.inr (h.symm.trans (congrArg _ hu))⟩
    · exact ⟨sdArc hM hB hX g, ⟨g, hg, Or.inl rfl⟩,
        Or.inr ((sdVert_target hM hB hX g).symm.trans (congrArg _ hu))⟩

/-- `liftEdges` is injective. -/
theorem liftEdges_injective : Function.Injective (liftEdges hM hB hX) := by
  intro D D' h
  ext g
  rw [← sdArc_mem_liftEdges_iff hM hB hX D, ← sdArc_mem_liftEdges_iff hM hB hX D', h]

/-- The LSA is a node of the cycle of `M` exactly when the merged edge is an edge of the cycle of
`N⁻`. -/
theorem lsa_mem_cycleNodes_liftEdges_iff (hr : lsa hM Set.univ Set.univ_nonempty = M.root)
    (D : Set (SemidirectedArc hM hB hX)) :
    lsa hM Set.univ Set.univ_nonempty ∈ cycleNodes M.graph (liftEdges hM hB hX D) ↔
      ∃ g ∈ D, M.graph.source (sdArc hM hB hX g) = lsa hM Set.univ Set.univ_nonempty := by
  constructor
  · rintro ⟨f, ⟨g, hg, rfl | ⟨hgm, rfl⟩⟩, hu | hu⟩
    · exact ⟨g, hg, hu⟩
    · exact absurd (hu.trans hr) (hM.target_ne_root _)
    · exact ⟨g, hg, hgm⟩
    · exact ⟨g, hg, hgm⟩
  · rintro ⟨g, hg, hgm⟩
    exact ⟨sdArc hM hB hX g, ⟨g, hg, Or.inl rfl⟩, Or.inl hgm⟩

/-- **A cycle of `M` through the LSA has one edge more than the cycle of `N⁻`**: `e₀` is added. -/
theorem ncard_liftEdges (D : Set (SemidirectedArc hM hB hX)) [Finite E] :
    (liftEdges hM hB hX D).ncard = D.ncard +
      (if ∃ g ∈ D, M.graph.source (sdArc hM hB hX g) = lsa hM Set.univ Set.univ_nonempty
        then 1 else 0) := by
  have himg : (sdArc hM hB hX '' D).ncard = D.ncard :=
    Set.ncard_image_of_injective _ (sdArc_injective hM hB hX)
  have hnot : sdRootArc hM hB hX ∉ sdArc hM hB hX '' D := fun ⟨g, _, h⟩ =>
    sdArc_ne_sdRootArc hM hB hX g h
  split_ifs with h
  · have heq : liftEdges hM hB hX D = insert (sdRootArc hM hB hX) (sdArc hM hB hX '' D) := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl | ⟨-, rfl⟩⟩
        · exact Or.inr ⟨g, hg, rfl⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨g, hg, rfl⟩)
        · obtain ⟨g, hg, hgm⟩ := h
          exact ⟨g, hg, Or.inr ⟨hgm, rfl⟩⟩
        · exact ⟨g, hg, Or.inl rfl⟩
    rw [heq, Set.ncard_insert_of_notMem hnot (Set.toFinite _), himg]
  · have heq : liftEdges hM hB hX D = sdArc hM hB hX '' D := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl | ⟨hgm, rfl⟩⟩
        · exact ⟨g, hg, rfl⟩
        · exact absurd ⟨g, hg, hgm⟩ h
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g, hg, Or.inl rfl⟩
    rw [heq, himg, Nat.add_zero]

/-- The nodes of `M` other than the LSA are nodes of `N⁻`. -/
theorem exists_sdVert_of_ne (hr : lsa hM Set.univ Set.univ_nonempty = M.root) {u : V}
    (hu : u ≠ M.root) : ∃ w, sdVert hM hX w = u :=
  (mem_range_sdVert hM hX u).2 ⟨hr ▸ hM.root_reaches u, hr ▸ hu⟩

/-- The arcs of `M` not leaving the LSA are edges of `N⁻`, with the same ends. -/
theorem exists_sdArc_of_ne (hr : lsa hM Set.univ Set.univ_nonempty = M.root) {f : E}
    (hf : M.graph.source f ≠ M.root) :
    ∃ g, sdArc hM hB hX g = f ∧
      sdVert hM hX ((semidirected hM hB hX).graph.source g) = M.graph.source f ∧
      sdVert hM hX ((semidirected hM hB hX).graph.target g) = M.graph.target f := by
  obtain ⟨g, rfl⟩ := (mem_range_sdArc hM hB hX f).2 ⟨hr ▸ hM.root_reaches _, fun h => hf (by
    rw [h, (sdRootArc_spec hM hB hX).1, hr])⟩
  refine ⟨g, rfl, ?_, sdVert_target hM hB hX g⟩
  rcases sdVert_source_cases hM hB hX g with ⟨-, h⟩ | ⟨hm, -⟩
  · exact h
  · exact absurd (hm.trans hr) hf

/-- A cycle of `M` read from the root is the cycle of `M` of a cycle of `N⁻`: its nodes other than the
root and its edges other than the two at the root form a path of `N⁻`, which the merged edge closes. -/
theorem exists_liftEdges_eq_of_root (hr : lsa hM Set.univ Set.univ_nonempty = M.root)
    (hbin : IsBinaryRootedNetwork M) {m : ℕ} {v : Fin (m + 2) → V} {e : Fin (m + 2) → E}
    (hC : IsCycleOf M.graph (m + 2) v e) (hv0 : v 0 = M.root) :
    ∃ D, IsCycle (semidirected hM hB hX).graph D ∧ liftEdges hM hB hX D = Set.range e := by
  have := hM.finite_arcs
  set G := semidirected hM hB hX
  have hnoin : ∀ f, M.graph.target f ≠ M.root := hM.target_ne_root
  have hvr : ∀ i : Fin (m + 1), v i.succ ≠ M.root := fun i h =>
    Fin.succ_ne_zero i (hC.injective_node (h.trans hv0.symm))
  -- the nodes and the inner edges as nodes and edges of `N⁻`
  choose w hw using fun i : Fin (m + 1) => exists_sdVert_of_ne hM hX hr (hvr i)
  have hlink : ∀ l : Fin m, Joins M.graph (e l.succ.castSucc) (v l.succ.castSucc) (v l.succ.succ) := by
    intro l
    have hr' : finRotate (m + 2) l.succ.castSucc = l.succ.succ := by
      ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last _).ne]
      simp
    have := hC.joins l.succ.castSucc
    rwa [hr'] at this
  have hsrc : ∀ l : Fin m, M.graph.source (e l.succ.castSucc) ≠ M.root := by
    intro l h
    rcases hlink l with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · rw [← Fin.succ_castSucc] at h₁
      exact hvr _ (h₁.symm.trans h)
    · exact hvr _ (h₁.symm.trans h)
  choose g hg using fun l : Fin m => exists_sdArc_of_ne hM hB hX hr (hsrc l)
  have hwv : ∀ l : Fin m, sdVert hM hX (w l.castSucc) = v l.succ.castSucc := fun l => by
    rw [hw, Fin.succ_castSucc]
  have hP : IsPathOf G.graph Set.univ m w g := by
    refine ⟨fun _ => trivial, fun l => ?_, fun i j h => ?_⟩
    · rcases hlink l with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · refine Or.inl ⟨sdVert_injective hM hX ?_, sdVert_injective hM hX ?_⟩
        · rw [(hg l).2.1, h₁, hwv]
        · rw [(hg l).2.2, h₂, hw]
      · refine Or.inr ⟨sdVert_injective hM hX ?_, sdVert_injective hM hX ?_⟩
        · rw [(hg l).2.1, h₁, hw]
        · rw [(hg l).2.2, h₂, hwv]
    · have := congrArg (sdVert hM hX) h
      rw [hw, hw] at this
      exact Fin.succ_injective _ (hC.injective_node this)
  -- the two edges at the root: one is `e₀`, the other the merged edge
  have hs0 : M.graph.source (e 0) = M.root := by
    rcases hC.joins 0 with ⟨h, -⟩ | ⟨-, h⟩
    · rw [h, hv0]
    · exact absurd (h.trans hv0) (hnoin _)
  have ht0 : M.graph.target (e 0) = v 1 := by
    rcases hC.joins 0 with ⟨-, h⟩ | ⟨h, h'⟩
    · rw [h]
      rfl
    · exact absurd (h'.trans hv0) (hnoin _)
  have hsl : M.graph.source (e (Fin.last (m + 1))) = M.root := by
    rcases hC.joins (Fin.last (m + 1)) with ⟨-, h⟩ | ⟨h, -⟩
    · rw [finRotate_last] at h
      exact absurd (h.trans hv0) (hnoin _)
    · rw [finRotate_last] at h
      rw [h, hv0]
  have htl : M.graph.target (e (Fin.last (m + 1))) = v (Fin.last (m + 1)) := by
    rcases hC.joins (Fin.last (m + 1)) with ⟨-, h⟩ | ⟨-, h⟩
    · rw [finRotate_last] at h
      exact absurd (h.trans hv0) (hnoin _)
    · exact h
  have h0l : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := fun h => by
    have := congrArg Fin.val h
    simp at this
  have hroot : M.root ∈ cycleNodes M.graph (Set.range e) := ⟨e 0, ⟨0, rfl⟩, Or.inl hs0⟩
  have he₀ : sdRootArc hM hB hX = e 0 ∨ sdRootArc hM hB hX = e (Fin.last (m + 1)) := by
    obtain ⟨i, hi⟩ := mem_of_source_eq_root hbin ⟨_, _, _, hC, rfl⟩ hroot
      ((sdRootArc_spec hM hB hX).1.trans hr)
    have hsi : M.graph.source (e i) = M.root := by rw [hi, (sdRootArc_spec hM hB hX).1, hr]
    rcases hC.joins i with ⟨h, -⟩ | ⟨h, -⟩
    · have : i = 0 := hC.injective_node (h.symm.trans (hsi.trans hv0.symm))
      exact Or.inl (hi ▸ this ▸ rfl)
    · have h' : finRotate (m + 2) i = 0 :=
        hC.injective_node (h.symm.trans (hsi.trans hv0.symm))
      have : i = Fin.last (m + 1) := by
        rw [← finRotate_last (n := m + 1)] at h'
        exact (finRotate (m + 2)).injective h'
      exact Or.inr (hi ▸ this ▸ rfl)
  have hlast : (Fin.last m).succ = Fin.last (m + 1) := rfl
  have h1 : ((0 : Fin (m + 1))).succ = (1 : Fin (m + 2)) := rfl
  -- the merged edge `gm` and the cycle of `N⁻`
  have key : ∀ (a b : Fin (m + 2)), (a = 0 ∧ b = Fin.last (m + 1) ∨ a = Fin.last (m + 1) ∧ b = 0) →
      sdRootArc hM hB hX = e a →
      ∃ D, IsCycle G.graph D ∧ liftEdges hM hB hX D = Set.range e := by
    intro a b hab he₀a
    have hsb : M.graph.source (e b) = M.root := by
      rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hsl
      · exact hs0
    have hab' : a ≠ b := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h0l
      · exact h0l.symm
    obtain ⟨gm, hgm⟩ := (mem_range_sdArc hM hB hX (e b)).2 ⟨hr ▸ hM.root_reaches _, fun h => hab'
      (hC.injective_edge (he₀a.symm.trans h.symm))⟩
    have hgml : M.graph.source (sdArc hM hB hX gm) = lsa hM Set.univ Set.univ_nonempty := by
      rw [hgm, hsb, hr]
    have hgms : sdVert hM hX (G.graph.source gm) = M.graph.target (e a) := by
      rw [← he₀a]
      rcases sdVert_source_cases hM hB hX gm with ⟨hne, -⟩ | ⟨-, h⟩
      · exact absurd hgml hne
      · exact h
    have hgmt : sdVert hM hX (G.graph.target gm) = M.graph.target (e b) := by
      rw [sdVert_target, hgm]
    have hgmg : gm ∉ Set.range g := by
      rintro ⟨l, hl⟩
      have := (hg l).1
      rw [hl, hgm] at this
      exact hsrc l (this ▸ hsb)
    have hj : Joins G.graph gm (w (Fin.last m)) (w 0) := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine Or.inr ⟨sdVert_injective hM hX ?_, sdVert_injective hM hX ?_⟩
        · rw [hgms, ht0, hw, h1]
        · rw [hgmt, htl, hw, hlast]
      · refine Or.inl ⟨sdVert_injective hM hX ?_, sdVert_injective hM hX ?_⟩
        · rw [hgms, htl, hw, hlast]
        · rw [hgmt, ht0, hw, h1]
    refine ⟨insert gm (Set.range g), hP.isCycle_insert hgmg hj, ?_⟩
    ext f
    constructor
    · rintro ⟨c, hc, rfl | ⟨-, rfl⟩⟩
      · rcases hc with rfl | ⟨l, rfl⟩
        · exact ⟨b, hgm.symm⟩
        · exact ⟨_, (hg l).1.symm⟩
      · exact ⟨a, he₀a.symm⟩
    · rintro ⟨i, rfl⟩
      by_cases hia : i = a
      · subst hia
        exact ⟨gm, Or.inl rfl, Or.inr ⟨hgml, he₀a.symm⟩⟩
      by_cases hib : i = b
      · subst hib
        exact ⟨gm, Or.inl rfl, Or.inl hgm.symm⟩
      -- an inner edge
      have hi0 : i ≠ 0 := by
        rcases hab with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact hia
        · exact hib
      have hil : i ≠ Fin.last (m + 1) := by
        rcases hab with ⟨-, rfl⟩ | ⟨rfl, -⟩
        · exact hib
        · exact hia
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi0
      have hj' : j ≠ Fin.last m := fun h => hil (by rw [h]; rfl)
      obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.2 hj'
      exact ⟨g l, Or.inr ⟨l, rfl⟩, Or.inl (by rw [(hg l).1, Fin.succ_castSucc])⟩
  rcases he₀ with h | h
  · exact key 0 (Fin.last (m + 1)) (Or.inl ⟨rfl, rfl⟩) h
  · exact key (Fin.last (m + 1)) 0 (Or.inr ⟨rfl, rfl⟩) h

/-- **Every cycle of `M` is the cycle of `M` of a cycle of `N⁻`.** -/
theorem exists_liftEdges_eq (hr : lsa hM Set.univ Set.univ_nonempty = M.root)
    (hbin : IsBinaryRootedNetwork M) {C : Set E} (hC : IsCycle M.graph C) :
    ∃ D, IsCycle (semidirected hM hB hX).graph D ∧ liftEdges hM hB hX D = C := by
  have := hM.finite_arcs
  set G := semidirected hM hB hX
  obtain ⟨k, v, e, hC', rfl⟩ := hC
  have hk := hC'.two_le (source_ne_target_of_binary hbin)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  by_cases hroot : M.root ∈ Set.range v
  · obtain ⟨j, hj⟩ := hroot
    have hR := hC'.rotate j
    have hrange : Set.range (fun i => e (i + j)) = Set.range e :=
      (Equiv.addRight j).surjective.range_comp e
    rw [← hrange]
    exact exists_liftEdges_eq_of_root hM hB hX hr hbin hR (by simp only [zero_add]; exact hj)
  · have hvr : ∀ i, v i ≠ M.root := fun i h => hroot ⟨i, h⟩
    choose w hw using fun i => exists_sdVert_of_ne hM hX hr (hvr i)
    have hsrc : ∀ i, M.graph.source (e i) ≠ M.root := by
      intro i h
      rcases hC'.joins i with ⟨h₁, -⟩ | ⟨h₁, -⟩
      · exact hvr _ (h₁.symm.trans h)
      · exact hvr _ (h₁.symm.trans h)
    choose g hg using fun i => exists_sdArc_of_ne hM hB hX hr (hsrc i)
    refine ⟨Set.range g, ⟨m + 2, w, g, ⟨hC'.pos, fun i => ?_, fun i j h => ?_, fun i j h => ?_⟩,
      rfl⟩, ?_⟩
    · rcases hC'.joins i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · refine Or.inl ⟨sdVert_injective hM hX ?_, sdVert_injective hM hX ?_⟩
        · rw [(hg i).2.1, h₁, hw]
        · rw [(hg i).2.2, h₂, hw]
      · refine Or.inr ⟨sdVert_injective hM hX ?_, sdVert_injective hM hX ?_⟩
        · rw [(hg i).2.1, h₁, hw]
        · rw [(hg i).2.2, h₂, hw]
    · have := congrArg (sdVert hM hX) h
      rw [hw, hw] at this
      exact hC'.injective_node this
    · have := congrArg (sdArc hM hB hX) h
      rw [(hg i).1, (hg j).1] at this
      exact hC'.injective_edge this
    · ext f
      constructor
      · rintro ⟨c, ⟨i, rfl⟩, rfl | ⟨hm, -⟩⟩
        · exact ⟨i, (hg i).1.symm⟩
        · exact absurd (by rw [(hg i).1] at hm; exact hm.trans hr) (hsrc i)
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, Or.inl (hg i).1.symm⟩

/-- **The hybrid node of a cycle of `N⁻` is the hybrid node of the cycle of `M`.** -/
theorem isHybridNodeOf_semidirected_iff (hbin : IsBinaryRootedNetwork M)
    (h1 : IsLevelOne M.graph) {D : Set (SemidirectedArc hM hB hX)}
    (hD : IsCycle (semidirected hM hB hX).graph D) (v : SemidirectedVertex hM hX) :
    IsHybridNodeOf (semidirected hM hB hX) D v ↔
      v ∈ cycleNodes (semidirected hM hB hX).graph D ∧ M.graph.indegree (sdVert hM hX v) = 2 := by
  have := hM.finite_arcs
  set G := semidirected hM hB hX
  constructor
  · rintro ⟨h₁, hh₁, h₂, hh₂, hne, -, -, ht₁, ht₂⟩
    refine ⟨⟨h₁, hh₁, Or.inr ht₁⟩, le_antisymm (hbin.indegree_le_two _) ?_⟩
    unfold DirectedMultigraph.indegree
    rw [← Set.ncard_pair (fun h => hne (sdArc_injective hM hB hX h))]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro f (rfl | hf)
    · change M.graph.target (sdArc hM hB hX h₁) = _
      rw [← sdVert_target, ht₁]
    · rw [Set.mem_singleton_iff.1 hf]
      change M.graph.target (sdArc hM hB hX h₂) = _
      rw [← sdVert_target, ht₂]
  · rintro ⟨hv, h2⟩
    have hvC := (sdVert_mem_cycleNodes_liftEdges_iff hM hB hX D v).2 hv
    have hC := isCycle_liftEdges hM hB hX hD
    obtain ⟨f₁, f₂, hne, hs⟩ := Set.ncard_eq_two.1 h2
    have hf₁ : M.graph.target f₁ = sdVert hM hX v := (Set.ext_iff.1 hs f₁).2 (Or.inl rfl)
    have hf₂ : M.graph.target f₂ = sdVert hM hX v := (Set.ext_iff.1 hs f₂).2 (Or.inr rfl)
    have hlift : ∀ f, M.graph.target f = sdVert hM hX v →
        ∃ g ∈ D, sdArc hM hB hX g = f ∧ G.graph.target g = v ∧ G.IsDirected g := by
      intro f hf
      obtain ⟨g, hg, h | ⟨-, h⟩⟩ := (lemma3 hbin h1 hC).2.1 _ hvC h2 f hf
      · refine ⟨g, hg, h.symm, sdVert_injective hM hX (by rw [sdVert_target, ← h, hf]), ?_⟩
        rw [semidirected_isDirected_iff, ← h]
        unfold IsHybridArc
        rw [hf, h2]
      · have h1' := (sdRootArc_spec hM hB hX).2
        unfold IsTreeArc at h1'
        rw [← h, hf, h2] at h1'
        exact absurd h1' (by norm_num)
    obtain ⟨g₁, hg₁, rfl, ht₁, hd₁⟩ := hlift f₁ hf₁
    obtain ⟨g₂, hg₂, rfl, ht₂, hd₂⟩ := hlift f₂ hf₂
    exact ⟨g₁, hg₁, g₂, hg₂, fun h => hne (h ▸ rfl), hd₁, hd₂, ht₁, ht₂⟩

/-- The LSA of all the taxa of an LSA network is its root. -/
theorem lsa_univ_eq_root (hlsa : M.IsLSANetwork) :
    lsa hM Set.univ Set.univ_nonempty = M.root :=
  eq_of_reaches_of_reaches hM.acyclic (hlsa.2 _ (lsa_spec hM _ _).1) ((lsa_spec hM _ _).2 _ hlsa.1)

/-- **The cycle of `M` of a cycle of `N⁻` has as many nodes other than the root as the cycle of `N⁻`
has edges.** -/
theorem card_cycleNodesOffRoot_liftEdges [Fintype V] [Fintype E]
    (hr : lsa hM Set.univ Set.univ_nonempty = M.root) {D : Set (SemidirectedArc hM hB hX)}
    (hD : IsCycle (semidirected hM hB hX).graph D) :
    Finset.card (cycleNodesOffRoot M (liftEdges hM hB hX D)) = D.ncard := by
  rw [card_cycleNodesOffRoot (isCycle_liftEdges hM hB hX hD), ncard_liftEdges, ← hr,
    lsa_mem_cycleNodes_liftEdges_iff hM hB hX hr]
  split_ifs <;> omega

end SemidirectedCycles

end Banos2019
