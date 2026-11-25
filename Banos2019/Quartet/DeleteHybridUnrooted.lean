module

public import Banos2019.Quartet.ReduceUnrootedKeep
public import Banos2019.Quartet.DeleteArcReduce

/-!
# `Q⁻` without a hybrid edge

For a binary network `Q` whose root is the LSA of its taxa and a hybrid edge `h` of `Q⁻`,
`deleteHybridEdge Q⁻ h` is `unrootAt` of `deleteArc Q h` at the arc of `Q` that `Q⁻` merges
(`nonempty_sdMetricIso_deleteHybridEdge_unrootAt`): the nodes are those of `Q` other than the root,
the edges the arcs other than `h` and the merged arc, and the other arc into the target of `h` is a
tree arc of `deleteArc Q h`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section Delete

variable {Q : RootedNetwork V E X} (hQ : IsBinaryRootedNetwork Q) (hX : Nontrivial X)

/-- **`Q⁻` without a hybrid edge `h` is `unrootAt` of `deleteArc Q h`** at the arc of `Q` that `Q⁻`
merges. -/
theorem nonempty_sdMetricIso_deleteHybridEdge_unrootAt
    (hr : lsa hQ.1 Set.univ Set.univ_nonempty = Q.root) (θ : MetricData E)
    {h : SemidirectedArc hQ.1 hQ.2 hX} (hh : (semidirected hQ.1 hQ.2 hX).IsDirected h)
    (hP : (deleteArc Q (sdArc hQ.1 hQ.2 hX h)).IsPhylogenetic) :
    Nonempty (SDMetricIso (deleteHybridEdge (semidirected hQ.1 hQ.2 hX) h)
      (restrictMetric (semidirectedMetric hQ.1 hQ.2 hX θ) _)
      (unrootAt (deleteArc Q (sdArc hQ.1 hQ.2 hX h)) hP
        ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩)
      (unrootAtMetric (deleteArc Q (sdArc hQ.1 hQ.2 hX h))
        ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩
        (deleteArcMetric Q (sdArc hQ.1 hQ.2 hX h) θ))) := by
  have := hQ.1.finite_arcs
  have hhyb : Q.IsHybridArc (sdArc hQ.1 hQ.2 hX h) := (semidirected_isDirected_iff _ _ _ h).1 hh
  -- the nodes
  have hvne : ∀ u : SemidirectedVertex hQ.1 hX,
      sdVert hQ.1 hX u ≠ (deleteArc Q (sdArc hQ.1 hQ.2 hX h)).root := fun u => by
    have := sdVert_ne_lsa hQ.1 hX u
    rwa [hr] at this
  let vert : SemidirectedVertex hQ.1 hX ≃
      {v : V // v ≠ (deleteArc Q (sdArc hQ.1 hQ.2 hX h)).root} :=
    Equiv.ofBijective (fun u => ⟨sdVert hQ.1 hX u, hvne u⟩)
      ⟨fun u u' huu => sdVert_injective hQ.1 hX
        (congrArg (fun z : {v : V // v ≠ (deleteArc Q (sdArc hQ.1 hQ.2 hX h)).root} =>
          z.1) huu), fun v => by
        obtain ⟨u, hu⟩ := exists_sdVert_of_ne hQ.1 hX hr v.2
        exact ⟨u, Subtype.ext hu⟩⟩
  -- the edges
  let edgeFun : {g : SemidirectedArc hQ.1 hQ.2 hX // g ≠ h} →
      {e : {e // e ≠ sdArc hQ.1 hQ.2 hX h} //
        e ≠ ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩} :=
    fun g => ⟨⟨sdArc hQ.1 hQ.2 hX g.1, fun h' => g.2 (sdArc_injective _ _ _ h')⟩,
      fun h' => sdArc_ne_sdRootArc hQ.1 hQ.2 hX g.1
        (congrArg (fun z : {e // e ≠ sdArc hQ.1 hQ.2 hX h} => z.1) h')⟩
  have hebij : Function.Bijective edgeFun := by
    refine ⟨fun g g' hg => Subtype.ext (sdArc_injective _ _ _
      (congrArg (fun e => e.1.1) hg)), fun e => ?_⟩
    obtain ⟨g, hg⟩ := (mem_range_sdArc hQ.1 hQ.2 hX e.1.1).2
      ⟨by rw [hr]; exact hQ.1.root_reaches _, fun h' => e.2 (Subtype.ext h')⟩
    exact ⟨⟨g, fun h' => e.1.2 (by rw [← hg, h'])⟩, Subtype.ext (Subtype.ext hg)⟩
  let edge := Equiv.ofBijective edgeFun hebij
  -- the ends
  have hsrc : ∀ g, (unrootAt (deleteArc Q (sdArc hQ.1 hQ.2 hX h)) hP
      ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩).graph.source (edge g) =
      vert ((deleteHybridEdge (semidirected hQ.1 hQ.2 hX) h).graph.source g) := by
    intro g
    apply Subtype.ext
    change (unrootAt (deleteArc Q (sdArc hQ.1 hQ.2 hX h)) hP
      ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩).graph.source
        (edgeFun g) = sdVert hQ.1 hX ((semidirected hQ.1 hQ.2 hX).graph.source g.1)
    rw [sdVert_source, hr]
    simp only [unrootAt, deleteArc, edgeFun]
    by_cases hs : Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) = Q.root
    · simp only [hs, ↓reduceDIte, ↓reduceIte]
    · simp only [hs, ↓reduceDIte, ↓reduceIte]
  have htgt : ∀ g, (unrootAt (deleteArc Q (sdArc hQ.1 hQ.2 hX h)) hP
      ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩).graph.target (edge g) =
      vert ((deleteHybridEdge (semidirected hQ.1 hQ.2 hX) h).graph.target g) := fun g =>
    Subtype.ext (sdVert_target hQ.1 hQ.2 hX g.1).symm
  -- the hybrid edges
  have hti : ∀ g : SemidirectedArc hQ.1 hQ.2 hX,
      (semidirected hQ.1 hQ.2 hX).graph.target g ≠ (semidirected hQ.1 hQ.2 hX).graph.target h ↔
        Q.graph.target (sdArc hQ.1 hQ.2 hX g) ≠ Q.graph.target (sdArc hQ.1 hQ.2 hX h) := by
    intro g
    rw [← sdVert_target, ← sdVert_target]
    exact (sdVert_injective hQ.1 hX).ne_iff.symm
  have hdir : ∀ g, (unrootAt (deleteArc Q (sdArc hQ.1 hQ.2 hX h)) hP
      ⟨sdRootArc hQ.1 hQ.2 hX, (sdArc_ne_sdRootArc hQ.1 hQ.2 hX h).symm⟩).IsDirected (edge g) ↔
      (deleteHybridEdge (semidirected hQ.1 hQ.2 hX) h).IsDirected g := by
    intro g
    change 2 ≤ (deleteArc Q (sdArc hQ.1 hQ.2 hX h)).graph.indegree
        (Q.graph.target (sdArc hQ.1 hQ.2 hX g.1)) ↔
      (semidirected hQ.1 hQ.2 hX).IsDirected g.1 ∧
        (semidirected hQ.1 hQ.2 hX).graph.target g.1 ≠ (semidirected hQ.1 hQ.2 hX).graph.target h
    rw [semidirected_isDirected_iff, hti]
    have hin := deleteArc_indegree (Q := Q) (h := sdArc hQ.1 hQ.2 hX h)
      (Q.graph.target (sdArc hQ.1 hQ.2 hX g.1))
    have h2 := hQ.indegree_le_two (Q.graph.target (sdArc hQ.1 hQ.2 hX h))
    unfold IsHybridArc at hhyb ⊢
    by_cases ht : Q.graph.target (sdArc hQ.1 hQ.2 hX g.1) = Q.graph.target (sdArc hQ.1 hQ.2 hX h)
    · rw [ite_eq_left ht.symm] at hin
      rw [ht] at hin ⊢
      exact ⟨fun h' => by omega, fun h' => absurd rfl h'.2⟩
    · rw [ite_eq_right (Ne.symm ht)] at hin
      constructor
      · intro h'
        exact ⟨by omega, ht⟩
      · intro h'
        omega
  refine ⟨⟨⟨vert, edge, hdir, fun g => Or.inl ⟨hsrc g, htgt g⟩, fun g _ => ⟨hsrc g, htgt g⟩,
    fun x => Subtype.ext (sdVert_leaf hQ.1 hQ.2 hX x).symm⟩, fun g => ?_, fun g hg => ?_⟩⟩
  · change (if Q.graph.source (sdArc hQ.1 hQ.2 hX g.1) = Q.root then
        θ.length (sdArc hQ.1 hQ.2 hX g.1) + θ.length (sdRootArc hQ.1 hQ.2 hX)
      else θ.length (sdArc hQ.1 hQ.2 hX g.1)) = (semidirectedMetric hQ.1 hQ.2 hX θ).length g.1
    rw [semidirectedMetric_length, hr]
  · have hne : Q.graph.target (sdArc hQ.1 hQ.2 hX g.1) ≠ Q.graph.target (sdArc hQ.1 hQ.2 hX h) :=
      (hti g.1).1 hg.2
    change (if Q.graph.target (sdArc hQ.1 hQ.2 hX g.1) = Q.graph.target (sdArc hQ.1 hQ.2 hX h)
      then 1 else θ.inheritance (sdArc hQ.1 hQ.2 hX g.1)) = θ.inheritance (sdArc hQ.1 hQ.2 hX g.1)
    rw [ite_eq_right hne]

end Delete

end Banos2019
