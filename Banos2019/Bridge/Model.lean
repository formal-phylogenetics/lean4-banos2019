module

public import Banos2019.Defs
public import Banos2019.Coalescent
public import Phylogenetics.NMSC.Inheritance

/-!
# The definitions of the Challenge and those of the library

The Challenge states its theorems on the definitions of `Banos2019.Defs` (namespace
`Banos2019.Model`), which use Mathlib only. This module translates them into the library's.

* `Model.Digraph.toDM`, `Model.Network.toRooted`, `Model.Params.toMetric`, `Model.SDNetwork.toSD`,
  `Model.ofSD`, `Model.ofRooted`: the same data as a `DirectedMultigraph`, a `RootedNetwork`, a
  `MetricData`, a `SemidirectedNetwork`, and back.
* `Model.Digraph.isCycle_iff`, `isLevelOne_iff`: cycles and level-1 graphs.
* `Model.Network.isBinaryNetwork_iff`: Definition 1, through `isBinaryRootedNetwork_iff`;
  connectedness follows from the other clauses.
* `Model.Network.isMetric_iff`: Definition 2 on a binary network, through `isMetricNetwork_iff`.
* `Model.Network.isLSA_iff`, `Model.Network.lsa_eq`: the lowest stable ancestor.
* `Model.quartetTreeEquiv`, `Model.Network.cf_eq`: concordance factors, the allocation
  `∏ r, γ (a r)` being `allocationWeight 0` (`allocationWeight_rho_zero`).
* `Model.bigCycleOn_iff`, `Model.sameOrdering_iff`, `Model.Network.forGenericParams_of`: the Big
  Cycle property, orderings and genericity; the Challenge's null sets are contained in the
  library's.
* `Model.SDIso.toLib`, `Model.SDIso.ofLib`, `Model.SDMetricIso.toLib`, `Model.SDMetricIso.ofLib`:
  isomorphisms.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

namespace Banos2019.Model

variable {V E X : Type*}

/-! ### The conversions -/

/-- The library's directed multigraph with the same edges. -/
def Digraph.toDM (G : Digraph V E) : DirectedMultigraph V E := ⟨G.source, G.target⟩

/-- The library's rooted network with the same data. -/
def Network.toRooted (N : Network V E X) : RootedNetwork V E X := ⟨N.graph.toDM, N.root, N.leaf⟩

/-- A rooted network of the library as a network of the Challenge. -/
def ofRooted (M : RootedNetwork V E X) : Network V E X :=
  ⟨⟨M.graph.source, M.graph.target⟩, M.root, M.leaf⟩

/-- The library's parameters with the same values. -/
def Params.toMetric (θ : Params E) : MetricData E := ⟨θ.length, θ.inheritance⟩

/-- Parameters of the library as parameters of the Challenge. -/
def ofMetric (θ : MetricData E) : Params E := ⟨θ.length, θ.inheritance⟩

/-- The library's semidirected network with the same data. -/
def SDNetwork.toSD (G : SDNetwork V E X) : SemidirectedNetwork V E X :=
  ⟨G.graph.toDM, G.IsDirected, G.leaf⟩

/-- A semidirected network of the library as a network of the Challenge. -/
def ofSD (G : SemidirectedNetwork V E X) : SDNetwork V E X :=
  ⟨⟨G.graph.source, G.graph.target⟩, G.IsDirected, G.leaf⟩

@[simp] theorem toRooted_ofRooted (M : RootedNetwork V E X) : (ofRooted M).toRooted = M := rfl

@[simp] theorem toMetric_ofMetric (θ : MetricData E) : (ofMetric θ).toMetric = θ := rfl

@[simp] theorem toSD_ofSD (G : SemidirectedNetwork V E X) : (ofSD G).toSD = G := rfl

/-! ### Graphs -/

namespace Digraph

variable (G : Digraph V E)

theorem adj_toDM {u v : V} : G.toDM.Adj u v ↔ G.Adj u v := Iff.rfl

theorem reaches_toDM {u v : V} : G.toDM.Reaches u v ↔ G.Reaches u v := Iff.rfl

theorem isAcyclic_toDM : G.toDM.IsAcyclic ↔ G.IsAcyclic := Iff.rfl

theorem indegree_toDM (v : V) : G.toDM.indegree v = G.indegree v := rfl

theorem outdegree_toDM (v : V) : G.toDM.outdegree v = G.outdegree v := rfl

theorem joins_toDM (e : E) (u w : V) : Banos2019.Joins G.toDM e u w ↔ G.Joins e u w := Iff.rfl

theorem nodes_eq (C : Set E) : G.nodes C = cycleNodes G.toDM C := rfl

/-- **Cycles** (Definition 11) are the library's. -/
theorem isCycle_iff (C : Set E) : G.IsCycle C ↔ Banos2019.IsCycle G.toDM C := by
  constructor
  · rintro ⟨k, v, e, hk, hj, hv, he, rfl⟩
    exact ⟨k, v, e, ⟨hk, hj, hv, he⟩, rfl⟩
  · rintro ⟨k, v, e, ⟨hk, hj, hv, he⟩, rfl⟩
    exact ⟨k, v, e, hk, hj, hv, he, rfl⟩

/-- **Level-1** (Definition 12) is the library's. -/
theorem isLevelOne_iff : G.IsLevelOne ↔ Banos2019.IsLevelOne G.toDM := by
  simp only [IsLevelOne, Banos2019.IsLevelOne, isCycle_iff]

end Digraph

/-! ### Definitions 1 and 2 -/

namespace Network

variable (N : Network V E X)

theorem graph_toRooted : N.toRooted.graph = N.graph.toDM := rfl

/-- **Definition 1** is the library's binary rooted phylogenetic network. Definition 1 also asks for
a connected graph, which the clauses give: going up from any node ends at the root. -/
theorem isBinaryNetwork_iff : N.IsBinaryNetwork ↔ IsBinaryRootedNetwork N.toRooted := by
  rw [isBinaryRootedNetwork_iff]
  constructor
  · rintro ⟨hV, hE, hX, hA, hr0, hr2, hleaf, hinj, hother⟩
    refine ⟨hV, hE, hX, ?_, hA, hr0, hr2, hleaf, hinj, hother⟩
    -- the root reaches every node: go up along entering arcs, which ends at the root
    let r : V → V → Prop := fun a b => Relation.TransGen N.toRooted.graph.Adj a b
    have : IsTrans V r := ⟨fun _ _ _ h h' => h.trans h'⟩
    have : Std.Irrefl r := ⟨fun a h => hA a h⟩
    have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
    have hnonroot : ∀ v, v ≠ N.root → 1 ≤ N.toRooted.graph.indegree v := fun v hv => by
      by_cases hl : v ∈ Set.range N.leaf
      · obtain ⟨x, rfl⟩ := hl
        exact (hleaf x).1.ge
      · rcases hother v hv hl with h | h
        · exact h.1.ge
        · change 1 ≤ N.graph.indegree v
          omega
    have hreach : ∀ v, N.toRooted.graph.Reaches N.root v := fun v => by
      induction v using hwf.induction with
      | _ v ih =>
        by_cases hv : v = N.root
        · rw [hv]
          exact .refl
        · obtain ⟨e, he⟩ := (N.toRooted.graph.one_le_indegree_iff v).mp (hnonroot v hv)
          exact (ih (N.toRooted.graph.source e) (.single ⟨e, rfl, he⟩)).tail ⟨e, rfl, he⟩
    intro u v
    exact (N.toRooted.graph.walks_symm (N.toRooted.graph.walks_of_reaches (hreach u))).trans
      (N.toRooted.graph.walks_of_reaches (hreach v))
  · rintro ⟨hV, hE, hX, -, hA, hr0, hr2, hleaf, hinj, hother⟩
    exact ⟨hV, hE, hX, hA, hr0, hr2, hleaf, hinj, hother⟩

theorem isHybridEdge_iff (hN : N.IsBinaryNetwork) (e : E) :
    N.IsHybridEdge e ↔ N.toRooted.IsHybridArc e := by
  have hb := (N.isBinaryNetwork_iff).mp hN
  have := hb.indegree_le_two (N.graph.target e)
  show N.graph.indegree (N.graph.target e) = 2 ↔ 2 ≤ N.graph.indegree (N.graph.target e)
  change N.graph.indegree (N.graph.target e) ≤ 2 at this
  omega

theorem not_isHybridEdge_iff (hN : N.IsBinaryNetwork) (e : E) :
    ¬ N.IsHybridEdge e ↔ N.toRooted.IsTreeArc e := by
  have hb := (N.isBinaryNetwork_iff).mp hN
  have := hb.1.finite_arcs
  have h2 := hb.indegree_le_two (N.graph.target e)
  have h1 := (N.toRooted.graph.one_le_indegree_iff (N.graph.target e)).mpr ⟨e, rfl⟩
  show ¬ N.graph.indegree (N.graph.target e) = 2 ↔ N.graph.indegree (N.graph.target e) = 1
  change N.graph.indegree (N.graph.target e) ≤ 2 at h2
  change 1 ≤ N.graph.indegree (N.graph.target e) at h1
  omega

/-- **Definition 2** is the library's metric, on a binary network. -/
theorem isMetric_iff [Fintype E] (hN : N.IsBinaryNetwork) (θ : Params E) :
    N.IsMetric θ ↔ IsMetricNetwork N.toRooted θ.toMetric := by
  rw [isMetricNetwork_iff ((N.isBinaryNetwork_iff).mp hN)]
  simp only [IsMetric, ← N.isHybridEdge_iff hN, ← N.not_isHybridEdge_iff hN]
  rfl

/-! ### The lowest stable ancestor -/

/-- **Definition 4** is the library's least stable ancestor. -/
theorem isLSA_iff (Z : Set X) (v : V) : N.IsLSA Z v ↔
    N.toRooted.IsLeastStableAncestor Z v := Iff.rfl

theorem lsa_eq (hN : N.IsBinaryNetwork) [Nonempty X] :
    N.lsa = RootedNetwork.lsa ((N.isBinaryNetwork_iff).mp hN).1 Set.univ Set.univ_nonempty := by
  have hP := ((N.isBinaryNetwork_iff).mp hN).1
  have hspec := lsa_spec hP Set.univ Set.univ_nonempty
  have : N.IsLSA Set.univ N.lsa := Classical.epsilon_spec (p := N.IsLSA Set.univ) ⟨_, hspec⟩
  exact RootedNetwork.IsLeastStableAncestor.unique (N := N.toRooted) hP this hspec

theorem isLSA_lsa (hN : N.IsBinaryNetwork) [Nonempty X] : N.IsLSA Set.univ N.lsa := by
  rw [N.lsa_eq hN]
  exact RootedNetwork.lsa_spec (N := N.toRooted) _ _ _

end Network

/-! ### Quartet trees and the coalescent -/

section Coalescent

variable {L : Type*} [Fintype L] [DecidableEq L]

theorem roots_eq (F : Finset (Finset L)) : roots F = Phylogenetics.roots F := rfl

theorem kingmanGenerator_eq :
    (kingmanGenerator : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) =
      Phylogenetics.kingmanGenerator := rfl

theorem kingmanTransition_eq (t : ℝ) :
    (kingmanTransition t : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) =
      Phylogenetics.kingmanTransition t := rfl

theorem kingmanAbsorption_eq :
    (kingmanAbsorption : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) =
      Phylogenetics.kingmanAbsorption := rfl

omit [Fintype L] in
theorem forestBelow_eq (F A : Finset (Finset L)) : forestBelow F A =
    Phylogenetics.forestBelow F A :=
  rfl

theorem unroot_eq (G : Finset (Finset L)) : unroot G = Phylogenetics.unroot G := rfl

end Coalescent

section Quartets

variable [DecidableEq X]

/-- The quartet trees of the Challenge are the library's. -/
def quartetTreeEquiv : QuartetTree X ≃ Phylogenetics.QuartetTree X where
  toFun s := ⟨s.1, s.2⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem quartetTreeEquiv_val (s : QuartetTree X) : (quartetTreeEquiv s).1 = s.1 := rfl

@[simp] theorem taxa_quartetTreeEquiv (s : QuartetTree X) :
    (quartetTreeEquiv s).taxa = s.taxa := rfl

theorem displays_iff (T : Finset (Finset X)) (s : QuartetTree X) :
    Displays T s ↔ Phylogenetics.Displays T (quartetTreeEquiv s) := Iff.rfl

variable [Fintype X]

theorem mem_treesOn_iff {q : Finset X} {s : QuartetTree X} : s ∈ treesOn q ↔ s.taxa = q := by
  simp [treesOn]

theorem mem_treesOn_iff' {q : Finset X} {s : Phylogenetics.QuartetTree X} :
    s ∈ Phylogenetics.treesOn q ↔ s.taxa = q := by
  simp [Phylogenetics.treesOn]

/-- **Definition 17** is the library's Big Cycle property. -/
theorem bigCycleOn_iff (p : Phylogenetics.QuartetTree X → ℝ) (q : Finset X) :
    BigCycleOn (p ∘ quartetTreeEquiv) q ↔ Banos2019.BigCycleOn p q := by
  constructor
  · intro h a ha b hb hab
    have ha' : quartetTreeEquiv.symm a ∈ treesOn q := mem_treesOn_iff.mpr (by
      rw [← taxa_quartetTreeEquiv, Equiv.apply_symm_apply]
      exact (mem_treesOn_iff'.mp ha))
    have hb' : quartetTreeEquiv.symm b ∈ treesOn q := mem_treesOn_iff.mpr (by
      rw [← taxa_quartetTreeEquiv, Equiv.apply_symm_apply]
      exact (mem_treesOn_iff'.mp hb))
    have := h _ ha' _ hb' fun h' => hab (quartetTreeEquiv.symm.injective h')
    simpa using this
  · intro h a ha b hb hab
    refine h (quartetTreeEquiv a) (mem_treesOn_iff'.mpr ?_) (quartetTreeEquiv b)
      (mem_treesOn_iff'.mpr ?_) fun h' => hab (quartetTreeEquiv.injective h')
    · rw [taxa_quartetTreeEquiv]
      exact mem_treesOn_iff.mp ha
    · rw [taxa_quartetTreeEquiv]
      exact mem_treesOn_iff.mp hb

omit [Fintype X] in
/-- **Definition 15** is the library's. -/
theorem sameOrdering_iff (p p' : Phylogenetics.QuartetTree X → ℝ) :
    SameOrdering (p ∘ quartetTreeEquiv) (p' ∘ quartetTreeEquiv) ↔ Banos2019.SameOrdering p p' := by
  constructor
  · intro h a b hab
    have := h (quartetTreeEquiv.symm a) (quartetTreeEquiv.symm b) (by
      rw [← taxa_quartetTreeEquiv, ← taxa_quartetTreeEquiv, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
      exact hab)
    simpa using this
  · intro h a b hab
    exact h (quartetTreeEquiv a) (quartetTreeEquiv b) hab

end Quartets

namespace Network

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : Network V E X) (θ : Params E)

omit [Fintype V] in
theorem arrivingForest_eq (top : E → Finset (Finset X)) (v : V) :
    N.arrivingForest top v = Phylogenetics.arrivingForest N.toRooted top v := rfl

omit [Fintype V] in
/-- The Challenge's allocation `∏ r, γ (a r)` is the library's `allocationWeight 0`. -/
theorem allocationFactor_eq (F : Finset (Finset X)) (v : V) (bot : E → Finset (Finset X)) :
    N.allocationFactor θ F v bot =
      Phylogenetics.allocationFactor N.toRooted θ.toMetric 0 F v bot := by
  unfold allocationFactor Phylogenetics.allocationFactor
  refine Finset.sum_congr rfl fun a _ => ?_
  exact ite_congr rfl (fun _ => (allocationWeight_rho_zero (γ := fun e :
    {e // N.toRooted.graph.target e = v} => θ.toMetric.inheritance e.val) a).symm) fun _ => rfl

theorem historyWeight_eq (bot top : E → Finset (Finset X)) :
    N.historyWeight θ bot top = Phylogenetics.historyWeight N.toRooted θ.toMetric 0 bot top := by
  unfold historyWeight Phylogenetics.historyWeight
  simp only [allocationFactor_eq, arrivingForest_eq]
  rfl

theorem geneTreeDist_eq (G : Finset (Finset X)) :
    N.geneTreeDist θ G = Phylogenetics.geneTreeDist N.toRooted θ.toMetric 0 G := by
  unfold geneTreeDist Phylogenetics.geneTreeDist
  simp only [historyWeight_eq, arrivingForest_eq]
  rfl

/-- **Definition 14**: the concordance factors of the Challenge are the library's, `nmscCF … 0`. -/
theorem cf_eq : N.cf θ = Banos2019.cf N.toRooted θ.toMetric ∘ quartetTreeEquiv := by
  funext s
  unfold cf
  simp only [Function.comp_apply, Banos2019.cf, nmscCF, geneTreeDist_eq]
  rfl

end Network

/-! ### Genericity -/

namespace Network

variable [Fintype E] (N : Network V E X)

/-- **Genericity transfers**: a property that holds for generic parameters in the library's sense
holds for generic parameters in the Challenge's. The Challenge's exceptional set,
`{θ | N.IsMetric θ ∧ ¬ P θ}` in the same coordinates, is contained in the library's. -/
theorem forGenericParams_of (hN : N.IsBinaryNetwork) {P : Params E → Prop} {Q : MetricData E → Prop}
    (hPQ : ∀ θ, N.IsMetric θ → Q θ.toMetric → P θ) (h : Banos2019.ForGenericParams N.toRooted Q) :
    N.ForGenericParams P := by
  intro d hd
  have hb := N.isBinaryNetwork_iff.mp hN
  refine measure_mono_null ?_ (h d fun v hv => hd v ?_)
  · rintro x ⟨θ, ⟨hθ, hP⟩, -, hlen, hinh⟩
    exact ⟨θ.toMetric, fun hQ => hP (hPQ θ hθ hQ), ((N.isMetric_iff hN θ).mp hθ).1, hlen,
      fun e he hne => hinh e ((N.isHybridEdge_iff hN e).mpr he) hne⟩
  · have := hb.indegree_le_two v
    change N.graph.indegree v ≤ 2 at this
    change 2 ≤ N.graph.indegree v at hv
    omega

end Network

/-! ### Isomorphisms -/

section Iso

variable {V' E' : Type*} {G : SDNetwork V E X} {G' : SDNetwork V' E' X}

/-- An isomorphism of the Challenge as one of the library. -/
def SDIso.toLib (ι : SDIso G G') : Banos2019.SDIso G.toSD G'.toSD :=
  ⟨ι.vert, ι.edge, ι.isDirected_iff, ι.joins, ι.directed, ι.leaf⟩

/-- An isomorphism of the library as one of the Challenge. -/
def SDIso.ofLib (ι : Banos2019.SDIso G.toSD G'.toSD) : SDIso G G' :=
  ⟨ι.vert, ι.edge, ι.isDirected_iff, ι.joins, ι.directed, ι.leaf⟩

/-- A metric isomorphism of the Challenge as one of the library. -/
def SDMetricIso.toLib {θ : Params E} {θ' : Params E'} (ι : SDMetricIso G θ G' θ') :
    Banos2019.SDMetricIso G.toSD θ.toMetric G'.toSD θ'.toMetric :=
  ⟨ι.toSDIso.toLib, ι.length, ι.inheritance⟩

/-- A metric isomorphism of the library as one of the Challenge. -/
def SDMetricIso.ofLib {θ : Params E} {θ' : Params E'}
    (ι : Banos2019.SDMetricIso G.toSD θ.toMetric G'.toSD θ'.toMetric) : SDMetricIso G θ G' θ' :=
  ⟨SDIso.ofLib ι.toSDIso, ι.length, ι.inheritance⟩

end Iso

end Banos2019.Model
