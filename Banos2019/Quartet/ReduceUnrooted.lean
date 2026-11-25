module

public import Banos2019.Quartet.DeleteArcReduce
public import Banos2019.Quartet.SemidirectedCycles
public import Banos2019.Network.SuppressIso

/-!
# The unrooted network of a reduced network

`unrootAt M hP e₀` is `M` with its root suppressed, the arc `e₀` at the root merged into the other
one, its tree arcs undirected (`unrootAtMetric`: the merged edge has the lengths of the two arcs).
When the root of `M` has outdegree two, the nodes of degree two of `unrootAt M hP e₀` are the chain
nodes of `M` (`isBranch_unrootAt_iff`), and the chain of `M` from a node is a trail of it
(`isUTrail_unrootAt_chainFrom`).

For `M` satisfying `IsReducible`, whose root has outdegree two, and `N = reduceNet M` an LSA
network, the unrooted network `N⁻` is `unrootAt M hP e₀` with its nodes of degree two suppressed
(`nonempty_sdMetricIso_suppress_unrootAt`), for `e₀ = reduceRootArc`, the first arc of the chain of
the arc that `N⁻` merges. The nodes of `N⁻` are the nodes of `M` other than the root and the chain
nodes (`reduceVert`); an edge of `N⁻` is the chain of `M` of its arc (`reduceArc`, `reduceChainOf`),
with the chain of `e₀` for the merged edge, a chain of `unrootAt M hP e₀` between the nodes of its ends
(`exists_isUTrail_reduceChainOf`); it is hybrid when the last arc of the chain is
(`eq_lastArc_of_mem_reduceChainOf`), and has the total length of the chain
(`length_eq_finsum_reduceChainOf`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

section UnrootAt

variable {M : RootedNetwork V E X} (hP : M.IsPhylogenetic) (e₀ : E)

/-- The parameters of `unrootAt M hP e₀`: the merged edge has the lengths of the two arcs at the
root. -/
def unrootAtMetric (M : RootedNetwork V E X) (e₀ : E) (θ : MetricData E) :
    MetricData {e // e ≠ e₀} :=
  ⟨fun e => if M.graph.source e.1 = M.root then θ.length e.1 + θ.length e₀ else θ.length e.1,
    fun e => θ.inheritance e.1⟩

variable {e₀} (he₀ : M.graph.source e₀ = M.root)
include he₀

omit he₀ in
theorem unrootAt_source_of_ne {g : {e // e ≠ e₀}} (hg : M.graph.source g.1 ≠ M.root) :
    ((unrootAt M hP e₀).graph.source g).1 = M.graph.source g.1 := by
  simp [unrootAt, hg]

omit he₀ in
theorem unrootAt_target (g : {e // e ≠ e₀}) :
    ((unrootAt M hP e₀).graph.target g).1 = M.graph.target g.1 := rfl

omit he₀ in
include hP in
/-- An arc out of a chain node is not `e₀`. -/
theorem ne_of_isChainVertex_source {g : E} (hg : M.IsChainVertex (M.graph.source g))
    (h : M.graph.source e₀ = M.root) : g ≠ e₀ := fun h' => by
  rw [h', h] at hg
  exact not_isChainVertex_root hP hg

/-- **The chain of `M` from a node `a` to a node `b` it reaches is a trail of `unrootAt M hP e₀`**,
through the chain nodes between them, along the arcs out of the chain nodes from `a` before `b`. -/
theorem isUTrail_unrootAt_chainFrom {a : V} (ha : a ≠ M.root) {b : V} (h : M.ChainReach a b)
    (hb : b ≠ M.root) :
    ∃ S : Set {v // v ≠ M.root}, IsUTrail (unrootAt M hP e₀).graph ⟨a, ha⟩ ⟨b, hb⟩ S
      {g | M.IsChainVertex (M.graph.source g.1) ∧ M.ChainReach a (M.graph.source g.1) ∧
        ¬ M.ChainReach b (M.graph.source g.1)} ∧
      ∀ s ∈ S, M.ChainReach a s.1 ∧ M.ChainReach s.1 b := by
  induction h with
  | refl =>
    refine ⟨{⟨a, ha⟩}, ?_, ?_⟩
    · have : {g : {e // e ≠ e₀} | M.IsChainVertex (M.graph.source g.1) ∧
          M.ChainReach a (M.graph.source g.1) ∧ ¬ M.ChainReach a (M.graph.source g.1)} = ∅ :=
        Set.eq_empty_of_forall_notMem fun g hg => hg.2.2 hg.2.1
      rw [this]
      exact .nil _
    · rintro s rfl
      exact ⟨.refl, .refl⟩
  | @tail y c hay hyc ih =>
    obtain ⟨hy, f, hfs, hft⟩ := hyc
    have hyr : y ≠ M.root := fun h => not_isChainVertex_root hP (h ▸ hy)
    obtain ⟨S, hS, hSmem⟩ := ih hyr
    have hfe : f ≠ e₀ := ne_of_isChainVertex_source hP (hfs ▸ hy) he₀
    have hj : Joins (unrootAt M hP e₀).graph ⟨f, hfe⟩ ⟨y, hyr⟩ ⟨c, hb⟩ :=
      Or.inl ⟨Subtype.ext ((unrootAt_source_of_ne hP (by rw [hfs]; exact hyr)).trans hfs),
        Subtype.ext hft⟩
    have hcyc : ∀ x, M.ChainReach c x → x ≠ y := fun x hx hxy =>
      hP.acyclic y (Relation.TransGen.head' ⟨f, hfs, hft⟩ (hxy ▸ hx.reaches))
    have hyc : (⟨y, hyr⟩ : {v // v ≠ M.root}) ≠ ⟨c, hb⟩ := fun h =>
      hcyc c .refl (congrArg Subtype.val h).symm
    have hcS : (⟨c, hb⟩ : {v // v ≠ M.root}) ∉ S := fun hcS => by
      obtain ⟨-, hcy⟩ := hSmem _ hcS
      exact hcyc y hcy rfl
    -- the chain nodes after `y` are those after `c`, and `y`
    have hafter : ∀ x, M.ChainReach y x ↔ x = y ∨ M.ChainReach c x := fun x => by
      constructor
      · intro hx
        rcases Relation.ReflTransGen.cases_head hx with h | ⟨z, hz, hzx⟩
        · exact Or.inl h.symm
        · have : z = c := hy.adj_unique hz.2 ⟨f, hfs, hft⟩
          exact Or.inr (this ▸ hzx)
      · rintro (rfl | hx)
        · exact .refl
        · exact Relation.ReflTransGen.head ⟨hy, f, hfs, hft⟩ hx
    refine ⟨S ∪ {⟨y, hyr⟩, ⟨c, hb⟩}, ?_, ?_⟩
    · have := hS.append (IsUTrail.single hj hyc) (by
        rintro x ⟨hxS, hx⟩
        rcases hx with rfl | hx
        · exact rfl
        · rw [Set.mem_singleton_iff.1 hx] at hxS
          exact absurd hxS hcS)
      convert this using 1
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hg, hag, hcg⟩
        by_cases hgy : M.graph.source g.1 = y
        · right
          obtain ⟨e, he⟩ := (M.graph.outdegree_eq_one_iff _).mp hy.2
          exact Subtype.ext (((he g.1).mp hgy).trans ((he f).mp hfs).symm)
        · left
          refine ⟨hg, hag, fun h' => hcg ?_⟩
          exact ((hafter _).1 h').resolve_left hgy
      · rintro (⟨hg, hag, hyg⟩ | rfl)
        · refine ⟨hg, hag, fun h' => hyg ((hafter _).2 (Or.inr h'))⟩
        · refine ⟨hfs ▸ hy, hfs ▸ hay, fun h' => hcyc _ h' hfs⟩
    · rintro s (hs | hs)
      · obtain ⟨h₁, h₂⟩ := hSmem s hs
        exact ⟨h₁, h₂.tail ⟨hy, f, hfs, hft⟩⟩
      · rcases hs with rfl | hs
        · exact ⟨hay, Relation.ReflTransGen.single ⟨hy, f, hfs, hft⟩⟩
        · rw [Set.mem_singleton_iff.1 hs]
          exact ⟨hay.tail ⟨hy, f, hfs, hft⟩, .refl⟩

omit he₀ in
theorem indegree_unrootAt_add [Finite E] (u : {v // v ≠ M.root}) :
    (unrootAt M hP e₀).graph.indegree u + (if M.graph.target e₀ = u.1 then 1 else 0) =
      M.graph.indegree u.1 := by
  have := ncard_subtype_ne_add e₀ (fun e => M.graph.target e = u.1)
  unfold DirectedMultigraph.indegree
  convert this using 3
  ext g
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem outdegree_unrootAt [Finite E] (h2 : M.graph.outdegree M.root = 2) (u : {v // v ≠ M.root}) :
    (unrootAt M hP e₀).graph.outdegree u =
      M.graph.outdegree u.1 + (if M.graph.target e₀ = u.1 then 1 else 0) := by
  set p : E → Prop := fun e => (M.graph.source e = M.root ∧ M.graph.target e₀ = u.1) ∨
    M.graph.source e = u.1
  have hset : {g : {e // e ≠ e₀} | (unrootAt M hP e₀).graph.source g = u} = {g | p g.1} := by
    ext g
    simp only [Set.mem_ofPred_eq, p, unrootAt]
    split_ifs with hg
    · constructor
      · intro h
        exact Or.inl ⟨hg, congrArg Subtype.val h⟩
      · rintro (⟨-, h⟩ | h)
        · exact Subtype.ext h
        · exact absurd (h.symm.trans hg) u.2
    · constructor
      · intro h
        exact Or.inr (congrArg Subtype.val h)
      · rintro (⟨h, -⟩ | h)
        · exact absurd h hg
        · exact Subtype.ext h
  have h1 := ncard_subtype_ne_add e₀ p
  have hpe₀ : p e₀ ↔ M.graph.target e₀ = u.1 := by
    simp only [p, he₀, true_and]
    exact ⟨fun h => h.resolve_right fun h' => u.2 h'.symm, Or.inl⟩
  have hall : {e | p e}.ncard = M.graph.outdegree u.1 +
      (if M.graph.target e₀ = u.1 then 2 else 0) := by
    split_ifs with ht
    · have : {e | p e} = {e | M.graph.source e = u.1} ∪ {e | M.graph.source e = M.root} := by
        ext e
        simp only [p, ht, and_true, Set.mem_ofPred_eq, Set.mem_union]
        tauto
      rw [this, Set.ncard_union_eq (Set.disjoint_left.2 fun e h h' =>
          u.2 ((show M.graph.source e = u.1 from h).symm.trans h'))
        (Set.toFinite _) (Set.toFinite _)]
      rw [← h2]
      rfl
    · have : {e | p e} = {e | M.graph.source e = u.1} := by
        ext e
        simp only [p, ht, and_false, false_or, Set.mem_ofPred_eq]
      rw [this, add_zero]
      rfl
  show {g | (unrootAt M hP e₀).graph.source g = u}.ncard = _
  rw [hset]
  rw [hall] at h1
  by_cases ht : M.graph.target e₀ = u.1
  · rw [ite_eq_left (hpe₀.2 ht), ite_eq_left ht] at h1
    rw [ite_eq_left ht]
    omega
  · rw [ite_eq_right (fun h => ht (hpe₀.1 h)), ite_eq_right ht] at h1
    rw [ite_eq_right ht]
    omega

/-- **The nodes that the suppression of `unrootAt M hP e₀` keeps are those that are not chain nodes
of `M`**, when the root has outdegree two and the other nodes have degree three, but the chain nodes
and the leaves. -/
theorem isBranch_unrootAt_iff [Finite E] (h2 : M.graph.outdegree M.root = 2)
    (hdeg : ∀ v, v ≠ M.root → M.graph.outdegree v ≠ 0 → ¬ M.IsChainVertex v →
      M.graph.indegree v + M.graph.outdegree v = 3) (u : {v // v ≠ M.root}) :
    IsBranch (unrootAt M hP e₀) ∅ u ↔ ¬ M.IsChainVertex u.1 := by
  have hdg : degree (unrootAt M hP e₀).graph u = M.graph.indegree u.1 + M.graph.outdegree u.1 := by
    unfold degree
    have h₁ := indegree_unrootAt_add hP (e₀ := e₀) u
    rw [outdegree_unrootAt hP he₀ h2 u]
    split_ifs at h₁ ⊢ <;> omega
  have hleaf : (∃ x, (unrootAt M hP e₀).leaf x = u) ↔ ∃ x, M.leaf x = u.1 :=
    ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩, fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
  unfold IsBranch
  rw [hdg, hleaf]
  simp only [Set.mem_empty_iff_false, or_false]
  constructor
  · rintro (h | ⟨x, hx⟩) hc
    · exact h (by rw [hc.1, hc.2])
    · exact not_isChainVertex_leaf hP x (hx ▸ hc)
  · intro hc
    by_cases h0 : M.graph.outdegree u.1 = 0
    · exact Or.inr ((hP.leaves u.1).1 h0)
    · left
      rw [hdeg u.1 u.2 h0 hc]
      omega

end UnrootAt

section Reduce

variable [Fintype V] [Fintype E] {M : RootedNetwork V E X} {θ : MetricData E}
  (hM : IsReducible M θ) (hb : IsBinaryRootedNetwork (reduceNet M hM.phylo)) (hX : Nontrivial X)

/-- The node of `M` of a node of the unrooted network of `reduceNet M`. -/
def reduceVert (w : SemidirectedVertex hb.1 hX) : V :=
  (finContractVertex (M.suppress hM.phylo) (sdVert hb.1 hX w)).1

/-- The first arc of `M` of the chain of an edge of the unrooted network of `reduceNet M`. -/
def reduceArc (g : SemidirectedArc hb.1 hb.2 hX) : E :=
  (finContractArc (M.suppress hM.phylo) (sdArc hb.1 hb.2 hX g)).1

/-- The first arc of `M` of the chain of the arc of `reduceNet M` that its unrooted network merges. -/
def reduceRootArc : E :=
  (finContractArc (M.suppress hM.phylo) (sdRootArc hb.1 hb.2 hX)).1

variable (h2 : M.graph.outdegree M.root = 2) (hl : (reduceNet M hM.phylo).IsLSANetwork)

include h2 in
theorem finContractVertex_root_reduceNet :
    finContractVertex (M.suppress hM.phylo) (reduceNet M hM.phylo).root =
      (M.suppress hM.phylo).root :=
  hM.isContraction.root_ne (by
    rw [suppress_outdegree]
    intro h
    change M.graph.outdegree M.root = 1 at h
    rw [h2] at h
    omega)

include h2 hl in
/-- The nodes of the unrooted network of `reduceNet M` are the nodes of `M` other than the root and
the chain nodes. -/
theorem reduceVert_spec (w : SemidirectedVertex hb.1 hX) :
    reduceVert hM hb hX w ≠ M.root ∧ ¬ M.IsChainVertex (reduceVert hM hb hX w) := by
  refine ⟨fun h => ?_, (finContractVertex (M.suppress hM.phylo) (sdVert hb.1 hX w)).2⟩
  have hr := lsa_univ_eq_root hb.1 hX hl
  apply sdVert_ne_lsa hb.1 hX w
  rw [hr]
  apply hM.isContraction.inj_v
  rw [finContractVertex_root_reduceNet hM h2]
  exact Subtype.ext h

theorem reduceVert_injective : Function.Injective (reduceVert hM hb hX) := fun _ _ h =>
  sdVert_injective hb.1 hX (hM.isContraction.inj_v (Subtype.ext h))

include h2 hl in
theorem exists_reduceVert_eq {v : V} (hv : v ≠ M.root) (hc : ¬ M.IsChainVertex v) :
    ∃ w, reduceVert hM hb hX w = v := by
  have hr := lsa_univ_eq_root hb.1 hX hl
  obtain ⟨c, hc'⟩ := (hM.isContraction.range_v ⟨v, hc⟩).2 fun h => hv (congrArg Subtype.val h.1)
  have hcr : c ≠ (reduceNet M hM.phylo).root := fun h => by
    rw [h, finContractVertex_root_reduceNet hM h2] at hc'
    exact hv (congrArg Subtype.val hc').symm
  obtain ⟨w, hw⟩ := (mem_range_sdVert hb.1 hX c).2 ⟨hr ▸ hb.1.root_reaches c, hr ▸ hcr⟩
  exact ⟨w, by rw [reduceVert, hw, hc']⟩

theorem reduceArc_injective : Function.Injective (reduceArc hM hb hX) := fun _ _ h =>
  sdArc_injective hb.1 hb.2 hX (hM.isContraction.inj_e (Subtype.ext h))

theorem not_isChainVertex_source_reduceArc (g : SemidirectedArc hb.1 hb.2 hX) :
    ¬ M.IsChainVertex (M.graph.source (reduceArc hM hb hX g)) :=
  (finContractArc (M.suppress hM.phylo) (sdArc hb.1 hb.2 hX g)).2

theorem not_isChainVertex_source_reduceRootArc :
    ¬ M.IsChainVertex (M.graph.source (reduceRootArc hM hb hX)) :=
  (finContractArc (M.suppress hM.phylo) (sdRootArc hb.1 hb.2 hX)).2

theorem reduceArc_ne_reduceRootArc (g : SemidirectedArc hb.1 hb.2 hX) :
    reduceArc hM hb hX g ≠ reduceRootArc hM hb hX := fun h =>
  sdArc_ne_sdRootArc hb.1 hb.2 hX g (hM.isContraction.inj_e (Subtype.ext h))

include h2 hl in
theorem exists_reduceArc_eq {e : E} (he : ¬ M.IsChainVertex (M.graph.source e))
    (he₀ : e ≠ reduceRootArc hM hb hX) : ∃ g, reduceArc hM hb hX g = e := by
  have hr := lsa_univ_eq_root hb.1 hX hl
  have h1 : (M.suppress hM.phylo).graph.outdegree (M.suppress hM.phylo).root ≠ 1 := by
    rw [suppress_outdegree]
    exact fun h => by change M.graph.outdegree M.root = 1 at h; rw [h2] at h; omega
  obtain ⟨a, ha⟩ := (hM.isContraction.range_e ⟨e, he⟩).2 fun h => h1 h.2
  have ha₀ : a ≠ sdRootArc hb.1 hb.2 hX := fun h => he₀ (by
    rw [reduceRootArc, ← h, ha])
  obtain ⟨g, hg⟩ := (mem_range_sdArc hb.1 hb.2 hX a).2 ⟨hr ▸ hb.1.root_reaches _, ha₀⟩
  exact ⟨g, by rw [reduceArc, hg, ha]⟩

include h2 hl in
/-- The arc `reduceRootArc` leaves the root. -/
theorem source_reduceRootArc : M.graph.source (reduceRootArc hM hb hX) = M.root := by
  have hr := lsa_univ_eq_root hb.1 hX hl
  have h := hM.isContraction.source (sdRootArc hb.1 hb.2 hX)
  rw [(sdRootArc_spec hb.1 hb.2 hX).1, hr, finContractVertex_root_reduceNet hM h2] at h
  exact (congrArg Subtype.val h).symm

include h2 hl in
/-- **The ends of an edge of the unrooted network of `reduceNet M`**: it leaves the first node of
the chain of its arc, or, for the merged edge, the last node of the chain of `reduceRootArc`, and
enters the last node of the chain of its arc. -/
theorem reduceVert_source (g : SemidirectedArc hb.1 hb.2 hX) :
    reduceVert hM hb hX ((unrooted _ hb hX).graph.source g) =
      if M.graph.source (reduceArc hM hb hX g) = M.root then
        chainEnd hM.phylo (M.graph.target (reduceRootArc hM hb hX))
      else M.graph.source (reduceArc hM hb hX g) := by
  have hr := lsa_univ_eq_root hb.1 hX hl
  have hK := hM.isContraction
  have hsrc := hK.source (sdArc hb.1 hb.2 hX g)
  have hroot : M.graph.source (reduceArc hM hb hX g) = M.root ↔
      (reduceNet M hM.phylo).graph.source (sdArc hb.1 hb.2 hX g) =
        lsa hb.1 Set.univ Set.univ_nonempty := by
    rw [hr]
    constructor
    · intro h
      apply hK.inj_v
      rw [hsrc, finContractVertex_root_reduceNet hM h2]
      exact Subtype.ext h
    · intro h
      rw [h, finContractVertex_root_reduceNet hM h2] at hsrc
      exact (congrArg Subtype.val hsrc).symm
  unfold reduceVert
  rw [sdVert_source]
  by_cases h : M.graph.source (reduceArc hM hb hX g) = M.root
  · rw [ite_eq_left h, ite_eq_left (hroot.1 h), hK.target]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hroot.2 h')), hsrc]
    rfl

theorem reduceVert_target (g : SemidirectedArc hb.1 hb.2 hX) :
    reduceVert hM hb hX ((unrooted _ hb hX).graph.target g) =
      chainEnd hM.phylo (M.graph.target (reduceArc hM hb hX g)) := by
  unfold reduceVert
  rw [sdVert_target, hM.isContraction.target]
  rfl

theorem reduceVert_leaf (x : X) :
    reduceVert hM hb hX ((unrooted _ hb hX).leaf x) = M.leaf x := by
  unfold reduceVert
  rw [sdVert_leaf, hM.isContraction.leaf]
  rfl

omit [Fintype V] in
/-- The chain of `M` from a node other than the root, to its end, as a trail of `unrootAt M hP e₀`. -/
theorem exists_isUTrail_unrootAt_chainEnd {e₀ : E} (he₀ : M.graph.source e₀ = M.root) {t : V}
    (ht : t ≠ M.root) :
    ∃ (hE : chainEnd hM.phylo t ≠ M.root) (S : Set {v // v ≠ M.root}),
      IsUTrail (unrootAt M hM.phylo e₀).graph ⟨t, ht⟩ ⟨chainEnd hM.phylo t, hE⟩ S
        {f | M.IsChainVertex (M.graph.source f.1) ∧ M.ChainReach t (M.graph.source f.1)} ∧
      ∀ s ∈ S, M.ChainReach t s.1 ∧ (s.1 ≠ chainEnd hM.phylo t → M.IsChainVertex s.1) := by
  have hP := hM.phylo
  have hc := chainReach_chainEnd hP t
  have hE : chainEnd hP t ≠ M.root := fun h => ht
    (eq_of_reaches_of_reaches hP.acyclic (h ▸ hc.reaches) (hP.root_reaches t))
  obtain ⟨S, hS, hSmem⟩ := isUTrail_unrootAt_chainFrom hP he₀ ht hc hE
  refine ⟨hE, S, ?_, fun s hs => ⟨(hSmem s hs).1, fun hne => ?_⟩⟩
  · convert hS using 1
    ext f
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun h => ⟨h.1, h.2, fun h' => ?_⟩, fun h => ⟨h.1, h.2.1⟩⟩
    rcases Relation.ReflTransGen.cases_head h' with h'' | ⟨z, hz, -⟩
    · exact not_isChainVertex_chainEnd hP t (h'' ▸ h.1)
    · exact not_isChainVertex_chainEnd hP t hz.1
  · rcases Relation.ReflTransGen.cases_head (hSmem s hs).2 with h'' | ⟨z, hz, -⟩
    · exact absurd h'' hne
    · exact hz.1

/-- The arcs of `unrootAt M hP e₀`, for `e₀ = reduceRootArc`, of the chain of an edge of the unrooted
network of `reduceNet M`: those of the chain of its arc, and of the chain of `e₀` for the merged
edge. -/
def reduceChainOf (g : SemidirectedArc hb.1 hb.2 hX) : Set {e // e ≠ reduceRootArc hM hb hX} :=
  {f | M.IsOnChain (reduceArc hM hb hX g) f.1 ∨
    (M.graph.source (reduceArc hM hb hX g) = M.root ∧ M.IsOnChain (reduceRootArc hM hb hX) f.1)}

include h2 hl in
/-- **The chain of an edge of the unrooted network of `reduceNet M` is a trail of `unrootAt M hP e₀`**
between the nodes of the ends of the edge, through chain nodes. -/
theorem exists_isUTrail_reduceChainOf (g : SemidirectedArc hb.1 hb.2 hX) :
    ∃ (u w : {v // v ≠ M.root}) (S : Set {v // v ≠ M.root}),
      IsUTrail (unrootAt M hM.phylo (reduceRootArc hM hb hX)).graph u w S
        (reduceChainOf hM hb hX g) ∧
      u.1 = reduceVert hM hb hX ((unrooted _ hb hX).graph.source g) ∧
      w.1 = reduceVert hM hb hX ((unrooted _ hb hX).graph.target g) ∧
      ∀ s ∈ S, s ≠ u → s ≠ w → M.IsChainVertex s.1 := by
  have hP := hM.phylo
  set e₀ := reduceRootArc hM hb hX
  set ε := reduceArc hM hb hX g
  have he₀ : M.graph.source e₀ = M.root := source_reduceRootArc hM hb hX h2 hl
  have hεe₀ : ε ≠ e₀ := reduceArc_ne_reduceRootArc hM hb hX g
  set G := (unrootAt M hP e₀).graph
  have hloop : ∀ f : E, M.graph.source f ≠ M.graph.target f := fun f h =>
    hP.acyclic _ (.single ⟨f, rfl, h.symm⟩)
  have hcyc : ∀ {a b : V} (f : E), M.graph.source f = a → M.graph.target f = b →
      M.graph.Reaches b a → False := fun f hfa hfb h =>
    hP.acyclic _ (Relation.TransGen.head' ⟨f, hfa, hfb⟩ h)
  have ht₁ : M.graph.target ε ≠ M.root := hP.target_ne_root ε
  obtain ⟨hE₁, S₁, hS₁, hS₁mem⟩ := exists_isUTrail_unrootAt_chainEnd hM he₀ ht₁
  by_cases hroot : M.graph.source ε = M.root
  · -- the merged edge: the chain of `e₀` backwards, `ε`, the chain of `ε`
    have ht₀ : M.graph.target e₀ ≠ M.root := hP.target_ne_root e₀
    obtain ⟨hE₀, S₀, hS₀, hS₀mem⟩ := exists_isUTrail_unrootAt_chainEnd hM he₀ ht₀
    have hsrc := reduceVert_source hM hb hX h2 hl g
    rw [ite_eq_left hroot] at hsrc
    have htgt := reduceVert_target hM hb hX g
    have hEE : chainEnd hP (M.graph.target e₀) ≠ chainEnd hP (M.graph.target ε) := by
      rw [← hsrc, ← htgt]
      intro h
      have := reduceVert_injective hM hb hX h
      exact (semidirected_graph_isAcyclic hb.1 hb.2 hX) _ (.single ⟨g, this, rfl⟩)
    have hdis : ∀ x, M.ChainReach (M.graph.target e₀) x → ¬ M.ChainReach (M.graph.target ε) x :=
      fun x h₀ h₁ => hEE ((chainEnd_eq_of_chainReach_left hP h₀).trans
        (chainEnd_eq_of_chainReach_left hP h₁).symm)
    have hj : Joins G ⟨ε, hεe₀⟩ ⟨M.graph.target e₀, ht₀⟩ ⟨M.graph.target ε, ht₁⟩ :=
      Or.inl ⟨Subtype.ext (by simp [G, unrootAt, hroot]), rfl⟩
    have ht₀S₁ : (⟨M.graph.target e₀, ht₀⟩ : {v // v ≠ M.root}) ∉ S₁ := fun h =>
      hdis _ .refl (hS₁mem _ h).1
    have hB := IsUTrail.cons hj ht₀S₁ hS₁
    have hAB := hS₀.reverse.append hB (by
      rintro x ⟨hx₀, hx | hx⟩
      · exact hx
      · exact absurd (hS₁mem x hx).1 (hdis _ (hS₀mem x hx₀).1))
    refine ⟨⟨chainEnd hP (M.graph.target e₀), hE₀⟩, ⟨chainEnd hP (M.graph.target ε), hE₁⟩,
      S₀ ∪ insert ⟨M.graph.target e₀, ht₀⟩ S₁, ?_, hsrc.symm, htgt.symm, ?_⟩
    · have hset : reduceChainOf hM hb hX g =
          {f | M.IsChainVertex (M.graph.source f.1) ∧
            M.ChainReach (M.graph.target e₀) (M.graph.source f.1)} ∪
          insert ⟨ε, hεe₀⟩ {f | M.IsChainVertex (M.graph.source f.1) ∧
            M.ChainReach (M.graph.target ε) (M.graph.source f.1)} := by
        ext f
        have h₀ : f.1 ≠ e₀ := f.2
        rw [Set.mem_union, Set.mem_insert_iff, Subtype.ext_iff]
        show (M.IsOnChain ε f.1 ∨ (M.graph.source ε = M.root ∧ M.IsOnChain e₀ f.1)) ↔ _
        unfold RootedNetwork.IsOnChain
        constructor
        · rintro ((h | h) | ⟨-, h | h⟩)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact absurd h h₀
          · exact Or.inl h
        · rintro (h | h | h)
          · exact Or.inr ⟨hroot, Or.inr h⟩
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
      rw [hset]
      exact hAB
    · rintro x hx hx₀ hx₁
      rcases hx with hx | hx | hx
      · exact (hS₀mem x hx).2 fun h => hx₀ (Subtype.ext h)
      · rw [hx]
        exact (hS₀mem _ hS₀.start_mem).2 fun h => hx₀ (by rw [hx]; exact Subtype.ext h)
      · exact (hS₁mem x hx).2 fun h => hx₁ (Subtype.ext h)
  · -- the other edges: `ε` then its chain
    have hj : Joins G ⟨ε, hεe₀⟩ ⟨M.graph.source ε, hroot⟩ ⟨M.graph.target ε, ht₁⟩ :=
      Or.inl ⟨Subtype.ext (unrootAt_source_of_ne hP hroot), rfl⟩
    have hsS₁ : (⟨M.graph.source ε, hroot⟩ : {v // v ≠ M.root}) ∉ S₁ := fun h =>
      hcyc ε rfl rfl (hS₁mem _ h).1.reaches
    have hB := IsUTrail.cons hj hsS₁ hS₁
    have hsrc := reduceVert_source hM hb hX h2 hl g
    rw [ite_eq_right hroot] at hsrc
    refine ⟨⟨M.graph.source ε, hroot⟩, ⟨chainEnd hP (M.graph.target ε), hE₁⟩,
      insert ⟨M.graph.source ε, hroot⟩ S₁, ?_, hsrc.symm, (reduceVert_target hM hb hX g).symm, ?_⟩
    · have hset : reduceChainOf hM hb hX g =
          insert ⟨ε, hεe₀⟩ {f | M.IsChainVertex (M.graph.source f.1) ∧
            M.ChainReach (M.graph.target ε) (M.graph.source f.1)} := by
        ext f
        rw [Set.mem_insert_iff, Subtype.ext_iff]
        show (M.IsOnChain ε f.1 ∨ (M.graph.source ε = M.root ∧ M.IsOnChain e₀ f.1)) ↔ _
        unfold RootedNetwork.IsOnChain
        constructor
        · rintro ((h | h) | ⟨h, -⟩)
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hroot
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
      rw [hset]
      exact hB
    · rintro x hx hxs hxw
      rcases hx with hx | hx
      · exact absurd hx hxs
      · exact (hS₁mem x hx).2 fun h => hxw (Subtype.ext h)

include h2 hl in
/-- The source in `M` of the arc of an edge of the unrooted network of `reduceNet M` is the root
exactly when its source in `reduceNet M` is the root. -/
theorem source_reduceArc_eq_root_iff (g : SemidirectedArc hb.1 hb.2 hX) :
    M.graph.source (reduceArc hM hb hX g) = M.root ↔
      (reduceNet M hM.phylo).graph.source (sdArc hb.1 hb.2 hX g) =
        lsa hb.1 Set.univ Set.univ_nonempty := by
  have hr := lsa_univ_eq_root hb.1 hX hl
  have hK := hM.isContraction
  have hsrc := hK.source (sdArc hb.1 hb.2 hX g)
  rw [hr]
  constructor
  · intro h
    apply hK.inj_v
    rw [hsrc, finContractVertex_root_reduceNet hM h2]
    exact Subtype.ext h
  · intro h
    rw [h, finContractVertex_root_reduceNet hM h2] at hsrc
    exact (congrArg Subtype.val hsrc).symm

include h2 hl in
/-- **Every arc of `M` other than `e₀` is on the chain of one edge** of the unrooted network of
`reduceNet M`. -/
theorem exists_mem_reduceChainOf (f : {e // e ≠ reduceRootArc hM hb hX}) :
    ∃ g, f ∈ reduceChainOf hM hb hX g := by
  have hP := hM.phylo
  have hr := lsa_univ_eq_root hb.1 hX hl
  set h := chainHead hP f.1
  by_cases hh : h.1 = reduceRootArc hM hb hX
  · -- the merged edge
    have := hb.1.finite_arcs
    obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 hb.2.1
    have hx : (reduceNet M hP).graph.source x = (reduceNet M hP).root :=
      (Set.ext_iff.1 hs x).2 (Or.inl rfl)
    have hy : (reduceNet M hP).graph.source y = (reduceNet M hP).root :=
      (Set.ext_iff.1 hs y).2 (Or.inr rfl)
    obtain ⟨a, ha, ha₀⟩ : ∃ a, (reduceNet M hP).graph.source a = (reduceNet M hP).root ∧
        a ≠ sdRootArc hb.1 hb.2 hX := by
      by_cases hx₀ : x = sdRootArc hb.1 hb.2 hX
      · exact ⟨y, hy, fun h' => hxy (hx₀.trans h'.symm)⟩
      · exact ⟨x, hx, hx₀⟩
    obtain ⟨g, rfl⟩ := (mem_range_sdArc hb.1 hb.2 hX a).2 ⟨hr ▸ hb.1.root_reaches _, ha₀⟩
    refine ⟨g, Or.inr ⟨(source_reduceArc_eq_root_iff hM hb hX h2 hl g).2 (ha.trans hr.symm), ?_⟩⟩
    have hc := isOnChain_chainHead hP f.1
    rw [hh] at hc
    exact hc
  · obtain ⟨g, hg⟩ := exists_reduceArc_eq hM hb hX h2 hl h.2 hh
    refine ⟨g, Or.inl ?_⟩
    rw [hg]
    exact isOnChain_chainHead hP f.1

include h2 hl in
/-- **An arc of `M` is on the chain of at most one edge.** -/
theorem eq_of_mem_reduceChainOf {f : {e // e ≠ reduceRootArc hM hb hX}}
    {g g' : SemidirectedArc hb.1 hb.2 hX} (hg : f ∈ reduceChainOf hM hb hX g)
    (hg' : f ∈ reduceChainOf hM hb hX g') : g = g' := by
  have hc := not_isChainVertex_source_reduceArc hM hb hX
  have hc₀ := not_isChainVertex_source_reduceRootArc hM hb hX
  have hne := reduceArc_ne_reduceRootArc hM hb hX
  rcases hg with hg | ⟨hgr, hg⟩ <;> rcases hg' with hg' | ⟨hgr', hg'⟩
  · exact reduceArc_injective hM hb hX (IsOnChain.unique hg hg' (hc g) (hc g'))
  · exact absurd (IsOnChain.unique hg hg' (hc g) hc₀) (hne g)
  · exact absurd (IsOnChain.unique hg' hg (hc g') hc₀) (hne g')
  · exact eq_of_source_sdArc_eq_lsa hb.1 hb.2 hX
      ((source_reduceArc_eq_root_iff hM hb hX h2 hl g).1 hgr)
      ((source_reduceArc_eq_root_iff hM hb hX h2 hl g').1 hgr')

/-- The chain of `reduceRootArc` has no hybrid arc: it is the arc that the unrooted network of
`reduceNet M` merges, a tree arc. -/
theorem not_isHybridArc_of_isOnChain_reduceRootArc {f : E}
    (hf : M.IsOnChain (reduceRootArc hM hb hX) f) : ¬ M.IsHybridArc f := by
  have hP := hM.phylo
  have htwo := hM.two
  intro hh
  have hlast := NMSC.eq_lastArc hP hf (fun hc => by
    unfold IsHybridArc at hh
    rw [hc.1] at hh
    omega)
  have ht := (sdRootArc_spec hb.1 hb.2 hX).2
  rw [hlast] at hh
  have := (isHybridArc_reduceNet_iff hP htwo (sdRootArc hb.1 hb.2 hX)).2 hh
  unfold IsTreeArc at ht
  unfold IsHybridArc at this
  omega

/-- **A hybrid arc on the chain of an edge is the last arc of the chain of the arc of the edge.** -/
theorem eq_lastArc_of_mem_reduceChainOf {g : SemidirectedArc hb.1 hb.2 hX}
    {f : {e // e ≠ reduceRootArc hM hb hX}} (hf : f ∈ reduceChainOf hM hb hX g)
    (hh : M.IsHybridArc f.1) : f.1 = NMSC.lastArc hM.phylo (reduceArc hM hb hX g) := by
  rcases hf with hf | ⟨-, hf⟩
  · exact NMSC.eq_lastArc hM.phylo hf (fun hc => by
      unfold IsHybridArc at hh
      rw [hc.1] at hh
      omega)
  · exact absurd hh (not_isHybridArc_of_isOnChain_reduceRootArc hM hb hX hf)

omit [Fintype V] in
/-- A sum over the arcs other than `e₀` satisfying `p`, which `e₀` does not. -/
theorem finsum_mem_subtype_ne {e₀ : E} {p : E → Prop} (hp : ¬ p e₀) (F : E → ℝ) :
    ∑ᶠ f ∈ {f : {e // e ≠ e₀} | p f.1}, F f.1 = ∑ e ∈ univ.filter p, F e := by
  have himg : Subtype.val '' {f : {e // e ≠ e₀} | p f.1} = ↑(univ.filter p) := by
    ext e
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro he
      exact ⟨⟨e, fun h => hp (h ▸ he)⟩, he, rfl⟩
  rw [← finsum_mem_image (g := Subtype.val) Subtype.val_injective.injOn, himg,
    finsum_mem_coe_finset]

include h2 hl in
/-- The last arc of the chain of the arc of an edge is not `e₀`. -/
theorem lastArc_reduceArc_ne (g : SemidirectedArc hb.1 hb.2 hX) :
    NMSC.lastArc hM.phylo (reduceArc hM hb hX g) ≠ reduceRootArc hM hb hX := fun h => by
  have hc := NMSC.isOnChain_lastArc hM.phylo (reduceArc hM hb hX g)
  rw [h] at hc
  rcases hc with hc | ⟨hc, -⟩
  · exact reduceArc_ne_reduceRootArc hM hb hX g hc.symm
  · rw [source_reduceRootArc hM hb hX h2 hl] at hc
    exact not_isChainVertex_root hM.phylo hc

include h2 hl in
/-- **The length of an edge of the unrooted network of `reduceNet M` is the total length of its
chain.** -/
theorem length_eq_finsum_reduceChainOf (g : SemidirectedArc hb.1 hb.2 hX) :
    (unrootedMetric (reduceNet M hM.phylo) hb hX (reduceMetric M hM.phylo θ)).length g =
      ∑ᶠ f ∈ reduceChainOf hM hb hX g,
        (unrootAtMetric M (reduceRootArc hM hb hX) θ).length f := by
  have hP := hM.phylo
  have hr := lsa_univ_eq_root hb.1 hX hl
  set e₀ := reduceRootArc hM hb hX
  set ε := reduceArc hM hb hX g
  have he₀ : M.graph.source e₀ = M.root := source_reduceRootArc hM hb hX h2 hl
  have hεe₀ : ε ≠ e₀ := reduceArc_ne_reduceRootArc hM hb hX g
  have hc₀ : ¬ M.IsChainVertex (M.graph.source e₀) :=
    not_isChainVertex_source_reduceRootArc hM hb hX
  have hnot₀ : ¬ M.IsOnChain ε e₀ := fun h => by
    rcases h with h | ⟨h, -⟩
    · exact hεe₀ h.symm
    · exact hc₀ h
  have hLε : (reduceMetric M hP θ).length (sdArc hb.1 hb.2 hX g) =
      ∑ f ∈ univ.filter (M.IsOnChain ε), θ.length f := rfl
  have hL₀ : (reduceMetric M hP θ).length (sdRootArc hb.1 hb.2 hX) =
      ∑ f ∈ univ.filter (M.IsOnChain e₀), θ.length f := rfl
  -- the arcs of a chain other than its first arc leave chain nodes, not the root
  have hsrc : ∀ {a f : E}, M.IsOnChain a f → f ≠ a → M.graph.source f ≠ M.root := by
    intro a f h hfa hr'
    rcases h with h | ⟨h, -⟩
    · exact hfa h
    · rw [hr'] at h
      exact not_isChainVertex_root hP h
  rw [semidirectedMetric_length]
  by_cases hroot : M.graph.source ε = M.root
  · have hroot' := (source_reduceArc_eq_root_iff hM hb hX h2 hl g).1 hroot
    rw [ite_eq_left hroot', hLε, hL₀]
    -- the merged edge
    set p : E → Prop := fun e => M.IsOnChain ε e ∨ (M.IsOnChain e₀ e ∧ e ≠ e₀)
    have hset : reduceChainOf hM hb hX g = {f : {e // e ≠ e₀} | p f.1} := by
      ext f
      have h₀ : f.1 ≠ e₀ := f.2
      show (M.IsOnChain ε f.1 ∨ (M.graph.source ε = M.root ∧ M.IsOnChain e₀ f.1)) ↔ p f.1
      simp only [p, hroot, true_and, ne_eq, h₀, not_false_eq_true, and_true]
    have hF : ∀ f ∈ {f : {e // e ≠ e₀} | p f.1},
        (unrootAtMetric M e₀ θ).length f =
          θ.length f.1 + (if f.1 = ε then θ.length e₀ else 0) := by
      intro f hf
      show (if M.graph.source f.1 = M.root then θ.length f.1 + θ.length e₀ else θ.length f.1) = _
      by_cases hfε : f.1 = ε
      · rw [ite_eq_left (hfε ▸ hroot), ite_eq_left hfε]
      · rw [ite_eq_right hfε, add_zero, ite_eq_right]
        rcases hf with hf | ⟨hf, -⟩
        · exact hsrc hf hfε
        · exact hsrc hf f.2
    rw [hset, finsum_mem_congr rfl hF, finsum_mem_subtype_ne (p := p)
      (fun h => h.elim hnot₀ (fun h' => h'.2 rfl))
      (fun e => θ.length e + if e = ε then θ.length e₀ else 0), sum_add_distrib]
    have hpε : p ε := Or.inl (Or.inl rfl)
    simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left hpε]
    have hdis : ∀ x, M.IsOnChain ε x → ¬ M.IsOnChain e₀ x := fun x h₁ h₂ =>
      hεe₀ (IsOnChain.unique h₁ h₂ (not_isChainVertex_source_reduceArc hM hb hX g) hc₀)
    have h₀₀ : M.IsOnChain e₀ e₀ := Or.inl rfl
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← sum_add_distrib,
      show θ.length e₀ = ∑ x, if x = e₀ then θ.length x else 0 by simp, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    by_cases h₁ : M.IsOnChain ε x
    · have h₂ : ¬ M.IsOnChain e₀ x := hdis x h₁
      have h₃ : x ≠ e₀ := fun h => hnot₀ (h ▸ h₁)
      simp [h₁, h₂, h₃]
    · by_cases h₃ : x = e₀
      · rw [h₃]
        simp [hnot₀, h₀₀]
      · by_cases h₂ : M.IsOnChain e₀ x <;> simp [h₁, h₂, h₃]
  · have hroot' : ¬ (reduceNet M hP).graph.source (sdArc hb.1 hb.2 hX g) =
        lsa hb.1 Set.univ Set.univ_nonempty := fun h =>
      hroot ((source_reduceArc_eq_root_iff hM hb hX h2 hl g).2 h)
    rw [ite_eq_right hroot', hLε]
    have hset : reduceChainOf hM hb hX g = {f : {e // e ≠ e₀} | M.IsOnChain ε f.1} := by
      ext f
      show (M.IsOnChain ε f.1 ∨ (M.graph.source ε = M.root ∧ M.IsOnChain e₀ f.1)) ↔
        M.IsOnChain ε f.1
      exact ⟨fun h => h.resolve_right fun h' => hroot h'.1, Or.inl⟩
    have hF : ∀ f ∈ {f : {e // e ≠ e₀} | M.IsOnChain ε f.1},
        (unrootAtMetric M e₀ θ).length f = θ.length f.1 := by
      intro f hf
      show (if M.graph.source f.1 = M.root then θ.length f.1 + θ.length e₀ else θ.length f.1) = _
      rw [ite_eq_right]
      by_cases hfε : f.1 = ε
      · rw [hfε]
        exact hroot
      · exact hsrc hf hfε
    rw [hset, finsum_mem_congr rfl hF, finsum_mem_subtype_ne hnot₀ θ.length]

include h2 hl in
/-- **The inheritance of a hybrid edge of the unrooted network of `reduceNet M` is that of the only
hybrid arc of its chain.** -/
theorem inheritance_eq_finprod_reduceChainOf (hθ : M.IsNormalized θ) (g : SemidirectedArc hb.1 hb.2 hX)
    (hd : (unrooted _ hb hX).IsDirected g) :
    (unrootedMetric (reduceNet M hM.phylo) hb hX (reduceMetric M hM.phylo θ)).inheritance g =
      ∏ᶠ f ∈ {f | f ∈ reduceChainOf hM hb hX g ∧
        (unrootAt M hM.phylo (reduceRootArc hM hb hX)).IsDirected f},
        (unrootAtMetric M (reduceRootArc hM hb hX) θ).inheritance f := by
  have hP := hM.phylo
  have hlast := lastArc_reduceArc_ne hM hb hX h2 hl g
  have hhyb : M.IsHybridArc (NMSC.lastArc hP (reduceArc hM hb hX g)) := by
    rw [semidirected_isDirected_iff] at hd
    exact (isHybridArc_reduceNet_iff hP hM.two _).1 hd
  have hset : {f | f ∈ reduceChainOf hM hb hX g ∧
      (unrootAt M hP (reduceRootArc hM hb hX)).IsDirected f} =
      {⟨NMSC.lastArc hP (reduceArc hM hb hX g), hlast⟩} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hf, hh⟩
      exact Subtype.ext (eq_lastArc_of_mem_reduceChainOf hM hb hX hf hh)
    · rintro rfl
      exact ⟨Or.inl (NMSC.isOnChain_lastArc hP _), hhyb⟩
  rw [hset, finprod_mem_singleton, semidirectedMetric_inheritance,
    reduceMetric_inheritance _ hθ]
  rfl

include h2 hl in
/-- **The unrooted network of `reduceNet M` is `unrootAt M` with its nodes of degree two
suppressed**, when the root of `M` has outdegree two, for `e₀ = reduceRootArc`: the edges of the
unrooted network are the chains of `M` through its chain nodes, the two chains at the root merged. -/
theorem nonempty_sdMetricIso_suppress_unrootAt (hθ : M.IsNormalized θ) :
    Nonempty (SDMetricIso (suppress (unrootAt M hM.phylo (reduceRootArc hM hb hX)))
      (suppressMetric (unrootAt M hM.phylo (reduceRootArc hM hb hX))
        (unrootAtMetric M (reduceRootArc hM hb hX) θ))
      (unrooted (reduceNet M hM.phylo) hb hX)
      (unrootedMetric (reduceNet M hM.phylo) hb hX (reduceMetric M hM.phylo θ))) := by
  have hP := hM.phylo
  have := hP.finite_arcs
  set e₀ := reduceRootArc hM hb hX
  have he₀ : M.graph.source e₀ = M.root := source_reduceRootArc hM hb hX h2 hl
  set G := unrootAt M hP e₀
  set R := unrooted (reduceNet M hP) hb hX
  have hbr : ∀ u, IsBranch G ∅ u ↔ ¬ M.IsChainVertex u.1 :=
    isBranch_unrootAt_iff hP he₀ h2 hM.deg
  -- the nodes
  let fv : SemidirectedVertex hb.1 hX → {u // IsBranch G ∅ u} := fun w =>
    ⟨⟨reduceVert hM hb hX w, (reduceVert_spec hM hb hX h2 hl w).1⟩,
      (hbr _).2 (reduceVert_spec hM hb hX h2 hl w).2⟩
  have hfv : Function.Bijective fv := by
    refine ⟨fun w w' h => reduceVert_injective hM hb hX (congrArg (fun u => u.1.1) h), ?_⟩
    rintro ⟨u, hu⟩
    obtain ⟨w, hw⟩ := exists_reduceVert_eq hM hb hX h2 hl u.2 ((hbr u).1 hu)
    exact ⟨w, Subtype.ext (Subtype.ext hw)⟩
  set φ := (Equiv.ofBijective fv hfv).symm
  have hφ : ∀ w, (φ.symm w).1.1 = reduceVert hM hb hX w := fun _ => rfl
  -- the chains
  choose ψ hψ using exists_mem_reduceChainOf hM hb hX h2 hl
  have hne' : ∀ g, (reduceChainOf hM hb hX g).Nonempty := fun g =>
    ⟨⟨reduceArc hM hb hX g, reduceArc_ne_reduceRootArc hM hb hX g⟩, Or.inl (Or.inl rfl)⟩
  have htrail : ∀ g, ∃ (u w : {v // v ≠ M.root}) (S : Set {v // v ≠ M.root}),
      IsUTrail G.graph u w S (reduceChainOf hM hb hX g) ∧ IsBranch G ∅ u ∧ IsBranch G ∅ w ∧
      (∀ s ∈ S, s ≠ u → s ≠ w → ¬ IsBranch G ∅ s) ∧ u = (φ.symm (R.graph.source g)).1 ∧
      w = (φ.symm (R.graph.target g)).1 := by
    intro g
    obtain ⟨u, w, S, hS, hu, hw, hin⟩ := exists_isUTrail_reduceChainOf hM hb hX h2 hl g
    refine ⟨u, w, S, hS, (hbr u).2 (by rw [hu]; exact (reduceVert_spec hM hb hX h2 hl _).2),
      (hbr w).2 (by rw [hw]; exact (reduceVert_spec hM hb hX h2 hl _).2),
      fun s hs h₁ h₂ hb' => (hbr s).1 hb' (hin s hs h₁ h₂), Subtype.ext hu, Subtype.ext hw⟩
  have hhyb : ∀ g, R.IsDirected g ↔
      M.IsHybridArc (NMSC.lastArc hP (reduceArc hM hb hX g)) := fun g => by
    rw [semidirected_isDirected_iff]
    exact isHybridArc_reduceNet_iff hP hM.two _
  refine nonempty_sdMetricIso_suppress (unrootAtMetric M e₀ θ)
    (unrootedMetric (reduceNet M hP) hb hX (reduceMetric M hP θ)) φ (reduceChainOf hM hb hX)
    (fun g => ?_) ψ hψ (fun g f hf => eq_of_mem_reduceChainOf hM hb hX h2 hl (hψ f) hf)
    (fun g => ?_) (fun g h => ?_) (fun g => ?_) (fun g f hf hd => ?_) (fun x => ?_)
    (length_eq_finsum_reduceChainOf hM hb hX h2 hl)
    (fun g hd => inheritance_eq_finprod_reduceChainOf hM hb hX h2 hl hθ g hd)
  · obtain ⟨u, w, S, hS, hu, hw, hin, -, -⟩ := htrail g
    exact hS.isChain (hne' g) hu hw hin
  · obtain ⟨u, w, S, hS, hu, hw, hin, hu', hw'⟩ := htrail g
    rw [hS.chainEnds_eq (hne' g) hu hw hin, hu', hw']
  · exact (semidirected_graph_isAcyclic hb.1 hb.2 hX) _ (.single ⟨g, h, rfl⟩)
  · rw [hhyb]
    constructor
    · intro h
      exact ⟨⟨_, lastArc_reduceArc_ne hM hb hX h2 hl g⟩,
        Or.inl (NMSC.isOnChain_lastArc hP _), h⟩
    · rintro ⟨f, hf, hd⟩
      have hd' : M.IsHybridArc f.1 := hd
      rw [← eq_lastArc_of_mem_reduceChainOf hM hb hX hf hd']
      exact hd'
  · have hd' : M.IsHybridArc f.1 := hd
    apply Subtype.ext
    show M.graph.target f.1 = reduceVert hM hb hX (R.graph.target g)
    rw [eq_lastArc_of_mem_reduceChainOf hM hb hX hf hd', NMSC.target_lastArc,
      reduceVert_target]
  · rw [Equiv.eq_symm_apply]
    exact Subtype.ext (Subtype.ext (reduceVert_leaf hM hb hX x))

end Reduce

end Banos2019
