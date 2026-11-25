module

public import Banos2019.Quartet.ReduceUnrooted
public import Banos2019.Network.SuppressMetric

/-!
# The unrooted network of a reduced network, with the top node kept

`keepRootSD M hP` is `M` with its tree arcs undirected and, when the root has outdegree one, without
the root and its arc. Its *top* node, the root or its child, has degree two. For `M` satisfying
`IsReducible` whose reduced network `reduceNet M` is an LSA network, and whose root, when of outdegree
one, has a child that is not a chain node, the unrooted network of `reduceNet M` is `keepRootSD M hP`
with its nodes of degree two suppressed (`nonempty_sdMetricIso_suppress_keepRootSD`): the top node and
the chain nodes.

* `keepRootTop`: the top node, the node of `M` of the root of `reduceNet M`
  (`keepRootTop_eq_root`, `keepRootTop_eq_target`); `isBranch_keepRootSD_iff`: the nodes kept by the
  suppression are those that are neither chain nodes nor the top node.
* `keepRootChainOf`: the arcs of `M` on the chain of an edge of the unrooted network of `reduceNet M`,
  a trail of `keepRootSD M` between the nodes of its ends (`exists_isUTrail_keepRootChainOf`), on
  which every arc lies exactly once (`exists_mem_keepRootChainOf`, `eq_of_mem_keepRootChainOf`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-- **`M` with its tree arcs undirected and its top node kept**: when the root has outdegree one,
without the root and its arc. -/
def keepRootSD (M : RootedNetwork V E X) (hP : M.IsPhylogenetic) :
    SemidirectedNetwork {v // ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)}
      {e // ¬ (M.graph.source e = M.root ∧ M.graph.outdegree M.root = 1)} X where
  graph :=
    { source := fun e => ⟨M.graph.source e.1, e.2⟩
      target := fun e => ⟨M.graph.target e.1, fun h => hP.target_ne_root e.1 h.1⟩ }
  IsDirected e := M.IsHybridArc e.1
  leaf x := ⟨M.leaf x, fun h => M.leaf_ne_root hP x h.1⟩

/-- The nodes of `keepRootSD M hP`. -/
abbrev KeepRootVertex (M : RootedNetwork V E X) :=
  {v // ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)}

/-- The edges of `keepRootSD M hP`. -/
abbrev KeepRootArc (M : RootedNetwork V E X) :=
  {e // ¬ (M.graph.source e = M.root ∧ M.graph.outdegree M.root = 1)}

section Trail

variable {M : RootedNetwork V E X} (hP : M.IsPhylogenetic)
include hP

/-- A node reached from a node of `keepRootSD M hP` is one. -/
theorem keepRoot_of_reaches {a b : V} (ha : ¬ (a = M.root ∧ M.graph.outdegree M.root = 1))
    (h : M.graph.Reaches a b) : ¬ (b = M.root ∧ M.graph.outdegree M.root = 1) := fun hb =>
  ha ⟨eq_of_reaches_of_reaches hP.acyclic (hb.1 ▸ h) (hP.root_reaches a), hb.2⟩

/-- A chain node is a node of `keepRootSD M hP`. -/
theorem keepRoot_of_isChainVertex {a : V} (ha : M.IsChainVertex a) :
    ¬ (a = M.root ∧ M.graph.outdegree M.root = 1) := fun h =>
  not_isChainVertex_root hP (h.1 ▸ ha)

/-- **The chain of `M` from a node `a` to a node `b` it reaches is a trail of `keepRootSD M hP`**,
through the chain nodes between them, along the arcs out of the chain nodes from `a` before `b`. -/
theorem isUTrail_keepRootSD_chainFrom {a : V} (ha : ¬ (a = M.root ∧ M.graph.outdegree M.root = 1))
    {b : V} (h : M.ChainReach a b) (hb : ¬ (b = M.root ∧ M.graph.outdegree M.root = 1)) :
    ∃ S : Set (KeepRootVertex M), IsUTrail (keepRootSD M hP).graph ⟨a, ha⟩ ⟨b, hb⟩ S
      {g | M.IsChainVertex (M.graph.source g.1) ∧ M.ChainReach a (M.graph.source g.1) ∧
        ¬ M.ChainReach b (M.graph.source g.1)} ∧
      ∀ s ∈ S, M.ChainReach a s.1 ∧ M.ChainReach s.1 b := by
  induction h with
  | refl =>
    refine ⟨{⟨a, ha⟩}, ?_, ?_⟩
    · have : {g : KeepRootArc M | M.IsChainVertex (M.graph.source g.1) ∧
          M.ChainReach a (M.graph.source g.1) ∧ ¬ M.ChainReach a (M.graph.source g.1)} = ∅ :=
        Set.eq_empty_of_forall_notMem fun g hg => hg.2.2 hg.2.1
      rw [this]
      exact .nil _
    · rintro s rfl
      exact ⟨.refl, .refl⟩
  | @tail y c hay hyc ih =>
    obtain ⟨hy, f, hfs, hft⟩ := hyc
    have hyr : ¬ (y = M.root ∧ M.graph.outdegree M.root = 1) := keepRoot_of_isChainVertex hP hy
    obtain ⟨S, hS, hSmem⟩ := ih hyr
    have hfk : ¬ (M.graph.source f = M.root ∧ M.graph.outdegree M.root = 1) := hfs ▸ hyr
    have hj : Joins (keepRootSD M hP).graph ⟨f, hfk⟩ ⟨y, hyr⟩ ⟨c, hb⟩ :=
      Or.inl ⟨Subtype.ext hfs, Subtype.ext hft⟩
    have hcyc : ∀ x, M.ChainReach c x → x ≠ y := fun x hx hxy =>
      hP.acyclic y (Relation.TransGen.head' ⟨f, hfs, hft⟩ (hxy ▸ hx.reaches))
    have hyc : (⟨y, hyr⟩ : KeepRootVertex M) ≠ ⟨c, hb⟩ := fun h =>
      hcyc c .refl (congrArg Subtype.val h).symm
    have hcS : (⟨c, hb⟩ : KeepRootVertex M) ∉ S := fun hcS => by
      obtain ⟨-, hcy⟩ := hSmem _ hcS
      exact hcyc y hcy rfl
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

/-- The chain of `M` from a node of `keepRootSD M hP`, to its end, as a trail of `keepRootSD M hP`. -/
theorem exists_isUTrail_keepRootSD_chainEnd {t : V}
    (ht : ¬ (t = M.root ∧ M.graph.outdegree M.root = 1)) :
    ∃ (hE : ¬ (chainEnd hP t = M.root ∧ M.graph.outdegree M.root = 1))
      (S : Set (KeepRootVertex M)),
      IsUTrail (keepRootSD M hP).graph ⟨t, ht⟩ ⟨chainEnd hP t, hE⟩ S
        {f | M.IsChainVertex (M.graph.source f.1) ∧ M.ChainReach t (M.graph.source f.1)} ∧
      ∀ s ∈ S, M.ChainReach t s.1 ∧ (s.1 ≠ chainEnd hP t → M.IsChainVertex s.1) := by
  have hc := chainReach_chainEnd hP t
  have hE := keepRoot_of_reaches hP ht hc.reaches
  obtain ⟨S, hS, hSmem⟩ := isUTrail_keepRootSD_chainFrom hP ht hc hE
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

end Trail

/-- The number of elements of a subtype satisfying `q`, when `q` implies the predicate of the
subtype. -/
theorem ncard_subtype_keepRoot {p q : E → Prop} (h : ∀ e, q e → p e) :
    {e : {e // p e} | q e.1}.ncard = {e | q e}.ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext e
  exact ⟨fun ⟨e', he', hee'⟩ => hee' ▸ he', fun he => ⟨⟨e, h e he⟩, he, rfl⟩⟩

/-- A sum over the elements of a subtype satisfying `p`, when `p` implies the predicate of the
subtype. -/
theorem finsum_mem_subtype_keepRoot [Fintype E] {q p : E → Prop} (hpq : ∀ e, p e → q e)
    (F : E → ℝ) : ∑ᶠ f ∈ {f : {e // q e} | p f.1}, F f.1 = ∑ e ∈ univ.filter p, F e := by
  have himg : Subtype.val '' {f : {e // q e} | p f.1} = ↑(univ.filter p) := by
    ext e
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro he
      exact ⟨⟨e, hpq e he⟩, he, rfl⟩
  rw [← finsum_mem_image (g := Subtype.val) Subtype.val_injective.injOn, himg,
    finsum_mem_coe_finset]

section KeepAux

variable [Fintype V] [Fintype E] {M : RootedNetwork V E X} {θ : MetricData E}

/-- The *top node* of `M`: the node of `M` of the root of `reduceNet M`, which is the root of `M`
when the root has outdegree two, and the end of the chain from its child when it has outdegree one. -/
def keepRootTop (M : RootedNetwork V E X) (hP : M.IsPhylogenetic) : V :=
  (finContractVertex (M.suppress hP) (reduceNet M hP).root).1

theorem not_isChainVertex_keepRootTop (hP : M.IsPhylogenetic) :
    ¬ M.IsChainVertex (keepRootTop M hP) :=
  (finContractVertex (M.suppress hP) (reduceNet M hP).root).2

variable (hM : IsReducible M θ)
include hM

/-- With a root of outdegree two, the top node is the root. -/
theorem keepRootTop_eq_root (h : M.graph.outdegree M.root ≠ 1) :
    keepRootTop M hM.phylo = M.root :=
  congrArg Subtype.val (hM.isContraction.root_ne (by rw [suppress_outdegree]; exact h))

/-- With a root of outdegree one, the top node is the end of the chain from the child of the
root. -/
theorem keepRootTop_eq_chainEnd (h : M.graph.outdegree M.root = 1) {e : E}
    (he : M.graph.source e = M.root) :
    keepRootTop M hM.phylo = chainEnd hM.phylo (M.graph.target e) := by
  obtain ⟨a, ha, ha'⟩ := hM.isContraction.root_one (by rw [suppress_outdegree]; exact h)
  have has : M.graph.source a.1 = M.root := congrArg Subtype.val ha
  obtain ⟨e₁, he₁⟩ := (M.graph.outdegree_eq_one_iff _).mp h
  have hae : a.1 = e := ((he₁ a.1).mp has).trans ((he₁ e).mp he).symm
  have h2 : chainEnd hM.phylo (M.graph.target a.1) = keepRootTop M hM.phylo :=
    congrArg Subtype.val ha'
  rw [← h2, hae]

/-- The top node is a node of `keepRootSD M`. -/
theorem keepRootTop_keepRoot :
    ¬ (keepRootTop M hM.phylo = M.root ∧ M.graph.outdegree M.root = 1) := by
  rintro ⟨hT, h1⟩
  obtain ⟨e, he⟩ := (M.graph.outdegree_eq_one_iff _).mp h1
  have hes : M.graph.source e = M.root := (he e).mpr rfl
  have heq := keepRootTop_eq_chainEnd hM h1 hes
  have hr := (chainReach_chainEnd hM.phylo (M.graph.target e)).reaches
  rw [← heq, hT] at hr
  exact hM.phylo.acyclic _ (Relation.TransGen.head' ⟨e, hes, rfl⟩ hr)

/-- The top node has outdegree two: it is the root of the binary network `reduceNet M`. -/
theorem outdegree_keepRootTop (hb : IsBinaryRootedNetwork (reduceNet M hM.phylo)) :
    M.graph.outdegree (keepRootTop M hM.phylo) = 2 := by
  have h := hM.isContraction.outdegree_eq (reduceNet M hM.phylo).root
  rw [hb.2.1, suppress_outdegree] at h
  exact h.symm

variable (hc : ∀ e, M.graph.source e = M.root → M.graph.outdegree M.root = 1 →
  ¬ M.IsChainVertex (M.graph.target e))

include hc in
/-- With a root of outdegree one whose child is not a chain node, the top node is the child. -/
theorem keepRootTop_eq_target (h : M.graph.outdegree M.root = 1) {e : E}
    (he : M.graph.source e = M.root) : keepRootTop M hM.phylo = M.graph.target e := by
  rw [keepRootTop_eq_chainEnd hM h he, chainEnd_eq_self hM.phylo (hc e he h)]

include hc in
/-- No arc of `keepRootSD M` enters the top node. -/
theorem target_ne_keepRootTop {f : E}
    (hf : ¬ (M.graph.source f = M.root ∧ M.graph.outdegree M.root = 1)) :
    M.graph.target f ≠ keepRootTop M hM.phylo := by
  intro hft
  by_cases h1 : M.graph.outdegree M.root = 1
  · obtain ⟨e, he⟩ := (M.graph.outdegree_eq_one_iff _).mp h1
    have hes : M.graph.source e = M.root := (he e).mpr rfl
    rw [keepRootTop_eq_target hM hc h1 hes] at hft
    have hfr : M.graph.source f ≠ M.root := fun h => hf ⟨h, h1⟩
    rcases Relation.ReflTransGen.cases_head (hM.phylo.root_reaches (M.graph.source f)) with
      h | ⟨b, ⟨a, has, hat⟩, hb⟩
    · exact hfr h.symm
    · have hae : a = e := (he a).mp has
      rw [hae] at hat
      exact hM.phylo.acyclic _ (Relation.TransGen.head' ⟨f, rfl, hft.trans hat⟩ hb)
  · rw [keepRootTop_eq_root hM h1] at hft
    exact hM.phylo.target_ne_root f hft

include hc in
/-- **The nodes that the suppression of `keepRootSD M` keeps** are those that are neither chain
nodes nor the top node. -/
theorem isBranch_keepRootSD_iff (hb : IsBinaryRootedNetwork (reduceNet M hM.phylo))
    (u : KeepRootVertex M) :
    IsBranch (keepRootSD M hM.phylo) ∅ u ↔
      ¬ M.IsChainVertex u.1 ∧ u.1 ≠ keepRootTop M hM.phylo := by
  have hP := hM.phylo
  have hout : (keepRootSD M hP).graph.outdegree u = M.graph.outdegree u.1 := by
    show {e : KeepRootArc M | (keepRootSD M hP).graph.source e = u}.ncard = _
    have : {e : KeepRootArc M | (keepRootSD M hP).graph.source e = u} =
        {e : KeepRootArc M | M.graph.source e.1 = u.1} := by
      ext e
      exact Subtype.ext_iff
    rw [this]
    exact ncard_subtype_keepRoot (q := fun e => M.graph.source e = u.1) fun e he => by
      rw [he]
      exact u.2
  have hin : u.1 ≠ keepRootTop M hP →
      (keepRootSD M hP).graph.indegree u = M.graph.indegree u.1 := by
    intro hT
    show {e : KeepRootArc M | (keepRootSD M hP).graph.target e = u}.ncard = _
    have : {e : KeepRootArc M | (keepRootSD M hP).graph.target e = u} =
        {e : KeepRootArc M | M.graph.target e.1 = u.1} := by
      ext e
      exact Subtype.ext_iff
    rw [this]
    refine ncard_subtype_keepRoot (q := fun e => M.graph.target e = u.1) fun e he => ?_
    rintro ⟨hs, h1⟩
    exact hT (he.symm.trans (keepRootTop_eq_target hM hc h1 hs).symm)
  have hinT : u.1 = keepRootTop M hP → (keepRootSD M hP).graph.indegree u = 0 := by
    intro hT
    show {e : KeepRootArc M | (keepRootSD M hP).graph.target e = u}.ncard = 0
    rw [Set.ncard_eq_zero]
    exact Set.eq_empty_of_forall_notMem fun e he =>
      target_ne_keepRootTop hM hc e.2 ((congrArg Subtype.val he).trans hT)
  have hleaf : (∃ x, (keepRootSD M hP).leaf x = u) ↔ ∃ x, M.leaf x = u.1 :=
    ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩, fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
  unfold IsBranch degree
  rw [hleaf]
  simp only [Set.mem_empty_iff_false, or_false]
  constructor
  · rintro (hd | ⟨x, hx⟩)
    · refine ⟨fun hch => hd ?_, fun hT => hd ?_⟩
      · have hT : u.1 ≠ keepRootTop M hP := fun h =>
          not_isChainVertex_keepRootTop hP (h ▸ hch)
        rw [hin hT, hout, hch.1, hch.2]
      · rw [hinT hT, hout, hT, outdegree_keepRootTop hM hb]
    · refine ⟨fun hch => not_isChainVertex_leaf hP x (hx ▸ hch), fun hT => ?_⟩
      have h2 := outdegree_keepRootTop hM hb
      rw [← hT, ← hx, (hP.leaves _).mpr ⟨x, rfl⟩] at h2
      omega
  · rintro ⟨hch, hT⟩
    by_cases h0 : M.graph.outdegree u.1 = 0
    · right
      obtain ⟨x, hx⟩ := (hP.leaves _).mp h0
      exact ⟨x, hx⟩
    · left
      have hur : u.1 ≠ M.root := fun h => by
        have h1 : M.graph.outdegree M.root = 1 := by
          by_contra h1
          exact hT (h.trans (keepRootTop_eq_root hM h1).symm)
        exact u.2 ⟨h, h1⟩
      rw [hin hT, hout, hM.deg u.1 hur h0 hch]
      omega

variable (hb : IsBinaryRootedNetwork (reduceNet M hM.phylo)) (hX : Nontrivial X)
  (hl : (reduceNet M hM.phylo).IsLSANetwork)

include hl in
/-- The node of `M` of a node of the unrooted network of `reduceNet M` is a node of `keepRootSD M`,
neither a chain node nor the top node. -/
theorem reduceVert_keepRoot (w : SemidirectedVertex hb.1 hX) :
    ¬ (reduceVert hM hb hX w = M.root ∧ M.graph.outdegree M.root = 1) ∧
      ¬ M.IsChainVertex (reduceVert hM hb hX w) ∧
      reduceVert hM hb hX w ≠ keepRootTop M hM.phylo := by
  have hK := hM.isContraction
  have hr := lsa_univ_eq_root hb.1 hX hl
  refine ⟨fun h => (hK.range_v _).1 ⟨_, rfl⟩ ⟨Subtype.ext h.1,
    (suppress_outdegree hM.phylo _).trans h.2⟩,
    (finContractVertex (M.suppress hM.phylo) (sdVert hb.1 hX w)).2, fun h => ?_⟩
  apply sdVert_ne_lsa hb.1 hX w
  rw [hr]
  exact hK.inj_v (Subtype.ext h)

include hl in
theorem exists_reduceVert_eq_keepRoot {v : V}
    (hv : ¬ (v = M.root ∧ M.graph.outdegree M.root = 1)) (hch : ¬ M.IsChainVertex v)
    (hT : v ≠ keepRootTop M hM.phylo) : ∃ w, reduceVert hM hb hX w = v := by
  have hK := hM.isContraction
  have hr := lsa_univ_eq_root hb.1 hX hl
  obtain ⟨c, hc'⟩ := (hK.range_v ⟨v, hch⟩).2 fun h =>
    hv ⟨congrArg Subtype.val h.1, (suppress_outdegree hM.phylo _).symm.trans h.2⟩
  have hcr : c ≠ (reduceNet M hM.phylo).root := fun h => hT (by
    unfold keepRootTop
    rw [← h, hc'])
  obtain ⟨w, hw⟩ := (mem_range_sdVert hb.1 hX c).2 ⟨hr ▸ hb.1.root_reaches c, hr ▸ hcr⟩
  exact ⟨w, by rw [reduceVert, hw, hc']⟩

omit hc in
/-- The arc of `M` of an edge of the unrooted network of `reduceNet M` is an arc of
`keepRootSD M`. -/
theorem reduceArc_keepRoot (g : SemidirectedArc hb.1 hb.2 hX) :
    ¬ (M.graph.source (reduceArc hM hb hX g) = M.root ∧ M.graph.outdegree M.root = 1) := fun h =>
  (hM.isContraction.range_e _).1 ⟨_, rfl⟩ ⟨Subtype.ext h.1, (suppress_outdegree hM.phylo _).trans h.2⟩

include hl in
theorem exists_reduceArc_eq_keepRoot {e : E} (he : ¬ M.IsChainVertex (M.graph.source e))
    (hk : ¬ (M.graph.source e = M.root ∧ M.graph.outdegree M.root = 1))
    (he₀ : e ≠ reduceRootArc hM hb hX) : ∃ g, reduceArc hM hb hX g = e := by
  have hr := lsa_univ_eq_root hb.1 hX hl
  obtain ⟨a, ha⟩ := (hM.isContraction.range_e ⟨e, he⟩).2 fun h =>
    hk ⟨congrArg Subtype.val h.1, (suppress_outdegree hM.phylo _).symm.trans h.2⟩
  have ha₀ : a ≠ sdRootArc hb.1 hb.2 hX := fun h => he₀ (by
    rw [reduceRootArc, ← h, ha])
  obtain ⟨g, hg⟩ := (mem_range_sdArc hb.1 hb.2 hX a).2 ⟨hr ▸ hb.1.root_reaches _, ha₀⟩
  exact ⟨g, by rw [reduceArc, hg, ha]⟩

include hl in
/-- The arc `reduceRootArc` leaves the top node. -/
theorem source_reduceRootArc_keepRoot :
    M.graph.source (reduceRootArc hM hb hX) = keepRootTop M hM.phylo := by
  have hr := lsa_univ_eq_root hb.1 hX hl
  have h := hM.isContraction.source (sdRootArc hb.1 hb.2 hX)
  rw [(sdRootArc_spec hb.1 hb.2 hX).1, hr] at h
  exact (congrArg Subtype.val h).symm

include hl in
/-- The source in `M` of the arc of an edge of the unrooted network of `reduceNet M` is the top node
exactly when its source in `reduceNet M` is the root. -/
theorem source_reduceArc_eq_keepRootTop_iff (g : SemidirectedArc hb.1 hb.2 hX) :
    M.graph.source (reduceArc hM hb hX g) = keepRootTop M hM.phylo ↔
      (reduceNet M hM.phylo).graph.source (sdArc hb.1 hb.2 hX g) =
        lsa hb.1 Set.univ Set.univ_nonempty := by
  have hr := lsa_univ_eq_root hb.1 hX hl
  have hK := hM.isContraction
  have hsrc := hK.source (sdArc hb.1 hb.2 hX g)
  rw [hr]
  constructor
  · intro h
    apply hK.inj_v
    rw [hsrc]
    exact Subtype.ext h
  · intro h
    rw [h] at hsrc
    exact (congrArg Subtype.val hsrc).symm

include hl in
/-- **The ends of an edge of the unrooted network of `reduceNet M`**: it leaves the first node of
the chain of its arc, or, for the merged edge, the last node of the chain of `reduceRootArc`, and
enters the last node of the chain of its arc. -/
theorem reduceVert_source_keepRoot (g : SemidirectedArc hb.1 hb.2 hX) :
    reduceVert hM hb hX ((unrooted _ hb hX).graph.source g) =
      if M.graph.source (reduceArc hM hb hX g) = keepRootTop M hM.phylo then
        chainEnd hM.phylo (M.graph.target (reduceRootArc hM hb hX))
      else M.graph.source (reduceArc hM hb hX g) := by
  have hK := hM.isContraction
  have hsrc := hK.source (sdArc hb.1 hb.2 hX g)
  have hroot := source_reduceArc_eq_keepRootTop_iff hM hb hX hl g
  unfold reduceVert
  rw [sdVert_source]
  by_cases h : M.graph.source (reduceArc hM hb hX g) = keepRootTop M hM.phylo
  · rw [ite_eq_left h, ite_eq_left (hroot.1 h), hK.target]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hroot.2 h')), hsrc]
    rfl

/-- The arcs of `keepRootSD M` of the chain of an edge of the unrooted network of `reduceNet M`:
those of the chain of its arc, and of the chain of `reduceRootArc` for the merged edge. -/
def keepRootChainOf (g : SemidirectedArc hb.1 hb.2 hX) : Set (KeepRootArc M) :=
  {f | M.IsOnChain (reduceArc hM hb hX g) f.1 ∨
    (M.graph.source (reduceArc hM hb hX g) = keepRootTop M hM.phylo ∧
      M.IsOnChain (reduceRootArc hM hb hX) f.1)}

omit hc in
include hl in
/-- **The chain of an edge of the unrooted network of `reduceNet M` is a trail of `keepRootSD M`**
between the nodes of the ends of the edge, through chain nodes and the top node. -/
theorem exists_isUTrail_keepRootChainOf (g : SemidirectedArc hb.1 hb.2 hX) :
    ∃ (u w : KeepRootVertex M) (S : Set (KeepRootVertex M)),
      IsUTrail (keepRootSD M hM.phylo).graph u w S (keepRootChainOf hM hb hX g) ∧
      u.1 = reduceVert hM hb hX ((unrooted _ hb hX).graph.source g) ∧
      w.1 = reduceVert hM hb hX ((unrooted _ hb hX).graph.target g) ∧
      ∀ s ∈ S, s ≠ u → s ≠ w → (M.IsChainVertex s.1 ∨ s.1 = keepRootTop M hM.phylo) := by
  have hP := hM.phylo
  set e₀ := reduceRootArc hM hb hX
  set ε := reduceArc hM hb hX g
  have he₀ : M.graph.source e₀ = keepRootTop M hM.phylo := source_reduceRootArc_keepRoot hM hb hX hl
  have hkε : ¬ (M.graph.source ε = M.root ∧ M.graph.outdegree M.root = 1) :=
    reduceArc_keepRoot hM hb hX g
  have hTk := keepRootTop_keepRoot hM
  have hk₀ : ¬ (M.graph.source e₀ = M.root ∧ M.graph.outdegree M.root = 1) := he₀ ▸ hTk
  have hcyc : ∀ {a b : V} (f : E), M.graph.source f = a → M.graph.target f = b →
      M.graph.Reaches b a → False := fun f hfa hfb h =>
    hP.acyclic _ (Relation.TransGen.head' ⟨f, hfa, hfb⟩ h)
  have ht₁ : ¬ (M.graph.target ε = M.root ∧ M.graph.outdegree M.root = 1) := fun h =>
    hP.target_ne_root ε h.1
  obtain ⟨hE₁, S₁, hS₁, hS₁mem⟩ := exists_isUTrail_keepRootSD_chainEnd hP ht₁
  by_cases hroot : M.graph.source ε = keepRootTop M hM.phylo
  · -- the merged edge: the chain of `e₀` backwards, the top node, `ε`, the chain of `ε`
    have ht₀ : ¬ (M.graph.target e₀ = M.root ∧ M.graph.outdegree M.root = 1) := fun h =>
      hP.target_ne_root e₀ h.1
    obtain ⟨hE₀, S₀, hS₀, hS₀mem⟩ := exists_isUTrail_keepRootSD_chainEnd hP ht₀
    have hsrc := reduceVert_source_keepRoot hM hb hX hl g
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
    have hj₁ : Joins (keepRootSD M hP).graph ⟨ε, hkε⟩ ⟨keepRootTop M hM.phylo, hTk⟩
        ⟨M.graph.target ε, ht₁⟩ := Or.inl ⟨Subtype.ext hroot, rfl⟩
    have hj₀ : Joins (keepRootSD M hP).graph ⟨e₀, hk₀⟩ ⟨keepRootTop M hM.phylo, hTk⟩
        ⟨M.graph.target e₀, ht₀⟩ := Or.inl ⟨Subtype.ext he₀, rfl⟩
    have hTS₁ : (⟨keepRootTop M hM.phylo, hTk⟩ : KeepRootVertex M) ∉ S₁ := fun h =>
      hcyc ε hroot rfl (hS₁mem _ h).1.reaches
    have hTS₀ : (⟨keepRootTop M hM.phylo, hTk⟩ : KeepRootVertex M) ∉ S₀ := fun h =>
      hcyc e₀ he₀ rfl (hS₀mem _ h).1.reaches
    have hB := IsUTrail.cons hj₁ hTS₁ hS₁
    have hA := IsUTrail.cons hj₀ hTS₀ hS₀
    have hAB := hA.reverse.append hB (by
      rintro x ⟨hx₀ | hx₀, hx₁ | hx₁⟩
      · exact hx₀
      · exact hx₀
      · exact hx₁
      · exact absurd (hS₁mem x hx₁).1 (hdis _ (hS₀mem x hx₀).1))
    refine ⟨⟨chainEnd hP (M.graph.target e₀), hE₀⟩, ⟨chainEnd hP (M.graph.target ε), hE₁⟩,
      insert ⟨keepRootTop M hM.phylo, hTk⟩ S₀ ∪ insert ⟨keepRootTop M hM.phylo, hTk⟩ S₁, ?_,
      hsrc.symm, htgt.symm, ?_⟩
    · have hset : keepRootChainOf hM hb hX g =
          insert ⟨e₀, hk₀⟩ {f : KeepRootArc M | M.IsChainVertex (M.graph.source f.1) ∧
            M.ChainReach (M.graph.target e₀) (M.graph.source f.1)} ∪
          insert ⟨ε, hkε⟩ {f : KeepRootArc M | M.IsChainVertex (M.graph.source f.1) ∧
            M.ChainReach (M.graph.target ε) (M.graph.source f.1)} := by
        ext f
        rw [Set.mem_union, Set.mem_insert_iff, Set.mem_insert_iff, Subtype.ext_iff,
          Subtype.ext_iff]
        show (M.IsOnChain ε f.1 ∨
            (M.graph.source ε = keepRootTop M hM.phylo ∧ M.IsOnChain e₀ f.1)) ↔ _
        unfold RootedNetwork.IsOnChain
        constructor
        · rintro ((h | h) | ⟨-, h | h⟩)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
        · rintro ((h | h) | (h | h))
          · exact Or.inr ⟨hroot, Or.inl h⟩
          · exact Or.inr ⟨hroot, Or.inr h⟩
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
      rw [hset]
      exact hAB
    · rintro x hx hx₀ hx₁
      rcases hx with (rfl | hx) | (rfl | hx)
      · exact Or.inr rfl
      · exact Or.inl ((hS₀mem x hx).2 fun h => hx₀ (Subtype.ext h))
      · exact Or.inr rfl
      · exact Or.inl ((hS₁mem x hx).2 fun h => hx₁ (Subtype.ext h))
  · -- the other edges: `ε` then its chain
    have hj : Joins (keepRootSD M hP).graph ⟨ε, hkε⟩ ⟨M.graph.source ε, hkε⟩
        ⟨M.graph.target ε, ht₁⟩ := Or.inl ⟨rfl, rfl⟩
    have hsS₁ : (⟨M.graph.source ε, hkε⟩ : KeepRootVertex M) ∉ S₁ := fun h =>
      hcyc ε rfl rfl (hS₁mem _ h).1.reaches
    have hB := IsUTrail.cons hj hsS₁ hS₁
    have hsrc := reduceVert_source_keepRoot hM hb hX hl g
    rw [ite_eq_right hroot] at hsrc
    refine ⟨⟨M.graph.source ε, hkε⟩, ⟨chainEnd hP (M.graph.target ε), hE₁⟩,
      insert ⟨M.graph.source ε, hkε⟩ S₁, ?_, hsrc.symm, (reduceVert_target hM hb hX g).symm, ?_⟩
    · have hset : keepRootChainOf hM hb hX g =
          insert ⟨ε, hkε⟩ {f : KeepRootArc M | M.IsChainVertex (M.graph.source f.1) ∧
            M.ChainReach (M.graph.target ε) (M.graph.source f.1)} := by
        ext f
        rw [Set.mem_insert_iff, Subtype.ext_iff]
        show (M.IsOnChain ε f.1 ∨
            (M.graph.source ε = keepRootTop M hM.phylo ∧ M.IsOnChain e₀ f.1)) ↔ _
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
      · exact Or.inl ((hS₁mem x hx).2 fun h => hxw (Subtype.ext h))

include hl hc in
/-- **Every arc of `keepRootSD M` is on the chain of one edge** of the unrooted network of
`reduceNet M`. -/
theorem exists_mem_keepRootChainOf (f : KeepRootArc M) :
    ∃ g, f ∈ keepRootChainOf hM hb hX g := by
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
    refine ⟨g, Or.inr ⟨(source_reduceArc_eq_keepRootTop_iff hM hb hX hl g).2 (ha.trans hr.symm),
      ?_⟩⟩
    have hc' := isOnChain_chainHead hP f.1
    rw [hh] at hc'
    exact hc'
  · have hk : ¬ (M.graph.source h.1 = M.root ∧ M.graph.outdegree M.root = 1) := by
      rintro ⟨hs, h1⟩
      rcases isOnChain_chainHead hP f.1 with hfe | ⟨hfc, hreach⟩
      · exact f.2 ⟨hfe ▸ hs, h1⟩
      · have hnc := hc h.1 hs h1
        rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨z, hz, -⟩
        · exact hnc (heq ▸ hfc)
        · exact hnc hz.1
    obtain ⟨g, hg⟩ := exists_reduceArc_eq_keepRoot hM hb hX hl h.2 hk hh
    refine ⟨g, Or.inl ?_⟩
    rw [hg]
    exact isOnChain_chainHead hP f.1

include hl in
/-- **An arc of `keepRootSD M` is on the chain of at most one edge.** -/
theorem eq_of_mem_keepRootChainOf {f : KeepRootArc M} {g g' : SemidirectedArc hb.1 hb.2 hX}
    (hg : f ∈ keepRootChainOf hM hb hX g) (hg' : f ∈ keepRootChainOf hM hb hX g') : g = g' := by
  have hc := not_isChainVertex_source_reduceArc hM hb hX
  have hc₀ := not_isChainVertex_source_reduceRootArc hM hb hX
  have hne := reduceArc_ne_reduceRootArc hM hb hX
  rcases hg with hg | ⟨hgr, hg⟩ <;> rcases hg' with hg' | ⟨hgr', hg'⟩
  · exact reduceArc_injective hM hb hX (IsOnChain.unique hg hg' (hc g) (hc g'))
  · exact absurd (IsOnChain.unique hg hg' (hc g) hc₀) (hne g)
  · exact absurd (IsOnChain.unique hg' hg (hc g') hc₀) (hne g')
  · exact eq_of_source_sdArc_eq_lsa hb.1 hb.2 hX
      ((source_reduceArc_eq_keepRootTop_iff hM hb hX hl g).1 hgr)
      ((source_reduceArc_eq_keepRootTop_iff hM hb hX hl g').1 hgr')

omit hc in
/-- **A hybrid arc on the chain of an edge is the last arc of the chain of the arc of the edge.** -/
theorem eq_lastArc_of_mem_keepRootChainOf {g : SemidirectedArc hb.1 hb.2 hX}
    {f : KeepRootArc M} (hf : f ∈ keepRootChainOf hM hb hX g) (hh : M.IsHybridArc f.1) :
    f.1 = NMSC.lastArc hM.phylo (reduceArc hM hb hX g) := by
  rcases hf with hf | ⟨-, hf⟩
  · exact NMSC.eq_lastArc hM.phylo hf (fun hc => by
      unfold IsHybridArc at hh
      rw [hc.1] at hh
      omega)
  · exact absurd hh (not_isHybridArc_of_isOnChain_reduceRootArc hM hb hX hf)

omit hc in
/-- The last arc of the chain of the arc of an edge is an arc of `keepRootSD M`. -/
theorem lastArc_reduceArc_keepRoot (g : SemidirectedArc hb.1 hb.2 hX) :
    ¬ (M.graph.source (NMSC.lastArc hM.phylo (reduceArc hM hb hX g)) = M.root ∧
      M.graph.outdegree M.root = 1) := by
  rcases NMSC.isOnChain_lastArc hM.phylo (reduceArc hM hb hX g) with h | ⟨h, -⟩
  · rw [h]
    exact reduceArc_keepRoot hM hb hX g
  · exact keepRoot_of_isChainVertex hM.phylo h

include hl in
/-- **The length of an edge of the unrooted network of `reduceNet M` is the total length of its
chain.** -/
theorem length_eq_finsum_keepRootChainOf (g : SemidirectedArc hb.1 hb.2 hX) :
    (unrootedMetric (reduceNet M hM.phylo) hb hX (reduceMetric M hM.phylo θ)).length g =
      ∑ᶠ f ∈ keepRootChainOf hM hb hX g, (restrictMetric θ _).length f := by
  have hP := hM.phylo
  set e₀ := reduceRootArc hM hb hX
  set ε := reduceArc hM hb hX g
  have hεe₀ : ε ≠ e₀ := reduceArc_ne_reduceRootArc hM hb hX g
  have hc₀ : ¬ M.IsChainVertex (M.graph.source e₀) :=
    not_isChainVertex_source_reduceRootArc hM hb hX
  have hLε : (reduceMetric M hP θ).length (sdArc hb.1 hb.2 hX g) =
      ∑ f ∈ univ.filter (M.IsOnChain ε), θ.length f := rfl
  have hL₀ : (reduceMetric M hP θ).length (sdRootArc hb.1 hb.2 hX) =
      ∑ f ∈ univ.filter (M.IsOnChain e₀), θ.length f := rfl
  have hk : ∀ {a f : E}, ¬ (M.graph.source a = M.root ∧ M.graph.outdegree M.root = 1) →
      M.IsOnChain a f → ¬ (M.graph.source f = M.root ∧ M.graph.outdegree M.root = 1) := by
    intro a f ha h
    rcases h with rfl | ⟨h, -⟩
    · exact ha
    · exact keepRoot_of_isChainVertex hP h
  have hkε : ¬ (M.graph.source ε = M.root ∧ M.graph.outdegree M.root = 1) :=
    reduceArc_keepRoot hM hb hX g
  have hk₀ : ¬ (M.graph.source e₀ = M.root ∧ M.graph.outdegree M.root = 1) :=
    (source_reduceRootArc_keepRoot hM hb hX hl) ▸ keepRootTop_keepRoot hM
  have hroot_iff := source_reduceArc_eq_keepRootTop_iff hM hb hX hl g
  rw [semidirectedMetric_length]
  by_cases hroot : M.graph.source ε = keepRootTop M hM.phylo
  · rw [ite_eq_left (hroot_iff.1 hroot), hLε, hL₀]
    have hset : keepRootChainOf hM hb hX g =
        {f : KeepRootArc M | M.IsOnChain ε f.1 ∨ M.IsOnChain e₀ f.1} := by
      ext f
      show (M.IsOnChain ε f.1 ∨
          (M.graph.source ε = keepRootTop M hM.phylo ∧ M.IsOnChain e₀ f.1)) ↔ _
      exact or_congr_right ⟨fun h => h.2, fun h => ⟨hroot, h⟩⟩
    rw [hset]
    change _ = ∑ᶠ f ∈ {f : KeepRootArc M | M.IsOnChain ε f.1 ∨ M.IsOnChain e₀ f.1},
      θ.length f.1
    have hdisj : Disjoint (univ.filter (M.IsOnChain ε)) (univ.filter (M.IsOnChain e₀)) :=
      Finset.disjoint_filter.2 fun x _ h₁ h₂ => hεe₀
        (IsOnChain.unique h₁ h₂ (not_isChainVertex_source_reduceArc hM hb hX g) hc₀)
    rw [finsum_mem_subtype_keepRoot (p := fun e => M.IsOnChain ε e ∨ M.IsOnChain e₀ e)
      (fun e h => h.elim (hk hkε) (hk hk₀)) θ.length, ← Finset.sum_union hdisj]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  · rw [ite_eq_right (fun h => hroot (hroot_iff.2 h)), hLε]
    have hset : keepRootChainOf hM hb hX g = {f : KeepRootArc M | M.IsOnChain ε f.1} := by
      ext f
      show (M.IsOnChain ε f.1 ∨
          (M.graph.source ε = keepRootTop M hM.phylo ∧ M.IsOnChain e₀ f.1)) ↔ _
      exact ⟨fun h => h.resolve_right fun h' => hroot h'.1, Or.inl⟩
    rw [hset]
    change _ = ∑ᶠ f ∈ {f : KeepRootArc M | M.IsOnChain ε f.1}, θ.length f.1
    rw [finsum_mem_subtype_keepRoot (p := fun e => M.IsOnChain ε e) (fun e h => hk hkε h)
      θ.length]

omit hc in
/-- **The inheritance of a hybrid edge of the unrooted network of `reduceNet M` is that of the only
hybrid arc of its chain.** -/
theorem inheritance_eq_finprod_keepRootChainOf (hθ : M.IsNormalized θ)
    (g : SemidirectedArc hb.1 hb.2 hX) (hd : (unrooted _ hb hX).IsDirected g) :
    (unrootedMetric (reduceNet M hM.phylo) hb hX (reduceMetric M hM.phylo θ)).inheritance g =
      ∏ᶠ f ∈ {f | f ∈ keepRootChainOf hM hb hX g ∧ (keepRootSD M hM.phylo).IsDirected f},
        (restrictMetric θ _).inheritance f := by
  have hP := hM.phylo
  have hk := lastArc_reduceArc_keepRoot hM hb hX g
  have hhyb : M.IsHybridArc (NMSC.lastArc hP (reduceArc hM hb hX g)) := by
    rw [semidirected_isDirected_iff] at hd
    exact (isHybridArc_reduceNet_iff hP hM.two _).1 hd
  have hset : {f | f ∈ keepRootChainOf hM hb hX g ∧ (keepRootSD M hP).IsDirected f} =
      {⟨NMSC.lastArc hP (reduceArc hM hb hX g), hk⟩} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hf, hh⟩
      exact Subtype.ext (eq_lastArc_of_mem_keepRootChainOf hM hb hX hf hh)
    · rintro rfl
      exact ⟨Or.inl (NMSC.isOnChain_lastArc hP _), hhyb⟩
  rw [hset, finprod_mem_singleton, semidirectedMetric_inheritance,
    reduceMetric_inheritance _ hθ]
  rfl

end KeepAux

section Keep

variable [Fintype V] [Fintype E] {M : RootedNetwork V E X} {θ : MetricData E}

/-- **The unrooted network of `reduceNet M` is `keepRootSD M` with its nodes of degree two
suppressed**: its nodes are the nodes of `M` other than the root, the top node and the chain nodes;
an edge is the chain of `M` of its arc, and the merged edge at the root the two chains out of the top
node. -/
theorem nonempty_sdMetricIso_suppress_keepRootSD (hM : IsReducible M θ)
    (hb : IsBinaryRootedNetwork (reduceNet M hM.phylo)) (hX : Nontrivial X)
    (hl : (reduceNet M hM.phylo).IsLSANetwork)
    (hc : ∀ e, M.graph.source e = M.root → M.graph.outdegree M.root = 1 →
      ¬ M.IsChainVertex (M.graph.target e)) :
    Nonempty (SDMetricIso (suppress (keepRootSD M hM.phylo))
      (suppressMetric (keepRootSD M hM.phylo) (restrictMetric θ _))
      (unrooted (reduceNet M hM.phylo) hb hX)
      (unrootedMetric (reduceNet M hM.phylo) hb hX (reduceMetric M hM.phylo θ))) := by
  have hP := hM.phylo
  have := hP.finite_arcs
  set G := keepRootSD M hP
  set R := unrooted (reduceNet M hP) hb hX
  have hbr : ∀ u, IsBranch G ∅ u ↔ ¬ M.IsChainVertex u.1 ∧ u.1 ≠ keepRootTop M hM.phylo :=
    isBranch_keepRootSD_iff hM hc hb
  -- the nodes
  let fv : SemidirectedVertex hb.1 hX → {u // IsBranch G ∅ u} := fun w =>
    ⟨⟨reduceVert hM hb hX w, (reduceVert_keepRoot hM hb hX hl w).1⟩,
      (hbr _).2 (reduceVert_keepRoot hM hb hX hl w).2⟩
  have hfv : Function.Bijective fv := by
    refine ⟨fun w w' h => reduceVert_injective hM hb hX (congrArg (fun u => u.1.1) h), ?_⟩
    rintro ⟨u, hu⟩
    obtain ⟨hch, hT⟩ := (hbr u).1 hu
    obtain ⟨w, hw⟩ := exists_reduceVert_eq_keepRoot hM hb hX hl u.2 hch hT
    exact ⟨w, Subtype.ext (Subtype.ext hw)⟩
  set φ := (Equiv.ofBijective fv hfv).symm
  -- the chains
  choose ψ hψ using exists_mem_keepRootChainOf hM hc hb hX hl
  have hne' : ∀ g, (keepRootChainOf hM hb hX g).Nonempty := fun g =>
    ⟨⟨reduceArc hM hb hX g, reduceArc_keepRoot hM hb hX g⟩, Or.inl (Or.inl rfl)⟩
  have htrail : ∀ g, ∃ (u w : KeepRootVertex M) (S : Set (KeepRootVertex M)),
      IsUTrail G.graph u w S (keepRootChainOf hM hb hX g) ∧ IsBranch G ∅ u ∧ IsBranch G ∅ w ∧
      (∀ s ∈ S, s ≠ u → s ≠ w → ¬ IsBranch G ∅ s) ∧ u = (φ.symm (R.graph.source g)).1 ∧
      w = (φ.symm (R.graph.target g)).1 := by
    intro g
    obtain ⟨u, w, S, hS, hu, hw, hin⟩ := exists_isUTrail_keepRootChainOf hM hb hX hl g
    refine ⟨u, w, S, hS, (hbr u).2 (by rw [hu]; exact (reduceVert_keepRoot hM hb hX hl _).2),
      (hbr w).2 (by rw [hw]; exact (reduceVert_keepRoot hM hb hX hl _).2),
      fun s hs h₁ h₂ hb' => ?_, Subtype.ext hu, Subtype.ext hw⟩
    obtain ⟨hch, hT⟩ := (hbr s).1 hb'
    rcases hin s hs h₁ h₂ with h | h
    · exact hch h
    · exact hT h
  have hhyb : ∀ g, R.IsDirected g ↔
      M.IsHybridArc (NMSC.lastArc hP (reduceArc hM hb hX g)) := fun g => by
    rw [semidirected_isDirected_iff]
    exact isHybridArc_reduceNet_iff hP hM.two _
  refine nonempty_sdMetricIso_suppress (restrictMetric θ _)
    (unrootedMetric (reduceNet M hP) hb hX (reduceMetric M hP θ)) φ (keepRootChainOf hM hb hX)
    (fun g => ?_) ψ hψ (fun g f hf => eq_of_mem_keepRootChainOf hM hb hX hl (hψ f) hf)
    (fun g => ?_) (fun g h => ?_) (fun g => ?_) (fun g f hf hd => ?_) (fun x => ?_)
    (length_eq_finsum_keepRootChainOf hM hb hX hl)
    (fun g hd => inheritance_eq_finprod_keepRootChainOf hM hb hX hM.metric.isNormalized g hd)
  · obtain ⟨u, w, S, hS, hu, hw, hin, -, -⟩ := htrail g
    exact hS.isChain (hne' g) hu hw hin
  · obtain ⟨u, w, S, hS, hu, hw, hin, hu', hw'⟩ := htrail g
    rw [hS.chainEnds_eq (hne' g) hu hw hin, hu', hw']
  · exact (semidirected_graph_isAcyclic hb.1 hb.2 hX) _ (.single ⟨g, h, rfl⟩)
  · rw [hhyb]
    constructor
    · intro h
      exact ⟨⟨_, lastArc_reduceArc_keepRoot hM hb hX g⟩,
        Or.inl (NMSC.isOnChain_lastArc hP _), h⟩
    · rintro ⟨f, hf, hd⟩
      have hd' : M.IsHybridArc f.1 := hd
      rw [← eq_lastArc_of_mem_keepRootChainOf hM hb hX hf hd']
      exact hd'
  · have hd' : M.IsHybridArc f.1 := hd
    apply Subtype.ext
    show M.graph.target f.1 = reduceVert hM hb hX (R.graph.target g)
    rw [eq_lastArc_of_mem_keepRootChainOf hM hb hX hf hd', NMSC.target_lastArc,
      reduceVert_target]
  · rw [Equiv.eq_symm_apply]
    exact Subtype.ext (Subtype.ext (reduceVert_leaf hM hb hX x))

end Keep

end Banos2019
