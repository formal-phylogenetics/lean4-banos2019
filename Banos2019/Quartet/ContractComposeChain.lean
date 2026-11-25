module

public import Banos2019.Quartet.RootedIso
public import Phylogenetics.NMSC.InducedSuppress

/-!
# Suppressing some of the chain nodes of a network

`RootedNetwork.suppress` suppresses all the nodes of indegree one and outdegree one (the chain
nodes) of a network at once. `IsPartialSuppression N N' φ ψ` says that `N'` is `N` with some of its
chain nodes suppressed: the nodes and arcs of `N'` are nodes and arcs of `N` through `φ` and `ψ`,
and an arc `e` of `N'` stands for the arcs of `N` along the chain from `ψ e` through the nodes of
`N` that are not nodes of `N'` (`segArcs`). The two networks have the same suppression, and, with
lengths added and inheritances multiplied along these arcs, the same concordance factors.

* `ChainReachOff N R`: reaching along a chain through chain nodes outside `R`.
* `IsPartialSuppression.chainEnd_map`: the chains of `N'` end where those of `N` end.
* `IsPartialSuppression.suppressIso`: the suppressions of `N'` and of `N` are isomorphic.
* `IsPartialSuppression.isOnChain_iff`, `disjoint_segArcs`: the chain of `N` of an arc of `N'` is
  the union of the disjoint sets of arcs that the arcs of its chain in `N'` stand for.
* `IsPartialSuppression.cf_eq`: `N'` and `N` have the same concordance factors.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace Banos2019

variable {V E V' E' X : Type*}

/-! ### Chains through nodes outside a set -/

section ChainReachOff

variable {N : RootedNetwork V E X} {R : Set V}

/-- `b` is reached from `a` along the chain from `a`, through chain nodes outside `R`. -/
def ChainReachOff (N : RootedNetwork V E X) (R : Set V) : V → V → Prop :=
  Relation.ReflTransGen fun a b => N.IsChainVertex a ∧ a ∉ R ∧ N.graph.Adj a b

theorem ChainReachOff.chainReach {a b : V} (h : ChainReachOff N R a b) : N.ChainReach a b :=
  Relation.ReflTransGen.mono (fun _ _ h => ⟨h.1, h.2.2⟩) _ _ h

/-- A chain through nodes outside `R` reaches at most one node of `R`. -/
theorem ChainReachOff.eq_of_mem {a b b' : V} (h : ChainReachOff N R a b)
    (h' : ChainReachOff N R a b') (hb : b ∈ R) (hb' : b' ∈ R) : b = b' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rcases Relation.ReflTransGen.cases_head h' with h | ⟨c, hc, -⟩
    · exact h
    · exact absurd hb hc.2.1
  | @head a a₁ hstep _ ih =>
    rcases Relation.ReflTransGen.cases_head h' with h | ⟨c, hc, hcb⟩
    · exact absurd (h ▸ hb') hstep.2.1
    · have : a₁ = c := hstep.1.adj_unique hstep.2.2 hc.2.2
      subst this
      exact ih hcb

/-- Two arcs out of nodes of `R`, whose chains through nodes outside `R` reach a common node of
indegree one, are the same arc. -/
theorem arc_eq_of_chainReachOff {e e' : E} {w : V} (he : N.graph.source e ∈ R)
    (he' : N.graph.source e' ∈ R) (h : ChainReachOff N R (N.graph.target e) w)
    (h' : ChainReachOff N R (N.graph.target e') w) (hw : N.graph.indegree w = 1) : e = e' := by
  induction h with
  | refl =>
    obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp hw
    rcases Relation.ReflTransGen.cases_tail h' with h | ⟨b, -, -, hbR, f, hfs, hft⟩
    · rw [(hg e).mp rfl, (hg e').mp h.symm]
    · have hfe : f = e := by rw [(hg f).mp hft, (hg e).mp rfl]
      subst hfe
      exact absurd (hfs ▸ he) hbR
  | @tail a b _ hstep ih =>
    obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp hw
    obtain ⟨ha, haR, f, hfs, hft⟩ := hstep
    rcases Relation.ReflTransGen.cases_tail h' with h | ⟨c, hc, -, -, f', hfs', hft'⟩
    · have hfe : f = e' := by rw [(hg f).mp hft, (hg e').mp h.symm]
      subst hfe
      exact absurd (hfs ▸ he') haR
    · have hff : f = f' := by rw [(hg f).mp hft, (hg f').mp hft']
      subst hff
      have hac : a = c := hfs.symm.trans hfs'
      subst hac
      exact ih hc ha.1

end ChainReachOff

/-! ### Suppressing some of the chain nodes -/

/-- **`N'` is `N` with some of its chain nodes suppressed**: the nodes and the arcs of `N'` are,
through the injective maps `φ` and `ψ`, nodes and arcs of `N`; every node of `N` that is not a chain
node is a node of `N'`, and every arc of `N` out of a node of `N'` an arc of `N'`; an arc of `N'`
keeps its source, and its target is reached from the target of its arc in `N` along the chain of `N`
through nodes that are not nodes of `N'`; a node of `N'` is a chain node of `N'` exactly when it is
one of `N`; the root and the leaves are those of `N`. -/
structure IsPartialSuppression (N : RootedNetwork V E X) (N' : RootedNetwork V' E' X) (φ : V' → V)
    (ψ : E' → E) : Prop where
  inj_v : Function.Injective φ
  inj_e : Function.Injective ψ
  source : ∀ e, N.graph.source (ψ e) = φ (N'.graph.source e)
  target : ∀ e, ChainReachOff N (Set.range φ) (N.graph.target (ψ e)) (φ (N'.graph.target e))
  chain_iff : ∀ v, N.IsChainVertex (φ v) ↔ N'.IsChainVertex v
  range_v : ∀ v, ¬ N.IsChainVertex v → v ∈ Set.range φ
  range_e : ∀ e v, N.graph.source e = φ v → e ∈ Set.range ψ
  root : φ N'.root = N.root
  leaf : ∀ x, φ (N'.leaf x) = N.leaf x

/-- The arcs of `N` that the arc `e` of `N'` stands for: its arc `ψ e`, and the arcs out of the
nodes that are not nodes of `N'` on the chain from its target. -/
def segArcs [Fintype E] (N : RootedNetwork V E X) (φ : V' → V) (ψ : E' → E) (e : E') : Finset E :=
  univ.filter fun g => g = ψ e ∨
    (N.graph.source g ∉ Set.range φ ∧
      ChainReachOff N (Set.range φ) (N.graph.target (ψ e)) (N.graph.source g))

namespace IsPartialSuppression

variable {N : RootedNetwork V E X} {N' : RootedNetwork V' E' X} {φ : V' → V} {ψ : E' → E}
  (hS : IsPartialSuppression N N' φ ψ)
include hS

theorem adj_chainReach {a b : V'} (ha : N'.IsChainVertex a) (hab : N'.graph.Adj a b) :
    N.ChainReach (φ a) (φ b) := by
  obtain ⟨f, rfl, rfl⟩ := hab
  exact Relation.ReflTransGen.head ⟨(hS.chain_iff _).2 ha, ψ f, hS.source f, rfl⟩
    (hS.target f).chainReach

/-- **A chain of `N'` is a chain of `N`.** -/
theorem chainReach_map {a b : V'} (h : N'.ChainReach a b) : N.ChainReach (φ a) (φ b) := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact ih.trans (hS.adj_chainReach hab.1 hab.2)

theorem isOnChain_map {e g : E'} (h : N'.IsOnChain e g) : N.IsOnChain (ψ e) (ψ g) := by
  rcases h with rfl | ⟨hc, hr⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, ?_⟩
    · rw [hS.source]
      exact (hS.chain_iff _).2 hc
    · rw [hS.source]
      exact (hS.target e).chainReach.trans (hS.chainReach_map hr)

/-- An arc of `N` out of a chain node of `N'` reached from the target of the arc `g` of the chain of
`e` in `N'` is the arc of an arc of the chain of `e`. -/
theorem exists_next {e g : E'} (hg : N'.IsOnChain e g) {f : E}
    (hr : ChainReachOff N (Set.range φ) (N.graph.target (ψ g)) (N.graph.source f))
    (hs : N.graph.source f ∈ Set.range φ) (hc : N.IsChainVertex (N.graph.source f)) :
    ∃ k, ψ k = f ∧ N'.IsOnChain e k := by
  have hu := hr.eq_of_mem (hS.target g) hs ⟨_, rfl⟩
  obtain ⟨k, rfl⟩ := hS.range_e f _ hu
  have hks : N'.graph.source k = N'.graph.target g := hS.inj_v ((hS.source k).symm.trans hu)
  refine ⟨k, rfl, Or.inr ⟨?_, ?_⟩⟩
  · rw [← hS.chain_iff, ← hS.source]
    exact hc
  · rw [hks]
    exact NMSC.IsOnChain.chainReach_target hg

theorem exists_isOnChain_chainReachOff {e : E'} {w : V}
    (h : N.ChainReach (N.graph.target (ψ e)) w) :
    ∃ g, N'.IsOnChain e g ∧ ChainReachOff N (Set.range φ) (N.graph.target (ψ g)) w := by
  induction h with
  | refl => exact ⟨e, Or.inl rfl, .refl⟩
  | @tail a b _ hab ih =>
    obtain ⟨g, hg, hr⟩ := ih
    obtain ⟨ha, f, hfs, hft⟩ := hab
    by_cases haR : a ∈ Set.range φ
    · subst hfs hft
      obtain ⟨k, rfl, hk⟩ := hS.exists_next hg hr haR ha
      exact ⟨k, hk, .refl⟩
    · exact ⟨g, hg, hr.tail ⟨ha, haR, f, hfs, hft⟩⟩

variable [Fintype E]

theorem isOnChain_of_mem_segArcs {e g : E'} (hg : N'.IsOnChain e g) {f : E}
    (hf : f ∈ segArcs N φ ψ g) : N.IsOnChain (ψ e) f := by
  have hon := hS.isOnChain_map hg
  rcases (mem_filter.1 hf).2 with rfl | ⟨hR, hr⟩
  · exact hon
  · have hc : N.IsChainVertex (N.graph.source f) := by
      by_contra h
      exact hR (hS.range_v _ h)
    exact Or.inr ⟨hc, (NMSC.IsOnChain.chainReach_target hon).trans hr.chainReach⟩

/-- **The chain of `N` of the arc of an arc `e` of `N'`** is made of the arcs that the arcs of the
chain of `e` in `N'` stand for. -/
theorem isOnChain_iff (e : E') (f : E) :
    N.IsOnChain (ψ e) f ↔ ∃ g, N'.IsOnChain e g ∧ f ∈ segArcs N φ ψ g := by
  refine ⟨fun h => ?_, fun ⟨g, hg, hf⟩ => hS.isOnChain_of_mem_segArcs hg hf⟩
  rcases h with rfl | ⟨hc, hr⟩
  · exact ⟨e, Or.inl rfl, mem_filter.2 ⟨mem_univ _, Or.inl rfl⟩⟩
  · obtain ⟨g, hg, hr'⟩ := hS.exists_isOnChain_chainReachOff hr
    by_cases hs : N.graph.source f ∈ Set.range φ
    · obtain ⟨k, rfl, hk⟩ := hS.exists_next hg hr' hs hc
      exact ⟨k, hk, mem_filter.2 ⟨mem_univ _, Or.inl rfl⟩⟩
    · exact ⟨g, hg, mem_filter.2 ⟨mem_univ _, Or.inr ⟨hs, hr'⟩⟩⟩

/-- **Distinct arcs of `N'` stand for disjoint sets of arcs of `N`.** -/
theorem disjoint_segArcs {g₁ g₂ : E'} (hne : g₁ ≠ g₂) :
    Disjoint (segArcs N φ ψ g₁) (segArcs N φ ψ g₂) := by
  refine Finset.disjoint_left.2 fun f hf₁ hf₂ => hne ?_
  rcases (mem_filter.1 hf₁).2 with rfl | ⟨hR₁, hr₁⟩ <;>
    rcases (mem_filter.1 hf₂).2 with h | ⟨hR₂, hr₂⟩
  · exact hS.inj_e h
  · exact (hR₂ ⟨_, (hS.source g₁).symm⟩).elim
  · exact (hR₁ ⟨_, h ▸ (hS.source g₂).symm⟩).elim
  · have hc : N.IsChainVertex (N.graph.source f) := by
      by_contra h
      exact hR₁ (hS.range_v _ h)
    exact hS.inj_e (arc_eq_of_chainReachOff (R := Set.range φ) ⟨_, (hS.source g₁).symm⟩
      ⟨_, (hS.source g₂).symm⟩ hr₁ hr₂ hc.1)

theorem filter_isOnChain_eq [Fintype E'] (e : E') :
    univ.filter (N.IsOnChain (ψ e)) = (univ.filter (N'.IsOnChain e)).biUnion (segArcs N φ ψ) := by
  ext f
  simp only [mem_filter, mem_univ, true_and, mem_biUnion]
  exact hS.isOnChain_iff e f

variable (hN : N.IsPhylogenetic) (hN' : N'.IsPhylogenetic)

omit [Fintype E] in
/-- **The chains of `N'` end where those of `N` end.** -/
theorem chainEnd_map (v : V') : chainEnd hN (φ v) = φ (chainEnd hN' v) :=
  chainEnd_eq_of_chainReach hN (hS.chainReach_map (chainReach_chainEnd hN' v))
    (fun h => not_isChainVertex_chainEnd hN' v ((hS.chain_iff _).1 h))

omit [Fintype E] in
theorem chainEnd_target (e : E') :
    chainEnd hN (N.graph.target (ψ e)) = φ (chainEnd hN' (N'.graph.target e)) := by
  rw [chainEnd_eq_of_chainReach_left hN (hS.target e).chainReach, hS.chainEnd_map hN hN']

omit hS hN hN' in
/-- The nodes of the suppressed networks. -/
def suppressVertEquiv (hS : IsPartialSuppression N N' φ ψ) :
    {v // ¬ N'.IsChainVertex v} ≃ {v // ¬ N.IsChainVertex v} :=
  Equiv.ofBijective (fun v => ⟨φ v.1, fun h => v.2 ((hS.chain_iff _).1 h)⟩)
    ⟨fun a b h => Subtype.ext (hS.inj_v (congrArg Subtype.val h)), fun v => by
      obtain ⟨u, hu⟩ := hS.range_v v.1 v.2
      exact ⟨⟨u, fun h => v.2 (hu ▸ (hS.chain_iff u).2 h)⟩, Subtype.ext hu⟩⟩

omit hS hN hN' in
/-- The arcs of the suppressed networks. -/
def suppressArcEquiv (hS : IsPartialSuppression N N' φ ψ) :
    {e // ¬ N'.IsChainVertex (N'.graph.source e)} ≃ {e // ¬ N.IsChainVertex (N.graph.source e)} :=
  Equiv.ofBijective
    (fun e => ⟨ψ e.1, by rw [hS.source]; exact fun h => e.2 ((hS.chain_iff _).1 h)⟩)
    ⟨fun a b h => Subtype.ext (hS.inj_e (congrArg Subtype.val h)), fun e => by
      obtain ⟨v, hv⟩ := hS.range_v _ e.2
      obtain ⟨f, hf⟩ := hS.range_e e.1 v hv.symm
      refine ⟨⟨f, fun h => e.2 ?_⟩, Subtype.ext hf⟩
      rw [← hf, hS.source]
      exact (hS.chain_iff _).2 h⟩

omit hS in
/-- **`N'` and `N` have the same suppression.** -/
def suppressIso (hS : IsPartialSuppression N N' φ ψ) :
    RootedNetworkIso (N'.suppress hN') (N.suppress hN) where
  vert := hS.suppressVertEquiv
  arc := hS.suppressArcEquiv
  source e := Subtype.ext (hS.source e.1)
  target e := Subtype.ext (hS.chainEnd_target hN hN' e.1)
  root := Subtype.ext hS.root.symm
  leaf x := Subtype.ext (hS.leaf x).symm

include hN hN' in
/-- **`N'` has the concordance factors of `N`** when the length of an arc of `N'` is the total
length of the arcs of `N` it stands for, and its inheritance the product of their inheritances. -/
theorem cf_eq [Fintype V] [Fintype V'] [Fintype E'] [Fintype X]
    {θ : MetricData E} {θ' : MetricData E'} (hθ : N.IsNormalized θ) (hθ' : N'.IsNormalized θ')
    (hlen : ∀ e, θ'.length e = ∑ f ∈ segArcs N φ ψ e, θ.length f)
    (hinh : ∀ e, θ'.inheritance e = ∏ f ∈ segArcs N φ ψ e, θ.inheritance f) :
    cf N' θ' = cf N θ := by
  have hd : ((univ : Finset E') : Set E').PairwiseDisjoint (segArcs N φ ψ) :=
    fun a _ b _ hab => hS.disjoint_segArcs hab
  have h := (hS.suppressIso hN hN').cf_eq (suppress_isPhylogenetic hN')
    (θ := N'.suppressMetric θ') (θ' := N.suppressMetric θ) (fun e => ?_) (fun e => ?_)
  · funext q
    show nmscCF N' θ' 0 q = nmscCF N θ 0 q
    rw [← nmscCF_suppress hN' hθ' le_rfl q, ← nmscCF_suppress hN hθ le_rfl q]
    exact (congrFun h q).symm
  · change ∑ f with N.IsOnChain (ψ e.1) f, θ.length f = ∑ f with N'.IsOnChain e.1 f, θ'.length f
    rw [hS.filter_isOnChain_eq, sum_biUnion (hd.subset (subset_univ _))]
    exact sum_congr rfl fun g _ => (hlen g).symm
  · change ∏ f with N.IsOnChain (ψ e.1) f, θ.inheritance f =
      ∏ f with N'.IsOnChain e.1 f, θ'.inheritance f
    rw [hS.filter_isOnChain_eq, prod_biUnion (hd.subset (subset_univ _))]
    exact prod_congr rfl fun g _ => (hinh g).symm

end IsPartialSuppression

end Banos2019
