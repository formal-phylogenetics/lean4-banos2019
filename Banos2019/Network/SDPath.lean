module

public import Banos2019.Network.SemidirectedDesc

/-!
# Semidirected paths, edge by edge

`IsSDP G u w S P`: a semidirected path from `u` to `w` with distinct nodes `S` and edges `P`, given
step by step; it is `IsSDPath` (`IsSDPathOf.isSDP`). In a semidirected network in which two edges
entering a node are hybrid (`IsSDP.shape`), such a path first goes against the direction of tree
edges and then follows the directions; and a simple trek of semidirected paths gives a simple trek
of directed paths (`exists_dtrek_of_sdtrek`). This is the argument of the proof of Proposition 1 that
the edges of a trek of `N⁻` are first traversed "uphill" and then "downhill".
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*}

section SDP

variable (G : SemidirectedNetwork V E X)

/-- A semidirected path through distinct nodes, step by step. -/
inductive IsSDP : V → V → Set V → Set E → Prop
  | nil (u : V) : IsSDP u u {u} ∅
  | cons {e : E} {a b w : V} {S : Set V} {P : Set E} :
      SDStep G e a b → a ∉ S → IsSDP b w S P → IsSDP a w (insert a S) (insert e P)

variable {G}

/-- A semidirected path given by its nodes and edges in order is a path step by step. -/
theorem IsSDPathOf.isSDP {k : ℕ} {v : Fin (k + 1) → V} {e : Fin k → E}
    (h : IsSDPathOf G k v e) : IsSDP G (v 0) (v (Fin.last k)) (Set.range v) (Set.range e) := by
  induction k with
  | zero =>
    have hv : Set.range v = {v 0} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        rw [show i = 0 from Fin.ext (by have := i.2; omega)]
        rfl
      · intro hx
        exact ⟨0, hx.symm⟩
    rw [hv, Set.range_eq_empty e, show Fin.last 0 = 0 from rfl]
    exact .nil _
  | succ k ih =>
    have ht : IsSDPathOf G k (Fin.tail v) (Fin.tail e) := by
      refine ⟨fun i => ?_, h.injective.comp (Fin.succ_injective _)⟩
      have := h.step i.succ
      simp only [Fin.tail]
      rwa [Fin.succ_castSucc]
    have := ih ht
    rw [Fin.range_fin_succ v, Fin.range_fin_succ e]
    refine .cons (h.step 0) ?_ ?_
    · rintro ⟨i, hi⟩
      exact Fin.succ_ne_zero i (h.injective hi)
    · simpa [Fin.tail, Fin.succ_last] using this

theorem IsSDPath.isSDP {u w : V} {P : Set E} {S : Set V} (h : IsSDPath G u w P S) :
    IsSDP G u w S P := by
  obtain ⟨k, v, e, hp, rfl, rfl, rfl, rfl⟩ := h
  exact hp.isSDP

/-- A semidirected path whose steps all follow the directions is a directed path. -/
theorem IsSDP.isDPath_of_forall (hd : ∀ e, G.IsDirected e) {u w : V} {S : Set V} {P : Set E}
    (h : IsSDP G u w S P) : IsDPath G.graph u w S P := by
  induction h with
  | nil u => exact .nil u
  | @cons e a b w S P hs _ _ ih =>
    rcases hs with ⟨rfl, rfl⟩ | ⟨hnd, -⟩
    · exact .cons e ih
    · exact absurd (hd e) hnd

/-- A directed path from a node to itself is trivial, in an acyclic graph. -/
theorem IsDPath.eq_nil {H : DirectedMultigraph V E} (hA : H.IsAcyclic) {u : V} {S : Set V}
    {P : Set E} (h : IsDPath H u u S P) : S = {u} ∧ P = ∅ := by
  have hS : S = {u} := by
    ext s
    constructor
    · intro hs
      exact reaches_antisymm hA (h.reaches_of_mem hs).2 (h.reaches_of_mem hs).1
    · rintro rfl
      exact h.start_mem
  refine ⟨hS, Set.eq_empty_of_forall_notMem fun e he => ?_⟩
  have h₁ := (h.ends_mem he).1
  have h₂ := (h.ends_mem he).2
  rw [hS] at h₁ h₂
  exact not_reaches_target_source' hA e
    (by rw [Set.mem_singleton_iff.mp h₁, Set.mem_singleton_iff.mp h₂]; exact .refl)

/-- A nontrivial directed path has a last edge. -/
theorem IsDPath.exists_last {H : DirectedMultigraph V E} {u w : V} {S : Set V} {P : Set E}
    (h : IsDPath H u w S P) (hne : u ≠ w) : ∃ e ∈ P, H.target e = w ∧ H.source e ∈ S := by
  induction h with
  | nil u => exact absurd rfl hne
  | @cons e w S P h ih =>
    by_cases ht : H.target e = w
    · exact ⟨e, Set.mem_insert _ _, ht, Set.mem_insert _ _⟩
    · obtain ⟨e', he', h₁, h₂⟩ := ih ht
      exact ⟨e', Set.mem_insert_of_mem _ he', h₁, Set.mem_insert_of_mem _ h₂⟩

/-- A nontrivial directed path has a first edge. -/
theorem IsDPath.exists_first {H : DirectedMultigraph V E} {u w : V} {S : Set V} {P : Set E}
    (h : IsDPath H u w S P) (hne : P.Nonempty) : ∃ e ∈ P, H.source e = u := by
  cases h with
  | nil => exact absurd hne Set.not_nonempty_empty
  | cons e _ => exact ⟨e, Set.mem_insert _ _, rfl⟩

/-- A node of a directed path other than its start is entered by an edge of the path. -/
theorem IsDPath.eq_or_target {H : DirectedMultigraph V E} {u w : V} {S : Set V} {P : Set E}
    (h : IsDPath H u w S P) {s : V} (hs : s ∈ S) : s = u ∨ ∃ e ∈ P, H.target e = s := by
  induction h with
  | nil u => exact Or.inl hs
  | @cons e w S P h ih =>
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact Or.inl rfl
    · rcases ih hs with rfl | ⟨e', he', h'⟩
      · exact Or.inr ⟨e, Set.mem_insert _ _, rfl⟩
      · exact Or.inr ⟨e', Set.mem_insert_of_mem _ he', h'⟩

/-- In an acyclic graph, an edge of a path leaving its start is its first edge. -/
theorem IsDPath.uncons {H : DirectedMultigraph V E} (hA : H.IsAcyclic) {u w : V} {S : Set V}
    {P : Set E} (h : IsDPath H u w S P) {e : E} (he : e ∈ P) (hs : H.source e = u) :
    ∃ S' P', IsDPath H (H.target e) w S' P' ∧ S = insert u S' ∧ P = insert e P' ∧ u ∉ S' := by
  cases h with
  | nil => exact absurd he (Set.notMem_empty e)
  | @cons e₀ _ S' P' h' =>
    have hu : H.source e₀ ∉ S' := fun hm => not_reaches_target_source' hA e₀ (h'.reaches_of_mem hm).1
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact ⟨S', P', h', rfl, rfl, hu⟩
    · exact absurd (hs ▸ (h'.ends_mem he).1) hu

/-- **The pullback of a directed path** along injective maps of nodes and edges that keep the ends
of the edges of the path. -/
theorem IsDPath.pullback {V' E' : Type*} {H : DirectedMultigraph V E} {H' : DirectedMultigraph V' E'}
    (fv : V' → V) (fe : E' → E) (hfv : Function.Injective fv) (hfe : Function.Injective fe)
    {u w : V} {S : Set V} {P : Set E} (h : IsDPath H u w S P)
    (hP : ∀ e ∈ P, ∃ e', fe e' = e ∧ H.source e = fv (H'.source e') ∧
      H.target e = fv (H'.target e'))
    {u' w' : V'} (hu : fv u' = u) (hw : fv w' = w) :
    IsDPath H' u' w' (fv ⁻¹' S) (fe ⁻¹' P) := by
  induction h generalizing u' with
  | nil u =>
    have : u' = w' := hfv (hu.trans hw.symm)
    subst this
    have h₁ : fv ⁻¹' {u} = {u'} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => hfv (h.trans hu.symm), fun h => h ▸ hu⟩
    rw [h₁, Set.preimage_empty]
    exact .nil u'
  | @cons e w S P h ih =>
    obtain ⟨e', rfl, hs, ht⟩ := hP e (Set.mem_insert _ _)
    have hu' : H'.source e' = u' := hfv (hs.symm.trans hu.symm)
    subst hu'
    have := IsDPath.cons e' (ih (fun f hf => hP f (Set.mem_insert_of_mem _ hf)) ht.symm hw)
    convert this using 1
    · ext x
      simp only [Set.mem_preimage, Set.mem_insert_iff]
      rw [hs]
      exact or_congr_left hfv.eq_iff
    · ext x
      simp only [Set.mem_preimage, Set.mem_insert_iff]
      exact or_congr_left hfe.eq_iff

/-- **The shape of a semidirected path**, when two edges entering a node are hybrid: it goes against
the direction of tree edges from its start up to a node `t`, then follows the directions. The first
part is given as a directed path from `t` to the start. -/
theorem IsSDP.shape (hA : G.graph.IsAcyclic)
    (hH : ∀ g g', g ≠ g' → G.graph.target g = G.graph.target g' → G.IsDirected g)
    {a w : V} {S : Set V} {P : Set E} (h : IsSDP G a w S P) :
    ∃ t S₁ P₁ S₂ P₂, IsDPath G.graph t a S₁ P₁ ∧ (∀ e ∈ P₁, ¬ G.IsDirected e) ∧
      IsDPath G.graph t w S₂ P₂ ∧ S = S₁ ∪ S₂ ∧ P = P₁ ∪ P₂ ∧ S₁ ∩ S₂ = {t} := by
  induction h with
  | nil u => exact ⟨u, {u}, ∅, {u}, ∅, .nil u, fun _ h => absurd h (Set.notMem_empty _), .nil u,
      by simp, by simp, by simp⟩
  | @cons e a b w S P hs ha h ih =>
    obtain ⟨t, S₁, P₁, S₂, P₂, h₁, hu, h₂, rfl, rfl, hS⟩ := ih
    rcases hs with ⟨hsa, htb⟩ | ⟨hnd, hta, hsb⟩
    · -- a step along the direction: the path from `b` follows the directions
      have htb' : t = b := by
        by_contra hne
        obtain ⟨g, hg, hgt, hgs⟩ := h₁.exists_last hne
        have hge : g ≠ e := fun h' => ha (Or.inl (hsa ▸ h' ▸ hgs))
        exact hu g hg (hH g e hge (hgt.trans htb.symm))
      subst htb'
      obtain ⟨rfl, rfl⟩ := h₁.eq_nil hA
      refine ⟨a, {a}, ∅, insert a S₂, insert e P₂, .nil a, fun _ h => absurd h (Set.notMem_empty _),
        ?_, ?_, ?_, ?_⟩
      · rw [← hsa]
        exact .cons e (htb ▸ h₂)
      · rw [Set.singleton_union, Set.singleton_union, Set.insert_eq_of_mem h₂.start_mem,
          Set.insert_eq_of_mem (Set.mem_insert a S₂)]
      · rw [Set.empty_union, Set.empty_union]
      · exact Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    · -- a step against the direction of a tree edge
      have hab : IsDPath G.graph b a {b, a} {e} := by
        have := IsDPath.cons (G := G.graph) e (.nil (G.graph.target e))
        rw [hsb, hta] at this
        simpa using this
      refine ⟨t, S₁ ∪ {b, a}, P₁ ∪ {e}, S₂, P₂, h₁.append hab, ?_, h₂, ?_, ?_, ?_⟩
      · rintro g (hg | hg)
        · exact hu g hg
        · rw [Set.mem_singleton_iff.mp hg]
          exact hnd
      · ext x
        simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
        have hb : b ∈ S₁ := h₁.end_mem
        constructor
        · rintro (rfl | h | h)
          · exact Or.inl (Or.inr (Or.inr rfl))
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rintro ((h | rfl | rfl) | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inl hb)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
      · ext x
        simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
        tauto
      · ext x
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h | rfl | rfl, h'⟩
          · exact (Set.ext_iff.mp hS x).mp ⟨h, h'⟩
          · exact (Set.ext_iff.mp hS x).mp ⟨h₁.end_mem, h'⟩
          · exact absurd (Or.inr h') ha
        · rintro rfl
          exact ⟨Or.inl ((Set.ext_iff.mp hS x).mpr rfl).1, ((Set.ext_iff.mp hS x).mpr rfl).2⟩

/-- **A simple trek of semidirected paths gives a simple trek of directed paths** with the same
edges, when two edges entering a node are hybrid. One of the two paths of the trek follows the
directions from the top: else they would enter the top by two tree edges. -/
theorem exists_dtrek_of_sdtrek (hA : G.graph.IsAcyclic)
    (hH : ∀ g g', g ≠ g' → G.graph.target g = G.graph.target g' → G.IsDirected g)
    {v x y : V} {S₁ S₂ : Set V} {P₁ P₂ : Set E} (h₁ : IsSDP G v x S₁ P₁) (h₂ : IsSDP G v y S₂ P₂)
    (hS : S₁ ∩ S₂ = {v}) :
    ∃ t Sa Pa Sb Pb, IsDPath G.graph t x Sa Pa ∧ IsDPath G.graph t y Sb Pb ∧ Sa ∩ Sb = {t} ∧
      P₁ ∪ P₂ ⊆ Pa ∪ Pb ∧ Sa ∪ Sb ⊆ S₁ ∪ S₂ := by
  obtain ⟨t₁, B₁, Q₁, F₁, R₁, hB₁, hu₁, hF₁, rfl, rfl, hS₁⟩ := h₁.shape hA hH
  obtain ⟨t₂, B₂, Q₂, F₂, R₂, hB₂, hu₂, hF₂, rfl, rfl, hS₂⟩ := h₂.shape hA hH
  -- the case where the second path follows the directions
  have key : ∀ {x y : V} {B₁ F₁ B₂ F₂ : Set V} {Q₁ R₁ Q₂ R₂ : Set E} {t₁ : V},
      IsDPath G.graph t₁ v B₁ Q₁ → IsDPath G.graph t₁ x F₁ R₁ → B₁ ∩ F₁ = {t₁} →
      IsDPath G.graph v v B₂ Q₂ → IsDPath G.graph v y F₂ R₂ →
      (B₁ ∪ F₁) ∩ (B₂ ∪ F₂) = {v} →
      ∃ t Sa Pa Sb Pb, IsDPath G.graph t x Sa Pa ∧ IsDPath G.graph t y Sb Pb ∧ Sa ∩ Sb = {t} ∧
        (Q₁ ∪ R₁) ∪ (Q₂ ∪ R₂) ⊆ Pa ∪ Pb ∧ Sa ∪ Sb ⊆ (B₁ ∪ F₁) ∪ (B₂ ∪ F₂) := by
    intro x y B₁ F₁ B₂ F₂ Q₁ R₁ Q₂ R₂ t₁ hB₁ hF₁ hS₁ hB₂ hF₂ hS
    obtain ⟨rfl, rfl⟩ := hB₂.eq_nil hA
    refine ⟨t₁, F₁, R₁, B₁ ∪ F₂, Q₁ ∪ R₂, hF₁, hB₁.append hF₂, ?_, ?_, ?_⟩
    · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hF₁.start_mem, Or.inl hB₁.start_mem⟩, ?_⟩
      rintro s ⟨hs₁, hs | hs⟩
      · exact (Set.eq_singleton_iff_unique_mem.mp hS₁).2 s ⟨hs, hs₁⟩
      · have hv : s = v := (Set.eq_singleton_iff_unique_mem.mp hS).2 s ⟨Or.inr hs₁, Or.inr hs⟩
        subst hv
        exact (Set.eq_singleton_iff_unique_mem.mp hS₁).2 _ ⟨hB₁.end_mem, hs₁⟩
    · rintro g ((hg | hg) | (hg | hg))
      · exact Or.inr (Or.inl hg)
      · exact Or.inl hg
      · exact absurd hg (Set.notMem_empty _)
      · exact Or.inr (Or.inr hg)
    · rintro s (hs | hs | hs)
      · exact Or.inl (Or.inr hs)
      · exact Or.inl (Or.inl hs)
      · exact Or.inr (Or.inr hs)
  -- one of the two paths follows the directions from the top
  have hjunction : t₁ = v ∨ t₂ = v := by
    by_contra hne
    push Not at hne
    obtain ⟨g₁, hg₁, hgt₁, hgs₁⟩ := hB₁.exists_last hne.1
    obtain ⟨g₂, hg₂, hgt₂, hgs₂⟩ := hB₂.exists_last hne.2
    have hne' : g₁ ≠ g₂ := by
      rintro rfl
      have : G.graph.source g₁ = v := (Set.eq_singleton_iff_unique_mem.mp hS).2 _
        ⟨Or.inl hgs₁, Or.inl hgs₂⟩
      exact not_reaches_target_source' hA g₁ (by rw [this, hgt₁]; exact .refl)
    exact hu₁ g₁ hg₁ (hH g₁ g₂ hne' (hgt₁.trans hgt₂.symm))
  rcases hjunction with rfl | rfl
  · obtain ⟨t, Sa, Pa, Sb, Pb, ha, hb, hab, hP, hS'⟩ :=
      key hB₂ hF₂ hS₂ hB₁ hF₁ (by rw [Set.inter_comm]; exact hS)
    refine ⟨t, Sb, Pb, Sa, Pa, hb, ha, by rw [Set.inter_comm, hab], ?_, ?_⟩
    · rw [Set.union_comm Pb, Set.union_comm (Q₁ ∪ R₁)]
      exact hP
    · rw [Set.union_comm Sb, Set.union_comm (B₁ ∪ F₁)]
      exact hS'
  · exact key hB₁ hF₁ hS₁ hB₂ hF₂ hS

end SDP

end Banos2019
