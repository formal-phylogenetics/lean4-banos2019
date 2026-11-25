module

public import Banos2019.Network.DirectedPath

/-!
# A simple trek through an arc (the argument of Lemma 17)

The case analysis of the proof of Lemma 17 (Appendix, `lem::trekmrca`), on a finite acyclic graph
whose reachability is the partial order `≤`. An arc `e` lies on a path `Px` from `m` to `a`; a path
`Py` from `m` to `b` avoids the child of `e`. When every node strictly below `m` is avoided by a path
from `m` to `a` or to `b`, as when `m` is the LSA of two taxa `a` and `b`, there is a simple trek
through `e` from `a` to `b`, with its nodes below `m` (`trek_of_config`).

The paper's notation: `A` and `B` are the nodes common to `Px` and `Py` above and below `e`, with `a`
the lowest node of `A` and `b⁻`, `b⁺` (`bm`, `bp`) the lowest and highest nodes of `B`; `P*` is a path
from `m` to `a` or `b` avoiding `b⁻`, `c` the first node of `P*` below `b⁻` on `Px` or `Py`, and `w`
the last node of `P*` above `b⁻` on `Px` or `Py`. The induction on `|B|` replaces the paper's choice of
`Px` and `Py` with `|B|` minimal.

* `HasTrekThrough`: the conclusion.
* `trek_of_not_below`: the case where the child of `e` is not above `b`.
* `trek_mainStep`: the five cases on the position of `w`.
* `trek_of_config`: the induction on `|B|`.
-/

@[expose] public noncomputable section

open Phylogenetics

namespace Banos2019

variable {V E X : Type*}

section Trek

variable (G : DirectedMultigraph V E)

/-- A simple trek through the arc `e`: directed paths from a top `t` to `a` and to `b` with only `t`
in common, one of them through `e`, all of whose nodes are below `m`. -/
def HasTrekThrough (m a b : V) (e : E) : Prop :=
  ∃ t S₁ P₁ S₂ P₂, IsDPath G t a S₁ P₁ ∧ IsDPath G t b S₂ P₂ ∧ S₁ ∩ S₂ = {t} ∧ e ∈ P₁ ∪ P₂ ∧
    ∀ s ∈ S₁ ∪ S₂, G.Reaches m s

variable {G}

theorem HasTrekThrough.symm {m a b : V} {e : E} (h : HasTrekThrough G m a b e) :
    HasTrekThrough G m b a e := by
  obtain ⟨t, S₁, P₁, S₂, P₂, h₁, h₂, hS, he, hm⟩ := h
  refine ⟨t, S₂, P₂, S₁, P₁, h₂, h₁, by rw [Set.inter_comm, hS], ?_, fun s hs => hm s ?_⟩
  · rw [Set.union_comm]
    exact he
  · rw [Set.union_comm]
    exact hs

variable [PartialOrder V]

/-- A part of a path, in the reachability order. -/
theorem IsDPath.segment_le (hle : ∀ a b, G.Reaches a b ↔ a ≤ b) (hA : G.IsAcyclic) {u w : V} {S : Set V}
    {P : Set E} (h : IsDPath G u w S P) {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≤ b) :
    ∃ P', IsDPath G a b {s | s ∈ S ∧ a ≤ s ∧ s ≤ b} P' ∧ P' ⊆ P ∧
      ∀ e ∈ P, a ≤ G.source e → G.target e ≤ b → e ∈ P' := by
  obtain ⟨P', h', hsub, hP⟩ := h.segment hA ha hb ((hle a b).mpr hab)
  refine ⟨P', ?_, hsub, fun e he h₁ h₂ => hP e he ((hle _ _).mpr h₁) ((hle _ _).mpr h₂)⟩
  simpa only [hle] using h'

/-- A trek whose nodes are on three paths from `m` has its nodes below `m`. -/
theorem hasTrekThrough_of_subset (hle : ∀ a b, G.Reaches a b ↔ a ≤ b) {m a b t : V} {e : E}
    {Sx Sy Ss S₁ S₂ : Set V} {P₁ P₂ : Set E} (hx : ∀ s ∈ Sx, m ≤ s) (hy : ∀ s ∈ Sy, m ≤ s)
    (hs : ∀ s ∈ Ss, m ≤ s) (h₁ : IsDPath G t a S₁ P₁) (h₂ : IsDPath G t b S₂ P₂)
    (hS : S₁ ∩ S₂ = {t}) (he : e ∈ P₁ ∪ P₂) (hsub : ∀ s ∈ S₁ ∪ S₂, s ∈ Sx ∨ s ∈ Sy ∨ s ∈ Ss) :
    HasTrekThrough G m a b e := by
  refine ⟨t, S₁, P₁, S₂, P₂, h₁, h₂, hS, he, fun s h => (hle _ _).mpr ?_⟩
  rcases hsub s h with h | h | h
  · exact hx s h
  · exact hy s h
  · exact hs s h

variable [Finite V]

/-- **Lemma 17, the case where `b` is not below `e`**: the lowest node `u` common to the two paths is
above `e`, and the parts of the paths from `u` form the trek. -/
theorem trek_of_not_below (hle : ∀ a b, G.Reaches a b ↔ a ≤ b) (hA : G.IsAcyclic)
    {m X₀ Y₀ : V} {e : E} {Sx Sy : Set V} {Px Py : Set E} (hPx : IsDPath G m X₀ Sx Px)
    (he : e ∈ Px) (hPy : IsDPath G m Y₀ Sy Py) (hY : ¬ G.target e ≤ Y₀) :
    HasTrekThrough G m X₀ Y₀ e := by
  have mx : ∀ s ∈ Sx, m ≤ s ∧ s ≤ X₀ := fun s hs =>
    ⟨(hle _ _).mp (hPx.reaches_of_mem hs).1, (hle _ _).mp (hPx.reaches_of_mem hs).2⟩
  have my : ∀ s ∈ Sy, m ≤ s ∧ s ≤ Y₀ := fun s hs =>
    ⟨(hle _ _).mp (hPy.reaches_of_mem hs).1, (hle _ _).mp (hPy.reaches_of_mem hs).2⟩
  obtain ⟨u, ⟨hux, huy⟩, hu⟩ := Set.Finite.exists_greatest_of_total (T := Sx ∩ Sy) (Set.toFinite _)
    ⟨m, hPx.start_mem, hPy.start_mem⟩ fun s hs t ht =>
      (hPx.total hs.1 ht.1).imp (hle _ _).mp (hle _ _).mp
  have hus : u ≤ G.source e := by
    rcases hPx.mem_or he hux with h | h
    · exact (hle _ _).mp h
    · exact absurd (((hle _ _).mp h).trans (my u huy).2) hY
  obtain ⟨P₁, hP₁, -, hP₁e⟩ := IsDPath.segment_le hle hA hPx hux hPx.end_mem (mx u hux).2
  obtain ⟨P₂, hP₂, -, -⟩ := IsDPath.segment_le hle hA hPy huy hPy.end_mem (my u huy).2
  refine hasTrekThrough_of_subset hle (fun s hs => (mx s hs).1) (fun s hs => (my s hs).1)
    (Ss := ∅) (fun _ h => absurd h (Set.notMem_empty _)) hP₁ hP₂ ?_
    (Or.inl (hP₁e e he hus (mx _ (hPx.ends_mem he).2).2)) ?_
  · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨hux, le_rfl, (mx u hux).2⟩, huy, le_rfl,
      (my u huy).2⟩, ?_⟩
    rintro s ⟨⟨hsx, hus', -⟩, hsy, -, -⟩
    exact le_antisymm (hu s ⟨hsx, hsy⟩) hus'
  · rintro s (⟨h, -⟩ | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **Lemma 17, the five cases on the position of `w`** (Figures 25–27). `Px` passes through `e`, `Py`
avoids its child, `bm` (`b⁻`) is the lowest node of `B`, `P*` avoids `bm`, and `c` is the first node of
`P*` strictly below `bm` on `Px` or `Py`; it is on `Py`. The last node `w` of `P*` above `bm` on `Px`
or `Py` is in one of five places: on `Py` between `a` and `b⁺` (case 1); on `Px` below `e` and above
`b⁺` (case 2); on `Px` above `e`, below `a` (case 3) or above `a` (case 4); between `b⁺` and `bm`
(case 5). In cases 1–4 the trek is built directly; in case 5 two new paths have fewer common nodes
below `e`, and `IH` applies.

The paper excludes `w = a` and `w = b⁺` since the network is binary; the constructions of cases 3
and 5 apply to them, and the case split below includes them there. Case 4 on `Px` is built as case 3,
and case 4 on `Py` as case 1, with `a` replaced by the node of `A` right above `w`. In case 5 the
paper takes `w` on `Px` without loss of generality when `w` is on one path only; the case `w` on
`Py` only is not symmetric to it, but the construction of case 5 (i) applies to it unchanged. -/
theorem trek_mainStep (hle : ∀ a b, G.Reaches a b ↔ a ≤ b) (hA : G.IsAcyclic)
    {m X₀ Y₀ Z₀ : V} {e : E} {Sx Sy Ss : Set V} {Px Py Ps : Set E}
    (hPx : IsDPath G m X₀ Sx Px) (he : e ∈ Px) (hPy : IsDPath G m Y₀ Sy Py)
    (hey : G.target e ∉ Sy) {bm : V} (hbmx : bm ∈ Sx) (hbmy : bm ∈ Sy) (hbm : G.target e ≤ bm)
    (hbm_low : ∀ v ∈ Sx, v ∈ Sy → G.target e ≤ v → v ≤ bm)
    (hPs : IsDPath G m Z₀ Ss Ps) (hbs : bm ∉ Ss) {c : V} (hcs : c ∈ Ss) (hcy : c ∈ Sy)
    (hcx : c ∉ Sx) (hbc : bm ≤ c) (hcb : c ≠ bm)
    (hc_high : ∀ v ∈ Ss, v ∈ Sx ∨ v ∈ Sy → bm ≤ v → v ≠ bm → c ≤ v)
    (IH : ∀ Sx' Px' Sy' Py', IsDPath G m X₀ Sx' Px' → e ∈ Px' → IsDPath G m Y₀ Sy' Py' →
      G.target e ∉ Sy' →
      (Sx' ∩ Sy' ∩ {v | G.target e ≤ v}).ncard < (Sx ∩ Sy ∩ {v | G.target e ≤ v}).ncard →
      HasTrekThrough G m X₀ Y₀ e) :
    HasTrekThrough G m X₀ Y₀ e := by
  classical
  -- the order along the three paths
  have hst : G.source e ≤ G.target e := (hle _ _).mp (.single ⟨e, rfl, rfl⟩)
  have hts : ¬ G.target e ≤ G.source e := fun h =>
    not_reaches_target_source_of_isAcyclic hA e ((hle _ _).mpr h)
  have mx : ∀ s ∈ Sx, m ≤ s ∧ s ≤ X₀ := fun s hs =>
    ⟨(hle _ _).mp (hPx.reaches_of_mem hs).1, (hle _ _).mp (hPx.reaches_of_mem hs).2⟩
  have my : ∀ s ∈ Sy, m ≤ s ∧ s ≤ Y₀ := fun s hs =>
    ⟨(hle _ _).mp (hPy.reaches_of_mem hs).1, (hle _ _).mp (hPy.reaches_of_mem hs).2⟩
  have ms : ∀ s ∈ Ss, m ≤ s := fun s hs => (hle _ _).mp (hPs.reaches_of_mem hs).1
  have tx : ∀ s ∈ Sx, ∀ t ∈ Sx, s ≤ t ∨ t ≤ s := fun s hs t ht =>
    (hPx.total hs ht).imp (hle _ _).mp (hle _ _).mp
  have ty : ∀ s ∈ Sy, ∀ t ∈ Sy, s ≤ t ∨ t ≤ s := fun s hs t ht =>
    (hPy.total hs ht).imp (hle _ _).mp (hle _ _).mp
  have ts : ∀ s ∈ Ss, ∀ t ∈ Ss, s ≤ t ∨ t ≤ s := fun s hs t ht =>
    (hPs.total hs ht).imp (hle _ _).mp (hle _ _).mp
  have dx : ∀ s ∈ Sx, s ≤ G.source e ∨ G.target e ≤ s := fun s hs =>
    (hPx.mem_or he hs).imp (hle _ _).mp (hle _ _).mp
  have hsrcx : G.source e ∈ Sx := (hPx.ends_mem he).1
  have htgtx : G.target e ∈ Sx := (hPx.ends_mem he).2
  have hmx : m ∈ Sx := hPx.start_mem
  have hmy : m ∈ Sy := hPy.start_mem
  have hmb : m ≠ bm := fun h => hts (h ▸ hbm |>.trans (mx _ hsrcx).1)
  -- `a`, the lowest node of `A`
  obtain ⟨a, ⟨hax, hay, has⟩, ha_low⟩ := Set.Finite.exists_greatest_of_total
    (T := {v | v ∈ Sx ∧ v ∈ Sy ∧ v ≤ G.source e}) (Set.toFinite _)
    ⟨m, hmx, hmy, (mx _ hsrcx).1⟩ fun s hs t ht => tx s hs.1 t ht.1
  -- `b⁺`, the highest node of `B`
  obtain ⟨bp, ⟨hbpx, hbpy, hbp⟩, hbp_high⟩ := Set.Finite.exists_least_of_total
    (T := {v | v ∈ Sx ∧ v ∈ Sy ∧ G.target e ≤ v}) (Set.toFinite _)
    ⟨bm, hbmx, hbmy, hbm⟩ fun s hs t ht => tx s hs.1 t ht.1
  -- `w`, the last node of `P*` above `b⁻` on `Px` or `Py`
  obtain ⟨w, ⟨hws, hwxy, hwb, hwb'⟩, hw_low⟩ := Set.Finite.exists_greatest_of_total
    (T := {v | v ∈ Ss ∧ (v ∈ Sx ∨ v ∈ Sy) ∧ v ≤ bm ∧ v ≠ bm}) (Set.toFinite _)
    ⟨m, hPs.start_mem, Or.inl hmx, (mx _ hbmx).1, hmb⟩ fun s hs t ht => ts s hs.1 t ht.1
  have hwc : w ≤ c := hwb.trans hbc
  obtain ⟨Pwc, hPwc, -, -⟩ := IsDPath.segment_le hle hA hPs hws hcs hwc
  -- the inner nodes of `P*` from `w` to `c` are on neither `Px` nor `Py`
  have inner : ∀ s ∈ {s | s ∈ Ss ∧ w ≤ s ∧ s ≤ c}, s ∈ Sx ∨ s ∈ Sy → s = w ∨ s = c := by
    rintro s ⟨hss, hws', hsc⟩ hsxy
    have hsb : s ≠ bm := fun h => hbs (h ▸ hss)
    have hcomp : s ≤ bm ∨ bm ≤ s :=
      hsxy.elim (fun h => tx s h bm hbmx) (fun h => ty s h bm hbmy)
    rcases hcomp with h | h
    · exact Or.inl (le_antisymm (hw_low s ⟨hss, hsxy, h, hsb⟩) hws')
    · exact Or.inr (le_antisymm hsc (hc_high s hss hsxy h hsb))
  obtain ⟨Pcy, hPcy, -, -⟩ := IsDPath.segment_le hle hA hPy hcy hPy.end_mem (my c hcy).2
  have hbm_le_c : ∀ v, c ≤ v → G.target e ≤ v := fun v h => hbm.trans (hbc.trans h)
  by_cases hI : w ∈ Sx ∧ w ≤ G.source e
  · -- cases 3 and 4 with `w` on `Px`: the trek with top `w`
    obtain ⟨hwx, hwsrc⟩ := hI
    obtain ⟨P₁, hP₁, -, hP₁e⟩ := IsDPath.segment_le hle hA hPx hwx hPx.end_mem (mx w hwx).2
    refine hasTrekThrough_of_subset hle (fun s hs => (mx s hs).1) (fun s hs => (my s hs).1) ms hP₁
      (hPwc.append hPcy) ?_ (Or.inl (hP₁e e he hwsrc (mx _ htgtx).2)) ?_
    · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨hwx, le_rfl, (mx w hwx).2⟩,
        Or.inl ⟨hws, le_rfl, hwc⟩⟩, ?_⟩
      rintro s ⟨⟨hsx, -, -⟩, hs | ⟨hsy, hcs', -⟩⟩
      · rcases inner s hs (Or.inl hsx) with h | h
        · exact h
        · exact absurd (h ▸ hsx) hcx
      · have := hbm_low s hsx hsy (hbm_le_c s hcs')
        exact absurd (by order) hcb
    · rintro s ((⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩))
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  by_cases hV : w ∈ Sy ∧ bp ≤ w
  · -- case 5 with `w` on `Py`: replace `Py` by `Py` to `w`, `P*` to `c`, `Py` from `c`
    obtain ⟨hwy, hbpw⟩ := hV
    obtain ⟨Q, hQ, -, -⟩ := IsDPath.segment_le hle hA hPy hmy hwy (my w hwy).1
    refine IH _ _ _ _ hPx he (hQ.append (hPwc.append hPcy)) ?_ ?_
    · rintro (⟨h, -⟩ | h | ⟨h, -⟩)
      · exact hey h
      · rcases inner _ h (Or.inl htgtx) with h' | h'
        · exact hey (h' ▸ hwy)
        · exact hcx (h' ▸ htgtx)
      · exact hey h
    · have hsub : Sx ∩ ({s | s ∈ Sy ∧ m ≤ s ∧ s ≤ w} ∪ ({s | s ∈ Ss ∧ w ≤ s ∧ s ≤ c} ∪
          {s | s ∈ Sy ∧ c ≤ s ∧ s ≤ Y₀})) ∩ {v | G.target e ≤ v} ⊆
          {v | (v ∈ Sx ∧ v ∈ Sy ∧ G.target e ≤ v) ∧ v ≤ w} := by
        rintro v ⟨⟨hvx, ⟨hvy, -, hvw⟩ | hvs | ⟨hvy, hcv, -⟩⟩, htv⟩
        · exact ⟨⟨hvx, hvy, htv⟩, hvw⟩
        · rcases inner v hvs (Or.inl hvx) with h | h
          · exact ⟨⟨hvx, h ▸ hwy, htv⟩, h.le⟩
          · exact absurd (h ▸ hvx) hcx
        · have := hbm_low v hvx hvy htv
          exact absurd (by order) hcb
      refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
      refine (Set.ssubset_iff_of_subset fun v hv => ?_).mpr ⟨bm, ⟨⟨hbmx, hbmy⟩, hbm⟩, fun h => ?_⟩
      · obtain ⟨⟨hvx, hvy, htv⟩, -⟩ := hsub hv
        exact ⟨⟨hvx, hvy⟩, htv⟩
      · have := (hsub h).2
        exact hwb' (by order)
  rcases hwxy with hwx | hwy
  · have htw : G.target e ≤ w := (dx w hwx).resolve_left fun h => hI ⟨hwx, h⟩
    have hwy : w ∉ Sy := fun hwy => hV ⟨hwy, hbp_high w ⟨hwx, hwy, htw⟩⟩
    rcases tx w hwx bp hbpx with hwbp | hbpw
    · -- case 2: the trek with top `a`, one path through `e` to `w`, `P*` to `c` and `Py` to `b`
      have haw : a ≤ w := has.trans (hst.trans htw)
      have habm : a ≤ bm := has.trans (hst.trans hbm)
      obtain ⟨Q₁, hQ₁, -, -⟩ := IsDPath.segment_le hle hA hPy hay hbmy habm
      obtain ⟨Q₂, hQ₂, -, -⟩ := IsDPath.segment_le hle hA hPx hbmx hPx.end_mem (mx bm hbmx).2
      obtain ⟨Q₃, hQ₃, -, hQ₃e⟩ := IsDPath.segment_le hle hA hPx hax hwx haw
      refine hasTrekThrough_of_subset hle (fun s hs => (mx s hs).1) (fun s hs => (my s hs).1) ms
        (hQ₁.append hQ₂) (hQ₃.append (hPwc.append hPcy)) ?_
        (Or.inr (Or.inl (hQ₃e e he has htw))) ?_
      · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨Or.inl ⟨hay, le_rfl, habm⟩,
          Or.inl ⟨hax, le_rfl, haw⟩⟩, ?_⟩
        rintro s ⟨⟨hsy, has', hsbm⟩ | ⟨hsx, hbms, -⟩, ⟨hsx', -, hsw⟩ | hs | ⟨hsy', hcs, -⟩⟩
        · rcases dx s hsx' with h | h
          · exact le_antisymm (ha_low s ⟨hsx', hsy, h⟩) has'
          · have := hbp_high s ⟨hsx', hsy, h⟩
            have hsw' : s = w := by order
            exact absurd (hsw' ▸ hsy) hwy
        · rcases inner s hs (Or.inr hsy) with h | h
          · exact absurd (h ▸ hsy) hwy
          · exact absurd (by order) hcb
        · exact absurd (by order) hcb
        · exact absurd (by order) hwb'
        · rcases inner s hs (Or.inl hsx) with h | h
          · exact absurd (by order) hwb'
          · exact absurd (h ▸ hsx) hcx
        · have := hbm_low s hsx hsy' (hbm.trans hbms)
          exact absurd (by order) hcb
      · rintro s ((⟨h, -⟩ | ⟨h, -⟩) | (⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩)))
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
    · -- case 5 with `w` on `Px` only: exchange the parts of `Px` and `Py` between `b` and `b'`
      obtain ⟨b, ⟨⟨hbx, hby, hbt⟩, hbw⟩, hb_low⟩ := Set.Finite.exists_greatest_of_total
        (T := {v | (v ∈ Sx ∧ v ∈ Sy ∧ G.target e ≤ v) ∧ v ≤ w}) (Set.toFinite _)
        ⟨bp, ⟨hbpx, hbpy, hbp⟩, hbpw⟩ fun s hs t ht => tx s hs.1.1 t ht.1.1
      obtain ⟨b', ⟨⟨hb'x, hb'y, hb't⟩, hwb''⟩, -⟩ := Set.Finite.exists_least_of_total
        (T := {v | (v ∈ Sx ∧ v ∈ Sy ∧ G.target e ≤ v) ∧ w ≤ v}) (Set.toFinite _)
        ⟨bm, ⟨hbmx, hbmy, hbm⟩, hwb⟩ fun s hs t ht => tx s hs.1.1 t ht.1.1
      have hb'bm : b' ≤ bm := hbm_low b' hb'x hb'y hb't
      obtain ⟨R₁, hR₁, -, hR₁e⟩ := IsDPath.segment_le hle hA hPx hmx hbx (mx b hbx).1
      obtain ⟨R₂, hR₂, -, -⟩ := IsDPath.segment_le hle hA hPy hby hb'y (hbw.trans hwb'')
      obtain ⟨R₃, hR₃, -, -⟩ := IsDPath.segment_le hle hA hPx hb'x hPx.end_mem (mx b' hb'x).2
      obtain ⟨R₄, hR₄, -, -⟩ := IsDPath.segment_le hle hA hPy hmy hby (my b hby).1
      obtain ⟨R₅, hR₅, -, -⟩ := IsDPath.segment_le hle hA hPx hbx hwx hbw
      refine IH _ _ _ _ (hR₁.append (hR₂.append hR₃)) (Or.inl (hR₁e e he (mx _ hsrcx).1 hbt))
        (hR₄.append (hR₅.append (hPwc.append hPcy))) ?_ ?_
      · rintro (⟨h, -⟩ | ⟨-, hbt', -⟩ | h | ⟨h, -⟩)
        · exact hey h
        · have : G.target e = b := le_antisymm hbt hbt'
          exact hey (this ▸ hby)
        · rcases inner _ h (Or.inl htgtx) with h' | h'
          · have : b = w := by order
            exact hwy (this ▸ hby)
          · exact hcx (h' ▸ htgtx)
        · exact hey h
      · have hsub : ∀ v, v ∈ {s | s ∈ Sx ∧ m ≤ s ∧ s ≤ b} ∪ ({s | s ∈ Sy ∧ b ≤ s ∧ s ≤ b'} ∪
            {s | s ∈ Sx ∧ b' ≤ s ∧ s ≤ X₀}) → v ∈ {s | s ∈ Sy ∧ m ≤ s ∧ s ≤ b} ∪
            ({s | s ∈ Sx ∧ b ≤ s ∧ s ≤ w} ∪ ({s | s ∈ Ss ∧ w ≤ s ∧ s ≤ c} ∪
              {s | s ∈ Sy ∧ c ≤ s ∧ s ≤ Y₀})) → G.target e ≤ v → v ∈ Sx ∧ v ∈ Sy ∧ v ≤ b := by
          rintro v (⟨hvx, -, hvb⟩ | ⟨hvy, hbv, hvb'⟩ | ⟨hvx, hb'v, -⟩)
            (⟨hvy', -, hvb2⟩ | ⟨hvx', hbv2, hvw⟩ | hvs | ⟨hvy', hcv, -⟩) htv
          · exact ⟨hvx, hvy', hvb⟩
          · have : v = b := le_antisymm hvb hbv2
            exact ⟨hvx, this ▸ hby, hvb⟩
          · rcases inner v hvs (Or.inl hvx) with h | h
            · have : w = b := by order
              exact absurd (this ▸ hby) hwy
            · exact absurd (h ▸ hvx) hcx
          · exact absurd (by order) hcb
          · have : v = b := le_antisymm hvb2 hbv
            exact ⟨this ▸ hbx, hvy, hvb2⟩
          · exact ⟨hvx', hvy, hb_low v ⟨⟨hvx', hvy, htv⟩, hvw⟩⟩
          · rcases inner v hvs (Or.inr hvy) with h | h
            · exact absurd (h ▸ hvy) hwy
            · exact absurd (by order) hcb
          · exact absurd (by order) hcb
          · have : w = b' := by order
            exact absurd (this ▸ hb'y) hwy
          · have : w = b' := by order
            exact absurd (this ▸ hb'y) hwy
          · rcases inner v hvs (Or.inl hvx) with h | h
            · have : w = b' := by order
              exact absurd (this ▸ hb'y) hwy
            · exact absurd (h ▸ hvx) hcx
          · have := hbm_low v hvx hvy' htv
            exact absurd (by order) hcb
        refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
        refine (Set.ssubset_iff_of_subset fun v hv => ?_).mpr ⟨bm, ⟨⟨hbmx, hbmy⟩, hbm⟩,
          fun h => ?_⟩
        · obtain ⟨hvx, hvy, -⟩ := hsub v hv.1.1 hv.1.2 hv.2
          exact ⟨⟨hvx, hvy⟩, hv.2⟩
        · have := (hsub bm h.1.1 h.1.2 h.2).2.2
          exact hwb' (by order)
  · have hwx : w ∉ Sx := fun hwx => by
      rcases dx w hwx with h | h
      · exact hI ⟨hwx, h⟩
      · exact hV ⟨hwy, hbp_high w ⟨hwx, hwy, h⟩⟩
    have hwbp : w ≤ bp := (ty w hwy bp hbpy).resolve_right fun h => hV ⟨hwy, h⟩
    -- cases 1 and 4 with `w` on `Py`: the trek with top `a'`, the node of `A` right above `w`
    -- (in case 1, `a' = a`)
    obtain ⟨a', ⟨⟨ha'x, ha'y, ha's⟩, ha'w⟩, ha'_low⟩ := Set.Finite.exists_greatest_of_total
      (T := {v | (v ∈ Sx ∧ v ∈ Sy ∧ v ≤ G.source e) ∧ v ≤ w}) (Set.toFinite _)
      ⟨m, ⟨hmx, hmy, (mx _ hsrcx).1⟩, ms w hws⟩ fun s hs t ht => tx s hs.1.1 t ht.1.1
    obtain ⟨Q₁, hQ₁, -, hQ₁e⟩ := IsDPath.segment_le hle hA hPx ha'x hPx.end_mem (mx a' ha'x).2
    obtain ⟨Q₂, hQ₂, -, -⟩ := IsDPath.segment_le hle hA hPy ha'y hwy ha'w
    refine hasTrekThrough_of_subset hle (fun s hs => (mx s hs).1) (fun s hs => (my s hs).1) ms hQ₁
      (hQ₂.append (hPwc.append hPcy)) ?_ (Or.inl (hQ₁e e he ha's (mx _ htgtx).2)) ?_
    · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨ha'x, le_rfl, (mx a' ha'x).2⟩,
        Or.inl ⟨ha'y, le_rfl, ha'w⟩⟩, ?_⟩
      rintro s ⟨⟨hsx, ha's', -⟩, ⟨hsy, -, hsw⟩ | hs | ⟨hsy, hcs, -⟩⟩
      · rcases dx s hsx with h | h
        · exact le_antisymm (ha'_low s ⟨⟨hsx, hsy, h⟩, hsw⟩) ha's'
        · have := hbp_high s ⟨hsx, hsy, h⟩
          have hsw' : s = w := by order
          exact absurd (hsw' ▸ hsx) hwx
      · rcases inner s hs (Or.inl hsx) with h | h
        · exact absurd (h ▸ hsx) hwx
        · exact absurd (h ▸ hsx) hcx
      · have := hbm_low s hsx hsy (hbm_le_c s hcs)
        exact absurd (by order) hcb
    · rintro s (⟨h, -⟩ | (⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩)))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)

/-- **Lemma 17, case B**, by induction on the number of nodes common to `Px` and `Py` below `e`
(the paper chooses `Px` and `Py` with this number minimal). When there are none, the parts of the
paths from the lowest common node `a` above `e` form the trek. Otherwise `b⁻` is strictly below `m`,
so a path `P*` from `m` avoids it, and `c` is its first node strictly below `b⁻` on `Px` or `Py`; if
`c` is on `Px`, the parts of `Px` and `Py` below `b⁻` are exchanged, which exchanges `a` and `b`, so
that `c` is on the path avoiding the child of `e` (the paper's "without loss of generality"). Then
`trek_mainStep` applies. -/
theorem trek_of_config (hle : ∀ a b, G.Reaches a b ↔ a ≤ b) (hA : G.IsAcyclic) {m : V} {e : E}
    (n : ℕ) : ∀ (X₀ Y₀ : V) (Sx Sy : Set V) (Px Py : Set E),
      (∀ b, m ≤ b → b ≠ m → ∃ Z₀, (Z₀ = X₀ ∨ Z₀ = Y₀) ∧ ∃ S P, IsDPath G m Z₀ S P ∧ b ∉ S) →
      IsDPath G m X₀ Sx Px → e ∈ Px → IsDPath G m Y₀ Sy Py → G.target e ∉ Sy →
      (Sx ∩ Sy ∩ {v | G.target e ≤ v}).ncard = n → HasTrekThrough G m X₀ Y₀ e := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro X₀ Y₀ Sx Sy Px Py hm hPx he hPy hey hn
  have hst : G.source e ≤ G.target e := (hle _ _).mp (.single ⟨e, rfl, rfl⟩)
  have hts : ¬ G.target e ≤ G.source e := fun h =>
    not_reaches_target_source_of_isAcyclic hA e ((hle _ _).mpr h)
  have mx : ∀ s ∈ Sx, m ≤ s ∧ s ≤ X₀ := fun s hs =>
    ⟨(hle _ _).mp (hPx.reaches_of_mem hs).1, (hle _ _).mp (hPx.reaches_of_mem hs).2⟩
  have my : ∀ s ∈ Sy, m ≤ s ∧ s ≤ Y₀ := fun s hs =>
    ⟨(hle _ _).mp (hPy.reaches_of_mem hs).1, (hle _ _).mp (hPy.reaches_of_mem hs).2⟩
  have tx : ∀ s ∈ Sx, ∀ t ∈ Sx, s ≤ t ∨ t ≤ s := fun s hs t ht =>
    (hPx.total hs ht).imp (hle _ _).mp (hle _ _).mp
  have dx : ∀ s ∈ Sx, s ≤ G.source e ∨ G.target e ≤ s := fun s hs =>
    (hPx.mem_or he hs).imp (hle _ _).mp (hle _ _).mp
  have hsrcx : G.source e ∈ Sx := (hPx.ends_mem he).1
  have htgtx : G.target e ∈ Sx := (hPx.ends_mem he).2
  have hmx : m ∈ Sx := hPx.start_mem
  have hmy : m ∈ Sy := hPy.start_mem
  obtain ⟨a, ⟨hax, hay, has⟩, ha_low⟩ := Set.Finite.exists_greatest_of_total
    (T := {v | v ∈ Sx ∧ v ∈ Sy ∧ v ≤ G.source e}) (Set.toFinite _)
    ⟨m, hmx, hmy, (mx _ hsrcx).1⟩ fun s hs t ht => tx s hs.1 t ht.1
  by_cases hB : (Sx ∩ Sy ∩ {v | G.target e ≤ v}).Nonempty
  swap
  · -- `B = ∅`: the trek with top `a`
    obtain ⟨P₁, hP₁, -, hP₁e⟩ := IsDPath.segment_le hle hA hPx hax hPx.end_mem (mx a hax).2
    obtain ⟨P₂, hP₂, -, -⟩ := IsDPath.segment_le hle hA hPy hay hPy.end_mem (my a hay).2
    refine hasTrekThrough_of_subset hle (fun s hs => (mx s hs).1) (fun s hs => (my s hs).1)
      (Ss := ∅) (fun _ h => absurd h (Set.notMem_empty _)) hP₁ hP₂ ?_
      (Or.inl (hP₁e e he has (mx _ htgtx).2)) ?_
    · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨hax, le_rfl, (mx a hax).2⟩, hay, le_rfl,
        (my a hay).2⟩, ?_⟩
      rintro s ⟨⟨hsx, has', -⟩, hsy, -, -⟩
      rcases dx s hsx with h | h
      · exact le_antisymm (ha_low s ⟨hsx, hsy, h⟩) has'
      · exact absurd ⟨s, ⟨hsx, hsy⟩, h⟩ hB
    · rintro s (⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  -- `b⁻`, the lowest node of `B`
  obtain ⟨bm, ⟨⟨hbmx, hbmy⟩, hbm⟩, hbm_low⟩ := Set.Finite.exists_greatest_of_total
    (T := Sx ∩ Sy ∩ {v | G.target e ≤ v}) (Set.toFinite _) hB fun s hs t ht => tx s hs.1.1 t ht.1.1
  have hmb : bm ≠ m := fun h => hts (h ▸ hbm |>.trans (mx _ hsrcx).1)
  -- `P*`, a path from `m` avoiding `b⁻`
  obtain ⟨Z₀, hZ₀, Ss, Ps, hPs, hbs⟩ := hm bm (mx bm hbmx).1 hmb
  have ms : ∀ s ∈ Ss, m ≤ s ∧ s ≤ Z₀ := fun s hs =>
    ⟨(hle _ _).mp (hPs.reaches_of_mem hs).1, (hle _ _).mp (hPs.reaches_of_mem hs).2⟩
  -- `c`, the first node of `P*` strictly below `b⁻` on `Px` or `Py`
  have hZT : Z₀ ∈ {v | v ∈ Ss ∧ (v ∈ Sx ∨ v ∈ Sy) ∧ bm ≤ v ∧ v ≠ bm} := by
    refine ⟨hPs.end_mem, ?_, ?_, fun h => hbs (h ▸ hPs.end_mem)⟩
    · rcases hZ₀ with rfl | rfl
      · exact Or.inl hPx.end_mem
      · exact Or.inr hPy.end_mem
    · rcases hZ₀ with rfl | rfl
      · exact (mx _ hbmx).2
      · exact (my _ hbmy).2
  obtain ⟨c, ⟨hcs, hcxy, hbc, hcb⟩, hc_high⟩ := Set.Finite.exists_least_of_total
    (T := {v | v ∈ Ss ∧ (v ∈ Sx ∨ v ∈ Sy) ∧ bm ≤ v ∧ v ≠ bm}) (Set.toFinite _) ⟨Z₀, hZT⟩
    fun s hs t ht => (hPs.total hs.1 ht.1).imp (hle _ _).mp (hle _ _).mp
  have hcxy' : ¬ (c ∈ Sx ∧ c ∈ Sy) := fun h =>
    hcb (le_antisymm (hbm_low c ⟨⟨h.1, h.2⟩, hbm.trans hbc⟩) hbc)
  rcases hcxy with hcx | hcy
  · -- `c` on `Px`: exchange the parts of the paths below `b⁻`
    have hcy : c ∉ Sy := fun h => hcxy' ⟨hcx, h⟩
    obtain ⟨Q₁, hQ₁, -, hQ₁e⟩ := IsDPath.segment_le hle hA hPx hmx hbmx (mx bm hbmx).1
    obtain ⟨Q₂, hQ₂, -, -⟩ := IsDPath.segment_le hle hA hPy hbmy hPy.end_mem (my bm hbmy).2
    obtain ⟨Q₃, hQ₃, -, -⟩ := IsDPath.segment_le hle hA hPy hmy hbmy (my bm hbmy).1
    obtain ⟨Q₄, hQ₄, -, -⟩ := IsDPath.segment_le hle hA hPx hbmx hPx.end_mem (mx bm hbmx).2
    have hB' : ({s | s ∈ Sx ∧ m ≤ s ∧ s ≤ bm} ∪ {s | s ∈ Sy ∧ bm ≤ s ∧ s ≤ Y₀}) ∩
        ({s | s ∈ Sy ∧ m ≤ s ∧ s ≤ bm} ∪ {s | s ∈ Sx ∧ bm ≤ s ∧ s ≤ X₀}) ∩
          {v | G.target e ≤ v} = Sx ∩ Sy ∩ {v | G.target e ≤ v} := by
      ext v
      constructor
      · rintro ⟨⟨⟨hvx, -, hvb⟩ | ⟨hvy, hbv, -⟩, ⟨hvy', -, hvb'⟩ | ⟨hvx', hbv', -⟩⟩, htv⟩
        · exact ⟨⟨hvx, hvy'⟩, htv⟩
        · have : v = bm := le_antisymm hvb hbv'
          exact ⟨⟨hvx, this ▸ hbmy⟩, htv⟩
        · have : v = bm := le_antisymm hvb' hbv
          exact ⟨⟨this ▸ hbmx, hvy⟩, htv⟩
        · exact ⟨⟨hvx', hvy⟩, htv⟩
      · rintro ⟨⟨hvx, hvy⟩, htv⟩
        have := hbm_low v ⟨⟨hvx, hvy⟩, htv⟩
        exact ⟨⟨Or.inl ⟨hvx, (mx v hvx).1, this⟩, Or.inl ⟨hvy, (my v hvy).1, this⟩⟩, htv⟩
    refine HasTrekThrough.symm (trek_mainStep hle hA (hQ₁.append hQ₂)
      (Or.inl (hQ₁e e he (mx _ hsrcx).1 hbm)) (hQ₃.append hQ₄) ?_ (Or.inl ⟨hbmx, (mx bm hbmx).1, le_rfl⟩)
      (Or.inl ⟨hbmy, (my bm hbmy).1, le_rfl⟩) hbm ?_ hPs hbs hcs
      (Or.inr ⟨hcx, hbc, (mx c hcx).2⟩) ?_ hbc hcb ?_ ?_)
    · rintro (⟨h, -⟩ | ⟨-, hbt, -⟩)
      · exact hey h
      · have : G.target e = bm := le_antisymm hbm hbt
        exact hey (this ▸ hbmy)
    · intro v hvx hvy htv
      have hv : v ∈ Sx ∩ Sy ∩ {v | G.target e ≤ v} := hB' ▸ ⟨⟨hvx, hvy⟩, htv⟩
      exact hbm_low v hv
    · rintro (⟨-, -, hcb'⟩ | ⟨h, -⟩)
      · exact hcb (le_antisymm hcb' hbc)
      · exact hcy h
    · intro v hvs hvxy hbv hvb
      refine hc_high v ⟨hvs, ?_, hbv, hvb⟩
      rcases hvxy with (⟨h, -⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr h
      · exact Or.inl h
    · intro Sx'' Px'' Sy'' Py'' h₁ h₂ h₃ h₄ hlt
      rw [hB'] at hlt
      exact IH _ (hn ▸ hlt) Y₀ X₀ Sx'' Sy'' Px'' Py''
        (fun b h h' => (hm b h h').imp fun _ h => ⟨h.1.symm, h.2⟩) h₁ h₂ h₃ h₄ rfl
  · have hcx : c ∉ Sx := fun h => hcxy' ⟨h, hcy⟩
    exact trek_mainStep hle hA hPx he hPy hey hbmx hbmy hbm
      (fun v hvx hvy htv => hbm_low v ⟨⟨hvx, hvy⟩, htv⟩) hPs hbs hcs hcy hcx hbc hcb
      (fun v hvs hvxy hbv hvb => hc_high v ⟨hvs, hvxy, hbv, hvb⟩)
      fun Sx' Px' Sy' Py' h₁ h₂ h₃ h₄ hlt =>
        IH _ (hn ▸ hlt) X₀ Y₀ Sx' Sy' Px' Py' hm h₁ h₂ h₃ h₄ rfl

end Trek

end Banos2019

namespace Banos2019

open Phylogenetics.RootedNetwork

variable {V E X : Type*}

/-- Below the LSA of `Y`, every node other than the LSA is avoided by a path from the LSA to a taxon
of `Y`: else it would be a lower stable ancestor. -/
theorem exists_isDPath_avoiding {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {Y : Set X}
    {l : V} (hl : N.IsLeastStableAncestor Y l) {b : V} (hlb : N.graph.Reaches l b) (hb : b ≠ l) :
    ∃ z ∈ Y, ∃ S P, IsDPath N.graph l (N.leaf z) S P ∧ b ∉ S := by
  by_contra hcon
  push Not at hcon
  have hst : N.IsStableAncestor Y b := by
    intro z hz hp
    have hs := hp.suffix_of_not_hasPathAvoiding (hl.1 z hz)
    obtain ⟨S, P, hP, hbS⟩ := IsDPath.of_reflTransGen_avoiding hs.2.2 hs.1
    exact hbS (hcon z hz S P hP)
  exact hb (eq_of_reaches_of_reaches hN.acyclic (hl.2 b hst) hlb)

end Banos2019
