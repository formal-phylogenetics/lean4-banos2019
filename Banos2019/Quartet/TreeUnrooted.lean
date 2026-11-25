module

public import Banos2019.Quartet.Trees
public import Banos2019.Quartet.UnrootedIso
public import Banos2019.Quartet.SemidirectedCycles
public import Banos2019.Quartet.ContractSet

/-!
# The unrooted metric tree of a tree, read off its unrooted network (base case of Proposition 5)

An edge `e` *cuts* the taxa `A` (`CutAt`) when it is the only edge crossing a set of nodes whose
taxa are `A`. The cuts of `N⁻` are those of `N` (`cutAt_unrooted_iff`): the two arcs at the root of
`N` cut the same sets (`cutAt_root_iff`), and `N⁻` merges them. An isomorphism of semidirected
networks keeps the cuts (`SDIso.cutAt_iff`).

For a binary tree `N` whose root is the LSA of its taxa, the arc into a node cuts the cluster of the
node and its complement, and nothing else (`cutAt_iff_of_tree`). So the splits of the unrooted
species tree of `N` are the sets of taxa cut by edges of `N⁻`
(`mem_unroot_treeClusters_iff_exists_cutAt`), and the length of a split is the total length of the
edges of `N⁻` that cut it (`unrootedLength_eq_cutLength`). Two such trees with isomorphic metric
unrooted networks have the same unrooted metric species tree (`sameUnrootedMetricTree_of_iso`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

variable {V E X : Type*}

/-! ### Cuts -/

/-- The edge `e` is the only edge crossing a set of nodes whose taxa are `A`. -/
def CutAt (G : DirectedMultigraph V E) (leaf : X → V) (e : E) (A : Set X) : Prop :=
  ∃ S : Set V, (∀ f, G.Crosses f S ↔ f = e) ∧ leaf ⁻¹' S = A

theorem crosses_iff_not_iff (G : DirectedMultigraph V E) (f : E) (S : Set V) :
    G.Crosses f S ↔ ¬ (G.source f ∈ S ↔ G.target f ∈ S) := by
  unfold DirectedMultigraph.Crosses
  tauto

section Iso

variable {V' E' : Type*} {G : SemidirectedNetwork V E X} {G' : SemidirectedNetwork V' E' X}

theorem SDIso.cutAt_of (ι : SDIso G G') {g : E} {A : Set X} (h : CutAt G.graph G.leaf g A) :
    CutAt G'.graph G'.leaf (ι.edge g) A := by
  obtain ⟨S, hS, hA⟩ := h
  refine ⟨ι.vert '' S, fun f' => ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := ι.edge.surjective f'
    rw [ι.edge.injective.eq_iff, ← hS f, crosses_iff_not_iff, crosses_iff_not_iff]
    rcases ι.joins f with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂, ι.vert.injective.mem_set_image, ι.vert.injective.mem_set_image]
    · rw [h₁, h₂, ι.vert.injective.mem_set_image, ι.vert.injective.mem_set_image]
      tauto
  · ext x
    simp only [Set.mem_preimage, ι.leaf, ι.vert.injective.mem_set_image]
    rw [← hA]
    rfl

/-- **An isomorphism keeps the cuts.** -/
theorem SDIso.cutAt_iff (ι : SDIso G G') (g : E) (A : Set X) :
    CutAt G'.graph G'.leaf (ι.edge g) A ↔ CutAt G.graph G.leaf g A := by
  refine ⟨fun h => ?_, ι.cutAt_of⟩
  have := ι.symm.cutAt_of h
  rwa [show ι.symm.edge (ι.edge g) = g from ι.edge.symm_apply_apply g] at this

end Iso

/-! ### The cuts of `N` and of `N⁻` -/

section Unrooted

variable {M : RootedNetwork V E X}

/-- **The two arcs at the root cut the same sets of taxa**: moving the root to the other side of a
cut by one of them makes it a cut by the other. -/
theorem cutAt_root_iff (hM : M.IsPhylogenetic) {e₁ e₂ : E} (hne : e₁ ≠ e₂)
    (h₁ : M.graph.source e₁ = M.root) (h₂ : M.graph.source e₂ = M.root)
    (hroot : ∀ f, M.graph.source f = M.root → f = e₁ ∨ f = e₂) (A : Set X) :
    CutAt M.graph M.leaf e₁ A ↔ CutAt M.graph M.leaf e₂ A := by
  have key : ∀ a b, a ≠ b → M.graph.source a = M.root → M.graph.source b = M.root →
      (∀ f, M.graph.source f = M.root → f = a ∨ f = b) →
      CutAt M.graph M.leaf a A → CutAt M.graph M.leaf b A := by
    intro a b hab ha hb hr ⟨S, hS, hA⟩
    refine ⟨symmDiff S {M.root}, fun f => ?_, ?_⟩
    · have ht : M.graph.target f ≠ M.root := hM.target_ne_root f
      have hmem : ∀ v, v ≠ M.root → (v ∈ symmDiff S {M.root} ↔ v ∈ S) := fun v hv => by
        simp [Set.mem_symmDiff, hv]
      have hroot' : M.root ∈ symmDiff S {M.root} ↔ M.root ∉ S := by
        simp [Set.mem_symmDiff]
      by_cases hf : M.graph.source f = M.root
      · rw [crosses_iff_not_iff, hf, hroot', hmem _ ht]
        have hcross := hS f
        rw [crosses_iff_not_iff, hf] at hcross
        rcases hr f hf with rfl | rfl
        · simp only [hab, iff_false] at hcross ⊢
          tauto
        · simp only [Ne.symm hab, iff_false, iff_true] at hcross ⊢
          tauto
      · rw [crosses_iff_not_iff, hmem _ hf, hmem _ ht, ← crosses_iff_not_iff, hS f]
        constructor
        · rintro rfl
          exact absurd ha hf
        · rintro rfl
          exact absurd hb hf
    · ext x
      have hx : M.leaf x ≠ M.root := M.leaf_ne_root hM x
      simp only [Set.mem_preimage, Set.mem_symmDiff, Set.mem_singleton_iff, hx, not_false_eq_true,
        and_true, false_and, or_false]
      rw [← hA]
      rfl
  exact ⟨key e₁ e₂ hne h₁ h₂ hroot,
    key e₂ e₁ (Ne.symm hne) h₂ h₁ fun f hf => (hroot f hf).symm⟩

variable (hM : IsBinaryRootedNetwork M) (hl : M.IsLSANetwork) (hX : Nontrivial X)
include hl

/-- **The cuts of `N⁻` are those of `N`**: an edge of `N⁻` cuts the taxa that its arc of `N` cuts.
-/
theorem cutAt_unrooted_iff (g : SemidirectedArc hM.1 hM.2 hX) (A : Set X) :
    CutAt (unrooted M hM hX).graph (unrooted M hM hX).leaf g A ↔
      CutAt M.graph M.leaf (sdArc hM.1 hM.2 hX g) A := by
  have hr := lsa_univ_eq_root hM.1 hX hl
  set G := unrooted M hM hX
  set e₀ := sdRootArc hM.1 hM.2 hX
  have he₀ : M.graph.source e₀ = M.root := (sdRootArc_spec hM.1 hM.2 hX).1.trans hr
  have hκe₀ : ∀ f, sdArc hM.1 hM.2 hX f ≠ e₀ := sdArc_ne_sdRootArc hM.1 hM.2 hX
  have hιr : ∀ u, sdVert hM.1 hX u ≠ M.root := fun u => hr ▸ sdVert_ne_lsa hM.1 hX u
  have hsrc : ∀ f, sdVert hM.1 hX (G.graph.source f) =
      if M.graph.source (sdArc hM.1 hM.2 hX f) = M.root then M.graph.target e₀
      else M.graph.source (sdArc hM.1 hM.2 hX f) := fun f => by
    rw [sdVert_source, hr]
  have htgt : ∀ f, sdVert hM.1 hX (G.graph.target f) = M.graph.target (sdArc hM.1 hM.2 hX f) :=
    sdVert_target hM.1 hM.2 hX
  -- every arc of `M` is `e₀` or the arc of an edge of `N⁻`
  have harc : ∀ e, e = e₀ ∨ ∃ f, sdArc hM.1 hM.2 hX f = e := fun e => by
    by_cases he : e = e₀
    · exact Or.inl he
    · exact Or.inr ((mem_range_sdArc hM.1 hM.2 hX e).2 ⟨hr ▸ hM.1.root_reaches _, he⟩)
  have hvert : ∀ v, v ≠ M.root → ∃ u, sdVert hM.1 hX u = v := fun v hv =>
    (mem_range_sdVert hM.1 hX v).2 ⟨hr ▸ hM.1.root_reaches _, hr ▸ hv⟩
  have ht₀ : M.graph.target e₀ ≠ M.root := hM.1.target_ne_root e₀
  constructor
  · rintro ⟨T, hT, hA⟩
    set S : Set V := sdVert hM.1 hX '' T ∪
      {v | v = M.root ∧ M.graph.target e₀ ∈ sdVert hM.1 hX '' T}
    have hS : ∀ u, sdVert hM.1 hX u ∈ S ↔ u ∈ T := fun u => by
      simp only [S, Set.mem_union, (sdVert_injective hM.1 hX).mem_set_image, Set.mem_ofPred_eq,
        hιr u, false_and, or_false]
    have hSr : M.root ∈ S ↔ M.graph.target e₀ ∈ sdVert hM.1 hX '' T := by
      simp only [S, Set.mem_union, Set.mem_ofPred_eq, true_and]
      constructor
      · rintro (⟨u, -, hu⟩ | h)
        · exact absurd hu (hιr u)
        · exact h
      · exact Or.inr
    have hS' : ∀ v, v ≠ M.root → (v ∈ S ↔ v ∈ sdVert hM.1 hX '' T) := fun v hv => by
      obtain ⟨u, rfl⟩ := hvert v hv
      rw [hS, (sdVert_injective hM.1 hX).mem_set_image]
    refine ⟨S, fun e => ?_, ?_⟩
    · rcases harc e with rfl | ⟨f, rfl⟩
      · rw [crosses_iff_not_iff, he₀, hSr, hS' _ ht₀]
        simp only [iff_self, not_true_eq_false, false_iff]
        exact fun h => hκe₀ g h.symm
      · rw [(sdArc_injective hM.1 hM.2 hX).eq_iff, ← hT f, crosses_iff_not_iff, crosses_iff_not_iff,
          ← hS (G.graph.source f), ← hS (G.graph.target f), hsrc, htgt]
        split_ifs with hfr
        · rw [hfr, hSr, hS' _ ht₀]
        · rfl
    · ext x
      have hx : M.leaf x ≠ M.root := M.leaf_ne_root hM.1 x
      rw [Set.mem_preimage, hS' _ hx, ← sdVert_leaf hM.1 hM.2 hX x,
        (sdVert_injective hM.1 hX).mem_set_image, ← hA]
      rfl
  · rintro ⟨S, hS, hA⟩
    refine ⟨{u | sdVert hM.1 hX u ∈ S}, fun f => ?_, ?_⟩
    · rw [crosses_iff_not_iff]
      simp only [Set.mem_ofPred_eq]
      rw [hsrc, htgt]
      split_ifs with hfr
      · -- the edge merged at the root
        have h₀ := hS e₀
        rw [crosses_iff_not_iff, he₀] at h₀
        have hf := hS (sdArc hM.1 hM.2 hX f)
        rw [crosses_iff_not_iff, hfr, (sdArc_injective hM.1 hM.2 hX).eq_iff] at hf
        rw [← hf]
        have : ¬ (e₀ = sdArc hM.1 hM.2 hX g) := fun h => hκe₀ g h.symm
        simp only [this, iff_false] at h₀
        tauto
      · rw [← crosses_iff_not_iff, hS, (sdArc_injective hM.1 hM.2 hX).eq_iff]
    · ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [← hA]
      rfl

/-- The other arc at the root is the arc of an edge of `N⁻`: the edge that `N⁻` merges. -/
theorem exists_sdArc_source_root :
    ∃ g, M.graph.source (sdArc hM.1 hM.2 hX g) = M.root ∧
      ∀ f, M.graph.source f = M.root → f = sdRootArc hM.1 hM.2 hX ∨ f = sdArc hM.1 hM.2 hX g := by
  have := hM.1.finite_arcs
  have hr := lsa_univ_eq_root hM.1 hX hl
  set e₀ := sdRootArc hM.1 hM.2 hX
  have he₀ : M.graph.source e₀ = M.root := (sdRootArc_spec hM.1 hM.2 hX).1.trans hr
  obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 hM.2.1
  have m : ∀ z, M.graph.source z = M.root → z = x ∨ z = y := fun z hz => by
    have : z ∈ {e | M.graph.source e = M.root} := hz
    rw [hs] at this
    simpa using this
  have hx : M.graph.source x = M.root := (Set.ext_iff.1 hs x).2 (Or.inl rfl)
  have hy : M.graph.source y = M.root := (Set.ext_iff.1 hs y).2 (Or.inr rfl)
  obtain ⟨e₁, he₁, hne⟩ : ∃ e₁, M.graph.source e₁ = M.root ∧ e₁ ≠ e₀ := by
    rcases m e₀ he₀ with h' | h'
    · exact ⟨y, hy, fun h'' => hxy (h'.symm.trans h''.symm)⟩
    · exact ⟨x, hx, fun h'' => hxy (h''.trans h')⟩
  have hroot : ∀ f, M.graph.source f = M.root → f = e₀ ∨ f = e₁ := fun f hf => by
    rcases m f hf with rfl | rfl <;> rcases m e₀ he₀ with h' | h' <;>
      rcases m e₁ he₁ with h'' | h'' <;> simp_all
  obtain ⟨g, hg⟩ := (mem_range_sdArc hM.1 hM.2 hX e₁).2 ⟨hr ▸ hM.1.root_reaches _, hne⟩
  exact ⟨g, hg ▸ he₁, fun f hf => hg ▸ hroot f hf⟩

/-- **Some arc of `N` cuts `A` exactly when some edge of `N⁻` does**: an arc other than the arc `e₀`
that `N⁻` merges is the arc of an edge, and `e₀` cuts what the other arc at the root cuts. -/
theorem exists_cutAt_iff_exists_unrooted (A : Set X) :
    (∃ e, CutAt M.graph M.leaf e A) ↔
      ∃ g, CutAt (unrooted M hM hX).graph (unrooted M hM hX).leaf g A := by
  have := hM.1.finite_arcs
  have hr := lsa_univ_eq_root hM.1 hX hl
  set e₀ := sdRootArc hM.1 hM.2 hX
  have he₀ : M.graph.source e₀ = M.root := (sdRootArc_spec hM.1 hM.2 hX).1.trans hr
  constructor
  · rintro ⟨e, he⟩
    by_cases h : e = e₀
    · -- the other arc at the root
      obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.1 hM.2.1
      have m : ∀ z, M.graph.source z = M.root → z = x ∨ z = y := fun z hz => by
        have : z ∈ {e | M.graph.source e = M.root} := hz
        rw [hs] at this
        simpa using this
      have hx : M.graph.source x = M.root := (Set.ext_iff.1 hs x).2 (Or.inl rfl)
      have hy : M.graph.source y = M.root := (Set.ext_iff.1 hs y).2 (Or.inr rfl)
      obtain ⟨e₁, he₁, hne⟩ : ∃ e₁, M.graph.source e₁ = M.root ∧ e₁ ≠ e₀ := by
        rcases m e₀ he₀ with h' | h'
        · exact ⟨y, hy, fun h'' => hxy (h'.symm.trans h''.symm)⟩
        · exact ⟨x, hx, fun h'' => hxy (h''.trans h')⟩
      have hroot : ∀ f, M.graph.source f = M.root → f = e₀ ∨ f = e₁ := fun f hf => by
        rcases m f hf with rfl | rfl <;> rcases m e₀ he₀ with h' | h' <;>
          rcases m e₁ he₁ with h'' | h'' <;> simp_all
      obtain ⟨g, hg⟩ := (mem_range_sdArc hM.1 hM.2 hX e₁).2 ⟨hr ▸ hM.1.root_reaches _, hne⟩
      refine ⟨g, (cutAt_unrooted_iff hM hl hX g A).2 ?_⟩
      rw [hg, ← cutAt_root_iff hM.1 (Ne.symm hne) he₀ he₁ hroot A, ← h]
      exact he
    · obtain ⟨g, rfl⟩ := (mem_range_sdArc hM.1 hM.2 hX e).2 ⟨hr ▸ hM.1.root_reaches _, h⟩
      exact ⟨g, (cutAt_unrooted_iff hM hl hX g A).2 he⟩
  · rintro ⟨g, hg⟩
    exact ⟨_, (cutAt_unrooted_iff hM hl hX g A).1 hg⟩

end Unrooted

/-! ### The length of the edges cutting a set of taxa -/

section CutLength

variable {V' E' : Type*}

/-- The total length of the edges of `G` that cut `A`. -/
def cutLength [Fintype E] (G : SemidirectedNetwork V E X) (μ : MetricData E) (A : Set X) : ℝ :=
  ∑ g ∈ univ.filter (fun g => CutAt G.graph G.leaf g A), μ.length g

/-- **An isomorphism keeps the length of the edges cutting a set of taxa.** -/
theorem SDMetricIso.cutLength_eq [Fintype E] [Fintype E'] {G : SemidirectedNetwork V E X}
    {μ : MetricData E} {G' : SemidirectedNetwork V' E' X} {μ' : MetricData E'}
    (ι : SDMetricIso G μ G' μ') (A : Set X) : cutLength G' μ' A = cutLength G μ A := by
  unfold cutLength
  rw [sum_filter, sum_filter, ← ι.edge.sum_comp]
  refine sum_congr rfl fun g _ => ?_
  rw [ι.cutAt_iff, ι.length]

end CutLength

/-! ### Trees -/

section Tree

variable [Fintype V] [Fintype E] [Fintype X] {M : RootedNetwork V E X}

omit [Fintype V] in
/-- **The arc into a node of a tree cuts the cluster of the node and its complement**, and no other
set of taxa: the nodes below the node are joined without the arc, and so are the others, through the
root. -/
theorem cutAt_iff_of_tree (hM : M.IsPhylogenetic) (ht : ∀ e, ¬ M.IsHybridArc e) (e : E)
    (A : Finset X) :
    CutAt M.graph M.leaf e ↑A ↔
      treeCluster M (M.graph.target e) = A ∨ treeCluster M (M.graph.target e) = Aᶜ := by
  set v := M.graph.target e
  -- the arc `e` is the only arc into the part below `v`
  have hcross : ∀ f, M.graph.Crosses f {w | M.graph.Reaches v w} ↔ f = e := by
    intro f
    rw [crosses_iff_not_iff]
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      by_contra hfe
      apply h
      constructor
      · exact fun hs => hs.tail ⟨f, rfl, rfl⟩
      · intro htg
        have hne : v ≠ M.graph.target f := fun h' => hfe (arc_eq_of_target_eq ht h'.symm)
        exact reaches_source_of_reaches_target ht htg hne
    · intro hfe
      rw [hfe]
      have := not_reaches_source hM e
      exact fun h => this (h.2 .refl)
  constructor
  · rintro ⟨T, hT, hAT⟩
    have hnot : ∀ f, M.graph.Reaches v (M.graph.source f) → f ≠ e := fun f hf hfe =>
      hM.acyclic _ (Relation.TransGen.head' ⟨e, rfl, rfl⟩ (by rw [hfe] at hf; exact hf))
    have hbelow : ∀ x, M.graph.Reaches v (M.leaf x) → (M.leaf x ∈ T ↔ v ∈ T) := fun x hx =>
      (M.graph.mem_iff_mem_of_walks (F := {e}ᶜ) (fun f hf hc => hf ((hT f).1 hc))
        (walks_of_reaches_of_forall hx fun f hf _ => hnot f hf)).symm
    have hroot : ∀ w, ¬ M.graph.Reaches v w → (w ∈ T ↔ M.root ∈ T) := fun w hw =>
      (M.graph.mem_iff_mem_of_walks (F := {e}ᶜ) (fun f hf hc => hf ((hT f).1 hc))
        (walks_of_reaches_of_forall (hM.root_reaches w) fun f _ hf hfe => hw (by
          rw [Set.mem_singleton_iff] at hfe
          subst hfe
          exact hf))).symm
    have hsv : M.graph.source e ∈ T ↔ ¬ v ∈ T := by
      have hc := (hT e).2 rfl
      unfold DirectedMultigraph.Crosses at hc
      tauto
    have hrs : M.root ∈ T ↔ M.graph.source e ∈ T := (hroot _ fun h =>
      hM.acyclic _ (Relation.TransGen.head' ⟨e, rfl, rfl⟩ h)).symm
    have hA_eq : ∀ x, x ∈ A ↔ (x ∈ treeCluster M v ↔ v ∈ T) := by
      intro x
      have hx : x ∈ A ↔ M.leaf x ∈ T := by
        rw [← Finset.mem_coe, ← hAT]
        rfl
      rw [hx, mem_treeCluster]
      by_cases hxv : M.graph.Reaches v (M.leaf x)
      · rw [hbelow x hxv]
        tauto
      · rw [hroot _ hxv, hrs, hsv]
        tauto
    by_cases hvT : v ∈ T
    · left
      ext x
      rw [hA_eq]
      tauto
    · right
      ext x
      rw [mem_compl, hA_eq]
      tauto
  · rintro (h | h)
    · refine ⟨{w | M.graph.Reaches v w}, hcross, ?_⟩
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Finset.mem_coe, ← h, mem_treeCluster]
    · refine ⟨{w | M.graph.Reaches v w}ᶜ, fun f => ?_, ?_⟩
      · rw [← hcross f]
        unfold DirectedMultigraph.Crosses
        simp only [Set.mem_compl_iff]
        tauto
      · ext x
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.mem_coe]
        rw [← mem_treeCluster (N := M), h, mem_compl, not_not]

/-- **The splits of the unrooted species tree of a binary tree are the sets of taxa its arcs
cut.** -/
theorem mem_unroot_treeClusters_iff_exists_cutAt (hM : IsBinaryRootedNetwork M)
    (ht : ∀ e, ¬ M.IsHybridArc e) (A : Finset X) :
    A ∈ unroot (treeClusters M) ↔ ∃ e, CutAt M.graph M.leaf e ↑A := by
  have hne : ∀ e, treeCluster M (M.graph.target e) ≠ univ := fun e =>
    treeCluster_target_ne_univ hM.1 ht (not_isChainVertex_of_binary hM) (Or.inr (by rw [hM.2.1]))
  have harc : ∀ B : Finset X, B ∈ treeClusters M → B ≠ univ →
      ∃ e, treeCluster M (M.graph.target e) = B := by
    intro B hB hBu
    obtain ⟨w, rfl⟩ := mem_treeClusters.1 hB
    have hwr : w ≠ M.root := fun h => hBu (h ▸ treeCluster_root hM.1)
    obtain ⟨e, he⟩ := (M.graph.one_le_indegree_iff w).1 (hM.1.nonroot_indegree w hwr)
    exact ⟨e, by rw [he]⟩
  rw [mem_unroot]
  constructor
  · rintro (⟨hA, hAu⟩ | ⟨hA, hAu⟩)
    · obtain ⟨e, he⟩ := harc A hA hAu
      exact ⟨e, (cutAt_iff_of_tree hM.1 ht e A).2 (Or.inl he)⟩
    · obtain ⟨e, he⟩ := harc _ hA hAu
      exact ⟨e, (cutAt_iff_of_tree hM.1 ht e A).2 (Or.inr he)⟩
  · rintro ⟨e, he⟩
    rcases (cutAt_iff_of_tree hM.1 ht e A).1 he with h | h
    · exact Or.inl ⟨h ▸ mem_treeClusters.2 ⟨_, rfl⟩, h ▸ hne e⟩
    · exact Or.inr ⟨h ▸ mem_treeClusters.2 ⟨_, rfl⟩, h ▸ hne e⟩

end Tree

/-- **The length of a split of the unrooted species tree of a binary tree is the total length of
the edges of `N⁻` that cut it**: the arcs of `N` cutting it, the two arcs at the root counted as the
edge of `N⁻` that merges them. -/
theorem unrootedLength_eq_cutLength [Fintype V] [Fintype E] [Fintype X] {M : RootedNetwork V E X}
    (hM : IsBinaryRootedNetwork M) (hl : M.IsLSANetwork) (hX : Nontrivial X)
    (ht : ∀ e, ¬ M.IsHybridArc e) {θ : MetricData E} (hθ : M.IsMetric θ) (A : Finset X) :
    (treeSpeciesTree M hM.1 ht hθ).unrootedLength A =
      cutLength (unrooted M hM hX) (unrootedMetric M hM hX θ) ↑A := by
  have hr := lsa_univ_eq_root hM.1 hX hl
  set e₀ := sdRootArc hM.1 hM.2 hX
  have he₀ : M.graph.source e₀ = M.root := (sdRootArc_spec hM.1 hM.2 hX).1.trans hr
  have hne : ∀ e, treeCluster M (M.graph.target e) ≠ univ := fun e =>
    treeCluster_target_ne_univ hM.1 ht (not_isChainVertex_of_binary hM) (Or.inr (by rw [hM.2.1]))
  have hC : ∀ e, (treeCluster M (M.graph.target e) ≠ univ ∧
      (treeCluster M (M.graph.target e) = A ∨ treeCluster M (M.graph.target e) = Aᶜ)) ↔
      CutAt M.graph M.leaf e ↑A := fun e => by
    rw [cutAt_iff_of_tree hM.1 ht e A]
    exact and_iff_right (hne e)
  rw [treeSpeciesTree_unrootedLength, Finset.filter_congr (fun e _ => hC e)]
  unfold cutLength
  rw [sum_filter, sum_filter, ← Finset.add_sum_erase _ _ (mem_univ e₀)]
  -- the arcs other than `e₀` are those of the edges of `N⁻`
  have hbij : ∑ e ∈ univ.erase e₀, (if CutAt M.graph M.leaf e ↑A then θ.length e else 0) =
      ∑ g, (if CutAt M.graph M.leaf (sdArc hM.1 hM.2 hX g) ↑A then
        θ.length (sdArc hM.1 hM.2 hX g) else 0) := by
    symm
    refine Finset.sum_bij (fun g _ => sdArc hM.1 hM.2 hX g)
      (fun g _ => mem_erase.2 ⟨sdArc_ne_sdRootArc hM.1 hM.2 hX g, mem_univ _⟩)
      (fun g _ g' _ h => sdArc_injective hM.1 hM.2 hX h) (fun e he => ?_) (fun _ _ => rfl)
    obtain ⟨g, hg⟩ := (mem_range_sdArc hM.1 hM.2 hX e).2
      ⟨hr ▸ hM.1.root_reaches _, (mem_erase.1 he).1⟩
    exact ⟨g, mem_univ _, hg⟩
  -- the edge merged at the root carries `e₀`
  obtain ⟨g₁, hg₁, hroot⟩ := exists_sdArc_source_root hM hl hX
  have hsplit : ∀ g, (if CutAt (unrooted M hM hX).graph (unrooted M hM hX).leaf g ↑A then
      (unrootedMetric M hM hX θ).length g else 0) =
      (if CutAt M.graph M.leaf (sdArc hM.1 hM.2 hX g) ↑A then
        θ.length (sdArc hM.1 hM.2 hX g) else 0) +
      (if CutAt M.graph M.leaf (sdArc hM.1 hM.2 hX g) ↑A ∧
        M.graph.source (sdArc hM.1 hM.2 hX g) = M.root then θ.length e₀ else 0) := by
    intro g
    rw [cutAt_unrooted_iff hM hl hX g, semidirectedMetric_length, hr]
    split_ifs <;> simp_all
    rfl
  have hK : (∑ g, if CutAt M.graph M.leaf (sdArc hM.1 hM.2 hX g) ↑A ∧
      M.graph.source (sdArc hM.1 hM.2 hX g) = M.root then θ.length e₀ else 0) =
      if CutAt M.graph M.leaf e₀ ↑A then θ.length e₀ else 0 := by
    rw [Finset.sum_eq_single g₁]
    · rw [if_congr (and_iff_left hg₁) rfl rfl,
        ← cutAt_root_iff hM.1 (sdArc_ne_sdRootArc hM.1 hM.2 hX g₁).symm he₀ hg₁ hroot]
    · intro g _ hg
      rw [ite_eq_right]
      rintro ⟨-, h⟩
      exact hg (eq_of_source_sdArc_eq_lsa hM.1 hM.2 hX (h.trans hr.symm) (hg₁.trans hr.symm))
    · exact fun h => absurd (mem_univ g₁) h
  rw [hbij, sum_congr rfl fun g _ => hsplit g, sum_add_distrib, hK, add_comm]

/-- **Base case of Proposition 5**: two binary trees whose roots are the LSAs of their taxa and
whose metric unrooted networks are isomorphic have the same unrooted metric species tree. -/
theorem sameUnrootedMetricTree_of_iso [Fintype V] [Fintype E] [Fintype X] {V' E' : Type*}
    [Fintype V'] [Fintype E'] {M : RootedNetwork V E X} {M' : RootedNetwork V' E' X}
    (hM : IsBinaryRootedNetwork M) (hl : M.IsLSANetwork) (hM' : IsBinaryRootedNetwork M')
    (hl' : M'.IsLSANetwork) (hX : Nontrivial X) (ht : ∀ e, ¬ M.IsHybridArc e)
    (ht' : ∀ e, ¬ M'.IsHybridArc e) {θ : MetricData E} (hθ : M.IsMetric θ) {θ' : MetricData E'}
    (hθ' : M'.IsMetric θ')
    (φ : SDMetricIso (unrooted M hM hX) (unrootedMetric M hM hX θ) (unrooted M' hM' hX)
      (unrootedMetric M' hM' hX θ')) :
    (treeSpeciesTree M hM.1 ht hθ).SameUnrootedMetricTree (treeSpeciesTree M' hM'.1 ht' hθ') := by
  refine ⟨?_, fun A _ _ _ => ?_⟩
  · ext A
    simp only [treeSpeciesTree_clusters]
    rw [mem_unroot_treeClusters_iff_exists_cutAt hM ht,
      mem_unroot_treeClusters_iff_exists_cutAt hM' ht',
      exists_cutAt_iff_exists_unrooted hM hl hX, exists_cutAt_iff_exists_unrooted hM' hl' hX]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨φ.edge g, (φ.cutAt_iff g _).2 hg⟩
    · rintro ⟨g', hg'⟩
      obtain ⟨g, rfl⟩ := φ.edge.surjective g'
      exact ⟨g, (φ.cutAt_iff g _).1 hg'⟩
  · rw [unrootedLength_eq_cutLength hM hl hX ht hθ, unrootedLength_eq_cutLength hM' hl' hX ht' hθ',
      φ.cutLength_eq]

end Banos2019
