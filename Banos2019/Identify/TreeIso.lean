module

public import Banos2019.External.SempleSteel2003.Quartets
public import Banos2019.Structure
public import Banos2019.Network.SuppressIso
public import Banos2019.Network.Suppress
public import Phylogenetics.Graph.Tree
public import Phylogenetics.Tree.SplitsEquivalence

/-!
# Trees, suppression and contraction of semidirected networks

General facts on graphs used by the base case of Theorem 4 (Baños 2019, Section 8).

* Multigraph trees (`DirectedMultigraph.IsTree`) and their simple graphs: no loops or parallel
  edges, the two sides of an edge, degrees (`isTree_ncard_neighborSet`). An isomorphism of the
  simple graphs of two multigraph trees without hybrid edges, fixing the taxa, is an isomorphism of
  the semidirected networks (`nonempty_sdIso_of_iso`).
* `X`-trees (`SplitsEquivalence.IsXTree`) with leaves labelled injectively resolve every set of
  four taxa when the other nodes have degree three (`exists_displays_splitFinset`): the splits
  (`External.SempleSteel2003.splitFinset`) display a quartet tree on it.
* Suppressing the nodes of degree two of a multigraph tree without hybrid edges: every edge is on a
  chain (`exists_isChain_mem`); the result is a multigraph tree (`suppress_isTree`) with the same
  degrees (`degree_suppress`), an `X`-tree (`suppress_xTree`) whose sides of edges are sides of
  edges of the tree (`suppress_splitSides`).
* Contracting all cycles of a connected network gives a multigraph tree (`contract_isTree`) with the
  sides of the edges of the network (`contract_walks_compl_iff`); when the cycles share no node, its
  degrees are those of `contract_degrees`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace Banos2019

section MultigraphTree

variable {V E : Type*} {G : DirectedMultigraph V E}

/-- An edge of a multigraph tree is not a loop. -/
theorem isTree_source_ne_target (hG : G.IsTree) (e : E) : G.source e ≠ G.target e := by
  intro h
  refine hG.2 e ?_
  rw [h]
  exact .refl

/-- Two edges of a multigraph tree with the same ends are the same edge. -/
theorem isTree_eq_of_joins (hG : G.IsTree) {e e' : E} {u w : V} (he : Joins G e u w)
    (he' : Joins G e' u w) : e = e' := by
  by_contra hne
  have hw : G.Walks {e}ᶜ u w := .single ⟨e', fun h => hne h.symm, he'⟩
  rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hG.2 e (h₁ ▸ h₂ ▸ hw)
  · exact hG.2 e (h₁ ▸ h₂ ▸ G.walks_symm hw)

/-- In a connected multigraph, every node is joined to one end of an edge without the edge. -/
theorem walks_compl_or_of_isConnected (hG : G.IsConnected) (e : E) (w : V) :
    G.Walks {e}ᶜ (G.source e) w ∨ G.Walks {e}ᶜ (G.target e) w := by
  have hw := hG (G.source e) w
  induction hw with
  | refl => exact Or.inl .refl
  | @tail b c _ hst ih =>
    obtain ⟨f, -, hf⟩ := hst
    by_cases hfe : f = e
    · subst hfe
      rcases hf with ⟨-, h₂⟩ | ⟨h₁, -⟩
      · exact Or.inr (h₂ ▸ .refl)
      · exact Or.inl (h₁ ▸ .refl)
    · exact ih.imp (fun h => h.tail ⟨f, hfe, hf⟩) (fun h => h.tail ⟨f, hfe, hf⟩)

/-- In a multigraph tree, every node is joined to one end of an edge without the edge. -/
theorem isTree_walks_or (hG : G.IsTree) (e : E) (w : V) :
    G.Walks {e}ᶜ (G.source e) w ∨ G.Walks {e}ᶜ (G.target e) w :=
  walks_compl_or_of_isConnected hG.1 e w

/-- An edge joins the nodes adjacent in the simple graph of a multigraph. -/
theorem exists_joins_of_toSimpleGraph_adj {a b : V} (h : G.toSimpleGraph.Adj a b) :
    ∃ e, Joins G e a b := by
  rw [DirectedMultigraph.toSimpleGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨e, h₁, h₂⟩ | ⟨e, h₁, h₂⟩
  · exact ⟨e, Or.inl ⟨h₁, h₂⟩⟩
  · exact ⟨e, Or.inr ⟨h₁, h₂⟩⟩

/-- Distinct nodes joined by an edge are adjacent in the simple graph. -/
theorem toSimpleGraph_adj_of_joins {e : E} {a b : V} (h : Joins G e a b) (hab : a ≠ b) :
    G.toSimpleGraph.Adj a b := by
  rw [DirectedMultigraph.toSimpleGraph, SimpleGraph.fromRel_adj]
  refine ⟨hab, ?_⟩
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨e, h₁, h₂⟩
  · exact Or.inr ⟨e, h₁, h₂⟩

/-- **Removing an edge of a multigraph tree**: the simple graph without the pair of its ends has the
walks of the multigraph without the edge. -/
theorem isTree_reachable_deleteEdges_iff (hG : G.IsTree) (e : E) {a b : V} :
    (G.toSimpleGraph.deleteEdges {s(G.source e, G.target e)}).Reachable a b ↔
      G.Walks {e}ᶜ a b := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    refine Relation.ReflTransGen.mono ?_ _ _ h
    intro c d hcd
    rw [SimpleGraph.deleteEdges_adj] at hcd
    obtain ⟨f, hf⟩ := exists_joins_of_toSimpleGraph_adj hcd.1
    refine ⟨f, fun hfe => hcd.2 ?_, hf⟩
    rw [Set.mem_singleton_iff] at hfe
    subst hfe
    rcases hf with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]; exact Set.mem_singleton _
    · rw [h₁, h₂]; exact Sym2.eq_swap
  · intro h
    induction h with
    | refl => exact .refl _
    | @tail c d _ hcd ih =>
      obtain ⟨f, hf, hj⟩ := hcd
      by_cases hc : c = d
      · exact hc ▸ ih
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨toSimpleGraph_adj_of_joins hj hc, fun hs => hf ?_⟩
      rw [Set.mem_singleton_iff] at hs ⊢
      refine isTree_eq_of_joins hG hj ?_
      rcases Sym2.eq_iff.1 hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁.symm, h₂.symm⟩
      · exact Or.inr ⟨h₂.symm, h₁.symm⟩

/-- **The neighbours of a node of a multigraph tree** in its simple graph are as many as the edges
at the node. -/
theorem isTree_ncard_neighborSet [Finite E] (hG : G.IsTree) (u : V) :
    (G.toSimpleGraph.neighborSet u).ncard = degree G u := by
  classical
  set I : Set E := {e | G.source e = u ∨ G.target e = u}
  let o : E → V := fun e => if G.source e = u then G.target e else G.source e
  have hj : ∀ e ∈ I, Joins G e u (o e) := by
    intro e he
    by_cases hs : G.source e = u
    · exact Or.inl ⟨hs, by simp [o, hs]⟩
    · exact Or.inr ⟨by simp [o, hs], he.resolve_left hs⟩
  have hinj : Set.InjOn o I := by
    intro e he e' he' h
    exact isTree_eq_of_joins hG (hj e he) (h ▸ hj e' he')
  have himg : o '' I = G.toSimpleGraph.neighborSet u := by
    ext w
    constructor
    · rintro ⟨e, he, rfl⟩
      refine toSimpleGraph_adj_of_joins (hj e he) fun h => isTree_source_ne_target hG e ?_
      rcases hj e he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂, h]
      · rw [h₁, h₂, h]
    · intro hw
      obtain ⟨e, he⟩ := exists_joins_of_toSimpleGraph_adj hw
      have heI : e ∈ I := by
        rcases he with ⟨h₁, -⟩ | ⟨-, h₂⟩
        · exact Or.inl h₁
        · exact Or.inr h₂
      refine ⟨e, heI, ?_⟩
      have := hj e heI
      rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases this with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
      · rw [← k₂, h₂]
      · exact absurd (h₁.trans k₂.symm) (isTree_source_ne_target hG e)
      · exact absurd (k₁.trans h₂.symm) (isTree_source_ne_target hG e)
      · rw [← k₁, h₁]
  rw [← himg, hinj.ncard_image]
  have hI : I = {e | G.target e = u} ∪ {e | G.source e = u} := by
    ext e
    simp only [I, Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [hI, Set.ncard_union_eq]
  · rfl
  · rw [Set.disjoint_left]
    intro e h₁ h₂
    exact isTree_source_ne_target hG e (h₂.trans h₁.symm)

end MultigraphTree

section IsoOfGraph

variable {V E V' E' X : Type*}

/-- The two ends of an edge, read in two ways, are the same pair. -/
theorem joins_unique {G : DirectedMultigraph V E} {e : E} {a b c d : V} (h : Joins G e a b)
    (h' : Joins G e c d) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases h' with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
  · exact Or.inl ⟨h₁.symm.trans k₁, h₂.symm.trans k₂⟩
  · exact Or.inr ⟨h₁.symm.trans k₁, h₂.symm.trans k₂⟩
  · exact Or.inr ⟨h₂.symm.trans k₂, h₁.symm.trans k₁⟩
  · exact Or.inl ⟨h₂.symm.trans k₂, h₁.symm.trans k₁⟩

/-- **An isomorphism of the simple graphs of two multigraph trees without hybrid edges**, fixing the
taxa, is an isomorphism of the semidirected networks: each edge goes to the edge joining the images
of its ends. -/
theorem nonempty_sdIso_of_iso {G : SemidirectedNetwork V E X} {G' : SemidirectedNetwork V' E' X}
    (hG : G.graph.IsTree) (hG' : G'.graph.IsTree) (hd : ∀ e, ¬ G.IsDirected e)
    (hd' : ∀ e, ¬ G'.IsDirected e) (f : G.graph.toSimpleGraph ≃g G'.graph.toSimpleGraph)
    (hf : ∀ x, f (G.leaf x) = G'.leaf x) : Nonempty (SDIso G G') := by
  have hex : ∀ e, ∃ e', Joins G'.graph e' (f (G.graph.source e)) (f (G.graph.target e)) := fun e =>
    exists_joins_of_toSimpleGraph_adj (f.map_adj_iff.2
      (toSimpleGraph_adj_of_joins (Or.inl ⟨rfl, rfl⟩) (isTree_source_ne_target hG e)))
  choose m hm using hex
  have hbij : Function.Bijective m := by
    constructor
    · intro e₁ e₂ h
      have h₂ := hm e₂
      rw [← h] at h₂
      refine isTree_eq_of_joins hG (Or.inl ⟨rfl, rfl⟩) ?_
      rcases joins_unique (hm e₁) h₂ with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩
      · exact Or.inl ⟨f.injective k₁.symm, f.injective k₂.symm⟩
      · exact Or.inr ⟨f.injective k₂.symm, f.injective k₁.symm⟩
    · intro e'
      obtain ⟨e, he⟩ := exists_joins_of_toSimpleGraph_adj (f.symm.map_adj_iff.2
        (toSimpleGraph_adj_of_joins (Or.inl ⟨rfl, rfl⟩) (isTree_source_ne_target hG' e')))
      refine ⟨e, isTree_eq_of_joins hG' (hm e) ?_⟩
      rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂, RelIso.apply_symm_apply, RelIso.apply_symm_apply]
        exact Or.inl ⟨rfl, rfl⟩
      · rw [h₁, h₂, RelIso.apply_symm_apply, RelIso.apply_symm_apply]
        exact Or.inr ⟨rfl, rfl⟩
  exact ⟨{ vert := f.toEquiv
           edge := Equiv.ofBijective m hbij
           isDirected_iff := fun e => iff_of_false (hd' _) (hd e)
           joins := fun e => hm e
           directed := fun e he => absurd he (hd e)
           leaf := fun x => (hf x).symm }⟩

end IsoOfGraph

section XTreeSplits

open SplitsEquivalence External.SempleSteel2003

variable {W X : Type*} {T : SimpleGraph W} {φ : X → W}

/-- A side of a split of `T` meeting the set `q` of four taxa in two taxa gives a quartet tree on
`q` displayed by the splits of `T`. -/
theorem exists_displays_of_side [Fintype X] [DecidableEq X] {q : Finset X} (hq : #q = 4)
    {A : Set X} (hA : A ∈ splitSides T φ) {y₁ y₂ : X} (hy₁ : y₁ ∈ q) (hy₂ : y₂ ∈ q)
    (hne : y₁ ≠ y₂) (hmem : ∀ y ∈ q, y ∈ A ↔ y = y₁ ∨ y = y₂) :
    ∃ s ∈ treesOn q, Displays (splitFinset T φ) s := by
  set A' := (Set.toFinite A).toFinset
  have hA' : A' ∈ splitFinset T φ := by
    rw [mem_splitFinset, Set.Finite.coe_toFinset]
    exact hA
  have hinter : A' ∩ q = {y₁, y₂} := by
    ext y
    rw [Finset.mem_inter, Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, hq⟩
      exact (hmem y hq).1 h
    · rintro (rfl | rfl)
      · exact ⟨(hmem _ hy₁).2 (Or.inl rfl), hy₁⟩
      · exact ⟨(hmem _ hy₂).2 (Or.inr rfl), hy₂⟩
  have h2 : (A' ∩ q).card = 2 := by rw [hinter, Finset.card_pair hne]
  exact ⟨_, by simp [mem_treesOn], displays_quartetOfCherry hA' hq h2⟩

/-- **Every set of four taxa is resolved** by a tree whose leaves are labelled injectively and whose
other nodes have at most three neighbours. Going from a taxon `a` toward the other three, take the
last edge `uv` with the three beyond `v`: `v` is not a leaf, and its two other branches cannot hold
all three, so they divide them two and one. -/
theorem exists_displays_splitFinset [Fintype X] [DecidableEq X] [Finite W] (hX : IsXTree T φ)
    (hinj : Function.Injective φ) (hleaf : ∀ x, (T.neighborSet (φ x)).ncard = 1)
    (hdeg : ∀ v, v ∉ Set.range φ → (T.neighborSet v).ncard ≤ 3) {q : Finset X} (hq : #q = 4) :
    ∃ s ∈ treesOn q, Displays (splitFinset T φ) s := by
  have hT := hX.isTree
  obtain ⟨a, ha⟩ : q.Nonempty := card_pos.1 (by omega)
  obtain ⟨b, c, d, hbc, hbd, hcd, hB⟩ := card_eq_three.1
    (show #(q.erase a) = 3 by rw [card_erase_of_mem ha, hq])
  have hq' : ∀ y, y ∈ q ↔ y = a ∨ y = b ∨ y = c ∨ y = d := by
    intro y
    by_cases hya : y = a
    · subst hya
      simp [ha]
    · have : y ∈ q ↔ y ∈ q.erase a := by simp [hya]
      rw [this, hB]
      simp [hya]
  have hab : b ≠ a := fun h => by simpa [h] using (hB ▸ (by simp : b ∈ ({b, c, d} : Finset X)) :
    b ∈ q.erase a)
  have hac : c ≠ a := fun h => by simpa [h] using (hB ▸ (by simp : c ∈ ({b, c, d} : Finset X)) :
    c ∈ q.erase a)
  have had : d ≠ a := fun h => by simpa [h] using (hB ▸ (by simp : d ∈ ({b, c, d} : Finset X)) :
    d ∈ q.erase a)
  have hbq : b ∈ q := (hq' b).2 (Or.inr (Or.inl rfl))
  have hcq : c ∈ q := (hq' c).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hdq : d ∈ q := (hq' d).2 (Or.inr (Or.inr (Or.inr rfl)))
  -- the claim for an edge `uv` with `a` on the side of `u` and `b, c, d` on that of `v`
  suffices key : ∀ m : ℕ, ∀ u v, T.Adj u v → (T.deleteEdges {s(u, v)}).Reachable u (φ a) →
      (T.deleteEdges {s(u, v)}).Reachable v (φ b) → (T.deleteEdges {s(u, v)}).Reachable v (φ c) →
      (T.deleteEdges {s(u, v)}).Reachable v (φ d) →
      {z | (T.deleteEdges {s(u, v)}).Reachable v z}.ncard = m →
      ∃ s ∈ treesOn q, Displays (splitFinset T φ) s by
    obtain ⟨n, hn⟩ := Set.ncard_eq_one.1 (hleaf a)
    have hadj : T.Adj (φ a) n := by
      have : n ∈ T.neighborSet (φ a) := by rw [hn]; exact Set.mem_singleton _
      exact this
    have hfar : ∀ y, y ≠ a → (T.deleteEdges {s(φ a, n)}).Reachable n (φ y) := fun y hy =>
      (reachable_deleteEdges_or hT.1 (φ a) n (φ y)).resolve_left fun h =>
        hy (hinj (eq_of_reachable_deleteEdges_of_ncard_eq_one (hleaf a) hadj h))
    exact key _ _ _ hadj (.refl _) (hfar b hab) (hfar c hac) (hfar d had) rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro u v huv hua hvb hvc hvd hm
  have hnr : ¬ (T.deleteEdges {s(u, v)}).Reachable u v := not_reachable_deleteEdges hT.2 huv
  -- `v` is not a leaf
  have hv : v ∉ Set.range φ := by
    rintro ⟨z, rfl⟩
    have hw : (T.neighborSet (φ z)).ncard = 1 := hleaf z
    have hs : s(u, φ z) = s(φ z, u) := Sym2.eq_swap
    rw [hs] at hvb hvc
    exact hbc (hinj ((eq_of_reachable_deleteEdges_of_ncard_eq_one hw huv.symm hvb).trans
      (eq_of_reachable_deleteEdges_of_ncard_eq_one hw huv.symm hvc).symm))
  -- the branch at `v` toward each of `b, c, d`
  have hbr : ∀ y, (T.deleteEdges {s(u, v)}).Reachable v (φ y) →
      ∃ n, T.Adj v n ∧ n ≠ u ∧ (T.deleteEdges {s(v, n)}).Reachable n (φ y) := by
    intro y hy
    have hne : v ≠ φ y := fun h => hv ⟨y, h.symm⟩
    obtain ⟨n, hn, hny⟩ := exists_adj_reachable_deleteEdges hT.1 hne
    refine ⟨n, hn, ?_, hny⟩
    rintro rfl
    rw [Sym2.eq_swap] at hny
    exact hnr (hny.trans hy.symm)
  obtain ⟨nb, hnb, hnbu, hb⟩ := hbr b hvb
  obtain ⟨nc, hnc, hncu, hc⟩ := hbr c hvc
  obtain ⟨nd, hnd, hndu, hd⟩ := hbr d hvd
  -- `a` is on the branch toward `u`
  have hua' : (T.deleteEdges {s(v, u)}).Reachable u (φ a) := by rw [Sym2.eq_swap]; exact hua
  -- two taxa on one branch, the third on another: the split of that branch
  have sep : ∀ {y₁ y₂ y₃ : X} {n₁ n₃ : W}, y₁ ∈ q → y₂ ∈ q → y₁ ≠ y₂ →
      (∀ y ∈ q, y = a ∨ y = y₁ ∨ y = y₂ ∨ y = y₃) → T.Adj v n₁ → T.Adj v n₃ → n₁ ≠ n₃ →
      n₁ ≠ u → (T.deleteEdges {s(v, n₁)}).Reachable n₁ (φ y₁) →
      (T.deleteEdges {s(v, n₁)}).Reachable n₁ (φ y₂) →
      (T.deleteEdges {s(v, n₃)}).Reachable n₃ (φ y₃) →
      ∃ s ∈ treesOn q, Displays (splitFinset T φ) s := by
    intro y₁ y₂ y₃ n₁ n₃ hy₁ hy₂ hne hall hn₁ hn₃ h13 h1u r₁ r₂ r₃
    refine exists_displays_of_side hq (A := sideOf T φ s(v, n₁) n₁) ⟨s(v, n₁), hn₁, y₁, ?_⟩
      hy₁ hy₂ hne fun y hy => ?_
    · rw [edgeSide_eq_sideOf]
      exact sideOf_eq_of_reachable r₁
    constructor
    · intro hyA
      rcases hall y hy with rfl | rfl | rfl | rfl
      · exact absurd hyA (not_reachable_branch hT huv.symm hn₁ (Ne.symm h1u) hua')
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hyA (not_reachable_branch hT hn₃ hn₁ (Ne.symm h13) r₃)
    · rintro (rfl | rfl)
      · exact r₁
      · exact r₂
  have hall : ∀ {y₁ y₂ y₃ : X}, ({y₁, y₂, y₃} : Finset X) = {b, c, d} →
      ∀ y ∈ q, y = a ∨ y = y₁ ∨ y = y₂ ∨ y = y₃ := by
    intro y₁ y₂ y₃ h y hy
    rcases (hq' y).1 hy with h' | h'
    · exact Or.inl h'
    · right
      have : y ∈ ({y₁, y₂, y₃} : Finset X) := by
        rw [h]
        simpa using h'
      simpa using this
  by_cases h₁ : nb = nc
  · subst h₁
    by_cases h₂ : nd = nb
    · subst h₂
      -- all three on one branch: go one edge further
      have hvn : (T.deleteEdges {s(v, nd)}).Reachable v (φ a) := by
        have hstep : (T.deleteEdges {s(v, nd)}).Adj v u :=
          deleteEdges_adj_of_ne huv.symm fun h => by
            rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨-, h⟩
            · exact hndu h.symm
            · exact huv.ne h
        exact hstep.reachable.trans
          (reachable_deleteEdges_of_not_reachable (c := v) (by simp) hnr hua)
      have hnrv : ¬ (T.deleteEdges {s(v, nd)}).Reachable nd v := fun h =>
        not_reachable_deleteEdges hT.2 hnd h.symm
      have hsub : ∀ {z}, (T.deleteEdges {s(v, nd)}).Reachable nd z →
          (T.deleteEdges {s(u, v)}).Reachable v z := by
        intro z hz
        have hstep : (T.deleteEdges {s(u, v)}).Adj v nd :=
          deleteEdges_adj_of_ne hnd fun h => by
            rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
            · exact huv.ne h.symm
            · exact hndu h
        exact hstep.reachable.trans
          (reachable_deleteEdges_of_not_reachable (c := v) (by simp) hnrv hz)
      have hlt : {z | (T.deleteEdges {s(v, nd)}).Reachable nd z}.ncard < m := by
        rw [← hm]
        refine Set.ncard_lt_ncard ⟨fun z hz => hsub hz, fun h => ?_⟩ (Set.toFinite _)
        exact hnrv (h (show (T.deleteEdges {s(u, v)}).Reachable v v from .refl _))
      exact ih _ hlt v nd hnd hvn hb hc hd rfl
    · exact sep hbq hcq hbc (hall rfl) hnb hnd (Ne.symm h₂) hnbu hb hc hd
  · by_cases h₂ : nd = nb
    · subst h₂
      exact sep hbq hdq hbd (hall (by ext; simp; tauto)) hnd hnc h₁ hnbu hb hd hc
    · by_cases h₃ : nd = nc
      · subst h₃
        exact sep hcq hdq hcd (hall (by ext; simp; tauto)) hnd hnb (Ne.symm h₁) hncu hc hd hb
      · -- four distinct neighbours of `v`
        exfalso
        have h4 : ({u, nb, nc, nd} : Set W).ncard = 4 := by
          have e1 : u ∉ ({nb, nc, nd} : Set W) := by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨Ne.symm hnbu, Ne.symm hncu, Ne.symm hndu⟩
          have e2 : nb ∉ ({nc, nd} : Set W) := by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨h₁, fun h => h₂ h.symm⟩
          rw [Set.ncard_insert_of_notMem e1, Set.ncard_insert_of_notMem e2,
            Set.ncard_pair fun h => h₃ h.symm]
        have := Set.ncard_le_ncard (show ({u, nb, nc, nd} : Set W) ⊆ T.neighborSet v by
          rintro z (rfl | rfl | rfl | rfl)
          · exact huv.symm
          · exact hnb
          · exact hnc
          · exact hnd) (Set.toFinite _)
        have := hdeg v hv
        omega

end XTreeSplits

section SuppressTree

variable {V E X : Type*}

/-- A path read backwards. -/
theorem IsPathOf.rev {G : DirectedMultigraph V E} {F : Set E} {n : ℕ} {p : Fin (n + 1) → V}
    {q : Fin n → E} (h : IsPathOf G F n p q) : IsPathOf G F n (p ∘ Fin.rev) (q ∘ Fin.rev) where
  mem i := h.mem _
  link i := by
    have := h.link (Fin.rev i)
    simp only [Function.comp_apply, Fin.rev_castSucc, Fin.rev_succ]
    exact Or.symm this
  injective := h.injective.comp Fin.rev_injective

/-- The part of a sequence of edges joining consecutive nodes between two of its nodes is a walk on
those edges. -/
theorem walks_of_joins_le {G : DirectedMultigraph V E} {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    (hj : ∀ i : Fin k, Joins G (e i) (p i.castSucc) (p i.succ)) {i j : Fin (k + 1)} (hij : i ≤ j) :
    G.Walks {f | ∃ l : Fin k, (i : ℕ) ≤ l ∧ (l : ℕ) < j ∧ e l = f} (p i) (p j) := by
  suffices ∀ d : ℕ, ∀ j : Fin (k + 1), (j : ℕ) = i + d →
      G.Walks {f | ∃ l : Fin k, (i : ℕ) ≤ l ∧ (l : ℕ) < j ∧ e l = f} (p i) (p j) from
    this _ j (Nat.add_sub_cancel' hij).symm
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [show j = i from Fin.ext (by simpa using hj)]
    exact .refl
  | succ d ih =>
    intro j hj'
    have hjn : (j : ℕ) - 1 < k := by have := j.isLt; omega
    obtain ⟨l, hl⟩ : ∃ l : Fin k, (l : ℕ) = j - 1 := ⟨⟨j - 1, hjn⟩, rfl⟩
    have hl₁ : l.castSucc = ⟨i + d, by have := j.isLt; omega⟩ := Fin.ext (by simp; omega)
    have hl₂ : l.succ = j := Fin.ext (by simp; omega)
    have hw := ih ⟨i + d, by have := j.isLt; omega⟩ rfl
    refine Relation.ReflTransGen.tail (walks_mono (fun f hf => ?_) hw) ?_
    · obtain ⟨l', h₁, h₂, h₃⟩ := hf
      exact ⟨l', h₁, by simp only at h₂; omega, h₃⟩
    · refine ⟨e l, ⟨l, by omega, by omega, rfl⟩, ?_⟩
      have := hj l
      rw [hl₁, hl₂] at this
      exact this

/-- At a node of degree two, an edge that is not a loop has another edge beside it. -/
theorem exists_ne_incident_of_degree_eq_two [Finite E] {G : DirectedMultigraph V E} {u : V}
    (hu : degree G u = 2) {e : E} (hloop : G.source e ≠ G.target e)
    (he : G.source e = u ∨ G.target e = u) :
    ∃ g, g ≠ e ∧ (G.source g = u ∨ G.target g = u) := by
  by_contra h
  push Not at h
  have hs : {g | G.source g = u} ⊆ {e} := fun g hg => by
    by_contra hne
    exact (h g hne).1 hg
  have ht : {g | G.target g = u} ⊆ {e} := fun g hg => by
    by_contra hne
    exact (h g hne).2 hg
  unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree at hu
  have h1 := Set.ncard_le_ncard hs (Set.toFinite _)
  have h2 := Set.ncard_le_ncard ht (Set.toFinite _)
  rw [Set.ncard_singleton] at h1 h2
  rcases he with he | he
  · have : {g | G.target g = u} = ∅ := Set.eq_empty_of_forall_notMem fun g hg => by
      have := ht hg
      rw [Set.mem_singleton_iff] at this
      subst this
      exact hloop (he.trans hg.symm)
    rw [this, Set.ncard_empty] at hu
    omega
  · have : {g | G.source g = u} = ∅ := Set.eq_empty_of_forall_notMem fun g hg => by
      have := hs hg
      rw [Set.mem_singleton_iff] at this
      subst this
      exact hloop (hg.trans he.symm)
    rw [this, Set.ncard_empty] at hu
    omega

variable {K : SemidirectedNetwork V E X}

/-- **Every edge of a multigraph tree lies on a chain**: a longest path through suppressed nodes
containing it ends at kept nodes, since a suppressed node has a second edge, which leads to a new
node in a tree. -/
theorem exists_isChain_mem [Finite V] [Finite E] (hK : K.graph.IsTree) (P : Set V) (g : E) :
    ∃ c, IsChain K P c ∧ g ∈ c := by
  -- extending a path through suppressed nodes at its last node
  have hext : ∀ (n k : ℕ) (p : Fin (k + 1) → V) (e : Fin k → E), Nat.card V - k = n → 0 < k →
      IsPathOf K.graph Set.univ k p e →
      (∀ i : Fin (k + 1), i ≠ 0 → i ≠ Fin.last k → ¬ IsBranch K P (p i)) → g ∈ Set.range e →
      ∃ (k' : ℕ) (p' : Fin (k' + 1) → V) (e' : Fin k' → E), 0 < k' ∧
        IsPathOf K.graph Set.univ k' p' e' ∧
        (∀ i : Fin (k' + 1), i ≠ 0 → i ≠ Fin.last k' → ¬ IsBranch K P (p' i)) ∧
        g ∈ Set.range e' ∧ p' 0 = p 0 ∧ IsBranch K P (p' (Fin.last k')) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro k p e hn hk hP hin hg
    by_cases hb : IsBranch K P (p (Fin.last k))
    · exact ⟨k, p, e, hk, hP, hin, hg, rfl, hb⟩
    have hdeg : degree K.graph (p (Fin.last k)) = 2 := by
      by_contra h
      exact hb (Or.inl h)
    obtain ⟨j, hj⟩ : ∃ j : Fin k, j.succ = Fin.last k :=
      ⟨⟨k - 1, by omega⟩, Fin.ext (by simp; omega)⟩
    have hinc : K.graph.source (e j) = p (Fin.last k) ∨ K.graph.target (e j) = p (Fin.last k) := by
      rcases hP.link j with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr (hj ▸ h)
      · exact Or.inl (hj ▸ h)
    obtain ⟨f, hfe, hf⟩ :=
      exists_ne_incident_of_degree_eq_two hdeg (isTree_source_ne_target hK (e j)) hinc
    -- the other end `z` of `f`
    set z := if K.graph.source f = p (Fin.last k) then K.graph.target f else K.graph.source f
      with hz_def
    have hfz : (K.graph.source f = p (Fin.last k) ∧ K.graph.target f = z) ∨
        (K.graph.source f = z ∧ K.graph.target f = p (Fin.last k)) := by
      by_cases hs : K.graph.source f = p (Fin.last k)
      · exact Or.inl ⟨hs, by simp [z, hs]⟩
      · exact Or.inr ⟨by simp [z, hs], hf.resolve_left hs⟩
    -- `f` is not on the path
    have hfP : f ∉ Set.range e := by
      rintro ⟨l, rfl⟩
      rcases hP.eq_or_eq_of_end l hf with h | h
      · have := congrArg Fin.val (hP.injective h)
        simp at this
        omega
      · apply hfe
        congr 1
        have h' := hP.injective h
        exact Fin.succ_injective _ (h'.symm.trans hj.symm)
    -- `z` is a new node, else `f` closes a cycle with the path
    have hz : z ∉ Set.range p := by
      rintro ⟨i, hi⟩
      have hw : K.graph.Walks {f}ᶜ (p i) (p (Fin.last k)) := by
        refine walks_mono (fun f' hf' => ?_) (hP.walks_of_le (Fin.le_last i))
        obtain ⟨l, -, -, rfl⟩ := hf'
        exact fun h => hfP ⟨l, h⟩
      apply hK.2 f
      rcases hfz with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂, ← hi]
        exact K.graph.walks_symm hw
      · rw [h₁, h₂, ← hi]
        exact hw
    have hP' := hP.snoc hz (Set.mem_univ f) hfz
    have hcard : k + 2 ≤ Nat.card V := by
      have := Nat.card_le_card_of_injective _ hP'.injective
      simp at this
      omega
    obtain ⟨k', p', e', hk', hP'', hin', hg', h0, hb'⟩ := ih (Nat.card V - (k + 1)) (by omega)
      (k + 1) _ _ rfl (by omega) hP' (fun i hi0 hil => by
        induction i using Fin.lastCases with
        | last => exact absurd rfl hil
        | cast i =>
          rw [Fin.snoc_castSucc]
          by_cases hil' : i = Fin.last k
          · subst hil'
            exact hb
          · exact hin i (fun h => hi0 (by rw [h]; rfl)) hil')
      (by
        obtain ⟨l, rfl⟩ := hg
        exact ⟨l.castSucc, Fin.snoc_castSucc (α := fun _ => E) ..⟩)
    refine ⟨k', p', e', hk', hP'', hin', hg', ?_, hb'⟩
    rw [h0]
    exact Fin.snoc_castSucc (α := fun _ => V) (i := 0) ..
  -- the edge `g` alone, extended at both ends
  have hg0 : IsPathOf K.graph Set.univ 1 ![K.graph.source g, K.graph.target g] ![g] := by
    refine ⟨fun _ => Set.mem_univ _, fun i => ?_, fun i j h => ?_⟩
    · fin_cases i
      exact Or.inl ⟨rfl, rfl⟩
    · fin_cases i <;> fin_cases j
      · rfl
      · exact absurd h (isTree_source_ne_target hK g)
      · exact absurd h.symm (isTree_source_ne_target hK g)
      · rfl
  obtain ⟨k₁, p₁, e₁, hk₁, hP₁, hin₁, hg₁, -, hb₁⟩ := hext _ 1 _ _ rfl one_pos hg0
    (fun i hi0 hil => by fin_cases i <;> simp_all) ⟨0, rfl⟩
  obtain ⟨k₂, p₂, e₂, hk₂, hP₂, hin₂, hg₂, h0₂, hb₂⟩ := hext _ k₁ _ _ rfl hk₁ hP₁.rev
    (fun i hi0 hil => hin₁ (Fin.rev i)
      (fun h' => hil (by rw [← Fin.rev_rev i, h', Fin.rev_zero]))
      (fun h' => hi0 (by rw [← Fin.rev_rev i, h', Fin.rev_last])))
    (by
      obtain ⟨l, rfl⟩ := hg₁
      exact ⟨Fin.rev l, by simp⟩)
  refine ⟨Set.range e₂, ⟨k₂, p₂, e₂, ⟨hk₂, fun i => hP₂.link i, hin₂, ⟨?_, hb₂⟩,
    hP₂.injective_edge⟩, rfl⟩, hg₂⟩
  rw [h0₂]
  simpa using hb₁

/-- In a multigraph without loops, the degree counts the edges at the node. -/
theorem degree_eq_ncard_incident [Finite E] {G : DirectedMultigraph V E}
    (hloop : ∀ e, G.source e ≠ G.target e) (u : V) :
    degree G u = {e | G.source e = u ∨ G.target e = u}.ncard := by
  have hI : {e | G.source e = u ∨ G.target e = u} =
      {e | G.target e = u} ∪ {e | G.source e = u} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [hI, Set.ncard_union_eq]
  · rfl
  · rw [Set.disjoint_left]
    intro e h₁ h₂
    exact hloop e (h₂.trans h₁.symm)

/-- In a chain, an edge at a kept node is the first edge, at the first node, or the last edge, at
the last node. -/
theorem IsChainOf.val_of_incident {P : Set V} {k : ℕ} {p : Fin (k + 1) → V} {e : Fin k → E}
    (h : IsChainOf K P k p e) {w : V} (hw : IsBranch K P w)
    {i : Fin k} (hi : K.graph.source (e i) = w ∨ K.graph.target (e i) = w) :
    (w = p 0 ∧ (i : ℕ) = 0) ∨ (w = p (Fin.last k) ∧ (i : ℕ) = k - 1) := by
  have hb : ∀ j : Fin (k + 1), p j = w → j = 0 ∨ j = Fin.last k := by
    intro j hj
    by_contra hn
    push Not at hn
    exact h.inner j hn.1 hn.2 (hj ▸ hw)
  rcases h.eq_of_incident hi with hw' | hw'
  · rcases hb _ hw'.symm with h0 | hl
    · left
      refine ⟨hw'.trans (by rw [h0]), ?_⟩
      simpa using congrArg Fin.val h0
    · exact absurd hl (Fin.castSucc_ne_last i)
  · rcases hb _ hw'.symm with h0 | hl
    · exact absurd h0 (Fin.succ_ne_zero i)
    · right
      refine ⟨hw'.trans (by rw [hl]), ?_⟩
      have := congrArg Fin.val hl
      simp at this
      omega

variable (hdir : ∀ e, ¬ K.IsDirected e)
include hdir

/-- Without hybrid edges, no chain points toward its first node. -/
theorem not_pointsBackward_of_undirected {P : Set V} {c : Set E} (r : ChainRep K P c) :
    ¬ r.PointsBackward := fun h => by
  obtain ⟨⟨i, hi⟩, -⟩ := h
  exact hdir _ hi

/-- Without hybrid edges, the suppressed edge of a chain goes from its first node. -/
theorem suppress_source_val (c : {c : Set E // IsChain K ∅ c}) :
    ((suppress K).graph.source c).1 = (chainRep K ∅ c.2).p 0 := by
  simp [suppressExcept, not_pointsBackward_of_undirected hdir]

/-- Without hybrid edges, the suppressed edge of a chain goes to its last node. -/
theorem suppress_target_val (c : {c : Set E // IsChain K ∅ c}) :
    ((suppress K).graph.target c).1 = (chainRep K ∅ c.2).p (Fin.last _) := by
  simp [suppressExcept, not_pointsBackward_of_undirected hdir]

/-- Without hybrid edges, the suppressed network has no hybrid edges. -/
theorem suppress_not_isDirected (c : {c : Set E // IsChain K ∅ c}) : ¬ (suppress K).IsDirected c :=
  fun h => h.elim (fun ⟨⟨_, hi⟩, _⟩ => hdir _ hi) (fun ⟨⟨_, hi⟩, _⟩ => hdir _ hi)

omit hdir in
/-- A chain is a walk on its edges from its first node to its last. -/
theorem ChainRep.walks_ends {P : Set V} {c : Set E} (r : ChainRep K P c) :
    K.graph.Walks c (r.p 0) (r.p (Fin.last r.k)) := by
  refine walks_mono (fun f hf => ?_) (walks_of_joins_le r.isChainOf.joins (Fin.zero_le _))
  obtain ⟨l, -, -, rfl⟩ := hf
  exact (Set.ext_iff.1 r.range_eq (r.e l)).1 ⟨l, rfl⟩

/-- A walk of the suppressed network is a walk of the network on the edges of its chains. -/
theorem suppress_walks_val {F : Set {c : Set E // IsChain K ∅ c}} {S : Set E}
    (hFS : ∀ c ∈ F, c.1 ⊆ S) {u w : {u // IsBranch K ∅ u}}
    (h : (suppress K).graph.Walks F u w) : K.graph.Walks S u.1 w.1 := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hst ih =>
    obtain ⟨c, hc, hj⟩ := hst
    refine ih.trans ?_
    have hw := walks_mono (hFS c hc) (chainRep K ∅ c.2).walks_ends
    rw [← suppress_source_val hdir c, ← suppress_target_val hdir c] at hw
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at hw
      exact hw
    · rw [h₁, h₂] at hw
      exact K.graph.walks_symm hw

/-- A chain of the suppressed network, at a kept node of one of its edges, has that node as an
end. -/
theorem suppress_incident_of_mem (c : {c : Set E // IsChain K ∅ c}) {g : E} (hg : g ∈ c.1) {w : V}
    (hw : IsBranch K ∅ w) (hinc : K.graph.source g = w ∨ K.graph.target g = w) :
    (suppress K).graph.source c = ⟨w, hw⟩ ∨ (suppress K).graph.target c = ⟨w, hw⟩ := by
  have hmem : w ∈ chainEnds K ∅ c.1 := ⟨hw, g, hg, hinc⟩
  rw [← (chainRep K ∅ c.2).range_eq, (chainRep K ∅ c.2).isChainOf.chainEnds_eq] at hmem
  rcases hmem with h | h
  · left
    exact Subtype.ext ((suppress_source_val hdir c).trans h.symm)
  · right
    exact Subtype.ext ((suppress_target_val hdir c).trans (Set.mem_singleton_iff.1 h).symm)

omit hdir in
/-- The first edge of a chain of a multigraph tree does not close a walk from the last node to the
first. -/
theorem ChainRep.not_walks_last_first (hK : K.graph.IsTree) {P : Set V} {c : Set E}
    (r : ChainRep K P c) :
    ¬ K.graph.Walks {r.e ⟨0, r.isChainOf.pos⟩}ᶜ (r.p (Fin.last r.k)) (r.p 0) := by
  intro hw
  have hk := r.isChainOf.pos
  set i₀ : Fin r.k := ⟨0, hk⟩
  have hrest : K.graph.Walks {r.e i₀}ᶜ (r.p i₀.succ) (r.p (Fin.last r.k)) := by
    refine walks_mono (fun f hf => ?_) (walks_of_joins_le r.isChainOf.joins (Fin.le_last _))
    obtain ⟨l, hl₁, -, rfl⟩ := hf
    intro h
    have := r.isChainOf.injective_edge (Set.mem_singleton_iff.1 h)
    rw [this] at hl₁
    simp [i₀] at hl₁
  have h0 : i₀.castSucc = 0 := Fin.ext rfl
  apply hK.2 (r.e i₀)
  rcases r.isChainOf.joins i₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂, h0]
    exact K.graph.walks_symm (hrest.trans hw)
  · rw [h₁, h₂, h0]
    exact hrest.trans hw

/-- **Suppressing the nodes of degree two of a multigraph tree gives a multigraph tree.** -/
theorem suppress_isTree [Finite V] [Finite E] (hK : K.graph.IsTree) :
    (suppress K).graph.IsTree := by
  constructor
  · intro u₀ v₀
    set R := {u | (suppress K).graph.Walks Set.univ u₀ u}
    have hRc : ∀ c : {c : Set E // IsChain K ∅ c},
        (suppress K).graph.source c ∈ R ↔ (suppress K).graph.target c ∈ R := fun c =>
      ⟨fun h => h.tail ⟨c, trivial, Or.inl ⟨rfl, rfl⟩⟩,
        fun h => h.tail ⟨c, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩
    set S : Set V := {w | (∀ hw : IsBranch K ∅ w, (⟨w, hw⟩ : {u // IsBranch K ∅ u}) ∈ R) ∧
      ∀ g, (K.graph.source g = w ∨ K.graph.target g = w) → ∀ c : {c : Set E // IsChain K ∅ c},
        g ∈ c.1 → (suppress K).graph.source c ∈ R}
    have key : ∀ (g : E) (c : {c : Set E // IsChain K ∅ c}), g ∈ c.1 → ∀ w,
        (K.graph.source g = w ∨ K.graph.target g = w) →
        (w ∈ S ↔ (suppress K).graph.source c ∈ R) := by
      intro g c hg w hinc
      constructor
      · exact fun h => h.2 g hinc c hg
      · intro hc
        by_cases hw : IsBranch K ∅ w
        · have hwR : (⟨w, hw⟩ : {u // IsBranch K ∅ u}) ∈ R := by
            rcases suppress_incident_of_mem hdir c hg hw hinc with h | h
            · exact h ▸ hc
            · exact h ▸ (hRc c).1 hc
          refine ⟨fun _ => hwR, fun g' hinc' c' hg' => ?_⟩
          rcases suppress_incident_of_mem hdir c' hg' hw hinc' with h | h
          · exact h ▸ hwR
          · exact (hRc c').2 (h ▸ hwR)
        · refine ⟨fun h => absurd h hw, fun g' hinc' c' hg' => ?_⟩
          have hl : ChainLink K ∅ g g' := ⟨w, hw, hinc, hinc'⟩
          set r := chainRep K ∅ c.2
          obtain ⟨i, rfl⟩ : g ∈ Set.range r.e := by rw [r.range_eq]; exact hg
          have hg'c : g' ∈ c.1 := by rw [← r.range_eq]; exact r.isChainOf.mem_of_chainLink hl
          have : c = c' := Subtype.ext (c.2.eq_of_mem c'.2 hg'c hg')
          rw [← this]
          exact hc
    have hS : ∀ g, ¬ K.graph.Crosses g S := by
      intro g hcr
      obtain ⟨c, hc, hgc⟩ := exists_isChain_mem hK ∅ g
      have h₁ := key g ⟨c, hc⟩ hgc _ (Or.inl rfl)
      have h₂ := key g ⟨c, hc⟩ hgc _ (Or.inr rfl)
      rcases hcr with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact ht (h₂.2 (h₁.1 hs))
      · exact hs (h₁.2 (h₂.1 ht))
    have hu₀ : u₀.1 ∈ S := by
      refine ⟨fun _ => .refl, fun g hinc c hg => ?_⟩
      rcases suppress_incident_of_mem hdir c hg u₀.2 hinc with h | h
      · rw [h]
        exact .refl
      · exact (hRc c).2 (by rw [h]; exact .refl)
    exact ((K.graph.mem_iff_mem_of_walks (fun g _ => hS g) (hK.1 u₀.1 v₀.1)).1 hu₀).1 v₀.2
  · intro c hw
    set r := chainRep K ∅ c.2
    have hw' : K.graph.Walks c.1ᶜ (r.p 0) (r.p (Fin.last r.k)) := by
      have := suppress_walks_val hdir (F := {c}ᶜ) (S := c.1ᶜ) (fun c' hc' f hf hfc =>
        (hc' : c' ∉ ({c} : Set _)) (Set.mem_singleton_iff.2
          (Subtype.ext (c'.2.eq_of_mem c.2 hf hfc)))) hw
      rwa [suppress_source_val hdir, suppress_target_val hdir] at this
    have hsub : c.1ᶜ ⊆ {r.e ⟨0, r.isChainOf.pos⟩}ᶜ := by
      intro f hf h
      rw [Set.mem_singleton_iff.1 h] at hf
      exact hf ((Set.ext_iff.1 r.range_eq _).1 ⟨_, rfl⟩)
    exact r.not_walks_last_first hK (K.graph.walks_symm (walks_mono hsub hw'))

/-- **The degrees of the suppressed tree**: a kept node has as many chains as edges, each edge at it
being the first or the last edge of its chain. -/
theorem degree_suppress [Finite V] [Finite E] (hK : K.graph.IsTree) (u : {u // IsBranch K ∅ u}) :
    degree (suppress K).graph u = degree K.graph u.1 := by
  have hT := suppress_isTree hdir hK
  rw [degree_eq_ncard_incident (isTree_source_ne_target hT),
    degree_eq_ncard_incident (isTree_source_ne_target hK)]
  symm
  choose ch hch hmem using exists_isChain_mem hK (∅ : Set V)
  refine Set.ncard_congr (fun g _ => (⟨ch g, hch g⟩ : {c : Set E // IsChain K ∅ c})) ?_ ?_ ?_
  · intro g hg
    rcases suppress_incident_of_mem hdir ⟨ch g, hch g⟩ (hmem g) u.2 hg with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro g g' hg hg' heq
    have heq' : ch g = ch g' := congrArg Subtype.val heq
    set r := chainRep K ∅ (hch g)
    obtain ⟨i, hi⟩ : g ∈ Set.range r.e := by rw [r.range_eq]; exact hmem g
    obtain ⟨i', hi'⟩ : g' ∈ Set.range r.e := by rw [r.range_eq, heq']; exact hmem g'
    have hne : r.p 0 ≠ r.p (Fin.last r.k) := fun h => isTree_source_ne_target hT ⟨ch _, hch _⟩
      (Subtype.ext (by rw [suppress_source_val hdir, suppress_target_val hdir]; exact h))
    have h1 := r.isChainOf.val_of_incident u.2 (i := i) (by rw [hi]; exact hg)
    have h2 := r.isChainOf.val_of_incident u.2 (i := i') (by rw [hi']; exact hg')
    calc g = r.e i := hi.symm
      _ = r.e i' := by
        congr 1
        ext
        rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
        · omega
        · exact absurd (h1.symm.trans h2) hne
        · exact absurd (h2.symm.trans h1) hne
        · omega
      _ = g' := hi'
  · intro c hc
    set r := chainRep K ∅ c.2
    have hk := r.isChainOf.pos
    have hsame : ∀ g ∈ c.1, (⟨ch g, hch g⟩ : {c : Set E // IsChain K ∅ c}) = c := fun g hg =>
      Subtype.ext ((hch g).eq_of_mem c.2 (hmem g) hg)
    rcases hc with hc | hc
    · have hs : r.p 0 = u.1 := (suppress_source_val hdir c).symm.trans (congrArg Subtype.val hc)
      refine ⟨r.e ⟨0, hk⟩, ?_, hsame _ ((Set.ext_iff.1 r.range_eq _).1 ⟨_, rfl⟩)⟩
      have h0 : (⟨0, hk⟩ : Fin r.k).castSucc = 0 := Fin.ext rfl
      rcases r.isChainOf.joins ⟨0, hk⟩ with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact Or.inl (h₁.trans (by rw [h0, hs]))
      · exact Or.inr (h₂.trans (by rw [h0, hs]))
    · have ht : r.p (Fin.last r.k) = u.1 :=
        (suppress_target_val hdir c).symm.trans (congrArg Subtype.val hc)
      refine ⟨r.e ⟨r.k - 1, by omega⟩, ?_, hsame _ ((Set.ext_iff.1 r.range_eq _).1 ⟨_, rfl⟩)⟩
      have hl : (⟨r.k - 1, by omega⟩ : Fin r.k).succ = Fin.last r.k := Fin.ext (by simp; omega)
      rcases r.isChainOf.joins ⟨r.k - 1, by omega⟩ with ⟨-, h₂⟩ | ⟨h₁, -⟩
      · exact Or.inr (h₂.trans (by rw [hl, ht]))
      · exact Or.inl (h₁.trans (by rw [hl, ht]))

/-- **The side of an edge of the suppressed tree** is the side of the first edge of its chain: the
nodes reached from the first node of the chain without the chain are those reached without its first
edge. -/
theorem suppress_side [Finite V] [Finite E] (hK : K.graph.IsTree)
    (c : {c : Set E // IsChain K ∅ c}) :
    ∃ g a, (K.graph.source g = a ∨ K.graph.target g = a) ∧ ∀ w : {u // IsBranch K ∅ u},
      ((suppress K).graph.Walks {c}ᶜ ((suppress K).graph.source c) w ↔
        K.graph.Walks {g}ᶜ a w.1) := by
  have hT := suppress_isTree hdir hK
  set r := chainRep K ∅ c.2
  have hk := r.isChainOf.pos
  have hsub : c.1ᶜ ⊆ {r.e ⟨0, hk⟩}ᶜ := by
    intro f hf h
    rw [Set.mem_singleton_iff.1 h] at hf
    exact hf ((Set.ext_iff.1 r.range_eq _).1 ⟨_, rfl⟩)
  have hlift : ∀ {a b : {u // IsBranch K ∅ u}}, (suppress K).graph.Walks {c}ᶜ a b →
      K.graph.Walks {r.e ⟨0, hk⟩}ᶜ a.1 b.1 := fun h =>
    walks_mono hsub (suppress_walks_val hdir (F := {c}ᶜ) (S := c.1ᶜ) (fun c' hc' f hf hfc =>
      (hc' : c' ∉ ({c} : Set _)) (Set.mem_singleton_iff.2
        (Subtype.ext (c'.2.eq_of_mem c.2 hf hfc)))) h)
  have h0 : (⟨0, hk⟩ : Fin r.k).castSucc = 0 := Fin.ext rfl
  refine ⟨r.e ⟨0, hk⟩, r.p 0, ?_, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases r.isChainOf.joins ⟨0, hk⟩ with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact Or.inl (h₁.trans (by rw [h0]))
    · exact Or.inr (h₂.trans (by rw [h0]))
  · have := hlift h
    rwa [suppress_source_val hdir] at this
  · by_contra hn
    have ht := (isTree_walks_or hT c w).resolve_left hn
    have := hlift ht
    rw [suppress_target_val hdir] at this
    exact r.not_walks_last_first hK (this.trans (K.graph.walks_symm h))

/-- The suppressed tree is an `X`-tree, with its taxa as leaves labelled injectively and its other
nodes of degree three, when the network is a multigraph tree whose taxa have degree one and whose
other nodes have degree two or three. -/
theorem suppress_xTree [Finite V] [Finite E] [Nonempty X] (hK : K.graph.IsTree)
    (hleaf : ∀ x, degree K.graph (K.leaf x) = 1)
    (hdeg : ∀ u, (¬ ∃ x, K.leaf x = u) → degree K.graph u = 2 ∨ degree K.graph u = 3)
    (hinj : Function.Injective K.leaf) :
    SplitsEquivalence.IsXTree (suppress K).graph.toSimpleGraph (suppress K).leaf ∧
      Function.Injective (suppress K).leaf ∧
      (∀ x, ((suppress K).graph.toSimpleGraph.neighborSet ((suppress K).leaf x)).ncard = 1) ∧
      ∀ v, v ∉ Set.range (suppress K).leaf →
        ((suppress K).graph.toSimpleGraph.neighborSet v).ncard = 3 := by
  have hT := suppress_isTree hdir hK
  have hnb : ∀ v, ((suppress K).graph.toSimpleGraph.neighborSet v).ncard = degree K.graph v.1 :=
    fun v => (isTree_ncard_neighborSet hT v).trans (degree_suppress hdir hK v)
  have h3 : ∀ v, v ∉ Set.range (suppress K).leaf →
      ((suppress K).graph.toSimpleGraph.neighborSet v).ncard = 3 := by
    intro v hv
    rw [hnb]
    have hnl : ¬ ∃ x, K.leaf x = v.1 := fun ⟨x, hx⟩ => hv ⟨x, Subtype.ext hx⟩
    rcases v.2 with h | h | h
    · exact (hdeg _ hnl).resolve_left h
    · exact absurd h hnl
    · exact absurd h (Set.notMem_empty _)
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have : Nonempty {u // IsBranch K ∅ u} := ⟨(suppress K).leaf x₀⟩
  refine ⟨⟨hT.toSimpleGraph_isTree, fun v hv => ?_⟩, fun x y h => hinj (congrArg Subtype.val h),
    fun x => (hnb _).trans (hleaf x), h3⟩
  by_contra hn
  have := h3 v hn
  omega

/-- **The sides of the splits of the suppressed tree** are sides of edges of the network: each is,
or has as complement, the set of taxa reached from an end of an edge without that edge. -/
theorem suppress_splitSides [Finite V] [Finite E] (hK : K.graph.IsTree) {A : Set X}
    (hA : A ∈ SplitsEquivalence.splitSides (suppress K).graph.toSimpleGraph (suppress K).leaf) :
    ∃ g a, (K.graph.source g = a ∨ K.graph.target g = a) ∧
      (A = {x | K.graph.Walks {g}ᶜ a (K.leaf x)} ∨ Aᶜ = {x | K.graph.Walks {g}ᶜ a (K.leaf x)}) := by
  have hT := suppress_isTree hdir hK
  obtain ⟨e, he, x, rfl⟩ := hA
  induction e using Sym2.ind with
  | _ u v =>
  obtain ⟨c, hc⟩ := exists_joins_of_toSimpleGraph_adj (show _ from he)
  -- the edge is the pair of ends of the chain `c`
  have hs : s(u, v) = s((suppress K).graph.source c, (suppress K).graph.target c) := by
    rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂, Sym2.eq_swap]
  obtain ⟨g, a, hga, hside⟩ := suppress_side hdir hK c
  refine ⟨g, a, hga, ?_⟩
  have hred : ∀ y, y ∈ SplitsEquivalence.edgeSide (suppress K).graph.toSimpleGraph (suppress K).leaf
      s(u, v) x ↔ (suppress K).graph.Walks {c}ᶜ ((suppress K).leaf x) ((suppress K).leaf y) := by
    intro y
    show (_ : SimpleGraph _).Reachable _ _ ↔ _
    rw [hs]
    exact isTree_reachable_deleteEdges_iff hT c
  rcases isTree_walks_or hT c ((suppress K).leaf x) with hx | hx
  · left
    ext y
    refine (hred y).trans (Iff.trans ?_ (hside ((suppress K).leaf y)))
    exact ⟨fun h => hx.trans h, fun h => ((suppress K).graph.walks_symm hx).trans h⟩
  · right
    ext y
    refine (not_congr (hred y)).trans (Iff.trans ?_ (hside ((suppress K).leaf y)))
    constructor
    · intro h
      rcases isTree_walks_or hT c ((suppress K).leaf y) with h' | h'
      · exact h'
      · exact absurd (((suppress K).graph.walks_symm hx).trans h') h
    · intro h h'
      exact hT.2 c ((h.trans ((suppress K).graph.walks_symm h')).trans
        ((suppress K).graph.walks_symm hx))

end SuppressTree

section Contract

variable {V E X : Type*} {G : SemidirectedNetwork V E X} {P : Set E → Prop}

/-- Nodes identified by contracting cycles are joined along cycles. -/
theorem walks_of_contract_eq {a b : V}
    (h : (Quot.mk _ a : Quot (ContractRel G.graph P)) = Quot.mk _ b) :
    G.graph.Walks {e | ∃ C, IsCycle G.graph C ∧ e ∈ C} a b := by
  have hg := Quot.eqvGen_exact h
  clear h
  induction hg with
  | rel x y hxy =>
    obtain ⟨C, hC, -, hx, hy⟩ := hxy
    obtain ⟨g, hg, -⟩ := id hx
    refine walks_mono ?_ (hC.walks_sdiff_singleton hg hx hy)
    intro e he
    exact ⟨C, hC, he.1⟩
  | refl => exact .refl
  | symm x y _ ih => exact G.graph.walks_symm ih
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A walk of the contracted network is a walk of the network**, on its edges and on edges of
cycles. -/
theorem walks_of_contract_walks {F : Set {e // ∀ C, IsCycle G.graph C → P C → e ∉ C}} {a b : V}
    (h : (contractCycles G P).graph.Walks F (Quot.mk _ a) (Quot.mk _ b)) :
    G.graph.Walks (Subtype.val '' F ∪ {e | ∃ C, IsCycle G.graph C ∧ e ∈ C}) a b := by
  suffices key : ∀ x y, (contractCycles G P).graph.Walks F x y → ∀ a b, Quot.mk _ a = x →
      Quot.mk _ b = y →
      G.graph.Walks (Subtype.val '' F ∪ {e | ∃ C, IsCycle G.graph C ∧ e ∈ C}) a b from
    key _ _ h a b rfl rfl
  intro x y hxy
  induction hxy with
  | refl =>
    intro a b ha hb
    exact walks_mono Set.subset_union_right (walks_of_contract_eq (ha.trans hb.symm))
  | @tail y z _ hst ih =>
    intro a b ha hb
    obtain ⟨f, hf, hj⟩ := hst
    have hstep : G.graph.Walks (Subtype.val '' F ∪ {e | ∃ C, IsCycle G.graph C ∧ e ∈ C})
        (G.graph.source f.1) (G.graph.target f.1) :=
      .single ⟨f.1, Or.inl ⟨f, hf, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ((ih a _ ha h₁).trans hstep).trans
        (walks_mono Set.subset_union_right (walks_of_contract_eq (h₂.trans hb.symm)))
    · exact ((ih a _ ha h₂).trans (G.graph.walks_symm hstep)).trans
        (walks_mono Set.subset_union_right (walks_of_contract_eq (h₁.trans hb.symm)))

variable (hP : ∀ C, IsCycle G.graph C → P C)
include hP

/-- **A walk of the network is a walk of the contracted network**, on the edges off cycles, when all
cycles are contracted. -/
theorem contract_walks_of_walks {F : Set E} {a b : V} (h : G.graph.Walks F a b) :
    (contractCycles G P).graph.Walks {e | e.1 ∈ F} (Quot.mk _ a) (Quot.mk _ b) := by
  induction h with
  | refl => exact .refl
  | @tail c d _ hst ih =>
    obtain ⟨f, hf, hj⟩ := hst
    by_cases hc : ∃ C, IsCycle G.graph C ∧ f ∈ C
    · obtain ⟨C, hC, hfC⟩ := hc
      have : (Quot.mk _ c : Quot (ContractRel G.graph P)) = Quot.mk _ d := by
        apply Quot.sound
        refine ⟨C, hC, hP C hC, ?_, ?_⟩
        · rcases hj with ⟨h₁, -⟩ | ⟨-, h₂⟩
          exacts [⟨f, hfC, Or.inl h₁⟩, ⟨f, hfC, Or.inr h₂⟩]
        · rcases hj with ⟨-, h₂⟩ | ⟨h₁, -⟩
          exacts [⟨f, hfC, Or.inr h₂⟩, ⟨f, hfC, Or.inl h₁⟩]
      rw [← this]
      exact ih
    · push Not at hc
      refine ih.tail ⟨⟨f, fun C hC _ => hc C hC⟩, hf, ?_⟩
      rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg _ h₁, congrArg _ h₂⟩
      · exact Or.inr ⟨congrArg _ h₁, congrArg _ h₂⟩

/-- **Contracting all cycles of a connected network gives a multigraph tree**: an edge of the
contraction joined to itself by a walk would lie on a cycle of the network. -/
theorem contract_isTree (hconn : G.graph.IsConnected) : (contractCycles G P).graph.IsTree := by
  refine ⟨fun x y => ?_, fun g hg => ?_⟩
  · induction x using Quot.ind with
    | mk a =>
    induction y using Quot.ind with
    | mk b =>
    exact walks_mono (fun _ _ => Set.mem_univ _) (contract_walks_of_walks hP (hconn a b))
  · have hw := walks_of_contract_walks (a := G.graph.source g.1) (b := G.graph.target g.1) hg
    have hnot : g.1 ∉ Subtype.val '' ({g}ᶜ : Set _) ∪ {e | ∃ C, IsCycle G.graph C ∧ e ∈ C} := by
      rintro (⟨g', hg', hgg⟩ | ⟨C, hC, hgC⟩)
      · exact hg' (Subtype.ext hgg)
      · exact g.2 C hC (hP C hC) hgC
    obtain ⟨C, hC, hgC, -⟩ := exists_isCycle_of_walks hnot (G.graph.walks_symm hw)
    exact g.2 C hC (hP C hC) hgC

/-- The sides of an edge of the contraction are those of the edge in the network. -/
theorem contract_walks_compl_iff (g : {e // ∀ C, IsCycle G.graph C → P C → e ∉ C}) (a b : V) :
    (contractCycles G P).graph.Walks {g}ᶜ (Quot.mk _ a) (Quot.mk _ b) ↔
      G.graph.Walks {g.1}ᶜ a b := by
  constructor
  · intro h
    refine walks_mono ?_ (walks_of_contract_walks h)
    rintro f (⟨g', hg', rfl⟩ | ⟨C, hC, hfC⟩) hfg
    · exact hg' (Subtype.ext hfg)
    · rw [Set.mem_singleton_iff.1 hfg] at hfC
      exact g.2 C hC (hP C hC) hfC
  · intro h
    refine walks_mono ?_ (contract_walks_of_walks hP h)
    intro f hf hfg
    exact hf (by rw [Set.mem_singleton_iff.1 hfg]; exact Set.mem_singleton _)

variable (hnd : ∀ C C', IsCycle G.graph C → IsCycle G.graph C' →
  (cycleNodes G.graph C ∩ cycleNodes G.graph C').Nonempty → C = C')
include hnd

/-- With cycles sharing no node, contracting identifies exactly the nodes of each cycle. -/
theorem contract_mk_eq_iff {a b : V} :
    (Quot.mk _ a : Quot (ContractRel G.graph P)) = Quot.mk _ b ↔
      a = b ∨ ∃ C, IsCycle G.graph C ∧ a ∈ cycleNodes G.graph C ∧ b ∈ cycleNodes G.graph C := by
  constructor
  · intro h
    have hg := Quot.eqvGen_exact h
    clear h
    induction hg with
    | rel x y hxy =>
      obtain ⟨C, hC, -, hx, hy⟩ := hxy
      exact Or.inr ⟨C, hC, hx, hy⟩
    | refl => exact Or.inl rfl
    | symm x y _ ih =>
      rcases ih with rfl | ⟨C, hC, h₁, h₂⟩
      exacts [Or.inl rfl, Or.inr ⟨C, hC, h₂, h₁⟩]
    | trans x y z _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨C, hC, h₁, h₂⟩
      · exact ih₂
      · rcases ih₂ with rfl | ⟨C', hC', h₁', h₂'⟩
        · exact Or.inr ⟨C, hC, h₁, h₂⟩
        · obtain rfl := hnd C C' hC hC' ⟨y, h₂, h₁'⟩
          exact Or.inr ⟨C, hC, h₁, h₂'⟩
  · rintro (rfl | ⟨C, hC, h₁, h₂⟩)
    · rfl
    · exact Quot.sound ⟨C, hC, hP C hC, h₁, h₂⟩

/-- A node on no cycle keeps its degree in the contraction. -/
theorem contract_degree_of_notMem {v : V}
    (hv : ∀ C, IsCycle G.graph C → v ∉ cycleNodes G.graph C) :
    degree (contractCycles G P).graph (Quot.mk _ v) = degree G.graph v := by
  have hcls : ∀ w, (Quot.mk _ w : Quot (ContractRel G.graph P)) = Quot.mk _ v ↔ w = v := fun w => by
    rw [contract_mk_eq_iff hP hnd]
    constructor
    · rintro (h | ⟨C, hC, -, hvC⟩)
      exacts [h, absurd hvC (hv C hC)]
    · exact Or.inl
  have hall : ∀ e : E, (G.graph.source e = v ∨ G.graph.target e = v) →
      ∀ C, IsCycle G.graph C → P C → e ∉ C := by
    intro e he C hC _ heC
    rcases he with he | he
    · exact hv C hC ⟨e, heC, Or.inl he⟩
    · exact hv C hC ⟨e, heC, Or.inr he⟩
  unfold degree DirectedMultigraph.indegree DirectedMultigraph.outdegree
  congr 1
  · refine Set.ncard_congr (fun e _ => e.1) (fun e he => (hcls _).1 he)
      (fun e e' _ _ h => Subtype.ext h) fun e he => ⟨⟨e, hall e (Or.inr he)⟩, (hcls _).2 he, rfl⟩
  · refine Set.ncard_congr (fun e _ => e.1) (fun e he => (hcls _).1 he)
      (fun e e' _ _ h => Subtype.ext h) fun e he => ⟨⟨e, hall e (Or.inl he)⟩, (hcls _).2 he, rfl⟩

/-- **A contracted cycle has degree its size**, when every node of the cycle has degree three: each
node of the cycle has one edge off it. -/
theorem contract_degree_of_mem [Finite E] (hloop : ∀ e, G.graph.source e ≠ G.graph.target e)
    (hT : (contractCycles G P).graph.IsTree) {C : Set E} (hC : IsCycle G.graph C)
    (h3 : ∀ w ∈ cycleNodes G.graph C, degree G.graph w = 3) {v : V}
    (hv : v ∈ cycleNodes G.graph C) :
    degree (contractCycles G P).graph (Quot.mk _ v) = C.ncard := by
  have hcls : ∀ w, (Quot.mk _ w : Quot (ContractRel G.graph P)) = Quot.mk _ v ↔
      w ∈ cycleNodes G.graph C := fun w => by
    rw [contract_mk_eq_iff hP hnd]
    constructor
    · rintro (rfl | ⟨C', hC', hw, hv'⟩)
      · exact hv
      · rwa [hnd C' C hC' hC ⟨v, hv', hv⟩] at hw
    · intro hw
      exact Or.inr ⟨C, hC, hw, hv⟩
  -- one edge off the cycle at each of its nodes
  have hone : ∀ w ∈ cycleNodes G.graph C,
      {e | (G.graph.source e = w ∨ G.graph.target e = w) ∧ e ∉ C}.ncard = 1 := by
    intro w hw
    have h2 := hC.ncard_incident hloop hw
    have hd := degree_eq_ncard_incident hloop w
    rw [h3 w hw] at hd
    have := Set.ncard_inter_add_ncard_sdiff_eq_ncard
      {e | G.graph.source e = w ∨ G.graph.target e = w} C
    have hi : {e | G.graph.source e = w ∨ G.graph.target e = w} ∩ C =
        {e | e ∈ C ∧ (G.graph.source e = w ∨ G.graph.target e = w)} := by
      ext e
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hi, h2] at this
    have hd' : {e | G.graph.source e = w ∨ G.graph.target e = w} \ C =
        {e | (G.graph.source e = w ∨ G.graph.target e = w) ∧ e ∉ C} := rfl
    rw [hd'] at this
    omega
  have hoff : ∀ w ∈ cycleNodes G.graph C, ∀ e e' : E, ((G.graph.source e = w ∨
      G.graph.target e = w) ∧ e ∉ C) → ((G.graph.source e' = w ∨ G.graph.target e' = w) ∧ e' ∉ C) →
      e = e' := by
    intro w hw e e' he he'
    obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 (hone w hw)
    have h1 : e ∈ ({e₀} : Set E) := he₀ ▸ he
    have h2 : e' ∈ ({e₀} : Set E) := he₀ ▸ he'
    rw [Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  have hloopT := isTree_source_ne_target hT
  rw [degree_eq_ncard_incident hloopT, ← ncard_cycleNodes hC]
  refine Set.ncard_congr (fun e _ => if G.graph.source e.1 ∈ cycleNodes G.graph C then
    G.graph.source e.1 else G.graph.target e.1) ?_ ?_ ?_
  · intro e he
    split_ifs with h
    · exact h
    · rcases he with he | he
      · exact absurd ((hcls _).1 he) h
      · exact (hcls _).1 he
  · intro e e' he he' heq
    have hnot : ∀ f : {e // ∀ C, IsCycle G.graph C → P C → e ∉ C}, f.1 ∉ C := fun f =>
      f.2 C hC (hP C hC)
    have hinc : ∀ f : {e // ∀ C, IsCycle G.graph C → P C → e ∉ C},
        f ∈ {e : {e // ∀ C, IsCycle G.graph C → P C → e ∉ C} |
          (contractCycles G P).graph.source e = Quot.mk _ v ∨
            (contractCycles G P).graph.target e = Quot.mk _ v} →
        (if G.graph.source f.1 ∈ cycleNodes G.graph C then G.graph.source f.1
          else G.graph.target f.1) ∈ cycleNodes G.graph C ∧
        ((G.graph.source f.1 = (if G.graph.source f.1 ∈ cycleNodes G.graph C then
          G.graph.source f.1 else G.graph.target f.1) ∨ G.graph.target f.1 =
          (if G.graph.source f.1 ∈ cycleNodes G.graph C then G.graph.source f.1
            else G.graph.target f.1)) ∧ f.1 ∉ C) := by
      intro f hf
      split_ifs with h
      · exact ⟨h, Or.inl rfl, hnot f⟩
      · refine ⟨?_, Or.inr rfl, hnot f⟩
        rcases hf with hf | hf
        · exact absurd ((hcls _).1 hf) h
        · exact (hcls _).1 hf
    obtain ⟨hw, he₁⟩ := hinc e he
    obtain ⟨-, he₂⟩ := hinc e' he'
    rw [← heq] at he₂
    exact Subtype.ext (hoff _ hw _ _ he₁ he₂)
  · intro w hw
    obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 (hone w hw)
    have hmem : e₀ ∈ {e | (G.graph.source e = w ∨ G.graph.target e = w) ∧ e ∉ C} := by
      rw [he₀]; exact Set.mem_singleton _
    obtain ⟨hinc, hnC⟩ := hmem
    -- `e₀` is on no cycle
    have hoffc : ∀ C', IsCycle G.graph C' → P C' → e₀ ∉ C' := by
      intro C' hC' _ he₀C'
      have hwC' : w ∈ cycleNodes G.graph C' := by
        rcases hinc with h | h
        exacts [⟨e₀, he₀C', Or.inl h⟩, ⟨e₀, he₀C', Or.inr h⟩]
      rw [hnd C' C hC' hC ⟨w, hwC', hw⟩] at he₀C'
      exact hnC he₀C'
    refine ⟨⟨e₀, hoffc⟩, ?_, ?_⟩
    · rcases hinc with h | h
      · exact Or.inl ((hcls _).2 (h ▸ hw))
      · exact Or.inr ((hcls _).2 (h ▸ hw))
    · split_ifs with h
      · rcases hinc with h' | h'
        · exact h'
        · exact absurd (((hcls _).2 h).trans ((hcls _).2 (h' ▸ hw)).symm)
            (hloopT ⟨e₀, hoffc⟩)
      · exact hinc.resolve_left fun h' => h (h' ▸ hw)

/-- **The contraction of all cycles** of a connected network without loops, whose cycles share no
node and have at most three edges, whose taxa have degree one and other nodes degree three: the taxa
have degree one and are labelled injectively, and the other nodes have degree two (a contracted
2-cycle) or three. -/
theorem contract_degrees [Finite E] (hloop : ∀ e, G.graph.source e ≠ G.graph.target e)
    (hconn : G.graph.IsConnected) (hsize : ∀ C, IsCycle G.graph C → C.ncard ≤ 3)
    (hleaf : ∀ x, degree G.graph (G.leaf x) = 1)
    (hdeg : ∀ u, (¬ ∃ x, G.leaf x = u) → degree G.graph u = 3) (hinj : Function.Injective G.leaf) :
    (∀ x, degree (contractCycles G P).graph ((contractCycles G P).leaf x) = 1) ∧
      (∀ u, (¬ ∃ x, (contractCycles G P).leaf x = u) →
        degree (contractCycles G P).graph u = 2 ∨ degree (contractCycles G P).graph u = 3) ∧
      Function.Injective (contractCycles G P).leaf := by
  have hT := contract_isTree hP hconn
  -- a node of a cycle is on two of its edges
  have h2C : ∀ C, IsCycle G.graph C → ∀ w ∈ cycleNodes G.graph C,
      2 ≤ {e | G.graph.source e = w ∨ G.graph.target e = w}.ncard ∧ 2 ≤ C.ncard := by
    intro C hC w hw
    have h2 := hC.ncard_incident hloop hw
    exact ⟨h2 ▸ Set.ncard_le_ncard (fun e he => he.2) (Set.toFinite _),
      h2 ▸ Set.ncard_le_ncard (fun e he => he.1) (Set.toFinite _)⟩
  have hnl : ∀ C, IsCycle G.graph C → ∀ w ∈ cycleNodes G.graph C, ¬ ∃ x, G.leaf x = w := by
    rintro C hC w hw ⟨x, rfl⟩
    have hd := degree_eq_ncard_incident hloop (G.leaf x)
    rw [hleaf x] at hd
    have := (h2C C hC _ hw).1
    omega
  have hleafC : ∀ x C, IsCycle G.graph C → G.leaf x ∉ cycleNodes G.graph C :=
    fun x C hC hx => hnl C hC _ hx ⟨x, rfl⟩
  refine ⟨fun x => (contract_degree_of_notMem hP hnd (hleafC x)).trans (hleaf x),
    fun u hu => ?_, fun x y h => ?_⟩
  · induction u using Quot.ind with
    | mk v =>
    by_cases hv : ∃ C, IsCycle G.graph C ∧ v ∈ cycleNodes G.graph C
    · obtain ⟨C, hC, hvC⟩ := hv
      rw [contract_degree_of_mem hP hnd hloop hT hC (fun w hw => hdeg w (hnl C hC w hw)) hvC]
      have := (h2C C hC v hvC).2
      have := hsize C hC
      omega
    · push Not at hv
      rw [contract_degree_of_notMem hP hnd hv]
      exact Or.inr (hdeg v fun ⟨x, hx⟩ => hu ⟨x, by rw [← hx]; rfl⟩)
  · rcases (contract_mk_eq_iff hP hnd).1 h with h | ⟨C, hC, hx, -⟩
    · exact hinj h
    · exact absurd hx (hleafC x C hC)

end Contract

end Banos2019
