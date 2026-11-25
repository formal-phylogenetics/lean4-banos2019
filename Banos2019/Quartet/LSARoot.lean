module

public import Banos2019.Quartet.Contract

/-!
# The root of a binary level-1 network as the LSA of its taxa

The networks that the proofs of Section 5 reduce to are binary level-1 networks built from an LSA
network; their roots are the LSAs of their taxa because their two root arcs do not end at the same
node.

* `reaches_of_isStableAncestor`: a node reached from the root avoiding a stable ancestor `w` of the
  taxa is above `w`.
* `isLSANetwork_of_target_ne`: in a binary level-1 network whose two root arcs have distinct
  targets, the root is the LSA of the taxa. A lower stable ancestor `w` would be below both children
  of the root; a child `c` of the root with a single parent has two children, both above `w`, and the
  paths from them to `w` close two cycles through the arc `c → y₁`, one through the root arc into `c`
  and one not.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X : Type*} {N : RootedNetwork V E X}

/-- A path from `u` to a node `b` stays away from a node `w` that `u` does not reach. -/
theorem reflTransGen_avoiding_of_not_reaches_left {u b w : V} (h : N.graph.Reaches u b)
    (hw : ¬ N.graph.Reaches u w) :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ w ∧ b ≠ w) u b := by
  induction h with
  | refl => exact .refl
  | @tail a c hua hac ih =>
    exact ih.tail ⟨hac, fun h => hw (h ▸ hua), fun h => hw (h ▸ hua.tail hac)⟩

/-- **A node reached from the root avoiding a stable ancestor `w` of all the taxa is above `w`**: it
is above a taxon, and a path to that taxon avoiding `w` would make `w` not stable. -/
theorem reaches_of_isStableAncestor (hN : N.IsPhylogenetic) {w u : V}
    (hw : N.IsStableAncestor Set.univ w) (hu : N.HasPathAvoiding N.root u w) :
    N.graph.Reaches u w := by
  by_contra h
  obtain ⟨x, hx⟩ := exists_reaches_leaf hN u
  exact hw x (Set.mem_univ x) ⟨hu.1, fun he => h (he ▸ hx),
    hu.2.2.trans (reflTransGen_avoiding_of_not_reaches_left hx h)⟩

/-- A child `c` of the root with a single parent, and another child, are not both above a stable
ancestor `w` of the taxa other than the root: the two children `y₁`, `y₂` of `c` are above `w`, and
the walks `y₁ ⇝ w ⇜ y₂ ← c` and `c → y₁ ⇝ w ⇜ c' ← r` close two cycles through `c → y₁`, the
second through the root arc `a` into `c` and the first not. -/
theorem false_of_isStableAncestor_of_root_arcs [Finite E] (hN : IsBinaryRootedNetwork N)
    (h1 : IsLevelOne N.graph) {a a' : E} (hne : a ≠ a') (ha : N.graph.source a = N.root)
    (ha' : N.graph.source a' = N.root) (hc : ∀ f, N.graph.target f = N.graph.target a → f = a)
    {w : V} (hwr : w ≠ N.root) (hw : N.IsStableAncestor Set.univ w) : False := by
  set c := N.graph.target a with hc_def
  set c' := N.graph.target a' with hc'_def
  have hA := hN.1.acyclic
  have htr : ∀ f, N.graph.target f ≠ N.root := fun f =>
    (N.graph.indegree_eq_zero_iff _).1 hN.1.root_indegree f
  have hloop : ∀ f, N.graph.source f ≠ N.graph.target f := fun f h =>
    hA _ (.single ⟨f, rfl, h.symm⟩)
  have hcyc : ∀ {x y}, N.graph.Reaches x y → N.graph.Adj y x → False := fun h hab =>
    hA _ (Relation.TransGen.tail' h hab)
  have hRr : ∀ u, N.graph.Reaches u N.root → u = N.root := fun u h => by
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, -, f, -, hf⟩
    · exact h.symm
    · exact absurd hf (htr f)
  have hRc : ∀ u, N.graph.Reaches u c → u = c ∨ u = N.root := fun u h => by
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, hb, f, hfs, hft⟩
    · exact Or.inl h.symm
    · rw [hc f hft, ha] at hfs
      exact Or.inr (hRr u (hfs ▸ hb))
  have hcr : c ≠ N.root := htr a
  have hc'r : c' ≠ N.root := htr a'
  have hcc' : c' ≠ c := fun h => hne (hc a' h).symm
  -- the children of the root are above `w`
  have hreach : ∀ f, N.graph.source f = N.root → N.graph.Reaches (N.graph.target f) w := by
    intro f hf
    by_cases hfw : N.graph.target f = w
    · rw [hfw]
      exact .refl
    · exact reaches_of_isStableAncestor hN.1 hw
        ⟨hwr.symm, hfw, .single ⟨⟨f, hf, rfl⟩, hwr.symm, hfw⟩⟩
  have hcw := hreach a ha
  have hc'w := hreach a' ha'
  have hwc : w ≠ c := fun h => by
    rcases hRc c' (h ▸ hc'w) with h' | h'
    · exact hcc' h'
    · exact hc'r h'
  -- `c` has two children
  have h0 : N.graph.outdegree c ≠ 0 := fun h0 =>
    hwc (N.graph.eq_of_reaches_of_outdegree_eq_zero hcw h0)
  have hin : N.graph.indegree c = 1 :=
    (N.graph.indegree_eq_one_iff _).2 ⟨a, fun f => ⟨hc f, fun h => h ▸ rfl⟩⟩
  have hout : N.graph.outdegree c = 2 := by
    have := hN.2.2 c hcr h0
    omega
  obtain ⟨g₁, g₂, hg, hs⟩ := Set.ncard_eq_two.1 hout
  have hg₁ : N.graph.source g₁ = c := (Set.ext_iff.1 hs g₁).2 (Or.inl rfl)
  have hg₂ : N.graph.source g₂ = c := (Set.ext_iff.1 hs g₂).2 (Or.inr rfl)
  have hout2 : ∀ f, N.graph.source f = c → f = g₁ ∨ f = g₂ := fun f hf => by
    have := (Set.ext_iff.1 hs f).1 hf
    simpa using this
  have hga : ∀ {g}, N.graph.source g = c → g ≠ a := fun {g} hg h => hcr (by rw [← hg, h, ha])
  have hga' : ∀ {g}, N.graph.source g = c → g ≠ a' := fun {g} hg h => hcr (by rw [← hg, h, ha'])
  -- the children of `c` are above `w`
  have hyw : ∀ g, N.graph.source g = c → N.graph.Reaches (N.graph.target g) w := by
    intro g hgc
    by_cases hyw : N.graph.target g = w
    · rw [hyw]
      exact .refl
    · exact reaches_of_isStableAncestor hN.1 hw ⟨hwr.symm, hyw,
        (Relation.ReflTransGen.single ⟨⟨a, ha, rfl⟩, hwr.symm, hwc.symm⟩).tail
          ⟨⟨g, hgc, rfl⟩, hwc.symm, hyw⟩⟩
  -- a node below a child of `c` is not above `c` or the root
  have hyc : ∀ g, N.graph.source g = c → ∀ f, N.graph.Reaches (N.graph.target g) (N.graph.source f) →
      N.graph.source f ≠ c ∧ N.graph.source f ≠ N.root := by
    intro g hgc f hf
    constructor
    · intro h
      exact hcyc (h ▸ hf) ⟨g, hgc, rfl⟩
    · intro h
      exact htr g (hRr _ (h ▸ hf))
  have hc'c : ∀ f, N.graph.Reaches c' (N.graph.source f) →
      N.graph.source f ≠ c ∧ N.graph.source f ≠ N.root := by
    intro f hf
    constructor
    · intro h
      rcases hRc c' (h ▸ hf) with h' | h'
      · exact hcc' h'
      · exact hc'r h'
    · intro h
      exact hc'r (hRr _ (h ▸ hf))
  -- the cycle `D₁` through `g₁` and not through `a`
  obtain ⟨D₁, hD₁, hg₁D₁, hD₁sub⟩ := exists_isCycle_of_walks (F := ({g₁, a} : Set E)ᶜ)
    (e := g₁) (by simp) (by
      rw [hg₁]
      refine ((walks_of_reaches_of_forall (hyw g₁ hg₁) fun f hf _ => ?_).trans
        (N.graph.walks_symm (walks_of_reaches_of_forall (hyw g₂ hg₂) fun f hf _ => ?_))).tail
        ⟨g₂, ?_, Or.inr ⟨hg₂, rfl⟩⟩
      · obtain ⟨h₁, h₂⟩ := hyc g₁ hg₁ f hf
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => h₁ (h ▸ hg₁), fun h => h₂ (h ▸ ha)⟩
      · obtain ⟨h₁, h₂⟩ := hyc g₂ hg₂ f hf
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => h₁ (h ▸ hg₁), fun h => h₂ (h ▸ ha)⟩
      · simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm hg, hga hg₂⟩)
  have haD₁ : a ∉ D₁ := fun h => by
    rcases hD₁sub h with h | h
    · exact hga hg₁ h.symm
    · exact h (by simp)
  -- the cycle `D₂` through `a` and not through `g₂`
  have hmem : ∀ f, f ≠ a → f ≠ g₂ → f ∈ ({a, g₂} : Set E)ᶜ := fun f h₁ h₂ => by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h₁, h₂⟩
  have hw₁ : N.graph.Walks ({a, g₂} : Set E)ᶜ c (N.graph.target g₁) :=
    .single ⟨g₁, hmem g₁ (hga hg₁) hg, Or.inl ⟨hg₁, rfl⟩⟩
  have hw₂ : N.graph.Walks ({a, g₂} : Set E)ᶜ (N.graph.target g₁) w :=
    walks_of_reaches_of_forall (hyw g₁ hg₁) fun f hf _ => by
      obtain ⟨h₁, h₂⟩ := hyc g₁ hg₁ f hf
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => h₂ (h ▸ ha), fun h => h₁ (h ▸ hg₂)⟩
  have hw₃ : N.graph.Walks ({a, g₂} : Set E)ᶜ w c' :=
    N.graph.walks_symm (walks_of_reaches_of_forall hc'w fun f hf _ => by
      obtain ⟨h₁, h₂⟩ := hc'c f hf
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => h₂ (h ▸ ha), fun h => h₁ (h ▸ hg₂)⟩)
  have hw₄ : N.graph.AdjOn ({a, g₂} : Set E)ᶜ c' N.root :=
    ⟨a', hmem a' (Ne.symm hne) (fun h => hga' hg₂ h.symm), Or.inr ⟨ha', rfl⟩⟩
  obtain ⟨D₂, hD₂, haD₂, hD₂sub⟩ := exists_isCycle_of_walks (F := ({a, g₂} : Set E)ᶜ)
    (e := a) (by simp) (by rw [ha]; exact ((hw₁.trans hw₂).trans hw₃).tail hw₄)
  have hg₂D₂ : g₂ ∉ D₂ := fun h => by
    rcases hD₂sub h with h | h
    · exact hga hg₂ h
    · exact h (by simp)
  -- `D₂` passes through `c` on `a` and on an arc out of `c`, which is `g₁`
  have hg₁D₂ : g₁ ∈ D₂ := by
    obtain ⟨f₁, hf₁, f₂, hf₂, hf, hi₁, hi₂⟩ := hD₂.exists_ne_of_mem (fun f _ => hloop f)
      (target_mem_cycleNodes haD₂ : c ∈ cycleNodes N.graph D₂)
    have key : ∀ f ∈ D₂, (N.graph.source f = c ∨ N.graph.target f = c) → f = a ∨ f = g₁ := by
      intro f hfD hf
      rcases hf with hf | hf
      · rcases hout2 f hf with rfl | rfl
        · exact Or.inr rfl
        · exact absurd hfD hg₂D₂
      · exact Or.inl (hc f hf)
    rcases key f₁ hf₁ hi₁ with rfl | rfl <;> rcases key f₂ hf₂ hi₂ with rfl | rfl
    · exact absurd rfl hf
    · exact hf₂
    · exact hf₁
    · exact hf₁
  exact haD₁ ((h1 D₁ D₂ hD₁ hD₂ ⟨g₁, hg₁D₁, hg₁D₂⟩) ▸ haD₂)

/-- **The root of a binary level-1 network whose two root arcs end at distinct nodes is the LSA of the
taxa.** One child of the root has a single parent: if each had a second parent, each would be below
the other. A stable ancestor of the taxa other than the root would contradict
`false_of_isStableAncestor_of_root_arcs`. -/
theorem isLSANetwork_of_target_ne [Finite E] (hN : IsBinaryRootedNetwork N) (h1 : IsLevelOne N.graph)
    (hroot : ∀ a₁ a₂, a₁ ≠ a₂ → N.graph.source a₁ = N.root → N.graph.source a₂ = N.root →
      N.graph.target a₁ ≠ N.graph.target a₂) :
    N.IsLSANetwork := by
  refine ⟨root_isStableAncestor _ _, fun w hw => ?_⟩
  by_contra hwr
  have hwr' : w ≠ N.root := fun h => hwr (h ▸ .refl)
  have hA := hN.1.acyclic
  obtain ⟨a₁, a₂, hne, hs⟩ := Set.ncard_eq_two.1 hN.2.1
  have ha₁ : N.graph.source a₁ = N.root := (Set.ext_iff.1 hs a₁).2 (Or.inl rfl)
  have ha₂ : N.graph.source a₂ = N.root := (Set.ext_iff.1 hs a₂).2 (Or.inr rfl)
  have hroot2 : ∀ f, N.graph.source f = N.root → f = a₁ ∨ f = a₂ := fun f hf => by
    have := (Set.ext_iff.1 hs f).1 hf
    simpa using this
  have hc12 := hroot a₁ a₂ hne ha₁ ha₂
  -- a second parent of the target of a root arc `a` is below the target of the other one `a'`
  have hbelow : ∀ a a', N.graph.source a = N.root → N.graph.source a' = N.root →
      N.graph.target a ≠ N.graph.target a' →
      (∀ g, N.graph.source g = N.root → g = a ∨ g = a') →
      ∀ f, N.graph.target f = N.graph.target a → f ≠ a →
        Relation.TransGen N.graph.Adj (N.graph.target a') (N.graph.target a) := by
    intro a a' ha ha' hne' h2 f hf hfa
    have hfr : N.graph.source f ≠ N.root := fun h => by
      rcases h2 f h with rfl | rfl
      · exact hfa rfl
      · exact hne' hf.symm
    rcases Relation.ReflTransGen.cases_head (hN.1.root_reaches (N.graph.source f)) with
      h | ⟨x, ⟨g, hg, rfl⟩, hx⟩
    · exact absurd h.symm hfr
    · rcases h2 g hg with rfl | rfl
      · exact absurd (Relation.TransGen.tail' hx ⟨f, rfl, hf⟩) (hA _)
      · exact Relation.TransGen.tail' hx ⟨f, rfl, hf⟩
  by_cases hu₁ : ∀ f, N.graph.target f = N.graph.target a₁ → f = a₁
  · exact false_of_isStableAncestor_of_root_arcs hN h1 hne ha₁ ha₂ hu₁ hwr' hw
  by_cases hu₂ : ∀ f, N.graph.target f = N.graph.target a₂ → f = a₂
  · exact false_of_isStableAncestor_of_root_arcs hN h1 (Ne.symm hne) ha₂ ha₁ hu₂ hwr' hw
  push Not at hu₁ hu₂
  obtain ⟨f₁, hf₁, hf₁a⟩ := hu₁
  obtain ⟨f₂, hf₂, hf₂a⟩ := hu₂
  exact hA _ ((hbelow a₁ a₂ ha₁ ha₂ hc12 hroot2 f₁ hf₁ hf₁a).trans
    (hbelow a₂ a₁ ha₂ ha₁ (Ne.symm hc12) (fun g hg => (hroot2 g hg).symm) f₂ hf₂ hf₂a))

end Banos2019
