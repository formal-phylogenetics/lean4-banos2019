module

public import Phylogenetics.MSC.Small
public import Phylogenetics.Tree.Splits

/-!
# The quartet tree displayed by an unrooted tree on four taxa

Allman, Degnan and Rhodes 2011 give the probabilities of the unrooted gene trees on four taxa, the
trees `treeOfClusters {B}` with the split `B | Bᶜ`, `#B = 2`. Baños 2019 uses them as the
probabilities that the gene tree displays a quartet tree (`Phylogenetics.Displays`). On four taxa
the two agree: the unrooted tree with the split `C | Cᶜ` displays the quartet tree `r` exactly when
it is the unrooted tree of the split of `r`.

* `mem_treeOfClusters_singleton_iff`, `treeOfClusters_compl`: the sides of the splits of the
  unrooted tree with one nontrivial split.
* `treeOfClusters_eq_iff`: on four taxa, two such trees are equal when their splits are.
* `displays_treeOfClusters_iff`: on four taxa, the quartet tree it displays.
-/

@[expose] public section

namespace External.AllmanDegnanRhodes2011

open Phylogenetics Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The sides of the splits of the unrooted tree with the nontrivial split `C | Cᶜ`: `C`, `Cᶜ`, the
single taxa and their complements. -/
theorem mem_treeOfClusters_singleton_iff (hX : 2 ≤ Fintype.card X) {A C : Finset X}
    (hC : C ≠ univ) :
    A ∈ treeOfClusters {C} ↔ A = C ∨ Aᶜ = C ∨ (∃ x, A = {x}) ∨ ∃ x, Aᶜ = {x} := by
  have hs : ∀ x : X, ({x} : Finset X) ≠ univ := fun x h => by
    have := congrArg Finset.card h
    rw [card_singleton, card_univ] at this
    omega
  unfold treeOfClusters
  simp only [mem_unroot, mem_insert, mem_union, mem_singleton, mem_image, mem_univ, true_and]
  constructor
  · rintro (⟨h | h | ⟨x, hx⟩, hu⟩ | ⟨h | h | ⟨x, hx⟩, hu⟩)
    · exact absurd h hu
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨x, hx.symm⟩))
    · exact absurd h hu
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr ⟨x, hx.symm⟩))
  · rintro (h | h | ⟨x, hx⟩ | ⟨x, hx⟩)
    · exact Or.inl ⟨Or.inr (Or.inl h), h ▸ hC⟩
    · exact Or.inr ⟨Or.inr (Or.inl h), h ▸ hC⟩
    · exact Or.inl ⟨Or.inr (Or.inr ⟨x, hx.symm⟩), hx ▸ hs x⟩
    · exact Or.inr ⟨Or.inr (Or.inr ⟨x, hx.symm⟩), hx ▸ hs x⟩

/-- The unrooted trees with the splits `C | Cᶜ` and `Cᶜ | C` are the same. -/
theorem treeOfClusters_compl (hX : 2 ≤ Fintype.card X) {C : Finset X} (hC : C ≠ univ)
    (hCne : C.Nonempty) : treeOfClusters {Cᶜ} = treeOfClusters {C} := by
  have hCc : Cᶜ ≠ univ := (compl_ne_univ_iff_nonempty C).2 hCne
  have hCcne : Cᶜ.Nonempty := (compl_ne_univ_iff_nonempty Cᶜ).1 (by rwa [compl_compl])
  ext A
  rw [mem_treeOfClusters_singleton_iff hX hCc, mem_treeOfClusters_singleton_iff hX hC,
    compl_inj_iff]
  have h1 : A = Cᶜ ↔ Aᶜ = C := ⟨fun h => by rw [h, compl_compl], fun h => by rw [← h, compl_compl]⟩
  rw [h1]
  tauto

/-- On four taxa, a set of two taxa is a side of a split of the unrooted tree with the split
`C | Cᶜ` (`#C = 2`) exactly when it is `C` or `Cᶜ`. -/
theorem mem_treeOfClusters_iff (hX : Fintype.card X = 4) {A C : Finset X} (hA : #A = 2)
    (hC : #C = 2) : A ∈ treeOfClusters {C} ↔ A = C ∨ A = Cᶜ := by
  have hCu : C ≠ univ := fun h => by rw [h, card_univ] at hC; omega
  have hAc : #Aᶜ = 2 := by rw [card_compl, hX, hA]
  rw [mem_treeOfClusters_singleton_iff (by omega) hCu]
  constructor
  · rintro (h | h | ⟨x, hx⟩ | ⟨x, hx⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [← h, compl_compl])
    · rw [hx, card_singleton] at hA
      omega
    · rw [hx, card_singleton] at hAc
      omega
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (by rw [h, compl_compl]))

/-- On four taxa, the unrooted trees with the splits `C | Cᶜ` and `B | Bᶜ` (`#B = #C = 2`) are equal
exactly when `C` is `B` or `Bᶜ`. -/
theorem treeOfClusters_eq_iff (hX : Fintype.card X = 4) {B C : Finset X} (hB : #B = 2)
    (hC : #C = 2) : treeOfClusters {C} = treeOfClusters {B} ↔ C = B ∨ C = Bᶜ := by
  constructor
  · intro h
    have hm : C ∈ treeOfClusters {B} := h ▸ (mem_treeOfClusters_iff hX hC hC).2 (Or.inl rfl)
    exact (mem_treeOfClusters_iff hX hC hB).1 hm
  · rintro (rfl | rfl)
    · rfl
    · exact treeOfClusters_compl (by omega) (fun h => by rw [h, card_univ] at hB; omega)
        (card_pos.1 (by omega))

/-- On four taxa, the taxa of a quartet tree are all the taxa. -/
theorem taxa_eq_univ (hX : Fintype.card X = 4) (r : QuartetTree X) : r.taxa = univ :=
  eq_univ_of_card r.taxa (by rw [r.card_taxa, hX])

/-- On four taxa, the cherries of a quartet tree are `B` and `Bᶜ`. -/
theorem val_eq_pair_compl (hX : Fintype.card X = 4) (r : QuartetTree X) {B : Finset X}
    (hB : B ∈ r.val) : r.val = {B, Bᶜ} := by
  rw [r.eq_pair_of_mem hB, taxa_eq_univ hX, ← compl_eq_univ_sdiff]

/-- On four taxa, the unrooted tree with the split `C | Cᶜ` (`#C = 2`) displays the quartet tree `r`
exactly when it is the unrooted tree of the split of `r`, with the cherry `B` of `r` on one side. -/
theorem displays_treeOfClusters_iff (hX : Fintype.card X = 4) (r : QuartetTree X)
    {B C : Finset X} (hB : B ∈ r.val) (hC : #C = 2) :
    Displays (treeOfClusters {C}) r ↔ treeOfClusters {C} = treeOfClusters {B} := by
  have hB2 : #B = 2 := r.card_of_mem hB
  have hBc : #Bᶜ = 2 := by rw [card_compl, hX, hB2]
  rw [treeOfClusters_eq_iff hX hB2 hC]
  unfold Displays
  simp only [taxa_eq_univ hX, inter_univ, val_eq_pair_compl hX r hB, mem_insert, mem_singleton]
  constructor
  · rintro ⟨A, hA, rfl | rfl⟩
    · rcases (mem_treeOfClusters_iff hX hB2 hC).1 hA with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, compl_compl])
    · rcases (mem_treeOfClusters_iff hX hBc hC).1 hA with h | h
      · exact Or.inr h.symm
      · exact Or.inl (compl_injective h).symm
  · rintro (rfl | rfl)
    · exact ⟨C, (mem_treeOfClusters_iff hX hC hC).2 (Or.inl rfl), Or.inl rfl⟩
    · exact ⟨Bᶜ, (mem_treeOfClusters_iff hX hC hC).2 (Or.inl rfl), Or.inr rfl⟩

end External.AllmanDegnanRhodes2011
