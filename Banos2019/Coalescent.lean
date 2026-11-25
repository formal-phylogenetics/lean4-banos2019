module

public import Banos2019.Structure
public import Phylogenetics.NMSC.Defs

/-!
# Quartet concordance factors (Baños 2019, Sections 4, 6 and 7)

The network multispecies coalescent of Meng and Kubatko (2009) with independent inheritance is the
library's `Phylogenetics.geneTreeDist N θ 0`, and the concordance factor of a quartet tree `q` is
`Phylogenetics.nmscCF N θ 0 q`: the probability that the unrooted gene tree displays `q`.

* `quartetTree a b c d`: the quartet tree `ab|cd`.
* `CF` (Definition 14): `CF_abcd = (CF_{AB|CD}, CF_{AC|BD}, CF_{AD|BC})`.
* `SameOrdering` (Definition 15): two families of concordance factors order the quartet trees on each
  set of four taxa in the same way.
* `IsTreelikeOn`, `CyclePropertyOn` (Definition 16), `BigCycleOn` (Definition 17), `IsBCQuartet`
  (`q^BC`), stated for a function on quartet trees and a set of four taxa. For a set `s` without four
  elements there is no quartet tree on `s`, so `IsTreelikeOn` is false and the two properties are true:
  every statement that uses them is about a set of four taxa.
* `ForGenericParams`: a property of the numerical parameters holds outside a null set
  (`RootedNetwork.IsGenericNull`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace Banos2019

variable {V E X : Type*} [DecidableEq X]

/-- Four distinct taxa. -/
def Distinct4 (a b c d : X) : Prop := a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- The quartet tree `ab|cd` on four distinct taxa. -/
def quartetTree (a b c d : X) (h : Distinct4 a b c d) : QuartetTree X :=
  ⟨{{a, b}, {c, d}}, by
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
    have hne : ({a, b} : Finset X) ≠ {c, d} := fun h' => by
      have : a ∈ ({c, d} : Finset X) := h' ▸ mem_insert_self a {b}
      simp only [mem_insert, mem_singleton] at this
      tauto
    refine ⟨card_pair hne, ?_, ?_⟩
    · intro B hB
      simp only [mem_insert, mem_singleton] at hB
      rcases hB with rfl | rfl
      · exact card_pair hab
      · exact card_pair hcd
    · intro B hB C hC hBC
      simp only [mem_insert, mem_singleton] at hB hC
      rcases hB with rfl | rfl <;> rcases hC with rfl | rfl
      · exact absurd rfl hBC
      · simp only [disjoint_insert_left, mem_insert, mem_singleton, disjoint_singleton_left]
        tauto
      · simp only [disjoint_insert_left, mem_insert, mem_singleton, disjoint_singleton_left]
        tauto
      · exact absurd rfl hBC⟩

omit [DecidableEq X] in
theorem distinct4_acbd {a b c d : X} (h : Distinct4 a b c d) : Distinct4 a c b d := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  exact ⟨hac, hab, had, hbc.symm, hcd, hbd⟩

omit [DecidableEq X] in
theorem distinct4_adbc {a b c d : X} (h : Distinct4 a b c d) : Distinct4 a d b c := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  exact ⟨had, hab, hac, hbd.symm, hcd.symm, hbc⟩

variable [Fintype V] [Fintype E] [Fintype X]

/-- **Definition 14**: the quartet concordance factors `CF_abcd = (CF_{AB|CD}, CF_{AC|BD}, CF_{AD|BC})`
under the network multispecies coalescent on the metric rooted network `(N, θ)`: the probabilities that
the gene tree displays `ab|cd`, `ac|bd`, `ad|bc`. -/
def CF (N : RootedNetwork V E X) (θ : MetricData E) (a b c d : X) (h : Distinct4 a b c d) :
    ℝ × ℝ × ℝ :=
  (nmscCF N θ 0 (quartetTree a b c d h), nmscCF N θ 0 (quartetTree a c b d (distinct4_acbd h)),
    nmscCF N θ 0 (quartetTree a d b c (distinct4_adbc h)))

omit [Fintype V] [Fintype E] in
/-- **Definition 15**: the concordance factors `p` and `p'` have the same *ordering* on every set of four
taxa: for any two quartet trees on the same four taxa, `p` orders them as `p'` does. The ordering of
`CF_abcd` is the decreasing order of its entries, ties included. -/
def SameOrdering (p p' : QuartetTree X → ℝ) : Prop :=
  ∀ q r : QuartetTree X, q.taxa = r.taxa → (p q ≤ p r ↔ p' q ≤ p' r)

omit [Fintype V] [Fintype E] in
/-- The concordance factors `p` on the four taxa `s` are *treelike*: the two smallest of the three
values are equal (Section 6). -/
def IsTreelikeOn (p : QuartetTree X → ℝ) (s : Finset X) : Prop :=
  ∃ q ∈ treesOn s, ∃ r ∈ treesOn s, q ≠ r ∧ p q = p r ∧ ∀ u ∈ treesOn s, p q ≤ p u

omit [Fintype V] [Fintype E] in
/-- **Definition 16** (`def::Cp`): the set `s` of four taxa satisfies the *Cycle property*: the
concordance factors on `s` are not treelike, that is, the two smallest values are not equal. -/
def CyclePropertyOn (p : QuartetTree X → ℝ) (s : Finset X) : Prop := ¬ IsTreelikeOn p s

omit [Fintype V] [Fintype E] in
/-- **Definition 17** (`bigcycle`): the set `s` of four taxa satisfies the *Big Cycle property* (`BC`):
the three concordance factors on `s` are different. -/
def BigCycleOn (p : QuartetTree X → ℝ) (s : Finset X) : Prop :=
  ∀ q ∈ treesOn s, ∀ r ∈ treesOn s, q ≠ r → p q ≠ p r

omit [Fintype V] [Fintype E] in
/-- **Definition 17**: `q^BC_s`, the quartet tree of the smallest concordance factor on `s`. -/
def IsBCQuartet (p : QuartetTree X → ℝ) (s : Finset X) (q : QuartetTree X) : Prop :=
  q ∈ treesOn s ∧ ∀ r ∈ treesOn s, r ≠ q → p q < p r

/-- The concordance factors of a metric rooted network, as a function on quartet trees. -/
abbrev cf (N : RootedNetwork V E X) (θ : MetricData E) : QuartetTree X → ℝ := nmscCF N θ 0

/-- "For generic numerical parameters, `P` holds": the parameters violating `P` form a null set
(`RootedNetwork.IsGenericNull`: Lebesgue measure in the coordinates given by the edge lengths and, at
each hybrid node, the inheritance probability of one of its two hybrid edges). -/
def ForGenericParams (N : RootedNetwork V E X) (P : MetricData E → Prop) : Prop :=
  N.IsGenericNull {θ | ¬ P θ}

end Banos2019
