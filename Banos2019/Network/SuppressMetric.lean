module

public import Banos2019.Bridge.Invariance

/-!
# Metric isomorphisms of suppressed, contracted and edge-deleted semidirected networks

* `restrictMetric`: the parameters of a subset of the edges.
* `SDMetricIso.suppress`: an isomorphism of metric semidirected networks is an isomorphism of their
  suppressions, with the lengths added and the inheritance probabilities multiplied along the chains
  (`suppressMetric`).
* `deleteHybridEdge G h`: `G` without the hybrid edge `h`, the other edges into the target of `h`
  undirected; `SDMetricIso.deleteHybridEdge`: an isomorphism maps it to the network without the image
  of `h`.
* `SDMetricIso.contractCycles`: an isomorphism keeping the contracted cycles gives isomorphic metric
  contracted networks.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace Banos2019

variable {V E X V' E' : Type*}

/-- The parameters of the edges satisfying `p`: those of `θ`. -/
def restrictMetric (θ : MetricData E) (p : E → Prop) : MetricData {e // p e} :=
  ⟨fun e => θ.length e.1, fun e => θ.inheritance e.1⟩

/-- **An isomorphism of metric semidirected networks is an isomorphism of their suppressions.** -/
def SDMetricIso.suppress [Finite E] {G : SemidirectedNetwork V E X} {θ : MetricData E}
    {G' : SemidirectedNetwork V' E' X} {θ' : MetricData E'} (ι : SDMetricIso G θ G' θ') :
    SDMetricIso (Banos2019.suppress G) (suppressMetric G θ) (Banos2019.suppress G')
      (suppressMetric G' θ') where
  toSDIso := ι.toSDIso.suppressExcept (P := ∅) (P' := ∅) fun _ => Iff.rfl
  length c := by
    change ∑ᶠ f ∈ ι.edge '' c.1, θ'.length f = ∑ᶠ g ∈ c.1, θ.length g
    rw [finsum_mem_image ι.edge.injective.injOn]
    exact finsum_mem_congr rfl fun g _ => ι.length g
  inheritance c _ := by
    change ∏ᶠ f ∈ {f | f ∈ ι.edge '' c.1 ∧ G'.IsDirected f}, θ'.inheritance f =
      ∏ᶠ g ∈ {g | g ∈ c.1 ∧ G.IsDirected g}, θ.inheritance g
    have himg : {f | f ∈ ι.edge '' c.1 ∧ G'.IsDirected f} =
        ι.edge '' {g | g ∈ c.1 ∧ G.IsDirected g} := by
      ext f
      constructor
      · rintro ⟨⟨g, hg, rfl⟩, hd⟩
        exact ⟨g, ⟨hg, (ι.isDirected_iff g).1 hd⟩, rfl⟩
      · rintro ⟨g, ⟨hg, hd⟩, rfl⟩
        exact ⟨⟨g, hg, rfl⟩, (ι.isDirected_iff g).2 hd⟩
    rw [himg, finprod_mem_image ι.edge.injective.injOn]
    exact finprod_mem_congr rfl fun g hg => ι.inheritance g hg.2

/-- **`G` without the hybrid edge `h`**: the other edges into the target of `h` become tree
edges. -/
def deleteHybridEdge (G : SemidirectedNetwork V E X) (h : E) :
    SemidirectedNetwork V {g // g ≠ h} X where
  graph := { source := fun g => G.graph.source g.1, target := fun g => G.graph.target g.1 }
  IsDirected g := G.IsDirected g.1 ∧ G.graph.target g.1 ≠ G.graph.target h
  leaf := G.leaf

/-- **An isomorphism maps the network without a hybrid edge to the network without its image.** -/
def SDMetricIso.deleteHybridEdge {G : SemidirectedNetwork V E X} {θ : MetricData E}
    {G' : SemidirectedNetwork V' E' X} {θ' : MetricData E'} (ι : SDMetricIso G θ G' θ') {h : E}
    (hh : G.IsDirected h) :
    SDMetricIso (Banos2019.deleteHybridEdge G h) (restrictMetric θ _)
      (Banos2019.deleteHybridEdge G' (ι.edge h)) (restrictMetric θ' _) where
  vert := ι.vert
  edge := ι.edge.subtypeEquiv fun g => ι.edge.injective.ne_iff.symm
  isDirected_iff g := by
    change G'.IsDirected (ι.edge g.1) ∧ G'.graph.target (ι.edge g.1) ≠ G'.graph.target (ι.edge h) ↔
      G.IsDirected g.1 ∧ G.graph.target g.1 ≠ G.graph.target h
    rw [ι.isDirected_iff]
    refine and_congr_right fun hd => ?_
    rw [(ι.directed g.1 hd).2, (ι.directed h hh).2, ι.vert.injective.ne_iff]
  joins g := ι.joins g.1
  directed g hg := ι.directed g.1 hg.1
  leaf x := ι.leaf x
  length g := ι.length g.1
  inheritance g hg := ι.inheritance g.1 hg.1

/-- **An isomorphism keeping the contracted cycles gives isomorphic metric contracted
networks.** -/
def SDMetricIso.contractCycles {G : SemidirectedNetwork V E X} {θ : MetricData E}
    {G' : SemidirectedNetwork V' E' X} {θ' : MetricData E'} (ι : SDMetricIso G θ G' θ')
    {Q : Set E → Prop} {Q' : Set E' → Prop}
    (hQ : ∀ C, IsCycle G.graph C → (Q' (ι.edge '' C) ↔ Q C)) :
    SDMetricIso (Banos2019.contractCycles G Q) (restrictMetric θ _)
      (Banos2019.contractCycles G' Q') (restrictMetric θ' _) where
  toSDIso := ι.toSDIso.contractCycles hQ
  length f := ι.length f.1
  inheritance f hf := ι.inheritance f.1 hf

end Banos2019
