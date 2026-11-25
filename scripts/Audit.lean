module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the libraries, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`): every module of `Banos2019/`
-- (`Basic/`, `External/` and the paper's library) and the paper's Solution in `palomar/`, but no
-- Challenge, which holds a copy of the paper's definitions under the library's names. Generate the
-- lines with
--   { find Banos2019 -name '*.lean'; cd palomar && find . -name Solution.lean; } |
--     sed 's#^\./##; s/\.lean$//; s#/#.#g; s/^/import all /' | sort
-- With several papers (references/multi-paper.md), `find ProjectName` in place of `find Banos2019`
-- lists every paper's modules and `Common/`, and the second `find` every paper's Solution.
import all Phylogenetics.Coalescent.Absorption
import all Phylogenetics.Coalescent.BinaryForest
import all Phylogenetics.Coalescent.Defs
import all Phylogenetics.Coalescent.Factorization
import all Phylogenetics.Coalescent.Forest
import all Phylogenetics.Coalescent.Lump
import all Phylogenetics.Coalescent.Outcome
import all Phylogenetics.Coalescent.PMF
import all Phylogenetics.Coalescent.Relabel
import all Phylogenetics.Coalescent.Tavare
import all Phylogenetics.Coalescent.Trace
import all Phylogenetics.Computation.Caterpillar5
import all Phylogenetics.Computation.Codes
import all Phylogenetics.Computation.Engine
import all Phylogenetics.Computation.FiveTaxa
import all Phylogenetics.Computation.FourTaxa
import all Phylogenetics.Computation.ThreeTaxa
import all Phylogenetics.Computation.Toolkit
import all Phylogenetics.ForMathlib.Analysis.MatrixExponential
import all Phylogenetics.ForMathlib.MeasureTheory.HaarPreimage
import all Phylogenetics.Graph.Basic
import all Phylogenetics.Graph.Blobs
import all Phylogenetics.Graph.BridgeCutLaminar
import all Phylogenetics.Graph.Connectivity
import all Phylogenetics.Graph.CutUniqueness
import all Phylogenetics.Graph.Defs
import all Phylogenetics.Graph.Degree
import all Phylogenetics.Graph.Tree
import all Phylogenetics.Hierarchy.Basic
import all Phylogenetics.Hierarchy.Counts
import all Phylogenetics.Hierarchy.Defs
import all Phylogenetics.Hierarchy.Quartets
import all Phylogenetics.Hierarchy.RootLocation
import all Phylogenetics.Hierarchy.SpeciesTree
import all Phylogenetics.MSC.Basic
import all Phylogenetics.MSC.Classify
import all Phylogenetics.MSC.Contract
import all Phylogenetics.MSC.Defs
import all Phylogenetics.MSC.History
import all Phylogenetics.MSC.Marginal
import all Phylogenetics.MSC.MultiSample
import all Phylogenetics.MSC.Relabel
import all Phylogenetics.MSC.Shapes
import all Phylogenetics.MSC.Small
import all Phylogenetics.NMSC.Analytic
import all Phylogenetics.NMSC.Basic
import all Phylogenetics.NMSC.Defs
import all Phylogenetics.NMSC.DisplayedTreeModel
import all Phylogenetics.NMSC.Exchangeability
import all Phylogenetics.NMSC.Factor
import all Phylogenetics.NMSC.Glue
import all Phylogenetics.NMSC.History
import all Phylogenetics.NMSC.Induced
import all Phylogenetics.NMSC.InducedAbove
import all Phylogenetics.NMSC.InducedParams
import all Phylogenetics.NMSC.InducedRestrict
import all Phylogenetics.NMSC.InducedSuppress
import all Phylogenetics.NMSC.Inheritance
import all Phylogenetics.NMSC.Level1.Arms
import all Phylogenetics.NMSC.Level1.Basic
import all Phylogenetics.NMSC.Level1.Consistency
import all Phylogenetics.NMSC.Level1.Context
import all Phylogenetics.NMSC.Level1.Cycle
import all Phylogenetics.NMSC.Level1.Defs
import all Phylogenetics.NMSC.Level1.Displays
import all Phylogenetics.NMSC.Level1.GeneTrees
import all Phylogenetics.NMSC.Level1.General
import all Phylogenetics.NMSC.Level1.MetricCycle.Basic
import all Phylogenetics.NMSC.Level1.MetricCycle.Instance
import all Phylogenetics.NMSC.Level1.MetricCycle.RationalLengths
import all Phylogenetics.NMSC.Level1.MetricCycle.Realization
import all Phylogenetics.NMSC.Level1.MetricCycle.Reflection
import all Phylogenetics.NMSC.Level1.Process
import all Phylogenetics.NMSC.Level1.Sampling
import all Phylogenetics.NMSC.Level1.Symmetry
import all Phylogenetics.NMSC.Marginal
import all Phylogenetics.NMSC.SpeciesTree
import all Phylogenetics.NMSC.Symmetry
import all Phylogenetics.NMSC.TreeCF
import all Phylogenetics.NMSC.Witness
import all Phylogenetics.Network.AncestralRestriction
import all Phylogenetics.Network.Basic
import all Phylogenetics.Network.CutHierarchy
import all Phylogenetics.Network.Cuts
import all Phylogenetics.Network.Defs
import all Phylogenetics.Network.DeletedArcs
import all Phylogenetics.Network.Induced
import all Phylogenetics.Network.InducedMetric
import all Phylogenetics.Network.Level1.CyclicOrder
import all Phylogenetics.Network.Level1.Defs
import all Phylogenetics.Network.Level1.Digraph.Basic
import all Phylogenetics.Network.Level1.Digraph.Complete
import all Phylogenetics.Network.Level1.Digraph.CompleteCycle
import all Phylogenetics.Network.Level1.Digraph.CompleteDesc
import all Phylogenetics.Network.Level1.Digraph.CompleteEmbed
import all Phylogenetics.Network.Level1.Digraph.Correspondence
import all Phylogenetics.Network.Level1.Digraph.CycleHybrid
import all Phylogenetics.Network.Level1.Digraph.Defs
import all Phylogenetics.Network.Level1.Digraph.Invariance
import all Phylogenetics.Network.Level1.Digraph.Invariant
import all Phylogenetics.Network.Level1.Digraph.InvariantCycle
import all Phylogenetics.Network.Level1.Digraph.InvariantSide
import all Phylogenetics.Network.Level1.Digraph.InvariantTree
import all Phylogenetics.Network.Level1.Digraph.OfNet
import all Phylogenetics.Network.Level1.Digraph.Sound
import all Phylogenetics.Network.Level1.LevelOne
import all Phylogenetics.Network.Level1.ToRootedNetwork
import all Phylogenetics.Network.OfHierarchy
import all Phylogenetics.Network.PendantCuts
import all Phylogenetics.Network.Quartets
import all Phylogenetics.Network.Semidirected
import all Phylogenetics.Network.TreeOfBlobs
import all Phylogenetics.Tree.AstralDP
import all Phylogenetics.Tree.Defs
import all Phylogenetics.Tree.Detach
import all Phylogenetics.Tree.FourPoint
import all Phylogenetics.Tree.GeneTree.AnchorNode
import all Phylogenetics.Tree.GeneTree.Annotate
import all Phylogenetics.Tree.GeneTree.Basic
import all Phylogenetics.Tree.Metric
import all Phylogenetics.Tree.NeighborJoining
import all Phylogenetics.Tree.Splice
import all Phylogenetics.Tree.Splits
import all Phylogenetics.Tree.SplitsEquivalence
import all Phylogenetics.Tree.XTree
import all Allman2011.AppendixA
import all Allman2011.AppendixC.Ac1Classes
import all Allman2011.AppendixC.FiveTaxa
import all Allman2011.AppendixC.Shapes
import all Allman2011.AppendixC.StarOneSplit
import all Allman2011.AppendixC.Tables
import all Allman2011.AppendixC.TwoSplits
import all Allman2011.Basic.Algebra.BigOperators.Group.List
import all Allman2011.Basic.Analysis.SpecialFunctions.Exp
import all Allman2011.Basic.Data.Fin.Basic
import all Allman2011.Basic.Data.Finset.Basic
import all Allman2011.Basic.Data.Fintype.Sigma
import all Allman2011.Basic.Data.Nat.Bitwise
import all Allman2011.Basic.Order.Interval.Finset.Nat
import all Allman2011.Bridge
import all Allman2011.Defs
import all Allman2011.Discussion
import all Allman2011.External.Cayley1857.Shapes
import all Allman2011.External.Steel1992.Quartets
import all Allman2011.External.Tavare1984.Formula
import all Allman2011.FiveTaxa.Balanced
import all Allman2011.FiveTaxa.Basic
import all Allman2011.FiveTaxa.Caterpillar
import all Allman2011.FiveTaxa.Explanations
import all Allman2011.FiveTaxa.Lemma4
import all Allman2011.FiveTaxa.Pseudocaterpillar
import all Allman2011.FourTaxa.Analysis
import all Allman2011.FourTaxa.Formulas
import all Allman2011.FourTaxa.Proposition3
import all Allman2011.Identifiability.Corollary10
import all Allman2011.Identifiability.Corollary6
import all Allman2011.Identifiability.FiveTaxa.Binary
import all Allman2011.Identifiability.FiveTaxa.Classes
import all Allman2011.Identifiability.FiveTaxa.Common
import all Allman2011.Identifiability.Lemma5
import all Allman2011.Identifiability.Proposition8
import all Allman2011.Identifiability.Quartets
import all Allman2011.Identifiability.Theorem9
import all Allman2011.Introduction.Equation1
import all Allman2011.Introduction.Proposition1
import all Allman2011.Model
import all Allman2011.Nonbinary.FourTaxa
import all Allman2011.Nonbinary.Limits
import all Allman2011.Nonbinary.Proposition11
import all Allman2011.Nonbinary.Theorem9
import all Allman2011.Nonbinary.Triples
import all Allman2011.Nonbinary.Unrooted
import all Allman2011.Rootings.Proofs
import all Allman2011.Rootings.Statements
import all Allman2011.Rootings.Support
import all PhyloNetwork
import all Banos2019.Basic.Analysis.AnalyticZeroSet
import all Banos2019.Basic.Data.Set.Card
import all Banos2019.Basic.Logic.EquivOfInjective
import all Banos2019.Basic.Logic.RelationSymm
import all Banos2019.Basic.Order.FiniteTotal
import all Banos2019.Bridge.Examples
import all Banos2019.Bridge.Generic
import all Banos2019.Bridge.Invariance
import all Banos2019.Bridge.Model
import all Banos2019.Bridge.Quartet
import all Banos2019.Bridge.Statements
import all Banos2019.Bridge.Suppress
import all Banos2019.Bridge.Unrooted
import all Banos2019.Coalescent
import all Banos2019.CycleProperty
import all Banos2019.Defs
import all Banos2019.External.AllmanDegnanRhodes2011.Basic
import all Banos2019.External.AllmanDegnanRhodes2011.Quartets
import all Banos2019.Identifiability
import all Banos2019.Network.AncestralSuppress
import all Banos2019.Network.Contraction
import all Banos2019.Network.Cycle
import all Banos2019.Network.CycleFacts
import all Banos2019.Network.DirectedPath
import all Banos2019.Network.Induced
import all Banos2019.Network.Path
import all Banos2019.Network.Proposition1
import all Banos2019.Network.Rooted
import all Banos2019.Network.SDPath
import all Banos2019.Network.Semidirected
import all Banos2019.Network.SemidirectedDesc
import all Banos2019.Network.Suppress
import all Banos2019.Network.SuppressIso
import all Banos2019.Network.TrekArc
import all Banos2019.Network.TrekEdges
import all Banos2019.Quartet.Concrete
import all Banos2019.Quartet.Conditioning
import all Banos2019.Quartet.Contract
import all Banos2019.Quartet.Correspondence
import all Banos2019.Quartet.CycleBlocks
import all Banos2019.Quartet.Defs
import all Banos2019.Quartet.Examples
import all Banos2019.Quartet.Fig15
import all Banos2019.Quartet.Fig16
import all Banos2019.Quartet.Fig17
import all Banos2019.Quartet.Fig18
import all Banos2019.Quartet.Generic
import all Banos2019.Quartet.HybridGlue
import all Banos2019.Quartet.Normal
import all Banos2019.Quartet.Reduction
import all Banos2019.Quartet.Remove
import all Banos2019.Quartet.SemidirectedCycles
import all Banos2019.Quartet.Transfer
import all Banos2019.Quartet.Trees
import all Banos2019.Solution
import all Banos2019.Structure

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`External/`) that it uses, whether proved there or, in a conditional formalization,
assumed as hypotheses of its statement. It then checks every declaration of the library and the
theorems that Palomar's comparator checks. The run fails if any of them depends on an axiom other
than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a `sorry` shows up as the
axiom `sorryAx`). Its table of results is the source of the report's dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `route_check.py` (in the skill's `scripts/`) compares these routes with the
results that the paper's proofs cite.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set `isLibraryModule`:
with one paper, every module under the root `Banos2019` but the Challenge; with several, the root
`ProjectName` and each paper's Solution module.
Keep one `import all` line per module of the libraries, each on its own line: a module that is
missing is still imported through the others, but without its proofs, and the audit then misses the
axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, with a short label: the theorems proved in `External/` or, when
general, in `Basic/`, and, in a conditional formalization, the propositions assumed as hypotheses.
The traversal stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Allman, Degnan, Rhodes 2011, equation (1)", ``External.AllmanDegnanRhodes2011.equation1),
   ("Allman, Degnan, Rhodes 2011, Proposition 3", ``External.AllmanDegnanRhodes2011.proposition3),
   ("Allman, Degnan, Rhodes 2011, Proposition 11 (Prop 4)", ``External.AllmanDegnanRhodes2011.proposition4),
   ("Allman, Degnan, Rhodes 2011, root placement", ``External.AllmanDegnanRhodes2011.unrootedDist_eq_of_sameUnrootedMetricTree)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Def 1", ``Banos2019.isBinaryRootedNetwork_iff),
   ("Def 2", ``Banos2019.isMetricNetwork_iff),
   ("Def 4", ``Banos2019.isLeastStableAncestor_iff_def4),
   ("Lemma 1", ``Banos2019.lemma1),
   ("Lemma 2", ``Banos2019.lemma2),
   ("Prop 1", ``Banos2019.proposition1),
   ("Prop 1 (metric)", ``Banos2019.proposition1_metric),
   ("Lemma 3", ``Banos2019.lemma3),
   ("Lemma 3 (unrooted)", ``Banos2019.lemma3_unrooted),
   ("Prop 2", ``Banos2019.proposition2),
   ("Lemma 4", ``Banos2019.lemma4),
   ("Cor 1", ``Banos2019.corollary1),
   ("Lemma 5", ``Banos2019.lemma5),
   ("Lemma 6", ``Banos2019.lemma6),
   ("Obs 1", ``Banos2019.observation1),
   ("Thm 2", ``Banos2019.theorem2),
   ("Lemma 7", ``Banos2019.lemma7),
   ("Lemma 8", ``Banos2019.lemma8),
   ("Cor 2", ``Banos2019.corollary2),
   ("Lemma 9", ``Banos2019.lemma9),
   ("Lemma 10", ``Banos2019.lemma10),
   ("Lemma 11", ``Banos2019.lemma11),
   ("Prop 5", ``Banos2019.proposition5),
   ("Cor 3", ``Banos2019.corollary3),
   ("Ex 2", ``Banos2019.example2),
   ("Ex 3", ``Banos2019.example3),
   ("Ex 4", ``Banos2019.example4),
   ("Ex 5", ``Banos2019.example5),
   ("Prop 6", ``Banos2019.proposition6),
   ("Ex 6", ``Banos2019.example6),
   ("Prop 7", ``Banos2019.proposition7),
   ("Prop 8", ``Banos2019.proposition8),
   ("Ex 7", ``Banos2019.example7),
   ("Prop 9", ``Banos2019.proposition9),
   ("Prop 10", ``Banos2019.proposition10),
   ("Thm 3", ``Banos2019.theorem3),
   ("Cor 4", ``Banos2019.corollary4),
   ("Prop 11", ``Banos2019.proposition11),
   ("Lemma 12", ``Banos2019.lemma12),
   ("Lemma 13", ``Banos2019.lemma13),
   ("Lemma 14", ``Banos2019.lemma14),
   ("Lemma 15", ``Banos2019.lemma15),
   ("Lemma 16", ``Banos2019.lemma16),
   ("Thm 4", ``Banos2019.theorem4),
   ("Prop 12", ``Banos2019.proposition12),
   ("Prop 13 (corrected)", ``Banos2019.proposition13),
   ("Prop 13 as printed is false", ``Banos2019.proposition13_asPrinted_false),
   ("Lemma 17", ``Banos2019.lemma17)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of
`palomar/Banos2019/comparator.json`), as the Solution restates them. -/
meta def solutionResults : List Name :=
  [``Banos2019Challenge.theorem3, ``Banos2019Challenge.theorem4, ``Banos2019Challenge.proposition5,
   ``Banos2019Challenge.equation1_balanced, ``Banos2019Challenge.lsa_isLSA,
   ``Banos2019Challenge.root_reaches, ``Banos2019Challenge.not_forGenericParams_false,
   ``Banos2019Challenge.example6, ``Banos2019Challenge.example7]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the libraries: under the root `Banos2019` (`Basic/`, `External/`,
the paper's library and the Solution), but not the Challenge. With several papers, under the root
`ProjectName` or a paper's Solution:
`` (`ProjectName).isPrefixOf m || [`PaperA.Solution, `PaperB.Solution].contains m ``. -/
meta def isLibraryModule (m : Name) : Bool :=
  ((`Banos2019).isPrefixOf m && m != `Banos2019.Challenge) || (`Phylogenetics).isPrefixOf m ||
    (`PhyloNetwork).isPrefixOf m || (`Allman2011).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
