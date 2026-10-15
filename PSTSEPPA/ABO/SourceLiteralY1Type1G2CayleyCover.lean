import PSTSEPPA.ABO.SourceLiteralY1Type1CompletedStageIso
import PSTSEPPA.ABO.SourceH1AllType1G2WordAction
import PSTSEPPA.ABO.CompleteStageWordKernelTransport
import PSTSEPPA.ABO.CompleteStageWordCongruenceReachableCover

/-!
# Actual finite G₂ action on LITERAL printed T(Y₁) anchored type-(1) stages

The corrected ABO rank-one Z₁ contains genuine anchored augmented
clusters CL(T(Y₁)[A],P) ∪ vT(Y₁)[D] for |A|=2, D⊊A and a true
old cluster anchor v. We have proved that the same-labelled group
isomorphism T(Y₁)≃*SourceH₁ identifies all OLD original cluster
subgroup pieces, their attached left D-cosets, oriented signed
edges and their LEGAL missing-label stationary-loop completions.

The separate source-H₁ theorem shows that the CONCRETE finite
input-dependent second group G₂ controls every signed complete
word action of every genuine anchored source type-(1) stage.
We transport the actual old-cluster anchor to the corresponding
source index and pull the word-action congruence BACK through the
true vertex/edge-bijective complete stage morphism.

Thus equal G₂ word values act identically at EVERY vertex of the
LITERAL paper anchored complete stage. A based labelled Cayley(G₂)
cover exists at every printed point, reaching exactly its connected
stage component on vertices AND formal signed directed edges.

No fictitious globally retractable H₁, abstract auxiliary G₂,
coset-tag coordinate collapse or artificial X₁ original edge.
The full printed type-(1) dependent index/family, type-(2)
augmented stages, higher Section 4/5 induction and PSTS EPPA
remain separate tasks.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Equality of signed word values in the ACTUAL finite input
G₂ forces identical completed signed actions at ALL vertices of
a true literal printed T(Y₁) anchored type-(1) stage. -/
theorem sourceG2LiteralY1Type1_wordValue_congr
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (P : ClusterSpec A)
    (D : {D : Finset ι // D ⊂ A})
    (v : (sourceLiteralY1 src dst).transitionGroup)
    (hv : v ∈ P.VertexSet
      (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ x : (P.augmentedCayleySubgraph
      (sourceLiteralY1 src dst).transitionSubgroupGenerator
      D.1 D.2.subset v).Vertex,
      (P.augmentedTrivialStage
        (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
        D.1 D.2.subset v).followWord x p =
      (P.augmentedTrivialStage
        (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
        D.1 D.2.subset v).followWord x q := by
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  let vH : SourceH1 src dst := E v
  have hvH : vH ∈ P.VertexSet (sourceH1Generator src dst) := by
    obtain ⟨C, hCP, hC⟩ := hv
    exact ⟨C, hCP,
      (labelledMulEquiv_mem_generatedSubgroup_iff
        (sourceLiteralY1 src dst).transitionSubgroupGenerator
        (sourceH1Generator src dst) E
        (sourceLiteralY1Generator_to_sourceH1 src dst) C v).mpr hC⟩
  let j : ClusterSpec.augmentedType1Index
      (sourceH1Generator src dst) A :=
    ⟨P, ⟨D, ⟨vH, hvH⟩⟩⟩
  let G := P.augmentedTrivialStage
    (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    D.1 D.2.subset v
  let H := P.augmentedTrivialStage
    (gen := sourceH1Generator src dst) D.1 D.2.subset vH
  let F := sourceLiteralY1Type1CompletedStageHom
    src dst P D.1 D.2.subset v
  have hSource :
      ∀ y : (P.augmentedCayleySubgraph
        (sourceH1Generator src dst) D.1 D.2.subset vH).Vertex,
        H.followWord y p = H.followWord y q := by
    intro y
    change (ClusterSpec.augmentedType1Stage j).followWord y p =
      (ClusterSpec.augmentedType1Stage j).followWord y q
    exact sourceG2OriginalH1AllType1_fibre_wordValue_congr
      src dst A hcard p q hpq j y
  exact G.wordActionCongr_of_injectiveHom H F
    (sourceLiteralY1Type1CompletedStageHom_bijective
      src dst P D.1 D.2.subset v).1.1
    p q hSource

/-- Actual generator-preserving signed Cayley(G₂) cover of any
true anchored complete printed type-(1) rank-one stage. -/
noncomputable def sourceG2LiteralY1Type1CayleyHom
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (P : ClusterSpec A)
    (D : {D : Finset ι // D ⊂ A})
    (v : (sourceLiteralY1 src dst).transitionGroup)
    (hv : v ∈ P.VertexSet
      (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    (u : (P.augmentedCayleySubgraph
      (sourceLiteralY1 src dst).transitionSubgroupGenerator
      D.1 D.2.subset v).Vertex) :
    LabelledGraphHom
      (cayleyGraph (sourceAllLocalG2Generator src dst)).toEGraph.toLabelledGraph
      (P.augmentedTrivialStage
        (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
        D.1 D.2.subset v).toEGraph.toLabelledGraph :=
  (P.augmentedTrivialStage
    (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    D.1 D.2.subset v).cayleyCoverFromWordCongruence
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceG2LiteralY1Type1_wordValue_congr
        src dst A hcard P D v hv) u

/-- The labelled Cayley(G₂) cover begins at its true paper
augmented-cluster vertex. -/
theorem sourceG2LiteralY1Type1CayleyHom_one
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (P : ClusterSpec A)
    (D : {D : Finset ι // D ⊂ A})
    (v : (sourceLiteralY1 src dst).transitionGroup)
    (hv : v ∈ P.VertexSet
      (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    (u : (P.augmentedCayleySubgraph
      (sourceLiteralY1 src dst).transitionSubgroupGenerator
      D.1 D.2.subset v).Vertex) :
    (sourceG2LiteralY1Type1CayleyHom
      src dst A hcard P D v hv u).onVertex 1 = u :=
  (P.augmentedTrivialStage
    (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    D.1 D.2.subset v).cayleyCoverFromWordCongruence_one
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceG2LiteralY1Type1_wordValue_congr
        src dst A hcard P D v hv) u

/-- Image on actual vertices is EXACTLY the reachable component
of the chosen printed type-(1) anchored complete stage vertex. -/
theorem sourceG2LiteralY1Type1CayleyHom_vertex_range
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (P : ClusterSpec A)
    (D : {D : Finset ι // D ⊂ A})
    (v : (sourceLiteralY1 src dst).transitionGroup)
    (hv : v ∈ P.VertexSet
      (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    (u : (P.augmentedCayleySubgraph
      (sourceLiteralY1 src dst).transitionSubgroupGenerator
      D.1 D.2.subset v).Vertex) :
    Set.range (sourceG2LiteralY1Type1CayleyHom
      src dst A hcard P D v hv u).onVertex =
    {y | (P.augmentedTrivialStage
      (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
      D.1 D.2.subset v).Reachable u y} :=
  (P.augmentedTrivialStage
    (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    D.1 D.2.subset v).cayleyCoverFromWordCongruence_vertex_range
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceG2LiteralY1Type1_wordValue_congr
        src dst A hcard P D v hv) u

/-- Every formal oriented signed action-edge token in the true
reachable component of a printed anchored type-(1) stage,
including its fixed loops, is hit by the same G₂-Cayley map. -/
theorem sourceG2LiteralY1Type1CayleyHom_edge_range
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (P : ClusterSpec A)
    (D : {D : Finset ι // D ⊂ A})
    (v : (sourceLiteralY1 src dst).transitionGroup)
    (hv : v ∈ P.VertexSet
      (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    (u : (P.augmentedCayleySubgraph
      (sourceLiteralY1 src dst).transitionSubgroupGenerator
      D.1 D.2.subset v).Vertex) :
    Set.range (sourceG2LiteralY1Type1CayleyHom
      src dst A hcard P D v hv u).onEdge =
    {e : ActionEdge
      (P.augmentedCayleySubgraph
        (sourceLiteralY1 src dst).transitionSubgroupGenerator
        D.1 D.2.subset v).Vertex ι |
      (P.augmentedTrivialStage
        (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
        D.1 D.2.subset v).Reachable u
          ((P.augmentedTrivialStage
            (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
            D.1 D.2.subset v).source e)} :=
  (P.augmentedTrivialStage
    (gen := (sourceLiteralY1 src dst).transitionSubgroupGenerator)
    D.1 D.2.subset v).cayleyCoverFromWordCongruence_edge_range
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (sourceG2LiteralY1Type1_wordValue_congr
        src dst A hcard P D v hv) u

end ABO
end PSTSEPPA
