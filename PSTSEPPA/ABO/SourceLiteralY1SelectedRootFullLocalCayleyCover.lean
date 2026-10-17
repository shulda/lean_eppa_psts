import PSTSEPPA.ABO.LocalCompleteCayleyStageCover
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainOutsideASupport
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainAConnected

/-!
# TRUE complete local G[A] signed Cayley cover of EVERY printed rooted P_A stage

The printed first-rank original-root P_A stage is the actual
component-tagged old/fresh quotient constructed from ORIGINAL
incomplete T(Y₁) input signed edges, legally completed by
adding only absent stationary positive/negative loops.

The independent formal steps now supply:
  (i)  one TRUE finite labelled G=T(X₂^all)↠Transition(T) quotient
       onto this exact rooted printed plain completed stage;
  (ii) all actual OLD/FRESH stage edges before legal completion
       use labels in A, hence every generator outside A fixes
       each stage vertex and equals 1 in Transition(T);
  (iii) all printed stage vertices are reachable from any
       selected root by one chronological signed A-word.

We combine them using the genuine LOCAL subgroup Q_A:
    G[A] = generatedSubgroup (sourceLiteralY1X2AllGenerator) A
with all labels outside A completed by 1. Thus for EVERY
genuine printed root `u` there is a complete labelled graph
SURJECTION

    Cayley(G[A])  ↠  printed_original_root_P_A_complete_stage,

based at 1↦u, surjective on all real tagged old/fresh
vertices and EVERY formal oriented signed edge token,
including both inverse signs and legal stationary loops.

This is the actual source-facing rank-two LOCAL group stage
cover needed as input to corrected ABO Theorem 4.7(ii).
The paper's further root-normalized old G-cover compatibility
and H/G mixed-support identification must still be composed;
the theorem alone is not the completed Theorem 4.7(ii)/(iii),
nor Condition 5.2, exact equivariant Z₁ selection or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The COMPLETE signed local T(X₂^all)[A] Cayley graph,
including both formal inverse tokens and labels outside A
completed by 1, maps to EVERY true rooted printed P_A
stage. The chosen local identity maps to exactly u, which
may be any OLD or FRESH component-tagged quotient point. -/
noncomputable def sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A))) :
    LabelledGraphHom
      (cayleyGraph (trivialCompletionGenerator
        (sourceLiteralY1X2AllGenerator src dst) A)).toEGraph.toLabelledGraph
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).toEGraph.toLabelledGraph :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).localGeneratedCayleyStageHom
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root)
      A
      (sourceLiteralY1SelectedRootPlain_transitionOutsideA_one
        src dst base A hcard root)
      u

/-- Exact source-normalized identity image in the tagged
printed P_A stage. No ambient H-value identification. -/
theorem sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom_one
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A))) :
    (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
      src dst base A hcard root u).onVertex 1 = u :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).localGeneratedCayleyStageHom_one
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root)
      A
      (sourceLiteralY1SelectedRootPlain_transitionOutsideA_one
        src dst base A hcard root)
      u

/-- REAL LOCAL Cayley(T(X₂^all)[A]) surjectivity
onto the ENTIRE signed printed P_A stage vertex type.
Every genuine old/fresh tag appears in the image. -/
theorem sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom_vertex_surjective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A))) :
    Function.Surjective
      (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
        src dst base A hcard root u).onVertex :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).localGeneratedCayleyStageHom_vertex_surjective
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root)
      A
      (sourceLiteralY1SelectedRootPlain_transitionOutsideA_one
        src dst base A hcard root)
      u
      ((sourceLiteralY1SelectedRootPlain_AWordConnected
        src dst base A hcard root) u)

/-- Every real oriented signed P_A edge token, whether
old or fresh, positive or inverse, moving or a legally
added stationary loop, is covered by an actual FULL
local Cayley(T(X₂^all)[A]) edge token. -/
theorem sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom_edge_surjective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A))) :
    Function.Surjective
      (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
        src dst base A hcard root u).onEdge :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).localGeneratedCayleyStageHom_edge_surjective
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root)
      A
      (sourceLiteralY1SelectedRootPlain_transitionOutsideA_one
        src dst base A hcard root)
      u
      ((sourceLiteralY1SelectedRootPlain_AWordConnected
        src dst base A hcard root) u)

end ABO
end PSTSEPPA
