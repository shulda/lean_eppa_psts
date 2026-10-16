import PSTSEPPA.ABO.SourceLiteralY1SelectedRootType2CompleteStageIso
import PSTSEPPA.ABO.CompleteStageWordKernelTransport
import PSTSEPPA.ABO.CompleteStageWordCongruenceReachableCover
import PSTSEPPA.ABO.SourceH1AllLocalG2

/-!
# Entire signed word congruence and concrete finite G₂ Cayley covers:
# selected literal T(Y₁) type-(2) actions from their TRUE source H₁ counterparts

Every genuinely selected off-B paper old quotient point z is
retained with its complete intrinsic component tags. The
signed FULL B-left coset attached at the true ambient value of
z identifies ONLY its anchor with the old vertex. Its LEGALLY
completed paper stage is isomorphic on old/fresh vertices and
formally oriented signed action edges to the corresponding
actual source-H₁ stage via T(Y₁)≃*SourceH₁.

We record a precise necessary/sufficient signed word-action
congruence equivalence between those two REAL complete actions.
Consequently, if equality of group values in the actual
input-dependent finite G₂ acts trivially on all vertices of
the corresponding source-H₁ stage, it also does so on the
literal paper stage. We then construct an actual labelled
Cayley(G₂) graph cover based at EVERY paper stage vertex, hitting
EXACTLY the reachable component in vertices and signed edge tokens.

IMPORTANT: this is a conditional interface. The source-specific
finite G₂ word-value hypothesis is NOT assumed for free:
its discharge uses the exact separately certified local
H₁[A] type-(2) catalogue index and root-translation formula.
Without that subsequent source normalization bridge this file
does NOT assert the unconditional type-(2) G₂ action or
completion of the whole selected rank-one three-family Z₁.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Exactly the same pairs of chronological signed words
act identically at ALL vertices of literal paper T(Y₁) and
source-H₁ actual selected off-B type-(2) COMPLETE actions. -/
theorem literalPaperSelectedOffBCompletedStage_wordActionCongr_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP)
    (p q : LabelWord ι) :
    (∀ x,
      (literalPaperSelectedOffBCompletedStage
        src dst base A hcard root B hBP z).followWord x p =
      (literalPaperSelectedOffBCompletedStage
        src dst base A hcard root B hBP z).followWord x q) ↔
    (∀ y,
      (literalPaperSelectedOffBSourceCompletedStage
        src dst base A hcard root B hBP z).followWord y p =
      (literalPaperSelectedOffBSourceCompletedStage
        src dst base A hcard root B hBP z).followWord y q) := by
  exact
    (literalPaperSelectedOffBCompletedStage
      src dst base A hcard root B hBP z).wordActionCongr_iff_of_bijectiveHom
      (literalPaperSelectedOffBSourceCompletedStage
        src dst base A hcard root B hBP z)
      (literalPaperSelectedOffBCompletedStageHom
        src dst base A hcard root B hBP z)
      (literalPaperSelectedOffBCompletedStageHom_bijective
        src dst base A hcard root B hBP z).1 p q

/-- The concrete finite input-derived G₂ word kernel transfers
from the true SourceH₁ selected off-B stage to the paper
T(Y₁) selected off-B stage, with no extra assumption about
ambient coordinate injectivity or global H₁ retractability.
The source-G₂ congruence itself is an EXPLICIT hypothesis. -/
theorem literalPaperSelectedOffB_G2_wordValue_congr_of_source
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP)
    (hSource : ∀ p q : LabelWord ι,
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q →
      ∀ y,
        (literalPaperSelectedOffBSourceCompletedStage
          src dst base A hcard root B hBP z).followWord y p =
        (literalPaperSelectedOffBSourceCompletedStage
          src dst base A hcard root B hBP z).followWord y q)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
      (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ x,
      (literalPaperSelectedOffBCompletedStage
        src dst base A hcard root B hBP z).followWord x p =
      (literalPaperSelectedOffBCompletedStage
        src dst base A hcard root B hBP z).followWord x q :=
  (literalPaperSelectedOffBCompletedStage_wordActionCongr_iff
    src dst base A hcard root B hBP z p q).mpr (hSource p q hpq)

/-- Once the ACTUAL source rank-two local-G₂ word congruence is
discharged, the based labelled finite Cayley(G₂) morphism
covers the TRUE paper selected off-B complete action. -/
noncomputable def literalPaperSelectedOffB_G2CayleyHom_of_source
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP)
    (hSource : ∀ p q : LabelWord ι,
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q →
      ∀ y,
        (literalPaperSelectedOffBSourceCompletedStage
          src dst base A hcard root B hBP z).followWord y p =
        (literalPaperSelectedOffBSourceCompletedStage
          src dst base A hcard root B hBP z).followWord y q)
    (u : IsolatedCosetGluing.Vertex
      (Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A)))
      (sourceLiteralY1 src dst).transitionSubgroupGenerator B
      (sourceLiteralY1SelectedRootAmbientValue
        src dst base A hcard root (allProperCosetFamily A) z.vertex)) :
    LabelledGraphHom
      (cayleyGraph (sourceAllLocalG2Generator src dst)).toEGraph.toLabelledGraph
      (literalPaperSelectedOffBCompletedStage
        src dst base A hcard root B hBP z).toEGraph.toLabelledGraph :=
  (literalPaperSelectedOffBCompletedStage
    src dst base A hcard root B hBP z).cayleyCoverFromWordCongruence
      (sourceAllLocalG2Generator src dst)
      (sourceAllLocalG2Generator_isGenerated src dst)
      (literalPaperSelectedOffB_G2_wordValue_congr_of_source
        src dst base A hcard root B hBP z hSource) u

end ABO
end PSTSEPPA
