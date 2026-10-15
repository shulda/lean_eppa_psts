import PSTSEPPA.ABO.SourceLiteralY1MultiCosetRawGraphIso
import PSTSEPPA.ABO.SourceLabelEdgeQuotientGraphIso

/-!
# Exact signed EDGE quotient transport: original paper T(Y₁) and source H₁

The original paper T(Y₁) and source H₁ old-edge preimages have a
genuine vertex/edge bijective signed RAW multi-coset graph map,
conditional only on supplying the ACTUAL intersection-supported
vertex gluing setoid. Here we quotient EVERY raw oriented signed
edge token by equality of its already glued SOURCE vertex and its
FULL SIGNED LABEL, as required by corrected ABO (3.10).

A deterministic EGraph additionally needs source-and-label-to-target
congruence. We prove that this congruence transfers across the true
raw graph isomorphism; it is NOT asserted for the whole unselected
T(Y₁) preimage from global retractability. Once congruence is
supplied on the paper side, an actual isomorphism of the FINAL
source-and-label edge quotient EGraphs follows, bijective on glued
vertices and signed directed EDGE CLASSES and reflecting all paths.

The remaining geometrical task is to discharge the precise setoid
and congruence premises for the SELECTED original root A-components
via their source H₁[A] rank-two local normalization. This is not
yet a selected Z₁ augmentation or final PSTS EPPA theorem.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The actual original-paper tagged RAW multi-coset graph over
a supplied EXACT old B∩C intersection-support gluing setoid. -/
noncomputable abbrev sourceLiteralY1PaperMultiCosetRawGraph
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P)) :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).multiCosetRawGraphOfSetoid P sL

/-- The original source-H₁ raw graph on the EXACT transported
intersection-support quotient of component-tagged coset points. -/
noncomputable abbrev sourceLiteralY1SourceMultiCosetRawGraph
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q) :=
  (sourceH1OriginalSkeleton src dst base).multiCosetRawGraphOfSetoid
    P (sourceLiteralY1DirectTransportedMultiCosetSetoid src dst base P sL hL)

/-- The signed raw-edge relation may be quotient-completed on
the source H₁ side whenever it can on the paper T(Y₁) side.
The transport is genuinely across source/edge BIJECTIONS,
not equality of ambient H₁ group coordinates. -/
theorem sourceLiteralY1MultiCosetRawTargetCongruent_transport
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q)
    (hG : (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL).SourceLabelTargetCongruent) :
    (sourceLiteralY1SourceMultiCosetRawGraph src dst base P sL hL).SourceLabelTargetCongruent :=
  sourceLabelTargetCongruent_transport
    (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL)
    (sourceLiteralY1SourceMultiCosetRawGraph src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetVertexEquiv src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P)
    (sourceLiteralY1DirectMultiCosetRawGraph_source_natural src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv_label src dst base P)
    (fun e => (sourceLiteralY1DirectMultiCosetRawEdgeEquiv_inv src dst base P e).symm)
    hG

/-- Paper old-input exact multi-coset completed graph, whose edges
are real oriented raw tokens modulo EQUAL GLUED SOURCE+SIGNED LABEL.
The premise is essential: the whole H₁ is NOT assumed retractable. -/
noncomputable abbrev sourceLiteralY1PaperMultiCosetEdgeQuotientEGraph
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P))
    (hG : (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL).SourceLabelTargetCongruent) :=
  sourceLabelGraphQuotientEGraph
    (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL) hG

/-- The corresponding exact SOURCE H₁ signed quotient EGraph.
Component tags are retained before the deterministic edge quotient. -/
noncomputable abbrev sourceLiteralY1SourceMultiCosetEdgeQuotientEGraph
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q)
    (hG : (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL).SourceLabelTargetCongruent) :=
  sourceLabelGraphQuotientEGraph
    (sourceLiteralY1SourceMultiCosetRawGraph src dst base P sL hL)
    (sourceLiteralY1MultiCosetRawTargetCongruent_transport src dst base P sL hL hG)

/-- The true signed graph isomorphism on final corrected ABO
source-and-label EDGE QUOTIENTS, not just disjoint raw edge tokens.
Every target/source/inverse/label equality is inherited from
certified original old/new signed edge transport. -/
noncomputable def sourceLiteralY1MultiCosetEdgeQuotientGraphHom
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q)
    (hG : (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL).SourceLabelTargetCongruent) :
    LabelledGraphHom
      (sourceLiteralY1PaperMultiCosetEdgeQuotientEGraph src dst base P sL hG).toLabelledGraph
      (sourceLiteralY1SourceMultiCosetEdgeQuotientEGraph src dst base P sL hL hG).toLabelledGraph :=
  sourceLabelGraphQuotientHom
    (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL)
    (sourceLiteralY1SourceMultiCosetRawGraph src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetVertexEquiv src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P)
    (sourceLiteralY1DirectMultiCosetRawGraph_source_natural src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv_label src dst base P)
    (fun e => (sourceLiteralY1DirectMultiCosetRawEdgeEquiv_inv src dst base P e).symm)
    hG
    (sourceLiteralY1MultiCosetRawTargetCongruent_transport src dst base P sL hL hG)

/-- Both glued original-cover vertex quotients AND the completed
formal oriented signed edge classes match bijectively. -/
theorem sourceLiteralY1MultiCosetEdgeQuotientGraphHom_bijective
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q)
    (hG : (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL).SourceLabelTargetCongruent) :
    Function.Bijective
      (sourceLiteralY1MultiCosetEdgeQuotientGraphHom src dst base P sL hL hG).onVertex ∧
    Function.Bijective
      (sourceLiteralY1MultiCosetEdgeQuotientGraphHom src dst base P sL hL hG).onEdge := by
  exact sourceLabelGraphQuotientHom_bijective
    (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL)
    (sourceLiteralY1SourceMultiCosetRawGraph src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetVertexEquiv src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv src dst base P)
    (sourceLiteralY1DirectMultiCosetRawGraph_source_natural src dst base P sL hL)
    (sourceLiteralY1DirectMultiCosetRawEdgeEquiv_label src dst base P)
    (fun e => (sourceLiteralY1DirectMultiCosetRawEdgeEquiv_inv src dst base P e).symm)
    hG
    (sourceLiteralY1MultiCosetRawTargetCongruent_transport src dst base P sL hL hG)

/-- Full signed PATH reflection between the two deterministic
completed exact edge quotient graphs, conditional on the explicit
genuine paper-side setoid and target-congruence premises. -/
theorem sourceLiteralY1MultiCosetEdgeQuotientGraphHom_follows_iff
    (src dst : ι → V) (base : V)
    (P : CosetFamilySpec (Finset.univ : Finset ι))
    (sL : Setoid ((sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawVertex P))
    (hL : ∀ p q, sL.r p q ↔
      (sourceLiteralY1DirectOriginalSkeleton src dst base).MultiCosetRawRelated P p q)
    (hG : (sourceLiteralY1PaperMultiCosetRawGraph src dst base P sL).SourceLabelTargetCongruent)
    (u v : Quotient sL)
    (w : LabelWord ι) :
    (sourceLiteralY1PaperMultiCosetEdgeQuotientEGraph src dst base P sL hG).Follows
      u w v ↔
    (sourceLiteralY1SourceMultiCosetEdgeQuotientEGraph src dst base P sL hL hG).Follows
      ((sourceLiteralY1MultiCosetEdgeQuotientGraphHom src dst base P sL hL hG).onVertex u)
      w
      ((sourceLiteralY1MultiCosetEdgeQuotientGraphHom src dst base P sL hL hG).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (sourceLiteralY1MultiCosetEdgeQuotientGraphHom src dst base P sL hL hG)
    (sourceLiteralY1MultiCosetEdgeQuotientGraphHom_bijective src dst base P sL hL hG).1
    (sourceLiteralY1MultiCosetEdgeQuotientGraphHom_bijective src dst base P sL hL hG).2
    u v w

end ABO
end PSTSEPPA
