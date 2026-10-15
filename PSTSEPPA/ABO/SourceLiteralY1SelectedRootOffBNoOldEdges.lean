import PSTSEPPA.ABO.SourceLiteralY1SelectedRootOffBIndexEquiv
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootMissingSignedEdges
import PSTSEPPA.ABO.RootedSourceOffCosetNoOldEdges
import PSTSEPPA.ABO.SourceH1OriginalRankTwoRawTargetCongruence

/-!
# Actual printed rank-one type-(2) OFF-B root has no old B-signed edge

The literal corrected ABO Definition 5.3 type-(2) selection is
not arbitrary: at a genuine selected original-root full proper
P_A coset quotient vertex z lying OUTSIDE the image of the whole
component-tagged B-constituent, attach a fresh full B-left coset.

The paper↔source exact OFF-B index equivalence already proves
that the corresponding original SourceH₁ vertex has the same
non-membership. The independently formalized rank-two local
H₁[A] retractable normalization proves that NO genuinely OLD
outgoing B-labelled signed edge exists at that source point,
even if its ambient group coordinate coincides with some B
constituent point. The genuine paper/source signed EGraph
isomorphism then reflects exactly that edge-absence property.

Thus the precise `IsolatedCosetGluing.gluedEGraph` deterministic
old/new augmentation premise is automatically discharged on
EVERY ACTUAL selected literal T(Y₁) off-B root, for |A|=2
and B∈P_A, including empty B, inverse labels and old loops.

This statement does not yet identify the attached new B-coset
signed graph or its legal fixed-loop completion / G₂ action.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The original source-H₁ selected |A|=2 proper-family root
quotient vertex z has no ACTUAL old outgoing ±B-labelled signed
edge whenever it is off the full component-tagged B-constituent.
This follows from H₁[A]'s local retractable source theorem, NOT
from globally retractable H₁ or ambient group coset equality. -/
theorem sourceH1OriginalRankTwoRoot_offB_noSignedEdges
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : Quotient
      (sourceH1OriginalRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A)))
    (hOff :
      ¬ ∃ q : (sourceH1OriginalRootComponent
        src dst base A root).AttachedCosetVertex B,
        sourceH1SelectedRootBInclude
          src dst base A hcard root (allProperCosetFamily A)
          B hBP q = z) :
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A)).NoSignedBEdgesAt B z := by
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let P := allProperCosetFamily A
  let hret := sourceH1_twoRetractable src dst
  let Q := K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret r P
  obtain ⟨w, hw⟩ := Q.surjective z
  have hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A r).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret r P B hBP q =
          Q w := by
    simpa only [hw] using hOff
  intro e he
  have hOldSource :
      (K.rootedAmbientMultiCosetCompletedEGraph
        A hcard hret r P).source e = Q w := by
    simpa only [hw] using he
  exact K.rootedAmbientOffCoset_no_old_B_edge
    A hcard hret r B hBP w hOffSource e hOldSource

/-- Every ACTUAL LITERAL paper T(Y₁) rank-two original-root
selected off-B coset-extension point has no old outgoing
B-signed edge. This supplies the exact legal deterministic
fresh B-left-coset gluing premise, and keeps all old component
tags distinct regardless of equal ambient coordinates. -/
theorem sourceLiteralY1SelectedRoot_offB_noSignedEdges
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A)))
    (hOff :
      ¬ ∃ p : (sourceLiteralY1DirectRootComponent
        src dst base A root).AttachedCosetVertex B,
        sourceLiteralY1SelectedRootBInclude
          src dst base A hcard root (allProperCosetFamily A)
          B hBP p = z) :
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root (allProperCosetFamily A)).NoSignedBEdgesAt B z := by
  let rootH := (sourceH1EquivLiteralY1Transition src dst).symm root
  let P := allProperCosetFamily A
  let F := sourceLiteralY1RootToH1MultiCosetVertexEquiv
    src dst base A hcard root P
  have hOffH :
      ¬ ∃ q : (sourceH1OriginalRootComponent src dst base A rootH).AttachedCosetVertex B,
        sourceH1SelectedRootBInclude src dst base A hcard rootH
          P B hBP q = F z :=
    (sourceLiteralY1SelectedRootOffB_iff
      src dst base A hcard root P B hBP z).mp hOff
  have hMissingH :
      (sourceH1OriginalRankTwoRootCompletedEGraph
        src dst base A hcard rootH P).NoSignedBEdgesAt B (F z) :=
    sourceH1OriginalRankTwoRoot_offB_noSignedEdges
      src dst base A hcard rootH B hBP (F z) hOffH
  exact (sourceLiteralY1SelectedRoot_noSignedBEdgesAt_iff
    src dst base A hcard root P B z).mpr hMissingH

end ABO
end PSTSEPPA
