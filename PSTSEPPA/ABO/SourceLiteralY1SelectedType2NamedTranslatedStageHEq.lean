import PSTSEPPA.ABO.SourceLiteralY1SelectedType2NamedSourceStageAgreement
import PSTSEPPA.ABO.IsolatedCosetCompletedStageHEqNaturality
import PSTSEPPA.ABO.SourceH1SelectedOffBLocalIndexRootExact
import PSTSEPPA.ABO.RootedOriginalSourceCompletedAugmentationTransport

/-!
# Original selected SourceH₁ type-(2) action equals its actual root-translated G₂ stage

For a TRUE selected literal-paper off-B type-(2) root z, its old
component-tagged B-coset quotient vertex transports to a genuine
original SourceH₁ old vertex zS. The finite G₂ catalogue index
is not chosen from ambient coordinates: the certified local
H₁[A] normalization produces the exact off-B index k=(B,w).

Two mathematically independent exact equalities hold:
  (1) the REAL original old root is e(w)=zS;
  (2) the actual SourceH₁ new full B-coset anchor is
      sourceValue(zS)=rootH·localValue(w).

The checked generic complete isolated-coset HEq API requires
BOTH equalities, then compares the two dependently typed
full signed LEGALLY COMPLETE actions: one independently named
at the original old source zS, the other root-translated from
the exact local H₁[A] G₂ stage. The proof never assumes global
SourceH₁ retractability or identifies distinct old vertices
with coincident ambient group coordinates.

This exact stage-model agreement is needed to transport the
unconditional actual finite input-dependent G₂ word action
from the root-translated source-H₁ type-(2) model onto the
corresponding literal paper T(Y₁) type-(2) stage.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Genuine ACTUAL ROOT-TRANSLATED original SourceH₁ type-(2)
complete signed action selected by the printed paper off-B root,
at its independently certified exact LOCAL G₂ index (B,w). -/
noncomputable abbrev literalPaperSelectedOffBSourceTranslatedLocalG2Stage
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :=
  let rootH := (sourceH1EquivLiteralY1Transition src dst).symm root
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨rootH, by trivial⟩
  let P := allProperCosetFamily A
  let zS := (sourceLiteralY1RootToH1MultiCosetVertexEquiv
    src dst base A hcard root P) z.vertex
  let hOffS := (sourceLiteralY1SelectedRootOffB_iff
    src dst base A hcard root P B hBP z.vertex).mp z.offB
  let k := sourceH1OriginalSelectedOffBLocalG2Index
    src dst base A hcard rootH B hBP zS hOffS
  K.rootedTranslatedSourceOffCosetCompletedStage
    A hcard (sourceH1_twoRetractable src dst) r
    B hBP k.2.1
    ((K.rootedLocalMultiCosetOffCoset_iff A hcard
      (sourceH1_twoRetractable src dst) r P B hBP k.2.1).mp k.2.2)

/-- Exact HEq of completed signed type-(2) structures:
the canonical SOURCE-H₁ stage at the real paper-transported
old quotient point and the ROOT-TRANSLATED local catalogue
model have the same vertices, signed oriented action edges,
and added stationary loops as dependent objects. -/
theorem literalPaperSelectedOffBNamedSourceCompletedStage_heq_translated
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    HEq
      (literalPaperSelectedOffBNamedSourceCompletedStage
        src dst base A hcard root B hBP z)
      (literalPaperSelectedOffBSourceTranslatedLocalG2Stage
        src dst base A hcard root B hBP z) := by
  let rootH := (sourceH1EquivLiteralY1Transition src dst).symm root
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨rootH, by trivial⟩
  let hret := sourceH1_twoRetractable src dst
  let P := allProperCosetFamily A
  let F := sourceLiteralY1RootToH1MultiCosetVertexEquiv
    src dst base A hcard root P
  let zS := F z.vertex
  have hOffS :
      ¬ ∃ p : (sourceH1OriginalRootComponent src dst base A rootH).AttachedCosetVertex B,
        sourceH1SelectedRootBInclude src dst base A hcard rootH P B hBP p = zS :=
    (sourceLiteralY1SelectedRootOffB_iff
      src dst base A hcard root P B hBP z.vertex).mp z.offB
  let k := sourceH1OriginalSelectedOffBLocalG2Index
    src dst base A hcard rootH B hBP zS hOffS
  let e := K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret r P
  have hRoot : zS = e k.2.1 :=
    (sourceH1OriginalSelectedOffBLocalG2Index_root_exact
      src dst base A hcard rootH B hBP zS hOffS).symm
  have hAnchor :
      sourceH1OriginalSelectedRootAmbientValue
        src dst base A hcard rootH P zS =
      rootH * ((K.intrinsicComponentLocalSlice A r).multiCosetAmbientValue
        P ((K.intrinsicComponentLocalSlice A r).admissible_of_card_le_two hcard.le)
        (isGenerated_trivialCompletionGenerator (sourceH1Generator src dst) A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2 hret A hcard.le) k.2.1 :
        SourceH1 src dst) :=
    sourceH1OriginalSelectedOffB_ambientValue_eq_root_mul_localValue
      src dst base A hcard rootH B hBP zS hOffS
  let G := sourceH1OriginalRankTwoRootCompletedEGraph
    src dst base A hcard rootH P
  let hOffT :=
    (K.rootedLocalMultiCosetOffCoset_iff A hcard hret r P
      B hBP k.2.1).mp k.2.2
  have hMissingN :
      ∀ edge, G.source edge = zS →
        signedBase (G.label edge) ∉ B := by
    exact z.source_noOldBEdges src dst base A hcard root B hBP
  have hMissingT :
      ∀ edge, G.source edge = e k.2.1 →
        signedBase (G.label edge) ∉ B := by
    intro edge he
    exact K.rootedAmbientOffCoset_no_old_B_edge
      A hcard hret r B hBP k.2.1 hOffT edge he
  have hPaired :
      G.LocallyPairedLabels :=
    sourceH1OriginalRootAllProper_locallyPaired
      src dst base A hcard rootH
  exact IsolatedCosetGluing.completedStage_heq_of_anchor_and_root_eq
    G (sourceH1Generator src dst) B hAnchor hRoot
    hMissingN hMissingT hPaired hPaired

end ABO
end PSTSEPPA
