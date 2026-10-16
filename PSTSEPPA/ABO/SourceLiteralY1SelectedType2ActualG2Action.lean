import PSTSEPPA.ABO.IsolatedCosetCompletedStageWordCongruence
import PSTSEPPA.ABO.SourceH1SelectedOffBTranslatedG2WordAction
import PSTSEPPA.ABO.SourceH1SelectedOffBLocalIndexRootExact
import PSTSEPPA.ABO.SourceLiteralY1SelectedType2G2WordActionTransport

/-!
# Actual finite G₂ word action on every literal T(Y₁) selected type-(2) stage

The corrected ABO first-rank off-B type-(2) stage is made from a
genuinely selected OLD component-tagged quotient point z, with
its exact B-constituent exclusion, and a new full B-left coset
attached at its TRUE ambient value. In the source model, the
original actual H₁[A] local normalization gives an actual finite
G₂ type-(2) (B,w) index.

Two separately certified equations are needed:
* the old tagged source quotient root is EXACTLY e(w)=zS,
  not merely a point with the same ambient H₁ coordinate;
* its full B-left-coset anchor is equal to rootH*localValue(w).
We apply the actual signed complete-stage word-congruence transfer
under BOTH equalities. By the already-certified paper↔source
complete signed EGraph iso, arbitrary G₂ word-value equality
therefore acts identically on EVERY vertex of the genuine printed
T(Y₁) type-(2) completed action. No source word-action premise
remains. The existing constructive Cayley(G₂) API gives the true
based labelled signed graph cover of its reachable component.

This still concerns the first-rank rank-two selected TYPE-(2)
family. Global corrected Section-5 Z₁ selection/equivariance,
Condition 5.2/Theorem 4.7 for arbitrary ranks, higher Yₖ/Zₖ,
reflecting group, concrete fibre-MAX and finite PSTS EPPA
remain separate gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The actual original SourceH₁ selected off-B type-(2)
LEGALLY completed action obeys the concrete finite input-derived
G₂ whole-stage signed word-action congruence, with no extra
hypothesis about the source stage or a hypothetical group action. -/
theorem literalPaperSelectedOffBSource_G2_wordValue_congr
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ y,
      (literalPaperSelectedOffBSourceCompletedStage
        src dst base A hcard root B hBP z).followWord y p =
      (literalPaperSelectedOffBSourceCompletedStage
        src dst base A hcard root B hBP z).followWord y q := by
  let rootH := (sourceH1EquivLiteralY1Transition src dst).symm root
  let P := allProperCosetFamily A
  let G := sourceH1OriginalRankTwoRootCompletedEGraph
    src dst base A hcard rootH P
  let zS := (sourceLiteralY1RootToH1MultiCosetVertexEquiv
    src dst base A hcard root P) z.vertex
  have hOffS :
      ¬ ∃ t : (sourceH1OriginalRootComponent src dst base A rootH).AttachedCosetVertex B,
        sourceH1SelectedRootBInclude
          src dst base A hcard rootH P B hBP t = zS :=
    (sourceLiteralY1SelectedRootOffB_iff
      src dst base A hcard root P B hBP z.vertex).mp z.offB
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨rootH, by trivial⟩
  let hret := sourceH1_twoRetractable src dst
  let k := sourceH1OriginalSelectedOffBLocalG2Index
    src dst base A hcard rootH B hBP zS hOffS
  let e := K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret r P
  have hRoot : zS = e k.2.1 :=
    (sourceH1OriginalSelectedOffBLocalG2Index_root_exact
      src dst base A hcard rootH B hBP zS hOffS).symm
  have hAnchor :
      (sourceH1EquivLiteralY1Transition src dst).symm
        (sourceLiteralY1SelectedRootAmbientValue
          src dst base A hcard root P z.vertex) =
      rootH * ((K.intrinsicComponentLocalSlice A r).multiCosetAmbientValue
        P ((K.intrinsicComponentLocalSlice A r).admissible_of_card_le_two hcard.le)
        (isGenerated_trivialCompletionGenerator (sourceH1Generator src dst) A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2 hret A hcard.le) k.2.1 :
        SourceH1 src dst) := by
    calc
      (sourceH1EquivLiteralY1Transition src dst).symm
          (sourceLiteralY1SelectedRootAmbientValue
            src dst base A hcard root P z.vertex) =
        sourceH1OriginalSelectedRootAmbientValue
          src dst base A hcard rootH P zS :=
        literalPaperSelectedOffBSourceAnchor_eq
          src dst base A hcard root B hBP z
      _ = rootH * ((K.intrinsicComponentLocalSlice A r).multiCosetAmbientValue
            P ((K.intrinsicComponentLocalSlice A r).admissible_of_card_le_two hcard.le)
            (isGenerated_trivialCompletionGenerator (sourceH1Generator src dst) A)
            (retractable_trivialCompletionGenerator_of_kRetractable
              (sourceH1Generator src dst) 2 hret A hcard.le) k.2.1 :
            SourceH1 src dst) :=
        sourceH1OriginalSelectedOffB_ambientValue_eq_root_mul_localValue
          src dst base A hcard rootH B hBP zS hOffS
  let hOffT := (K.rootedLocalMultiCosetOffCoset_iff
    A hcard hret r P B hBP k.2.1).mp k.2.2
  have hMissingS :
      ∀ edge, G.source edge = zS →
        signedBase (G.label edge) ∉ B :=
    z.source_noOldBEdges src dst base A hcard root B hBP
  have hMissingT :
      ∀ edge, G.source edge = e k.2.1 →
        signedBase (G.label edge) ∉ B := by
    intro edge hsource
    exact K.rootedAmbientOffCoset_no_old_B_edge
      A hcard hret r B hBP k.2.1 hOffT edge hsource
  have hPaired : G.LocallyPairedLabels :=
    sourceH1OriginalRootAllProper_locallyPaired
      src dst base A hcard rootH
  have hTranslated :
      ∀ y,
        (sourceH1OriginalSelectedOffBTranslatedStage
          src dst base A hcard rootH B hBP zS hOffS).followWord y p =
        (sourceH1OriginalSelectedOffBTranslatedStage
          src dst base A hcard rootH B hBP zS hOffS).followWord y q :=
    sourceH1OriginalSelectedOffBTranslatedStage_G2_wordValue_congr
      src dst base A hcard rootH B hBP zS hOffS p q hpq
  exact (IsolatedCosetGluing.completedStage_wordActionCongr_iff_of_anchor_root_eq
    G (sourceH1Generator src dst) B hAnchor hRoot
    hMissingS hMissingT hPaired hPaired p q).mpr hTranslated

/-- The original PAPER T(Y₁) selected off-B type-(2)
LEGALLY complete action is unconditionally controlled by
the true finite input-dependent source G₂. Every two signed
words with the same group value act identically at ALL
old-tagged and fresh B-coset vertices, including loops. -/
theorem literalPaperSelectedOffB_G2_wordValue_congr
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP)
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
    src dst base A hcard root B hBP z p q).mpr
    (literalPaperSelectedOffBSource_G2_wordValue_congr
      src dst base A hcard root B hBP z p q hpq)

/-- For EVERY point u of an actual literal selected paper
type-(2) stage, construct the genuine labelled Cayley(G₂)
graph morphism covering its reachable signed-action component.
There is NO extra source word congruence premise. -/
noncomputable def literalPaperSelectedOffB_G2CayleyHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP)
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
  literalPaperSelectedOffB_G2CayleyHom_of_source
    src dst base A hcard root B hBP z
    (fun p q hpq =>
      literalPaperSelectedOffBSource_G2_wordValue_congr
        src dst base A hcard root B hBP z p q hpq) u

end ABO
end PSTSEPPA
