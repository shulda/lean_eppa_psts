import PSTSEPPA.ABO.SourceH1OriginalSelectedOffBLocalG2IndexValue
import PSTSEPPA.ABO.SourceH1Type2ActualG2WordAction

/-!
# Original-source H₁ selected off-B stage: exact finite G₂ word congruence

The existing source G₂ theorem acts on every genuinely indexed
ORIGINAL incomplete H₁ root A-component of the input graph and its
LOCAL rank-two (B,w) completed type-(2) augmentation. A selected
original source B-augmentation root is instead supplied as a real
component-tagged quotient vertex z OFF the whole B constituent.

The separately checked source local-G₂ index normalization gives
the precise w, without choosing a coset representative or silently
identifying different intrinsic path-component tags. We here use
that exact index to show that the ROOT-TRANSLATED genuine original
source-H₁ completed type-(2) stage itself obeys the ACTUAL finite
input-dependent G₂ signed-word action congruence.

This does not yet assert that the independently named literal
paper T(Y₁) stage is the translated source stage; their complete
signed EGraph agreement is a separate HEq/geometric bridge.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The genuine original source-H₁ type-(2) stage with local index
uniquely determined by actual off-B membership, presented in the
root-translated original H₁ coordinates, including its fresh
component-tagged B-coset and all legally added stationary loops. -/
noncomputable abbrev sourceH1OriginalSelectedOffBTranslatedStage
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : Quotient (sourceH1OriginalRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A)))
    (hOff : ¬ ∃ p : (sourceH1OriginalRootComponent
      src dst base A root).AttachedCosetVertex B,
      sourceH1SelectedRootBInclude
        src dst base A hcard root (allProperCosetFamily A)
        B hBP p = z) :=
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceH1_twoRetractable src dst
  let k := sourceH1OriginalSelectedOffBLocalG2Index
    src dst base A hcard root B hBP z hOff
  K.rootedTranslatedSourceOffCosetCompletedStage
    A hcard hret r B hBP k.2.1
    ((K.rootedLocalMultiCosetOffCoset_iff A hcard hret r
      (allProperCosetFamily A) B hBP k.2.1).mp k.2.2)

/-- Equality of actual finite input-derived G₂ signed-word values
forces equality of COMPLETE signed actions at EVERY vertex of
the true original-source H₁ selected OFF-B type-(2) translated stage.
This holds without global retractability and for B=∅ as well. -/
theorem sourceH1OriginalSelectedOffBTranslatedStage_G2_wordValue_congr
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : Quotient (sourceH1OriginalRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A)))
    (hOff : ¬ ∃ p : (sourceH1OriginalRootComponent
      src dst base A root).AttachedCosetVertex B,
      sourceH1SelectedRootBInclude
        src dst base A hcard root (allProperCosetFamily A)
        B hBP p = z)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ y,
      (sourceH1OriginalSelectedOffBTranslatedStage
        src dst base A hcard root B hBP z hOff).followWord y p =
      (sourceH1OriginalSelectedOffBTranslatedStage
        src dst base A hcard root B hBP z hOff).followWord y q := by
  let j : SourceOriginalH1CoverIndex src dst :=
    ⟨base, ⟨⟨A,hcard⟩,root⟩⟩
  let k := sourceH1OriginalSelectedOffBLocalG2Index
    src dst base A hcard root B hBP z hOff
  exact sourceG2OriginalH1Type2Translated_wordValue_congr
    src dst j k p q hpq

end ABO
end PSTSEPPA
