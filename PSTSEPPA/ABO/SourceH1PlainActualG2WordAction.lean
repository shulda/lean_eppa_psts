import PSTSEPPA.ABO.SourceG2PlainStageCayleyCover
import PSTSEPPA.ABO.RootedLocalPlainStageCatalogueAgreement
import PSTSEPPA.ABO.RootedSourcePlainWordActionCongruence
import PSTSEPPA.ABO.SourceOriginalH1LocalCoverIndex

/-!
# Genuine ORIGINAL unaugmented rank-two H₁ source coset stage inherits finite G₂ word actions

The corrected first source family Z₁ includes ordinary completed
full proper-alphabet coset extensions, not just its type-(1)/(2)
augmentations. For every original input H₁-Cayley preimage
component j, the true rooted Γ[A] normalization is one of the
actual locally indexed incomplete skeletons used by the finite
input-dependent G₂ catalogue.

The independent complete P_A stage equality identifies the
locally rooted source model with that catalogue's P_A stage.
The ACTUAL G₂ Cayley word-cover formula for the latter yields
word-action congruence for the former. Finally the already
certified vertex- and oriented-signed-edge-bijective legal
completion isomorphism transfers the whole equality to the
TRUE ORIGINAL rooted H₁ plain stage.

All original component tags, both signs and legal fixed loops
remain distinct. This is not a coordinate-only Cayley pullback.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- At every original H₁ source input basepoint, two-letter
alphabet and actual preimage-component root, equality of two
chronological signed word-values in the CONCRETE finite source
G₂ implies exactly equal endpoints at EVERY vertex of the
ORIGINAL ROOTED H₁ LEGALLY COMPLETED P_A plain coset extension.
No global retractability of H₁ is needed. -/
theorem sourceG2OriginalH1Plain_wordValue_congr
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ y,
      (((sourceCoverIndexSkeleton src dst j).restrictAlphabet
        j.2.1.1).rootedAmbientAllProperCompletedStage
        j.2.1.1 j.2.1.2 (sourceH1_twoRetractable src dst)
        (sourceCoverIndexRoot src dst j)).followWord y p =
      (((sourceCoverIndexSkeleton src dst j).restrictAlphabet
        j.2.1.1).rootedAmbientAllProperCompletedStage
        j.2.1.1 j.2.1.2 (sourceH1_twoRetractable src dst)
        (sourceCoverIndexRoot src dst j)).followWord y q := by
  let A := j.2.1.1
  let hcard := j.2.1.2
  let K := (sourceCoverIndexSkeleton src dst j).restrictAlphabet A
  let hret := sourceH1_twoRetractable src dst
  let root := sourceCoverIndexRoot src dst j
  have hLocal :
      ∀ x, (K.rootedLocalAllProperCompletedStage A hcard hret root).followWord x p =
        (K.rootedLocalAllProperCompletedStage A hcard hret root).followWord x q := by
    intro x
    change
      ((allLocalRankTwoSkeleton
        (sourceCoverIntoAllLocalIndex src dst j)).allProperCompletedStage
        ((allLocalRankTwoSkeleton
          (sourceCoverIntoAllLocalIndex src dst j)).admissible_of_card_le_two
          (allLocalRankTwoAlphabet_card (sourceCoverIntoAllLocalIndex src dst j)).le)
        (isGenerated_trivialCompletionGenerator
          (sourceH1Generator src dst)
          (allLocalRankTwoAlphabet (sourceCoverIntoAllLocalIndex src dst j)))
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2
          (sourceH1_twoRetractable src dst)
          (allLocalRankTwoAlphabet (sourceCoverIntoAllLocalIndex src dst j))
          (allLocalRankTwoAlphabet_card
            (sourceCoverIntoAllLocalIndex src dst j)).le)
        (allLocalRankTwoAlphabet_card
          (sourceCoverIntoAllLocalIndex src dst j)).ge).followWord x p =
      ((allLocalRankTwoSkeleton
        (sourceCoverIntoAllLocalIndex src dst j)).allProperCompletedStage
        ((allLocalRankTwoSkeleton
          (sourceCoverIntoAllLocalIndex src dst j)).admissible_of_card_le_two
          (allLocalRankTwoAlphabet_card (sourceCoverIntoAllLocalIndex src dst j)).le)
        (isGenerated_trivialCompletionGenerator
          (sourceH1Generator src dst)
          (allLocalRankTwoAlphabet (sourceCoverIntoAllLocalIndex src dst j)))
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2
          (sourceH1_twoRetractable src dst)
          (allLocalRankTwoAlphabet (sourceCoverIntoAllLocalIndex src dst j))
          (allLocalRankTwoAlphabet_card
            (sourceCoverIntoAllLocalIndex src dst j)).le)
        (allLocalRankTwoAlphabet_card
          (sourceCoverIntoAllLocalIndex src dst j)).ge).followWord x q
    exact sourceG2PlainCatalogue_wordValue_congr
      src dst (sourceCoverIntoAllLocalIndex src dst j) x p q hpq
  exact (K.rootedAllProperCompletedStage_wordActionCongr_iff
    A hcard hret root p q).mp hLocal

end ABO
end PSTSEPPA
