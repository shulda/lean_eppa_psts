import PSTSEPPA.ABO.SourceG2AugmentedStageWordKernel
import PSTSEPPA.ABO.DependentDisjointWordCongruence

/-!
# Exact individual type-(2) completed-stage word actions controlled by genuine source G₂

The finite original-input-dependent G₂ acts on the entire complete
local type-(2) family with an explicit (B,z)-tag. This file
specializes the already verified G₂ whole-family word-action
congruence to EVERY literal INDIVIDUAL augmented coset stage.

No representational collapse of tagged (B,z) index or old/fresh
quotient vertex takes place, even when ambient Γ-coordinates
coincide. The proof uses the exact dependent-sigma stage
action formula for BOTH signs, fixed loops and every signed word.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every local type-(2) (B,z) complete augmented stage action
inherits arbitrary signed-word group-value equality in the REAL
finite G₂ constructed from the original H₁ source input. -/
theorem sourceG2Type2Singleton_wordValue_congr
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (k : localType2CatalogueIndex
      (sourceH1Generator src dst)
      (sourceH1_twoRetractable src dst) j)
    (x : (allLocalRankTwoSkeleton j).rankTwoType2SingletonVertex
      (allLocalRankTwoAlphabet_card j)
      (isGenerated_trivialCompletionGenerator
        (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst)
        (allLocalRankTwoAlphabet j)
        (allLocalRankTwoAlphabet_card j).le)
      k)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ((allLocalRankTwoSkeleton j).rankTwoType2SingletonStage
      (allLocalRankTwoAlphabet_card j)
      (isGenerated_trivialCompletionGenerator
        (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst)
        (allLocalRankTwoAlphabet j)
        (allLocalRankTwoAlphabet_card j).le)
      k).followWord x p =
    ((allLocalRankTwoSkeleton j).rankTwoType2SingletonStage
      (allLocalRankTwoAlphabet_card j)
      (isGenerated_trivialCompletionGenerator
        (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst)
        (allLocalRankTwoAlphabet j)
        (allLocalRankTwoAlphabet_card j).le)
      k).followWord x q := by
  let K := allLocalRankTwoSkeleton j
  let hcard := allLocalRankTwoAlphabet_card j
  let hgen := isGenerated_trivialCompletionGenerator
    (sourceH1Generator src dst) (allLocalRankTwoAlphabet j)
  let hret := retractable_trivialCompletionGenerator_of_kRetractable
    (sourceH1Generator src dst) 2
    (sourceH1_twoRetractable src dst)
    (allLocalRankTwoAlphabet j) hcard.le
  let T := fun k : K.rankTwoType2SingletonIndex hcard hgen hret =>
    K.rankTwoType2SingletonStage hcard hgen hret k
  have hFamily :
      (K.rankTwoType2SingletonFamilyStage hcard hgen hret).followWord
        (⟨k, x⟩ : Σ t : K.rankTwoType2SingletonIndex hcard hgen hret,
          K.rankTwoType2SingletonVertex hcard hgen hret t) p =
      (K.rankTwoType2SingletonFamilyStage hcard hgen hret).followWord
        (⟨k, x⟩ : Σ t : K.rankTwoType2SingletonIndex hcard hgen hret,
          K.rankTwoType2SingletonVertex hcard hgen hret t) q :=
    sourceG2Type2Catalogue_wordValue_congr
      src dst j ⟨k, x⟩ p q hpq
  exact (dependentDisjointStage_wordEquality_at_tag_iff T k x p q).mp hFamily

end ABO
end PSTSEPPA
