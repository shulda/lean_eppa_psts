import PSTSEPPA.ABO.Type2G2CatalogueActionOccurrence
import PSTSEPPA.ABO.SourceG2LocalCayleyCovers

/-!
# The actual finite SOURCE G₂ Cayley graph covers every local type-(2) action

The input-dependent finite source G₂ is not an abstract existence
claim: it is the synchronised generated subgroup of the ACTUAL all-local
three-family signed action built from the source-oriented input's H₁.

The entire completed local type-(2) family at ANY genuinely indexed
local (A,K) skeleton is an explicit tagged signed-action summand of
that all-local action. Therefore the actual finite source G₂
Cayley-cover map, rooted at the corresponding tagged stage point,
sends every chronological signed word w to PRECISELY the point
reached by w in that true type-(2) family.

This is equality of ACTUAL action endpoints, not merely equality
of word values in H₁, and it handles all signed inverses, fixed loops
and disconnected source components. It needs no injectivity of
the ambient H₁-coordinate map.

The remaining missing global source obligation is to identify the
COMPLETE original H₁ augmented stage with its exact local type-(2)
catalogue fibre, for each genuine original cover index. The source/
local index correspondence and completed action isomorphism are
separately formalized; this file prepares their final composition.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The REAL tagged point in the source-dependent G₂ stage,
selected by a literal local (A,K) skeleton index, genuine
type-(2) augmented stage index (B,z) and corresponding old/fresh
completed-stage vertex. -/
noncomputable def sourceG2Type2CatalogueBasepoint
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (x : localType2CatalogueFamilyVertex
      (sourceH1Generator src dst)
      (sourceH1_twoRetractable src dst) j) :
    sourceG2LocalStageVertex src dst :=
  type2StageVertexIntoAllLocalG2
    (sourceH1Generator src dst)
    (sourceH1_twoRetractable src dst) j x

/-- The ACTUAL source G₂ identity element maps to the selected
type-(2) signed-completed stage vertex, not merely to its
ambient H₁ group coordinate or an arbitrarily selected copy. -/
@[simp] theorem sourceG2Type2CatalogueCover_one
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (x : localType2CatalogueFamilyVertex
      (sourceH1Generator src dst)
      (sourceH1_twoRetractable src dst) j) :
    (sourceG2LocalCayleyHom src dst
      (sourceG2Type2CatalogueBasepoint src dst j x)).onVertex 1 =
    sourceG2Type2CatalogueBasepoint src dst j x :=
  sourceG2LocalCayleyHom_one src dst
    (sourceG2Type2CatalogueBasepoint src dst j x)

/-- Every signed word in the concrete finite source G₂,
interpreted via its literal Cayley graph cover, reaches
precisely the endpoint of the SAME signed word in the exact
completed local type-(2) augmented family stage.

This includes nontrivial negative signed letters and true
fresh B-coset action edges; no ambient H₁ coordinate collapse. -/
theorem sourceG2Type2CatalogueCover_word
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (x : localType2CatalogueFamilyVertex
      (sourceH1Generator src dst)
      (sourceH1_twoRetractable src dst) j)
    (w : LabelWord ι) :
    (sourceG2LocalCayleyHom src dst
      (sourceG2Type2CatalogueBasepoint src dst j x)).onVertex
      (PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w) =
    sourceG2Type2CatalogueBasepoint src dst j
      (((allLocalRankTwoSkeleton j).rankTwoType2SingletonFamilyStage
        (allLocalRankTwoAlphabet_card j)
        (isGenerated_trivialCompletionGenerator
          (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2
          (sourceH1_twoRetractable src dst)
          (allLocalRankTwoAlphabet j)
          (allLocalRankTwoAlphabet_card j).le)).followWord x w) := by
  calc
    (sourceG2LocalCayleyHom src dst
      (sourceG2Type2CatalogueBasepoint src dst j x)).onVertex
        (PSTS.SignedWord.evalGroup
          (sourceAllLocalG2Generator src dst) w) =
      (sourceG2LocalCompleteStage src dst).followWord
        (sourceG2Type2CatalogueBasepoint src dst j x) w :=
        sourceG2LocalCayleyHom_word src dst
          (sourceG2Type2CatalogueBasepoint src dst j x) w
    _ = sourceG2Type2CatalogueBasepoint src dst j
          (((allLocalRankTwoSkeleton j).rankTwoType2SingletonFamilyStage
            (allLocalRankTwoAlphabet_card j)
            (isGenerated_trivialCompletionGenerator
              (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
            (retractable_trivialCompletionGenerator_of_kRetractable
              (sourceH1Generator src dst) 2
              (sourceH1_twoRetractable src dst)
              (allLocalRankTwoAlphabet j)
              (allLocalRankTwoAlphabet_card j).le)).followWord x w) :=
        type2StageVertexIntoAllLocalG2_followWord
          (sourceH1Generator src dst)
          (sourceH1_twoRetractable src dst) j x w

end ABO
end PSTSEPPA
