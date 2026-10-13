import PSTSEPPA.ABO.AllLocalRankTwoCayleySkeletons
import PSTSEPPA.ABO.RankTwoThreeFamilyStableCover
import PSTSEPPA.ABO.DependentDisjointStages

/-!
# The TRUE type-(2) completed action occurs in the actual finite G₂ catalogue

It is not enough to match a source type-(2) augmentation's
dependent (B,z) INDEX to the catalogue. Its complete signed
action must be genuinely the action of a tagged summand of
the actual all-local stage used in the finite G₂ construction.

For EVERY literal two-letter local Cayley skeleton index j
in the actual all-local catalogue and EVERY type-(2) stage
(B,z) at j, this file embeds the ENTIRE type-(2) dependent
completed action into the TRUE finite G₂ stage. We retain:

* the exact outer index (A,K), not an arbitrary representative;
* the internal three-family TYPE-(2) tag;
* the exact B,z augmentation index and its old/fresh vertex tags;
* BOTH directions of every signed generator and EVERY signed-word
  endpoint, including added fixed-point loops.

The completed action of the selected type-(2) family is
literally the type-(2) summand of the three-family local action,
which is itself the j-summand of the finite global G₂ action.
Nothing is quotient-identified by ambient group coordinate.

This is the ACTION half needed after the separately proved
source/local B,z catalogue-index equivalence. It is not the
full source Definition-5.3 Z₁ completeness or Condition 5.2.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- The precise type-(2) augmentation-index carrier in the
already constructed three-family action for the selected
literal all-local catalogue skeleton j. -/
abbrev localType2CatalogueIndex
    (gen : ι → Γ) (hret : KRetractable gen 2)
    (j : AllLocalRankTwoSkeletonIndex gen) :=
  (allLocalRankTwoSkeleton j).rankTwoType2SingletonIndex
    (allLocalRankTwoAlphabet_card j)
    (isGenerated_trivialCompletionGenerator gen (allLocalRankTwoAlphabet j))
    (retractable_trivialCompletionGenerator_of_kRetractable
      gen 2 hret (allLocalRankTwoAlphabet j)
      (allLocalRankTwoAlphabet_card j).le)

/-- The real dependent type-(2) FAMILY carrier for the exact
local skeleton j, with every B,z and old/fresh tag retained. -/
abbrev localType2CatalogueFamilyVertex
    (gen : ι → Γ) (hret : KRetractable gen 2)
    (j : AllLocalRankTwoSkeletonIndex gen) :=
  Σ k : localType2CatalogueIndex gen hret j,
    (allLocalRankTwoSkeleton j).rankTwoType2SingletonVertex
      (allLocalRankTwoAlphabet_card j)
      (isGenerated_trivialCompletionGenerator gen (allLocalRankTwoAlphabet j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret (allLocalRankTwoAlphabet j)
        (allLocalRankTwoAlphabet_card j).le)
      k

/-- The precise vertex carrier of the complete ALL-LOCAL
three-family stage used in the concrete finite G₂. -/
abbrev actualAllLocalG2StageVertex
    (gen : ι → Γ) (hret : KRetractable gen 2) :=
  rankTwoIndexedAmbientVertex (gen := gen)
    (fun j : AllLocalRankTwoSkeletonIndex gen =>
      allLocalRankTwoAlphabet j)
    (fun j => allLocalRankTwoAlphabet_card j)
    (fun j => allLocalRankTwoSkeleton j)
    hret

/-- Embed the entire local type-(2) family into the REAL G₂
stage at the LITERAL outer catalogue index j, followed by
the internal type-(2) summand tag (right,right). -/
noncomputable def type2StageVertexIntoAllLocalG2
    (gen : ι → Γ) (hret : KRetractable gen 2)
    (j : AllLocalRankTwoSkeletonIndex gen)
    (x : localType2CatalogueFamilyVertex gen hret j) :
    actualAllLocalG2StageVertex gen hret :=
  ⟨j, Sum.inr (Sum.inr x)⟩

/-- This true tagged inclusion is injective: distinct (B,z)
stage tags or distinct old/fresh points are never collapsed,
regardless of equality of their ambient Γ coordinates. -/
theorem type2StageVertexIntoAllLocalG2_injective
    (gen : ι → Γ) (hret : KRetractable gen 2)
    (j : AllLocalRankTwoSkeletonIndex gen) :
    Function.Injective (type2StageVertexIntoAllLocalG2 gen hret j) := by
  intro x y h
  have htag : Sum.inr (Sum.inr x) = Sum.inr (Sum.inr y) :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact Sum.inr.inj (Sum.inr.inj htag)

/-- Every signed word in the EXACT local type-(2)
augmented family has the same endpoint after the genuine
three-family and global G₂ catalogue inclusions.

This follows the actual COMPLETE permutations, including
inverse letters and loop-only completion, not a mere
claim about ambient group word values. -/
theorem type2StageVertexIntoAllLocalG2_followWord
    (gen : ι → Γ) (hret : KRetractable gen 2)
    (j : AllLocalRankTwoSkeletonIndex gen)
    (x : localType2CatalogueFamilyVertex gen hret j)
    (w : LabelWord ι) :
    (allLocalRankTwoStage (gen := gen) hret).followWord
        (type2StageVertexIntoAllLocalG2 gen hret j x) w =
      type2StageVertexIntoAllLocalG2 gen hret j
        (((allLocalRankTwoSkeleton j).rankTwoType2SingletonFamilyStage
          (allLocalRankTwoAlphabet_card j)
          (isGenerated_trivialCompletionGenerator
            gen (allLocalRankTwoAlphabet j))
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen 2 hret (allLocalRankTwoAlphabet j)
            (allLocalRankTwoAlphabet_card j).le)).followWord x w) := by
  let K0 := allLocalRankTwoSkeleton j
  let hcard := allLocalRankTwoAlphabet_card j
  let hgen := isGenerated_trivialCompletionGenerator
    gen (allLocalRankTwoAlphabet j)
  let hretL := retractable_trivialCompletionGenerator_of_kRetractable
    gen 2 hret (allLocalRankTwoAlphabet j) hcard.le
  let T0 := K0.allProperCompletedStage
    (K0.admissible_of_card_le_two hcard.le)
    hgen hretL hcard.ge
  let T1 := ClusterSpec.augmentedType1FamilyStage
    (trivialCompletionGenerator gen (allLocalRankTwoAlphabet j))
    (allLocalRankTwoAlphabet j)
  let T2 := K0.rankTwoType2SingletonFamilyStage
    hcard hgen hretL
  change
    (dependentDisjointStage
      (fun k : AllLocalRankTwoSkeletonIndex gen =>
        (allLocalRankTwoSkeleton k).rankTwoAmbientLocalStage
          (allLocalRankTwoAlphabet_card k) hret)).followWord
      (⟨j, Sum.inr (Sum.inr x)⟩ :
        actualAllLocalG2StageVertex gen hret) w =
    (⟨j, Sum.inr (Sum.inr (T2.followWord x w))⟩ :
      actualAllLocalG2StageVertex gen hret)
  rw [dependentDisjointStage_followWord]
  change
    (⟨j, (T0.disjointUnion (T1.disjointUnion T2)).followWord
      (Sum.inr (Sum.inr x)) w⟩ :
      actualAllLocalG2StageVertex gen hret) =
    (⟨j, Sum.inr (Sum.inr (T2.followWord x w))⟩ :
      actualAllLocalG2StageVertex gen hret)
  rw [CompleteEGraph.disjointUnion_followWord_inr,
      CompleteEGraph.disjointUnion_followWord_inr]
  rfl

end ABO
end PSTSEPPA
