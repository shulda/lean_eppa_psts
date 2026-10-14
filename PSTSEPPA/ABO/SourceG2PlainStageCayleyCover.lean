import PSTSEPPA.ABO.SourceG2LocalCayleyCovers
import PSTSEPPA.ABO.RankTwoThreeFamilyStableCover
import PSTSEPPA.ABO.AllLocalRankTwoCayleySkeletons
import PSTSEPPA.ABO.DependentDisjointStages

/-!
# Real finite source G₂ Cayley cover of the plain rank-two completed coset extension

The corrected Z₁ source stages also include the un-augmented full
proper-alphabet coset extension. It is not sufficient to cover
only newly B-augmented stages. The actual all-local three-family
action used to construct the finite source G₂ already contains
the LEGAL completed P_A plain coset extension as its first,
literal left-sum summand at every (A,K) catalogue index.

This module constructs that literal occurrence and the concrete
source-G₂ Cayley-cover word formula on ALL original coset-quotient
vertices, including both signed directions and completed loops.
No identification is made via possibly duplicated ambient H₁
group coordinates. A later source/local rooted isomorphism transfers
these local facts to the actual original H₁-cover components.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Exact old tagged multi-coset quotient carrier of the selected
genuine local rank-two skeleton's P_A completed stage. -/
abbrev sourceG2PlainLocalVertex
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst)) :=
  (allLocalRankTwoSkeleton j).MultiCosetVertex
    (allProperCosetFamily (allLocalRankTwoAlphabet j))
    ((allLocalRankTwoSkeleton j).admissible_of_card_le_two
      (allLocalRankTwoAlphabet_card j).le)
    (isGenerated_trivialCompletionGenerator
      (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
    (retractable_trivialCompletionGenerator_of_kRetractable
      (sourceH1Generator src dst) 2
      (sourceH1_twoRetractable src dst)
      (allLocalRankTwoAlphabet j)
      (allLocalRankTwoAlphabet_card j).le)

/-- The true complete P_A stage included as the first summand
of the input-dependent finite G₂'s original global signed action. -/
noncomputable def sourceG2PlainCatalogueBasepoint
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (x : sourceG2PlainLocalVertex src dst j) :
    sourceG2LocalStageVertex src dst :=
  ⟨j, Sum.inl x⟩

/-- Every original tagged plain stage point remains distinct
under the real outer (A,K) and inner plain-action inclusion. -/
theorem sourceG2PlainCatalogueBasepoint_injective
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst)) :
    Function.Injective (sourceG2PlainCatalogueBasepoint src dst j) := by
  intro x y h
  have htag : Sum.inl x = Sum.inl y :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact Sum.inl.inj htag

/-- Identity of concrete finite G₂ maps to the chosen literal
root of the actual P_A completed stage. -/
@[simp] theorem sourceG2PlainCatalogueCover_one
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (x : sourceG2PlainLocalVertex src dst j) :
    (sourceG2LocalCayleyHom src dst
      (sourceG2PlainCatalogueBasepoint src dst j x)).onVertex 1 =
      sourceG2PlainCatalogueBasepoint src dst j x :=
  sourceG2LocalCayleyHom_one src dst
    (sourceG2PlainCatalogueBasepoint src dst j x)

/-- Actual source G₂ signed chronological group words reach
precisely the same tagged endpoint as following the word inside
the local LEGALLY COMPLETED P_A plain multi-coset extension. -/
theorem sourceG2PlainCatalogueCover_word
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (x : sourceG2PlainLocalVertex src dst j)
    (w : LabelWord ι) :
    (sourceG2LocalCayleyHom src dst
      (sourceG2PlainCatalogueBasepoint src dst j x)).onVertex
      (PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w) =
    sourceG2PlainCatalogueBasepoint src dst j
      (((allLocalRankTwoSkeleton j).allProperCompletedStage
        ((allLocalRankTwoSkeleton j).admissible_of_card_le_two
          (allLocalRankTwoAlphabet_card j).le)
        (isGenerated_trivialCompletionGenerator
          (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
        (retractable_trivialCompletionGenerator_of_kRetractable
          (sourceH1Generator src dst) 2
          (sourceH1_twoRetractable src dst)
          (allLocalRankTwoAlphabet j)
          (allLocalRankTwoAlphabet_card j).le)
        (allLocalRankTwoAlphabet_card j).ge).followWord x w) := by
  let K := allLocalRankTwoSkeleton j
  let hcard := allLocalRankTwoAlphabet_card j
  let hgen := isGenerated_trivialCompletionGenerator
    (sourceH1Generator src dst) (allLocalRankTwoAlphabet j)
  let hret := retractable_trivialCompletionGenerator_of_kRetractable
    (sourceH1Generator src dst) 2
    (sourceH1_twoRetractable src dst)
    (allLocalRankTwoAlphabet j) hcard.le
  let T0 := K.allProperCompletedStage
    (K.admissible_of_card_le_two hcard.le) hgen hret hcard.ge
  let T1 := ClusterSpec.augmentedType1FamilyStage
    (trivialCompletionGenerator (sourceH1Generator src dst)
      (allLocalRankTwoAlphabet j))
    (allLocalRankTwoAlphabet j)
  let T2 := K.rankTwoType2SingletonFamilyStage hcard hgen hret
  calc
    (sourceG2LocalCayleyHom src dst
      (sourceG2PlainCatalogueBasepoint src dst j x)).onVertex
      (PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w) =
        (sourceG2LocalCompleteStage src dst).followWord
          (sourceG2PlainCatalogueBasepoint src dst j x) w :=
      sourceG2LocalCayleyHom_word src dst
        (sourceG2PlainCatalogueBasepoint src dst j x) w
    _ = sourceG2PlainCatalogueBasepoint src dst j
          (T0.followWord x w) := by
      change
        (dependentDisjointStage
          (fun k : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst) =>
            (allLocalRankTwoSkeleton k).rankTwoAmbientLocalStage
              (allLocalRankTwoAlphabet_card k)
              (sourceH1_twoRetractable src dst))).followWord
            (⟨j, Sum.inl x⟩ : sourceG2LocalStageVertex src dst) w =
        (⟨j, Sum.inl (T0.followWord x w)⟩ :
          sourceG2LocalStageVertex src dst)
      rw [dependentDisjointStage_followWord]
      change
        (⟨j, (T0.disjointUnion (T1.disjointUnion T2)).followWord
            (Sum.inl x) w⟩ : sourceG2LocalStageVertex src dst) =
          (⟨j, Sum.inl (T0.followWord x w)⟩ :
            sourceG2LocalStageVertex src dst)
      rw [CompleteEGraph.disjointUnion_followWord_inl]

/-- Equality of TWO arbitrary signed word-values in the genuine
finite source G₂ implies equality of their word endpoints on
EVERY vertex of this literal plain (unaugmented) completed stage. -/
theorem sourceG2PlainCatalogue_wordValue_congr
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (x : sourceG2PlainLocalVertex src dst j)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ((allLocalRankTwoSkeleton j).allProperCompletedStage
      ((allLocalRankTwoSkeleton j).admissible_of_card_le_two
        (allLocalRankTwoAlphabet_card j).le)
      (isGenerated_trivialCompletionGenerator
        (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst)
        (allLocalRankTwoAlphabet j)
        (allLocalRankTwoAlphabet_card j).le)
      (allLocalRankTwoAlphabet_card j).ge).followWord x p =
    ((allLocalRankTwoSkeleton j).allProperCompletedStage
      ((allLocalRankTwoSkeleton j).admissible_of_card_le_two
        (allLocalRankTwoAlphabet_card j).le)
      (isGenerated_trivialCompletionGenerator
        (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst)
        (allLocalRankTwoAlphabet j)
        (allLocalRankTwoAlphabet_card j).le)
      (allLocalRankTwoAlphabet_card j).ge).followWord x q := by
  apply sourceG2PlainCatalogueBasepoint_injective src dst j
  have hp := sourceG2PlainCatalogueCover_word src dst j x p
  have hq := sourceG2PlainCatalogueCover_word src dst j x q
  exact hp.symm.trans
    ((congrArg
      (sourceG2LocalCayleyHom src dst
        (sourceG2PlainCatalogueBasepoint src dst j x)).onVertex hpq).trans hq)

end ABO
end PSTSEPPA
