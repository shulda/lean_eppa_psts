import PSTSEPPA.ABO.SourceG2Type1FamilyActionCover
import PSTSEPPA.ABO.SourceG2Type2FamilyActionCover

/-!
# Exact signed-word kernels of both augmented stage families of the real source G₂

Every local augmented cluster (type 1) and every local augmented full
coset extension (type 2) occurs as a genuinely tagged subaction of
the ACTUAL finite input-dependent second-rank group G₂.

The concrete Cayley-cover endpoint formula and the injectivity of
the original stage tag imply that ANY word acting trivially in this G₂
acts trivially on EVERY vertex of both completed families.

This statement concerns genuine completed SIGNED word actions,
including the inverses, new coset vertices and legally added loops;
it is not a claim about ambient H₁ group coordinates. The separate
source/local Z₁ identification and higher-rank induction are still
needed for the final PSTS EPPA theorem.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The exact double-tagged embedding of type-(1) augmented
cluster stages into the real source G₂ stage is injective
on all old and newly attached vertices. -/
theorem sourceG2Type1CatalogueBasepoint_injective
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2) :
    Function.Injective
      (sourceG2Type1CatalogueBasepoint src dst A hcard) := by
  intro x y h
  have htag : Sum.inr (Sum.inl x) = Sum.inr (Sum.inl y) :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact Sum.inl.inj (Sum.inr.inj htag)

/-- If a signed word evaluates to identity in the ACTUAL finite
source G₂, it fixes every vertex of each local legally completed
type-(1) augmented cluster. -/
theorem sourceG2Type1Catalogue_wordKernel
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (x : Σ j : ClusterSpec.augmentedType1Index
      (trivialCompletionGenerator (sourceH1Generator src dst) A) A,
        ClusterSpec.augmentedType1Vertex j)
    (w : LabelWord ι)
    (hw : PSTS.SignedWord.evalGroup
      (sourceAllLocalG2Generator src dst) w = 1) :
    (ClusterSpec.augmentedType1FamilyStage
      (trivialCompletionGenerator (sourceH1Generator src dst) A) A
    ).followWord x w = x := by
  apply sourceG2Type1CatalogueBasepoint_injective src dst A hcard
  have h := sourceG2Type1CatalogueCover_word src dst A hcard x w
  exact h.symm.trans
    ((congrArg
      (sourceG2LocalCayleyHom src dst
        (sourceG2Type1CatalogueBasepoint src dst A hcard x)).onVertex hw).trans
      (sourceG2Type1CatalogueCover_one src dst A hcard x))

/-- The exact doubly tagged type-(2) catalogue embedding is
injective for a prescribed real local Cayley skeleton. -/
theorem sourceG2Type2CatalogueBasepoint_injective
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst)) :
    Function.Injective (sourceG2Type2CatalogueBasepoint src dst j) :=
  type2StageVertexIntoAllLocalG2_injective
    (sourceH1Generator src dst)
    (sourceH1_twoRetractable src dst) j

/-- The same actual G₂ identity-word kernel acts trivially on
EVERY complete local type-(2) B-coset augmentation action,
including B=∅, full signed edges and legal fixed loops. -/
theorem sourceG2Type2Catalogue_wordKernel
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (x : localType2CatalogueFamilyVertex
      (sourceH1Generator src dst)
      (sourceH1_twoRetractable src dst) j)
    (w : LabelWord ι)
    (hw : PSTS.SignedWord.evalGroup
      (sourceAllLocalG2Generator src dst) w = 1) :
    ((allLocalRankTwoSkeleton j).rankTwoType2SingletonFamilyStage
      (allLocalRankTwoAlphabet_card j)
      (isGenerated_trivialCompletionGenerator
        (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst)
        (allLocalRankTwoAlphabet j)
        (allLocalRankTwoAlphabet_card j).le)).followWord x w = x := by
  apply sourceG2Type2CatalogueBasepoint_injective src dst j
  have h := sourceG2Type2CatalogueCover_word src dst j x w
  exact h.symm.trans
    ((congrArg
      (sourceG2LocalCayleyHom src dst
        (sourceG2Type2CatalogueBasepoint src dst j x)).onVertex hw).trans
      (sourceG2Type2CatalogueCover_one src dst j x))


/-- More generally, equal values of ANY TWO signed words in the real
source-dependent G₂ induce exactly equal action endpoints on every
completed type-(1) augmented cluster. The equality holds at the
original tagged stage point, not merely after projection to H₁. -/
theorem sourceG2Type1Catalogue_wordValue_congr
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (x : Σ j : ClusterSpec.augmentedType1Index
      (trivialCompletionGenerator (sourceH1Generator src dst) A) A,
        ClusterSpec.augmentedType1Vertex j)
    (w₁ w₂ : LabelWord ι)
    (hw : PSTS.SignedWord.evalGroup
      (sourceAllLocalG2Generator src dst) w₁ =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w₂) :
    (ClusterSpec.augmentedType1FamilyStage
      (trivialCompletionGenerator (sourceH1Generator src dst) A) A
    ).followWord x w₁ =
    (ClusterSpec.augmentedType1FamilyStage
      (trivialCompletionGenerator (sourceH1Generator src dst) A) A
    ).followWord x w₂ := by
  apply sourceG2Type1CatalogueBasepoint_injective src dst A hcard
  have h₁ := sourceG2Type1CatalogueCover_word src dst A hcard x w₁
  have h₂ := sourceG2Type1CatalogueCover_word src dst A hcard x w₂
  exact h₁.symm.trans
    ((congrArg
      (sourceG2LocalCayleyHom src dst
        (sourceG2Type1CatalogueBasepoint src dst A hcard x)).onVertex hw).trans h₂)

/-- Equality of values in the actual finite input-dependent G₂
likewise forces equality of the genuine SIGNED completed-action
endpoints on every local type-(2) augmented full B-coset stage. -/
theorem sourceG2Type2Catalogue_wordValue_congr
    (src dst : ι → V)
    (j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst))
    (x : localType2CatalogueFamilyVertex
      (sourceH1Generator src dst)
      (sourceH1_twoRetractable src dst) j)
    (w₁ w₂ : LabelWord ι)
    (hw : PSTS.SignedWord.evalGroup
      (sourceAllLocalG2Generator src dst) w₁ =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w₂) :
    ((allLocalRankTwoSkeleton j).rankTwoType2SingletonFamilyStage
      (allLocalRankTwoAlphabet_card j)
      (isGenerated_trivialCompletionGenerator
        (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst)
        (allLocalRankTwoAlphabet j)
        (allLocalRankTwoAlphabet_card j).le)).followWord x w₁ =
    ((allLocalRankTwoSkeleton j).rankTwoType2SingletonFamilyStage
      (allLocalRankTwoAlphabet_card j)
      (isGenerated_trivialCompletionGenerator
        (sourceH1Generator src dst) (allLocalRankTwoAlphabet j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst)
        (allLocalRankTwoAlphabet j)
        (allLocalRankTwoAlphabet_card j).le)).followWord x w₂ := by
  apply sourceG2Type2CatalogueBasepoint_injective src dst j
  have h₁ := sourceG2Type2CatalogueCover_word src dst j x w₁
  have h₂ := sourceG2Type2CatalogueCover_word src dst j x w₂
  exact h₁.symm.trans
    ((congrArg
      (sourceG2LocalCayleyHom src dst
        (sourceG2Type2CatalogueBasepoint src dst j x)).onVertex hw).trans h₂)

end ABO
end PSTSEPPA
