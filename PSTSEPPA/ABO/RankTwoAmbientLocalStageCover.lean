import PSTSEPPA.ABO.RankTwoLocalThreeFamilyCover

/-!
# Three genuine rank-two stages synchronized with the ORIGINAL k-retractable group

PR #310 proves that a generated subalphabet subgroup Γ[A], with generators
outside A completed by identity, is globally retractable whenever Γ is
k-retractable and |A| ≤ k. Hence the genuine three-family rank-two
completed stage can be formed over Γ[A] without globally retractable Γ.

Here we go beyond merely constructing a cover OF THE LOCAL SUBGROUP:
the same stage has the rank-one word kernel with respect to the ORIGINAL
ambient Γ. Indeed rank-two retractability implies that every single-label
relation of Γ survives restriction to A and hence is a relation of Γ[A].
We can therefore synchronize the actual complete three-family action
directly with the ORIGINAL generators gen : ι → Γ.

This yields a surjective 1-stable quotient onto Γ, a 2-retractable
domain (using the corrected source R1 lemma), and a finite domain
when Γ is finite. Its concrete actions realize genuine rank-two
stages over Γ[A] and no extra global retractability is assumed.

This is NOT the whole source Z₁/H₁-cover or the full G₂→H₁ tower:
K is an externally supplied local Cayley skeleton and the stage
catalogue remains a conservatively chosen rank-two subfamily.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Any relation on at most k letters of Γ persists under trivial
completion of a subalphabet, despite a lack of global retractability.
This is a relation-level bridge, not a homomorphism Γ → Γ[A]. -/
theorem evalGroup_trivialCompletion_eq_one_of_kRetractable
    (gen : ι → Γ) {k : ℕ} (hret : KRetractable gen k)
    (A C : Finset ι) (hC : C.card ≤ k)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    PSTS.SignedWord.evalGroup (trivialCompletionGenerator gen A) w = 1 := by
  have hsrc :
      PSTS.SignedWord.evalGroup gen w =
        PSTS.SignedWord.evalGroup gen ([] : LabelWord ι) := by
    simpa using hval
  have hRestrict :=
    KRetractable.restrictTo_eq_of_uses
      gen hret C hC A w [] hw (LabelWord.uses_nil C) hsrc
  apply Subtype.ext
  change
    ((PSTS.SignedWord.evalGroup
      (trivialCompletionGenerator gen A) w :
        generatedSubgroup gen A) : Γ) = 1
  rw [coe_evalGroup_trivialCompletionGenerator]
  have hNil : LabelWord.restrictTo A ([] : LabelWord ι) = [] := rfl
  rw [hNil] at hRestrict
  simpa using hRestrict

namespace CayleySubgraphSpec

variable {gen : ι → Γ} {A : Finset ι}
variable (K : CayleySubgraphSpec (trivialCompletionGenerator gen A) A)

/-- The literal disjoint complete action of all three genuine rank-two
stage families over the ACTUAL A-generated subgroup. -/
noncomputable abbrev rankTwoAmbientLocalStage
    (hcard : A.card = 2) (hret : KRetractable gen 2) :=
  K.rankTwoThreeFamilyStage hcard
    (isGenerated_trivialCompletionGenerator gen A)
    (retractable_trivialCompletionGenerator_of_kRetractable
      gen 2 hret A hcard.le)

/-- Every original Γ-identity relation on any singleton alphabet
acts trivially on the genuine combined completed stage over Γ[A].
This includes generators outside A and formal inverses. -/
theorem rankTwoAmbientLocalStage_rankOne_wordValue_eq_one
    (hcard : A.card = 2) (hret : KRetractable gen 2)
    (C : Finset ι) (hC : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (K.rankTwoAmbientLocalStage hcard hret).wordValue w = 1 := by
  have hlocal :
      PSTS.SignedWord.evalGroup
        (trivialCompletionGenerator gen A) w = 1 :=
    evalGroup_trivialCompletion_eq_one_of_kRetractable
      gen hret A C (by omega) w hw hval
  exact K.rankTwoThreeFamilyStage_rankOne_wordValue_eq_one
    hcard (isGenerated_trivialCompletionGenerator gen A)
    (retractable_trivialCompletionGenerator_of_kRetractable
      gen 2 hret A hcard.le)
    C hC w hw hlocal

/-- A real generator-preserving SURJECTIVE quotient to the ORIGINAL
ambient group Γ, not only to the smaller local subgroup Γ[A]. -/
noncomputable def rankTwoAmbientLocalCoverQuotient
    (hcard : A.card = 2) (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    LabelledGroupQuotient
      (SynchronizedProduct.generator gen
        (K.rankTwoAmbientLocalStage hcard hret).transitionSubgroupGenerator)
      gen :=
  SynchronizedProduct.stageCoverQuotient gen
    (K.rankTwoAmbientLocalStage hcard hret) hgen

/-- The concrete global synchronized quotient is rank-ONE stable,
without imposing full retractability of the ambient Γ. -/
theorem rankTwoAmbientLocalCoverQuotient_oneStable
    (hcard : A.card = 2) (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    (K.rankTwoAmbientLocalCoverQuotient hcard hret hgen).KStable 1 := by
  exact SynchronizedProduct.stageCoverQuotient_kStable_of_stageKernel
    gen (K.rankTwoAmbientLocalStage hcard hret) hgen 1
    (by
      intro C hC w hw hval
      exact K.rankTwoAmbientLocalStage_rankOne_wordValue_eq_one
        hcard hret C hC w hw hval)

/-- Corrected ABO R1 transfers rank-TWO retractability from Γ
to the REAL global group cover using this 1-stable quotient. -/
theorem rankTwoAmbientLocalCover_twoRetractable
    (hcard : A.card = 2) (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    KRetractable
      (SynchronizedProduct.generator gen
        (K.rankTwoAmbientLocalStage hcard hret).transitionSubgroupGenerator)
      2 := by
  have hUp :=
    (K.rankTwoAmbientLocalCoverQuotient hcard hret hgen).kRetractable_of_kStable
      1 (K.rankTwoAmbientLocalCoverQuotient_oneStable
        hcard hret hgen)
      hret
  simpa using hUp

variable [Finite Γ]

/-- The global synchronized rank-two stage group is FINITE
when the ORIGINAL ambient group Γ is finite. -/
theorem finite_rankTwoAmbientLocalCover
    (hcard : A.card = 2) (hret : KRetractable gen 2) :
    Finite (SynchronizedProduct.stageCover gen
      (K.rankTwoAmbientLocalStage hcard hret)) := by
  classical
  letI : Finite (generatedSubgroup gen A) := inferInstance
  letI : Finite
      (K.rankTwoThreeFamilyVertex hcard
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le)) :=
    K.finite_rankTwoThreeFamilyVertex hcard
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le)
  exact SynchronizedProduct.finite_stageCover gen
    (K.rankTwoAmbientLocalStage hcard hret)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
