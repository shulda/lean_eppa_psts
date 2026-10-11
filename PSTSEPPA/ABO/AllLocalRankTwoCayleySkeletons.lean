import PSTSEPPA.ABO.AllFiniteRankTwoCayleySkeletons
import PSTSEPPA.ABO.RankTwoIndexedAmbientStageCover

/-!
# All local rank-two Cayley skeleton stages over a 2-retractable group

At the first substantive step of the corrected ABO induction, the
intermediate generated group H₁ is only TWO-retractable; global
retractability is not a legitimate hypothesis.

For EACH two-letter subalphabet A, the trivially completed actual
subgroup H₁[A] is globally retractable by the certified local
rank-retractability theorem. We enumerate ALL possible literal
incomplete A-labelled Cayley skeletons over this actual subgroup,
including disconnected old graphs, repeated/identity generator
labels and signed inverse edge tokens. No arbitrary source-cover
representatives are chosen.

For finite Γ the index type (A,K) is finite. The checked local
rank-two three-family completion of each K is assembled into one
literal tagged dependent disjoint complete action. Synchronizing
this TRUE action with the original Γ produces a finite genuinely
generated group, a generator-preserving surjective 1-STABLE
quotient back onto Γ, and a 2-retractable domain.

The theorem does NOT yet identify ALL corrected source Z₁ stages
with these local (A,K) actions, nor does it prove bridge-freeness,
general k stability or PSTS EPPA. Source-specific cover indexing
and the higher-rank geometry remain separate proof obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ}

/-- Every two-letter subalphabet A together with EVERY actual
incomplete A-Cayley skeleton in the fully generated, trivially
completed subgroup Γ[A]. Distinct K tags are retained. -/
abbrev AllLocalRankTwoSkeletonIndex (gen : ι → Γ) :=
  Σ a : {A : Finset ι // A.card = 2},
    CayleySubgraphSpec (trivialCompletionGenerator gen a.1) a.1

/-- The exact parent alphabet of a local skeleton index. -/
def allLocalRankTwoAlphabet
    (j : AllLocalRankTwoSkeletonIndex gen) : Finset ι :=
  j.1.1

@[simp]
theorem allLocalRankTwoAlphabet_card
    (j : AllLocalRankTwoSkeletonIndex gen) :
    (allLocalRankTwoAlphabet j).card = 2 :=
  j.1.2

/-- The genuine local skeleton at the selected two-letter
subgroup, rather than an arbitrary Γ-Cayley ambient set. -/
noncomputable abbrev allLocalRankTwoSkeleton
    (j : AllLocalRankTwoSkeletonIndex gen) :
    CayleySubgraphSpec
      (trivialCompletionGenerator gen (allLocalRankTwoAlphabet j))
      (allLocalRankTwoAlphabet j) :=
  j.2

/-- The actual complete tagged action of the local rank-two
three-family augmented stages, simultaneously for all A and K. -/
noncomputable abbrev allLocalRankTwoStage
    (hret : KRetractable gen 2) :=
  rankTwoIndexedAmbientStage
    (gen := gen)
    (fun j : AllLocalRankTwoSkeletonIndex gen =>
      allLocalRankTwoAlphabet j)
    (fun j => allLocalRankTwoAlphabet_card j)
    (fun j => allLocalRankTwoSkeleton j)
    hret

/-- Actual rank-one word kernel against the ORIGINAL labelled
group Γ, not merely the smaller local groups Γ[A]. It applies
to every signed word supported in at most one label, including
outside the selected parent alphabet. -/
theorem allLocalRankTwoStage_rankOneKernel
    (hret : KRetractable gen 2)
    (C : Finset ι) (hC : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hvalue : PSTS.SignedWord.evalGroup gen w = 1) :
    (allLocalRankTwoStage (gen := gen) hret).wordValue w = 1 := by
  exact rankTwoIndexedAmbientStage_rankOne_wordValue_eq_one
    (gen := gen)
    (fun j : AllLocalRankTwoSkeletonIndex gen =>
      allLocalRankTwoAlphabet j)
    (fun j => allLocalRankTwoAlphabet_card j)
    (fun j => allLocalRankTwoSkeleton j)
    hret C hC w hw hvalue

/-- The literal synchronized generated subgroup over Γ and
the complete action consisting of ALL its local rank-two stages. -/
noncomputable abbrev allLocalRankTwoGroup
    (hret : KRetractable gen 2) :=
  SynchronizedProduct.stageCover gen
    (allLocalRankTwoStage (gen := gen) hret)

/-- A TRUE generator-preserving surjection from the all-local
group onto Γ. This is not a hypothetical group cover. -/
noncomputable def allLocalRankTwoCoverQuotient
    (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :=
  rankTwoIndexedAmbientCoverQuotient (gen := gen)
    (fun j : AllLocalRankTwoSkeletonIndex gen =>
      allLocalRankTwoAlphabet j)
    (fun j => allLocalRankTwoAlphabet_card j)
    (fun j => allLocalRankTwoSkeleton j)
    hret hgen

/-- The actual Γ-labelled quotient of this universal family
is 1-stable for ANY 2-retractable Γ. In particular global
retractability of Γ is not being used. -/
theorem allLocalRankTwoCoverQuotient_oneStable
    (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    (allLocalRankTwoCoverQuotient (gen := gen) hret hgen).KStable 1 := by
  exact rankTwoIndexedAmbientCoverQuotient_oneStable (gen := gen)
    (fun j : AllLocalRankTwoSkeletonIndex gen =>
      allLocalRankTwoAlphabet j)
    (fun j => allLocalRankTwoAlphabet_card j)
    (fun j => allLocalRankTwoSkeleton j)
    hret hgen

/-- Corrected ABO R1: its genuine generated group is already
2-retractable because the quotient to Γ is 1-stable and Γ
is 2-retractable, even without a global deletion map on Γ. -/
theorem allLocalRankTwoGroup_twoRetractable
    (hret : KRetractable gen 2)
    (hgen : IsGenerated gen) :
    KRetractable
      (SynchronizedProduct.generator gen
        (allLocalRankTwoStage (gen := gen) hret).transitionSubgroupGenerator)
      2 := by
  exact rankTwoIndexedAmbientCover_twoRetractable (gen := gen)
    (fun j : AllLocalRankTwoSkeletonIndex gen =>
      allLocalRankTwoAlphabet j)
    (fun j => allLocalRankTwoAlphabet_card j)
    (fun j => allLocalRankTwoSkeleton j)
    hret hgen

variable [Finite Γ]

/-- Because Γ and its finite label alphabet are finite,
ALL pairs (A,K) of local two-letter alphabets and genuine
signed A-Cayley skeletons form a finite index type.
No preselected family of source-cover skeletons is needed. -/
theorem finite_allLocalRankTwoSkeletonIndex :
    Finite (AllLocalRankTwoSkeletonIndex gen) := by
  classical
  exact @Finite.instSigma _ _
    (inferInstance : Finite {A : Finset ι // A.card = 2})
    (fun a => by
      letI : Finite (generatedSubgroup gen a.1) := inferInstance
      exact finite_allCayleySubgraphSpec
        (trivialCompletionGenerator gen a.1) a.1)

/-- The tagged vertex carrier of every local completed
rank-two action is finite. The actual quotient and component
tags are preserved even when two vertices have the same
coordinate in Γ. -/
theorem finite_allLocalRankTwoStageVertex
    (hret : KRetractable gen 2) :
    Finite
      (rankTwoIndexedAmbientVertex
        (fun j : AllLocalRankTwoSkeletonIndex gen =>
          allLocalRankTwoAlphabet j)
        (fun j => allLocalRankTwoAlphabet_card j)
        (fun j => allLocalRankTwoSkeleton j)
        hret) := by
  classical
  letI : Finite (AllLocalRankTwoSkeletonIndex gen) :=
    finite_allLocalRankTwoSkeletonIndex (gen := gen)
  exact @Finite.instSigma _ _ (inferInstance : Finite (AllLocalRankTwoSkeletonIndex gen))
    (fun j => by
      letI : Finite (generatedSubgroup gen (allLocalRankTwoAlphabet j)) :=
        inferInstance
      exact (allLocalRankTwoSkeleton j).finite_rankTwoThreeFamilyVertex
        (allLocalRankTwoAlphabet_card j)
        (isGenerated_trivialCompletionGenerator gen (allLocalRankTwoAlphabet j))
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret (allLocalRankTwoAlphabet j)
          (allLocalRankTwoAlphabet_card j).le))

/-- The ACTUAL synchronized generated group of every two-letter
local skeleton is finite, despite its huge redundant index.
No quantitative bound and no decidable word equivalence needed. -/
theorem finite_allLocalRankTwoGroup
    (hret : KRetractable gen 2) :
    Finite (allLocalRankTwoGroup (gen := gen) hret) := by
  classical
  letI : Finite (AllLocalRankTwoSkeletonIndex gen) :=
    finite_allLocalRankTwoSkeletonIndex (gen := gen)
  exact finite_rankTwoIndexedAmbientCover (gen := gen)
    (fun j : AllLocalRankTwoSkeletonIndex gen =>
      allLocalRankTwoAlphabet j)
    (fun j => allLocalRankTwoAlphabet_card j)
    (fun j => allLocalRankTwoSkeleton j)
    hret

end ABO
end PSTSEPPA
