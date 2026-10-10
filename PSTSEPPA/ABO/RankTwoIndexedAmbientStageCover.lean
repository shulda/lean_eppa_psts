import PSTSEPPA.ABO.RankTwoAmbientLocalStageCover
import PSTSEPPA.ABO.DependentDisjointStages

/-!
# One genuine synchronized group realizing any FINITE family of rank-two local stages

Corrected ABO Definition 5.3 requires a finite collection of many
complete stage graphs; it does not suffice to construct just one good
rank-two stage. From a generated ambient group Γ which is merely
2-retractable, we may take ANY family (indexed by J) of rank-two
alphabets A[j] and true Cayley skeletons K[j] over the genuine local
completed subgroup Γ[A[j]].

We retain each true rank-two three-family completed action on its
actual tagged vertex carrier, and combine the whole J-family via the
literal dependent disjoint action. The label-action kernel of this
one combined complete EGraph is the intersection of the per-stage
kernels. Each kernel holds against the ORIGINAL ambient Γ, by the
bounded retractability transfer.

Consequently synchronizing Γ directly with this finite family yields
ONE concrete surjective 1-stable quotient onto Γ; its domain is
2-retractable, and finite whenever Γ and J are finite.

This is an algebraic ASSEMBLY theorem for an arbitrary given finite
rank-two catalogue, NOT a construction of the particular H₁-covers
or all source Definition-5.3 objects of the still-unbuilt Z₁.
-/

namespace PSTSEPPA
namespace ABO

variable {J ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ}

/-- Exact sigma-tagged carrier of a family of genuine rank-two stages.
Every member has a distinct stage tag; its component/coset tags
are themselves retained, rather than identified by Γ-coordinates. -/
abbrev rankTwoIndexedAmbientVertex
    (A : J → Finset ι)
    (hcard : ∀ j : J, (A j).card = 2)
    (K : ∀ j : J,
      CayleySubgraphSpec (trivialCompletionGenerator gen (A j)) (A j))
    (hret : KRetractable gen 2) :=
  Σ j : J,
    (K j).rankTwoThreeFamilyVertex (hcard j)
      (isGenerated_trivialCompletionGenerator gen (A j))
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret (A j) (hcard j).le)

/-- THE actual complete action combining ALL given local stages.
The sigma index and full stage carrier are not collapsed; empty
family, empty fibres, trivial and repeated generators are allowed. -/
noncomputable def rankTwoIndexedAmbientStage
    (A : J → Finset ι)
    (hcard : ∀ j : J, (A j).card = 2)
    (K : ∀ j : J,
      CayleySubgraphSpec (trivialCompletionGenerator gen (A j)) (A j))
    (hret : KRetractable gen 2) :
    CompleteEGraph
      (rankTwoIndexedAmbientVertex A hcard K hret)
      (ActionEdge (rankTwoIndexedAmbientVertex A hcard K hret) ι) ι :=
  dependentDisjointStage
    (fun j : J => (K j).rankTwoAmbientLocalStage (hcard j) hret)

/-- No Γ-identity word on ≤1 labels can move a point in ANY
member of this entire dependent rank-two stage collection. -/
theorem rankTwoIndexedAmbientStage_rankOne_wordValue_eq_one
    (A : J → Finset ι)
    (hcard : ∀ j : J, (A j).card = 2)
    (K : ∀ j : J,
      CayleySubgraphSpec (trivialCompletionGenerator gen (A j)) (A j))
    (hret : KRetractable gen 2)
    (C : Finset ι) (hC : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (rankTwoIndexedAmbientStage A hcard K hret).wordValue w = 1 := by
  change
    (dependentDisjointStage
      (fun j : J => (K j).rankTwoAmbientLocalStage (hcard j) hret)).wordValue w = 1
  apply (dependentDisjointStage_wordValue_eq_one_iff
    (fun j : J => (K j).rankTwoAmbientLocalStage (hcard j) hret) w).mpr
  intro j
  exact (K j).rankTwoAmbientLocalStage_rankOne_wordValue_eq_one
    (hcard j) hret C hC w hw hval

/-- The real generated synchronized quotient onto Γ from the WHOLE
indexed family, not a separate quotient for each individual stage. -/
noncomputable def rankTwoIndexedAmbientCoverQuotient
    (A : J → Finset ι)
    (hcard : ∀ j : J, (A j).card = 2)
    (K : ∀ j : J,
      CayleySubgraphSpec (trivialCompletionGenerator gen (A j)) (A j))
    (hret : KRetractable gen 2) (hgen : IsGenerated gen) :
    LabelledGroupQuotient
      (SynchronizedProduct.generator gen
        (rankTwoIndexedAmbientStage A hcard K hret).transitionSubgroupGenerator)
      gen :=
  SynchronizedProduct.stageCoverQuotient gen
    (rankTwoIndexedAmbientStage A hcard K hret) hgen

/-- A single rank-ONE stable surjection to the ORIGINAL Γ from
the genuinely assembled dependent multi-stage transition group. -/
theorem rankTwoIndexedAmbientCoverQuotient_oneStable
    (A : J → Finset ι)
    (hcard : ∀ j : J, (A j).card = 2)
    (K : ∀ j : J,
      CayleySubgraphSpec (trivialCompletionGenerator gen (A j)) (A j))
    (hret : KRetractable gen 2) (hgen : IsGenerated gen) :
    (rankTwoIndexedAmbientCoverQuotient A hcard K hret hgen).KStable 1 := by
  exact SynchronizedProduct.stageCoverQuotient_kStable_of_stageKernel
    gen (rankTwoIndexedAmbientStage A hcard K hret) hgen 1
    (by
      intro C hC w hw hval
      exact rankTwoIndexedAmbientStage_rankOne_wordValue_eq_one
        A hcard K hret C hC w hw hval)

/-- This single synchronized group realizing every indexed stage is
rank-TWO retractable by corrected ABO R1 and 1-stability. -/
theorem rankTwoIndexedAmbientCover_twoRetractable
    (A : J → Finset ι)
    (hcard : ∀ j : J, (A j).card = 2)
    (K : ∀ j : J,
      CayleySubgraphSpec (trivialCompletionGenerator gen (A j)) (A j))
    (hret : KRetractable gen 2) (hgen : IsGenerated gen) :
    KRetractable
      (SynchronizedProduct.generator gen
        (rankTwoIndexedAmbientStage A hcard K hret).transitionSubgroupGenerator)
      2 := by
  have hUp :=
    (rankTwoIndexedAmbientCoverQuotient
      A hcard K hret hgen).kRetractable_of_kStable
      1 (rankTwoIndexedAmbientCoverQuotient_oneStable
        A hcard K hret hgen)
      hret
  simpa using hUp

variable [Finite J] [Finite Γ]

/-- The ENTIRE indexed action carrier and its synchronized group
are finite. This is a real dependent sigma finiteness proof,
not a claim that image coordinates in Γ distinguish tagged points. -/
theorem finite_rankTwoIndexedAmbientCover
    (A : J → Finset ι)
    (hcard : ∀ j : J, (A j).card = 2)
    (K : ∀ j : J,
      CayleySubgraphSpec (trivialCompletionGenerator gen (A j)) (A j))
    (hret : KRetractable gen 2) :
    Finite
      (SynchronizedProduct.stageCover gen
        (rankTwoIndexedAmbientStage A hcard K hret)) := by
  classical
  letI : Finite (rankTwoIndexedAmbientVertex A hcard K hret) :=
    @Finite.instSigma _ _
      (inferInstance : Finite J)
      (fun j => by
        letI : Finite (generatedSubgroup gen (A j)) := inferInstance
        exact (K j).finite_rankTwoThreeFamilyVertex
          (hcard j)
          (isGenerated_trivialCompletionGenerator gen (A j))
          (retractable_trivialCompletionGenerator_of_kRetractable
            gen 2 hret (A j) (hcard j).le))
  exact SynchronizedProduct.finite_stageCover gen
    (rankTwoIndexedAmbientStage A hcard K hret)

end ABO
end PSTSEPPA
