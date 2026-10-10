import PSTSEPPA.ABO.RankTwoThreeFamilyStableCover
import PSTSEPPA.ABO.StabilityRetractability

/-!
# Two-retractability of the actual three-family synchronized R2 cover

Corrected ABO Proposition 5.4 uses a 1-stable quotient of
G₂ onto H₁ to obtain 2-retractability of G₂. The printed
paper hides the k=1 stability case, and the independent
audit explicitly repairs that gap.

For a GIVEN finite generated retractable ambient group Γ
and a rank-two Cayley skeleton K, the preceding Lean
construction already gives a GENUINE surjective labelled
1-stable quotient from the synchronized group realizing
three actual families of completed rank-two stages.

The independently checked R1 stability/retractability
theorem now proves the domain of THIS concrete cover is
2-retractable. No extra ad hoc deletion argument is needed.

This is a useful base-case CONSTRUCTION CONDITIONAL ON Γ,
K and global retractability of Γ, not a claim to construct
source H₁, its full Z₁, the true G₂ or PSTS EPPA.
In particular full `Retractable gen` is a stronger input
than H₁'s expected merely rank-two retractability.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The genuinely constructed three-family synchronized
group is rank-TWO retractable: equality of group values
of two signed words on ≤2 letters survives erasing any
single unsigned generator. This follows from the
actual one-stable quotient and rank-two retractability
of the ambient Γ. -/
theorem rankTwoThreeFamilyCover_twoRetractable
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    KRetractable
      (SynchronizedProduct.generator gen
        (K.rankTwoThreeFamilyStage hcard hgen hret).transitionSubgroupGenerator)
      2 := by
  have hDown : KRetractable gen (1 + 1) :=
    kRetractable_of_retractable gen hret (1 + 1)
  have hUp :=
    (K.rankTwoThreeFamilyCoverQuotient hcard hgen hret).kRetractable_of_kStable
      1 (K.rankTwoThreeFamilyCoverQuotient_oneStable hcard hgen hret)
      hDown
  simpa using hUp

end CayleySubgraphSpec
end ABO
end PSTSEPPA
