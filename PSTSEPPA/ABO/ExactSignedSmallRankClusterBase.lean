import PSTSEPPA.ABO.ExactSignedRankTwoClusterBase
import PSTSEPPA.ABO.OffFullBCosetMinimalSupport

/-!
# Source forward-induction small-rank bases, including 0 and 1

Printed ABO Proposition 4.4 gives the substantive two-letter
base of the exact whole signed cluster property. The complete
cardinality induction of Theorem 4.5 ALSO encounters lower
components with at most one letter. The corresponding base
must not be silently asserted by applying the two-letter result
out of scope.

For |A| <= 1, every selected proper alphabet is empty. Consequently
any point of the FULL proper-alphabet tagged coset extension is
supported by B=empty, so it has a genuine B-word path from the
original old skeleton. Thus NO off-skeleton B-component exists:
the precise signed Definition 3.22 predicate holds vacuously.

Combine this direct argument with the certified EXACT signed
rank-two source Proposition 4.4. We get the entire base
|A| <= 2 with source admissibility DERIVED automatically,
including all degenerate empty/singleton alphabet cases.

No fictitious old edges, coordinate-tag identification, new
axioms or sorry, and no lower bridgefree assumption.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- At alphabet rank 0 or 1, every actual quotient B-component
necessarily meets the old skeleton. There are NO off-skeleton
components to which Definition 3.22 must be applied.

We do not require the generated group to be rank-one or the
original K to be complete; all paths are true signed paths. -/
theorem smallRank_hasExactSignedWholeComponentClusterProperty
    [Finite Γ]
    (hcard : A.card ≤ 1)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    K.HasExactSignedWholeComponentClusterProperty hadm hgen hret := by
  classical
  let P := allProperCosetFamily A
  intro B hBP anchor hOff
  have hBcard : B.card = 0 := by
    have hlt : B.card < A.card :=
      Finset.card_lt_card ((mem_allProperCosetFamily A B).mp hBP)
    omega
  have hBempty : B = ∅ := Finset.card_eq_zero.mp hBcard
  obtain ⟨C, hCP, p, hp⟩ :=
    K.multiCosetVertex_exists_support P hadm hgen hret anchor
  have hCcard : C.card = 0 := by
    have hlt : C.card < A.card :=
      Finset.card_lt_card ((mem_allProperCosetFamily A C).mp hCP)
    omega
  have hCeqB : C = B := by
    calc
      C = ∅ := Finset.card_eq_zero.mp hCcard
      _ = B := hBempty.symm
  subst C
  have hSupported :
      K.MultiCosetVertexSupported P hadm hgen hret B anchor :=
    ⟨hCP, p, hp⟩
  exact False.elim
    ((K.offSkeleton_B_not_B_supported
      hadm hgen hret B hBP anchor hOff) hSupported)

/-- The COMPLETE small-rank base of the forward cluster induction,
covering rank 0, rank 1, and the genuine nontrivial rank 2.
Source admissibility is proven from |A| <= 2; no artificial
"rank>=2" assumption is smuggled into an induction hypothesis. -/
theorem card_le_two_hasExactSignedWholeComponentClusterProperty
    [Finite Γ]
    (hcard : A.card ≤ 2)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    K.HasExactSignedWholeComponentClusterProperty
      (K.admissible_of_card_le_two hcard) hgen hret := by
  by_cases hsmall : A.card ≤ 1
  · exact K.smallRank_hasExactSignedWholeComponentClusterProperty
      hsmall (K.admissible_of_card_le_two hcard) hgen hret
  · have htwo : A.card = 2 := by omega
    exact K.rankTwo_hasExactSignedWholeComponentClusterProperty
      htwo hgen hret

end CayleySubgraphSpec
end ABO
end PSTSEPPA
