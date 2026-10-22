import PSTSEPPA.ABO.UpwardInductionR1LocalGroupPackage
import PSTSEPPA.ABO.KStablePullbackAdmissibility
import PSTSEPPA.ABO.ForwardInductionLocalAdmissibility

/-!
# ABO corrected Theorem 4.7(i): admissibility of EVERY actual G-cover

Take a labelled group quotient Q: G → H which is k-stable,
a connected admissible H[A]-Cayley skeleton K and an alphabet
A with |A|≤k+1. The source G-cover of K, rooted at any
actual vertex r of its canonical signed full preimage under Q,
is the intrinsic A-connected component of that preimage.

The previously certified general k-stable pullback theorem
transfers admissibility of K to the full *actual signed*
pullback skeleton. Its hereditary component theorem, valid
for B⊆A including B=A, then gives admissibility of EVERY
individual G-cover component.

This is the exact local signed skeleton case of source
upward Theorem 4.7(i) and does not assume the missing
embedding/bridgefreeness claims (ii)-(iii), or surjectivity
of the actual *connected* cover on any unrelated H-component.
No imaginary original old edges, no ambient-coordinate tag
collapses, no global retractability of G, no new axioms/sorry.

Repair R1 needed for the following coset-geometry stage
is proved separately in UpwardInductionR1LocalGroupPackage.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- Source ABO upward Theorem 4.7(i), literal G-COVER
admissibility for any connected A-component in the genuine
signed inverse-image Cayley graph of an admissible H[A]
skeleton. Only k-stability (and |A|≤k+1) is necessary
for this admissibility implication; global retractability,
the cluster property and augmented stage cover hypotheses
belong to the later (ii)-(iii) clauses. -/
theorem upwardGCover_admissible_of_kStable
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (k : ℕ) (hStable : Q.KStable k)
    (hA : A.card ≤ k+1)
    (hAdmH : K.AdmissibleForCosetExtension)
    (root : (K.pullbackQuotient Q).Vertex) :
    ((K.pullbackQuotient Q).subalphabetComponentSubgraph A root).AdmissibleForCosetExtension := by
  have hAdmPullback :
      (K.pullbackQuotient Q).AdmissibleForCosetExtension :=
    K.pullbackQuotient_admissible_of_kStable
      Q k hStable hA hAdmH
  exact (K.pullbackQuotient Q).subalphabetComponentSubgraph_admissible_of_subset
    hAdmPullback A (by intro i hi; exact hi) root

end CayleySubgraphSpec
end ABO
end PSTSEPPA
