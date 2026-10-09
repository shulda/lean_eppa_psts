import PSTSEPPA.PSTS.CayleyReflectingSemidirectToMax
import PSTSEPPA.PSTS.CayleyContentConditionalPSTSTheorem

/-!
# Final closed-PSTS EPPA from a finite Cayley reflecting group

The full PSTS transfer no longer needs any selected-subfamily
restriction or prepackaged H-valued maximum-word certificate:
the finite G with Q-equivariant positive-edge generators and
same-endpoint pairwise content-reduction is sufficient.

The chain, all checked explicitly in Lean, is

  finite reflecting G
    => finite H ≤ G ⋊ Q
    => pairwise signed Cayley path reduction in each H-fibre
    => a minimum positive-edge-content representative
    => fibre-MAX
    => finite closed-PSTS EPPA witness.

This module asserts **no existence** of reflecting G. That is
exactly the remaining finite Cayley-GRL proof obligation.
-/

namespace PSTSEPPA
namespace PSTS

variable {V : Type*} [Fintype V]

/-- Conditional constructive EPPA for ALL partial automorphisms
of a finite PSTS, requiring only a finite equivariant Cayley
reflecting-group certificate with geometric path reduction. -/
noncomputable def allPartialAutEPPA_of_FiniteCayleyReflection
    (A : PSTS V)
    (R : FiniteEquivariantCayleyReflection
      (allPartialAutPermutationLifts A)) :
    SelectedEPPAWitness A (fun p : PartialAut A => p) :=
  (R.toMaxTransporterExtension).selectedEPPAWitness

/-- The resulting finite witness extends each partial automorphism
on its full closed source, not merely a selected subfamily. -/
theorem allPartialAutEPPA_of_FiniteCayleyReflection_extends
    (A : PSTS V)
    (R : FiniteEquivariantCayleyReflection
      (allPartialAutPermutationLifts A))
    (p : PartialAut A) {x y : V}
    (hxy : p.toPEquiv x = some y) :
    ((allPartialAutEPPA_of_FiniteCayleyReflection A R).extend p).toPEquiv
      ((allPartialAutEPPA_of_FiniteCayleyReflection A R).embed x) =
    some ((allPartialAutEPPA_of_FiniteCayleyReflection A R).embed y) :=
  (allPartialAutEPPA_of_FiniteCayleyReflection A R).extends_gen p hxy

end PSTS
end PSTSEPPA
