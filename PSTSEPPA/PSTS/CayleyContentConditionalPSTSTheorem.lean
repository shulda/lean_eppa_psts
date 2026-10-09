import PSTSEPPA.PSTS.CayleyMinimalContentToMax
import PSTSEPPA.PSTS.FinitePermutationCompletion
import PSTSEPPA.PSTS.EPPAFromMax

/-!
# The exact final PSTS EPPA theorem conditional on finite Cayley-GRL

Everything on the PSTS transfer side can now be assembled directly.
For a finite PSTS A, index the chosen selected partial automorphisms
by the TYPE of ALL partial automorphisms of A, with identity
generator function; this requires no arbitrary enumeration.

Every one of them admits a total auxiliary permutation extension
by the finite partial-permutation completion theorem. These
chosen permutations generate the concrete finite Q and define
the actual oriented Cayley graph.

The ONE remaining input is a finite Cayley minimal positive-edge
content certificate for these canonical permutation lifts:
the corrected finite group-reflection theorem must CONSTRUCT it.
Given this explicit object, path inclusion implies fibre-MAX,
and the already-certified Gate T2 produces a finite PSTS witness,
closed embedding and total extensions of EVERY partial automorphism.

The construction below is genuinely conditional: it does NOT
infer the content certificate or the existence of its finite
reflecting group from admissibility, nor assert unconditional EPPA.
It is an executable specification of what remains to be proved.
-/

namespace PSTSEPPA
namespace PSTS

variable {V : Type*} [Fintype V]

/-- Canonical auxiliary total permutation lifts of ALL
partial automorphisms of the finite PSTS, indexed by
the partial automorphism itself. -/
noncomputable def allPartialAutPermutationLifts (A : PSTS V) :
    TotalPermutationLifts A
      (fun p : PartialAut A => p) :=
  finiteTotalPermutationLifts A (fun p : PartialAut A => p)

/-- Final CONSTRUCTIVE ordinary finite-PSTS EPPA, conditional only
on the explicit specialised Cayley minimal-content certificate.
The returned witness includes its finite carrier, closed induced
copy of A, and total extensions for EVERY partial automorphism. -/
noncomputable def allPartialAutEPPA_of_CayleyContent
    (A : PSTS V)
    (C : CayleyMinimalContentCertificate
      (allPartialAutPermutationLifts A)) :
    SelectedEPPAWitness A (fun p : PartialAut A => p) :=
  (C.toMaxTransporterExtension).selectedEPPAWitness

/-- The conditional witness extends every partial automorphism,
not just a previously selected proper subfamily. -/
theorem allPartialAutEPPA_of_CayleyContent_extends
    (A : PSTS V)
    (C : CayleyMinimalContentCertificate
      (allPartialAutPermutationLifts A))
    (p : PartialAut A) {x y : V}
    (hxy : p.toPEquiv x = some y) :
    ((allPartialAutEPPA_of_CayleyContent A C).extend p).toPEquiv
        ((allPartialAutEPPA_of_CayleyContent A C).embed x) =
      some ((allPartialAutEPPA_of_CayleyContent A C).embed y) :=
  (allPartialAutEPPA_of_CayleyContent A C).extends_gen p hxy

end PSTS
end PSTSEPPA
