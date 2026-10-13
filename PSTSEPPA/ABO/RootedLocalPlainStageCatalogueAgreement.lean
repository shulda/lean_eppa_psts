import PSTSEPPA.ABO.RootedSourceAllProperCompletedStageIso
import PSTSEPPA.ABO.CompletedFullCosetStage

/-!
# Exact local rooted plain P_A completion versus the canonical catalogue stage

The true rooted original H₁-source proper-coset EGraph is normalized
into its local Γ[A] representative. At rank two, the independently
defined local source-facing unaugmented completion should be
LITERALLY the same signed COMPLETE stage as the canonical
`allProperCompletedStage` appearing as the first component of
the finite all-local G₂ three-family action.

This file tests the full definitional match, including actual
component-tagged quotient vertices, signed edge tokens and fixed
loops. No equality of ambient Γ coordinates is used to identify
different quotient points; the statement is about the REAL
complete action APIs.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The source-rooted LOCAL complete plain proper-coset extension
and the literal complete P_A catalogue stage of the local Cayley
skeleton are the same complete signed action, including all
vertex and edge tags and stationary-loop completion. -/
theorem rootedLocalAllProperCompletedStage_eq_catalogue
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) :
    K.rootedLocalAllProperCompletedStage A hcard hret root =
      (K.intrinsicComponentLocalSlice A root).allProperCompletedStage
        ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
          hcard.le)
        (isGenerated_trivialCompletionGenerator gen A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen 2 hret A hcard.le)
        hcard.ge := by
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
