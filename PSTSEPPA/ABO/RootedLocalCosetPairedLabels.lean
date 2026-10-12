import PSTSEPPA.ABO.RootedSourceMultiCosetCompletedEGraphIso
import PSTSEPPA.ABO.WeakCompletePairedEdges
import PSTSEPPA.ABO.StandardCosetFamily

/-!
# Legal signed loop completion on the actual local rank-two coset extension

The source-rooted multi-coset EGraph is obtained from the local
Γ[A] representative, with |A|=2 and ambient Γ only 2-retractable.

The genuine ALL-PROPER subalphabet family is weakly complete on the
local skeleton. Its canonical multi-coset EGraph therefore has paired
signed outgoing labels. We identify that precise EGraph with the
independently reconstructed source/label quotient EGraph from the
rooted source-isomorphism API (#387), so the LEGAL stationary-loop
completion applies to this very graph without an extra hypothesis.

This is about the plain proper-alphabet coset EGraph, before any
source B-augmentation. The original rooted source EGraph's pairing
will follow by transporting this property along the full signed
graph isomorphism, not by pretending ambient Γ is globally retractable.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- Every vertex of the genuine local Γ[A] full proper-coset quotient
has outgoing positive i if and only if it has outgoing negative i.
This establishes the EXACT legality condition for trivial fixed-loop
completion, with Γ only rank-2 retractable. -/
theorem rootedLocalAllProperMultiCoset_locallyPairedLabels
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex) :
    (K.rootedLocalMultiCosetCompletedEGraph A hcard hret root
      (allProperCosetFamily A)).LocallyPairedLabels := by
  let L := K.intrinsicComponentLocalSlice A root
  let hadm : L.AdmissibleForCosetExtension :=
    L.admissible_of_card_le_two hcard.le
  let hgen : IsGenerated (trivialCompletionGenerator gen A) :=
    isGenerated_trivialCompletionGenerator gen A
  let hretL : Retractable (trivialCompletionGenerator gen A) :=
    retractable_trivialCompletionGenerator_of_kRetractable
      gen 2 hret A hcard.le
  let P := allProperCosetFamily A
  have hweak : L.MultiCosetWeaklyComplete P hadm hgen hretL :=
    allProperCosetFamily_weaklyComplete L hadm hgen hretL hcard.ge
  have hpaired : (L.multiCosetEGraph P hadm hgen hretL).LocallyPairedLabels :=
    L.multiCoset_locallyPairedLabels_of_weakComplete
      P hadm hgen hretL hweak
  change (L.multiCosetEGraph P hadm hgen hretL).LocallyPairedLabels
  exact hpaired

end CayleySubgraphSpec
end ABO
end PSTSEPPA
