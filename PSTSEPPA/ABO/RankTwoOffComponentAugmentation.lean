import PSTSEPPA.ABO.RankTwoSingletonAugmentationInput
import PSTSEPPA.ABO.IsolatedCosetGluing

/-!
# Actual rank-two off-component full-coset augmentation (ABO Definition 5.3 type 2)

The abstract isolated-coset gluing construction is now instantiated on the
REAL rank-two full proper-alphabet multi-coset extension. Its root is a genuine
tagged vertex outside every selected completed B-coset. The full new B-coset
is based at the true ambient Cayley coordinate of that root.

The sole no-old-B-edge input required by the generic EGraph construction is
proved for this exact quotient EGraph by the rank-two signed-edge-source
classification. Thus the resulting graph is an actual ABO EGraph with genuine
formal inverse edges, not a conditional interface assuming its determinism.

This is the non-full singleton alternative of the corrected type-(2)
augmentation, not yet the full finite Section-5 family or its stability.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The genuine rank-two full coset extension with a fresh full B-coset
attached at an off-selected-B singleton component. All source graph data
and the new coset share the same actual generator family. -/
noncomputable def rankTwoOffComponentAugmentation
    (hcard : A.card ≤ 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard) hgen hret)
    (hOff :
      ¬ ∃ q : K.AttachedCosetVertex B,
        K.multiCosetInclude (allProperCosetFamily A)
          (K.admissible_of_card_le_two hcard)
          hgen hret B hBP q = z) :=
  IsolatedCosetGluing.gluedEGraph
    (K.multiCosetEGraph (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard) hgen hret)
    gen B
    (K.multiCosetAmbientValue (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard) hgen hret z)
    z
    (by
      intro e he
      exact K.rank_two_off_selected_B_no_outgoing_edges
        hcard hgen hret B hBP z hOff e he)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
