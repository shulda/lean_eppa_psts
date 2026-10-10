import PSTSEPPA.ABO.RankTwoClusterPropertyBase

/-!
# Rank-two singleton augmentation: the exact missing-edge premise

The type-(2) objects of corrected ABO Definition 5.3 attach a full
B-coset along an actual B-component of the full proper-alphabet
coset extension. At rank two, the B-component classification
already proves that a component not contained in any selected
full B-coset is literally a singleton.

For the singleton case, it is essential that the root has NO
outgoing old B-labelled edge, in either sign. This is not merely
the absence of paths to *other* points: even an old B-labelled
geometric loop could interfere with determinism when a full
B-coset is attached. Here we derive the stronger missing-edge
condition from the true signed-edge source coverage theorem.

This is a direct input to constructing the off-component
augmentation of the genuine rank-two multi-coset EGraph.
It does not itself glue the coset or prove the full
Definition-5.3 R2 stability statement.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A rank-two point outside every tagged selected B-coset
has *no* outgoing genuine old signed B-edge whatsoever.
In particular this excludes old B-labelled loops. -/
theorem rank_two_off_selected_B_no_outgoing_edges
    (hcard : A.card ≤ 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard) hgen hret)
    (hOff : ¬ ∃ q : K.AttachedCosetVertex B,
      K.multiCosetInclude (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard)
        hgen hret B hBP q = z)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard) hgen hret)
    (hsource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard)
        hgen hret).source e = z) :
    signedBase
      ((K.multiCosetEGraph (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard)
        hgen hret).label e) ∉ B := by
  intro hlabel
  obtain ⟨q, hq⟩ :=
    K.rank_two_B_edge_source_has_selected_support
      (K.admissible_of_card_le_two hcard)
      hgen hret hcard B hBP e hlabel
  exact hOff ⟨q, hq.trans hsource⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
