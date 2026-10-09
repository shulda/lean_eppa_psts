import PSTSEPPA.ABO.RankTwoComponentBase
import PSTSEPPA.ABO.MultiCosetMinimalSupport

/-!
# Whole-component minimal tagged support in rank two

Definition 3.22 of ABO requires unique minimal support for an
*entire* off-skeleton B-component, attained at a core vertex,
rather than just minimal support for each individual vertex.

For rank |A| ≤ 2, the preceding actual-edge argument proves
that every such B-component is a singleton. Hence its entire
component automatically has the unique least component-tagged
support of its only vertex, attained at that vertex.

This is the previously missing second part of the rank-two
cluster-property base, formulated explicitly as a universal
support comparison across every vertex in the B-component.
No cluster-property axiom or bridge-freeness is assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An off-skeleton rank-two B-component has a unique least
component-tagged support attained at its sole vertex z.

Unlike the singleton-support theorem, the universal quantifier
here ranges over all vertices y genuinely B-reachable from z,
and *all* their tagged coset representations (C,q). -/
theorem rank_two_off_B_component_unique_minimal_support
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : A.card ≤ 2)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hOff :
      ¬ ∃ q : K.AttachedCosetVertex B,
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret B hBP q = z) :
    ∃ (M : Finset ι)
      (hMP : M ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex M),
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret M hMP p = z ∧
      ∀ (y : K.MultiCosetVertex (allProperCosetFamily A)
            hadm hgen hret),
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows z w y) →
        ∀ (C : Finset ι)
          (hCP : C ∈ (allProperCosetFamily A).alphabets)
          (q : K.AttachedCosetVertex C),
          K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP q = y →
          ∃ hMC : M ⊆ C,
            K.attachedSubalphabetMap M C hMC p = q := by
  obtain ⟨M, hMP, p, hp, hmin⟩ :=
    K.allProperCosetVertex_exists_minimal_tagged_support
      hadm hgen hret z
  refine ⟨M, hMP, p, hp, ?_⟩
  intro y hzy C hCP q hq
  have hyz : y = z :=
    K.rank_two_off_selected_B_component_singleton
      hadm hgen hret hcard B hBP z hOff y hzy
  rw [hyz] at hq
  exact hmin C hCP q hq

end CayleySubgraphSpec
end ABO
end PSTSEPPA
