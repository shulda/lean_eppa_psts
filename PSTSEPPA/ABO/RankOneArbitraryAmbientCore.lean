import PSTSEPPA.ABO.RankOneArbitraryAmbient
import PSTSEPPA.ABO.MultiCosetMinimalSupport

/-!
# Whole-component least tagged support for the rank-one lower branch

At arbitrary ambient alphabet rank, a B-component with |B|≤1
which avoids every selected C⊇B is a singleton. The existing
individual-vertex minimal support lemma can therefore be
promoted to the full *whole-component* universal condition
in Definition 3.22, without assuming the cluster property.

The quantifier below genuinely ranges over every B-reachable
vertex y and all possible selected tagged presentations of y,
and identifies one specific support point (M,p) at z that
factors through all such presentations. This is stronger
than merely naming the least supporting alphabet of z.

We deliberately restrict to the no-large-constituent branch:
the full-coset alternative was already proved separately.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A rank-one (or empty alphabet) B-component which meets
no selected C⊇B is a singleton, with a single unique
least tagged component support attained at its core vertex.
The source's *whole-component* minimality quantifiers are explicit. -/
theorem allProperCoset_rank_one_no_large_whole_component_core
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (hcard : B.card ≤ 1)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLargeZ :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C z) :
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
    K.allProperCoset_rank_one_no_large_component_singleton
      hadm hgen hret B hBP hcard z y hNoLargeZ hzy
  rw [hyz] at hq
  exact hmin C hCP q hq

end CayleySubgraphSpec
end ABO
end PSTSEPPA
