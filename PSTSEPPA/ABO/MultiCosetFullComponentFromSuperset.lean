import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Full B-component geometry whenever a selected C-coset is met

A vertex z of an arbitrary multi-coset extension may have a
B-component disjoint from the old skeleton. Nevertheless, if
that B-component meets a completed C-coset with B⊆C, then
the **entire** B-component, not merely the part inside C,
is exactly one full left B-coset in the tagged C-copy.

The proof is actual path transport: reachability from z is
equivalent to reachability from the meeting point p, by
inverting the witnessed B-path p→z and concatenating.
The tagged-C B-coset classification then gives an exact iff.

This is the unrestricted-rank *full-coset alternative* of
the source Definition 3.22 component geometry. It requires
no pre-existing cluster-property hypothesis, and does not
claim the other, lower-cluster alternative.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Once an intrinsic B-component meets a selected tagged full
C-coset with B⊆C, the B-component's entire vertex set is exactly
one literal tagged C-copy of an ambient full B-coset. This allows
other selected alphabet constituents incomparable with B or C. -/
theorem multiCoset_B_component_full_if_meets_selected_superset
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (B : Finset ι) (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex C)
    (z : K.MultiCosetVertex P hadm hgen hret)
    (hMeet : ∃ u : LabelWord ι, LabelWord.Uses B u ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C hCP p) u z)
    (y : K.MultiCosetVertex P hadm hgen hret) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows z w y) ↔
    ∃ q : K.AttachedCosetVertex C,
      q.1 = p.1 ∧
      q.2.1 ∈ generatedLeftCoset gen B p.2.1 ∧
      y = K.multiCosetInclude P hadm hgen hret C hCP q := by
  let G := K.multiCosetEGraph P hadm hgen hret
  have hFromP :=
    K.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret C hCP B hBC p y
  obtain ⟨u, hu, hPathPZ⟩ := hMeet
  constructor
  · rintro ⟨w, hw, hPathZY⟩
    apply hFromP.mp
    refine ⟨u ++ w,
      (LabelWord.uses_append B u w).2 ⟨hu, hw⟩, ?_⟩
    exact G.follows_append hPathPZ hPathZY
  · intro hy
    obtain ⟨w, hw, hPathPY⟩ := hFromP.mpr hy
    refine ⟨PSTS.SignedWord.inv u ++ w,
      (LabelWord.uses_append B (PSTS.SignedWord.inv u) w).2
        ⟨hu.inv, hw⟩, ?_⟩
    exact G.follows_append (G.follows_inverse hPathPZ) hPathPY

end CayleySubgraphSpec
end ABO
end PSTSEPPA
