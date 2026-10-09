import PSTSEPPA.ABO.AdmissibleComponentIntersections
import PSTSEPPA.ABO.ComponentIndexMonotonicity

/-!
# Component-index refinement as an injective pair of parent tags

Let K be an admissible A-skeleton and B,C proper subalphabets.
Every intrinsic (B∩C)-component has canonical parent B-component
and C-component tags. The pair of tags uniquely identifies the
(B∩C)-component.

This is a quotient-index form of the already formalized path-level
ABO Lemma 3.21: simultaneous B- and C-reachability is precisely
(B∩C)-reachability. The result is exactly the bookkeeping needed
to compare intersection supports in two selected complete coset
constituents of a full multi-coset extension.

No ambient coset or group coordinate determines the index by
itself: both intrinsic parent component tags are essential.
The equal-, nested-, and empty-alphabet cases are explicit
consequences of the same proof.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The map from an intrinsic (B∩C)-component index to its
containing B- and C-component indices is injective. This uses
K's admissibility and retractability, not ambient injectivity. -/
theorem componentIndex_inter_pair_injective
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hBA : B ⊂ A) (hCA : C ⊂ A)
    (p q : K.ComponentIndex (B ∩ C))
    (hB :
      K.componentIndexMap (B ∩ C) B Finset.inter_subset_left p =
      K.componentIndexMap (B ∩ C) B Finset.inter_subset_left q)
    (hC :
      K.componentIndexMap (B ∩ C) C Finset.inter_subset_right p =
      K.componentIndexMap (B ∩ C) C Finset.inter_subset_right q) :
    p = q := by
  induction p using Quotient.inductionOn with
  | h x =>
    induction q using Quotient.inductionOn with
    | h y =>
      change K.componentClass B x = K.componentClass B y at hB
      change K.componentClass C x = K.componentClass C y at hC
      have hxy :
          K.SubalphabetReachable (B ∩ C) x y :=
        (K.subalphabetReachable_inter_iff
          hadm hgen hret B C hBA hCA x y).mp
          ⟨(K.componentClass_eq_iff B x y).mp hB,
            (K.componentClass_eq_iff C x y).mp hC⟩
      exact (K.componentClass_eq_iff (B ∩ C) x y).mpr hxy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
