import PSTSEPPA.ABO.AttachedCosetNaturality
import PSTSEPPA.ABO.MultiCosetVertexQuotient

/-!
# Skeleton-point rigidity in the multi-alphabet vertex quotient

Suppose a point in a component-indexed B-coset and an embedded original
skeleton vertex x in a C-coset represent the same point of the checked
multi-alphabet quotient. Then the B-point must be *exactly* the
component-tagged copy of x, not merely a point with the same ambient
group coordinate.

The proof uses the actual shared (B ∩ C)-support, and the injection
of (B ∩ C)-attached copies into C, including the degenerate B ∩ C = C
case. It does not assume the canonical map into the ambient Cayley
group is globally injective.

This lemma is the key bridge for mixed edges: an edge completed inside
a B-coset can overlap an old skeleton edge outside C only at a literal
old skeleton vertex, with the correct component tag.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If a tagged B-point is glued to an embedded original skeleton
vertex in the C-summand, it is already that skeleton point in B. -/
theorem multiCosetInclude_reflects_skeleton_point
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (p : K.AttachedCosetVertex B) (x : K.Vertex)
    (hglue :
      K.multiCosetInclude P hadm hgen hret B hBP p =
        K.multiCosetInclude P hadm hgen hret C hCP
          (K.attachedOfSkeletonVertex C x)) :
    p = K.attachedOfSkeletonVertex B x := by
  have hrel := Quotient.exact hglue
  change K.ShareIntersectionSupport B C p
    (K.attachedOfSkeletonVertex C x) at hrel
  rcases hrel with ⟨r, hrB, hrC⟩
  have hrx :
      r = K.attachedOfSkeletonVertex (B ∩ C) x :=
    K.attachedSubalphabetMap_reflects_skeleton
      hadm C (B ∩ C) (P.proper C hCP)
      Finset.inter_subset_right r x hrC
  calc
    p = K.attachedSubalphabetMap (B ∩ C) B
          Finset.inter_subset_left r := hrB.symm
    _ = K.attachedSubalphabetMap (B ∩ C) B
          Finset.inter_subset_left
          (K.attachedOfSkeletonVertex (B ∩ C) x) := by rw [hrx]
    _ = K.attachedOfSkeletonVertex B x :=
      K.attachedSubalphabetMap_ofSkeletonVertex
        (B ∩ C) B Finset.inter_subset_left x

/-- Two old skeleton vertices that become equal in the multi-coset
quotient are literally the same original skeleton vertex. -/
theorem multiCosetInclude_skeleton_eq_of_glue
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (x y : K.Vertex)
    (hglue :
      K.multiCosetInclude P hadm hgen hret B hBP
          (K.attachedOfSkeletonVertex B x) =
        K.multiCosetInclude P hadm hgen hret C hCP
          (K.attachedOfSkeletonVertex C y)) :
    x = y := by
  have hxy : K.attachedOfSkeletonVertex B x =
      K.attachedOfSkeletonVertex B y :=
    K.multiCosetInclude_reflects_skeleton_point
      P hadm hgen hret B C hBP hCP
      (K.attachedOfSkeletonVertex B x) y hglue
  exact K.attachedOfSkeletonVertex_injective B hxy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
