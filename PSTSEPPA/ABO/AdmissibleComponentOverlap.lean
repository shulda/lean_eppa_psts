import PSTSEPPA.ABO.CayleySubgraphAdmissibility
import PSTSEPPA.ABO.ComponentIndexedCosets

/-!
# Admissibility reflects ambient coset overlaps to intrinsic components

ABO Definition 3.16 excludes unintended identifications when two
lower-alphabet cosets meet inside a common higher-alphabet component.
The central consequence for the gluing construction is that if two
C-cosets meet and their basepoints lie in the same intrinsic B-component,
where C ⊂ B ⊂ A, then the basepoints already belong to one intrinsic
C-component.

This is needed for the injections of lower-rank coset extensions into
higher-rank ones (ABO (3.9)) and is valid for equal lower alphabets
and even C = ∅.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact positive form of admissibility: an ambient coset overlap for two
subcomponents produces an actual common skeleton vertex. -/
theorem admissible_intrinsic_inter_nonempty
    (hadm : K.AdmissibleForCosetExtension)
    (B B₁ B₂ : Finset ι)
    (hBA : B ⊂ A)
    (hB₁ : B₁ ⊂ B) (hB₂ : B₂ ⊂ B)
    (x y : K.Vertex)
    (hxy : K.SubalphabetReachable B x y)
    (hcoset :
      (generatedLeftCoset gen B₁ x.1 ∩
        generatedLeftCoset gen B₂ y.1).Nonempty) :
    (K.SubalphabetComponent B₁ x ∩
      K.SubalphabetComponent B₂ y).Nonempty := by
  obtain ⟨z, hxz, hyz⟩ :=
    hadm B B₁ B₂ hBA hB₁ hB₂ x y hxy hcoset
  exact ⟨z, hxz, hyz⟩

/-- If two C-cosets in the same B-component meet, the two C-component
indices agree. This is the equal-lower-alphabet instance of admissibility;
it does not require any distinctness of the two basepoints. -/
theorem admissible_componentClass_eq_of_cosets_meet
    (hadm : K.AdmissibleForCosetExtension)
    (B C : Finset ι)
    (hBA : B ⊂ A) (hCB : C ⊂ B)
    (x y : K.Vertex)
    (hxy : K.SubalphabetReachable B x y)
    (hcoset :
      (generatedLeftCoset gen C x.1 ∩
        generatedLeftCoset gen C y.1).Nonempty) :
    K.componentClass C x = K.componentClass C y := by
  rcases hadm B C C hBA hCB hCB x y hxy hcoset with
    ⟨z, hxz, hyz⟩
  have hxyC : K.SubalphabetReachable C x y :=
    K.subalphabetReachable_trans C hxz
      (K.subalphabetReachable_symm C hyz)
  exact (K.componentClass_eq_iff C x y).2 hxyC

/-- In particular, equal ambient C-cosets based in one B-component
must come from the same intrinsic C-component. -/
theorem admissible_componentClass_eq_of_cosets_equal
    (hadm : K.AdmissibleForCosetExtension)
    (B C : Finset ι)
    (hBA : B ⊂ A) (hCB : C ⊂ B)
    (x y : K.Vertex)
    (hxy : K.SubalphabetReachable B x y)
    (hcoset :
      generatedLeftCoset gen C x.1 =
        generatedLeftCoset gen C y.1) :
    K.componentClass C x = K.componentClass C y := by
  apply K.admissible_componentClass_eq_of_cosets_meet
    hadm B C hBA hCB x y hxy
  refine ⟨x.1, self_mem_generatedLeftCoset gen C x.1, ?_⟩
  rw [← hcoset]
  exact self_mem_generatedLeftCoset gen C x.1

end CayleySubgraphSpec

end ABO
end PSTSEPPA
