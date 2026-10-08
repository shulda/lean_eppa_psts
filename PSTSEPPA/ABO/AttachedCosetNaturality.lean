import PSTSEPPA.ABO.MultiCosetOverlap
import PSTSEPPA.ABO.AdmissibleAttachedEmbedding
import PSTSEPPA.ABO.SingleCosetExtension

/-!
# Non-strict injectivity and naturality for attached coset copies

The source R5 repairs require allowing D = B in maps from smaller
component-indexed coset copies into B-copies. Under admissibility the
enlargement D → B is injective for all D ⊆ B ⊂ A, not just D ⊂ B.

The completed B-action is natural under these embeddings. An attached
point lying over a literal skeleton point remains the *same* skeleton
point when reflected into a smaller alphabet (no accidental tag change).
These lemmas support the mixed inside/outside-letter case in the
multi-alphabet directed-edge gluing proof.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Under admissibility, every D ⊆ B ⊂ A enlargement map on
component-indexed coset copies is injective, including D = B. -/
theorem attachedSubalphabetMap_injective_of_admissible_le
    (hadm : K.AdmissibleForCosetExtension)
    (B D : Finset ι)
    (hBA : B ⊂ A) (hDB : D ⊆ B) :
    Function.Injective (K.attachedSubalphabetMap D B hDB) := by
  by_cases hEq : D = B
  · subst D
    intro p q hpq
    simpa only [K.attachedSubalphabetMap_self] using hpq
  · have hproper : D ⊂ B := by
      refine ⟨hDB, ?_⟩
      intro hBD
      exact hEq (Finset.Subset.antisymm hDB hBD)
    exact K.attachedSubalphabetMap_injective_of_admissible
      hadm B D hBA hproper hDB

/-- A point of the D-copy that becomes the literal embedded skeleton
point x inside the B-copy must already be x inside its original D-copy. -/
theorem attachedSubalphabetMap_reflects_skeleton
    (hadm : K.AdmissibleForCosetExtension)
    (B D : Finset ι)
    (hBA : B ⊂ A) (hDB : D ⊆ B)
    (p : K.AttachedCosetVertex D) (x : K.Vertex)
    (hp :
      K.attachedSubalphabetMap D B hDB p =
        K.attachedOfSkeletonVertex B x) :
    p = K.attachedOfSkeletonVertex D x := by
  apply K.attachedSubalphabetMap_injective_of_admissible_le
    hadm B D hBA hDB
  rw [K.attachedSubalphabetMap_ofSkeletonVertex]
  exact hp

/-- Completing a signed D-edge and then enlarging from D to B gives
the same point as enlarging first and taking the corresponding B-edge.
This holds even for a trivial generator or D = B. -/
theorem attachedSubalphabetMap_cosetStep
    (D B : Finset ι) (hDB : D ⊆ B)
    (p : K.AttachedCosetVertex D)
    (s : {s : SignedLabel ι // signedBase s ∈ D}) :
    K.attachedSubalphabetMap D B hDB
        (K.cosetStep D p s) =
      K.cosetStep B
        (K.attachedSubalphabetMap D B hDB p)
        ⟨s.1, hDB s.2⟩ := by
  apply K.attachedValue_injective_of_same_index B
  · rfl
  · rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
