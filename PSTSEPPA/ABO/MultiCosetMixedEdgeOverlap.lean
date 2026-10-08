import PSTSEPPA.ABO.MultiCosetSkeletonRigidity
import PSTSEPPA.ABO.SingleCosetSkeletonEmbedding
import PSTSEPPA.ABO.MultiCosetRawEdges

/-!
# Mixed original/completed edge target congruence

Suppose a retained original skeleton edge is outside alphabet B, while
the same signed generator occurs as a completed C-coset edge.

If the two edge sources coincide in the glued vertex quotient, the
completed edge's source is *literally the original skeleton vertex*
inside the C-copy, by skeleton-point rigidity. The completed C-step
therefore reaches the embedded target of the original skeleton edge.

Hence the two edge targets also coincide in the glued vertex quotient.
This handles the delicate case where exactly one side is a full
coset edge; the opposite orientation is its symmetric counterpart.

The argument uses actual component tags and the original skeleton
edge. It never deduces gluing from ambient group-coordinate equality.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An old skeleton edge in the B-extension and a completed C-coset
edge of the same signed label have equal glued targets whenever their
glued sources coincide. -/
theorem multiCosetOldCompletedEdge_targets_eq
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (e : K.OutsideEdge B) (f : K.CosetEdge C)
    (hsource :
      K.multiCosetInclude P hadm hgen hret B hBP
          (K.attachedOfSkeletonVertex B ((K.toEGraph).source e.1)) =
        K.multiCosetInclude P hadm hgen hret C hCP f.1)
    (hlabel : e.1.1.2 = f.2.1) :
    K.multiCosetInclude P hadm hgen hret B hBP
        ((K.singleCosetEGraph B).target (Sum.inl e)) =
      K.multiCosetInclude P hadm hgen hret C hCP
        (K.cosetStep C f.1 f.2) := by
  have hfSource :
      f.1 = K.attachedOfSkeletonVertex C ((K.toEGraph).source e.1) :=
    K.multiCosetInclude_reflects_skeleton_point
      P hadm hgen hret C B hCP hBP
      f.1 ((K.toEGraph).source e.1) hsource.symm
  have heC : signedBase e.1.1.2 ∈ C := by
    rw [hlabel]
    exact f.2.2
  have hsigned :
      (⟨e.1.1.2, heC⟩ : {s : SignedLabel ι // signedBase s ∈ C}) =
        f.2 :=
    Subtype.ext hlabel
  have hfTarget :
      K.cosetStep C f.1 f.2 =
        K.attachedOfSkeletonVertex C ((K.toEGraph).target e.1) := by
    rw [hfSource, ← hsigned]
    exact K.cosetStep_attached_source_eq_target C e.1 heC
  change
    K.multiCosetInclude P hadm hgen hret B hBP
        (K.attachedOfSkeletonVertex B ((K.toEGraph).target e.1)) =
      K.multiCosetInclude P hadm hgen hret C hCP
        (K.cosetStep C f.1 f.2)
  calc
    K.multiCosetInclude P hadm hgen hret B hBP
        (K.attachedOfSkeletonVertex B ((K.toEGraph).target e.1)) =
      K.multiCosetInclude P hadm hgen hret C hCP
        (K.attachedOfSkeletonVertex C ((K.toEGraph).target e.1)) :=
      K.multiCosetInclude_skeleton_independent
        P hadm hgen hret B C hBP hCP ((K.toEGraph).target e.1)
    _ = K.multiCosetInclude P hadm hgen hret C hCP
        (K.cosetStep C f.1 f.2) := by rw [hfTarget]

end CayleySubgraphSpec
end ABO
end PSTSEPPA
