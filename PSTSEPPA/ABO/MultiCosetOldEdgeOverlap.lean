import PSTSEPPA.ABO.MultiCosetRawEdges
import PSTSEPPA.ABO.SingleCosetSkeletonEmbedding

/-!
# Two old skeleton edges cannot acquire conflicting glued targets

Each single-alphabet coset extension retains every old skeleton edge
whose signed generator is outside the completed alphabet.

If two such old edge tokens in different alphabet summands have equal
sources in the checked vertex quotient and equal signed labels, their
underlying original skeleton edges are literally equal: their group
sources agree by the ambient projection, and the original Cayley
skeleton is deterministic. Their targets therefore agree in the
vertex quotient by alphabet-independence of the old skeleton copy.

Unlike the mixed and completed cases, this argument does not need
admissibility beyond the hypotheses already used to construct the
multi-alphabet vertex quotient.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Two original skeleton edges retained outside two completed
alphabets have the same glued targets whenever their glued sources
and signed labels coincide. -/
theorem multiCosetOldEdge_targets_eq
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (e : K.OutsideEdge B) (f : K.OutsideEdge C)
    (hsource :
      K.multiCosetInclude P hadm hgen hret B hBP
          (K.attachedOfSkeletonVertex B ((K.toEGraph).source e.1)) =
        K.multiCosetInclude P hadm hgen hret C hCP
          (K.attachedOfSkeletonVertex C ((K.toEGraph).source f.1)))
    (hlabel : e.1.1.2 = f.1.1.2) :
    K.multiCosetInclude P hadm hgen hret B hBP
        ((K.singleCosetEGraph B).target (Sum.inl e)) =
      K.multiCosetInclude P hadm hgen hret C hCP
        ((K.singleCosetEGraph C).target (Sum.inl f)) := by
  have hval :
      e.1.1.1 = f.1.1.1 := by
    have h := congrArg (K.multiCosetAmbientValue P hadm hgen hret) hsource
    simpa only [K.multiCosetAmbientValue_include,
      K.attachedValue_ofSkeletonVertex] using h
  have holdsource :
      (K.toEGraph).source e.1 = (K.toEGraph).source f.1 :=
    Subtype.ext hval
  have holdlabel :
      (K.toEGraph).label e.1 = (K.toEGraph).label f.1 :=
    hlabel
  have heq : e.1 = f.1 :=
    (K.toEGraph).deterministic holdsource holdlabel
  change
    K.multiCosetInclude P hadm hgen hret B hBP
        (K.attachedOfSkeletonVertex B ((K.toEGraph).target e.1)) =
      K.multiCosetInclude P hadm hgen hret C hCP
        (K.attachedOfSkeletonVertex C ((K.toEGraph).target f.1))
  rw [heq]
  exact K.multiCosetInclude_skeleton_independent
    P hadm hgen hret B C hBP hCP ((K.toEGraph).target f.1)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
