import PSTSEPPA.ABO.MultiCosetRawEdges
import PSTSEPPA.ABO.AttachedCosetNaturality

/-!
# Matching targets of completed coset edges across alphabets

Suppose the sources of a completed B-edge and a completed C-edge are
identified in the multi-alphabet coset-extension vertex quotient, and
the signed edge labels are equal. Then the targets are also identified.

The proof takes the actual (B ∩ C)-tagged witness to source overlap,
follows the common signed letter in its own complete (B ∩ C)-coset, and
uses naturality of coset steps under both alphabet enlargements. Thus
the new target overlap has an *explicit* (B ∩ C)-tagged witness.

This is the fully-completed/fully-completed case of the
source-and-label target-congruence gate for directed edges; the mixed
completed/old-skeleton and old/old cases remain separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Equal glued sources and signed labels of two completed coset
edges force equal glued targets, with an explicit lower-alphabet
coset witness. -/
theorem multiCosetCompletedEdge_targets_eq
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (e : K.CosetEdge B) (f : K.CosetEdge C)
    (hs :
      K.multiCosetInclude P hadm hgen hret B hBP e.1 =
        K.multiCosetInclude P hadm hgen hret C hCP f.1)
    (hl : e.2.1 = f.2.1) :
    K.multiCosetInclude P hadm hgen hret B hBP
        (K.cosetStep B e.1 e.2) =
      K.multiCosetInclude P hadm hgen hret C hCP
        (K.cosetStep C f.1 f.2) := by
  have hshare : K.ShareIntersectionSupport B C e.1 f.1 := by
    have h := Quotient.exact hs
    change K.ShareIntersectionSupport B C e.1 f.1 at h
    exact h
  rcases hshare with ⟨r, hrB, hrC⟩
  have hlabelC : signedBase e.2.1 ∈ C := by
    rw [hl]
    exact f.2.2
  let s : {s : SignedLabel ι // signedBase s ∈ B ∩ C} :=
    ⟨e.2.1, Finset.mem_inter.mpr ⟨e.2.2, hlabelC⟩⟩
  let r' : K.AttachedCosetVertex (B ∩ C) :=
    K.cosetStep (B ∩ C) r s
  have hrB' :
      K.attachedSubalphabetMap (B ∩ C) B
          Finset.inter_subset_left r' =
        K.cosetStep B e.1 e.2 := by
    calc
      K.attachedSubalphabetMap (B ∩ C) B
          Finset.inter_subset_left r' =
        K.cosetStep B
          (K.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left r)
          ⟨s.1, Finset.inter_subset_left s.2⟩ :=
        K.attachedSubalphabetMap_cosetStep
          (B ∩ C) B Finset.inter_subset_left r s
      _ = K.cosetStep B e.1 e.2 := by
        rw [hrB]
  have hrC' :
      K.attachedSubalphabetMap (B ∩ C) C
          Finset.inter_subset_right r' =
        K.cosetStep C f.1 f.2 := by
    calc
      K.attachedSubalphabetMap (B ∩ C) C
          Finset.inter_subset_right r' =
        K.cosetStep C
          (K.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right r)
          ⟨s.1, Finset.inter_subset_right s.2⟩ :=
        K.attachedSubalphabetMap_cosetStep
          (B ∩ C) C Finset.inter_subset_right r s
      _ = K.cosetStep C f.1 f.2 := by
        rw [hrC]
        apply congrArg (K.cosetStep C f.1)
        exact Subtype.ext hl
  apply Quotient.sound
  change K.ShareIntersectionSupport B C
    (K.cosetStep B e.1 e.2) (K.cosetStep C f.1 f.2)
  exact ⟨r', hrB', hrC'⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
