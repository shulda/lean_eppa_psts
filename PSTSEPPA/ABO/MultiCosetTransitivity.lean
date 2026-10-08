import PSTSEPPA.ABO.MultiCosetOverlap
import PSTSEPPA.ABO.AdmissibleAttachedIntersectionLe

/-!
# Transitivity of exact multi-alphabet coset overlap (ABO 3.10, repair R5)

Let B₁, B₂, B₃ be alphabets, with the middle B₂ proper in the ambient
A. Two successive pairwise overlaps are witnessed by attached points
on B₁ ∩ B₂ and B₂ ∩ B₃. These have the same image in the tagged B₂-copy.

The non-strict common-refinement lemma yields a witness on
(B₁ ∩ B₂) ∩ (B₂ ∩ B₃). Mapping it to B₁ ∩ B₃ supplies the overlap
between the endpoints, with all component tags and ambient values
preserved.

This proof does not use a strict-subalphabet lemma for degenerate cases:
B₁ ∩ B₂ or B₂ ∩ B₃ may equal B₂, and the constituent alphabets may
coincide. It provides the missing transitivity of the literal quotient
relation (3.10), not merely its transitive closure.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Source-facing transitivity of the exact intersection-support relation,
including equal, nested and empty intersection alphabets. -/
theorem shareIntersectionSupport_trans
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B₁ B₂ B₃ : Finset ι)
    (hB₂ : B₂ ⊂ A)
    {p : K.AttachedCosetVertex B₁}
    {q : K.AttachedCosetVertex B₂}
    {t : K.AttachedCosetVertex B₃}
    (hpq : K.ShareIntersectionSupport B₁ B₂ p q)
    (hqt : K.ShareIntersectionSupport B₂ B₃ q t) :
    K.ShareIntersectionSupport B₁ B₃ p t := by
  rcases hpq with ⟨s, hsp, hsq⟩
  rcases hqt with ⟨v, hvq, hvt⟩
  have hparent :
      K.attachedSubalphabetMap (B₁ ∩ B₂) B₂
          Finset.inter_subset_right s =
        K.attachedSubalphabetMap (B₂ ∩ B₃) B₂
          Finset.inter_subset_left v :=
    hsq.trans hvq.symm
  obtain ⟨u, huS, huV⟩ :=
    K.attachedSubalphabetMap_common_refinement_le
      hadm hgen hret
      B₂ (B₁ ∩ B₂) (B₂ ∩ B₃) hB₂
      Finset.inter_subset_right Finset.inter_subset_left
      s v hparent
  let E : Finset ι := (B₁ ∩ B₂) ∩ (B₂ ∩ B₃)
  have hE : E ⊆ B₁ ∩ B₃ := by
    intro i hi
    rcases Finset.mem_inter.mp hi with ⟨h12, h23⟩
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp h12).1,
        (Finset.mem_inter.mp h23).2⟩
  let r : K.AttachedCosetVertex (B₁ ∩ B₃) :=
    K.attachedSubalphabetMap E (B₁ ∩ B₃) hE u
  refine ⟨r, ?_, ?_⟩
  · calc
      K.attachedSubalphabetMap (B₁ ∩ B₃) B₁
          Finset.inter_subset_left r =
        K.attachedSubalphabetMap E B₁
          (hE.trans Finset.inter_subset_left) u :=
        K.attachedSubalphabetMap_comp
          E (B₁ ∩ B₃) B₁ hE Finset.inter_subset_left u
      _ = K.attachedSubalphabetMap E B₁
          ((Finset.inter_subset_left : E ⊆ B₁ ∩ B₂).trans
            Finset.inter_subset_left) u := rfl
      _ = K.attachedSubalphabetMap (B₁ ∩ B₂) B₁
            Finset.inter_subset_left
            (K.attachedSubalphabetMap E (B₁ ∩ B₂)
              Finset.inter_subset_left u) :=
        (K.attachedSubalphabetMap_comp
          E (B₁ ∩ B₂) B₁
          Finset.inter_subset_left Finset.inter_subset_left u).symm
      _ = K.attachedSubalphabetMap (B₁ ∩ B₂) B₁
            Finset.inter_subset_left s :=
        congrArg _ huS
      _ = p := hsp
  · calc
      K.attachedSubalphabetMap (B₁ ∩ B₃) B₃
          Finset.inter_subset_right r =
        K.attachedSubalphabetMap E B₃
          (hE.trans Finset.inter_subset_right) u :=
        K.attachedSubalphabetMap_comp
          E (B₁ ∩ B₃) B₃ hE Finset.inter_subset_right u
      _ = K.attachedSubalphabetMap E B₃
          ((Finset.inter_subset_right : E ⊆ B₂ ∩ B₃).trans
            Finset.inter_subset_right) u := rfl
      _ = K.attachedSubalphabetMap (B₂ ∩ B₃) B₃
            Finset.inter_subset_right
            (K.attachedSubalphabetMap E (B₂ ∩ B₃)
              Finset.inter_subset_right u) :=
        (K.attachedSubalphabetMap_comp
          E (B₂ ∩ B₃) B₃
          Finset.inter_subset_right Finset.inter_subset_right u).symm
      _ = K.attachedSubalphabetMap (B₂ ∩ B₃) B₃
            Finset.inter_subset_right v :=
        congrArg _ huV
      _ = t := hvt

end CayleySubgraphSpec
end ABO
end PSTSEPPA
