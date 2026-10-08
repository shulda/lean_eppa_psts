import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.AdmissibleAttachedIntersectionLe

/-!
# Local ambient injectivity within an intrinsic B-component

This is the key embedding mechanism in ABO Lemma 3.20.

The canonical projection CE(G,K;P) → G[A] is not globally
injective. However, if two points belong to lower-alphabet coset
constituents C,D ⊆ B whose intrinsic component indices map to
the *same* B-component of the original skeleton, then equality of
ambient group values forces equality already in the CE vertex quotient.

The proof uses exactly admissibility within the containing
B-component, proper B⊂A, and retractable subgroup intersections.
It never claims the same injectivity for different B-component tags.

The result also provides edge agreement whenever the source
criterion applies and the signed labels coincide. This is an
algebraic vertex/edge core of Lemma 3.20; realizing the restricted
B-component as a separate lower-rank coset-extension graph remains
a subsequent step.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Two lower-alphabet tagged coset points whose B-component indices
and ambient coordinates coincide must have an actual common
(C∩D)-coset witness, for any C,D⊆B⊂A. -/
theorem attached_lower_cosets_share_of_same_parent
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C D : Finset ι)
    (hBA : B ⊂ A) (hCB : C ⊆ B) (hDB : D ⊆ B)
    (p : K.AttachedCosetVertex C)
    (q : K.AttachedCosetVertex D)
    (hparent :
      K.componentIndexMap C B hCB p.1 =
        K.componentIndexMap D B hDB q.1)
    (hvalue : p.2.1 = q.2.1) :
    K.ShareIntersectionSupport C D p q := by
  have heq :
      K.attachedSubalphabetMap C B hCB p =
        K.attachedSubalphabetMap D B hDB q :=
    K.attachedValue_injective_of_same_index B hparent hvalue
  obtain ⟨r, hrp, hrq⟩ :=
    K.attachedSubalphabetMap_common_refinement_le
      hadm hgen hret B C D hBA hCB hDB p q heq
  exact ⟨r, hrp, hrq⟩

/-- The actual multi-coset quotient identifies such lower-alphabet
vertices: ambient equality is sufficient only WITHIN a common
intrinsic parent B-component. -/
theorem multiCosetInclude_eq_of_same_parent_and_value
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C D : Finset ι)
    (hBA : B ⊂ A)
    (hCP : C ∈ P.alphabets) (hDP : D ∈ P.alphabets)
    (hCB : C ⊆ B) (hDB : D ⊆ B)
    (p : K.AttachedCosetVertex C)
    (q : K.AttachedCosetVertex D)
    (hparent :
      K.componentIndexMap C B hCB p.1 =
        K.componentIndexMap D B hDB q.1)
    (hvalue : p.2.1 = q.2.1) :
    K.multiCosetInclude P hadm hgen hret C hCP p =
      K.multiCosetInclude P hadm hgen hret D hDP q := by
  apply Quotient.sound
  change K.ShareIntersectionSupport C D p q
  exact K.attached_lower_cosets_share_of_same_parent
    hadm hgen hret B C D hBA hCB hDB p q hparent hvalue

/-- The corresponding signed directed edges agree whenever their
sources meet the same-parent injectivity criterion and their
oriented labels coincide. This uses determinism of the *glued*
E-graph, not injectivity of its ambient Cayley projection. -/
theorem multiCosetEdgeInclude_eq_of_same_parent_and_label
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C D : Finset ι) (hBA : B ⊂ A)
    (hCP : C ∈ P.alphabets) (hDP : D ∈ P.alphabets)
    (hCB : C ⊆ B) (hDB : D ⊆ B)
    (e : K.SingleCosetEdge C)
    (f : K.SingleCosetEdge D)
    (hparent :
      K.componentIndexMap C B hCB
          ((K.singleCosetEGraph C).source e).1 =
        K.componentIndexMap D B hDB
          ((K.singleCosetEGraph D).source f).1)
    (hvalue :
      ((K.singleCosetEGraph C).source e).2.1 =
        ((K.singleCosetEGraph D).source f).2.1)
    (hlabel :
      (K.singleCosetEGraph C).label e =
        (K.singleCosetEGraph D).label f) :
    K.multiCosetEdgeInclude P hadm hgen hret C hCP e =
      K.multiCosetEdgeInclude P hadm hgen hret D hDP f := by
  apply (K.multiCosetEGraph P hadm hgen hret).deterministic
  · exact K.multiCosetInclude_eq_of_same_parent_and_value
      P hadm hgen hret B C D hBA hCP hDP hCB hDB
      ((K.singleCosetEGraph C).source e)
      ((K.singleCosetEGraph D).source f)
      hparent hvalue
  · exact hlabel

end CayleySubgraphSpec
end ABO
end PSTSEPPA
