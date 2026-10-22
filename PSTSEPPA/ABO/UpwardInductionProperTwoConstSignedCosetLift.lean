import PSTSEPPA.ABO.SignedGraphPathReverse
import PSTSEPPA.ABO.UpwardInductionProperTwoPieceCoreFromEmbedding
import PSTSEPPA.ABO.SingleCosetConnectivity

/-!
# ABO 4.7(iii): construct the TWO genuine G constituent paths automatically

The previously certified proper-cluster core-coalescence theorem
removed the spurious assumption that the two putative G cores
already agree as ORIGINAL component-tagged quotient points.
It still assumed two real G signed constituent paths had been
supplied independently.

But for a selected full Cᵢ-coset these paths require NO extra
stage-cover assumption: every signed word using Cᵢ can be
followed in that ACTUAL G attached full Cᵢ-coset, including
positive/inverse labels and existing geometric loops.

Given two TRUE selected C₁,C₂ constituent anchor points
a₁ and a₂, B∩Cᵢ words w₁,w₂ from each anchor towards the
corresponding H common core, an original ambient B-word p
connecting the G coordinates of a₁ and a₂, and the H-side
B-augmentation equality [p]_H=[w₁ inv(w₂)]_H, we:

  1. construct actual G paths aᵢ --wᵢ--> cᵢ inside their
     ORIGINAL intrinsic component-tagged full Cᵢ-cosets;
  2. reverse the SECOND actual path using FORMAL inverse
     original signed edge tokens, without adding an edge;
  3. use k-stability and the PREVIOUSLY PROVED true G multiCE
     ambient EMBEDDING to deduce c₁=c₂ as original quotient
     vertices (not just equal G coordinates);
  4. concatenate to an ACTUAL signed G multiCE B-path
     from the first anchor to the second, of exactly the
     same G-word value as p.

Thus the remaining source input for this proper n≥2
bridge subcase consists ONLY of real H-supported words
and their equality in the B-AUGMENTED H-stage; there is
NO artificial hypothesis about any G common core,
nor pre-supplied G piece paths. The hard remaining
source work is connecting actual H-cluster geometry and
augmented stage covers to those H-word certificates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec genΓ A)

/-- Full source PROPER n≥2 path construction from true
B∩Cᵢ words, original component-tagged constituent
anchors and actual group-word equality in H.

Only the original H B-augmentation equality remains
as a source-specific geometric certificate; all G
constituent paths and the common G core are PRODUCED
by the existing signed full-coset and genuine embedding APIs. -/
theorem upwardProperTwoConstituents_signedBridge_of_HWordEquality
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated genΓ) (hret : Retractable genΓ)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hStable : Q.StableAt B)
    (C₁ C₂ : Finset ι)
    (hC₁ : C₁ ∈ P.alphabets)
    (hC₂ : C₂ ∈ P.alphabets)
    (a₁ : K.AttachedCosetVertex C₁)
    (a₂ : K.AttachedCosetVertex C₂)
    (p w₁ w₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hw₁ : LabelWord.Uses (B ∩ C₁) w₁)
    (hw₂ : LabelWord.Uses (B ∩ C₂) w₂)
    (hAmbient :
      a₂.2.1 = a₁.2.1 * PSTS.SignedWord.evalGroup genΓ p)
    (hH :
      PSTS.SignedWord.evalGroup genΔ p =
        PSTS.SignedWord.evalGroup genΔ
          (w₁ ++ PSTS.SignedWord.inv w₂))
    (hEmbed :
      Function.Injective
        (K.multiCosetAmbientValue P hadm hgen hret)) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C₁ hC₁ a₁)
        w
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ a₂) ∧
      PSTS.SignedWord.evalGroup genΓ w =
        PSTS.SignedWord.evalGroup genΓ p := by
  let G := K.multiCosetEGraph P hadm hgen hret
  have hW₁ : LabelWord.Uses C₁ w₁ :=
    LabelWord.Uses.mono_explicit
      (B ∩ C₁) C₁ Finset.inter_subset_right w₁ hw₁
  have hW₂ : LabelWord.Uses C₂ w₂ :=
    LabelWord.Uses.mono_explicit
      (B ∩ C₂) C₂ Finset.inter_subset_right w₂ hw₂
  obtain ⟨c₁, hOld₁, _hTag₁, _hVal₁⟩ :=
    K.singleCosetEGraph_follows_word C₁ a₁ hW₁
  obtain ⟨c₂, hOld₂, _hTag₂, _hVal₂⟩ :=
    K.singleCosetEGraph_follows_word C₂ a₂ hW₂
  have hPath₁ :
      G.Follows
        (K.multiCosetInclude P hadm hgen hret C₁ hC₁ a₁)
        w₁
        (K.multiCosetInclude P hadm hgen hret C₁ hC₁ c₁) := by
    exact hOld₁.map
      (K.singleCosetToMultiHom P hadm hgen hret C₁ hC₁)
  have hPath₂Forward :
      G.Follows
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ a₂)
        w₂
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ c₂) := by
    exact hOld₂.map
      (K.singleCosetToMultiHom P hadm hgen hret C₂ hC₂)
  have hPath₂ :
      G.Follows
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ c₂)
        (PSTS.SignedWord.inv w₂)
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ a₂) :=
    G.follows_signedWord_reverse hPath₂Forward
  have hW₂inv :
      LabelWord.Uses (B ∩ C₂) (PSTS.SignedWord.inv w₂) :=
    hw₂.inv
  have hAmbientCE :
      K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ a₂) =
      K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetInclude P hadm hgen hret C₁ hC₁ a₁) *
          PSTS.SignedWord.evalGroup genΓ p := by
    simpa only [K.multiCosetAmbientValue_include] using hAmbient
  exact K.upwardProperTwoPiece_signedBridge_of_embedding
    P hadm hgen hret Q B hStable C₁ C₂
    (K.multiCosetInclude P hadm hgen hret C₁ hC₁ a₁)
    (K.multiCosetInclude P hadm hgen hret C₁ hC₁ c₁)
    (K.multiCosetInclude P hadm hgen hret C₂ hC₂ c₂)
    (K.multiCosetInclude P hadm hgen hret C₂ hC₂ a₂)
    p w₁ (PSTS.SignedWord.inv w₂)
    hp hw₁ hW₂inv
    hAmbientCE hH hPath₁ hPath₂ hEmbed

end CayleySubgraphSpec
end ABO
end PSTSEPPA
