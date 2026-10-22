import PSTSEPPA.ABO.UpwardInductionProperTwoPieceSignedBridge
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Corrected ABO Theorem 4.7(iii): the two proper pieces have the SAME true core

The last accepted two-piece signed bridge lemma required two actual
G-multiCE paths to meet at literally the same original quotient
vertex, a dangerous assumption: equal ambient G coordinates
alone MUST NOT collapse different intrinsic old-component tags.

This module discharges that missing identification using the
PREVIOUSLY PROVED source 4.7(ii) ambient G-multiCE embedding.

Suppose:
* there is a real ambient signed Cayley(G) B-word p from the
  ambient coordinate of s₁ to that of s₂;
* there are TWO G-CE signed paths s₁ --p₁--> c₁ and
  c₂ --p₂--> s₂, using B∩C₁ and B∩C₂ respectively,
  with no prior assumption that c₁=c₂ as tagged quotient points;
* the B-augmented H stage certifies the actual equality
  [p]_H = [p₁p₂]_H;
* Q:G→H is stable at B and the already established full
  G-CE ambient map is INJECTIVE on original quotient vertices.

First the signed paths yield literal ambient G-coordinate
equations. k-stability converts the H word equality to G,
and group cancellation shows the TWO putative core vertices
have equal G coordinates. NOW (and only now!) the proved
embedding forces c₁=c₂ AS ACTUAL original tagged quotient
vertices. Consequently the two real signed G paths concatenate
to a true G multiCE B-bridge.

This removes a substantial artificial common-core hypothesis
from the proper n≥2 part of corrected Theorem 4.7(iii),
while still not inventing the source B-augmented stage's
actual signed lifts or word equality. Formal inverse
edge tokens are preserved, no absent old edges inserted,
and there are no new axioms or sorry.
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

/-- Every ACTUAL signed multiCE word path has the expected
ambient G-group endpoint equation. This uses the genuine
labelled ambient Cayley morphism, not an abstract or completed
substitute for a missing old edge. -/
theorem multiCosetAmbientValue_eq_mul_eval_of_follows
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated genΓ) (hret : Retractable genΓ)
    (s t : K.MultiCosetVertex P hadm hgen hret)
    (w : LabelWord ι)
    (hPath : (K.multiCosetEGraph P hadm hgen hret).Follows s w t) :
    K.multiCosetAmbientValue P hadm hgen hret t =
      K.multiCosetAmbientValue P hadm hgen hret s *
        PSTS.SignedWord.evalGroup genΓ w := by
  let F := K.multiCosetAmbientHom P hadm hgen hret
  have hMapped :
      (cayleyGraph genΓ).toEGraph.Follows
        (F.onVertex s) w (F.onVertex t) :=
    hPath.map F
  have hCanonical :
      (cayleyGraph genΓ).toEGraph.Follows
        (F.onVertex s) w
          ((cayleyGraph genΓ).followWord (F.onVertex s) w) :=
    (cayleyGraph genΓ).follows_followWord (F.onVertex s) w
  have hEndpoint :
      (cayleyGraph genΓ).followWord (F.onVertex s) w =
        F.onVertex t :=
    (cayleyGraph genΓ).toEGraph.follows_right_unique
      hCanonical hMapped
  change F.onVertex t =
    F.onVertex s * PSTS.SignedWord.evalGroup genΓ w
  calc
    F.onVertex t =
        (cayleyGraph genΓ).followWord (F.onVertex s) w :=
      hEndpoint.symm
    _ = F.onVertex s * PSTS.SignedWord.evalGroup genΓ w :=
      cayleyGraph.followWord_eq_mul_evalGroup genΓ (F.onVertex s) w

/-- Two PROPER signed constituent paths with endpoints c₁ and
c₂ that may have DIFFERENT original old tags necessarily have
the SAME actual G-quotient core once (i) H-stage B-word equality,
(ii) B-stability and (iii) genuine source CE embeddedness hold.

No equality of ambient group coordinates is used to identify
distinct component tags before the ambient embedding is invoked. -/
theorem upwardProperTwoPiece_actualCore_coalesces_of_embedding
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated genΓ) (hret : Retractable genΓ)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hStable : Q.StableAt B)
    (C₁ C₂ : Finset ι)
    (s₁ c₁ c₂ s₂ : K.MultiCosetVertex P hadm hgen hret)
    (p p₁ p₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hp₁ : LabelWord.Uses (B ∩ C₁) p₁)
    (hp₂ : LabelWord.Uses (B ∩ C₂) p₂)
    (hAmbient :
      K.multiCosetAmbientValue P hadm hgen hret s₂ =
        K.multiCosetAmbientValue P hadm hgen hret s₁ *
          PSTS.SignedWord.evalGroup genΓ p)
    (hH :
      PSTS.SignedWord.evalGroup genΔ p =
      PSTS.SignedWord.evalGroup genΔ (p₁ ++ p₂))
    (hPath₁ :
      (K.multiCosetEGraph P hadm hgen hret).Follows s₁ p₁ c₁)
    (hPath₂ :
      (K.multiCosetEGraph P hadm hgen hret).Follows c₂ p₂ s₂)
    (hEmbed :
      Function.Injective
        (K.multiCosetAmbientValue P hadm hgen hret)) :
    c₁ = c₂ := by
  have h₁ : LabelWord.Uses B p₁ :=
    LabelWord.Uses.mono_explicit (B ∩ C₁) B
      Finset.inter_subset_left p₁ hp₁
  have h₂ : LabelWord.Uses B p₂ :=
    LabelWord.Uses.mono_explicit (B ∩ C₂) B
      Finset.inter_subset_left p₂ hp₂
  have hBoth : LabelWord.Uses B (p₁ ++ p₂) :=
    (LabelWord.uses_append B p₁ p₂).mpr ⟨h₁, h₂⟩
  have hG :
      PSTS.SignedWord.evalGroup genΓ p =
      PSTS.SignedWord.evalGroup genΓ (p₁ ++ p₂) :=
    Q.evalGroup_eq_of_stableAt hStable hp hBoth hH
  have hEnd₁ :=
    K.multiCosetAmbientValue_eq_mul_eval_of_follows
      P hadm hgen hret s₁ c₁ p₁ hPath₁
  have hEnd₂ :=
    K.multiCosetAmbientValue_eq_mul_eval_of_follows
      P hadm hgen hret c₂ s₂ p₂ hPath₂
  apply hEmbed
  have hCancel :
      K.multiCosetAmbientValue P hadm hgen hret c₁ *
        PSTS.SignedWord.evalGroup genΓ p₂ =
      K.multiCosetAmbientValue P hadm hgen hret c₂ *
        PSTS.SignedWord.evalGroup genΓ p₂ := by
    calc
      K.multiCosetAmbientValue P hadm hgen hret c₁ *
          PSTS.SignedWord.evalGroup genΓ p₂ =
        (K.multiCosetAmbientValue P hadm hgen hret s₁ *
          PSTS.SignedWord.evalGroup genΓ p₁) *
          PSTS.SignedWord.evalGroup genΓ p₂ := by
            rw [hEnd₁]
      _ = K.multiCosetAmbientValue P hadm hgen hret s₁ *
          PSTS.SignedWord.evalGroup genΓ (p₁ ++ p₂) := by
            rw [PSTS.SignedWord.evalGroup_append]
            group
      _ = K.multiCosetAmbientValue P hadm hgen hret s₁ *
          PSTS.SignedWord.evalGroup genΓ p := by
            rw [← hG]
      _ = K.multiCosetAmbientValue P hadm hgen hret s₂ :=
        hAmbient.symm
      _ = K.multiCosetAmbientValue P hadm hgen hret c₂ *
          PSTS.SignedWord.evalGroup genΓ p₂ := hEnd₂
  exact mul_right_cancel hCancel

/-- Source UPWARD proper-cluster bridge reassembly with NO
unjustified assumption that the two constituent lifts already
share one tagged quotient core. True signed paths on the two
constituents, ambient original B-word and H B-augmentation
word equality, plus the previously proved source CE embedding,
SUFFICE to manufacture a real signed G B-bridge. -/
theorem upwardProperTwoPiece_signedBridge_of_embedding
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated genΓ) (hret : Retractable genΓ)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hStable : Q.StableAt B)
    (C₁ C₂ : Finset ι)
    (s₁ c₁ c₂ s₂ : K.MultiCosetVertex P hadm hgen hret)
    (p p₁ p₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hp₁ : LabelWord.Uses (B ∩ C₁) p₁)
    (hp₂ : LabelWord.Uses (B ∩ C₂) p₂)
    (hAmbient :
      K.multiCosetAmbientValue P hadm hgen hret s₂ =
        K.multiCosetAmbientValue P hadm hgen hret s₁ *
          PSTS.SignedWord.evalGroup genΓ p)
    (hH :
      PSTS.SignedWord.evalGroup genΔ p =
      PSTS.SignedWord.evalGroup genΔ (p₁ ++ p₂))
    (hPath₁ :
      (K.multiCosetEGraph P hadm hgen hret).Follows s₁ p₁ c₁)
    (hPath₂ :
      (K.multiCosetEGraph P hadm hgen hret).Follows c₂ p₂ s₂)
    (hEmbed :
      Function.Injective (K.multiCosetAmbientValue P hadm hgen hret)) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows s₁ w s₂ ∧
      PSTS.SignedWord.evalGroup genΓ w =
        PSTS.SignedWord.evalGroup genΓ p := by
  have hCore : c₁ = c₂ :=
    K.upwardProperTwoPiece_actualCore_coalesces_of_embedding
      P hadm hgen hret Q B hStable C₁ C₂
      s₁ c₁ c₂ s₂ p p₁ p₂ hp hp₁ hp₂
      hAmbient hH hPath₁ hPath₂ hEmbed
  subst c₂
  have h₁ : LabelWord.Uses B p₁ :=
    LabelWord.Uses.mono_explicit (B ∩ C₁) B
      Finset.inter_subset_left p₁ hp₁
  have h₂ : LabelWord.Uses B p₂ :=
    LabelWord.Uses.mono_explicit (B ∩ C₂) B
      Finset.inter_subset_left p₂ hp₂
  have hw : LabelWord.Uses B (p₁ ++ p₂) :=
    (LabelWord.uses_append B p₁ p₂).mpr ⟨h₁, h₂⟩
  have hG :
      PSTS.SignedWord.evalGroup genΓ p =
      PSTS.SignedWord.evalGroup genΓ (p₁ ++ p₂) :=
    Q.evalGroup_eq_of_stableAt hStable hp hw hH
  refine ⟨p₁ ++ p₂, hw, ?_, hG.symm⟩
  exact (K.multiCosetEGraph P hadm hgen hret).follows_append
    hPath₁ hPath₂

end CayleySubgraphSpec
end ABO
end PSTSEPPA
