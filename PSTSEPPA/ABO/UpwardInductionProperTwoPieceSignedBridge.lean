import PSTSEPPA.ABO.Stability
import PSTSEPPA.ABO.KRetractableCosetIntersections
import PSTSEPPA.ABO.MultiCosetEGraph

/-!
# Corrected ABO Theorem 4.7(iii): proper signed B-cluster TWO-piece bridge step

In the published UPWARD bridge-freeness proof, consider the
off-skeleton proper B-cluster alternative. If the two true signed
B-component endpoints lie in two different constituent
(B∩C_i)-cosets, a genuine common core gives TWO actual signed
piece paths with labels p₁ over B∩C₁ and p₂ over B∩C₂.

The source's G-Cayley cover of the B-augmentation of the H-stage
then proves in the H-group that the original ambient B-word
p has the same H-value as p₁p₂. Since B⊊A and |B|≤k, a
k-stable G→H quotient reflects exactly this equality to G.

This file formalizes the LAST proof step with the original
positive/inverse signed word conventions and ACTUAL signed
old+fresh quotient graph paths. In particular:

- neither the actual common-core G quotient vertex nor either
  genuine G constituent path is assumed to exist from
  ambient group-coordinate equality: they are explicit
  signed path witnesses to be constructed by the remaining
  geometric stage-cover lemma;
- equal H-word values are likewise an explicit consequence
  to be obtained from the real B-augmented H-stage;
- once those source data are available, their actual G
  concatenation is a REAL signed B-path between the original
  G multiCE endpoints and has the SAME G-group value as p.

This is the OFF-SKELETON ≥2-constituent algebraic/graph
reassembly gate in corrected Theorem 4.7(iii), complementary
to the separate skeleton-meeting FULL B-coset R8 path
lifting lemma. It is not the entire bridge-free theorem.
No globally generatedness of Δ, fake old edge, or extra axioms/sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- Corrected UPWARD 4.7(iii), genuine PROPER two-piece signed
bridge reassembly: if two real G-quotient paths of types
B∩C₁ and B∩C₂ meet at the SAME actual source core and the
original B-word p agrees in H-value with their concatenation,
k-stability yields a REAL source G signed B-path of the
same G-group value as p. Formal inverse letters and
true directed signed edges are retained verbatim. -/
theorem upwardProperTwoPiece_actualSignedBridge
    (K : CayleySubgraphSpec genΓ A)
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated genΓ) (hret : Retractable genΓ)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (k : ℕ) (hk : Q.KStable k)
    (B : Finset ι) (hBk : B.card ≤ k)
    (C₁ C₂ : Finset ι)
    (s₁ core s₂ : K.MultiCosetVertex P hadm hgen hret)
    (p p₁ p₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hp₁ : LabelWord.Uses (B ∩ C₁) p₁)
    (hp₂ : LabelWord.Uses (B ∩ C₂) p₂)
    (hH : PSTS.SignedWord.evalGroup genΔ p =
      PSTS.SignedWord.evalGroup genΔ (p₁ ++ p₂))
    (hPath₁ :
      (K.multiCosetEGraph P hadm hgen hret).Follows s₁ p₁ core)
    (hPath₂ :
      (K.multiCosetEGraph P hadm hgen hret).Follows core p₂ s₂) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows s₁ w s₂ ∧
      PSTS.SignedWord.evalGroup genΓ w =
        PSTS.SignedWord.evalGroup genΓ p := by
  have h₁ : LabelWord.Uses B p₁ :=
    LabelWord.Uses.mono_explicit (B ∩ C₁) B
      Finset.inter_subset_left p₁ hp₁
  have h₂ : LabelWord.Uses B p₂ :=
    LabelWord.Uses.mono_explicit (B ∩ C₂) B
      Finset.inter_subset_left p₂ hp₂
  have hw : LabelWord.Uses B (p₁ ++ p₂) :=
    (LabelWord.uses_append B p₁ p₂).mpr ⟨h₁,h₂⟩
  have hG : PSTS.SignedWord.evalGroup genΓ p =
      PSTS.SignedWord.evalGroup genΓ (p₁ ++ p₂) :=
    Q.evalGroup_eq_of_stableAt (hk B hBk) hp hw hH
  refine ⟨p₁ ++ p₂, hw, ?_, hG.symm⟩
  exact (K.multiCosetEGraph P hadm hgen hret).follows_append hPath₁ hPath₂

end CayleySubgraphSpec
end ABO
end PSTSEPPA
