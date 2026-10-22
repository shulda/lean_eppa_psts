import PSTSEPPA.ABO.UpwardInductionSignedWordCertifiedEmbedding
import PSTSEPPA.ABO.CompleteStageWordCongruenceCayleyCover

/-!
# Corrected ABO Theorem 4.7(ii): FULL signed embedding from stage word congruence

This theorem removes even the separately assumed G[A]→completed
H[A]-stage graph morphism from the source 4.7(ii) stage-cover
embedding interface.

INPUT DATA:
  * a COMPLETE signed H[A] multiCE-vertex stage T;
  * equality of G[A]-signed word values implies equality of the
    ACTUAL T word-path endpoints from EVERY stage vertex (full
    signed word-action congruence; §5 constructs this by finite
    synchronized actions);
  * for each selected original G[A] B-coset point p, an ACTUAL
    signed word with both the correct exact G[A]-point coordinate
    and the correct completed H[A] stage endpoint from the
    chosen real stage basepoint.

The established constructive `CompleteEGraph.cayleyCoverFromWordCongruence`
produces a true labelled Cayley(G[A])→T homomorphism based at
that vertex, preserving BOTH directed edge orientations.
The genuine signed-word certificates prove the needed
original H-tagged coset pointwise compatibility by actual
signed path naturality; the accepted conditional source
4.7(ii) theorem then gives G[A] multiCE embedding on BOTH
original quotient vertices and actual signed edge tokens.

No ambient G globally retractable assumption, imaginary old edge,
or collapsing of distinct original component tags by H group
coordinates; NO extra axiom or sorry.

The source still must construct the uniform full-B-augmented
H-stage word-action congruence AND suitable real word
certificates for the particular selected historical stage
family. We do not claim that here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}

namespace CayleySubgraphSpec

/-- The fully constructive, signed-word certificate version
of corrected upward source Theorem 4.7(ii). Generates the
ACTUAL signed Cayley stage cover by its uniform word-action
congruence, then proves source-original signed multiCE
embedding from real attached-coset word endpoints. -/
theorem upwardLocalMultiCosetSignedEmbedding_of_wordCongruence
    (Q : LabelledGroupQuotient genΓ genΔ)
    (k : ℕ) (hk : Q.KStable k)
    (hRetH : KRetractable genΔ (k + 1))
    (A : Finset ι) (hA : A.card ≤ k + 1)
    (K : CayleySubgraphSpec (trivialCompletionGenerator genΔ A) A)
    (P : CosetFamilySpec A)
    (Edge : Type*)
    (hAdmH : K.AdmissibleForCosetExtension)
    (T : CompleteEGraph
      (K.MultiCosetVertex P hAdmH
        (isGenerated_trivialCompletionGenerator genΔ A)
        (retractable_trivialCompletionGenerator_of_kRetractable
          genΔ (k + 1) hRetH A hA)) Edge ι)
    (base : K.MultiCosetVertex P hAdmH
      (isGenerated_trivialCompletionGenerator genΔ A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        genΔ (k + 1) hRetH A hA))
    (hWordAction :
      ∀ (w v : LabelWord ι),
        PSTS.SignedWord.evalGroup (trivialCompletionGenerator genΓ A) w =
          PSTS.SignedWord.evalGroup (trivialCompletionGenerator genΓ A) v →
        ∀ x : K.MultiCosetVertex P hAdmH
          (isGenerated_trivialCompletionGenerator genΔ A)
          (retractable_trivialCompletionGenerator_of_kRetractable
            genΔ (k + 1) hRetH A hA),
          T.followWord x w = T.followWord x v)
    (hWordCertificate :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (p : (K.pullbackQuotient
          (Q.localGeneratedSubgroupQuotient A)).AttachedCosetVertex B),
        ∃ w : LabelWord ι,
          PSTS.SignedWord.evalGroup
            (trivialCompletionGenerator genΓ A) w =
              (K.pullbackQuotient (Q.localGeneratedSubgroupQuotient A)).attachedValue B p ∧
          T.followWord base w =
            K.multiCosetInclude P hAdmH
              (isGenerated_trivialCompletionGenerator genΔ A)
              (retractable_trivialCompletionGenerator_of_kRetractable
                genΔ (k + 1) hRetH A hA) B hBP
              (K.pullbackQuotient_attachedCosetToBase
                (Q.localGeneratedSubgroupQuotient A) B p)) :
    Function.Injective
      ((K.pullbackQuotient (Q.localGeneratedSubgroupQuotient A)).multiCosetAmbientHom
        P
        (K.pullbackQuotient_admissible_of_kStable
          (Q.localGeneratedSubgroupQuotient A) k
          (Q.localGeneratedSubgroupQuotient_kStable A k hk) hA hAdmH)
        (isGenerated_trivialCompletionGenerator genΓ A)
        (Q.upwardLocalRetractable_domain k hk hRetH A hA)).onVertex ∧
    Function.Injective
      ((K.pullbackQuotient (Q.localGeneratedSubgroupQuotient A)).multiCosetAmbientHom
        P
        (K.pullbackQuotient_admissible_of_kStable
          (Q.localGeneratedSubgroupQuotient A) k
          (Q.localGeneratedSubgroupQuotient_kStable A k hk) hA hAdmH)
        (isGenerated_trivialCompletionGenerator genΓ A)
        (Q.upwardLocalRetractable_domain k hk hRetH A hA)).onEdge := by
  let gA := trivialCompletionGenerator genΓ A
  let hgenG := isGenerated_trivialCompletionGenerator genΓ A
  let F := T.cayleyCoverFromWordCongruence gA hgenG hWordAction base
  have hOne : F.onVertex (1 : generatedSubgroup genΓ A) = base := by
    exact T.cayleyCoverFromWordCongruence_one
      gA hgenG hWordAction base
  have hCert :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (p : (K.pullbackQuotient
          (Q.localGeneratedSubgroupQuotient A)).AttachedCosetVertex B),
        ∃ w : LabelWord ι,
          PSTS.SignedWord.evalGroup gA w =
            (K.pullbackQuotient (Q.localGeneratedSubgroupQuotient A)).attachedValue B p ∧
          T.followWord (F.onVertex (1 : generatedSubgroup genΓ A)) w =
            K.multiCosetInclude P hAdmH
              (isGenerated_trivialCompletionGenerator genΔ A)
              (retractable_trivialCompletionGenerator_of_kRetractable
                genΔ (k + 1) hRetH A hA) B hBP
              (K.pullbackQuotient_attachedCosetToBase
                (Q.localGeneratedSubgroupQuotient A) B p) := by
    intro B hBP p
    obtain ⟨w, hwG, hwStage⟩ := hWordCertificate B hBP p
    refine ⟨w, hwG, ?_⟩
    rw [hOne]
    exact hwStage
  exact K.upwardLocalMultiCosetSignedEmbedding_of_signedWordCertificates
    Q k hk hRetH A hA K P Edge hAdmH T F hCert

end CayleySubgraphSpec
end ABO
end PSTSEPPA
