import PSTSEPPA.ABO.UpwardInductionLocalStageCoverSignedEmbedding
import PSTSEPPA.ABO.UpwardInductionStageSignedWordEndpoint

/-!
# Corrected ABO Theorem 4.7(ii): from ACTUAL signed stage paths to G multiCE embedding

The difficult source obligation behind pointwise H-stage compatibility
is normally given by ACTUAL signed words. For each selected attached
G[A] B-coset point p, suppose a chronological signed word w has

  (1) the correct exact G[A]-group value, namely its actual
      original component-tagged attached point's group coordinate;
  (2) the correct TRUE completed-stage T endpoint from F(1),
      namely its corresponding exact H[A] original tagged coset vertex.

The accepted real signed Cayley-stage homomorphism path naturality
proves the exact old-tagged pointwise representation equality;
the already certified conditional local upward embedding theorem
then gives injectivity of the entire G[A] multiCE on true signed
quotient VERTICES AND both orientations of actual EDGE TOKENS.

The hypothesis is a finite/rank-sensitive ACTUAL stage signed-word
certificate, not a false assumption that H multiCE already embeds
in ambient H[A]. It is designed to be discharged by the source's
selected B-coset AUGMENTED H-stage Cayley covers; the latter remain
a genuine separate theorem still to be formalized. No global
retractability of original G, fake old edge, or custom axiom/sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}

namespace CayleySubgraphSpec

/-- Corrected source 4.7(ii), local signed-word witness interface.
A genuine signed G[A]-Cayley hom F to an H[A] completed stage,
equipped with one REAL source G-group-valued signed word and
correct H-stage endpoint for EVERY original selected B-coset point,
forces a true labelled-graph embedding of the whole G[A]
multiCE into its original ambient Cayley graph. -/
theorem upwardLocalMultiCosetSignedEmbedding_of_signedWordCertificates
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
    (F : LabelledGraphHom
      (cayleyGraph (trivialCompletionGenerator genΓ A)).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (hWordCertificate :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (p : (K.pullbackQuotient
          (Q.localGeneratedSubgroupQuotient A)).AttachedCosetVertex B),
        ∃ w : LabelWord ι,
          PSTS.SignedWord.evalGroup
            (trivialCompletionGenerator genΓ A) w =
              (K.pullbackQuotient (Q.localGeneratedSubgroupQuotient A)).attachedValue B p ∧
          T.followWord (F.onVertex (1 : generatedSubgroup genΓ A)) w =
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
  apply K.upwardLocalMultiCosetSignedEmbedding_of_stageCover
    Q k hk hRetH A hA K P Edge hAdmH T F
  intro B hBP p
  obtain ⟨w, hGroup, hStage⟩ := hWordCertificate B hBP p
  calc
    F.onVertex
        ((K.pullbackQuotient (Q.localGeneratedSubgroupQuotient A)).attachedValue B p) =
      F.onVertex (PSTS.SignedWord.evalGroup
        (trivialCompletionGenerator genΓ A) w) :=
      congrArg F.onVertex hGroup.symm
    _ = T.followWord (F.onVertex (1 : generatedSubgroup genΓ A)) w :=
      T.cayleyHom_on_signedWordValue
        (trivialCompletionGenerator genΓ A) F w
    _ = K.multiCosetInclude P hAdmH
          (isGenerated_trivialCompletionGenerator genΔ A)
          (retractable_trivialCompletionGenerator_of_kRetractable
            genΔ (k + 1) hRetH A hA) B hBP
          (K.pullbackQuotient_attachedCosetToBase
            (Q.localGeneratedSubgroupQuotient A) B p) := hStage

end CayleySubgraphSpec
end ABO
end PSTSEPPA
