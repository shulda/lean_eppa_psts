import PSTSEPPA.ABO.UpwardInductionR1LocalGroupPackage
import PSTSEPPA.ABO.KStableLocalGeneratedSubgroupQuotient
import PSTSEPPA.ABO.KStablePullbackMultiCosetStageCoverEmbedding
import PSTSEPPA.ABO.GraphHomInjectivity

/-!
# Corrected ABO Theorem 4.7(ii): signed local multiCE embedding from a REAL stage cover

The source group G need not be globally retractable on all E letters.
The accepted repair R1 supplies retractability of the true local G[A]
and H[A] groups whenever G→H is k-stable, H is (k+1)-retractable
and |A|≤k+1.

The labelled local quotient Q_A : G[A]→H[A] is a genuine k-stable
surjective generator-preserving quotient, not an identification of
old-component tags with ambient group coordinates.

The already certified stage-cover embedding theorem is here
specialized to these true LOCAL groups. Its crucial stage input is
EXPLICIT: a genuine COMPLETE signed EGraph T with vertices the true
H[A] multi-coset quotient and a labelled Cayley(G[A])→T morphism
whose value at EVERY actual attached B-coset point is EXACTLY
its H-side original-component-tagged B-summand inclusion.

Under that ACTUAL stage representation condition, the source
G[A]-side selected multi-coset quotient embeds into its ambient
G[A] Cayley graph on both genuine VERTICES and positive/inverse
oriented signed EDGE TOKENS. This is NOT a proof that the printed
Definition 5.3 stage family satisfies the necessary representation
condition: showing the promised cover of every H CE B-augmentation
gives this condition is the remaining source Theorem 4.7(ii)
instantiation gate. We never infer H-side embeddedness from its
cluster property, nor insert an absent old edge.

No global G retractability, imaginary original edge or custom axiom/sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}

/-- Real k-stable source local quotient, with the correct full
label alphabet but only A-generated group carriers. -/
theorem LabelledGroupQuotient.upwardLocalGeneratedQuotient_kStable
    (Q : LabelledGroupQuotient genΓ genΔ)
    (k : ℕ) (hk : Q.KStable k) (A : Finset ι) :
    (Q.localGeneratedSubgroupQuotient A).KStable k :=
  Q.localGeneratedSubgroupQuotient_kStable A k hk

namespace CayleySubgraphSpec

/-- Source 4.7(ii), LOCAL CONDITIONAL stage-cover interface:
actual k-stable G→H expansion, (k+1)-retractable H,
local generated G[A]/H[A], and an actual signed complete
stage Cayley G[A] cover representing EVERY selected original
component-tagged H[A] coset point.

Then the genuine source local G[A] multiCE is INJECTIVE in
ambient G[A], simultaneously on original quotient VERTICES
and directed signed EDGE TOKENS, including inverses and loops.

This is exactly conditional on the actual stage representation
hypothesis, not an unproved assertion that the historical
selected source stages of §5 already supply that cover. -/
theorem upwardLocalMultiCosetSignedEmbedding_of_stageCover
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
    (hRepresent :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (p : (K.pullbackQuotient
          (Q.localGeneratedSubgroupQuotient A)).AttachedCosetVertex B),
        F.onVertex
          ((K.pullbackQuotient (Q.localGeneratedSubgroupQuotient A)).attachedValue B p) =
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
  let QA := Q.localGeneratedSubgroupQuotient A
  let L := K.pullbackQuotient QA
  let hGenG := isGenerated_trivialCompletionGenerator genΓ A
  let hGenH := isGenerated_trivialCompletionGenerator genΔ A
  let hRetG := Q.upwardLocalRetractable_domain k hk hRetH A hA
  let hRetLocalH := retractable_trivialCompletionGenerator_of_kRetractable
    genΔ (k+1) hRetH A hA
  let hStableLocal := Q.localGeneratedSubgroupQuotient_kStable A k hk
  let hAdmG := K.pullbackQuotient_admissible_of_kStable
    QA k hStableLocal hA hAdmH
  have hVertex :
      Function.Injective
        (L.multiCosetAmbientValue P hAdmG hGenG hRetG) :=
    K.pullbackQuotient_multiCosetAmbient_injective_of_kStable_stageCover
      QA P k hStableLocal hA hAdmH
      hGenH hRetLocalH hGenG hRetG T F hRepresent
  exact
    (L.multiCosetAmbientHom P hAdmG hGenG hRetG).bijective_on_image_of_vertex_injective
      hVertex

end CayleySubgraphSpec
end ABO
end PSTSEPPA
