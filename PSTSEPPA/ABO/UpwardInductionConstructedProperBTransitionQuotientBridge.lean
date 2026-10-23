import PSTSEPPA.ABO.UpwardInductionConstructedProperHStageToGBridge
import PSTSEPPA.ABO.UpwardInductionBasedCayleyCoverAtOriginalAnchor

/-!
# Corrected ABO upward 4.7(iii): actual FULL H[B]-augmented transition quotient forces the G bridge

The source's proper n≥2 bridge theorem previously required a
REAL correctly based signed Cayley(G)→the CONSTRUCTED nonisolated
completed H B-augmentation T morphism F.

The ORIGINAL finite reflecting-group stage construction is
phrased instead as a LABELLED homomorphism of the original
G group into the TRUE transition subgroup of that stage,
sending every generator of G to the corresponding stage
transition permutation.

Here we replace the remaining arbitrary signed Cayley
cover F hypothesis by EXACTLY that group-theoretic
transition quotient φ:G→Transition(T). We CONSTRUCT F
from the accepted signed canonical Cayley projection,
correctly based at the ORIGINAL G first constituent
anchor coordinate a₁ and the ACTUAL ORIGINAL H-stage
vertex `Sum.inr(cHom(s₁))` using left G translation.
All positive and negative signed edges and stationary
outside-B loops are preserved by this real morphism.

Then the verified source construction gives automatically:
* full original H-stage T built from entire actual B-component;
* the genuine signed full H[B] coset J and ORIGINAL H signed i;
* root match i(s₁)=J(cHom(s₁));
* exact second G→H source quotient stage endpoint i(s₂);
* both actual H constituent signed B∩Cᵢ paths and shared old core;
* true H word equality, G stability reflection and ACTUAL
  ORIGINAL tagged G multiCE B path with group value [p]_G.

Crucial remaining high-rank source obligation is to CONSTRUCT
the history-selected finite stage labelled transition quotient
φ for all relevant actual H[B] augmentations, and instantiate
the true original H forward cluster active coatom/source
matching. There is no claim that such a quotient exists
for arbitrary old H stages without the induction hypotheses.
No new axiom, fake old signed edge or collapsed original tags.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ V OldEdge : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

namespace CayleySubgraphSpec

variable {genG : ι → Γ} {genH : ι → Δ} {A : Finset ι}
variable (K : CayleySubgraphSpec genG A)

/-- True constructed proper n≥2 B-cluster upward bridge with
NO free completed H-stage, old signed i, full coset J,
based signed Cayley(G) morphism, free H group equation,
arbitrary second endpoint or source signed constituent
path witnesses. The only group-cover premise is a TRUE
labelled transition-quotient φ into the ACTUAL constructed
finite H[B] augmentation stage. -/
theorem upwardProperTwoConstituents_signedBridge_of_constructedHStageTransitionQuotient
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated genG) (hret : Retractable genG)
    (Q : LabelledGroupQuotient genG genH)
    (B : Finset ι) (hStable : Q.StableAt B)
    (C₁ C₂ : Finset ι)
    (hC₁ : C₁ ∈ P.alphabets)
    (hC₂ : C₂ ∈ P.alphabets)
    (a₁ : K.AttachedCosetVertex C₁)
    (a₂ : K.AttachedCosetVertex C₂)
    (p : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hAmbient :
      a₂.2.1 = a₁.2.1 * PSTS.SignedWord.evalGroup genG p)
    (hEmbed :
      Function.Injective
        (K.multiCosetAmbientValue P hadm hgen hret))
    (H : EGraph V OldEdge ι)
    (hpaired : H.LocallyPairedLabels)
    (anchor : V)
    (cluster : ClusterSpec B) (gH : Δ)
    (f : LabelledGraphHom
      (H.BComponentEGraph B anchor).toLabelledGraph
      ((cluster.rootTranslatedCayleySubgraph genH gH).toEGraph).toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (hPiece₁ : B ∩ C₁ ∈ cluster.pieces)
    (hPiece₂ : B ∩ C₂ ∈ cluster.pieces)
    (s₁ s₂ core : {v : V // v ∈ H.BComponentVertexSet B anchor})
    (hs₁ : (f.onVertex s₁).1 ∈
      generatedLeftCoset genH (B ∩ C₁) gH)
    (hs₂ : (f.onVertex s₂).1 ∈
      generatedLeftCoset genH (B ∩ C₂) gH)
    (hc₁ : (f.onVertex core).1 ∈
      generatedLeftCoset genH (B ∩ C₁) gH)
    (hc₂ : (f.onVertex core).1 ∈
      generatedLeftCoset genH (B ∩ C₂) gH)
    (φ : Γ →*
      (H.canonicalProperBAugmentedStage
        hpaired genH B anchor gH cluster f hv.1).transitionGroup)
    (hφ : ∀ i : ι,
      φ (genG i) =
        (H.canonicalProperBAugmentedStage
          hpaired genH B anchor gH cluster f hv.1).transitionSubgroupGenerator i)
    (hH₁ :
      ((H.originalBComponentToFullBCosetHom
        B anchor genH cluster gH f).onVertex s₁).1 =
          Q.hom a₁.2.1)
    (hH₂ :
      ((H.originalBComponentToFullBCosetHom
        B anchor genH cluster gH f).onVertex s₂).1 =
          Q.hom a₂.2.1)
 :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C₁ hC₁ a₁)
        w
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ a₂) ∧
      PSTS.SignedWord.evalGroup genG w =
        PSTS.SignedWord.evalGroup genG p := by
  let T := H.canonicalProperBAugmentedStage
    hpaired genH B anchor gH cluster f hv.1
  let cHom := H.originalBComponentToFullBCosetHom
    B anchor genH cluster gH f
  let u : H.FullBComponentReplacementVertex genH B anchor gH :=
    Sum.inr (cHom.onVertex s₁)
  let F := T.basedCayleyProjectionAtGroupPoint
    genG φ hφ a₁.2.1 u
  have hBased :
      F.onVertex a₁.2.1 =
        Sum.inr (cHom.onVertex s₁) := by
    exact T.basedCayleyProjectionAtGroupPoint_anchor
      genG φ hφ a₁.2.1 u
  exact K.upwardProperTwoConstituents_signedBridge_of_constructedHStage
    P hadm hgen hret Q B hStable C₁ C₂ hC₁ hC₂
    a₁ a₂ p hp hAmbient hEmbed
    H hpaired anchor cluster gH f hv he
    hPiece₁ hPiece₂ s₁ s₂ core
    hs₁ hs₂ hc₁ hc₂ F hH₁ hH₂ hBased

end CayleySubgraphSpec
end ABO
end PSTSEPPA
