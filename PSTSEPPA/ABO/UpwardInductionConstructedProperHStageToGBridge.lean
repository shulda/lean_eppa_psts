import PSTSEPPA.ABO.UpwardInductionCanonicalHClusterToRealGBridge
import PSTSEPPA.ABO.UpwardInductionOriginalHWholeStageCosetAgreement

/-!
# Corrected ABO 4.7(iii): ACTUAL constructed H B-augmentation forces ORIGINAL G bridge

The source's proper n≥2 B-cluster bridge previously required
independently supplying an entire completed H-stage T, a signed
old-H component→T map i, an injective full H[B] coset map J,
and the two exact based Cayley(G) stage endpoint equalities.
All these requirements EXCEPT the real based Cayley(G) cover
are now discharged by the certified whole-component nonisolated
B-augmentation construction.

The genuine original old-H B-component is signed-labelled
graph-isomorphic to the canonical root-translated proper
B-cluster (from forward Theorem 4.5), preserving ALL old
component-tagged vertices and BOTH oriented edge tokens.
Compose that iso with the true canonical signed full
H[B]-coset inclusion cHom. Build the ACTUAL completed
nonisolated H-stage T with its ORIGINAL old-H signed graph
embedding i and REAL vertex-injective H[B] coset embedding J.

The exact agreement i(x)=J(cHom(x)) on all TRUE original
selected B-component vertices removes the old hRoot
hypothesis. If the real G Cayley→T cover F is based at
the original first anchor, labelled G→H quotient Q
and the true ORIGINAL source H anchor coordinates
force its second endpoint i(s₂) automatically. Thus
hCoverEnd disappears as a separate assumption too.

The previous signed constituent-path theorem derives two
REAL old H paths through a true old common core from
actual B∩C₁, B∩C₂ piece membership. Mapping, formally
reversing and concatenating those TRUE signed paths in T
forces H-word equality; B-stability then constructs a REAL
ORIGINAL G multiCE signed B-bridge between its ACTUAL tagged
constituent anchors with EXACT original G word value.

The remaining crucial source-input is existence of the
CORRECTLY BASED Cayley(G)→this actual T signed graph cover,
which must be produced by the published labelled stage
transition quotient/synchronized finite §5 construction.
The source historical selected H component and its active
coatom/core conditions must also be identified. They are
NOT assumed automatic. No absent old edge, arbitrary
identification of unrelated old tags or new axioms.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ V OldEdge : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

namespace EGraph

/-- An exact signed inclusion of one TRUE ORIGINAL
B-component EGraph into the ENTIRE ORIGINAL signed H EGraph.
No missing edges are inserted; both directed old edge
tokens are literally reused. -/
noncomputable def BComponentToOriginalHom
    (H : EGraph V OldEdge ι)
    (B : Finset ι) (anchor : V) :
    LabelledGraphHom
      (H.BComponentEGraph B anchor).toLabelledGraph
      H.toLabelledGraph where
  onVertex x := x.1
  onEdge e := e.1
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

/-- The ACTUAL complete signed H B-augmentation built
directly from the signed canonical proper B-cluster
isomorphism. The needed selected-component full-coset
vertex injection is DERIVED from that isomorphism;
it is not a free source premise. -/
noncomputable def canonicalProperBAugmentedStage
    (H : EGraph V OldEdge ι)
    (hpaired : H.LocallyPairedLabels)
    (genH : ι → Δ)
    (B : Finset ι) (anchor : V) (gH : Δ)
    (cluster : ClusterSpec B)
    (f : LabelledGraphHom
      (H.BComponentEGraph B anchor).toLabelledGraph
      ((cluster.rootTranslatedCayleySubgraph genH gH).toEGraph).toLabelledGraph)
    (hf : Function.Injective f.onVertex) :
    CompleteEGraph
      (H.FullBComponentReplacementVertex genH B anchor gH)
      (ActionEdge (H.FullBComponentReplacementVertex genH B anchor gH) ι) ι :=
  H.wholeOriginalBComponentAugmentedStage
    hpaired genH B anchor gH
    (H.originalBComponentToFullBCosetHom B anchor genH cluster gH f).onVertex
    (H.originalBComponentToFullBCosetHom_vertex_injective
      B anchor genH cluster gH f hf)

end EGraph

namespace CayleySubgraphSpec

variable {genG : ι → Γ} {genH : ι → Δ} {A : Finset ι}
variable (K : CayleySubgraphSpec genG A)

/-- REAL original G two-constituent signed B-bridge from
the G→H labelled quotient, genuine original signed H
canonical proper B-component and the ACTUALLY CONSTRUCTED
complete H[B]-augmentation.

NO separately assumed: full H-stage T, chosen-component
coordinate injection, original signed H→T map i, coset
signed J, equality of original H and J root images,
equality of second cover endpoint, two original H
constituent paths, H group word relation, or G original
signed core/constituent paths.

The ONLY COVER input is an ACTUAL correctly based signed
Cayley(G)→the constructed T map F, as expected from the
source inductive stage-cover hypothesis. -/
theorem upwardProperTwoConstituents_signedBridge_of_constructedHStage
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
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      (H.canonicalProperBAugmentedStage
        hpaired genH B anchor gH cluster f hv.1).toEGraph.toLabelledGraph)
    (hH₁ :
      ((H.originalBComponentToFullBCosetHom
        B anchor genH cluster gH f).onVertex s₁).1 =
          Q.hom a₁.2.1)
    (hH₂ :
      ((H.originalBComponentToFullBCosetHom
        B anchor genH cluster gH f).onVertex s₂).1 =
          Q.hom a₂.2.1)
    (hBased :
      F.onVertex a₁.2.1 =
        Sum.inr ((H.originalBComponentToFullBCosetHom
          B anchor genH cluster gH f).onVertex s₁)) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C₁ hC₁ a₁)
        w
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ a₂) ∧
      PSTS.SignedWord.evalGroup genG w =
        PSTS.SignedWord.evalGroup genG p := by
  let Gcomp := H.BComponentEGraph B anchor
  let cHom := H.originalBComponentToFullBCosetHom
    B anchor genH cluster gH f
  let hcInjective : Function.Injective cHom.onVertex :=
    H.originalBComponentToFullBCosetHom_vertex_injective
      B anchor genH cluster gH f hv.1
  let T := H.canonicalProperBAugmentedStage
    hpaired genH B anchor gH cluster f hv.1
  let J := H.fullBCosetToWholeOriginalBComponentStageHom
    hpaired genH B anchor gH cHom.onVertex hcInjective
  let iOld := H.wholeOriginalBComponentOldSignedHom
    hpaired genH B anchor gH cHom hcInjective
  let i := iOld.comp (H.BComponentToOriginalHom B anchor)
  have hAgree₁ : i.onVertex s₁ = J.onVertex (cHom.onVertex s₁) := by
    change iOld.onVertex s₁.1 = J.onVertex (cHom.onVertex s₁)
    exact H.wholeOriginalBComponentOldSignedHom_agrees_fullCoset
      hpaired genH B anchor gH cHom hcInjective s₁
  have hAgree₂ : i.onVertex s₂ = J.onVertex (cHom.onVertex s₂) := by
    change iOld.onVertex s₂.1 = J.onVertex (cHom.onVertex s₂)
    exact H.wholeOriginalBComponentOldSignedHom_agrees_fullCoset
      hpaired genH B anchor gH cHom hcInjective s₂
  have hBaseOld : F.onVertex a₁.2.1 = iOld.onVertex s₁.1 :=
    hBased.trans (by
      change J.onVertex (cHom.onVertex s₁) = iOld.onVertex s₁.1
      exact (H.wholeOriginalBComponentOldSignedHom_agrees_fullCoset
        hpaired genH B anchor gH cHom hcInjective s₁).symm)
  have hTarget :
      F.onVertex a₂.2.1 = iOld.onVertex s₂.1 :=
    H.wholeOriginalBComponent_oldTarget_of_realGCover_and_HQuotient
      genG genH Q hpaired B anchor gH cHom hcInjective
      F a₁.2.1 a₂.2.1 s₁ s₂ p hp
      hAmbient hH₁ hH₂ hBaseOld
  have hCoverEnd :
      i.onVertex s₂ =
        F.onVertex
          (a₁.2.1 * PSTS.SignedWord.evalGroup genG p) := by
    change iOld.onVertex s₂.1 =
      F.onVertex (a₁.2.1 * PSTS.SignedWord.evalGroup genG p)
    rw [← hAmbient]
    exact hTarget.symm
  have hCoverBase : F.onVertex a₁.2.1 = i.onVertex s₁ :=
    hBased.trans hAgree₁.symm
  exact K.upwardProperTwoConstituents_signedBridge_of_canonicalHCluster
    P hadm hgen hret Q B hStable C₁ C₂ hC₁ hC₂ a₁ a₂
    p hp hAmbient hEmbed
    Gcomp cluster gH f hv he hPiece₁ hPiece₂
    s₁ s₂ core hs₁ hs₂ hc₁ hc₂
    T i J
    (H.fullBCosetToWholeOriginalBComponentStageHom_vertex_injective
      hpaired genH B anchor gH cHom.onVertex hcInjective)
    F (cHom.onVertex s₁) hAgree₁ hCoverBase hCoverEnd

end CayleySubgraphSpec
end ABO
end PSTSEPPA
