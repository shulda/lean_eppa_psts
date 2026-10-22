import PSTSEPPA.ABO.UpwardInductionOriginalConstituentPathsFromCanonicalCluster
import PSTSEPPA.ABO.UpwardInductionOriginalHPathsToGBridge

/-!
# Corrected upward ABO 4.7(iii): actual canonical H component yields actual G bridge

This is the complete CONDITIONAL PROPER n≥2 algebra/geometry
interface, with NO free witness of either original H path,
NO free H-word equality, NO free augmented H-stage piece
path, NO pre-supplied real G constituent paths and NO
assumed equality of independently constructed G quotient
cores.

The accepted forward ABO Theorem 4.5 already gives signed
vertex/edge isomorphisms of the ACTUAL original H
component-tagged proper B-cluster with a root-LEFT-
TRANSLATED canonical cluster. Given that actual isomorphism
and genuine membership of s₁,s₂ and an original common
core in their respective selected full B∩Cᵢ constituents,
the independent exact-full-coset path theorem produces
both real signed ORIGINAL H paths to the actual core.

We map those real paths through an actual old-H→complete
augmented stage hom, formally reverse the second genuine
path, and concatenate. With a vertex-injective literal
full H[B]-coset embedding J in the stage, a genuinely
based Cayley(G)→T morphism F and correct tagged end
comparisons, the two REAL augmented signed paths force
[p]_H=[w₁ ++ inv(w₂)]_H. B-stability reflects this
identity to G. Both genuine original G completed-coset
paths and their common ORIGINAL quotient core follow from
the certified signed full coset and multiCE embedding
lemmas. Thus there is a genuine original G multiCE
B-path joining exactly the two original attached tagged
G anchors, with exact G word evaluation [p]_G.

Remaining source-specific requirements (NOT yet discharged):
* instantiate the canonical signed H-component isomorphism
  and its genuine selected constituent coset memberships
  using the precise original forward Theorem 4.5;
* construct the actual HISTORY-SELECTED whole-component
  H[B] augmentation T with old-H signed morphism i,
  injective full-H[B] signed embedding J and actual
  Cayley(G) cover F, based at true original H/G anchors;
* verify original tagged H endpoint images under i and F
  and correct selected stage for every proper B.

The base H component can have genuine old B-edges;
no isolated-root assumption, ambient-H CE injectivity
or identification of distinct component tags from
ambient group values is used.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ V OldEdge W StageEdge : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genG : ι → Γ} {genH : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec genG A)

/-- Genuine original G signed B-bridge derived from the TRUE
canonical signed H proper B-component, with actual selected
two-constituent membership and the correctly based
whole-augmentation signed H/G covers. The ambient original
G B-word endpoint and true quotient tags are preserved. -/
theorem upwardProperTwoConstituents_signedBridge_of_canonicalHCluster
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
    (cluster : ClusterSpec B)
    (gH : Δ)
    (f : LabelledGraphHom
      H.toLabelledGraph
      ((cluster.rootTranslatedCayleySubgraph genH gH).toEGraph).toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (hPiece₁ : B ∩ C₁ ∈ cluster.pieces)
    (hPiece₂ : B ∩ C₂ ∈ cluster.pieces)
    (s₁ s₂ core : V)
    (hs₁ : (f.onVertex s₁).1 ∈
      generatedLeftCoset genH (B ∩ C₁) gH)
    (hs₂ : (f.onVertex s₂).1 ∈
      generatedLeftCoset genH (B ∩ C₂) gH)
    (hc₁ : (f.onVertex core).1 ∈
      generatedLeftCoset genH (B ∩ C₁) gH)
    (hc₂ : (f.onVertex core).1 ∈
      generatedLeftCoset genH (B ∩ C₂) gH)
    (T : CompleteEGraph W StageEdge ι)
    (i : LabelledGraphHom
      H.toLabelledGraph T.toEGraph.toLabelledGraph)
    (J : LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph genH B gH).toEGraph).toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (hJInjective : Function.Injective J.onVertex)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (p₀ : IsolatedCosetGluing.CosetPoint genH B gH)
    (hRoot : i.onVertex s₁ = J.onVertex p₀)
    (hCoverBase : F.onVertex a₁.2.1 = i.onVertex s₁)
    (hCoverEnd :
      i.onVertex s₂ =
        F.onVertex
          (a₁.2.1 * PSTS.SignedWord.evalGroup genG p)) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C₁ hC₁ a₁)
        w
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ a₂) ∧
      PSTS.SignedWord.evalGroup genG w =
        PSTS.SignedWord.evalGroup genG p := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hHPath₁, hHPath₂⟩ :=
    cluster.original_two_constituent_signed_paths_of_translated_cluster_iso
      H genH gH f hv he
      (B ∩ C₁) (B ∩ C₂) hPiece₁ hPiece₂
      s₁ s₂ core hs₁ hs₂ hc₁ hc₂
  exact K.upwardProperTwoConstituents_signedBridge_of_originalHPieces
    P hadm hgen hret Q B hStable C₁ C₂ hC₁ hC₂
    a₁ a₂ p w₁ w₂ hp hw₁ hw₂ hAmbient hEmbed
    H T i s₁ s₂ core hHPath₁ hHPath₂
    gH J hJInjective F p₀ hRoot hCoverBase hCoverEnd

end CayleySubgraphSpec
end ABO
end PSTSEPPA
