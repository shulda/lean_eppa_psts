import PSTSEPPA.ABO.UpwardInductionProperTwoConstituentsFromRealAugmentedCover
import PSTSEPPA.ABO.SignedGraphPathReverse

/-!
# Corrected upward ABO 4.7(iii): genuine original H constituent paths force the G bridge

For the published nonisolated proper B-cluster with at least two active
constituents, the old H coset extension contains ACTUAL signed paths
s₁ --w₁--> core and s₂ --w₂--> core. These are NOT merely group
equalities and have NOT been invented by completing missing labels.

First we prove a generic transport lemma: a real labelled morphism
from the original incomplete signed H EGraph to a complete stage T
carries the FIRST real path forward and the SECOND real path backward
via formal inverse signed edge tokens. Their concatenation is an
ACTUAL signed T path with word w₁ ++ inv(w₂).

Then we combine this with the previously certified cover-forced
H-group word equality and true original G constituent signed paths:
if the original H endpoint images agree EXACTLY with the images
of the original G ambient word endpoints under a real
Cayley(G)→T cover, and the full H[B] coset injects into T,
the result is a REAL G multi-coset-extension signed B-path
between the ORIGINAL component-tagged G coset anchor vertices,
having the EXACT original ambient G word value.

No pre-supplied two-piece path in T, no free [p]_H=[w₁ inv(w₂)]_H
hypothesis, no invented G paths, no forced equality of differently
tagged original vertices from ambient group coordinates, no
isolated-root/no-old-B-edge assumption and no global T→Cayley(H).

The genuinely OPEN higher-stage obligation is to CONSTRUCT the
published component-tagged H augmentation T, its correct old-stage
embedding, full-B-coset inclusion and Cayley(G) cover, and to
establish the exact based original endpoint identifications. Those
are transparent explicit inputs here, rather than claimed theorems.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ V OldEdge W StageEdge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]

namespace EGraph

/-- Two REAL original incomplete-H signed paths entering the SAME
original H core give a real signed path between their old starts
in ANY complete augmented stage carrying the original H graph.
The inverse portion uses the old formal reverse edge tokens. -/
theorem two_original_pieces_map_to_signed_completeStage
    (H : EGraph V OldEdge ι)
    (T : CompleteEGraph W StageEdge ι)
    (i : LabelledGraphHom
      H.toLabelledGraph T.toEGraph.toLabelledGraph)
    (s₁ s₂ core : V)
    (w₁ w₂ : LabelWord ι)
    (h₁ : H.Follows s₁ w₁ core)
    (h₂ : H.Follows s₂ w₂ core) :
    T.toEGraph.Follows
      (i.onVertex s₁)
      (w₁ ++ PSTS.SignedWord.inv w₂)
      (i.onVertex s₂) := by
  have hForward :
      T.toEGraph.Follows
        (i.onVertex s₁) w₁ (i.onVertex core) :=
    h₁.map i
  have hBackward :
      T.toEGraph.Follows
        (i.onVertex core) (PSTS.SignedWord.inv w₂)
        (i.onVertex s₂) :=
    (H.follows_signedWord_reverse h₂).map i
  exact T.toEGraph.follows_append hForward hBackward

end EGraph

namespace CayleySubgraphSpec

variable {genG : ι → Γ} {genH : ι → Δ} {A : Finset ι}
variable (K : CayleySubgraphSpec genG A)

/-- Corrected Theorem 4.7(iii), proper n≥2 ORIGINAL G B-bridge:
from two TRUE old H constituent paths to one TRUE old H core, a
genuine original-H→augmented-T labelled morphism and the correctly
based full-coset/Cayley(G) stage covers, derive a REAL signed
original G multiCE bridge with exact G word value.

The two H paths provide the actual augmented piece path previously
assumed in `upwardProperTwoConstituents_signedBridge_of_realAugmentedCover`.
The theorem explicitly keeps the important source endpoint
equalities on ORIGINAL tagged H vertices, not their ambient H values. -/
theorem upwardProperTwoConstituents_signedBridge_of_originalHPieces
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
    (p w₁ w₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hw₁ : LabelWord.Uses (B ∩ C₁) w₁)
    (hw₂ : LabelWord.Uses (B ∩ C₂) w₂)
    (hAmbient :
      a₂.2.1 = a₁.2.1 * PSTS.SignedWord.evalGroup genG p)
    (hEmbed :
      Function.Injective
        (K.multiCosetAmbientValue P hadm hgen hret))
    (H : EGraph V OldEdge ι)
    (T : CompleteEGraph W StageEdge ι)
    (i : LabelledGraphHom H.toLabelledGraph T.toEGraph.toLabelledGraph)
    (s₁ s₂ core : V)
    (hHPath₁ : H.Follows s₁ w₁ core)
    (hHPath₂ : H.Follows s₂ w₂ core)
    (gH : Δ)
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
  have hStagePieces :
      T.toEGraph.Follows
        (i.onVertex s₁)
        (w₁ ++ PSTS.SignedWord.inv w₂)
        (i.onVertex s₂) :=
    H.two_original_pieces_map_to_signed_completeStage
      T i s₁ s₂ core w₁ w₂ hHPath₁ hHPath₂
  have hAugmentedPiecePath :
      T.toEGraph.Follows
        (J.onVertex p₀)
        (w₁ ++ PSTS.SignedWord.inv w₂)
        (F.onVertex
          (a₁.2.1 * PSTS.SignedWord.evalGroup genG p)) := by
    rw [← hRoot, ← hCoverEnd]
    exact hStagePieces
  exact K.upwardProperTwoConstituents_signedBridge_of_realAugmentedCover
    P hadm hgen hret Q B hStable C₁ C₂ hC₁ hC₂
    a₁ a₂ p w₁ w₂ hp hw₁ hw₂ hAmbient hEmbed
    T gH J hJInjective F p₀
    (hCoverBase.trans hRoot) hAugmentedPiecePath

end CayleySubgraphSpec
end ABO
end PSTSEPPA
