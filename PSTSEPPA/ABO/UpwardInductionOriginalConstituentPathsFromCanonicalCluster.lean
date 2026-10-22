import PSTSEPPA.ABO.ProperClusterRootTranslatedSignedIso
import PSTSEPPA.ABO.CayleySubgraphFullCosetPaths
import PSTSEPPA.ABO.BijectiveLabelledEGraphPaths

/-!
# ABO upward Theorem 4.7(iii): ACTUAL old H constituent paths from signed cluster shape

The corrected source proper B-cluster (n>=2) branch uses two actual
signed OLD H paths from component-tagged constituent endpoints to
a common TRUE original tagged cluster core. Merely equating
ambient H coordinates is NOT enough to obtain these paths.

ABO's already formally certified forward Theorem 4.5 identifies
the entire actual original B-component, on vertices AND both
oriented signed edge tokens, with a root-LEFT-TRANSLATED canonical
proper cluster. The cluster is a literal union of full subgroup
constituents. For each active constituent alphabet D⊊B, EVERY
signed D-edge in the corresponding translated gH[D] is present.

Consequently, if the images of an actual original constituent
vertex and an actual original common core lie in the SAME
translated gH[D] constituent, they are connected by an ACTUAL
signed D-word in the canonical cluster. The already checked
bijective labelled graph path REFLECTION lifts the path to the
original H B-component EGraph, with its ORIGINAL quotient
tags and real old positive/inverse edge tokens unchanged.

This module proves the full-coset edge inclusion in the actual
translated canonical signed cluster, and obtains both original
constituent paths simultaneously from the exact canonical
signed isomorphism and their TRUE piece membership.

It requires NO G-stage cover, no global old H multiCE ambient
embedding, no no-old-B-edge assumption, no fake edge and no
group-coordinate identification of different old H tags.
The remaining specific source work is to extract the chosen
two constituent vertex/core memberships and the signed
component isomorphism from ORIGINAL H Theorem 4.5 data.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {B : Finset ι}

namespace ClusterSpec

/-- All actual positive and inverse D-Cayley edges of the
translated constituent gH[D] occur as REAL old signed edges
of the translated canonical proper B-cluster whenever
D is one of its genuine selected constituent pieces.
No additional retractability or generation assumption. -/
theorem rootTranslated_full_piece_signed_edge_mem
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ)
    (D : Finset ι) (hDP : D ∈ P.pieces)
    (e : ActionEdge Γ ι)
    (he : e ∈ FullCosetEdgeSet gen D g) :
    e ∈ (P.rootTranslatedCayleySubgraph gen g).edges := by
  change
    ∃ E ∈ P.pieces,
      g⁻¹ * e.1 ∈ generatedSubgroup gen E ∧
      signedBase e.2 ∈ E
  exact ⟨D, hDP, he.1, he.2⟩

/-- ACTUAL original H signed two-constituent paths obtained by
reflecting the FULL translated-coset paths through the
vertex-and-directed-edge bijective labelled graph isomorphism
of the original signed B-component.

For each constituent Di, the true images of si and core must
both lie in the SINGLE original translated gH[Di] piece.
There is no identification of different original vertices
from equality of their ambient H coordinates. -/
theorem original_two_constituent_signed_paths_of_translated_cluster_iso
    {V OldEdge : Type*}
    (H : EGraph V OldEdge ι)
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ)
    (f : LabelledGraphHom
      H.toLabelledGraph
      ((P.rootTranslatedCayleySubgraph gen g).toEGraph).toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (D₁ D₂ : Finset ι)
    (hD₁ : D₁ ∈ P.pieces)
    (hD₂ : D₂ ∈ P.pieces)
    (s₁ s₂ core : V)
    (hs₁ : (f.onVertex s₁).1 ∈ generatedLeftCoset gen D₁ g)
    (hs₂ : (f.onVertex s₂).1 ∈ generatedLeftCoset gen D₂ g)
    (hc₁ : (f.onVertex core).1 ∈ generatedLeftCoset gen D₁ g)
    (hc₂ : (f.onVertex core).1 ∈ generatedLeftCoset gen D₂ g) :
    ∃ w₁ w₂ : LabelWord ι,
      LabelWord.Uses D₁ w₁ ∧
      LabelWord.Uses D₂ w₂ ∧
      H.Follows s₁ w₁ core ∧
      H.Follows s₂ w₂ core := by
  let K := P.rootTranslatedCayleySubgraph gen g
  obtain ⟨w₁, hw₁, hCluster₁⟩ :=
    K.reachable_in_fullCoset D₁ g
      (fun e eMem =>
        P.rootTranslated_full_piece_signed_edge_mem
          gen g D₁ hD₁ e eMem)
      (f.onVertex s₁) (f.onVertex core)
      hs₁ hc₁
  obtain ⟨w₂, hw₂, hCluster₂⟩ :=
    K.reachable_in_fullCoset D₂ g
      (fun e eMem =>
        P.rootTranslated_full_piece_signed_edge_mem
          gen g D₂ hD₂ e eMem)
      (f.onVertex s₂) (f.onVertex core)
      hs₂ hc₂
  have hOld₁ : H.Follows s₁ w₁ core :=
    (H.follows_iff_of_bijective_labelledHom
      K.toEGraph f hv he s₁ core w₁).mpr hCluster₁
  have hOld₂ : H.Follows s₂ w₂ core :=
    (H.follows_iff_of_bijective_labelledHom
      K.toEGraph f hv he s₂ core w₂).mpr hCluster₂
  exact ⟨w₁, w₂, hw₁, hw₂, hOld₁, hOld₂⟩

end ClusterSpec
end ABO
end PSTSEPPA
