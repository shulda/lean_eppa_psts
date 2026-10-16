import PSTSEPPA.ABO.SourceLiteralY1SelectedRootType2CompleteStageIso
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootAmbientValueNaturality
import PSTSEPPA.ABO.IsolatedCosetCompletion

/-!
# Exact source-H₁ named type-(2) completion at its intrinsic old-root anchor

The TRUE selected literal T(Y₁) off-B completion transports to a
genuine SourceH₁ completion attached at the group-isomorphic image
of its REAL noninjective ambient glued vertex coordinate.

Independently, the original SourceH₁ chosen-root construction uses
the ACTUAL group coordinate of the corresponding source-H₁ glued
vertex. The already certified selected-quotient value naturality
proves these two group anchors are LITERALLY EQUAL, without merging
different component-tagged old vertices with the same coordinate.

The carrier of an isolated fresh B-coset depends on its anchor, so
the correct API statement is heterogeneous equality of the two
completed signed action graphs. This explicitly identifies the
independently named SourceH₁ complete action with the printed
type-(2) source-side transport, including formal inverse edges,
new coset points and legal missing stationary loops.

The further comparison to the H₁[A] ROOT-TRANSLATED local G₂
catalogue stage is a separate gate; no G₂ word kernel is claimed.
-/

namespace PSTSEPPA
namespace ABO

namespace IsolatedCosetGluing

variable {ι V Γ OldEdge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Natural heterogeneous equality of the LEGALLY completed
signed isolated B-coset action whenever the ACTUAL two group
anchor elements agree. Old/new coset vertex carriers depend on
the anchor; no equation of unrelated ambient-coordinate-tagged
old vertices is claimed. Proofs of pairedness and missing old
B-edges may differ propositionally. -/
theorem completedStage_heq_of_group_anchor_eq
    (G : EGraph V OldEdge ι) (gen : ι → Γ)
    (B : Finset ι) {g h : Γ} (hgh : g = h)
    (u : V)
    (hMissingG hMissingH : ∀ e : OldEdge,
      G.source e = u → signedBase (G.label e) ∉ B)
    (hPairedG hPairedH : G.LocallyPairedLabels) :
    HEq
      (completedStage G gen B g u hMissingG hPairedG)
      (completedStage G gen B h u hMissingH hPairedH) := by
  cases hgh
  rfl

end IsolatedCosetGluing

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The named source stage of the actual paper off-B choice,
attached at the exact true SOURCE ambient group value of
the transformed tagged old root, rather than at an arbitrary
ambient H₁ coset representative. -/
noncomputable abbrev literalPaperSelectedOffBNamedSourceCompletedStage
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :=
  IsolatedCosetGluing.completedStage
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root)
      (allProperCosetFamily A))
    (sourceH1Generator src dst) B
    (sourceH1OriginalSelectedRootAmbientValue
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root)
      (allProperCosetFamily A)
      ((sourceLiteralY1RootToH1MultiCosetVertexEquiv
        src dst base A hcard root (allProperCosetFamily A)) z.vertex))
    ((sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root (allProperCosetFamily A)) z.vertex)
    (z.source_noOldBEdges src dst base A hcard root B hBP)
    (sourceH1OriginalRootAllProper_locallyPaired
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root))

/-- Exact (dependent) equality of the two TRUE completed source
models for a selected literal paper off-B root: the source
stage transported from the printed augmentation, and the
original source-H₁ stage attached at its canonical old value.

The equality follows from real tagged quotient value naturality,
not from injectivity of the noninjective ambient-value map. -/
theorem literalPaperSelectedOffBSourceCompletedStage_heq_named
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP) :
    HEq
      (literalPaperSelectedOffBSourceCompletedStage
        src dst base A hcard root B hBP z)
      (literalPaperSelectedOffBNamedSourceCompletedStage
        src dst base A hcard root B hBP z) := by
  exact IsolatedCosetGluing.completedStage_heq_of_group_anchor_eq
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root)
        (allProperCosetFamily A))
    (sourceH1Generator src dst) B
    (literalPaperSelectedOffBSourceAnchor_eq
      src dst base A hcard root B hBP z)
    ((sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root (allProperCosetFamily A)) z.vertex)
    (z.source_noOldBEdges src dst base A hcard root B hBP)
    (z.source_noOldBEdges src dst base A hcard root B hBP)
    (sourceH1OriginalRootAllProper_locallyPaired src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root))
    (sourceH1OriginalRootAllProper_locallyPaired src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root))
end ABO
end PSTSEPPA
