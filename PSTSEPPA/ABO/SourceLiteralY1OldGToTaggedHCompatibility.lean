import PSTSEPPA.ABO.SourceLiteralY1OldRootTaggedStageInclusion
import PSTSEPPA.ABO.SourceLiteralY1OldPathLocalStageAgreement
import PSTSEPPA.ABO.AmbientSkeletonAlphabetRestriction
import PSTSEPPA.ABO.ComponentSubgraphPaths

/-!
# SOURCE-EXACT G[A] cover vs true original H component-tagged old vertices

The two separately checked root-side statements were:
* real original G=T(X₂^all) signed A-words have normalized
  G[A]-coordinates with their exact completed-stage word endpoints;
* the actual old H=T(Y₁) selected original A-component maps to
  the exact same signed word endpoints of the genuine component-
  tagged H P_A completed stage, through the empty-B constituent.

Here we finally COMPOSE them, but ONLY for ONE selected original G
A-component rooted over the given H root, not for arbitrary ambient
G points with the same H image.

An actual original G A-word path is mapped to an actual old H word
path. We RESTRICT its original edges to A, then lift every signed
edge to the TRUE selected H A-component subgraph, preserving its
endpoint and original component tag. The resulting old H point is
mapped by the exact quotient inclusion from the previous module.

This gives the true source-facing equality
  fullLocalG[A]StageCover(gRoot⁻¹ * x)
     = exactOldTaggedHStageInclusion(H_old_endpoint),
for EVERY original G A-path from the selected root, using equality
of vertices in the literal component-tagged stage quotient (NOT
equality of ambient H-group coordinates).

No full G/H coset extension embedding, arbitrary disconnected G
component identification, R8 bridge freeness, Condition 5.2 or
unconditional PSTS EPPA is asserted.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every TRUE old original G A-word path from a root lying
above an H original old root projects to a REAL path in the
corresponding H original A-component. The whole path is lifted
into that component via ACTUAL original signed edges, not by
replacing components with ambient group cosets.

We return the exact H group point of the endpoint as well as
the true component-subgraph vertex and original signed path. -/
theorem sourceLiteralY1X2AllOriginal_selectedOldH_APath_lift
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (gRoot x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (hRoot :
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex gRoot =
        (⟨root, by trivial⟩ :
          (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex))
    (w : LabelWord ι) (hw : LabelWord.Uses A w)
    (hp : ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).Follows
      gRoot w x) :
    ∃ y : (sourceLiteralY1DirectRootComponent
        src dst base A root).Vertex,
      y.1 =
        ((sourceLiteralY1X2AllOriginalToY1Hom
          src dst base).onVertex x).1 ∧
      ((sourceLiteralY1DirectRootComponent
        src dst base A root).toEGraph).Follows
          (sourceLiteralY1SelectedRootOldPoint
            src dst base A root) w y := by
  let H := sourceLiteralY1DirectOriginalSkeleton src dst base
  let F := sourceLiteralY1X2AllOriginalToY1Hom src dst base
  let K := H.restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  have hpH : H.toEGraph.Follows (F.onVertex gRoot) w (F.onVertex x) :=
    hp.map F
  have hRoot' : F.onVertex gRoot = r := hRoot
  rw [hRoot'] at hpH
  have hpK : K.toEGraph.Follows r w (F.onVertex x) :=
    H.follows_lift_restrictAlphabet A hpH hw
  have hSelf : K.SubalphabetReachable A r r :=
    K.subalphabetReachable_refl A r
  obtain ⟨hReach, hpSelected⟩ :=
    K.follows_lift_component A r hpK hw hSelf
  let y : (K.subalphabetComponentSubgraph A r).Vertex :=
    K.componentLiftVertex A r (F.onVertex x) hReach
  have hSelectedRoot :
      K.componentLiftVertex A r r hSelf =
        sourceLiteralY1SelectedRootOldPoint src dst base A root := by
    apply Subtype.ext
    rfl
  refine ⟨y, rfl, ?_⟩
  change (K.subalphabetComponentSubgraph A r).toEGraph.Follows
    (sourceLiteralY1SelectedRootOldPoint
      src dst base A root) w y
  rw [← hSelectedRoot]
  exact hpSelected

/-- FIRST RANK corrected ABO 4.7(ii) OLD-COMPONENT ROOT
COMPATIBILITY. For any chosen original old G A-word endpoint
x, the actual original normalized G[A] element produces
PRECISELY the tagged H old vertex of the corresponding genuine
H old rooted A-component, inside the TRUE printed completed
P_A stage quotient. No ambient H-coordinate injectivity. -/
theorem sourceLiteralY1X2AllSelectedRoot_oldAComponent_taggedCompatibility
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (gRoot x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (hRoot :
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex gRoot =
        (⟨root, by trivial⟩ :
          (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex))
    (w : LabelWord ι) (hw : LabelWord.Uses A w)
    (hp : ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).Follows
      gRoot w x) :
    ∃ (z : generatedSubgroup (sourceLiteralY1X2AllGenerator src dst) A)
      (y : (sourceLiteralY1DirectRootComponent
        src dst base A root).Vertex),
      (z : (sourceLiteralY1X2AllStage src dst).transitionGroup) =
        gRoot.1⁻¹ * x.1 ∧
      y.1 =
        ((sourceLiteralY1X2AllOriginalToY1Hom
          src dst base).onVertex x).1 ∧
      (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
        src dst base A hcard root
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root)).onVertex z =
        (sourceLiteralY1SelectedRootOldToPlainHom
          src dst base A hcard root).onVertex y := by
  obtain ⟨y, hY, hpH⟩ :=
    sourceLiteralY1X2AllOriginal_selectedOldH_APath_lift
      src dst base A root gRoot x hRoot w hw hp
  obtain ⟨z, hZ, hGStage⟩ :=
    sourceLiteralY1X2AllSelectedRoot_oldPath_fullLocalStage
      src dst base A hcard root gRoot x hRoot w hw hp
  refine ⟨z, y, hZ, hY, ?_⟩
  exact hGStage.trans
    (sourceLiteralY1SelectedRootOldToPlainHom_rootWord
      src dst base A hcard root y w hpH)

end ABO
end PSTSEPPA
