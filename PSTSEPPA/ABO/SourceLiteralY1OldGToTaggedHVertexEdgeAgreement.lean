import PSTSEPPA.ABO.SourceLiteralY1OldGToTaggedHCompatibility
import PSTSEPPA.ABO.ComponentSubgraphPaths
import PSTSEPPA.ABO.AmbientSkeletonAlphabetRestriction

/-!
# Actual G[A] old-component compatibility with ALL old signed H edge tokens

At the literal first corrected ABO rank, PR #637 proved that
the finite local Cayley(G[A]) cover, based at a true old G root,
takes each reachable old G point x to exactly the corresponding
true component-tagged old H point in the printed completed P_A stage.

An equality of VERTEX endpoints is not yet the assertion required
for an honest signed old graph covering. We now strengthen it:

* choose ANY actual G ORIGINAL A-component vertex x, with a TRUE
  A-path from the selected G root (not merely an ambient coset
  group element);
* choose ANY actual old directed signed A-edge e of the INCOMPLETE
  G original skeleton starting at x;
* project e by the literal original G->H cover to a TRUE original
  H old edge token, restrict to the REAL signed A-edges, and lift
  it into the chosen old H A-component, retaining the exact token;
* compare images under the genuine full local G[A] completed-stage
  cover and the true old H->P_A component-tagged quotient inclusion.

The vertex and ORIENTED EDGE images agree exactly as elements of
the printed completed P_A EGraph. No imaginary edges are inserted
into the ORIGINAL G or H skeleton and formal inverses, old loops
and possibly repeated/identity generators remain accounted for.

These are the precise old vertex/edge compatibility obligations
for the selected source old component of corrected ABO 4.7(ii).
They do not imply injection of the ambient H projection, full
G multi-coset embeddedness, R8 bridge freeness, Condition 5.2
or unconditional PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Remove the auxiliary word witness from the previous
source-rooted G/H compatibility theorem. This is the canonical
ALL-VERTICES interface on an intrinsic ORIGINAL G A-component,
not on the generally larger ambient left coset. -/
theorem sourceLiteralY1X2AllSelectedRoot_oldAComponent_allVertices_tagged
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (gRoot x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (hRoot :
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex gRoot =
        (⟨root, by trivial⟩ :
          (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex))
    (hReach :
      (sourceLiteralY1X2AllOriginalSkeleton src dst base).SubalphabetReachable
        A gRoot x) :
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
  obtain ⟨w, hw, hp⟩ := hReach
  exact sourceLiteralY1X2AllSelectedRoot_oldAComponent_taggedCompatibility
    src dst base A hcard root gRoot x hRoot w hw hp

/-- The decisive FULL SIGNED-EDGE compatibility on a selected old
G A-component. The true H old edge is exhibited explicitly, with
its EXACT underlying formal signed original H token, actual source
in the selected H A-component, and equality of both complete
P_A stage directed-edge images.

NO completion edge is asserted to exist in the original old
skeleton. The A-label hypothesis applies to this ACTUAL old e;
all other G original labels can remain missing. -/
theorem sourceLiteralY1X2AllSelectedRoot_oldAComponent_allEdges_tagged
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (gRoot x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (hRoot :
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex gRoot =
        (⟨root, by trivial⟩ :
          (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex))
    (hReach :
      (sourceLiteralY1X2AllOriginalSkeleton src dst base).SubalphabetReachable
        A gRoot x)
    (e : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Edge)
    (heSource :
      ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).source e = x)
    (heA :
      signedBase
        ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).label e ∈ A) :
    ∃ (z : generatedSubgroup (sourceLiteralY1X2AllGenerator src dst) A)
      (y : (sourceLiteralY1DirectRootComponent src dst base A root).Vertex)
      (eH : (sourceLiteralY1DirectRootComponent src dst base A root).Edge),
      (z : (sourceLiteralY1X2AllStage src dst).transitionGroup) =
        gRoot.1⁻¹ * x.1 ∧
      y.1 =
        ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex x).1 ∧
      eH.1 =
        ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onEdge e).1 ∧
      ((sourceLiteralY1DirectRootComponent src dst base A root).toEGraph).source eH =
        y ∧
      (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
        src dst base A hcard root
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root)).onVertex z =
        (sourceLiteralY1SelectedRootOldToPlainHom
          src dst base A hcard root).onVertex y ∧
      (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
        src dst base A hcard root
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root)).onEdge
          (z, ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).label e) =
        (sourceLiteralY1SelectedRootOldToPlainHom
          src dst base A hcard root).onEdge eH := by
  let G := sourceLiteralY1X2AllOriginalSkeleton src dst base
  let H := sourceLiteralY1DirectOriginalSkeleton src dst base
  let F := sourceLiteralY1X2AllOriginalToY1Hom src dst base
  let K := H.restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  let T := sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root
  let FG := sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
    src dst base A hcard root
      (sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root)
  let FH := sourceLiteralY1SelectedRootOldToPlainHom
    src dst base A hcard root
  obtain ⟨z, y, hZ, hY, hVertex⟩ :=
    sourceLiteralY1X2AllSelectedRoot_oldAComponent_allVertices_tagged
      src dst base A hcard root gRoot x hRoot hReach
  obtain ⟨w, hw, hp⟩ := hReach
  have hpH : H.toEGraph.Follows (F.onVertex gRoot) w (F.onVertex x) :=
    hp.map F
  have hr : F.onVertex gRoot = r := hRoot
  rw [hr] at hpH
  have hpK : K.toEGraph.Follows r w (F.onVertex x) :=
    H.follows_lift_restrictAlphabet A hpH hw
  have hReachH : K.SubalphabetReachable A r (F.onVertex x) :=
    ⟨w, hw, hpK⟩
  have heHA : signedBase ((H.toEGraph).label (F.onEdge e)) ∈ A := by
    rw [F.map_label e]
    exact heA
  let eK : K.Edge :=
    ⟨(F.onEdge e).1, ⟨(F.onEdge e).2, heHA⟩⟩
  have heKSource : K.toEGraph.source eK = F.onVertex x := by
    change H.toEGraph.source (F.onEdge e) = F.onVertex x
    calc
      H.toEGraph.source (F.onEdge e) =
          F.onVertex (G.toEGraph.source e) := F.map_source e
      _ = F.onVertex x := by rw [heSource]
  have heKReach : K.SubalphabetReachable A r (K.toEGraph.source eK) := by
    rw [heKSource]
    exact hReachH
  let eL : L.Edge := K.componentLiftEdge A r eK heHA heKReach
  have heLToken : (eL.1 : ActionEdge (sourceLiteralY1 src dst).transitionGroup ι) =
      (F.onEdge e).1 := rfl
  have heLSource : L.toEGraph.source eL = y := by
    apply Subtype.ext
    change (K.toEGraph.source eK).1 = y.1
    exact (congrArg Subtype.val heKSource).trans hY.symm
  have heLLabel : L.toEGraph.label eL = G.toEGraph.label e := by
    change H.toEGraph.label (F.onEdge e) = G.toEGraph.label e
    exact F.map_label e
  have hs :
      T.source (FG.onEdge (z, G.toEGraph.label e)) =
        T.source (FH.onEdge eL) := by
    calc
      T.source (FG.onEdge (z, G.toEGraph.label e)) =
          FG.onVertex z := FG.map_source _
      _ = FH.onVertex y := hVertex
      _ = T.source (FH.onEdge eL) := by
          rw [FH.map_source eL, heLSource]
  have hl :
      T.label (FG.onEdge (z, G.toEGraph.label e)) =
        T.label (FH.onEdge eL) := by
    calc
      T.label (FG.onEdge (z, G.toEGraph.label e)) =
          G.toEGraph.label e := FG.map_label _
      _ = L.toEGraph.label eL := heLLabel.symm
      _ = T.label (FH.onEdge eL) := (FH.map_label eL).symm
  refine ⟨z, y, eL, hZ, hY, heLToken, heLSource, hVertex, ?_⟩
  exact T.deterministic hs hl

end ABO
end PSTSEPPA
