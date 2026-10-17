import PSTSEPPA.ABO.SourceLiteralY1PrintedRootPAEqualsNormalizedAmbient
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootFullLocalCayleyCover
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainOldAnchorCover
import PSTSEPPA.ABO.RootedLocalPlainStageCatalogueAgreement

/-!
# True full signed G[A] Cayley cover of the NORMALIZED original H[A] stage

The already-certified literal first rank map is a FULL signed
surjection from Cayley(T(X₂^all)[A]) onto the actual printed
component-tagged original T(Y₁)-rooted P_A complete stage.

PR #641 establishes a source-exact identification of that
printed stage with the actual ambient-rooted multi-coset
completion obtained from the SAME literal original H skeleton,
with no ambient-coordinate tag collapse.

The independently certified bijective signed graph morphism
from the TRUE locally inverse-translated H[A] completed
multi-coset extension to its ambient original-root completion
has a signed inverse. Compose it with the actual source
local G[A] signed cover to obtain a CONCRETE FULL-CAYLEY MAP
into the precise normalized original H[A] stage:

  Cayley(T(X₂^all)[A]) -> printed rooted P_A stage
                             -> normalized H[A] P_A stage.

The composite is explicitly a labelled graph morphism,
based at exactly the inverse image of the REAL printed OLD
component-tagged anchor, and is SURJECTIVE on ALL genuine
stage vertices and ALL formal ORIENTED SIGNED EDGE tokens,
including the legally inserted fixed loops.

This now constructs the stage cover itself, not an abstract
hypothesized labelled quotient or an unjustified whole-H
ambient embedding. The next separate step is to identify
its exact normalized OLD anchor with the source-rooted
H[A] skeleton inclusion expected by corrected 4.7(ii);
only then can the embeddedness theorem be instantiated.
No R8 bridge freeness, higher induction or PSTS EPPA yet.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The genuine inverse signed stage isomorphism from
the LITERAL printed T(Y₁) selected P_A stage to
the selected genuine H[A]-normalized P_A stage.
Both the old/fresh tags and BOTH oriented signed edge
tokens are retained, rather than just H group values. -/
noncomputable def sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).toEGraph.toLabelledGraph
      (((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).rootedLocalAllProperCompletedStage A hcard
          (sourceLiteralY1_transitionTwoRetractable src dst)
          (⟨root, by trivial⟩ :
            ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).Vertex)
      ).toEGraph.toLabelledGraph := by
  let K := (sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceLiteralY1_transitionTwoRetractable src dst
  let f := K.rootedAllProperCompletedStageHom A hcard hret r
  have hb := K.rootedAllProperCompletedStageHom_bijective A hcard hret r
  exact f.inverseOfBijective hb.1 hb.2

/-- The exact inverse graph isomorphism covers EVERY actual
normalized H[A] stage VERTEX, including all fresh coset
points with their independent intrinsic component tags. -/
theorem sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom_vertex_surjective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Surjective
      (sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
        src dst base A hcard root).onVertex := by
  let K := (sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceLiteralY1_transitionTwoRetractable src dst
  let f := K.rootedAllProperCompletedStageHom A hcard hret r
  have hb := K.rootedAllProperCompletedStageHom_bijective A hcard hret r
  intro u
  refine ⟨f.onVertex u, ?_⟩
  exact f.inverseOfBijective_onVertex_apply hb.1 hb.2 u

/-- Same source-faithful surjectivity on each actual formal
SIGNED ORIENTED normalized H[A] stage EDGE, including
positive/negative stationary loops and moving old/fresh edges. -/
theorem sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom_edge_surjective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Surjective
      (sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
        src dst base A hcard root).onEdge := by
  let K := (sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceLiteralY1_transitionTwoRetractable src dst
  let f := K.rootedAllProperCompletedStageHom A hcard hret r
  have hb := K.rootedAllProperCompletedStageHom_bijective A hcard hret r
  intro e
  refine ⟨f.onEdge e, ?_⟩
  exact f.inverseOfBijective_onEdge_apply hb.1 hb.2 e

/-- Actual FULL labelled complete-Cayley(G[A]) cover of the
source-normalized original H[A] P_A stage, based at the
exact transported OLD component-tagged printed H root. -/
noncomputable def sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      (cayleyGraph (trivialCompletionGenerator
        (sourceLiteralY1X2AllGenerator src dst) A)).toEGraph.toLabelledGraph
      (((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).rootedLocalAllProperCompletedStage A hcard
          (sourceLiteralY1_transitionTwoRetractable src dst)
          (⟨root, by trivial⟩ :
            ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).Vertex)
      ).toEGraph.toLabelledGraph :=
  (sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
    src dst base A hcard root).comp
      (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
        src dst base A hcard root
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root))

/-- Normalization is exactly at the true OLD tagged H anchor,
transported through the genuine signed stage isomorphism.
No ambient H coordinate identification. -/
@[simp] theorem sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom_one
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom
      src dst base A hcard root).onVertex 1 =
    (sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
      src dst base A hcard root).onVertex
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root) := by
  change
    (sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
      src dst base A hcard root).onVertex
        ((sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
          src dst base A hcard root
          (sourceLiteralY1SelectedRootPlainOldAnchor
            src dst base A hcard root)).onVertex 1) =
      _
  rw [sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom_one]

/-- EVERY vertex of the actual local rooted P_A completed
H[A] stage is covered by some real local G[A] group point. -/
theorem sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom_vertex_surjective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Surjective
      (sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom
        src dst base A hcard root).onVertex := by
  let f := sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
    src dst base A hcard root
  let g := sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
    src dst base A hcard root
    (sourceLiteralY1SelectedRootPlainOldAnchor
      src dst base A hcard root)
  intro u
  obtain ⟨v, hv⟩ :=
    sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom_vertex_surjective
      src dst base A hcard root u
  obtain ⟨x, hx⟩ :=
    sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom_vertex_surjective
      src dst base A hcard root
      (sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root) v
  refine ⟨x, ?_⟩
  change f.onVertex (g.onVertex x) = u
  rw [hx]
  exact hv

/-- EVERY formal oriented SIGNED edge token of the true
completed H[A] stage is reached by a real full local
Cayley(G[A]) edge, including inverse and legal fixed loops. -/
theorem sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom_edge_surjective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Surjective
      (sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom
        src dst base A hcard root).onEdge := by
  let f := sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
    src dst base A hcard root
  let g := sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
    src dst base A hcard root
    (sourceLiteralY1SelectedRootPlainOldAnchor
      src dst base A hcard root)
  intro e
  obtain ⟨d, hd⟩ :=
    sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom_edge_surjective
      src dst base A hcard root e
  obtain ⟨c, hc⟩ :=
    sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom_edge_surjective
      src dst base A hcard root
      (sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root) d
  refine ⟨c, ?_⟩
  change f.onEdge (g.onEdge c) = e
  rw [hc]
  exact hd

end ABO
end PSTSEPPA
