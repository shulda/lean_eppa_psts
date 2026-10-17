import PSTSEPPA.ABO.SourceLiteralY1SelectedRootFullLocalCayleyCover
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainOldAnchorCover
import PSTSEPPA.ABO.LocalCompleteCayleyStageCoverGlobalAgreement
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Exact original OLD A-word coordinates inside the TRUE full local G[A] stage cover

Corrected ABO Theorem 4.7(ii) combines TWO different signed graphs:
* the actual INCOMPLETE original G skeleton and ONE of its true OLD
  A-connected components, rooted at an original G point `gRoot`;
* the legally completed, component-tagged H-level P_A stage, whose
  based full local Cayley(G[A]) cover sends 1 to the true OLD H anchor.

The global original skeleton may have multiple disconnected A-components.
We must use `gRoot⁻¹ * x` only when x is reached by a REAL old signed
A-path from gRoot. This is a genuine member of G[A], independent of the
global quotient's injectivity on G[A].

First prove that every actual incomplete Cayley-skeleton word path
gRoot --w--> x has exactly the group displacement evalGroup(w).
Then combine it with the already checked local/full signed Cayley
agreement: the TRUE full local stage cover evaluated at that group
displacement ends precisely at the selected completed-stage point
reached by w from the actual OLD tagged H anchor.

We include the genuine oriented signed edge token (x,s): its image
is exactly the completed-stage s-edge at that word endpoint. This
handles both signs, old loops, repeated or identity generators, and
missing other original edges without inserting any edge in the old
skeleton.

This is the SOURCE ROOT-NORMALIZATION / OLD WORD bridge. It deliberately
does NOT yet identify the image point with the paper's exact tagged
OLD H image of x; that further component-tagged old-inclusion
naturality is the remaining gate to apply the component-scoped
embedding theorem. Nor does it prove R8, Condition 5.2, or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

/-- An ACTUALLY REALISED word in an incomplete signed Cayley skeleton
has exactly its expected ambient group displacement. This is not a
claim that arbitrary complete Cayley words lie in the old skeleton. -/
theorem oldPath_evalGroup_eq_root_inv_mul
    (K : CayleySubgraphSpec gen S)
    (root x : K.Vertex) (w : LabelWord ι)
    (hp : (K.toEGraph).Follows root w x) :
    PSTS.SignedWord.evalGroup gen w = root.1⁻¹ * x.1 := by
  have hMapped :
      (cayleyGraph gen).toEGraph.Follows root.1 w x.1 :=
    hp.map K.inclusion
  have hEnd :
      (cayleyGraph gen).followWord root.1 w = x.1 :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord root.1 w) hMapped
  have hMul : root.1 * PSTS.SignedWord.evalGroup gen w = x.1 := by
    calc
      root.1 * PSTS.SignedWord.evalGroup gen w =
          (cayleyGraph gen).followWord root.1 w :=
        (cayleyGraph.followWord_eq_mul_evalGroup gen root.1 w).symm
      _ = x.1 := hEnd
  calc
    PSTS.SignedWord.evalGroup gen w =
        root.1⁻¹ * (root.1 * PSTS.SignedWord.evalGroup gen w) := by simp
    _ = root.1⁻¹ * x.1 :=
      congrArg (fun y : Γ => root.1⁻¹ * y) hMul

variable {V Edge : Type*}

/-- Root-normalize ANY genuine old B-word path, retain its TRUE
local-group coordinate z=gRoot⁻¹*x in G[B], and evaluate the SAME
word in the actual COMPLETE local Cayley(G[B]) stage cover.
The complete stage is independent of the original old skeleton;
the conclusion is an exact signed-word formula, not a claimed
embedding of the old component-tagged graph. -/
theorem oldPath_fullLocalStage_vertex
    (K : CayleySubgraphSpec gen S)
    (T : CompleteEGraph V Edge ι)
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (B : Finset ι)
    (hOutside : ∀ i : ι, i ∉ B → T.transitionSubgroupGenerator i = 1)
    (root x : K.Vertex) (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hp : (K.toEGraph).Follows root w x)
    (u : V) :
    ∃ z : generatedSubgroup gen B,
      (z : Γ) = root.1⁻¹ * x.1 ∧
      (T.localGeneratedCayleyStageHom Q B hOutside u).onVertex z =
        T.followWord u w := by
  have hz : root.1⁻¹ * x.1 ∈ generatedSubgroup gen B :=
    K.subalphabetReachable_implies_coset B root x ⟨w, hw, hp⟩
  let z : generatedSubgroup gen B := ⟨root.1⁻¹ * x.1, hz⟩
  refine ⟨z, rfl, ?_⟩
  calc
    (T.localGeneratedCayleyStageHom Q B hOutside u).onVertex z =
      (T.cayleyProjectionFromGroup gen Q.hom Q.map_gen u).onVertex (z : Γ) :=
        T.localGeneratedCayleyStageHom_vertex_eq_global Q B hOutside u z
    _ = (T.cayleyProjectionFromGroup gen Q.hom Q.map_gen u).onVertex
          (PSTS.SignedWord.evalGroup gen w) := by
      exact congrArg
        (T.cayleyProjectionFromGroup gen Q.hom Q.map_gen u).onVertex
        (K.oldPath_evalGroup_eq_root_inv_mul root x w hp).symm
    _ = T.followWord u w :=
      T.cayleyProjectionFromGroup_evalGroup gen Q.hom Q.map_gen u w

/-- Strong signed-edge version: at a TRUE ORIGINAL old edge e
leaving the old-word endpoint x, the local completed-stage
projection sends its formal signed label to the UNIQUE
same-label stage edge leaving the reached completed-stage point.
The edge e itself is not silently completed or fabricated. -/
theorem oldPath_fullLocalStage_edge
    (K : CayleySubgraphSpec gen S)
    (T : CompleteEGraph V Edge ι)
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (B : Finset ι)
    (hOutside : ∀ i : ι, i ∉ B → T.transitionSubgroupGenerator i = 1)
    (root x : K.Vertex) (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hp : (K.toEGraph).Follows root w x)
    (e : K.Edge) (_he : (K.toEGraph).source e = x)
    (u : V) :
    ∃ z : generatedSubgroup gen B,
      (z : Γ) = root.1⁻¹ * x.1 ∧
      (T.localGeneratedCayleyStageHom Q B hOutside u).onVertex z =
        T.followWord u w ∧
      (T.localGeneratedCayleyStageHom Q B hOutside u).onEdge
          (z, (K.toEGraph).label e) =
        T.edgeAt (T.followWord u w) ((K.toEGraph).label e) := by
  obtain ⟨z, hz, hVertex⟩ :=
    K.oldPath_fullLocalStage_vertex T Q B hOutside root x w hw hp u
  refine ⟨z, hz, hVertex, ?_⟩
  let F := T.localGeneratedCayleyStageHom Q B hOutside u
  have hs :
      T.source (F.onEdge (z, (K.toEGraph).label e)) =
        T.followWord u w := by
    calc
      T.source (F.onEdge (z, (K.toEGraph).label e)) =
          F.onVertex z := F.map_source _
      _ = T.followWord u w := hVertex
  have hl :
      T.label (F.onEdge (z, (K.toEGraph).label e)) =
        (K.toEGraph).label e := F.map_label _
  exact (T.edgeAt_eq hs hl).symm

end CayleySubgraphSpec

variable {W : Type*}
variable [Fintype W] [DecidableEq W]

/-- SOURCE-FACING old-root specialization: start from one G=T(X₂^all)
point above the CHOSEN original printed H=T(Y₁) root, follow ONLY
real ORIGINAL signed A-edges, and evaluate the normalized local
G[A] coordinate in the ACTUAL printed fully completed P_A stage.
The completed-stage base vertex is EXACTLY the old component-tagged
H quotient anchor, not an ambient H-coordinate surrogate. -/
theorem sourceLiteralY1X2AllSelectedRoot_oldPath_fullLocalStage
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (gRoot x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (_hRoot :
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex gRoot =
        (⟨root, by trivial⟩ :
          (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex))
    (w : LabelWord ι) (hw : LabelWord.Uses A w)
    (hp : ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).Follows
      gRoot w x) :
    ∃ z : generatedSubgroup (sourceLiteralY1X2AllGenerator src dst) A,
      (z : (sourceLiteralY1X2AllStage src dst).transitionGroup) =
        gRoot.1⁻¹ * x.1 ∧
      (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
        src dst base A hcard root
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root)).onVertex z =
        (sourceLiteralY1SelectedRootPlainCompleteStage
          src dst base A hcard root).followWord
          (sourceLiteralY1SelectedRootPlainOldAnchor
            src dst base A hcard root) w := by
  exact
    (sourceLiteralY1X2AllOriginalSkeleton src dst base).oldPath_fullLocalStage_vertex
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root)
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root)
      A
      (sourceLiteralY1SelectedRootPlain_transitionOutsideA_one
        src dst base A hcard root)
      gRoot x w hw hp
      (sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root)

/-- The stronger SOURCE result includes each original directed signed
G edge leaving the selected old A-path endpoint; its completed-stage
image is the exact formally oriented edge at the reached H stage
vertex. This is edge-token equality, not only reachability. -/
theorem sourceLiteralY1X2AllSelectedRoot_oldPath_fullLocalStage_edge
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (gRoot x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (_hRoot :
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex gRoot =
        (⟨root, by trivial⟩ :
          (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex))
    (w : LabelWord ι) (hw : LabelWord.Uses A w)
    (hp : ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).Follows
      gRoot w x)
    (e : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Edge)
    (he : ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).source e = x) :
    ∃ z : generatedSubgroup (sourceLiteralY1X2AllGenerator src dst) A,
      (z : (sourceLiteralY1X2AllStage src dst).transitionGroup) =
        gRoot.1⁻¹ * x.1 ∧
      (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
        src dst base A hcard root
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root)).onVertex z =
        (sourceLiteralY1SelectedRootPlainCompleteStage
          src dst base A hcard root).followWord
          (sourceLiteralY1SelectedRootPlainOldAnchor
            src dst base A hcard root) w ∧
      (sourceLiteralY1X2AllSelectedRootPlainFullLocalCayleyHom
        src dst base A hcard root
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root)).onEdge
          (z, ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).label e) =
        (sourceLiteralY1SelectedRootPlainCompleteStage
          src dst base A hcard root).edgeAt
            ((sourceLiteralY1SelectedRootPlainCompleteStage
              src dst base A hcard root).followWord
              (sourceLiteralY1SelectedRootPlainOldAnchor
                src dst base A hcard root) w)
            (((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).label e) := by
  exact
    (sourceLiteralY1X2AllOriginalSkeleton src dst base).oldPath_fullLocalStage_edge
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root)
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root)
      A
      (sourceLiteralY1SelectedRootPlain_transitionOutsideA_one
        src dst base A hcard root)
      gRoot x w hw hp e he
      (sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root)

end ABO
end PSTSEPPA
