import PSTSEPPA.ABO.LocalCompleteCayleyStageCover
import PSTSEPPA.ABO.SourceLiteralY1X2AllExactCayleyRanges
import PSTSEPPA.ABO.SourceLiteralY1X2AllPrintedPlainTransitionQuotient

/-!
# An ACTUAL local complete signed Cayley stage cover is a restriction of the GLOBAL cover

In corrected ABO Theorem 4.7(ii), the local group G[A]
must act on the legally completed true H-level P_A stage
by precisely the same signed transitions as the full
global group G. Independent surjective local and global
covers do NOT suffice if they disagree on the original
old signed graph.

We establish exact naturality:

For a generator-preserving surjection Q:G↠Transition(T)
whose actual signed stage transitions outside A act by 1,
the local COMPLETE stage Cayley cover built from the
genuine generated subgroup G[A] agrees on EVERY group
VERTEX and EVERY FORMAL ORIENTED SIGNED EDGE with the
restriction of the already-proved GLOBAL Cayley(G)→T
based cover. The ambient edge token embedding is

    (x,s) ∈ G[A] × SignedLabel ι ↦ ((x: G),s) ∈ G × SignedLabel ι,

retaining both formal inverse signs and stationary loops.

The proof uses the exact Q.subgroupHom underlying-value
identity: this is an actual group-hom restriction,
not just word-reachability or a matching ambient H value.

Specialize to the TRUE literal first-rank source
G=T(X₂^all), selected paper T(Y₁) original rooted P_A
stage and its ALREADY certified group-transition quotient.
The sole extra local-stage hypothesis is genuinely
stationary outside-A transitions; the precise source
theorem is separately staged (#631). Once it is available,
this identifies the local COMPLETE Cayley(G[A]) hom with
the old global based G-stage hom on all old/fresh tagged
stage vertices and directed signed edge images.

This equality supports the remaining true G/H original
old-component rooted compatibility, but DOES NOT claim
the whole corrected Thm 4.7(ii)/(iii), bridge-freeness,
full B-coset R8 alternative or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)
variable {gen : ι → Γ}

/-- The group value of the true G[A]-local stage
transition hom is exactly Q of the original
underlying group value, with no further quotient. -/
@[simp] theorem localGeneratedStageTransitionHom_apply
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (A : Finset ι) (x : generatedSubgroup gen A) :
    T.localGeneratedStageTransitionHom Q A x = Q.hom x.1 :=
  rfl

/-- Full signed local Cayley(G[A]) COVER and global
Cayley(G) COVER agree on the exact selected vertex x.
All original component tags are preserved by the
stage action. -/
theorem localGeneratedCayleyStageHom_vertex_eq_global
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (A : Finset ι)
    (hOutside : ∀ i : ι, i ∉ A → T.transitionSubgroupGenerator i = 1)
    (u : V) (x : generatedSubgroup gen A) :
    (T.localGeneratedCayleyStageHom Q A hOutside u).onVertex x =
      (T.cayleyProjectionFromGroup gen Q.hom Q.map_gen u).onVertex x.1 := by
  rw [T.localGeneratedCayleyStageHom,
      T.cayleyProjectionFromGroup_onVertex,
      T.cayleyProjectionFromGroup_onVertex,
      T.localGeneratedStageTransitionHom_apply Q A x]

/-- Equality extends to EVERY FORMAL directed signed edge
token (x,s), even when its signed letter is outside A
and both local and stage actions have stationary loops.
No artificial original-input old edge is asserted. -/
theorem localGeneratedCayleyStageHom_edge_eq_global
    (Q : LabelledGroupQuotient gen T.transitionSubgroupGenerator)
    (A : Finset ι)
    (hOutside : ∀ i : ι, i ∉ A → T.transitionSubgroupGenerator i = 1)
    (u : V)
    (e : ActionEdge (generatedSubgroup gen A) ι) :
    (T.localGeneratedCayleyStageHom Q A hOutside u).onEdge e =
      (T.cayleyProjectionFromGroup gen Q.hom Q.map_gen u).onEdge
        ((e.1 : Γ), e.2) := by
  rw [T.localGeneratedCayleyStageHom,
      T.cayleyProjectionFromGroup_onEdge,
      T.cayleyProjectionFromGroup_onEdge,
      T.localGeneratedStageTransitionHom_apply Q A e.1]

end CompleteEGraph

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- TRUE original printed stage instance: once the
actual stage's outside-A stationary transitions
are certified, the independently constructed complete
local G[A] action agrees on EVERY vertex coordinate
with the earlier genuine global T(X₂^all) based cover. -/
theorem sourceLiteralY1X2AllPrintedPlainLocal_cover_vertex_eq_global
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A)))
    (hOutside :
      ∀ i : ι, i ∉ A →
        (sourceLiteralY1SelectedRootPlainCompleteStage
          src dst base A hcard root).transitionSubgroupGenerator i = 1)
    (x : generatedSubgroup
      (sourceLiteralY1X2AllGenerator src dst) A) :
    ((sourceLiteralY1SelectedRootPlainCompleteStage
      src dst base A hcard root).localGeneratedCayleyStageHom
        (sourceLiteralY1X2AllToPrintedPlainStage
          src dst base A hcard root) A hOutside u).onVertex x =
    (sourceLiteralY1X2AllPrintedPlainCayleyHom
      src dst base A hcard root u).onVertex x.1 :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).localGeneratedCayleyStageHom_vertex_eq_global
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root) A hOutside u x

/-- The same source-faithful restriction identity for
all actual ORIENTED SIGNED Cayley(G[A]) edge tokens,
including formal negatives and fixed outside-A loops. -/
theorem sourceLiteralY1X2AllPrintedPlainLocal_cover_edge_eq_global
    (src dst : ι → W) (base : W)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u : Quotient
      (sourceLiteralY1DirectRootMultiCosetSetoid
        src dst base A hcard root (allProperCosetFamily A)))
    (hOutside :
      ∀ i : ι, i ∉ A →
        (sourceLiteralY1SelectedRootPlainCompleteStage
          src dst base A hcard root).transitionSubgroupGenerator i = 1)
    (e : ActionEdge
      (generatedSubgroup (sourceLiteralY1X2AllGenerator src dst) A) ι) :
    ((sourceLiteralY1SelectedRootPlainCompleteStage
      src dst base A hcard root).localGeneratedCayleyStageHom
        (sourceLiteralY1X2AllToPrintedPlainStage
          src dst base A hcard root) A hOutside u).onEdge e =
    (sourceLiteralY1X2AllPrintedPlainCayleyHom
      src dst base A hcard root u).onEdge
        ((e.1 : (sourceLiteralY1X2AllStage src dst).transitionGroup), e.2) :=
  (sourceLiteralY1SelectedRootPlainCompleteStage
    src dst base A hcard root).localGeneratedCayleyStageHom_edge_eq_global
      (sourceLiteralY1X2AllToPrintedPlainStage
        src dst base A hcard root) A hOutside u e

end ABO
end PSTSEPPA
