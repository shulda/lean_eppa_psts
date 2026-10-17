import PSTSEPPA.ABO.SourceLiteralY1NormalizedOldRootAnchorAgreement
import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalRootedEmbeddingInputs
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootNormalizedLocalHFullCayleyCover

/-!
# Actual first-rank corrected ABO 4.7(ii): unconditional ROOTED COMPONENT embedding

Let H=T(Y₁) and G=T(X₂^all), with their genuinely certified
ONE-stable labelled quotient. For any ACTUAL original signed
old H root, a two-letter A, and the true local H[A] old
component and G[A] OLD signed pullback rooted at identity,
the completed H[A] P_A stage is covered by the ACTUAL finite
FULL signed Cayley(G[A]) construction.

The source-exact anchor comparison proves that this cover
sends the G[A] group identity to precisely the ORIGINAL H[A]
old component-tagged quotient image of the G[A] OLD pullback
identity (NOT merely to a vertex with the same ambient
group coordinate).

All hypotheses of the already verified ROOTED mixed B/C
support-gluing/embeddedness theorem can thus be discharged
using only:
* true generated and retractable local subgroups G[A], H[A];
* actual original incomplete A-skeletons and genuine G/A pullback;
* true 1-stability on all strictly proper B⊊A;
* weakly complete properly tagged P_A coset extensions;
* the full source-signed Cayley(G[A]) cover aligned on the
  exact OLD H component-tagged root.

The resulting finite rank-two G[A] P_A multi-coset extension
has an INJECTIVE ambient Cayley coordinate map on the
ENTIRE tagged attached-coset region rooted in ONE genuine
old G[A] A-component, including its FRESH coset points.

SCOPE: We do NOT claim that the entire disconnected
original G[A] pullback is connected, or that H-level
ambient group coordinates identify different old component
tags; we do NOT claim the globally unqualified
Theorem 4.7(ii)/(iii), G-external bridge-freeness,
R8 full-B-coset repair, Condition 5.2, higher rank,
or unconditional finite PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The TRUE finite full signed local Cayley(G[A]) stage cover
has the EXACT old component-tagged H[A] root required by
the source's rooted 4.7(ii) mechanism, not an ambient
coordinate substitute. Both real old G/H roots have
genuine original incomplete signed A-components. -/
theorem sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom_exactOldRoot
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom
      src dst base A hcard root).onVertex 1 =
    ((sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root).pullbackOldToWeakMultiCosetStageHom
        (sourceLiteralY1X2AllLocalQuotient src dst A)
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalHOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1Local_isGenerated src dst A)
        (sourceLiteralY1Local_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalHOld_weakComplete
          src dst base A hcard root)
        ∅
        (empty_mem_allProperCosetFamily A
          (Finset.card_pos.mp (by rw [hcard]; decide)))).onVertex
      (sourceLiteralY1SelectedLocalGOld_identity
        src dst base A root) := by
  calc
    (sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom
        src dst base A hcard root).onVertex 1 =
      (sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
        src dst base A hcard root).onVertex
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root) :=
      sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom_one
        src dst base A hcard root
    _ = sourceLiteralY1SelectedLocalHOld_anchor
          src dst base A hcard root :=
      sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom_oldAnchor
        src dst base A hcard root
    _ = _ :=
      sourceLiteralY1SelectedLocalHOld_anchor_eq_pullbackRoot
        src dst base A hcard root

/-- Literal rank-two corrected ABO Theorem 4.7(ii)
COMPONENT-SCOPED embeddedness statement with NO
additional Cayley-cover, root-compatibility, stability,
retractability, or admissibility assumptions. The
entire original G[A] proper-coset extension region
supported over ONE actual OLD intrinsic A-component
is embedded in the true ambient Cayley(G[A]).

The finite group G[A] is not required to be A-stable
over H[A] (only proper-B stability), and the full
original pullback may still have unrelated disconnected
old A-components. -/
theorem sourceLiteralY1SelectedLocal_rootedMultiCoset_injOn
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Set.InjOn
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetAmbientValue
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le))
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).rootedMultiCosetImage
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root)) := by
  exact sourceLiteralY1SelectedLocal_rootedMultiCoset_injOn_of_cover
    src dst base A hcard root
    (sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom
      src dst base A hcard root)
    (sourceLiteralY1X2AllSelectedRootNormalizedLocalHStageHom_exactOldRoot
      src dst base A hcard root)

end ABO
end PSTSEPPA
