import PSTSEPPA.ABO.PullbackMultiCosetSignedGraphNaturality
import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalRootedAmbientEmbedding
import PSTSEPPA.ABO.SourceLiteralY1NormalizedOldRootAnchorAgreement

/-!
# Source-specific TRUE first-rank original signed G[A]→H[A] multiCE morphism

The corrected ABO first-rank genuine finite group tower is
  G = T(X₂^all)   ↠   H = T(Y₁)
with actual original INPUT signed incomplete old edges.

For |A|=2 we use the TRUE inverse-root-translated original H[A]
old A-component and the exact original signed G[A] Q-pullback,
which may be disconnected. The attached multiCE family is ALL
proper B⊊A, with separately indexed B-component coset copies
and genuine source+FULL-SIGNED-LABEL edge gluing.

We instantiate the independently checked general signed
pullback multiCE morphism without any new assumptions.
This is an HONEST LabelledGraphHom, not a vertex map:
on EVERY originally present signed old edge and EVERY fresh
full B-coset signed edge its map preserves source,
both formal inverse orientations, signed labels and targets.

Moreover its image of the exact selected original G[A]
OLD identity vertex is the exact normalized H[A] OLD
component-tagged full P_A anchor, not merely its group
coordinate. The complete signed old map is now available
for the based type-(2) off-B augmented stage compatibility
of corrected 4.7(iii).

The further remaining source-specific input is to choose
the ACTUAL literal printed (B,z)-type-(2) completed stage
and corresponding G[A]-Cayley cover with its identity
correctly based at that very OLD tagged H[z] point.
Use the connectedness of the SELECTED A-region only,
not the generally disconnected original G[A] pullback.
The H-full-B-image alternative also needs separate
genuine old B path lifting. None is hidden here.

No new global H-ambient injection, false A-stability,
invented old edge, full 4.7(iii)/R8, higher induction,
Condition 5.2, or PSTS EPPA is claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The entire actual first-rank OLD multiCE source morphism
from G=T(X₂^all)[A] to H=T(Y₁)[A], on true original
signed edges AND all freshly completed coset signed edges.
No hidden original G[A] connectedness assumption. -/
noncomputable def sourceLiteralY1SelectedLocalGOldToHMultiCosetSignedHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetEGraph
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le)).toLabelledGraph
      ((sourceLiteralY1SelectedLocalHOldSkeleton
        src dst base A root).multiCosetEGraph
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalHOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1Local_isGenerated src dst A)
        (sourceLiteralY1Local_retractable
          src dst A hcard.le)).toLabelledGraph :=
  (sourceLiteralY1SelectedLocalHOldSkeleton
    src dst base A root).pullbackQuotient_multiCosetSignedHom
    (sourceLiteralY1X2AllLocalQuotient src dst A)
    (allProperCosetFamily A)
    (sourceLiteralY1SelectedLocalGOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1X2AllLocal_isGenerated src dst A)
    (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
    (sourceLiteralY1SelectedLocalHOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1Local_isGenerated src dst A)
    (sourceLiteralY1Local_retractable src dst A hcard.le)

/-- The ACTUAL source signed multiCE OLD morphism sends the
genuine original G[A]-pullback identity via its TRUE old
B=empty skeleton inclusion to exactly the chosen OLD H[A]
component-tagged normalized P_A anchor.

This is the concrete source compatibility on the OLD root,
stronger than equality of G/H ambient group values. -/
theorem sourceLiteralY1SelectedLocalGOldToHMultiCosetSignedHom_oldRoot
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalGOldToHMultiCosetSignedHom
      src dst base A hcard root).onVertex
      (((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).skeletonToMultiCosetHom
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le)
          ∅
          (empty_mem_allProperCosetFamily A
            (Finset.card_pos.mp (by rw [hcard]; decide)))).onVertex
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root)) =
    sourceLiteralY1SelectedLocalHOld_anchor
      src dst base A hcard root := by
  let H := sourceLiteralY1SelectedLocalHOldSkeleton
    src dst base A root
  let Q := sourceLiteralY1X2AllLocalQuotient src dst A
  let P := allProperCosetFamily A
  let hAdmG := sourceLiteralY1SelectedLocalGOld_admissible
    src dst base A hcard root
  let hGenG := sourceLiteralY1X2AllLocal_isGenerated src dst A
  let hRetG := sourceLiteralY1X2AllLocal_retractable
    src dst A hcard.le
  let hAdmH := sourceLiteralY1SelectedLocalHOld_admissible
    src dst base A hcard root
  let hGenH := sourceLiteralY1Local_isGenerated src dst A
  let hRetH := sourceLiteralY1Local_retractable src dst A hcard.le
  let hEmpty : (∅ : Finset ι) ∈ P.alphabets :=
    empty_mem_allProperCosetFamily A
      (Finset.card_pos.mp (by rw [hcard]; decide))
  let gRoot := sourceLiteralY1SelectedLocalGOld_identity
    src dst base A root
  let hRoot := sourceLiteralY1SelectedLocalHOld_identity
    src dst base A root
  have hMap : (H.pullbackQuotientHom Q).onVertex gRoot = hRoot := by
    apply Subtype.ext
    change Q.hom (1 : generatedSubgroup
      (sourceLiteralY1X2AllGenerator src dst) A) =
      (1 : generatedSubgroup
        (sourceLiteralY1 src dst).transitionSubgroupGenerator A)
    exact map_one Q.hom
  have hNaturality :=
    H.pullbackQuotient_multiCosetSignedHom_oldVertex
      Q P hAdmG hGenG hRetG hAdmH hGenH hRetH
      ∅ hEmpty gRoot
  change
    (sourceLiteralY1SelectedLocalGOldToHMultiCosetSignedHom
      src dst base A hcard root).onVertex
      (((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).skeletonToMultiCosetHom
          P hAdmG hGenG hRetG ∅ hEmpty).onVertex gRoot) =
    (H.skeletonToMultiCosetHom
      P hAdmH hGenH hRetH ∅ hEmpty).onVertex
      ((H.pullbackQuotientHom Q).onVertex gRoot)
      at hNaturality
  rw [hMap] at hNaturality
  change
    (sourceLiteralY1SelectedLocalGOldToHMultiCosetSignedHom
      src dst base A hcard root).onVertex
      (((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).skeletonToMultiCosetHom
          P hAdmG hGenG hRetG ∅ hEmpty).onVertex gRoot) =
    sourceLiteralY1SelectedLocalHOld_anchor
      src dst base A hcard root at hNaturality
  exact hNaturality

end ABO
end PSTSEPPA
