import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalSignedOldMultiCosetHom
import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalSignedOffBReflection
import PSTSEPPA.ABO.SourceLiteralY1LocalHOffBPrintedType2Index
import PSTSEPPA.ABO.RootedSourceMultiCosetCompletedEGraphIso

/-!
# True signed G[A] original multiCE → LITERAL printed H=T(Y₁) old stage

The first-rank G=T(X₂^all) signed ORIGINAL locally rooted
P_A multi-coset extension has already been mapped by a real
labelled signed graph morphism into the NORMALIZED H[A]
original P_A multiCE. But the actual finite Section-5
type-(2) augmented stages are indexed by the old
component-tagged ORIGINAL printed ambient T(Y₁) rooted
P_A quotient, not the H[A] representative.

The independently certified ROOTED local H[A]→ambient
original H signed multiCE isomorphism preserves genuine
component tags, all true old/fresh oriented edge tokens,
both formal inverse orientations and exact signed labels.
Compose the two REAL morphisms to obtain an ACTUAL signed
G[A]-multiCE→ORIGINAL-paper-H-old-multiCE map.

This is exactly the original OLD graph morphism M required
for the corrected ABO Theorem 4.7(iii) type-(2) augmented
B-orbit detector, with its OLD H carrier literally the
source graph of the printed type-(2) augmented completed
stage — NOT an auxiliary isomorphic or ambient-only graph.

For ANY G[A] old/fresh quotient vertex outside a genuine
full B-constituent, apply actual stable pullback off-B
reflection to its H[A] image, then the certified true
local H[A]→printed original H type-(2) index transport.
The OLD tagged vertex of this selected genuine printed
stage is EXACTLY the vertex M sends the given G point to.

This is a vertex-index and true signed old graph result.
The remaining source input is the correctly ROOT-BASED
finite global G Cayley cover and its compatibility
with the true local G[A] original signed Cayley embedding.
No false whole-pullback connectedness, global H coordinate
injectivity or outside-A completed original edge is used.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The TRUE original source-finite G[A] old/fresh signed
multiCE graph maps to the ACTUAL PRINTED T(Y₁) rooted
incomplete P_A OLD multiCE EGraph, preserving ALL real
orientations, formal inverses, and exact signed labels.

It is not a fictitious direct group-coordinate map or
an original X₁ graph with unproved completed edges. -/
noncomputable def sourceLiteralY1SelectedLocalGOldToPrintedSignedHom
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
      (sourceLiteralY1SelectedRootCompletedEGraph
        src dst base A hcard root
        (allProperCosetFamily A)).toLabelledGraph := by
  let K := (sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceLiteralY1_transitionTwoRetractable src dst
  let P := allProperCosetFamily A
  exact (K.rootedMultiCosetCompletedEGraphHom
    A hcard hret r P).comp
      (sourceLiteralY1SelectedLocalGOldToHMultiCosetSignedHom
        src dst base A hcard root)

/-- Any actual original signed G[A] multiCE quotient point
OFF its complete B-constituent determines a concrete
ORIGINAL PRINTED T(Y₁) type-(2) stage index.

The index is obtained by true G→H tagged signed morphism,
1-stability off-B reflection, and genuine root-local
H[A]→printed old signed stage normalization.
No independent new type-(2) universe is invented. -/
noncomputable def sourceLiteralY1SelectedLocalGOffB_toPrintedType2
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).MultiCosetVertex
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le))
    (hOff : ¬ ∃ p : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetInclude
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le) B hBP p = z) :
    LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP :=
  sourceLiteralY1SelectedLocalHOffB_toPrintedType2
    src dst base A hcard root B hBP
    ((sourceLiteralY1SelectedLocalGOldToHMultiCosetSignedHom
      src dst base A hcard root).onVertex z)
    ((sourceLiteralY1SelectedLocalGOldToH_off_B_iff
      src dst base A hcard root B hBP z).mp hOff)

/-- The actual printed type-(2) augmentation's OLD
component-tagged attachment root is EXACTLY the image
of its genuine original signed G[A] multiCE root
under the SOURCE old graph morphism constructed above.

This compares real old quotient vertices, not merely the
possibly non-injective original H group-coordinate map. -/
theorem sourceLiteralY1SelectedLocalGOffB_toPrintedType2_oldRoot
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).MultiCosetVertex
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le))
    (hOff : ¬ ∃ p : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetInclude
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le) B hBP p = z) :
    (sourceLiteralY1SelectedLocalGOffB_toPrintedType2
      src dst base A hcard root B hBP z hOff).vertex =
      (sourceLiteralY1SelectedLocalGOldToPrintedSignedHom
        src dst base A hcard root).onVertex z := by
  rfl

end ABO
end PSTSEPPA
