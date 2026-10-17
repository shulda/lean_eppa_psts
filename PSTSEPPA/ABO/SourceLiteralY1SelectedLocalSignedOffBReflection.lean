import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalSignedOldMultiCosetHom
import PSTSEPPA.ABO.PullbackMultiCosetFullConstituentReflection
import PSTSEPPA.ABO.RankTwoSingletonAugmentationInput

/-!
# True first-rank G[A] off-B points remain off-B in the ORIGINAL H[A] graph

The actual finite corrected ABO rank-one source has
  G = T(X₂^all) ↠ H = T(Y₁)
with one-stable labelled quotient, and |A|=2.

The H[A] old skeleton is the ORIGINAL incomplete signed
A-component of a genuine printed H root translated into
H[A]. The actual G[A] signed old skeleton is its genuine
Q_A pullback, possibly disconnected, and its exact full
P_A multiCE has independently indexed B-component tags.

We instantiate the fully certified generic theorem that
a G coset-extension point belongs to a full tagged B
constituent iff its TRUE H signed graph image does.
One-stability is sufficient for every proper B⊊A,
and full A-stability is NEVER assumed.

Consequently an original G[A] P_A quotient vertex lying
OFF all full B-cosets is mapped by the actual SIGNED
G[A]→H[A] old multiCE morphism to a genuine H[A] vertex
also OFF every full B-coset. Rank-two edge geometry then
proves that this H image has NO originally present
oriented signed B-edge, including negative tokens and
original loops.

This is exactly the legal input for attaching the
corrected ABO type-(2) new full H[B]-coset at the TRUE
H component-tagged image of a G off-B vertex; there
is no phantom H-side full-B alternative to address
in the rank-two original pullback case.

It does NOT yet identify the particular printed T(Y₁)
type-(2) catalogue index and the true global finite
G Cayley based map at the corresponding original G[A]
coordinate. These last source-specific compatibility
facts remain separate, along with distinct corrected R8,
4.7(iii), higher rank and final finite PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Source-exact equivalence of ACTUAL full B-constituent
membership for the signed original G[A] multiCE graph
and its TRUE component-indexed signed H[A] image.
This does not identify distinct old H components by
equality of their ambient H coordinates. -/
theorem sourceLiteralY1SelectedLocalGOldToH_full_B_iff
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
          src dst A hcard.le)) :
    (∃ p : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetInclude
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le) B hBP p = z) ↔
    (∃ q : (sourceLiteralY1SelectedLocalHOldSkeleton
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalHOldSkeleton
        src dst base A root).multiCosetInclude
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalHOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1Local_isGenerated src dst A)
        (sourceLiteralY1Local_retractable
          src dst A hcard.le) B hBP q =
      (sourceLiteralY1SelectedLocalGOldToHMultiCosetSignedHom
        src dst base A hcard root).onVertex z) := by
  let H := sourceLiteralY1SelectedLocalHOldSkeleton
    src dst base A root
  let Q := sourceLiteralY1X2AllLocalQuotient src dst A
  let P := allProperCosetFamily A
  let hAdmG := sourceLiteralY1SelectedLocalGOld_admissible
    src dst base A hcard root
  let hGenG := sourceLiteralY1X2AllLocal_isGenerated src dst A
  let hRetG := sourceLiteralY1X2AllLocal_retractable src dst A hcard.le
  let hAdmH := sourceLiteralY1SelectedLocalHOld_admissible
    src dst base A hcard root
  let hGenH := sourceLiteralY1Local_isGenerated src dst A
  let hRetH := sourceLiteralY1Local_retractable src dst A hcard.le
  have hStable : ∀ C : Finset ι, C ∈ P.alphabets → Q.StableAt C := by
    intro C hCP
    exact sourceLiteralY1SelectedLocalQuotient_properStable
      src dst A hcard C hCP
  exact H.pullbackQuotient_multiCosetToBase_full_B_iff
    Q P hAdmG hGenG hRetG hAdmH hGenH hRetH
    hStable B hBP z

/-- The actual selected G[A] proper multiCE vertex is OFF
the full B-constituent precisely if its real component-tagged
H[A] signed image is also OFF the full H B-constituent.
This uses only genuine Q_A one-stability on proper B. -/
theorem sourceLiteralY1SelectedLocalGOldToH_off_B_iff
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
          src dst A hcard.le)) :
    (¬ ∃ p : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetInclude
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le) B hBP p = z) ↔
    (¬ ∃ q : (sourceLiteralY1SelectedLocalHOldSkeleton
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalHOldSkeleton
        src dst base A root).multiCosetInclude
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalHOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1Local_isGenerated src dst A)
        (sourceLiteralY1Local_retractable
          src dst A hcard.le) B hBP q =
      (sourceLiteralY1SelectedLocalGOldToHMultiCosetSignedHom
        src dst base A hcard root).onVertex z) :=
  not_congr
    (sourceLiteralY1SelectedLocalGOldToH_full_B_iff
      src dst base A hcard root B hBP z)

end ABO
end PSTSEPPA
