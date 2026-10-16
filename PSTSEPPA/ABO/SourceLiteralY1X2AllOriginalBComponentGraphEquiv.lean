import PSTSEPPA.ABO.KStablePullbackComponentGraphEquiv
import PSTSEPPA.ABO.SourceLiteralY1X2AllOriginalCover
import PSTSEPPA.ABO.SourceLiteralY1X2AllOriginalBComponents
import Mathlib.Data.Finset.Card

/-!
# Literal original-input B-component signed graph equivalences in G₂→H₁

The actual printed first-rank group tower has G=T(X₂^all),
H=T(Y₁) and the verified labelled one-stable quotient Q:G↠H.
Their TRUE ORIGINAL incomplete signed edge preimage covers
L_G and L_H were constructed without adding any artificial
X₁ completion edges; L_G is exactly Q⁻¹(L_H).

We now specialize the ALL-RANK intrinsic old B-component
isomorphism to the first-rank true source input. For each
|B|≤1 and an actual chosen old group point x in L_G,
the canonical old graph covering L_G→L_H is a BIJECTION
on the entire genuine B-path component VERTEX carrier
and on EVERY formally oriented signed B-EDGE token
with source in that component.

In particular these equivalences hold for every
proper B⊊A when the real parent has |A|=2.
They preserve B-component tags and inverse edge tokens,
including original input loops, repeated labels and
disconnected input graph components.

This provides exact paper first-rank ORIGINAL cover
component geometry for later corrected Theorem 4.7
full tagged coset-extension embedding. It does NOT
equate distinct B-components sharing one H ambient
coordinate, nor prove the remaining mixed-support
collision or B-bridge exclusion for the full G-multiCE.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The full genuine old-input component vertices
for the actual literal G₂→H₁ projection correspond
bijectively over any singleton/empty B-alphabet.
Not just ambient cosets: the old paths are required. -/
noncomputable def sourceLiteralY1X2AllOriginal_BComponentVertexEquiv
    (src dst : ι → V) (base : V)
    (B : Finset ι) (hB : B.card ≤ 1)
    (x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex) :
    {y : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex //
      (sourceLiteralY1X2AllOriginalSkeleton src dst base).SubalphabetReachable B x y} ≃
    {z : (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex //
      (sourceLiteralY1DirectOriginalSkeleton src dst base).SubalphabetReachable B
        ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex x) z} :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotient_intrinsicBComponentEquiv
      (sourceLiteralY1X2AllToY1 src dst)
      B ((sourceLiteralY1X2AllToY1_oneStable src dst) B hB) x

/-- All genuine OLD oriented signed B-edge tokens in
one original G₂ B-component map bijectively to the
actual original H₁ B-component edge tokens. Both
formal inverse labels are kept, even on old loops. -/
noncomputable def sourceLiteralY1X2AllOriginal_BComponentEdgeEquiv
    (src dst : ι → V) (base : V)
    (B : Finset ι) (hB : B.card ≤ 1)
    (x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex) :
    (sourceLiteralY1X2AllOriginalSkeleton src dst base).IntrinsicBEdgeAt B x ≃
      (sourceLiteralY1DirectOriginalSkeleton src dst base).IntrinsicBEdgeAt B
        ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex x) :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotient_intrinsicBComponentEdgeEquiv
      (sourceLiteralY1X2AllToY1 src dst)
      B ((sourceLiteralY1X2AllToY1_oneStable src dst) B hB) x

/-- At any genuine rank-two parent A all proper
B⊊A are singleton or empty. These are precisely
the original proper-coset constituent fibres used
to form the full P_A extension in corrected ABO. -/
theorem rankTwoProper_card_le_one
    (A B : Finset ι) (hA : A.card = 2) (hBA : B ⊂ A) :
    B.card ≤ 1 := by
  have hlt : B.card < 2 := by
    calc
      B.card < A.card := Finset.card_lt_card hBA
      _ = 2 := hA
  exact Nat.lt_succ_iff.mp hlt

/-- Source-exact old signed B-vertex component
equivalence for any proper B⊊A, |A|=2, without
an extra 1-stability assumption (already certified). -/
noncomputable def sourceLiteralY1X2AllOriginal_rankTwoBVertexEquiv
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hA : A.card = 2)
    (B : Finset ι) (hBA : B ⊂ A)
    (x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex) :
    {y : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex //
      (sourceLiteralY1X2AllOriginalSkeleton src dst base).SubalphabetReachable B x y} ≃
    {z : (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex //
      (sourceLiteralY1DirectOriginalSkeleton src dst base).SubalphabetReachable B
        ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex x) z} :=
  sourceLiteralY1X2AllOriginal_BComponentVertexEquiv
    src dst base B (rankTwoProper_card_le_one A B hA hBA) x

/-- Source-exact oriented signed old edge-component
equivalence for every proper B⊊A at the first
nontrivial rank, including negative signed loops. -/
noncomputable def sourceLiteralY1X2AllOriginal_rankTwoBEdgeEquiv
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hA : A.card = 2)
    (B : Finset ι) (hBA : B ⊂ A)
    (x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex) :
    (sourceLiteralY1X2AllOriginalSkeleton src dst base).IntrinsicBEdgeAt B x ≃
      (sourceLiteralY1DirectOriginalSkeleton src dst base).IntrinsicBEdgeAt B
        ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex x) :=
  sourceLiteralY1X2AllOriginal_BComponentEdgeEquiv
    src dst base B (rankTwoProper_card_le_one A B hA hBA) x

end ABO
end PSTSEPPA
