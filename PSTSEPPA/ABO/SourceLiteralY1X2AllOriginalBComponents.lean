import PSTSEPPA.ABO.KStablePullbackIntrinsicBComponents
import PSTSEPPA.ABO.SourceLiteralY1X2AllOriginalCover
import Mathlib.Data.Finset.Card

/-!
# Exact original G/H signed B-components at the literal first rank

The accepted first-rank printed group tower has a genuine
surjective ONE-STABLE labelled quotient

      G = T(X₂^all)  ↠  H = T(Y₁).

Both actual ORIGINAL-EDGE signed Cayley skeletons L_G
and L_H were constructed (without X₁-completed fake
edges), and L_G is the exact quotient-pullback of L_H.

For every actual signed alphabet B of size ≤1, every
pair of L_G points INSIDE THE SAME ambient G[B]-coset
is connected by a REAL original B-path upstairs iff
the image points are connected by a REAL original
B-path downstairs. This is the genuine, input-specific
first-rank version of the generic two-group component
reflection theorem.

At an actual rank-two A with B⊊A, the size premise
is automatic. The SAME-G[B]-coset premise is essential:
different intrinsic source-component tags can share
the same ambient H-coordinate, but are never collapsed
by this theorem.

This establishes precisely the component-level
comparison used to begin corrected ABO Theorem 4.7(i)
at k=1, not yet the extension-to-Cayley G-level
embedding or full bridge-freeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Actual original signed B-component correspondence
between the literal second group G=T(X₂^all) and the
literal first expanded group H=T(Y₁), restricted to
points in ONE same generated G[B] left coset.
No artificial original edges and no component-tag collapse. -/
theorem sourceLiteralY1X2AllOriginal_BReachable_iff
    (src dst : ι → V) (base : V)
    (B : Finset ι) (hB : B.card ≤ 1)
    (x y : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (hyCoset :
      y.1 ∈ generatedLeftCoset
        (sourceLiteralY1X2AllGenerator src dst) B x.1) :
    (sourceLiteralY1X2AllOriginalSkeleton src dst base).SubalphabetReachable B x y ↔
    (sourceLiteralY1DirectOriginalSkeleton src dst base).SubalphabetReachable B
          ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex x)
          ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex y) := by
  exact
    (sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotient_subalphabetReachable_iff_of_kStable
      (sourceLiteralY1X2AllToY1 src dst)
      1 (sourceLiteralY1X2AllToY1_oneStable src dst)
      B hB x y hyCoset

/-- Source-exact corrected rank-two specialization: every
strictly proper B⊊A has at most one generator; therefore
the ACTUAL G/H original signed B-component reflection
is unconditional on k-stability beyond the already
certified first-rank 1-stability. -/
theorem sourceLiteralY1X2AllOriginal_rankTwoProperBReachable_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hA : A.card = 2)
    (B : Finset ι) (hBA : B ⊂ A)
    (x y : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (hyCoset :
      y.1 ∈ generatedLeftCoset
        (sourceLiteralY1X2AllGenerator src dst) B x.1) :
    (sourceLiteralY1X2AllOriginalSkeleton src dst base).SubalphabetReachable B x y ↔
    (sourceLiteralY1DirectOriginalSkeleton src dst base).SubalphabetReachable B
          ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex x)
          ((sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex y) := by
  have hB : B.card ≤ 1 := by
    have hlt : B.card < 2 := by
      calc
        B.card < A.card := Finset.card_lt_card hBA
        _ = 2 := hA
    exact Nat.lt_succ_iff.mp hlt
  exact sourceLiteralY1X2AllOriginal_BReachable_iff
    src dst base B hB x y hyCoset

end ABO
end PSTSEPPA
