import PSTSEPPA.ABO.SourceOriginalH1PreimageSkeleton

/-!
# Exact original-graph signed paths in the first genuine H₁ Cayley preimage

The original incomplete input EGraph has precisely its named positive
edges and their formal inverses. The initial complete X₁ action has
additional artificial edges, and MUST NOT be used as if all of those
extra edges belonged to the original input.

For any actual signed ORIGINAL input path u --w--> v, the canonical
original-edge H₁ preimage graph lifts that very path from the identity
above u. The lift ends at exactly the signed group-word value of w
in the actual first-rank H₁, not at an arbitrarily chosen point of an
ambient H₁ coset. Consequently that group value projects to v.

This is a source-facing path-normalization gate for eventually showing
that arbitrary connected original H₁-cover components belong to the
source-indexed rank-one Z₁ stage family. It does not claim the still-open
cover selection/exhaustiveness theorem, a completed-coset equivalence,
or any higher-rank geometry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Every ACTUAL signed path in the true original-edge H₁ Cayley
preimage obeys the exact Cayley group-word endpoint formula,
including inverse letters, stationary loops, and repeated labels.
This only assumes a realized old-edge path: no X₁-completion edge
is inserted. -/
theorem sourceH1OriginalSkeleton_follows_group_value
    (src dst : ι → V) (base : V)
    {x y : (sourceH1OriginalSkeleton src dst base).Vertex}
    {w : LabelWord ι}
    (hp : (sourceH1OriginalSkeleton src dst base).toEGraph.Follows x w y) :
    x.1 * PSTS.SignedWord.evalGroup
      (sourceH1Generator src dst) w = y.1 := by
  let K := sourceH1OriginalSkeleton src dst base
  have hpCayley :
      (cayleyGraph (sourceH1Generator src dst)).toEGraph.Follows
        x.1 w y.1 :=
    hp.map K.inclusion
  have hCanonical :=
    (cayleyGraph (sourceH1Generator src dst)).follows_followWord x.1 w
  have hEnd :=
    (cayleyGraph (sourceH1Generator src dst)).toEGraph.follows_right_unique
      hCanonical hpCayley
  rw [cayleyGraph.followWord_eq_mul_evalGroup] at hEnd
  exact hEnd

/-- Every genuine signed path in the ORIGINAL (incomplete)
input graph u --w--> v lifts from group identity in its
corresponding actual original-edge H₁ preimage. Its exact
lifted group endpoint is the chronological signed-word value.
No arbitrary path representative, artificial X₁ edge or
coset-coordinate identification is used. -/
theorem sourceH1OriginalSkeleton_original_path_lift_value
    (src dst : ι → V)
    {u v : V} {w : LabelWord ι}
    (hp : (sourceInputEGraph src dst).Follows u w v) :
    ∃ y : (sourceH1OriginalSkeleton src dst u).Vertex,
      (sourceH1OriginalSkeleton src dst u).toEGraph.Follows
        (⟨1, by trivial⟩ : (sourceH1OriginalSkeleton src dst u).Vertex) w y ∧
      y.1 = PSTS.SignedWord.evalGroup
        (sourceH1Generator src dst) w ∧
      (sourceH1OriginalSkeletonHom src dst u).onVertex y = v := by
  let K := sourceH1OriginalSkeleton src dst u
  let root : K.Vertex := ⟨1, by trivial⟩
  have hroot :
      (sourceH1OriginalSkeletonHom src dst u).onVertex root = u :=
    sourceH1OriginalSkeleton_identity_base src dst u
  obtain ⟨y, hy, hyval⟩ :=
    sourceH1OriginalSkeleton_follows_lift src dst u hp root hroot
  have hGroup :=
    sourceH1OriginalSkeleton_follows_group_value src dst u hy
  have hExact :
      y.1 = PSTS.SignedWord.evalGroup
        (sourceH1Generator src dst) w := by
    simpa only [root, one_mul] using hGroup.symm
  exact ⟨y, hy, hExact, hyval⟩

/-- A realized original input signed path ends at the
projection of its EXACT H₁ word value. This gives a canonical
path-to-group normalization useful for classifying original
cover components, without invoking any extra X₁ edge. -/
theorem sourceH1_original_path_orbit_evalGroup
    (src dst : ι → V)
    {u v : V} {w : LabelWord ι}
    (hp : (sourceInputEGraph src dst).Follows u w v) :
    sourceH1Orbit src dst u
      (PSTS.SignedWord.evalGroup (sourceH1Generator src dst) w) = v := by
  obtain ⟨y, _hy, hg, hv⟩ :=
    sourceH1OriginalSkeleton_original_path_lift_value src dst hp
  change sourceH1Orbit src dst u y.1 = v at hv
  exact hg ▸ hv

/-- As a direct original-graph consequence, two REAL paths
from the same input vertex whose signed words agree in the
actual first-rank H₁ must have the same endpoint. This
does not assert either path exists just because an X₁-word
value happens to take u to its endpoint. -/
theorem sourceH1_original_paths_group_value_endpoint_unique
    (src dst : ι → V)
    {u v z : V} {p q : LabelWord ι}
    (hp : (sourceInputEGraph src dst).Follows u p v)
    (hq : (sourceInputEGraph src dst).Follows u q z)
    (heq : PSTS.SignedWord.evalGroup (sourceH1Generator src dst) p =
      PSTS.SignedWord.evalGroup (sourceH1Generator src dst) q) :
    v = z := by
  calc
    v = sourceH1Orbit src dst u
          (PSTS.SignedWord.evalGroup (sourceH1Generator src dst) p) :=
      (sourceH1_original_path_orbit_evalGroup src dst hp).symm
    _ = sourceH1Orbit src dst u
          (PSTS.SignedWord.evalGroup (sourceH1Generator src dst) q) :=
      congrArg (sourceH1Orbit src dst u) heq
    _ = z := sourceH1_original_path_orbit_evalGroup src dst hq

end ABO
end PSTSEPPA
