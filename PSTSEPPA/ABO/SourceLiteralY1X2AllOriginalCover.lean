import PSTSEPPA.ABO.LabelledQuotientSkeletonPathLift
import PSTSEPPA.ABO.SourceLiteralY1CanonicalOriginalCover
import PSTSEPPA.ABO.SourceLiteralY1X2AllRankOne

/-!
# The actual literal second transition group's ORIGINAL incomplete graph cover

Theorem 4.7 of corrected ABO compares a G-level cover L_G
of an H-level original-input cover L_H. At the first rank
the real finite group is NOT an abstract placeholder:

  G := T(X₂^all),       H := T(Y₁),
  Q := the already-certified 1-stable labelled G ↠ H.

The genuine original input signed edge preimage inside
H=T(Y₁) was already constructed DIRECTLY using the literal
paper Y₁ and excludes all artificial X₁ completion edges.

We now define the equally genuine G-level old-edge preimage
by pulling back that H-skeleton along the REAL Q. This is
a literal CayleySubgraphSpec over G: it has all G points
but ONLY the exact original signed edges. Compose its
canonical H-cover with H→E_original to obtain an actual
G-cover of the original incomplete input EGraph.

Every true original signed edge and arbitrary signed old
path lifts from ANY selected G-cover source point, with
exactly the same signed labels and final input vertex.
No fictitious complete-action edges or coset-tag folding
are added. This is the precise L_G/L_H base geometry
needed before the rank-two pulled-back component and
multi-coset extension comparison in corrected Theorem 4.7.

The statements do not yet prove G-level coset-extension
embeddedness, admissibility or bridge-freeness; those
are the remaining substantial induction obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- True ORIGINAL-input signed-edge preimage inside the
ACTUAL printed finite T(X₂^all), obtained by the exact
1-stable group quotient to literal paper T(Y₁).
No X₁-only completion edge survives this pullback. -/
noncomputable def sourceLiteralY1X2AllOriginalSkeleton
    (src dst : ι → V) (base : V) :
    CayleySubgraphSpec
      (sourceLiteralY1X2AllGenerator src dst) Finset.univ :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotient
    (sourceLiteralY1X2AllToY1 src dst)

/-- The genuine graph covering L_G → L_H on REAL
old signed vertices and oriented edge tokens. -/
noncomputable def sourceLiteralY1X2AllOriginalToY1Hom
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).toLabelledGraph
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).toEGraph).toLabelledGraph :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotientHom
    (sourceLiteralY1X2AllToY1 src dst)

/-- Compose literal G-level to H-level cover with the
independently certified H-level → ORIGINAL INCOMPLETE
input EGraph morphism, preserving formal signs. -/
noncomputable def sourceLiteralY1X2AllOriginalToInputHom
    (src dst : ι → V) (base : V) :
    LabelledGraphHom
      ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).toLabelledGraph
      (sourceInputEGraph src dst).toLabelledGraph :=
  (sourceLiteralY1DirectOriginalHom src dst base).comp
    (sourceLiteralY1X2AllOriginalToY1Hom src dst base)

/-- Every ACTUAL original literal H=T(Y₁) old preimage
vertex has a true G=T(X₂^all) old preimage point.
No representative of an intrinsic A-component is chosen. -/
theorem sourceLiteralY1X2AllOriginalToY1_vertex_surjective
    (src dst : ι → V) (base : V) :
    Function.Surjective
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotientHom_vertex_surjective
    (sourceLiteralY1X2AllToY1 src dst)

/-- Every actual oriented signed ORIGINAL H-cover edge
has an equally genuine G-cover edge above it,
including geometric loops, inverse signs and missing
other original labels. -/
theorem sourceLiteralY1X2AllOriginalToY1_edge_surjective
    (src dst : ι → V) (base : V) :
    Function.Surjective
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onEdge :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotientHom_edge_surjective
    (sourceLiteralY1X2AllToY1 src dst)

/-- Every genuine original INPUT signed edge has an
actual G-level old preimage edge starting at ANY
selected G-cover vertex over its source. The
formal edge token and signed label are preserved. -/
theorem sourceLiteralY1X2AllOriginal_edge_lift
    (src dst : ι → V) (base : V)
    (s : SignedLabel ι)
    (x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (hx :
      (sourceLiteralY1X2AllOriginalToInputHom src dst base).onVertex x =
        (sourceInputEGraph src dst).source s) :
    ∃ e : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Edge,
      ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).source e = x ∧
      (sourceLiteralY1X2AllOriginalToInputHom src dst base).onEdge e = s := by
  let K := sourceLiteralY1DirectOriginalSkeleton src dst base
  let F := sourceLiteralY1X2AllOriginalToY1Hom src dst base
  let H := sourceLiteralY1DirectOriginalHom src dst base
  have hxH : H.onVertex (F.onVertex x) =
      (sourceInputEGraph src dst).source s := hx
  obtain ⟨e, hesrc, hemap⟩ :=
    sourceLiteralY1DirectOriginal_edge_lift
      src dst base s (F.onVertex x) hxH
  have hxK :
      (K.pullbackQuotientHom
        (sourceLiteralY1X2AllToY1 src dst)).onVertex x =
      (K.toEGraph).source e := hesrc.symm
  obtain ⟨f, hfsrc, hfmap⟩ :=
    K.pullbackQuotientHom_edge_lift
      (sourceLiteralY1X2AllToY1 src dst) e x hxK
  refine ⟨f, hfsrc, ?_⟩
  calc
    (sourceLiteralY1X2AllOriginalToInputHom src dst base).onEdge f =
        H.onEdge (F.onEdge f) := rfl
    _ = H.onEdge e := congrArg H.onEdge hfmap
    _ = s := hemap

/-- Every REAL original input chronological signed path
lifts from every actual printed G=T(X₂^all) point lying
over its start, and its G-level endpoint projects to
the prescribed final input point. This is two-stage
old-graph path lifting, not completion. -/
theorem sourceLiteralY1X2AllOriginal_follows_lift
    (src dst : ι → V) (base : V)
    {u v : V} {w : LabelWord ι}
    (hp : (sourceInputEGraph src dst).Follows u w v)
    (x : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex)
    (hx :
      (sourceLiteralY1X2AllOriginalToInputHom src dst base).onVertex x = u) :
    ∃ y : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex,
      ((sourceLiteralY1X2AllOriginalSkeleton src dst base).toEGraph).Follows x w y ∧
      (sourceLiteralY1X2AllOriginalToInputHom src dst base).onVertex y = v := by
  let K := sourceLiteralY1DirectOriginalSkeleton src dst base
  let F := sourceLiteralY1X2AllOriginalToY1Hom src dst base
  let H := sourceLiteralY1DirectOriginalHom src dst base
  have hxH : H.onVertex (F.onVertex x) = u := hx
  obtain ⟨z, hzPath, hzMap⟩ :=
    sourceLiteralY1DirectOriginal_follows_lift
      src dst base hp (F.onVertex x) hxH
  have hxK :
      (K.pullbackQuotientHom
        (sourceLiteralY1X2AllToY1 src dst)).onVertex x =
      (F.onVertex x) := rfl
  obtain ⟨y, hyPath, hyMap⟩ :=
    K.pullbackQuotientHom_follows_lift
      (sourceLiteralY1X2AllToY1 src dst) hzPath x hxK
  refine ⟨y, hyPath, ?_⟩
  change H.onVertex (F.onVertex y) = v
  have hF : F.onVertex y = z := hyMap
  calc
    H.onVertex (F.onVertex y) = H.onVertex z :=
      congrArg H.onVertex hF
    _ = v := hzMap

end ABO
end PSTSEPPA
