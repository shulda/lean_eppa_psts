import PSTSEPPA.ABO.SourceOriginalH1BasepointTranslation
import PSTSEPPA.ABO.SourceOriginalH1PathValueNormalization

/-!
# Canonical H₁ basepoint translation OVER THE ORIGINAL INPUT GRAPH

A signed labelled isomorphism of abstract H₁ preimage graphs is
not enough for corrected ABO Definition 5.3. It must also
commute with the actual covering projections into the ORIGINAL
incomplete oriented input EGraph, not the artificially
completed initial X₁ action.

The first rank source preimage at orbit(base,t) is carried to
the one at base by left multiplication h ↦ t*h. We verify the
two commuting diagrams on original projected vertices and on
ALL formal directed signed edge tokens. This is a genuine
morphism of labelled covers over the fixed original input,
with no choice of coset representatives.

Every pair of original input vertices joined by a REAL signed
input path has such a group element t (the actual H₁ value of
that path), so its based preimage covers are isomorphic over
the original input graph. We do not assume the whole input
is connected, or identify different disconnected components.

This settles the basepoint-change part of the source rank-one
cover-index comparison only. Stage augmentations, Definition
5.3 catalogue equality, Condition 5.2, Theorem 4.7 and final
unconditional PSTS EPPA remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Actual source H₁ basepoint translation commutes STRICTLY
with projection of every tagged original-preimage vertex
to the ORIGINAL input vertex; this is not an equation merely
between abstract Cayley ambient coordinates. -/
theorem sourceH1OriginalSkeleton_translate_over_input_vertex
    (src dst : ι → V) (base : V) (t : SourceH1 src dst)
    (x : (sourceH1OriginalSkeleton src dst
      (sourceH1Orbit src dst base t)).Vertex) :
    (sourceH1OriginalSkeletonHom src dst base).onVertex
        ((sourceH1OriginalSkeleton_translateHom src dst base t).onVertex x) =
      (sourceH1OriginalSkeletonHom src dst
        (sourceH1Orbit src dst base t)).onVertex x := by
  change sourceH1Orbit src dst base (t * x.1) =
    sourceH1Orbit src dst
      (sourceH1Orbit src dst base t) x.1
  exact sourceH1Orbit_mul src dst base t x.1

/-- The SAME cover-commutation property holds on EVERY
actual original oriented signed edge token, including inverse
formal edges, geometric loops, and repeated labels. No
extra artificial edge from complete X₁ is introduced. -/
theorem sourceH1OriginalSkeleton_translate_over_input_edge
    (src dst : ι → V) (base : V) (t : SourceH1 src dst)
    (e : (sourceH1OriginalSkeleton src dst
      (sourceH1Orbit src dst base t)).Edge) :
    (sourceH1OriginalSkeletonHom src dst base).onEdge
        ((sourceH1OriginalSkeleton_translateHom src dst base t).onEdge e) =
      (sourceH1OriginalSkeletonHom src dst
        (sourceH1Orbit src dst base t)).onEdge e :=
  rfl

/-- If u and v are joined by ANY genuine original signed
input path, the group-word value of that path changes the
H₁ covering basepoint from u to v. The resulting literal
left-translation homomorphism is bijective on both complete
old-vertex and original oriented-edge token carriers, and
commutes with the covering projection into the original
input graph by the two preceding theorems.

This is intentionally stated without global connectedness:
an unrelated input component need not be in the orbit. -/
theorem sourceH1_original_connected_basepoints_are_cover_isomorphic
    (src dst : ι → V)
    {u v : V} {w : LabelWord ι}
    (hpath : (sourceInputEGraph src dst).Follows u w v) :
    ∃ t : SourceH1 src dst,
      sourceH1Orbit src dst u t = v ∧
      Function.Bijective
        (sourceH1OriginalSkeleton_translateHom src dst u t).onVertex ∧
      Function.Bijective
        (sourceH1OriginalSkeleton_translateHom src dst u t).onEdge := by
  let t := PSTS.SignedWord.evalGroup
    (sourceH1Generator src dst) w
  refine ⟨t, ?_, ?_⟩
  · exact sourceH1_original_path_orbit_evalGroup src dst hpath
  · exact sourceH1OriginalSkeleton_translateHom_bijective
      src dst u t

end ABO
end PSTSEPPA
