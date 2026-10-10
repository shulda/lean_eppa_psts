import PSTSEPPA.ABO.UnaryDetectorSynchronizedCover
import PSTSEPPA.ABO.LabelledQuotientSkeletonPathLifting
import PSTSEPPA.ABO.FiniteActionStages

/-!
# A concrete finite rank-one algebraic H₁ cover of every Γ-Cayley skeleton

For an ARBITRARY finite, finitely generated labelled group Γ, the
unary synchronized group H is already certified:
  H ↠ Γ is a true 1-stable labelled quotient;
  H is 2-retractable;
  H is finite if Γ is finite.

The labelled-quotient pullback and unique signed-path-lifting theorems
convert this algebraic construction into a GENUINE finite directed
graph cover of ANY incomplete Γ-Cayley A-skeleton K.

The lifted H-Cayley graph retains exactly the actual preimage
vertices and existing signed edges of K. Its covering morphism is
surjective on both sorts, has the unique edge/path lifting property
at every chosen starting vertex, and maps every intrinsic
C-component ONTO the corresponding component of K for ALL C.

This package is a mathematically concrete rank-one H₁-style
algebraic/group-cover replacement. It does not assert that its
permutation group and finite complete-stage family coincide with
the special Y₁/T(Y₁) construction in the ABO source paper.
The exact source Z₁, R2/Condition 5.2 and later levels remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A literal Cayley SUBGRAPH of the constructed unary H₁ group:
take exactly the preimages of the vertices and actual signed edges
of K under the certified 1-stable group quotient H₁ ↠ Γ. -/
noncomputable abbrev unaryH1CoverSkeleton
    (hgen : IsGenerated gen) :=
  K.pullbackQuotient (unarySynchronizedCoverQuotient gen hgen)

/-- The canonical, genuinely surjective labelled graph morphism
of the preceding actual incomplete Cayley pullback to K. -/
noncomputable abbrev unaryH1CoverHom
    (hgen : IsGenerated gen) :=
  K.pullbackQuotientHom (unarySynchronizedCoverQuotient gen hgen)

/-- Every original K vertex has a genuine lift in the unary H₁
graph (not merely in its ambient group). -/
theorem unaryH1CoverHom_vertex_surjective
    (hgen : IsGenerated gen) :
    Function.Surjective (K.unaryH1CoverHom hgen).onVertex :=
  K.pullbackQuotientHom_vertex_surjective
    (unarySynchronizedCoverQuotient gen hgen)

/-- Every old oriented signed edge has a genuine H₁ graph lift,
including inverses, geometric loops and repeated labels. -/
theorem unaryH1CoverHom_edge_surjective
    (hgen : IsGenerated gen) :
    Function.Surjective (K.unaryH1CoverHom hgen).onEdge :=
  K.pullbackQuotientHom_edge_surjective
    (unarySynchronizedCoverQuotient gen hgen)

/-- For any specified lift x, any original signed path starting
at its image lifts along the SAME signed word and has exactly
ONE endpoint above the original endpoint. -/
theorem unaryH1Cover_follows_lift_unique
    (hgen : IsGenerated gen)
    {u v : K.Vertex} {w : LabelWord ι}
    (hp : (K.toEGraph).Follows u w v)
    (x : (K.unaryH1CoverSkeleton hgen).Vertex)
    (hx : (K.unaryH1CoverHom hgen).onVertex x = u) :
    ∃! y : (K.unaryH1CoverSkeleton hgen).Vertex,
      ((K.unaryH1CoverSkeleton hgen).toEGraph).Follows x w y ∧
      (K.unaryH1CoverHom hgen).onVertex y = v :=
  K.pullbackQuotient_follows_lift_unique
    (unarySynchronizedCoverQuotient gen hgen) hp x hx

/-- The EXACT intrinsic C-reachable component downstairs
equals the image of the ACTUAL C-component of each selected
H₁-cover vertex. There is no replacement by ambient group cosets. -/
theorem unaryH1Cover_subalphabetReachable_iff
    (hgen : IsGenerated gen)
    (C : Finset ι)
    (x : (K.unaryH1CoverSkeleton hgen).Vertex)
    (v : K.Vertex) :
    K.SubalphabetReachable C
        ((K.unaryH1CoverHom hgen).onVertex x) v ↔
      ∃ y : (K.unaryH1CoverSkeleton hgen).Vertex,
        (K.unaryH1CoverSkeleton hgen).SubalphabetReachable C x y ∧
        (K.unaryH1CoverHom hgen).onVertex y = v :=
  K.pullbackQuotient_subalphabetReachable_iff
    (unarySynchronizedCoverQuotient gen hgen) C x v

variable [Finite Γ]

/-- The TRUE vertex set of the pulled-back incomplete H₁
skeleton is finite, even when K is disconnected. -/
theorem finite_unaryH1CoverSkeleton_vertices
    (hgen : IsGenerated gen) :
    Finite (K.unaryH1CoverSkeleton hgen).Vertex := by
  classical
  letI : Finite (UnarySynchronizedCover gen) :=
    finite_unarySynchronizedCover gen
  infer_instance

/-- Its REAL signed directed edge tokens are finite as well.
The finite alphabet includes both positive and inverse tokens. -/
theorem finite_unaryH1CoverSkeleton_edges
    (hgen : IsGenerated gen) :
    Finite (K.unaryH1CoverSkeleton hgen).Edge := by
  classical
  letI : Finite (UnarySynchronizedCover gen) :=
    finite_unarySynchronizedCover gen
  letI : Fintype (UnarySynchronizedCover gen) := Fintype.ofFinite _
  letI : Fintype (ActionEdge (UnarySynchronizedCover gen) ι) :=
    inferInstance
  infer_instance

end CayleySubgraphSpec
end ABO
end PSTSEPPA
