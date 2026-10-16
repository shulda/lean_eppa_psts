import PSTSEPPA.ABO.KStablePullbackComponentGraphEquiv
import PSTSEPPA.ABO.SourceLiteralY1X2AllOriginalCover

/-!
# TRUE selected old A-components cover their entire H A-components, without 2-stability

For corrected ABO Theorem 4.7, the original incomplete
H-Cayley A-cover is a genuine disjoint union of rooted old
A-components. Pulling it back under a labelled quotient
Q:G↠H does NOT usually yield a connected old graph,
and Q need not be injective on the whole generated group G[A].

The correct all-rank conclusion requiring NO stability is:

* for any chosen true old G root r, the genuine original
  signed B-component of r maps SURJECTIVELY onto the
  genuine old H B-component of Q(r), on old VERTICES;
* the same component covers EVERY original formally
  oriented signed B-EDGE token with source in that
  H B-component, without adding missing old edges.

The vertex argument lifts the actual ORIGINAL B-word
from the prescribed upstairs root. For an old H edge,
first lift its SOURCE within the selected component,
then lift the particular original signed edge from
that precise point. The resulting signed edge source
is again in the selected old B-component.

These hold for arbitrary B, including B=∅, without
k-stability, global retractability, injectivity on
ambient cosets or faithfulness of generator labels.

At the actual first-rank groups
    G=T(X₂^all), H=T(Y₁),
we specialize to all two-letter original A-components.
This is a SURJECTIVE old A-cover, not a bijection
(that would wrongly require two-stability). For
proper B⊊A, by contrast, the independently certified
one-stability provides VERTEX AND EDGE equivalences.

This is a precise component-selection input for the
corrected source Theorem 4.7(ii) and the first rank
Definition-5.3 stage catalogue; it does not by itself
construct a rooted compatible completed-stage Cayley
map, handle augmented R8 B-bridges or conclude EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {E : Finset ι}

namespace CayleySubgraphSpec

/-- Canonical labelled old vertex projection on ONE
genuine intrinsic B-component. NO B-stability is used
and distinct upstairs old points can have equal image. -/
noncomputable def pullbackQuotient_intrinsicBComponentVertexMap
    (K : CayleySubgraphSpec genΔ E)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (root : (K.pullbackQuotient Q).Vertex) :
    {x : (K.pullbackQuotient Q).Vertex //
      (K.pullbackQuotient Q).SubalphabetReachable B root x} →
    {y : K.Vertex //
      K.SubalphabetReachable B
        ((K.pullbackQuotientHom Q).onVertex root) y} :=
  fun x =>
    ⟨(K.pullbackQuotientHom Q).onVertex x.1, by
      obtain ⟨w, hw, hp⟩ := x.2
      exact ⟨w, hw, hp.map (K.pullbackQuotientHom Q)⟩⟩

/-- EVERY genuine downstairs OLD B-component vertex has
an upstairs vertex in the same true B-component as
the CHOSEN old upstairs root, without ANY quotient
stability or global injectivity assumptions. -/
theorem pullbackQuotient_intrinsicBComponentVertexMap_surjective
    (K : CayleySubgraphSpec genΔ E)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (root : (K.pullbackQuotient Q).Vertex) :
    Function.Surjective
      (K.pullbackQuotient_intrinsicBComponentVertexMap Q B root) := by
  intro y
  obtain ⟨w, hw, hp⟩ := y.2
  obtain ⟨x, hxPath, hxMap⟩ :=
    K.pullbackQuotientHom_follows_lift Q hp root rfl
  refine ⟨⟨x, ⟨w, hw, hxPath⟩⟩, ?_⟩
  apply Subtype.ext
  exact hxMap

/-- EVERY original directed signed B-EDGE token with a
source in the chosen H B-component has an actual OLD
G B-edge lift whose source is in the CHOSEN G B-component.
This includes inverse signs, original loops, and B=∅.
It requires NO B-stability, in contrast to the
separately proved full B-component EDGE equivalence. -/
theorem pullbackQuotient_intrinsicBComponentEdgeMap_surjective_unstable
    (K : CayleySubgraphSpec genΔ E)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (root : (K.pullbackQuotient Q).Vertex) :
    Function.Surjective
      (K.pullbackQuotient_intrinsicBComponentEdgeMap Q B root) := by
  let L := K.pullbackQuotient Q
  let F := K.pullbackQuotientHom Q
  intro e
  obtain ⟨x, hxMap⟩ :=
    (K.pullbackQuotient_intrinsicBComponentVertexMap_surjective Q B root)
      (⟨K.toEGraph.source e.1, e.2.1⟩ :
        {y : K.Vertex // K.SubalphabetReachable B (F.onVertex root) y})
  have hxSource :
      F.onVertex x.1 = K.toEGraph.source e.1 :=
    congrArg Subtype.val hxMap
  obtain ⟨f, hfSource, hfMap⟩ :=
    K.pullbackQuotientHom_edge_lift Q e.1 x.1 hxSource
  have hfReach : L.SubalphabetReachable B root (L.toEGraph.source f) := by
    rw [hfSource]
    exact x.2
  have hfBase : signedBase (L.toEGraph.label f) ∈ B := by
    rw [← F.map_label f, hfMap]
    exact e.2.2
  refine ⟨⟨f, ⟨hfReach, hfBase⟩⟩, ?_⟩
  apply Subtype.ext
  exact hfMap

end CayleySubgraphSpec

variable {V : Type*}
variable [Fintype V] [DecidableEq V]

/-- The actual first-rank original signed G=T(X₂^all)
A-component maps SURJECTIVELY onto the chosen original
H=T(Y₁) A-component for every alphabet A, in
particular for the TWO-letter original source parents.
There is no claim of 2-stable injectivity. -/
theorem sourceLiteralY1X2AllOriginal_AComponentVertex_surjective
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex) :
    Function.Surjective
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).        pullbackQuotient_intrinsicBComponentVertexMap
          (sourceLiteralY1X2AllToY1 src dst) A root) :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).    pullbackQuotient_intrinsicBComponentVertexMap_surjective
      (sourceLiteralY1X2AllToY1 src dst) A root

/-- The exact first-rank original G A-component
covers ALL true H A-oriented signed edge tokens
with sources in the chosen original H A-component.
No non-original completed edge is introduced. -/
theorem sourceLiteralY1X2AllOriginal_AComponentEdge_surjective
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex) :
    Function.Surjective
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).        pullbackQuotient_intrinsicBComponentEdgeMap
          (sourceLiteralY1X2AllToY1 src dst) A root) :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).    pullbackQuotient_intrinsicBComponentEdgeMap_surjective_unstable
      (sourceLiteralY1X2AllToY1 src dst) A root

end ABO
end PSTSEPPA
