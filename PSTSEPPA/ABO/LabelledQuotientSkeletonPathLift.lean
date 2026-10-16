import PSTSEPPA.ABO.LabelledQuotientSkeletonPullback
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Exact signed OLD path lifting for quotient-pullback Cayley skeletons

The corrected ABO Theorem 4.7 requires a genuinely labelled
G-cover L_G of an admissible H-skeleton L_H under a labelled
quotient G ↠ H. Pulling back a true INCOMPLETE H-Cayley skeleton
creates exactly the old signed edges, with no artificial
complete-action edges.

The previous module constructs the canonical pullback and
lifts ONE old directed edge from ANY chosen lift of its source.
We now induct over arbitrary chronological signed OLD paths:
from any selected point over their actual source, every H-path
has a G-pullback path with THE SAME signed word and an endpoint
over the specified H target.

The projection of such a lift is forced by the original path
and, because the pullback is deterministic, its endpoint is
unique after fixing the upstairs source and signed word.

This is the exact graph-cover/path-lifting interface needed
before comparing intrinsic subalphabet B-components in two
groups. It does NOT assert any embedding of completed
multi-coset extensions or Theorem 4.7 bridge freeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- An arbitrary genuine old chronological signed path in an
incomplete H-Cayley skeleton lifts from EVERY chosen source
point of its G-pullback, retaining exactly the original word,
each formal inverse token, and the specified downstairs
endpoint. Nothing is completed or adjoined here. -/
theorem pullbackQuotientHom_follows_lift
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    {u v : K.Vertex} {w : LabelWord ι}
    (hp : K.toEGraph.Follows u w v)
    (x : (K.pullbackQuotient Q).Vertex)
    (hx : (K.pullbackQuotientHom Q).onVertex x = u) :
    ∃ y : (K.pullbackQuotient Q).Vertex,
      ((K.pullbackQuotient Q).toEGraph).Follows x w y ∧
      (K.pullbackQuotientHom Q).onVertex y = v := by
  let L := K.pullbackQuotient Q
  let F := K.pullbackQuotientHom Q
  induction hp generalizing x with
  | nil u =>
      exact ⟨x, EGraph.Follows.nil x, hx⟩
  | @cons u v s w e hs hl hrest ih =>
      have hsrc : F.onVertex x = K.toEGraph.source e :=
        hx.trans hs.symm
      obtain ⟨f, hfsrc, hfmap⟩ :=
        K.pullbackQuotientHom_edge_lift Q e x hsrc
      have htarget :
          F.onVertex (L.toEGraph.target f) =
            K.toEGraph.target e := by
        calc
          F.onVertex (L.toEGraph.target f) =
              K.toEGraph.target (F.onEdge f) :=
            (F.map_target f).symm
          _ = K.toEGraph.target e := by rw [hfmap]
      obtain ⟨y, hyLift, hyMap⟩ :=
        ih (L.toEGraph.target f) htarget
      have hfLabel : L.toEGraph.label f = s := by
        calc
          L.toEGraph.label f =
              K.toEGraph.label (F.onEdge f) :=
            (F.map_label f).symm
          _ = K.toEGraph.label e := by rw [hfmap]
          _ = s := hl
      exact ⟨y, EGraph.Follows.cons f hfsrc hfLabel hyLift,
        hyMap⟩

/-- Two potential lifts of the SAME old signed path from the
SAME upstairs source have the SAME actual upstairs endpoint.
This is deterministic path uniqueness, even when the
whole group homomorphism is non-injective. -/
theorem pullbackQuotientHom_follows_endpoint_unique
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    {x y z : (K.pullbackQuotient Q).Vertex}
    {w : LabelWord ι}
    (hy : ((K.pullbackQuotient Q).toEGraph).Follows x w y)
    (hz : ((K.pullbackQuotient Q).toEGraph).Follows x w z) :
    y = z :=
  (K.pullbackQuotient Q).toEGraph.follows_right_unique hy hz

end CayleySubgraphSpec
end ABO
end PSTSEPPA
