import PSTSEPPA.ABO.LabelledQuotientSkeletonPullback
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Exact path lifting for pullbacks of incomplete Cayley skeletons

For a surjective labelled group quotient Q : H ↠ Γ, the preceding
construction provides a true directed-graph covering of EVERY genuine
incomplete Γ-Cayley skeleton K: the H-pullback has precisely the
preimages of the old vertices and signed directed edges.

Here we prove the strong covering property needed by the corrected
ABO Y₁/H₁ geometrical construction.

* Every genuine old signed path lifts from EVERY chosen preimage of
  its starting vertex, with precisely the same signed word.
* The lifted endpoint is UNIQUE (the pullback is deterministic).
* An old signed path starting at Q(x) exists iff an actual lifted
  signed path starting at x exists and projects to its endpoint.
* For ANY subalphabet C, the exact intrinsic C-component at Q(x)
  is the image of the intrinsic C-component at x.

The graph can be incomplete and disconnected, and there can be
geometric loops, nonfaithful or repeated labels. No extra edges
are added, nor are ambient-coset paths substituted for true paths.

This is a certified geometric covering interface, NOT the choice
of the specific H₁ action/cover catalogue or the finite reflecting
group in corrected ABO.
-/

namespace PSTSEPPA
namespace ABO

variable {ι H Γ : Type*} [Fintype ι] [DecidableEq ι]
variable [Group H] [Group Γ]
variable {genH : ι → H} {genΓ : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec genΓ A)
variable (Q : LabelledGroupQuotient genH genΓ)

/-- Every REAL original signed path has a lifted path over
any prescribed starting lift. Its signed word is identical
and the endpoint maps to the original endpoint. -/
theorem pullbackQuotient_follows_lift
    {u v : K.Vertex} {w : LabelWord ι}
    (hp : (K.toEGraph).Follows u w v)
    (x : (K.pullbackQuotient Q).Vertex)
    (hx : (K.pullbackQuotientHom Q).onVertex x = u) :
    ∃ y : (K.pullbackQuotient Q).Vertex,
      ((K.pullbackQuotient Q).toEGraph).Follows x w y ∧
      (K.pullbackQuotientHom Q).onVertex y = v := by
  induction hp generalizing x with
  | nil u =>
      exact ⟨x, EGraph.Follows.nil x, hx⟩
  | @cons u v s w e hs hl hrest ih =>
      have hsrc :
          (K.pullbackQuotientHom Q).onVertex x =
            (K.toEGraph).source e := hx.trans hs.symm
      obtain ⟨f, hfsrc, hfmap⟩ :=
        K.pullbackQuotientHom_edge_lift Q e x hsrc
      have htarget :
          (K.pullbackQuotientHom Q).onVertex
              (((K.pullbackQuotient Q).toEGraph).target f) =
            (K.toEGraph).target e := by
        calc
          (K.pullbackQuotientHom Q).onVertex
              (((K.pullbackQuotient Q).toEGraph).target f) =
              (K.toEGraph).target ((K.pullbackQuotientHom Q).onEdge f) :=
            ((K.pullbackQuotientHom Q).map_target f).symm
          _ = (K.toEGraph).target e := by rw [hfmap]
      obtain ⟨y, hyLift, hyMap⟩ :=
        ih (((K.pullbackQuotient Q).toEGraph).target f) htarget
      have hfLabel :
          ((K.pullbackQuotient Q).toEGraph).label f = s := by
        calc
          ((K.pullbackQuotient Q).toEGraph).label f =
              (K.toEGraph).label ((K.pullbackQuotientHom Q).onEdge f) :=
            ((K.pullbackQuotientHom Q).map_label f).symm
          _ = (K.toEGraph).label e := by rw [hfmap]
          _ = s := hl
      exact ⟨y, EGraph.Follows.cons f hfsrc hfLabel hyLift, hyMap⟩

/-- A projected path exists precisely when the prescribed lift
can follow the SAME signed word to a vertex over its endpoint.
The forward implication lifts REAL edges; the backward
implication is labelled morphism naturality. -/
theorem pullbackQuotient_follows_iff
    (x : (K.pullbackQuotient Q).Vertex)
    (v : K.Vertex) (w : LabelWord ι) :
    (K.toEGraph).Follows
        ((K.pullbackQuotientHom Q).onVertex x) w v ↔
      ∃ y : (K.pullbackQuotient Q).Vertex,
        ((K.pullbackQuotient Q).toEGraph).Follows x w y ∧
        (K.pullbackQuotientHom Q).onVertex y = v := by
  constructor
  · intro hp
    exact K.pullbackQuotient_follows_lift Q hp x rfl
  · rintro ⟨y, hpath, hy⟩
    have hp := hpath.map (K.pullbackQuotientHom Q)
    rw [hy] at hp
    exact hp

/-- Starting from ANY fixed lift of a base vertex, a genuine
base signed path has a UNIQUE lifted endpoint over the
specified old endpoint. This also covers empty words. -/
theorem pullbackQuotient_follows_lift_unique
    {u v : K.Vertex} {w : LabelWord ι}
    (hp : (K.toEGraph).Follows u w v)
    (x : (K.pullbackQuotient Q).Vertex)
    (hx : (K.pullbackQuotientHom Q).onVertex x = u) :
    ∃! y : (K.pullbackQuotient Q).Vertex,
      ((K.pullbackQuotient Q).toEGraph).Follows x w y ∧
      (K.pullbackQuotientHom Q).onVertex y = v := by
  obtain ⟨y, hLift, hyMap⟩ := K.pullbackQuotient_follows_lift Q hp x hx
  refine ⟨y, ⟨hLift, hyMap⟩, ?_⟩
  intro z hz
  exact ((K.pullbackQuotient Q).toEGraph.follows_right_unique
    hLift hz.1).symm

/-- The image of the intrinsic C-component of ANY starting lift
is EXACTLY the intrinsic C-component of its quotient vertex.
This is about real signed paths, NOT ambient C-cosets. -/
theorem pullbackQuotient_subalphabetReachable_iff
    (C : Finset ι)
    (x : (K.pullbackQuotient Q).Vertex)
    (v : K.Vertex) :
    K.SubalphabetReachable C
        ((K.pullbackQuotientHom Q).onVertex x) v ↔
      ∃ y : (K.pullbackQuotient Q).Vertex,
        (K.pullbackQuotient Q).SubalphabetReachable C x y ∧
        (K.pullbackQuotientHom Q).onVertex y = v := by
  constructor
  · rintro ⟨w, hw, hp⟩
    obtain ⟨y, hLift, hy⟩ :=
      K.pullbackQuotient_follows_lift Q hp x rfl
    exact ⟨y, ⟨w, hw, hLift⟩, hy⟩
  · rintro ⟨y, ⟨w, hw, hLift⟩, hy⟩
    have hp := hLift.map (K.pullbackQuotientHom Q)
    rw [hy] at hp
    exact ⟨w, hw, hp⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
