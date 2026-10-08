import PSTSEPPA.ABO.ComponentSubgraph
import PSTSEPPA.ABO.ComponentIndexMonotonicity

/-!
# Lifting paths into the literal intrinsic B-component subgraph

An actual B-labelled path in the parent Cayley skeleton, starting in
the intrinsic B-component of root, is a path of that component's
literal B-subgraph. No edges are supplied by ambient group cosets:
the lifted path uses precisely the original directed edge tokens.

This path reflection is the technical bridge needed to turn local
admissibility of the vertex component into actual admissibility of the
lower-rank CayleySubgraphSpec (the first half of ABO Lemma 3.20).
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Lift a vertex in the B-component of root to the explicit
component subgraph. -/
def componentLiftVertex
    (B : Finset ι) (root x : K.Vertex)
    (hx : K.SubalphabetReachable B root x) :
    (K.subalphabetComponentSubgraph B root).Vertex :=
  ⟨x.1, ⟨x, rfl, hx⟩⟩

/-- Lift a genuine B-labelled edge from the parent skeleton,
when its source belongs to the chosen B-component. -/
def componentLiftEdge
    (B : Finset ι) (root : K.Vertex)
    (e : K.Edge)
    (heB : signedBase e.1.2 ∈ B)
    (heRoot : K.SubalphabetReachable B root ((K.toEGraph).source e)) :
    (K.subalphabetComponentSubgraph B root).Edge :=
  ⟨e.1, ⟨e, rfl, heB, heRoot⟩⟩

/-- The inclusion of the component subgraph maps the lifted
vertex to the original vertex literally. -/
theorem subalphabetComponentSubgraphHom_liftVertex
    (B : Finset ι) (root x : K.Vertex)
    (hx : K.SubalphabetReachable B root x) :
    (K.subalphabetComponentSubgraphHom B root).onVertex
      (K.componentLiftVertex B root x hx) = x := by
  apply Subtype.ext
  rfl

/-- The inclusion of the component subgraph maps a lifted directed
edge to its original signed edge token. -/
theorem subalphabetComponentSubgraphHom_liftEdge
    (B : Finset ι) (root : K.Vertex)
    (e : K.Edge)
    (heB : signedBase e.1.2 ∈ B)
    (heRoot : K.SubalphabetReachable B root ((K.toEGraph).source e)) :
    (K.subalphabetComponentSubgraphHom B root).onEdge
      (K.componentLiftEdge B root e heB heRoot) = e := by
  apply Subtype.ext
  rfl

/-- Every genuine B-supported parent-skeleton path beginning in
the selected B-component is realised in the component subgraph.

The endpoint reachability witness is returned along with the
lifted path, so the statement makes no noncanonical choice
of endpoint membership proofs. -/
theorem follows_lift_component
    (B : Finset ι) (root : K.Vertex)
    {u v : K.Vertex} {w : LabelWord ι}
    (hpath : (K.toEGraph).Follows u w v)
    (huses : LabelWord.Uses B w)
    (hu : K.SubalphabetReachable B root u) :
    ∃ hv : K.SubalphabetReachable B root v,
      ((K.subalphabetComponentSubgraph B root).toEGraph).Follows
        (K.componentLiftVertex B root u hu)
        w
        (K.componentLiftVertex B root v hv) := by
  induction hpath with
  | nil u =>
      exact ⟨hu, EGraph.Follows.nil _⟩
  | @cons u v s w e hs hl hrest ih =>
      have heB : signedBase e.1.2 ∈ B := by
        change signedBase ((K.toEGraph).label e) ∈ B
        rw [hl]
        exact huses.1
      have hsrc :
          K.SubalphabetReachable B root ((K.toEGraph).source e) := by
        rw [hs]
        exact hu
      have htgt :
          K.SubalphabetReachable B root ((K.toEGraph).target e) :=
        K.subalphabetReachable_trans B hsrc
          (K.edge_subalphabetReachable B e heB)
      obtain ⟨hv, hrestLift⟩ := ih huses.2 htgt
      let newEdge := K.componentLiftEdge B root e heB hsrc
      have hsource :
          ((K.subalphabetComponentSubgraph B root).toEGraph).source newEdge =
            K.componentLiftVertex B root u hu := by
        apply Subtype.ext
        exact congrArg Subtype.val hs
      have htarget :
          ((K.subalphabetComponentSubgraph B root).toEGraph).target newEdge =
            K.componentLiftVertex B root ((K.toEGraph).target e) htgt := by
        apply Subtype.ext
        rfl
      have hlabel :
          ((K.subalphabetComponentSubgraph B root).toEGraph).label newEdge = s := by
        change e.1.2 = s
        exact hl
      refine ⟨hv, EGraph.Follows.cons newEdge hsource hlabel ?_⟩
      rw [htarget]
      exact hrestLift

/-- Every D-path with D⊆B between two vertices of the component
lifts to its literal B-component subgraph. -/
theorem reachable_lift_component
    (B D : Finset ι) (hDB : D ⊆ B)
    (root x y : K.Vertex)
    (hx : K.SubalphabetReachable B root x)
    (hxy : K.SubalphabetReachable D x y) :
    ∃ (hy : K.SubalphabetReachable B root y),
      (K.subalphabetComponentSubgraph B root).SubalphabetReachable
        D
        (K.componentLiftVertex B root x hx)
        (K.componentLiftVertex B root y hy) := by
  obtain ⟨w, hw, hp⟩ := hxy
  obtain ⟨hy, hlift⟩ :=
    K.follows_lift_component B root hp
      (hw.mono hDB) hx
  exact ⟨hy, w, hw, hlift⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
