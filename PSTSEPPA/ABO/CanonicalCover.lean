import PSTSEPPA.ABO.CayleyGraph
import PSTSEPPA.ABO.Morphisms
import PSTSEPPA.ABO.Reachability

/-!
# Canonical Cayley maps onto complete-graph components

For a complete E-graph G and a base vertex u, its transition group has a
canonical Cayley graph.  Evaluation at u gives a labelled graph morphism from
that Cayley graph into G.

The vertex image is proved exactly equal to the set of vertices reachable from
u, and the edge image is exactly the set of directed edges whose source is in
that reachable component.  No injectivity is asserted or needed.
-/

namespace PSTSEPPA
namespace ABO
namespace CompleteEGraph

variable {V Edge ι : Type*} (G : CompleteEGraph V Edge ι)

/-- The labelled generators, now regarded as elements of the transition
subgroup itself. -/
noncomputable def transitionSubgroupGenerator (i : ι) : G.transitionGroup :=
  ⟨G.transitionGenerator i, G.transitionGenerator_mem i⟩

@[simp]
theorem transitionSubgroupGenerator_val (i : ι) :
    (G.transitionSubgroupGenerator i : RightPerm V) =
      G.transitionGenerator i :=
  rfl

/-- Signed group evaluation in the transition subgroup has the same underlying
right permutation as the signed transition value of G. -/
@[simp]
theorem evalGroupLetter_transitionSubgroup_val (s : SignedLabel ι) :
    ((PSTS.SignedWord.evalGroupLetter G.transitionSubgroupGenerator s :
        G.transitionGroup) : RightPerm V) =
      G.signedTransition s := by
  cases s <;> rfl

/-- Evaluate a transition-group element at a chosen base vertex. -/
def canonicalVertex (u : V) (g : G.transitionGroup) : V :=
  rightApply g.1 u

/-- The edge map forced by the vertex map and preservation of labels. -/
noncomputable def canonicalEdge (u : V)
    (e : ActionEdge G.transitionGroup ι) : Edge :=
  G.edgeAt (G.canonicalVertex u e.1) e.2

/-- The canonical vertex map intertwines a single Cayley step with the
corresponding labelled step in G. -/
theorem canonicalVertex_target (u : V) (g : G.transitionGroup)
    (s : SignedLabel ι) :
    G.canonicalVertex u
        ((cayleyGraph G.transitionSubgroupGenerator).target (g, s)) =
      G.target (G.edgeAt (G.canonicalVertex u g) s) := by
  rw [cayleyGraph.target_eq_mul_evalGroupLetter]
  unfold canonicalVertex
  change
    rightApply
        (g.1 *
          ((PSTS.SignedWord.evalGroupLetter
            G.transitionSubgroupGenerator s : G.transitionGroup) :
              RightPerm V)) u =
      G.target (G.edgeAt (rightApply g.1 u) s)
  rw [rightApply_mul, G.evalGroupLetter_transitionSubgroup_val]
  rw [G.rightApply_signedTransition]
  rfl

/-- The canonical labelled morphism from the transition-group Cayley graph
into G, based at u. -/
noncomputable def canonicalCayleyHom (u : V) :
    LabelledGraphHom
      (cayleyGraph G.transitionSubgroupGenerator).toEGraph.toLabelledGraph
      G.toEGraph.toLabelledGraph where
  onVertex := G.canonicalVertex u
  onEdge := G.canonicalEdge u
  map_source := by
    rintro ⟨g, s⟩
    exact G.edgeAt_source (G.canonicalVertex u g) s
  map_inv := by
    rintro ⟨g, s⟩
    unfold canonicalEdge
    change
      G.edgeAt
          (G.canonicalVertex u
            ((cayleyGraph G.transitionSubgroupGenerator).target (g, s)))
          (PSTS.SignedLetter.inv s) =
        G.inv (G.edgeAt (G.canonicalVertex u g) s)
    rw [G.canonicalVertex_target]
    exact G.edgeAt_inv (G.canonicalVertex u g) s
  map_label := by
    rintro ⟨g, s⟩
    exact G.edgeAt_label (G.canonicalVertex u g) s

@[simp]
theorem canonicalCayleyHom_onVertex (u : V) (g : G.transitionGroup) :
    (G.canonicalCayleyHom u).onVertex g = G.canonicalVertex u g :=
  rfl

@[simp]
theorem canonicalCayleyHom_onEdge (u : V)
    (e : ActionEdge G.transitionGroup ι) :
    (G.canonicalCayleyHom u).onEdge e = G.canonicalEdge u e :=
  rfl

/-- Every Cayley vertex lands in the reachable component of the basepoint. -/
theorem canonicalVertex_reachable (u : V) (g : G.transitionGroup) :
    G.Reachable u (G.canonicalVertex u g) := by
  rcases G.exists_wordValue_eq g.property with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  calc
    G.followWord u w = rightApply (G.wordValue w) u :=
      (G.rightApply_wordValue w u).symm
    _ = rightApply g.1 u := by rw [hw]
    _ = G.canonicalVertex u g := rfl

/-- Every reachable vertex is hit by the canonical Cayley vertex map. -/
theorem reachable_exists_canonicalVertex (u : V) {v : V}
    (hv : G.Reachable u v) :
    ∃ g : G.transitionGroup, G.canonicalVertex u g = v := by
  rcases hv with ⟨w, hw⟩
  let g : G.transitionGroup := ⟨G.wordValue w, G.wordValue_mem w⟩
  refine ⟨g, ?_⟩
  change rightApply (G.wordValue w) u = v
  rw [G.rightApply_wordValue]
  exact hw

/-- The vertex image of the canonical Cayley map is exactly the component
reachable from the chosen basepoint. -/
theorem canonicalVertex_range (u : V) :
    Set.range (G.canonicalVertex u) =
      {v : V | G.Reachable u v} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    exact G.canonicalVertex_reachable u g
  · intro hv
    rcases G.reachable_exists_canonicalVertex u hv with ⟨g, hg⟩
    exact ⟨g, hg⟩

/-- The edge image is exactly the directed edges whose source lies in the
reachable component. -/
theorem canonicalEdge_range (u : V) :
    Set.range (G.canonicalEdge u) =
      {e : Edge | G.Reachable u (G.source e)} := by
  ext e
  constructor
  · rintro ⟨⟨g, s⟩, rfl⟩
    change
      G.Reachable u
        (G.source (G.edgeAt (G.canonicalVertex u g) s))
    rw [G.edgeAt_source]
    exact G.canonicalVertex_reachable u g
  · intro he
    rcases G.reachable_exists_canonicalVertex u he with ⟨g, hg⟩
    refine ⟨(g, G.label e), ?_⟩
    unfold canonicalEdge
    apply G.edgeAt_eq
    · exact hg.symm
    · rfl

end CompleteEGraph
end ABO
end PSTSEPPA
