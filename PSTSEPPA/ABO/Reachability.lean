import PSTSEPPA.ABO.Graph

/-!
# Reachability in complete ABO E-graphs

This file isolates the elementary component calculus needed for canonical
Cayley covers.  Reachability is stated by the canonical word-following
operation, so it is independent of any choice of a concrete path object.
-/

namespace PSTSEPPA
namespace ABO
namespace CompleteEGraph

variable {V Edge ι : Type*} (G : CompleteEGraph V Edge ι)

/-- Following a concatenated word means first following the left word and
then the right word. -/
theorem followWord_append (u : V) (p q : LabelWord ι) :
    G.followWord u (p ++ q) =
      G.followWord (G.followWord u p) q := by
  induction p generalizing u with
  | nil =>
      rfl
  | cons s p ih =>
      change
        G.followWord (G.target (G.edgeAt u s)) (p ++ q) =
          G.followWord
            (G.followWord (G.target (G.edgeAt u s)) p) q
      exact ih (u := G.target (G.edgeAt u s))

/-- Vertex `v` is reachable from `u` by some labelled word. -/
def Reachable (u v : V) : Prop :=
  ∃ w : LabelWord ι, G.followWord u w = v

@[simp]
theorem reachable_refl (u : V) :
    G.Reachable u u :=
  ⟨[], rfl⟩

/-- Reachability is transitive by word concatenation. -/
theorem Reachable.trans {u v z : V}
    (huv : G.Reachable u v)
    (hvz : G.Reachable v z) :
    G.Reachable u z := by
  rcases huv with ⟨p, hp⟩
  rcases hvz with ⟨q, hq⟩
  refine ⟨p ++ q, ?_⟩
  rw [G.followWord_append, hp, hq]

/-- A single labelled step from a reachable vertex remains reachable. -/
theorem reachable_target_edgeAt
    {u v : V} (huv : G.Reachable u v)
    (s : SignedLabel ι) :
    G.Reachable u (G.target (G.edgeAt v s)) := by
  rcases huv with ⟨w, hw⟩
  refine ⟨w ++ [s], ?_⟩
  rw [G.followWord_append, hw]
  rfl

/-- Reachability is equivalent to existence of an explicit `Follows`
derivation. -/
theorem reachable_iff_follows {u v : V} :
    G.Reachable u v ↔
      ∃ w : LabelWord ι, G.toEGraph.Follows u w v := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [← hw]
    exact G.follows_followWord u w
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    exact G.toEGraph.follows_right_unique (G.follows_followWord u w) hw

end CompleteEGraph
end ABO
end PSTSEPPA
