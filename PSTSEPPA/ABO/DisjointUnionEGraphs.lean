import PSTSEPPA.ABO.CanonicalCover
import PSTSEPPA.ABO.SynchronizedLabelledGroups
import Mathlib.Data.Fintype.Sum

/-!
# Literal disjoint unions of ABO E-graphs and complete transition stages

The finite Section 5 reflecting-group construction repeatedly takes
DISJOINT UNIONS of finite complete labelled E-graphs, and uses
the transition group of the resulting action graph. This must be
represented by actual vertex and directed-edge disjoint unions,
not merely a product of abstract group labels.

This module constructs a literal labelled EGraph on V₁ ⊕ V₂,
with edge set E₁ ⊕ E₂ and exact source, inverse, signed labels and
determinism, then shows that two complete E-graphs give a complete
disjoint union with true paths confined to their original component.

The construction respects the two distinct oriented tokens of
each geometric loop and repeated/trivial generator labels. It is
finite whenever both vertex and edge types are finite.

Together with #257's finite synchronized products, this is
preparatory infrastructure for identifying stage transition
groups with synchronized actions. That isomorphism, the finite
ABO tower, and endpoint-preserving reflection are NOT proved here.
-/

namespace PSTSEPPA
namespace ABO

variable {V₁ E₁ V₂ E₂ ι : Type*}

namespace EGraph

/-- Literal disjoint union of two potentially incomplete E-graphs.
Every edge retains its component tag, source, signed label and
formal reverse edge. No artificial identifications occur. -/
def disjointUnion (G : EGraph V₁ E₁ ι) (H : EGraph V₂ E₂ ι) :
    EGraph (V₁ ⊕ V₂) (E₁ ⊕ E₂) ι where
  toLabelledGraph :=
    { source := fun
        | .inl e => .inl (G.source e)
        | .inr e => .inr (H.source e)
      inv := fun
        | .inl e => .inl (G.inv e)
        | .inr e => .inr (H.inv e)
      inv_inv := by
        intro e
        cases e with
        | inl e =>
            exact congrArg Sum.inl (G.inv_inv e)
        | inr e =>
            exact congrArg Sum.inr (H.inv_inv e)
      inv_ne := by
        intro e he
        cases e with
        | inl e =>
            exact G.inv_ne e (Sum.inl.inj he)
        | inr e =>
            exact H.inv_ne e (Sum.inr.inj he)
      label := fun
        | .inl e => G.label e
        | .inr e => H.label e
      label_inv := by
        intro e
        cases e with
        | inl e => exact G.label_inv e
        | inr e => exact H.label_inv e }
  deterministic := by
    intro e f hsource hlabel
    cases e with
    | inl e =>
        cases f with
        | inl f =>
            have hs : G.source e = G.source f :=
              Sum.inl.inj hsource
            exact congrArg Sum.inl (G.deterministic hs hlabel)
        | inr f =>
            cases hsource
    | inr e =>
        cases f with
        | inl f =>
            cases hsource
        | inr f =>
            have hs : H.source e = H.source f :=
              Sum.inr.inj hsource
            exact congrArg Sum.inr (H.deterministic hs hlabel)

/-- Each original E-graph embeds as a literal subgraph into
the disjoint union, on vertices and directed edge tokens. -/
def disjointUnion_inlHom
    (G : EGraph V₁ E₁ ι) (H : EGraph V₂ E₂ ι) :
    LabelledGraphHom
      G.toLabelledGraph
      (G.disjointUnion H).toLabelledGraph where
  onVertex := Sum.inl
  onEdge := Sum.inl
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

def disjointUnion_inrHom
    (G : EGraph V₁ E₁ ι) (H : EGraph V₂ E₂ ι) :
    LabelledGraphHom
      H.toLabelledGraph
      (G.disjointUnion H).toLabelledGraph where
  onVertex := Sum.inr
  onEdge := Sum.inr
  map_source _ := rfl
  map_inv _ := rfl
  map_label _ := rfl

/-- An actual signed path in the left component remains an
actual signed path in the disjoint-union EGraph. -/
theorem follows_disjointUnion_inl
    (G : EGraph V₁ E₁ ι) (H : EGraph V₂ E₂ ι)
    {x y : V₁} {w : LabelWord ι}
    (h : G.Follows x w y) :
    (G.disjointUnion H).Follows (.inl x) w (.inl y) :=
  h.map (disjointUnion_inlHom G H)

theorem follows_disjointUnion_inr
    (G : EGraph V₁ E₁ ι) (H : EGraph V₂ E₂ ι)
    {x y : V₂} {w : LabelWord ι}
    (h : H.Follows x w y) :
    (G.disjointUnion H).Follows (.inr x) w (.inr y) :=
  h.map (disjointUnion_inrHom G H)

/-- No path starting in the left component can move to
the right: its terminal vertex and the entire path still lie
inside the left input graph. -/
theorem follows_disjointUnion_inl_reflect
    (G : EGraph V₁ E₁ ι) (H : EGraph V₂ E₂ ι)
    {x : V₁} {z : V₁ ⊕ V₂} {w : LabelWord ι}
    (h : (G.disjointUnion H).Follows (.inl x) w z) :
    ∃ y : V₁, z = .inl y ∧ G.Follows x w y := by
  induction w generalizing x z with
  | nil =>
      have hz : (Sum.inl x : V₁ ⊕ V₂) = z :=
        (G.disjointUnion H).follows_nil_iff.mp h
      subst z
      exact ⟨x, rfl, EGraph.Follows.nil x⟩
  | cons s w ih =>
      cases h with
      | cons e hsrc hl hrest =>
          cases e with
          | inl e =>
              have hsrc' : G.source e = x := Sum.inl.inj hsrc
              have htail :
                  (G.disjointUnion H).Follows
                    (.inl (G.target e)) w z := hrest
              obtain ⟨y, hy, hp⟩ := ih htail
              exact ⟨y, hy, EGraph.Follows.cons e hsrc' hl hp⟩
          | inr e =>
              cases hsrc

/-- Symmetric no-crossing property for paths starting in
the right component. -/
theorem follows_disjointUnion_inr_reflect
    (G : EGraph V₁ E₁ ι) (H : EGraph V₂ E₂ ι)
    {x : V₂} {z : V₁ ⊕ V₂} {w : LabelWord ι}
    (h : (G.disjointUnion H).Follows (.inr x) w z) :
    ∃ y : V₂, z = .inr y ∧ H.Follows x w y := by
  induction w generalizing x z with
  | nil =>
      have hz : (Sum.inr x : V₁ ⊕ V₂) = z :=
        (G.disjointUnion H).follows_nil_iff.mp h
      subst z
      exact ⟨x, rfl, EGraph.Follows.nil x⟩
  | cons s w ih =>
      cases h with
      | cons e hsrc hl hrest =>
          cases e with
          | inl e =>
              cases hsrc
          | inr e =>
              have hsrc' : H.source e = x := Sum.inr.inj hsrc
              have htail :
                  (G.disjointUnion H).Follows
                    (.inr (H.target e)) w z := hrest
              obtain ⟨y, hy, hp⟩ := ih htail
              exact ⟨y, hy, EGraph.Follows.cons e hsrc' hl hp⟩

end EGraph

namespace CompleteEGraph

/-- A disjoint union of two complete E-graphs is again complete,
with actual inverse edges and no cross-component paths. -/
noncomputable def disjointUnion
    (G : CompleteEGraph V₁ E₁ ι) (H : CompleteEGraph V₂ E₂ ι) :
    CompleteEGraph (V₁ ⊕ V₂) (E₁ ⊕ E₂) ι where
  toEGraph := G.toEGraph.disjointUnion H.toEGraph
  complete := by
    intro u s
    cases u with
    | inl x =>
        obtain ⟨e, heSrc, heLab⟩ := G.complete x s
        exact ⟨.inl e, congrArg Sum.inl heSrc, heLab⟩
    | inr x =>
        obtain ⟨e, heSrc, heLab⟩ := H.complete x s
        exact ⟨.inr e, congrArg Sum.inr heSrc, heLab⟩

/-- Canonical signed word-following is componentwise for
the literal disjoint union, including inverse letters. -/
theorem disjointUnion_followWord_inl
    (G : CompleteEGraph V₁ E₁ ι) (H : CompleteEGraph V₂ E₂ ι)
    (x : V₁) (w : LabelWord ι) :
    (G.disjointUnion H).followWord (.inl x) w =
      .inl (G.followWord x w) := by
  have hp :
      (G.disjointUnion H).toEGraph.Follows (.inl x) w
        (.inl (G.followWord x w)) :=
    (G.follows_followWord x w).map
      (EGraph.disjointUnion_inlHom G.toEGraph H.toEGraph)
  exact (G.disjointUnion H).toEGraph.follows_right_unique
    ((G.disjointUnion H).follows_followWord (.inl x) w) hp

theorem disjointUnion_followWord_inr
    (G : CompleteEGraph V₁ E₁ ι) (H : CompleteEGraph V₂ E₂ ι)
    (x : V₂) (w : LabelWord ι) :
    (G.disjointUnion H).followWord (.inr x) w =
      .inr (H.followWord x w) := by
  have hp :
      (G.disjointUnion H).toEGraph.Follows (.inr x) w
        (.inr (H.followWord x w)) :=
    (H.follows_followWord x w).map
      (EGraph.disjointUnion_inrHom G.toEGraph H.toEGraph)
  exact (G.disjointUnion H).toEGraph.follows_right_unique
    ((G.disjointUnion H).follows_followWord (.inr x) w) hp

end CompleteEGraph
end ABO
end PSTSEPPA
