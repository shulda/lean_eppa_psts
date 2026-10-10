import PSTSEPPA.ABO.IsolatedCosetGluing
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Exact subalphabet paths through an isolated full-coset attachment

In a genuine type-(2) rank-two augmentation, a full B-coset is
glued at an old vertex whose original B-component is a singleton.
For any alphabet C disjoint from B, the augmentation adds no
C-labelled edge. Therefore:
* every C-path between old points remains a path in the old graph;
* every C-path beginning at a fresh coset point is stationary;
* the old C-component relation is preserved and reflected EXACTLY.

The statements are about ACTUAL signed paths in the constructed
EGraph, not ambient group coordinates or a proposed completion.
They include C empty and formal inverse labels. Combined with
the new full B-component, these are the elementary component
cases of corrected ABO Proposition 3.24 in rank two.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Every genuine edge of the attached graph whose
unsigned label belongs to C disjoint from B must be
an original edge. None of the new B-coset edges qualifies. -/
theorem glued_C_edge_is_old
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (C : Finset ι) (hdis : Disjoint C B)
    (e : Edge OldEdge gen B g)
    (hC : signedBase
      ((gluedEGraph G gen B g root hMissing).label e) ∈ C) :
    ∃ f : OldEdge, e = Sum.inl f := by
  cases e with
  | inl e =>
      exact ⟨e, rfl⟩
  | inr e =>
      have hC' :
          signedBase ((cayleyGraph gen).label e.1) ∈ C := hC
      have hB :
          signedBase ((cayleyGraph gen).label e.1) ∈ B := e.2.2
      exact False.elim
        ((Finset.disjoint_left.mp hdis) hC' hB)

/-- Every C-path out of an old point, when C∩B=∅,
comes from a genuine old C-path and ends at an old point.
This is a path induction through the actual EGraph. -/
theorem glued_C_path_from_old_reflect
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (C : Finset ι) (hdis : Disjoint C B)
    (x : V) (z : Vertex V gen B g)
    (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hpath :
      (gluedEGraph G gen B g root hMissing).Follows
        (Sum.inl x) w z) :
    ∃ y : V, z = Sum.inl y ∧ G.Follows x w y := by
  let H := gluedEGraph G gen B g root hMissing
  induction w generalizing x z with
  | nil =>
      have hz : (Sum.inl x : Vertex V gen B g) = z :=
        H.follows_nil_iff.mp hpath
      subst z
      exact ⟨x, rfl, EGraph.Follows.nil x⟩
  | cons s w ih =>
      cases hpath with
      | cons e hsource hlabel htail =>
          have heC : signedBase (H.label e) ∈ C := by
            rw [hlabel]
            exact hw.1
          obtain ⟨eOld, heOld⟩ :=
            glued_C_edge_is_old G gen B g root
              hMissing C hdis e heC
          subst e
          have hsrc : G.source eOld = x :=
            Sum.inl.inj hsource
          have htail' :
              H.Follows (Sum.inl (G.target eOld)) w z := htail
          obtain ⟨y, hzy, hp⟩ :=
            ih hw.2 (x := G.target eOld) (z := z) htail'
          refine ⟨y, hzy, ?_⟩
          exact EGraph.Follows.cons eOld hsrc hlabel hp

/-- Exact C-reachability between original vertices is
preserved and reflected by the new full B-coset,
as long as C and B are disjoint. -/
theorem glued_C_reachable_old_iff
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (C : Finset ι) (hdis : Disjoint C B)
    (x y : V) :
    (∃ w : LabelWord ι, LabelWord.Uses C w ∧
      (gluedEGraph G gen B g root hMissing).Follows
        (Sum.inl x) w (Sum.inl y)) ↔
    (∃ w : LabelWord ι, LabelWord.Uses C w ∧
      G.Follows x w y) := by
  constructor
  · rintro ⟨w, hw, hp⟩
    obtain ⟨z, hzy, hzPath⟩ :=
      glued_C_path_from_old_reflect
        G gen B g root hMissing C hdis x
        (Sum.inl y) w hw hp
    have hyz : y = z := Sum.inl.inj hzy
    subst z
    exact ⟨w, hw, hzPath⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw,
      hp.map (oldHom G gen B g root hMissing)⟩

/-- A fresh point has no outgoing C-edges for C disjoint
from B, hence every actually realised C-path from it
is the empty stationary path. -/
theorem glued_C_path_from_fresh_stationary
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (C : Finset ι) (hdis : Disjoint C B)
    (q : FreshPoint gen B g)
    (z : Vertex V gen B g) (w : LabelWord ι)
    (hw : LabelWord.Uses C w)
    (hpath :
      (gluedEGraph G gen B g root hMissing).Follows
        (Sum.inr q) w z) :
    z = Sum.inr q := by
  let H := gluedEGraph G gen B g root hMissing
  cases hpath with
  | nil _ =>
      rfl
  | cons e hsrc hl hrest =>
      have heC : signedBase (H.label e) ∈ C := by
        rw [hl]
        exact hw.1
      obtain ⟨f, hf⟩ :=
        glued_C_edge_is_old G gen B g root hMissing
          C hdis e heC
      subst e
      cases hsrc

end IsolatedCosetGluing
end ABO
end PSTSEPPA
