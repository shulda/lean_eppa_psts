import PSTSEPPA.PSTS.WordEval

/-!
# ABO labelled graphs

A small custom graph API matching Sections 2.3 and 3.1 of
Auinger--Bitterlich--Otto.

Edges are directed tokens equipped with a fixed-point-free involution.  Hence
a geometric loop still has two distinct directed edge tokens.  Labels are
signed letters and edge reversal inverts the label.
-/

namespace PSTSEPPA
namespace ABO

abbrev SignedLabel (ι : Type*) := PSTS.SignedLetter ι
abbrev LabelWord (ι : Type*) := PSTS.SignedWord ι

/-- A directed labelled multigraph with formal edge reversal.

Only the source map is stored: the target of an edge is the source of its
formal inverse.  This makes the two incidence/reversal equations automatic.
The involution has no fixed edges, even for geometric loops. -/
structure LabelledGraph (V Edge ι : Type*) where
  source : Edge → V
  inv : Edge → Edge
  inv_inv : ∀ e, inv (inv e) = e
  inv_ne : ∀ e, inv e ≠ e
  label : Edge → SignedLabel ι
  label_inv : ∀ e, label (inv e) = PSTS.SignedLetter.inv (label e)

namespace LabelledGraph

variable {V Edge ι : Type*} (G : LabelledGraph V Edge ι)

/-- Terminal vertex of a directed edge. -/
def target (e : Edge) : V :=
  G.source (G.inv e)

@[simp]
theorem target_inv (e : Edge) :
    G.target (G.inv e) = G.source e := by
  simp [target, G.inv_inv]

@[simp]
theorem source_inv (e : Edge) :
    G.source (G.inv e) = G.target e :=
  rfl

@[simp]
theorem label_inv_eq (e : Edge) :
    G.label (G.inv e) = PSTS.SignedLetter.inv (G.label e) :=
  G.label_inv e

/-- A geometric loop is allowed; it still consists of two distinct directed
edge tokens related by `inv`. -/
def IsLoop (e : Edge) : Prop :=
  G.source e = G.target e

theorem inv_isLoop_iff (e : Edge) :
    G.IsLoop (G.inv e) ↔ G.IsLoop e := by
  simp [IsLoop, eq_comm]

end LabelledGraph

/-- An ABO `E`-graph: from a fixed source there is at most one outgoing edge
with any prescribed signed label.  Multiple edges and repeated endpoints are
otherwise allowed. -/
structure EGraph (V Edge ι : Type*) extends LabelledGraph V Edge ι where
  deterministic :
    ∀ {e f : Edge},
      toLabelledGraph.source e = toLabelledGraph.source f →
      toLabelledGraph.label e = toLabelledGraph.label f →
      e = f

namespace EGraph

variable {V Edge ι : Type*} (G : EGraph V Edge ι)

abbrev target := G.toLabelledGraph.target

/-- An `E`-graph is complete when every signed label occurs exactly once as
an outgoing edge at every vertex.  Uniqueness is already supplied by
`deterministic`. -/
def IsComplete : Prop :=
  ∀ u : V, ∀ s : SignedLabel ι,
    ∃ e : Edge, G.source e = u ∧ G.label e = s

/-- A witness that a labelled word is realised by a path from `u` to `v`.
This recursive relation includes the empty path. -/
inductive Follows : V → LabelWord ι → V → Prop
  | nil (u : V) : Follows u [] u
  | cons {u v : V} {s : SignedLabel ι} {w : LabelWord ι}
      (e : Edge)
      (hsource : G.source e = u)
      (hlabel : G.label e = s)
      (hrest : Follows (G.target e) w v) :
      Follows u (s :: w) v

@[simp]
theorem follows_nil_iff {u v : V} :
    G.Follows u [] v ↔ u = v := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Follows.nil _

/-- Determinism of labelled paths in an `E`-graph. -/
theorem follows_right_unique {u v₁ v₂ : V} {w : LabelWord ι}
    (h₁ : G.Follows u w v₁) (h₂ : G.Follows u w v₂) :
    v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | nil u =>
      exact G.follows_nil_iff.mp h₂
  | @cons u v s w e hs hl hrest ih =>
      cases h₂ with
      | cons f hs' hl' hrest' =>
          have hef : e = f := by
            apply G.deterministic
            · exact hs.trans hs'.symm
            · exact hl.trans hl'.symm
          subst f
          exact ih hrest'

end EGraph

/-- A complete `E`-graph, also called a group action graph/permutation
automaton by ABO. -/
structure CompleteEGraph (V Edge ι : Type*) extends EGraph V Edge ι where
  complete : toEGraph.IsComplete

namespace CompleteEGraph

variable {V Edge ι : Type*} (G : CompleteEGraph V Edge ι)

abbrev target := G.toEGraph.target

/-- The unique outgoing edge with source `u` and signed label `s`. -/
noncomputable def edgeAt (u : V) (s : SignedLabel ι) : Edge :=
  Classical.choose (G.complete u s)

@[simp]
theorem edgeAt_source (u : V) (s : SignedLabel ι) :
    G.source (G.edgeAt u s) = u :=
  (Classical.choose_spec (G.complete u s)).1

@[simp]
theorem edgeAt_label (u : V) (s : SignedLabel ι) :
    G.label (G.edgeAt u s) = s :=
  (Classical.choose_spec (G.complete u s)).2

theorem edgeAt_eq {u : V} {s : SignedLabel ι} {e : Edge}
    (hs : G.source e = u) (hl : G.label e = s) :
    G.edgeAt u s = e := by
  apply G.toEGraph.deterministic
  · simpa [hs]
  · simpa [hl]

/-- Reversing the unique `s`-edge gives the unique inverse-labelled edge
from its terminal vertex. -/
theorem edgeAt_inv (u : V) (s : SignedLabel ι) :
    G.edgeAt (G.target (G.edgeAt u s)) (PSTS.SignedLetter.inv s) =
      G.inv (G.edgeAt u s) := by
  apply G.edgeAt_eq
  · rfl
  · simp

/-- Every word labels a unique path from every starting vertex in a complete
`E`-graph. -/
noncomputable def followWord (H : CompleteEGraph V Edge ι)
    (u : V) : LabelWord ι → V
  | [] => u
  | s :: w =>
      followWord H (H.target (H.edgeAt u s)) w

@[simp]
theorem followWord_nil (u : V) :
    G.followWord u [] = u :=
  rfl

@[simp]
theorem followWord_cons (u : V) (s : SignedLabel ι) (w : LabelWord ι) :
    G.followWord u (s :: w) =
      G.followWord (G.target (G.edgeAt u s)) w :=
  rfl

theorem follows_followWord (u : V) (w : LabelWord ι) :
    G.toEGraph.Follows u w (G.followWord u w) := by
  induction w generalizing u with
  | nil =>
      exact EGraph.Follows.nil u
  | cons s w ih =>
      exact EGraph.Follows.cons
        (G.edgeAt u s)
        (G.edgeAt_source u s)
        (G.edgeAt_label u s)
        (ih (u := G.target (G.edgeAt u s)))

end CompleteEGraph

end ABO
end PSTSEPPA
