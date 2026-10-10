import PSTSEPPA.ABO.WeakCompletePairedEdges
import PSTSEPPA.ABO.ActionGraph
import PSTSEPPA.ABO.Morphisms

/-!
# Trivial loop completion of E-graphs with locally paired signed labels

An arbitrary oriented E-graph cannot generally be completed just by
adding loops: a vertex may have a positive i-edge but lack a negative
i-edge. Completing that missing inverse label by a loop would create
a second positive i-edge and violate determinism.

The source's ABO weakly complete multi-coset extensions DO have the
needed invariant, proved separately in #262: for each vertex and
unsigned label i, either both signed outgoing edges exist or
neither exists.

For any EGraph satisfying that property, the partial i-transition
and its inverse are bijections on the SAME subset of vertices.
Extend the partial permutation by FIXING all remaining vertices.
The resulting actionGraph is a complete E-graph on exactly the SAME
vertices, and the old EGraph embeds as an induced labelled subgraph
on its pre-existing edge tokens. Every newly supplied signed edge
is a geometric LOOP.

This is the literal source-facing "trivial completion adds only
loops" construction needed in ABO Sections 3--5. It handles true
inverse labels, repeated/trivial generators, and old geometric loops.
The finite Section 5 induction and reflecting group remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {V Edge ι : Type*}

namespace EGraph

variable (G : EGraph V Edge ι)

/-- Follow an existing signed edge if the edge exists from u;
otherwise stay at u. This is a partial action extended by the
identity, but is a permutation only under locally paired labels. -/
noncomputable def loopCompletedStep
    (G : EGraph V Edge ι)
    (s : SignedLabel ι) (u : V) : V := by
  classical
  exact if h : ∃ e : Edge, G.source e = u ∧ G.label e = s then
    G.target (Classical.choose h)
  else u

theorem loopCompletedStep_of_edge
    (s : SignedLabel ι) (u : V) (e : Edge)
    (hsrc : G.source e = u) (hlab : G.label e = s) :
    G.loopCompletedStep s u = G.target e := by
  classical
  have h : ∃ f : Edge, G.source f = u ∧ G.label f = s :=
    ⟨e, hsrc, hlab⟩
  have hc := Classical.choose_spec h
  have heq : Classical.choose h = e :=
    G.deterministic (hc.1.trans hsrc.symm) (hc.2.trans hlab.symm)
  simp only [loopCompletedStep, dif_pos h]
  exact congrArg G.target heq

theorem loopCompletedStep_of_missing
    (s : SignedLabel ι) (u : V)
    (h : ¬ ∃ e : Edge, G.source e = u ∧ G.label e = s) :
    G.loopCompletedStep s u = u := by
  simp [loopCompletedStep, h]

/-- Local signed availability is used ONLY when the chosen label
is absent: then its inverse label must also be absent. -/
theorem missing_inverse_of_locallyPaired
    (hpaired : G.LocallyPairedLabels)
    (s : SignedLabel ι) (u : V)
    (h : ¬ ∃ e : Edge, G.source e = u ∧ G.label e = s) :
    ¬ ∃ e : Edge,
      G.source e = u ∧
      G.label e = PSTS.SignedLetter.inv s := by
  cases s with
  | pos i =>
      intro hback
      exact h ((hpaired u i).mpr hback)
  | neg i =>
      intro hback
      exact h ((hpaired u i).mp hback)

/-- Under locally paired signed labels, the completed step in
the opposite signed direction is the exact inverse function. -/
theorem loopCompletedStep_inverse
    (hpaired : G.LocallyPairedLabels)
    (s : SignedLabel ι) (u : V) :
    G.loopCompletedStep (PSTS.SignedLetter.inv s)
      (G.loopCompletedStep s u) = u := by
  classical
  by_cases h : ∃ e : Edge, G.source e = u ∧ G.label e = s
  · obtain ⟨e, hsrc, hlab⟩ := h
    have hForward :
        G.loopCompletedStep s u = G.target e :=
      G.loopCompletedStep_of_edge s u e hsrc hlab
    have hBackward :
        G.loopCompletedStep (PSTS.SignedLetter.inv s) (G.target e) =
          G.target (G.inv e) := by
      apply G.loopCompletedStep_of_edge
      · rfl
      · exact G.label_inv e |>.trans (congrArg PSTS.SignedLetter.inv hlab)
    calc
      G.loopCompletedStep (PSTS.SignedLetter.inv s)
          (G.loopCompletedStep s u) =
        G.loopCompletedStep (PSTS.SignedLetter.inv s) (G.target e) :=
          congrArg _ hForward
      _ = G.target (G.inv e) := hBackward
      _ = G.source e := G.toLabelledGraph.target_inv e
      _ = u := hsrc
  · have hinv := G.missing_inverse_of_locallyPaired hpaired s u h
    calc
      G.loopCompletedStep (PSTS.SignedLetter.inv s)
          (G.loopCompletedStep s u) =
        G.loopCompletedStep (PSTS.SignedLetter.inv s) u :=
          congrArg _ (G.loopCompletedStep_of_missing s u h)
      _ = u :=
        G.loopCompletedStep_of_missing (PSTS.SignedLetter.inv s) u hinv

/-- Each unsigned generator becomes a genuine total permutation by
adding fixed points exactly where BOTH signed directions were absent. -/
noncomputable def loopCompletedPermutation
    (hpaired : G.LocallyPairedLabels) (i : ι) :
    Equiv.Perm V where
  toFun := G.loopCompletedStep (.pos i)
  invFun := G.loopCompletedStep (.neg i)
  left_inv u := G.loopCompletedStep_inverse hpaired (.pos i) u
  right_inv u := G.loopCompletedStep_inverse hpaired (.neg i) u

/-- The complete action graph extending G, with no new vertices.
An absent signed generator acts as an identity loop at that vertex. -/
noncomputable def trivialLoopCompletion
    (hpaired : G.LocallyPairedLabels) :
    CompleteEGraph V (ActionEdge V ι) ι :=
  actionGraph (G.loopCompletedPermutation hpaired)

/-- Every originally present directed edge retains its exact target
under the new total action, even for negative labels. -/
theorem trivialLoopCompletion_target_existing
    (hpaired : G.LocallyPairedLabels) (e : Edge) :
    (G.trivialLoopCompletion hpaired).target
        (G.source e, G.label e) = G.target e := by
  cases hs : G.label e with
  | pos i =>
      change G.loopCompletedStep (.pos i) (G.source e) = G.target e
      exact G.loopCompletedStep_of_edge (.pos i)
        (G.source e) e rfl hs
  | neg i =>
      change G.loopCompletedStep (.neg i) (G.source e) = G.target e
      exact G.loopCompletedStep_of_edge (.neg i)
        (G.source e) e rfl hs

/-- The original labelled EGraph embeds into its loop completion:
no original vertex or oriented edge is identified or changed.
The new tokens simply re-encode an old directed edge as
(source, signed label), injectively by original determinism. -/
noncomputable def trivialLoopCompletionHom
    (hpaired : G.LocallyPairedLabels) :
    LabelledGraphHom
      G.toLabelledGraph
      (G.trivialLoopCompletion hpaired).toEGraph.toLabelledGraph where
  onVertex := id
  onEdge e := (G.source e, G.label e)
  map_source _ := rfl
  map_label _ := rfl
  map_inv e := by
    apply Prod.ext
    · change G.source (G.inv e) =
        (G.trivialLoopCompletion hpaired).target
          (G.source e, G.label e)
      exact (G.trivialLoopCompletion_target_existing hpaired e).symm
    · exact G.label_inv e

/-- Original directed edge tokens embed injectively, even for a
geometric loop (whose inverse token must remain distinct). -/
theorem trivialLoopCompletionHom_edge_injective
    (hpaired : G.LocallyPairedLabels) :
    Function.Injective (G.trivialLoopCompletionHom hpaired).onEdge := by
  intro e f heq
  have hsrc : G.source e = G.source f :=
    congrArg Prod.fst heq
  have hlab : G.label e = G.label f :=
    congrArg Prod.snd heq
  exact G.deterministic hsrc hlab

/-- A signed label missing from u becomes exactly a loop at u.
In particular trivial completion introduces NO non-loop edges. -/
theorem trivialLoopCompletion_loop_of_missing
    (hpaired : G.LocallyPairedLabels)
    (u : V) (s : SignedLabel ι)
    (hMissing :
      ¬ ∃ e : Edge, G.source e = u ∧ G.label e = s) :
    (G.trivialLoopCompletion hpaired).target (u,s) = u := by
  cases s with
  | pos i =>
      change G.loopCompletedStep (.pos i) u = u
      exact G.loopCompletedStep_of_missing (.pos i) u hMissing
  | neg i =>
      change G.loopCompletedStep (.neg i) u = u
      exact G.loopCompletedStep_of_missing (.neg i) u hMissing

end EGraph
end ABO
end PSTSEPPA
