import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso
import PSTSEPPA.ABO.TrivialLoopCompletion

/-!
# True original signed B-components are invariant under LEGAL loop completion

For the published ABO upward 4.7(iii) proper nonisolated
B-augmentation we need to replace the B-action on ONE
actual old B-connected component by the full canonical
H[B]-coset action, leaving other original vertices and
outside-B transitions unchanged. This is legal only if
a B-labelled transition can NEVER cross the boundary of
the selected old B-component in EITHER direction.

For ANY deterministic incomplete signed original EGraph G,
the TRUE B-component (defined by actual signed B-paths,
with all original old vertex tags retained) is closed under
each existing positive/inverse B-edge. A missing edge adds
only a STATIONARY loop under legal completion; therefore
the completed signed B-action still preserves that
component in the forward direction.

Under the precise locally-paired-label hypothesis which
allows the official ABO stationary-loop completion, the
reverse signed generator is exactly the inverse permutation.
Thus membership in the old B-component is in fact
EQUIVALENT before and after EVERY positive/inverse B-step.
Its complement is invariant too.

This is an actual geometric preparation for a whole-
component (not isolated-root) B-coset action amalgam:
one can later replace the signed B-actions on the selected
component by those of H[B] without corrupting the old
B-actions outside it. It does NOT yet construct the pushout,
the selected complete stage or the G-cover itself.

No artificial old edge, no ambient-coordinate quotient
and no additional axioms/sorry.
-/

namespace PSTSEPPA
namespace ABO
namespace EGraph

variable {V Edge ι : Type*}
variable [Fintype ι] [DecidableEq ι]

/-- Every B-labelled positive OR inverse completion step
from an actual old B-component vertex remains in that
SAME TRUE original signed B-component. Missing old
labels become stationary loops, not invented old edges.
No globally complete group action or injective ambient
Cayley morphism is required. -/
theorem loopCompletedStep_BComponent_forward
    (G : EGraph V Edge ι) (B : Finset ι) (anchor : V)
    (s : SignedLabel ι) (hs : signedBase s ∈ B)
    (v : V) (hv : v ∈ G.BComponentVertexSet B anchor) :
    G.loopCompletedStep s v ∈ G.BComponentVertexSet B anchor := by
  classical
  by_cases he : ∃ e : Edge, G.source e = v ∧ G.label e = s
  · obtain ⟨e, heSource, heLabel⟩ := he
    have hOldEdge : e ∈ G.BComponentEdgeSet B anchor := by
      constructor
      · rw [heLabel]
        exact hs
      · rw [heSource]
        exact hv
    have hOldTarget :
        G.target e ∈ G.BComponentVertexSet B anchor :=
      G.BComponentEdge_target_mem B anchor e hOldEdge
    simpa only [G.loopCompletedStep_of_edge s v e heSource heLabel]
      using hOldTarget
  · simpa only [G.loopCompletedStep_of_missing s v he]
      using hv

/-- The crucial SATURATION lemma for nonisolated B-action
augmentation: legal loop completion never sends a vertex
INTO or OUT OF the actual old B-component along any
signed B-generator. This includes missing old labels,
real old signed inverse edges, and old geometric loops. -/
theorem loopCompletedStep_BComponent_mem_iff
    (G : EGraph V Edge ι)
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι) (anchor : V)
    (s : SignedLabel ι) (hs : signedBase s ∈ B)
    (v : V) :
    G.loopCompletedStep s v ∈ G.BComponentVertexSet B anchor ↔
      v ∈ G.BComponentVertexSet B anchor := by
  constructor
  · intro hnext
    have hsInv : signedBase (PSTS.SignedLetter.inv s) ∈ B := by
      simpa only [signedBase_inv] using hs
    have hprev :
        G.loopCompletedStep (PSTS.SignedLetter.inv s)
          (G.loopCompletedStep s v) ∈
        G.BComponentVertexSet B anchor :=
      G.loopCompletedStep_BComponent_forward B anchor
        (PSTS.SignedLetter.inv s) hsInv
        (G.loopCompletedStep s v) hnext
    simpa only [G.loopCompletedStep_inverse hpaired s v]
      using hprev
  · exact G.loopCompletedStep_BComponent_forward B anchor s hs v

/-- The complement of ONE true old B-component is closed
under EVERY real or stationary signed B-transition of the
legally loop-completed stage. This prevents unintended
identifications with unrelated old component-tagged vertices
when adjoining a full H[B] coset. -/
theorem loopCompletedStep_outside_BComponent
    (G : EGraph V Edge ι)
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι) (anchor : V)
    (s : SignedLabel ι) (hs : signedBase s ∈ B)
    (v : V) (houtside : v ∉ G.BComponentVertexSet B anchor) :
    G.loopCompletedStep s v ∉ G.BComponentVertexSet B anchor := by
  intro hnext
  exact houtside ((G.loopCompletedStep_BComponent_mem_iff
    hpaired B anchor s hs v).mp hnext)

end EGraph
end ABO
end PSTSEPPA
