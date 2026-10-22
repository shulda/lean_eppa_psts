import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents
import PSTSEPPA.ABO.CosetConnectivity

/-!
# Reversal of ACTUAL finite signed E-graph paths

In the ABO model each geometric edge carries TWO actual directed
edge tokens connected by a fixed-point-free formal inverse,
even at loops. Therefore the reverse of a genuine signed
path u --w--> v is the genuine path v --inv(w)--> u.

This statement holds for INCOMPLETE deterministic EGraphs:
it does not invent any missing directed edge. Every edge of
the reversed path is exactly the formal inverse of the
corresponding old/fresh edge token of the original path.
It is independent of group coset values and quotient tags.

The signed reverse-path lemma is used in the corrected upward
Theorem 4.7(iii) two-constituent proper cluster case: we
construct two real forward paths from the two endpoints into
their selected full cosets, reverse the second one, and
only THEN apply the previously certified genuine core
coalescence by source CE embeddedness.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V Edge ι : Type*} (G : EGraph V Edge ι)

/-- Reverse an ACTUAL original signed path, preserving
positive/inverse edge tokens and all genuine old/fresh
source–target incidences. Works for missing edges and loops. -/
theorem follows_signedWord_reverse
    {u v : V} {w : LabelWord ι}
    (h : G.Follows u w v) :
    G.Follows v (PSTS.SignedWord.inv w) u := by
  induction h with
  | nil u =>
      change G.Follows u [] u
      exact EGraph.Follows.nil u
  | @cons u v s w e hs hl hrest ih =>
      rw [PSTS.SignedWord.inv_cons]
      have hReverseEdge :
          G.Follows (G.target e) [PSTS.SignedLetter.inv s] u := by
        refine EGraph.Follows.cons (G.inv e) ?_ ?_ ?_
        · rfl
        · calc
            G.label (G.inv e) =
              PSTS.SignedLetter.inv (G.label e) :=
              G.toLabelledGraph.label_inv e
            _ = PSTS.SignedLetter.inv s :=
              congrArg PSTS.SignedLetter.inv hl
        · rw [show G.target (G.inv e) = G.source e from
            G.toLabelledGraph.target_inv e]
          rw [hs]
          exact EGraph.Follows.nil u
      exact G.follows_append ih hReverseEdge

end EGraph
end ABO
end PSTSEPPA
