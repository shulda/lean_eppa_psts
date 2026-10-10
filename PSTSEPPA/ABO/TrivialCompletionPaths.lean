import PSTSEPPA.ABO.TrivialLoopCompletion
import PSTSEPPA.ABO.CosetConnectivity

/-!
# Trivial loop completion reflects genuine subalphabet paths

Corrected ABO Proposition 5.4 repeatedly uses the fact that
"trivial completion introduces only loops" and therefore creates
no new connectivity for any chosen generator subalphabet B.

Under the *precise* local-paired condition certified for weakly
complete coset extensions, the preceding module constructs this
loop completion as a total action EGraph. This file completes
its geometric verification.

A real signed B-labelled path in the completed graph can be
transformed, letter by letter, into a REAL B-labelled path in the
original EGraph with the same start and endpoint:

* whenever the signed edge existed originally, retain the letter
  and the corresponding original edge (targets agree exactly);
* whenever that signed edge was absent, the completed edge is a
  fixed-point loop and the letter is dropped.

This handles arbitrary B, inverse letters, repeated labels,
geometric loops, empty B and empty words. No ambient Cayley
injectivity or reflecting-group existence is assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {V Edge ι : Type*}
variable [DecidableEq ι]

namespace EGraph

variable (G : EGraph V Edge ι)

/-- A signed B-path in a loop completion reduces to a signed
B-path in the OLD graph, by deleting only newly added loops.
This is the nontrivial direction: no new B-reachability is
created by the completion. -/
theorem trivialLoopCompletion_B_path_reflect
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι)
    (u v : V) (w : LabelWord ι)
    (hUses : LabelWord.Uses B w)
    (hPath :
      (G.trivialLoopCompletion hpaired).toEGraph.Follows u w v) :
    ∃ q : LabelWord ι,
      LabelWord.Uses B q ∧
      G.Follows u q v := by
  let T := G.trivialLoopCompletion hpaired
  induction w generalizing u v with
  | nil =>
      have huv : u = v := T.toEGraph.follows_nil_iff.mp hPath
      subst v
      exact ⟨[], LabelWord.uses_nil B, EGraph.Follows.nil u⟩
  | cons s w ih =>
      cases hPath with
      | cons e hsrc hlab hrest =>
          have heq : e = (u,s) := by
            apply Prod.ext
            · exact hsrc
            · exact hlab
          by_cases hOld :
              ∃ eOld : Edge, G.source eOld = u ∧ G.label eOld = s
          · obtain ⟨eOld, hOldSource, hOldLabel⟩ := hOld
            have htgt : T.target e = G.target eOld := by
              calc
                T.target e = T.target (u,s) := congrArg T.target heq
                _ = T.target (G.source eOld, G.label eOld) := by
                    rw [hOldSource, hOldLabel]
                _ = G.target eOld :=
                    G.trivialLoopCompletion_target_existing hpaired eOld
            have htail : T.toEGraph.Follows (G.target eOld) w v := by
              rw [← htgt]
              exact hrest
            obtain ⟨q, hqUses, hqPath⟩ :=
              ih hUses.2 htail
            refine ⟨s :: q, ⟨hUses.1, hqUses⟩, ?_⟩
            exact EGraph.Follows.cons eOld hOldSource hOldLabel hqPath
          · have htgt : T.target e = u := by
              rw [heq]
              exact G.trivialLoopCompletion_loop_of_missing
                hpaired u s hOld
            have htail : T.toEGraph.Follows u w v := by
              rw [← htgt]
              exact hrest
            exact ih hUses.2 htail

/-- Trivial loop completion preserves and reflects the EXISTENCE
of genuine B-paths between old vertices. All vertices are old,
because the completion adds no points. -/
theorem trivialLoopCompletion_B_reachable_iff
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι) (u v : V) :
    (∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (G.trivialLoopCompletion hpaired).toEGraph.Follows u w v) ↔
    (∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      G.Follows u w v) := by
  constructor
  · rintro ⟨w, hUses, hp⟩
    exact G.trivialLoopCompletion_B_path_reflect
      hpaired B u v w hUses hp
  · rintro ⟨w, hUses, hp⟩
    exact ⟨w, hUses,
      hp.map (G.trivialLoopCompletionHom hpaired)⟩

end EGraph
end ABO
end PSTSEPPA
