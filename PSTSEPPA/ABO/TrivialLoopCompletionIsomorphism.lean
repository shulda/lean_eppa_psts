import PSTSEPPA.ABO.TrivialLoopCompletion
import PSTSEPPA.ABO.BijectiveGraphPathReflection

/-!
# Trivial loop completion preserves genuine signed graph isomorphisms

The corrected ABO constructions complete a locally paired EGraph by
adding only missing signed-label loops, with NO new vertices. This
construction must commute with the rooted source/local graph
isomorphisms, or the source Z1 completed action could diverge from
the verified local stage despite perfect agreement before completion.

We prove that every vertex- and oriented-edge-bijective labelled
graph morphism commutes with the ACTUAL loop-completed transition of
every signed label, including inverses and trivial group generators.
Under separately supplied locally-paired hypotheses, its vertex map
then extends to an honest isomorphism of the two COMPLETE action
graphs and preserves AND REFLECTS all labelled words/paths.

There is no assumption about ambient Cayley coordinates or group
retractability; this lemma is reusable for both the PSTS/ABO
source component step and later coset augmentations.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V W E F ι : Type*}
variable (G : EGraph V E ι) (H : EGraph W F ι)

/-- Exact naturality of each *signed* step completed by stationary
loops, provided the old incomplete signed graphs are truly isomorphic.
No local pairing condition is needed just to compare the steps. -/
theorem loopCompletedStep_natural_of_bijective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (s : SignedLabel ι) (u : V) :
    H.loopCompletedStep s (f.onVertex u) =
      f.onVertex (G.loopCompletedStep s u) := by
  classical
  by_cases hOld : ∃ e : E, G.source e = u ∧ G.label e = s
  · obtain ⟨e, hs, hl⟩ := hOld
    have hsH : H.source (f.onEdge e) = f.onVertex u :=
      (f.map_source e).trans (congrArg f.onVertex hs)
    have hlH : H.label (f.onEdge e) = s :=
      (f.map_label e).trans hl
    calc
      H.loopCompletedStep s (f.onVertex u) =
        H.target (f.onEdge e) :=
          H.loopCompletedStep_of_edge s (f.onVertex u)
            (f.onEdge e) hsH hlH
      _ = f.onVertex (G.target e) := f.map_target e
      _ = f.onVertex (G.loopCompletedStep s u) :=
        congrArg f.onVertex
          (G.loopCompletedStep_of_edge s u e hs hl).symm
  · have hMissingH :
        ¬ ∃ e : F, H.source e = f.onVertex u ∧ H.label e = s := by
      rintro ⟨edge, hsrc, hlab⟩
      obtain ⟨e, rfl⟩ := he.2 edge
      have hs : G.source e = u := by
        apply hv.1
        exact (f.map_source e).symm.trans hsrc
      have hl : G.label e = s :=
        (f.map_label e).symm.trans hlab
      exact hOld ⟨e, hs, hl⟩
    calc
      H.loopCompletedStep s (f.onVertex u) = f.onVertex u :=
        H.loopCompletedStep_of_missing s (f.onVertex u) hMissingH
      _ = f.onVertex (G.loopCompletedStep s u) := by
        rw [G.loopCompletedStep_of_missing s u hOld]

/-- A genuine morphism of the completed signed EGraphs, preserving
old transitions and every newly added fixed-point loop. The edge
type is now the canonical (source, signed label) action token. -/
noncomputable def trivialLoopCompletionIsoHom
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (hg : G.LocallyPairedLabels)
    (hh : H.LocallyPairedLabels) :
    LabelledGraphHom
      (G.trivialLoopCompletion hg).toEGraph.toLabelledGraph
      (H.trivialLoopCompletion hh).toEGraph.toLabelledGraph where
  onVertex := f.onVertex
  onEdge e := (f.onVertex e.1, e.2)
  map_source _ := rfl
  map_label _ := rfl
  map_inv := by
    rintro ⟨u, s⟩
    apply Prod.ext
    · change f.onVertex (G.loopCompletedStep s u) =
        H.loopCompletedStep s (f.onVertex u)
      exact (G.loopCompletedStep_natural_of_bijective H f hv he s u).symm
    · rfl

/-- Bijective on the actual vertices AND on all oriented SIGNED
action tokens; inverses and geometric loops remain distinct tokens. -/
theorem trivialLoopCompletionIsoHom_bijective
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (hg : G.LocallyPairedLabels)
    (hh : H.LocallyPairedLabels) :
    Function.Bijective
        (G.trivialLoopCompletionIsoHom H f hv he hg hh).onVertex ∧
      Function.Bijective
        (G.trivialLoopCompletionIsoHom H f hv he hg hh).onEdge := by
  constructor
  · exact hv
  · constructor
    · rintro ⟨u, s⟩ ⟨v, t⟩ heq
      have hvertex : u = v := hv.1 (congrArg Prod.fst heq)
      have hlabel : s = t := congrArg Prod.snd heq
      exact Prod.ext hvertex hlabel
    · rintro ⟨x, s⟩
      obtain ⟨u, hu⟩ := hv.2 x
      exact ⟨(u, s), Prod.ext hu rfl⟩

/-- Every genuinely realised word in the loop-completed action
is reflected and preserved by the same vertex equivalence,
including words that traverse the newly inserted fixed loops. -/
theorem trivialLoopCompletionIsoHom_follows_iff
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (hg : G.LocallyPairedLabels)
    (hh : H.LocallyPairedLabels)
    (u v : V) (w : LabelWord ι) :
    (G.trivialLoopCompletion hg).toEGraph.Follows u w v ↔
      (H.trivialLoopCompletion hh).toEGraph.Follows
        (f.onVertex u) w (f.onVertex v) := by
  exact EGraph.follows_iff_bijective
    (G.trivialLoopCompletionIsoHom H f hv he hg hh)
    (G.trivialLoopCompletionIsoHom_bijective H f hv he hg hh).1
    (G.trivialLoopCompletionIsoHom_bijective H f hv he hg hh).2
    u v w

end EGraph
end ABO
end PSTSEPPA
