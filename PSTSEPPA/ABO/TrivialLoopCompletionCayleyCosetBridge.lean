import PSTSEPPA.ABO.TrivialLoopCompletionStripPaths
import PSTSEPPA.ABO.CayleyStageProjection
import PSTSEPPA.ABO.CosetConnectivity

/-!
# Project actual signed Cayley B-coset paths through LEGAL loop completion

The corrected ABO bridge-freeness argument needs more than a
based Cayley-to-stage graph morphism: if two group points differ
by a word over B, their images should be connected in the OLD
incomplete stage, rather than merely in the legally completed
graph. We prove this precisely for any locally paired EGraph.

Given any label-preserving map from Cayley(Γ) into the actual
legal stationary-loop completion of an incomplete EGraph G,
every B-coset connection g -> h in Γ yields a genuine signed
B-path IN G between their images. The proof maps an actual
B-word Cayley path, then uses the constructive certified
removal of ONLY newly introduced stationary loops. Both
positive and formal inverse edge tokens are preserved.

No injectivity or surjectivity is required for the map:
this is a bridge-LIFTING criterion for points in the Cayley
image, NOT the general embedding or bridge-freeness of a
coset extension. We also specialize to the canonical
group-to-transition based Cayley projection. Corrected ABO
Theorem 4.7 still needs the further component/cluster/embedding
argument and the higher-rank induction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V Edge Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace EGraph

variable (G : EGraph V Edge ι)

/-- Every B-coset connection in a labelled Cayley graph projects,
along ANY labelled graph morphism into the legal completion,
to a TRUE B-path in the old, INCOMPLETE signed EGraph G.
The new stationary loops are erased, not mistaken for edges. -/
theorem trivialLoopCompletion_cayleyCoset_oldPath
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      (G.trivialLoopCompletion hpaired).toEGraph.toLabelledGraph)
    (B : Finset ι)
    (g h : Γ)
    (hcoset : h ∈ generatedLeftCoset gen B g) :
    ∃ q : LabelWord ι,
      LabelWord.Uses B q ∧
      G.Follows (F.onVertex g) q (F.onVertex h) := by
  obtain ⟨w, hwB, hwEnd⟩ :=
    (mem_generatedLeftCoset_iff_subalphabetReachable gen B g h).mp hcoset
  have hCayley :
      (cayleyGraph gen).toEGraph.Follows g w h := by
    have hw := (cayleyGraph gen).follows_followWord g w
    rw [hwEnd] at hw
    exact hw
  have hCompleted :
      (G.trivialLoopCompletion hpaired).toEGraph.Follows
        (F.onVertex g) w (F.onVertex h) :=
    hCayley.map F
  exact G.trivialLoopCompletion_stripFollows
    hpaired B (F.onVertex g) (F.onVertex h)
      w hwB hCompleted

/-- The same bridge lifting applies to the ACTUAL canonical
based Cayley projection of any generator-preserving group
homomorphism Γ -> Transition(complete(G)). Surjectivity is
unnecessary for the conditional statement about two given
points of its image. -/
theorem trivialLoopCompletion_groupProjectionCoset_oldPath
    (hpaired : G.LocallyPairedLabels)
    (gen : ι → Γ)
    (φ : Γ →* (G.trivialLoopCompletion hpaired).transitionGroup)
    (hφ : ∀ i : ι,
      φ (gen i) =
        (G.trivialLoopCompletion hpaired).transitionSubgroupGenerator i)
    (u : V)
    (B : Finset ι)
    (g h : Γ)
    (hcoset : h ∈ generatedLeftCoset gen B g) :
    ∃ q : LabelWord ι,
      LabelWord.Uses B q ∧
      G.Follows
        ((G.trivialLoopCompletion hpaired).cayleyProjectionFromGroup
          gen φ hφ u).onVertex g
        q
        ((G.trivialLoopCompletion hpaired).cayleyProjectionFromGroup
          gen φ hφ u).onVertex h := by
  exact G.trivialLoopCompletion_cayleyCoset_oldPath
    hpaired gen
    ((G.trivialLoopCompletion hpaired).cayleyProjectionFromGroup
      gen φ hφ u) B g h hcoset

end EGraph
end ABO
end PSTSEPPA
