import PSTSEPPA.ABO.TrivialCompletionPaths
import PSTSEPPA.ABO.StandardCosetFamily
import PSTSEPPA.ABO.MultiCosetSkeletonComponentIntersections

/-!
# Complete full coset stages preserve intrinsic B-components of the skeleton

The independently audited ABO Section 5 construction forms complete
stage graphs by starting from a weakly complete multi-coset extension
and then performing a TRIVIAL completion, adding loops for missing
signed labels but preserving all old vertices.

This module connects four independent kernel-checked results:

1. A weakly complete multi-coset extension has simultaneously available
   positive/negative signs for each generator at each vertex (#262).
2. Such an E-graph admits an ACTUAL complete action E-graph on the same
   vertices, with only loops added for missing labels (#263).
3. Its trivial completion preserves and reflects genuine B-reachability
   for EVERY subalphabet B (#264).
4. If B itself occurs as one of the completed constituent alphabets,
   a genuine B-path between OLD skeleton vertices in the multi-coset
   extension is equivalent to an original B-path in the skeleton
   (A2 selected-component theorem).

Therefore the full multi-coset completion followed by literal trivial
completion does not introduce ANY new B-component connections among
the original skeleton vertices, for any selected B. In particular,
for the canonical family of ALL proper subalphabets of A and |A|>=2,
it works for EVERY proper B subset A.

This is a source-facing geometric ingredient for the finite tower and
the k=1 repair of Proposition 5.4. It does NOT establish the harder
rank-(k+1) cluster property, bridge-freeness, the actual stage
H_k-cover assembly, or the k-stability G_(k+1) -> H_k by itself.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The literal COMPLETE action graph of a weakly complete
multi-coset extension, on EXACTLY the same tagged vertex quotient.
The graph action fixes vertices where a generator label is missing. -/
noncomputable def weakMultiCosetCompletedStage
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hweak : K.MultiCosetWeaklyComplete P hadm hgen hret) :
    CompleteEGraph
      (K.MultiCosetVertex P hadm hgen hret)
      (ActionEdge (K.MultiCosetVertex P hadm hgen hret) ι)
      ι :=
  (K.multiCosetEGraph P hadm hgen hret).trivialLoopCompletion
    (K.multiCoset_locallyPairedLabels_of_weakComplete
      P hadm hgen hret hweak)

/-- Every selected B's true component relation on original
skeleton vertices is unchanged by full multi-coset extension
and subsequent trivial completion by missing loops. -/
theorem weakMultiCosetCompletedStage_skeleton_B_reachable_iff
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hweak : K.MultiCosetWeaklyComplete P hadm hgen hret)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (x y : K.Vertex) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.weakMultiCosetCompletedStage P hadm hgen hret hweak).toEGraph.Follows
        ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x)
        w
        ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex y)) ↔
      K.SubalphabetReachable B x y := by
  let CE := K.multiCosetEGraph P hadm hgen hret
  let hpaired : CE.LocallyPairedLabels :=
    K.multiCoset_locallyPairedLabels_of_weakComplete
      P hadm hgen hret hweak
  let f := K.skeletonToMultiCosetHom P hadm hgen hret B hBP
  have hLoop :=
    CE.trivialLoopCompletion_B_reachable_iff
      hpaired B (f.onVertex x) (f.onVertex y)
  have hSkeleton :=
    K.multiCoset_selected_skeleton_B_reachable_iff
      P hadm hgen hret B hBP x y
  exact hLoop.trans hSkeleton

/-- The canonical finite family of ALL proper subalphabets
produces a weakly complete extension whenever |A|>=2.
Therefore it also produces an actual complete stage E-graph
by adding only missing signed loops. -/
noncomputable def allProperCompletedStage
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card) :
    CompleteEGraph
      (K.MultiCosetVertex (allProperCosetFamily A) hadm hgen hret)
      (ActionEdge
        (K.MultiCosetVertex (allProperCosetFamily A) hadm hgen hret) ι)
      ι :=
  K.weakMultiCosetCompletedStage
    (allProperCosetFamily A) hadm hgen hret
      (allProperCosetFamily_weaklyComplete K hadm hgen hret hcard)

/-- Source-facing rank >= 2 specialisation: for EVERY proper
B subset A, the canonical full coset extension with the
trivial loop completion reflects exactly the OLD skeleton
B-components between embedded skeleton points. -/
theorem allProperCompletedStage_skeleton_B_reachable_iff
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι) (hBA : B ⊂ A)
    (x y : K.Vertex) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.allProperCompletedStage hadm hgen hret hcard).toEGraph.Follows
        ((K.skeletonToMultiCosetHom
          (allProperCosetFamily A) hadm hgen hret B
          ((mem_allProperCosetFamily A B).mpr hBA)).onVertex x)
        w
        ((K.skeletonToMultiCosetHom
          (allProperCosetFamily A) hadm hgen hret B
          ((mem_allProperCosetFamily A B).mpr hBA)).onVertex y)) ↔
    K.SubalphabetReachable B x y := by
  exact K.weakMultiCosetCompletedStage_skeleton_B_reachable_iff
    (allProperCosetFamily A) hadm hgen hret
    (allProperCosetFamily_weaklyComplete K hadm hgen hret hcard)
    B ((mem_allProperCosetFamily A B).mpr hBA) x y

end CayleySubgraphSpec
end ABO
end PSTSEPPA
