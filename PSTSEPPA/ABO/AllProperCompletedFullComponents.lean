import PSTSEPPA.ABO.AllProperCompletedParentComponents
import PSTSEPPA.ABO.TrivialCompletionSupportedReachability
import PSTSEPPA.ABO.AllProperCosetEdgeSupport

/-!
# Entire connected components of the LEGAL full proper-coset completion

For an arbitrary admissible incomplete signed Cayley skeleton K with
parent A and its genuine full proper-alphabet coset EGraph CE(K;P_A),
the completed stage adds only the legally missing stationary signed
loops. All real oriented edges of that multi-coset extension have
underlying generator in A, so all generators outside A act by identity.

The previous checked exact A-component theorem classifies signed
A-word paths by the original K A-component tags of the genuinely
component-tagged coset quotient points. Every arbitrary signed word
in the *complete* action has the same endpoint as its restriction
to A; hence it cannot connect different original A-components.

The full connected components of the ACTUAL complete signed stage,
with no bound on word length or alphabet, are therefore EXACTLY
the fibres of the old K A-component tag.

This is the vertex-and-path portion of the missing original
Section-5 componentwise decomposition. A further signed graph
edge-surjective local CE-isomorphism and automorphism-equivariant
stage-family assembly are separate downstream obligations; there
is no coordinate-only Cayley collapse.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Entire signed-word REACHABILITY in the LEGAL completed
full proper-coset extension is equivalent to equality of the
true original parent A-component tags. No extra labels or
stationary fixed loops can merge distinct original components. -/
theorem allProperCompletedStage_reachable_iff_parent
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (p q : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    (K.allProperCompletedStage hadm hgen hret hcard).Reachable p q ↔
      (K.multiCosetVertexToParent
        (allProperCosetFamily A) hadm hgen hret A
        allProperCosetFamily_alphabets_subset_parent p).1 =
      (K.multiCosetVertexToParent
        (allProperCosetFamily A) hadm hgen hret A
        allProperCosetFamily_alphabets_subset_parent q).1 := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let hweak := allProperCosetFamily_weaklyComplete
    K hadm hgen hret hcard
  let hpaired : G.LocallyPairedLabels :=
    K.multiCoset_locallyPairedLabels_of_weakComplete
      P hadm hgen hret hweak
  have hFull :=
    G.trivialLoopCompletion_reachable_iff_supported_path
      A (K.allProperCosetEdge_label_mem_parent hadm hgen hret)
      hpaired p q
  have hParent :=
    K.allProperCompletedStage_A_reachable_iff_parent
      hadm hgen hret hcard p q
  exact hFull.trans hParent

end CayleySubgraphSpec
end ABO
end PSTSEPPA
