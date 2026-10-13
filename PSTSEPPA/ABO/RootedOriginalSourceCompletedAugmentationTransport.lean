import PSTSEPPA.ABO.RootedOriginalSourceAugmentedGraphTransport
import PSTSEPPA.ABO.RootedFullBAugmentationCompletedActionIso

/-!
# TRUE original H₁ source rank-two completed B-augmentation action isomorphism

The corrected ABO Section-5 source stage must come from a REAL
possibly incomplete H₁-Cayley preimage of the ORIGINAL input
graph, not the artificially completed X₁ action. The genuine
source H₁ is only 2-retractable, not globally retractable.

The preceding source-normalization theorem transports the
literal old+new signed B-augmented EGraph, with all component
and coset tags and the correct common glued root, to the
local Γ[A] skeleton. The generic completed-augmentation theorem
further shows that legal fixed-point-loop completion is natural
for ANY bijective signed graph map with paired old labels.

We instantiate these results on an actual rooted rank-two
source component and a genuine off-selected-B old quotient
vertex. The output is an honest morphism of COMPLETE SIGNED
actions between the Γ[A] local augmented stage and the
root-translated ORIGINAL Γ source stage, bijective on all
vertices and oriented action-edge tokens, preserving and
reflecting EVERY realised signed path.

The source type-(2) catalogue-index identification and
source-specific named-stage API conversion remain separate.
The exact Z₁ family also contains type-(1) augmented clusters;
corrected Condition 5.2 and later rank induction remain OPEN.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The truly locally-normalized rank-two B-augmentation,
LEGALLY completed only by missing stationary signed loops. -/
noncomputable def rootedLocalOffCosetCompletedStage
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :=
  IsolatedCosetGluing.completedStage
    (K.rootedLocalMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    (trivialCompletionGenerator gen A) B
    ((K.intrinsicComponentLocalSlice A root).multiCosetAmbientValue
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le) z)
    z
    (by intro e he
        exact K.rootedLocalOffCoset_no_old_B_edge
          A hcard hret root B hBP z hOffSource e he)
    (K.rootedLocalAllProperMultiCoset_locallyPairedLabels
      A hcard hret root)

/-- The corresponding TRUE original-source H₁ augmented
COMPLETE action in explicit root-TRANSLATED coordinates.
Its identified root remains the old component-tagged
quotient point, and all other attached B-points are fresh. -/
noncomputable def rootedTranslatedSourceOffCosetCompletedStage
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :=
  IsolatedCosetGluing.completedStage
    (K.rootedAmbientMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    gen B
    (root.1 * ((K.intrinsicComponentLocalSlice A root).multiCosetAmbientValue
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le) z : Γ))
    (K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root (allProperCosetFamily A) z)
    (by intro e he
        exact K.rootedAmbientOffCoset_no_old_B_edge
          A hcard hret root B hBP z hOffSource e he)
    (K.rootedAmbientAllProperMultiCoset_locallyPairedLabels
      A hcard hret root)

/-- The local Γ[A] B-augmented complete signed action
maps to the ACTUAL root-translated original H₁ action.
The map preserves all old/new signed transitions, inversion
and fixed-point loops, without globally retractable Γ. -/
noncomputable def rootedSourceOffCosetCompletedStageHom
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :
    LabelledGraphHom
      (K.rootedLocalOffCosetCompletedStage
        A hcard hret root B hBP z hOffSource).toEGraph.toLabelledGraph
      (K.rootedTranslatedSourceOffCosetCompletedStage
        A hcard hret root B hBP z hOffSource).toEGraph.toLabelledGraph :=
  rootedFullBAugmentationCompletedStageHom
    (K.rootedLocalMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    (K.rootedAmbientMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    (K.rootedMultiCosetCompletedEGraphHom
      A hcard hret root (allProperCosetFamily A))
    (K.rootedMultiCosetCompletedEGraphHom_bijective
      A hcard hret root (allProperCosetFamily A)).1
    (K.rootedMultiCosetCompletedEGraphHom_bijective
      A hcard hret root (allProperCosetFamily A)).2
    gen A B (((allProperCosetFamily A).proper B hBP).subset)
    root.1
    ((K.intrinsicComponentLocalSlice A root).multiCosetAmbientValue
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le) z)
    z
    (K.rootedLocalOffCoset_no_old_B_edge
      A hcard hret root B hBP z hOffSource)
    (K.rootedAmbientOffCoset_no_old_B_edge
      A hcard hret root B hBP z hOffSource)
    (K.rootedLocalAllProperMultiCoset_locallyPairedLabels
      A hcard hret root)
    (K.rootedAmbientAllProperMultiCoset_locallyPairedLabels
      A hcard hret root)

/-- True source/local complete augmented actions are
BIJECTIVE on all vertices and all formal directed signed
action-edge tokens, including newly added fixed loops. -/
theorem rootedSourceOffCosetCompletedStageHom_bijective
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :
    Function.Bijective
      (K.rootedSourceOffCosetCompletedStageHom
        A hcard hret root B hBP z hOffSource).onVertex ∧
    Function.Bijective
      (K.rootedSourceOffCosetCompletedStageHom
        A hcard hret root B hBP z hOffSource).onEdge := by
  exact rootedFullBAugmentationCompletedStageHom_bijective
    (K.rootedLocalMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    (K.rootedAmbientMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    (K.rootedMultiCosetCompletedEGraphHom
      A hcard hret root (allProperCosetFamily A))
    (K.rootedMultiCosetCompletedEGraphHom_bijective
      A hcard hret root (allProperCosetFamily A)).1
    (K.rootedMultiCosetCompletedEGraphHom_bijective
      A hcard hret root (allProperCosetFamily A)).2
    gen A B (((allProperCosetFamily A).proper B hBP).subset)
    root.1
    ((K.intrinsicComponentLocalSlice A root).multiCosetAmbientValue
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le) z)
    z
    (K.rootedLocalOffCoset_no_old_B_edge
      A hcard hret root B hBP z hOffSource)
    (K.rootedAmbientOffCoset_no_old_B_edge
      A hcard hret root B hBP z hOffSource)
    (K.rootedLocalAllProperMultiCoset_locallyPairedLabels
      A hcard hret root)
    (K.rootedAmbientAllProperMultiCoset_locallyPairedLabels
      A hcard hret root)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
