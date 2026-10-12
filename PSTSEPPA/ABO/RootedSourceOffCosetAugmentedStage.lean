import PSTSEPPA.ABO.RootedSourceOffCosetNoOldEdges
import PSTSEPPA.ABO.RootedSourceMultiCosetAmbientValue
import PSTSEPPA.ABO.IsolatedCosetCompletion

/-!
# Genuine source-rooted rank-two type-(2) B-coset augmentation

Corrected ABO Definition 5.3 requires REAL source H1-cover
augmentations, not just stages over a globally retractable local
Γ[A] model. Source H1 is only 2-retractable and its completed
multi-coset vertices retain all component/alphabet tags.

Here we combine three independently established facts:
* the literal true source-rooted multi-coset signed EGraph exists,
  with globally retractable geometry needed only locally (#390);
* exactly the source-eligible off-B roots are preserved (#389);
* no old B-labelled signed edge (even an old loop) leaves such
  a true source root (#397, pending independent CI).

This permits an ACTUAL deterministic EGraph formed by attaching
the honest ambient Γ[B] full coset at the true ambient group
coordinate of the chosen old root (#394), keeping separately
tagged fresh coset points. Since the genuine source plain graph
is locally paired (#396), the augmented graph also admits the
LEGAL stationary-loop completion to a complete signed action.

We do not assert that this is yet isomorphic to the local
Γ[A] augmented stage; that needs transport of the fresh coset
signed edges and gluing of the basepoints, in addition to the
already certified fresh-point bijection (#393). Nor does this
alone establish full source Z1 stage-family coverage, corrected
Condition 5.2, higher-rank reflecting group or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The ACTUAL incomplete signed EGraph obtained from a TRUE
source-rooted rank-two full proper-coset extension by attaching
a newly tagged full ambient B-coset at an eligible off-B vertex.

The old signed edges remain unchanged, and the new edges are
genuine ambient Γ[B] coset transitions; no new old B-edge or
ambient-coordinate collapse is postulated. -/
noncomputable def rootedSourceOffCosetAugmentedEGraph
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :=
  IsolatedCosetGluing.gluedEGraph
    (K.rootedAmbientMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    gen B
    (K.rootedAmbientMultiCosetValue A hcard hret root
      (allProperCosetFamily A)
      (K.rootedLocalMultiCosetVertexQuotientEquiv
        A hcard hret root (allProperCosetFamily A) z))
    (K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root (allProperCosetFamily A) z)
    (by
      intro e he
      exact K.rootedAmbientOffCoset_no_old_B_edge
        A hcard hret root B hBP z hOffSource e he)

/-- The original true source-rooted coset extension injects
as a literal labelled subgraph of the new B-augmentation:
no original vertex or oriented edge is deleted, merged or
relabelled. This includes all inverse edge tokens and loops. -/
noncomputable def rootedSourceOffCosetOldGraphHom
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
      (isGenerated_trivialCompletionGenerator gen A)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le))
    (hOffSource :
      ¬ ∃ q : (K.subalphabetComponentSubgraph A root).AttachedCosetVertex B,
        K.rootedAmbientMultiCosetInclude A hcard hret root
          (allProperCosetFamily A) B hBP q =
        K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z) :=
  IsolatedCosetGluing.oldHom
    (K.rootedAmbientMultiCosetCompletedEGraph
      A hcard hret root (allProperCosetFamily A))
    gen B
    (K.rootedAmbientMultiCosetValue A hcard hret root
      (allProperCosetFamily A)
      (K.rootedLocalMultiCosetVertexQuotientEquiv
        A hcard hret root (allProperCosetFamily A) z))
    (K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root (allProperCosetFamily A) z)
    (by
      intro e he
      exact K.rootedAmbientOffCoset_no_old_B_edge
        A hcard hret root B hBP z hOffSource e he)

/-- The corresponding TRUE source-rooted type-(2)
augmentation after LEGAL completion. Every absent signed
label contributes a fixed-point LOOP; all original signed
edges and new complete B-coset edges remain genuinely
realized. The carrier is the exact disjoint sum of old
tagged quotient points and new non-root B-coset points. -/
noncomputable def rootedSourceOffCosetCompletedStage
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (K.intrinsicComponentLocalSlice A root).MultiCosetVertex
      (allProperCosetFamily A)
      ((K.intrinsicComponentLocalSlice A root).admissible_of_card_le_two
        hcard.le)
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
    (K.rootedAmbientMultiCosetValue A hcard hret root
      (allProperCosetFamily A)
      (K.rootedLocalMultiCosetVertexQuotientEquiv
        A hcard hret root (allProperCosetFamily A) z))
    (K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root (allProperCosetFamily A) z)
    (by
      intro e he
      exact K.rootedAmbientOffCoset_no_old_B_edge
        A hcard hret root B hBP z hOffSource e he)
    (K.rootedAmbientAllProperMultiCoset_locallyPairedLabels
      A hcard hret root)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
