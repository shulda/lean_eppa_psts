import PSTSEPPA.ABO.RankTwoClusterPropertyBase
import PSTSEPPA.ABO.CompletedFullCosetStage

/-!
# Corrected ABO Proposition 5.4: rank-two component shapes survive completion

The source's k=1 repair R2 classifies singleton-labelled
components in the finite complete stage built from rank-two
full coset extensions. The earlier kernel-checked
Proposition-4.4 base gives an exact dichotomy INSIDE the
incomplete tagged multi-coset EGraph:

* a full component-tagged B-coset constituent;
* an isolated singleton outside that constituent.

The newer #264 and #267 results prove that TRIVIAL completion
by missing loops preserves *all* B-path reachability.

This file now transfers the rank-two full-coset-versus-singleton
dichotomy to the ACTUAL COMPLETE action EGraph of the canonical
rank-two full coset extension. In particular the singleton
alternative remains fixed by every B-word after completion,
so newly added loops cannot invalidate the R2 base.

The augmented Z₁ objects and the group action on their disjoint
union still require the separately audited Corollary-3.15 /
Proposition-3.24 component classification; the full 1-stability
G₂→H₁ is NOT asserted here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- For a rank-two skeleton, every actual B-component of its
CANONICALLY COMPLETED full coset extension is either exactly
one full tagged B-coset constituent or an isolated singleton.
The result is stated using real signed EGraph Follows paths
in the COMPLETED graph, not merely a setwise coset partition.

This closes the complete-stage shape part of corrected
Proposition-5.4's k=1 base for unaugmented full extensions. -/
theorem rankTwo_completedStage_B_component_full_or_singleton
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret) :
    (∃ p : K.AttachedCosetVertex B,
      z = K.multiCosetInclude (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret
        B hBP p ∧
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.allProperCompletedStage
              (K.admissible_of_card_le_two hcard.le)
              hgen hret hcard.ge).toEGraph.Follows z w y) ↔
        ∃ q : K.AttachedCosetVertex B,
          q.1 = p.1 ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            (K.admissible_of_card_le_two hcard.le)
            hgen hret B hBP q) ∨
    (∀ y : K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.allProperCompletedStage
              (K.admissible_of_card_le_two hcard.le)
              hgen hret hcard.ge).toEGraph.Follows z w y) →
        y = z) := by
  let hadm : K.AdmissibleForCosetExtension :=
    K.admissible_of_card_le_two hcard.le
  let P := allProperCosetFamily A
  let hweak : K.MultiCosetWeaklyComplete P hadm hgen hret :=
    allProperCosetFamily_weaklyComplete K hadm hgen hret hcard.ge
  let CE := K.multiCosetEGraph P hadm hgen hret
  let hpaired : CE.LocallyPairedLabels :=
    K.multiCoset_locallyPairedLabels_of_weakComplete
      P hadm hgen hret hweak
  have hpaths
      (x y : K.MultiCosetVertex P hadm hgen hret) :
      (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.allProperCompletedStage hadm hgen hret hcard.ge).toEGraph.Follows
          x w y) ↔
      (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        CE.Follows x w y) :=
    CE.trivialLoopCompletion_B_reachable_iff hpaired B x y
  obtain ⟨p, hz, hComponent⟩ | ⟨hSingleton, _⟩ :=
    K.rank_two_B_component_full_or_singleton_with_core_support
      hcard.le hgen hret B hBP z
  · left
    refine ⟨p, hz, ?_⟩
    intro y
    exact (hpaths z y).trans (hComponent y)
  · right
    intro y hReach
    exact hSingleton y ((hpaths z y).mp hReach)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
