import PSTSEPPA.ABO.MultiCosetParentComponentExact
import PSTSEPPA.ABO.CompletedFullCosetStage

/-!
# Parent A-components of the legally completed full proper-coset extension

The corrected ABO Section 5.3 construction completes every proper
B⊊A-coset of an original incomplete A-Cayley skeleton K, then
adds only the legally missing stationary signed loops.

Every old B-constituent has B⊆A. The previously checked parent
fold makes the intrinsic *original* A-component tag of a
quotient vertex invariant under all genuine A-labelled edges.
Conversely two quotient vertices with the same intrinsic
A-component tag are joined by an actual A-path.

Legal loop-only completion neither merges vertices nor creates
new A-connections. Hence A-reachability in the COMPLETE signed
full-CE action is characterized EXACTLY by equality of the
true old-skeleton A-component tags. In particular no two
separate A-components of the original source H₁-cover can be
glued together by coset identification or loop completion.

This is a component-level step toward faithful source
Definition-5.3 decomposition. It does not claim the stronger
labelled edge-surjective graph isomorphism between each original
disconnected full CE and a disjoint family of connected CEs.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every selected alphabet in the canonical full proper-coset
family is contained in the parent A, including B=∅. -/
theorem allProperCosetFamily_alphabets_subset_parent :
    ∀ B ∈ (allProperCosetFamily A).alphabets, B ⊆ A := by
  intro B hBA
  exact ((allProperCosetFamily A).proper B hBA).subset

/-- The original A-component tag of the source incomplete
skeleton precisely classifies signed A-word paths in the
LEGAL COMPLETED full proper-coset action. Distinct original
component tags can NEVER be identified or newly connected. -/
theorem allProperCompletedStage_A_reachable_iff_parent
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (p q : K.MultiCosetVertex (allProperCosetFamily A) hadm hgen hret) :
    (∃ w : LabelWord ι,
      LabelWord.Uses A w ∧
        (K.allProperCompletedStage hadm hgen hret hcard).toEGraph.Follows
          p w q) ↔
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
  have hLoop :=
    G.trivialLoopCompletion_B_reachable_iff hpaired A p q
  have hParent :=
    K.multiCosetEGraph_B_reachable_iff_parent_index
      P hadm hgen hret A
      allProperCosetFamily_alphabets_subset_parent p q
  exact hLoop.trans hParent

end CayleySubgraphSpec
end ABO
end PSTSEPPA
