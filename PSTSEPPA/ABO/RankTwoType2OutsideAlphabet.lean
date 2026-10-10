import PSTSEPPA.ABO.IsolatedCosetOutsideSupport
import PSTSEPPA.ABO.RankTwoOffComponentCompletedStage

/-!
# Outside-A generator words on the actual rank-two type-(2) stage

In the corrected ABO rank-one Proposition 5.4 repair,
singleton generators outside the parent alphabet A
must not produce an accidental transition in a completed
augmented A-stage.

The all-proper multi-CE has only real A-labelled edges;
the type-(2) singleton augmentation attaches a complete
B-coset for B⊂A and hence introduces only B-labelled
edges. The legal loop-only completion therefore makes
EVERY generator outside A a fixed-point permutation
on ALL old and new vertices.

This source-specializes the separately certified edge
support theorem and generic isolated-coset gluing result
to the genuine rank-two quotient and its completed
Definition 5.3 type-(2) singleton-augmentation stage.

Every signed word on C disjoint A fixes all vertices,
even without the word being trivial in the ambient group.
Together with the all-proper-C word kernel, this supplies
the two generator-label regimes necessary for full
rank-one stage stability.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A word supported entirely outside A fixes all
vertices of the actual completed rank-two off-component
type-(2) full-coset augmentation, including its old root. -/
theorem rankTwoOffComponentCompletedStage_outside_A_word_fixes
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret)
    (hOff : ¬ ∃ q : K.AttachedCosetVertex B,
      K.multiCosetInclude (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le)
        hgen hret B hBP q = z)
    (C : Finset ι) (hdis : Disjoint C A)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (v : IsolatedCosetGluing.Vertex
      (K.MultiCosetVertex (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le) hgen hret)
      gen B
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        (K.admissible_of_card_le_two hcard.le)
        hgen hret z)) :
    (K.rankTwoOffComponentCompletedStage
      hcard hgen hret B hBP z hOff).followWord v w = v := by
  let hadm : K.AdmissibleForCosetExtension :=
    K.admissible_of_card_le_two hcard.le
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let g : Γ := K.multiCosetAmbientValue P hadm hgen hret z
  let hpaired : G.LocallyPairedLabels :=
    K.rankTwo_fullProperCE_locallyPaired hcard hgen hret
  have hBA : B ⊆ A :=
    ((mem_allProperCosetFamily A B).mp hBP).subset
  have hMissing : ∀ e : K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret,
      G.source e = z → signedBase (G.label e) ∉ B := by
    intro e he
    exact K.rank_two_off_selected_B_no_outgoing_edges
      hcard.le hgen hret B hBP z hOff e he
  have hOldSupport : ∀ e : K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret,
      signedBase (G.label e) ∈ A :=
    K.allProperCosetEdge_label_mem_parent hadm hgen hret
  exact IsolatedCosetGluing.completedStage_outside_parent_word_fixes
    G gen A B hBA g z hMissing hOldSupport hpaired
    C hdis w hw v

end CayleySubgraphSpec
end ABO
end PSTSEPPA
