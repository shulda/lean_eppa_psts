import PSTSEPPA.ABO.IsolatedCosetGlobalWordKernel
import PSTSEPPA.ABO.RankTwoOffComponentCompletedStage
import PSTSEPPA.ABO.RankTwoCompletedWordKernel

/-!
# Global rank-two identity-word kernel on the ACTUAL ABO type-(2) stage

This combines two previously certified geometric inputs for the corrected
Auinger--Bitterlich--Otto Proposition 5.4 at k=1:

* The source-corrected canonical rank-two full proper-alphabet coset
  extension has an actual complete action whose B-word kernel contains
  every ambient identity-valued B-word, at EVERY old vertex.
* The singleton type-(2) full B-coset augmentation preserves that kernel
  under actual deterministic full-coset gluing and legal loop-only
  completion, including all OLD off-root vertices and all NEW points.

The resulting theorem concerns the LITERAL rank-two type-(2) augmented
full coset extension, constructed from an actual Cayley skeleton, its
component-tagged multi-coset quotient, and a root off every selected
B-coset. It proves the word identity for every point of the entire
completed stage, not just the attached coset or a hypothesized action.

Together with the preexisting ordinary rank-two completed full-coset
kernel and augmented-cluster singleton kernel, this closes the
rank-two **per-stage word-kernel** check for the type-(2) singleton
alternative of the corrected Definition 5.3 stage catalogue.

The actual assembly of the finite Z1 family, the map G2→H1
and proof of its 1-stability, and higher rank remain separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Any B-word trivial in the ambient generating group fixes
EVERY point of a genuinely completed rank-two type-(2)
full-coset augmentation at an off-B-component singleton.

This quantifies over all old tagged multi-CE vertices as well
as the genuinely newly attached B-coset vertices, not only
the root, and does not assume a global morphism between
old and augmented complete EGraphs. -/
theorem rankTwoOffComponentCompletedStage_identity_B_word_fixes
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
    (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
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
  have hMissing : ∀ e : K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret,
      G.source e = z → signedBase (G.label e) ∉ B := by
    intro e he
    exact K.rank_two_off_selected_B_no_outgoing_edges
      hcard.le hgen hret B hBP z hOff e he
  have hOldKernel :
      ∀ x : K.MultiCosetVertex P hadm hgen hret,
        (G.trivialLoopCompletion hpaired).followWord x w = x := by
    intro x
    exact K.rankTwo_completedStage_identity_B_word_fixes
      hcard hgen hret B hBP w hw hval x
  exact IsolatedCosetGluing.completedStage_B_identity_word_fixes_every_vertex
    G gen B g z hMissing hpaired w hw hval hOldKernel v

end CayleySubgraphSpec
end ABO
end PSTSEPPA
