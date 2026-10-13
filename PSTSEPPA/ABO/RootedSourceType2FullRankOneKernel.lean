import PSTSEPPA.ABO.RootedSourceAugmentedRankOneKernel
import PSTSEPPA.ABO.IsolatedCosetDisjointCompletedWords
import PSTSEPPA.ABO.RankOneAlphabetDichotomy
import PSTSEPPA.ABO.RankTwoType2AllProperKernel

/-!
# FULL rank-one word kernel of genuine ORIGINAL H1 type-(2) B-augmentations

Corrected ABO Proposition 5.4 at k=1 requires more than the
selected B-word kernel: EVERY identity-valued signed word supported
on ANY alphabet C of at most one generator must fix EVERY vertex
of every corrected source Definition-5.3 completed type-(2) stage.

Here the ambient original Γ is only TWO-retractable, and the old
graph is the true INCOMPLETE original-source A-Cayley component
(|A|=2), with its exact component-tagged multi-coset quotient.
The genuine B-augmentation of this source component is already
constructed and Lean-certified, including all new full coset points
and its legally loop-completed action.

The proof closes the previously missing singleton C cases:
* On the OLD source completed full-proper-coset stage, every
  identity-valued C-word fixes each vertex. If C⊂A, use the
  certified source proper-C kernel; if C is disjoint from A,
  transport the genuine local Γ[A] outside-A stationary-loop
  kernel along the exact complete ACTION isomorphism.
* If C is disjoint from attached B, the certified generic
  B-augmentation disjoint-C theorem preserves the old completed
  C-action on EVERY old vertex (including root) and inserts only
  fixed loops for C at every NEW B-coset point.
* Otherwise C intersects B. The exact rank-two small-alphabet
  lemma forces C=B, so the independently certified true-source
  B-supported global kernel applies.

The result fixes ALL old, root and fresh vertices, and then proves
the ACTUAL transition-group word value is identity. No global
retractability of original H1, false identification of component
tags or unproved source/local AUGMENTED isomorphism is used.

This is a per-stage original-source type-(2) k=1 kernel, NOT a
proof that ALL source Z1 type-(1)/(2) stages are covered by the
finite source-dependent G2 catalogue, nor Condition 5.2, higher
rank or unconditional PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- FULL source-rooted unaugmented rank-one word kernel,
including singleton letters OUTSIDE the parent alphabet A.
No global ambient Γ retractability. -/
theorem rootedAmbientAllProperCompletedStage_rankOne_word_fixes
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
    (x : Quotient (K.rootedAmbientMultiCosetSetoid
      A hcard hret root (allProperCosetFamily A))) :
    (K.rootedAmbientAllProperCompletedStage
      A hcard hret root).followWord x w = x := by
  rcases small_alphabet_proper_or_disjoint_rank_two
      A C hcard hCcard with hCA | hdis
  · have hCP : C ∈ (allProperCosetFamily A).alphabets :=
      (mem_allProperCosetFamily A C).mpr hCA
    exact K.rootedAmbientAllProperCompletedStage_identity_B_word_fixes
      A hcard hret root C hCP w hw hval x
  · let L := K.intrinsicComponentLocalSlice A root
    let hadm : L.AdmissibleForCosetExtension :=
      L.admissible_of_card_le_two hcard.le
    let hgen : IsGenerated (trivialCompletionGenerator gen A) :=
      isGenerated_trivialCompletionGenerator gen A
    let hretL : Retractable (trivialCompletionGenerator gen A) :=
      retractable_trivialCompletionGenerator_of_kRetractable
        gen 2 hret A hcard.le
    let Tloc := K.rootedLocalAllProperCompletedStage A hcard hret root
    let Tamb := K.rootedAmbientAllProperCompletedStage A hcard hret root
    let f := K.rootedAllProperCompletedStageHom A hcard hret root
    obtain ⟨u, hu⟩ :=
      (K.rootedAllProperCompletedStageHom_bijective
        A hcard hret root).1.2 x
    have hLocal : Tloc.followWord u w = u := by
      change
        (L.allProperCompletedStage hadm hgen hretL hcard.ge).followWord
          u w = u
      exact L.allProperCompletedStage_disjoint_word_fixes
        hadm hgen hretL hcard.ge C hdis w hw u
    rw [← hu]
    calc
      Tamb.followWord (f.onVertex u) w =
          f.onVertex (Tloc.followWord u w) :=
        CompleteEGraph.hom_followWord Tloc Tamb f u w
      _ = f.onVertex u := by rw [hLocal]

/-- Exact FULL k=1 FIXED-VERTEX theorem for ACTUAL original-source
rank-two type-(2) singleton B-augmentation. For every C of at
most ONE unsigned letter and every ambient identity-valued
signed C-word, the completed stage fixes ALL its vertices.

Includes original quotient points, the glued attachment root,
and all newly tagged full B-coset points. -/
theorem rootedSourceOffCosetCompletedStage_rankOne_word_fixes
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
          A hcard hret root (allProperCosetFamily A) z)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
    (v : IsolatedCosetGluing.Vertex
      (Quotient (K.rootedAmbientMultiCosetSetoid
        A hcard hret root (allProperCosetFamily A)))
      gen B
      (K.rootedAmbientMultiCosetValue A hcard hret root
        (allProperCosetFamily A)
        (K.rootedLocalMultiCosetVertexQuotientEquiv
          A hcard hret root (allProperCosetFamily A) z))) :
    (K.rootedSourceOffCosetCompletedStage
      A hcard hret root B hBP z hOffSource).followWord v w = v := by
  classical
  let P := allProperCosetFamily A
  let G := K.rootedAmbientMultiCosetCompletedEGraph A hcard hret root P
  let g : Γ := K.rootedAmbientMultiCosetValue
    A hcard hret root P
    (K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root P z)
  let oldRoot := K.rootedLocalMultiCosetVertexQuotientEquiv
    A hcard hret root P z
  have hMissing :
      ∀ e : K.rootedAmbientAllProperRawEdgeQuotient A hcard hret root,
        G.source e = oldRoot → signedBase (G.label e) ∉ B := by
    intro e he
    exact K.rootedAmbientOffCoset_no_old_B_edge
      A hcard hret root B hBP z hOffSource e he
  have hpaired : G.LocallyPairedLabels :=
    K.rootedAmbientAllProperMultiCoset_locallyPairedLabels
      A hcard hret root
  have hOldKernel :
      ∀ x : Quotient (K.rootedAmbientMultiCosetSetoid
        A hcard hret root P),
        (G.trivialLoopCompletion hpaired).followWord x w = x := by
    intro x
    exact K.rootedAmbientAllProperCompletedStage_rankOne_word_fixes
      A hcard hret root C hCcard w hw hval x
  by_cases hdis : Disjoint C B
  · exact IsolatedCosetGluing.completedStage_disjoint_C_word_kernel
      G gen B g oldRoot hMissing hpaired
      C hdis w hw hOldKernel v
  · have hCA : C ⊂ A := by
      rcases small_alphabet_proper_or_disjoint_rank_two
          A C hcard hCcard with hp | hd
      · exact hp
      · have hBA : B ⊆ A :=
          ((mem_allProperCosetFamily A B).mp hBP).subset
        have hdCB : Disjoint C B := by
          apply Finset.disjoint_left.mpr
          intro i hiC hiB
          exact (Finset.disjoint_left.mp hd) hiC (hBA hiB)
        exact (hdis hdCB).elim
    have hmeet : ∃ i : ι, i ∈ C ∧ i ∈ B := by
      by_contra hnone
      apply hdis
      apply Finset.disjoint_left.mpr
      intro i hiC hiB
      exact hnone ⟨i, hiC, hiB⟩
    obtain ⟨i, hiC, hiB⟩ := hmeet
    have hCB : C = B :=
      proper_alphabets_shared_letter_eq_rank_two
        A C B hcard.le
        hCA ((mem_allProperCosetFamily A B).mp hBP)
        i hiC hiB
    subst C
    exact K.rootedSourceOffCosetCompletedStage_identity_B_word_fixes
      A hcard hret root B hBP z hOffSource w hw hval v

/-- The complete actual source type-(2) augmented stage's
TRANSITION GROUP word value is trivial on ALL ambient
identity-valued signed C-words with |C|≤1.
This is the precise corrected rank-one PER-STAGE word-kernel
statement, not just the attached B case. -/
theorem rootedSourceOffCosetCompletedStage_rankOne_wordValue_eq_one
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
          A hcard hret root (allProperCosetFamily A) z)
    (C : Finset ι) (hCcard : C.card ≤ 1)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1) :
    (K.rootedSourceOffCosetCompletedStage
      A hcard hret root B hBP z hOffSource).wordValue w = 1 := by
  apply ((K.rootedSourceOffCosetCompletedStage
    A hcard hret root B hBP z hOffSource).wordValue_eq_one_iff_all_vertices_fixed w).mpr
  intro v
  exact K.rootedSourceOffCosetCompletedStage_rankOne_word_fixes
    A hcard hret root B hBP z hOffSource
    C hCcard w hw hval v

end CayleySubgraphSpec
end ABO
end PSTSEPPA
