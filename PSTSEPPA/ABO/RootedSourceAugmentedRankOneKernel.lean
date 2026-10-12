import PSTSEPPA.ABO.RootedSourceOffCosetAugmentedStage
import PSTSEPPA.ABO.RankTwoCompletedWordKernel
import PSTSEPPA.ABO.IsolatedCosetGlobalWordKernel

/-!
# Exact rank-one word kernel for genuine original-source rank-two B-augmentations

The source H1 first-rank group is only 2-retractable, and the
source corrected Definition 5.3 type-(2) stage is an actual
signed full-coset augmentation of an INCOMPLETE original graph
cover, not just a local Γ[A] model.

An identity-valued signed B-word w supported on B⊂A must act
trivially on ALL completed old vertices before augmentation.
We prove this by transporting the ALREADY CERTIFIED local rank-two
completed-word kernel through the actual signed complete-action
isomorphism of source/local full proper-coset stages (#396).

A generic verified isolated-B-coset theorem then shows that
attaching the genuine NEW full ambient B-coset at a source
off-B root preserves this exact B-word kernel at EVERY vertex,
including the old root, all fresh points and every old off-root
vertex. This is a genuine SOURCE type-(2) stage result; it
does not presuppose a source/local AUGMENTED graph isomorphism.

It does not yet establish inclusion of all source Z1 stages
in the concrete finite G2 local three-family catalogue,
Condition 5.2, arbitrary-rank Y_k/Z_k or unconditional PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- EVERY old original-source full-proper-coset completed
vertex is fixed by any signed B-word which is trivial in Γ.

This is derived from the LOCAL Γ[A] word-kernel theorem
and the actual source/local COMPLETE action isomorphism.
No global retractability of Γ, nor injectivity of the
source ambient-coordinate projection, is assumed. -/
theorem rootedAmbientAllProperCompletedStage_identity_B_word_fixes
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2)
    (root : K.Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (w : LabelWord ι) (hw : LabelWord.Uses B w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
    (x : Quotient (K.rootedAmbientMultiCosetSetoid
      A hcard hret root (allProperCosetFamily A))) :
    (K.rootedAmbientAllProperCompletedStage
      A hcard hret root).followWord x w = x := by
  let L := K.intrinsicComponentLocalSlice A root
  let hgen : IsGenerated (trivialCompletionGenerator gen A) :=
    isGenerated_trivialCompletionGenerator gen A
  let hretL : Retractable (trivialCompletionGenerator gen A) :=
    retractable_trivialCompletionGenerator_of_kRetractable
      gen 2 hret A hcard.le
  let hadm : L.AdmissibleForCosetExtension :=
    L.admissible_of_card_le_two hcard.le
  let Tloc := K.rootedLocalAllProperCompletedStage A hcard hret root
  let Tamb := K.rootedAmbientAllProperCompletedStage A hcard hret root
  let f := K.rootedAllProperCompletedStageHom A hcard hret root
  have hBsubset : B ⊆ A :=
    ((allProperCosetFamily A).proper B hBP).subset
  have hwA : LabelWord.Uses A w := hw.mono hBsubset
  have hvalCoe :
      ((PSTS.SignedWord.evalGroup
        (trivialCompletionGenerator gen A) w :
        generatedSubgroup gen A) : Γ) =
      PSTS.SignedWord.evalGroup gen w := by
    rw [coe_evalGroup_trivialCompletionGenerator,
      LabelWord.restrictTo_eq_self_of_uses A w hwA]
  have hvalLocal :
      PSTS.SignedWord.evalGroup
        (trivialCompletionGenerator gen A) w = 1 := by
    apply Subtype.ext
    change
      ((PSTS.SignedWord.evalGroup
          (trivialCompletionGenerator gen A) w :
          generatedSubgroup gen A) : Γ) = (1 : Γ)
    rw [hvalCoe]
    exact hval
  obtain ⟨u, hu⟩ :=
    (K.rootedAllProperCompletedStageHom_bijective
      A hcard hret root).1.2 x
  have hLocal : Tloc.followWord u w = u := by
    change
      (L.allProperCompletedStage hadm hgen hretL hcard.ge).followWord u w = u
    exact L.rankTwo_completedStage_identity_B_word_fixes
      hcard hgen hretL B hBP w hw hvalLocal u
  rw [← hu]
  calc
    Tamb.followWord (f.onVertex u) w =
        f.onVertex (Tloc.followWord u w) :=
      CompleteEGraph.hom_followWord Tloc Tamb f u w
    _ = f.onVertex u := by rw [hLocal]

/-- Every vertex of the TRUE original-source corrected
rank-two singleton B-augmentation has rank-one identity
word kernel. The quantification includes ALL old tagged
points and ALL new ambient B-coset points: no hidden
isomorphism of augmented stages or arbitrary representative
is supplied.

This is a source-Z1 type-(2) candidate theorem for the
specific off-B singleton stage constructed from the actual
original graph component, under only rank-two retractability. -/
theorem rootedSourceOffCosetCompletedStage_identity_B_word_fixes
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
    (w : LabelWord ι) (hw : LabelWord.Uses B w)
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
  let P := allProperCosetFamily A
  let G := K.rootedAmbientMultiCosetCompletedEGraph A hcard hret root P
  let g := K.rootedAmbientMultiCosetValue A hcard hret root P
    (K.rootedLocalMultiCosetVertexQuotientEquiv
      A hcard hret root P z)
  let oldRoot := K.rootedLocalMultiCosetVertexQuotientEquiv
    A hcard hret root P z
  have hMissing :
      ∀ e : K.rootedAmbientAllProperRawEdgeQuotient
          A hcard hret root,
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
    exact K.rootedAmbientAllProperCompletedStage_identity_B_word_fixes
      A hcard hret root B hBP w hw hval x
  exact IsolatedCosetGluing.completedStage_B_identity_word_fixes_every_vertex
    G gen B g oldRoot hMissing hpaired
    w hw hval hOldKernel v

end CayleySubgraphSpec
end ABO
end PSTSEPPA
