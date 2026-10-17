import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalRootedEmbeddingInputs
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootNormalizedLocalHFullCayleyCover
import PSTSEPPA.ABO.RootedLocalCompletedPAOldVertexNaturality
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootPlainOldAnchorCover

/-!
# Exactly normalize the genuine printed OLD root in the local H[A] P_A stage

The full signed G[A]-to-local-H[A] Cayley cover exists, but corrected
ABO 4.7(ii) requires the group identity to map to the true OLD H[A]
component-tagged coset-extension vertex over the selected G[A]
original root, not merely a point with equal ambient H-coordinate.

We compare three genuine old root presentations: (1) the actual
original printed H=T(Y_1) old root in its incomplete rooted A
component, (2) the identity of the inverse-translated old H[A]
skeleton, and (3) the identity of the locally pulled-back old G[A]
skeleton. Previous certified naturality of fully tagged cosets
commutes with the actual completed local-to-printed signed stage
isomorphism for B=empty. Hence the inverse transport of the
printed OLD anchor is EXACTLY the local old root inclusion.

No unproved global H embedding, identification of disconnected
old components, outside-original signed edges, R8 or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The genuine original root is the image of the LOCAL H[A]
old skeleton identity by inverse left root-translation, including
its true old A-connected component tag. -/
theorem sourceLiteralY1SelectedLocalHOld_identity_to_originalRoot
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).intrinsicComponentLocalHom A
        (⟨root, by trivial⟩ :
          ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).Vertex)).onVertex
          (sourceLiteralY1SelectedLocalHOld_identity
            src dst base A root) =
      sourceLiteralY1SelectedRootOldPoint src dst base A root := by
  apply Subtype.ext
  change root *
    (((sourceLiteralY1SelectedLocalHOld_identity
      src dst base A root).1 :
        generatedSubgroup
          (sourceLiteralY1 src dst).transitionSubgroupGenerator A) :
      (sourceLiteralY1 src dst).transitionGroup) = root
  rw [sourceLiteralY1SelectedLocalHOld_identity_val]
  simp

/-- The LITERAL exact H[A]-local completed-stage OLD anchor.
It is the tagged B=empty original skeleton point, never
an ambient-group-coordinate quotient. -/
noncomputable def sourceLiteralY1SelectedLocalHOld_anchor
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalHCompleteStage
      src dst base A hcard root).Vertex := by
  let H := sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root
  have hn : A.Nonempty := Finset.card_pos.mp (by rw [hcard]; decide)
  let hEmpty : (∅ : Finset ι) ∈ (allProperCosetFamily A).alphabets :=
    empty_mem_allProperCosetFamily A hn
  exact (H.skeletonToMultiCosetHom
    (allProperCosetFamily A)
    (sourceLiteralY1SelectedLocalHOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1Local_isGenerated src dst A)
    (sourceLiteralY1Local_retractable src dst A hcard.le)
    ∅ hEmpty).onVertex
      (sourceLiteralY1SelectedLocalHOld_identity
        src dst base A root)

/-- The exact source-normalizing FULL signed P_A graph
isomorphism sends the normalized OLD tagged H[A] identity
to precisely the previously chosen printed OLD H root tag.
The theorem compares VERTICES IN THE GENUINE QUOTIENT. -/
theorem sourceLiteralY1SelectedLocalHOld_anchor_to_paper
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).rootedAllProperCompletedStageHom A hcard
        (sourceLiteralY1_transitionTwoRetractable src dst)
        (⟨root, by trivial⟩ :
          ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).Vertex)).onVertex
        (sourceLiteralY1SelectedLocalHOld_anchor
          src dst base A hcard root) =
      sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root := by
  let K := (sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceLiteralY1_transitionTwoRetractable src dst
  let x := sourceLiteralY1SelectedLocalHOld_identity src dst base A root
  have hn : A.Nonempty := Finset.card_pos.mp (by rw [hcard]; decide)
  let hEmpty : (∅ : Finset ι) ∈ (allProperCosetFamily A).alphabets :=
    empty_mem_allProperCosetFamily A hn
  have hroot : (K.intrinsicComponentLocalHom A r).onVertex x =
      sourceLiteralY1SelectedRootOldPoint src dst base A root :=
    sourceLiteralY1SelectedLocalHOld_identity_to_originalRoot
      src dst base A root
  have h := K.rootedAllProperCompletedStageHom_oldVertex
    A hcard hret r ∅ hEmpty x
  rw [hroot] at h
  change (K.rootedAllProperCompletedStageHom A hcard hret r).onVertex
    (sourceLiteralY1SelectedLocalHOld_anchor
      src dst base A hcard root) =
    sourceLiteralY1SelectedRootPlainOldAnchor
      src dst base A hcard root at h
  exact h

/-- Consequently the INVERSE of the true labelled completed-stage
isomorphism takes the literal printed OLD H anchor precisely to
the genuine normalized old H[A] skeleton identity inclusion. -/
theorem sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom_oldAnchor
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
      src dst base A hcard root).onVertex
      (sourceLiteralY1SelectedRootPlainOldAnchor
        src dst base A hcard root) =
    sourceLiteralY1SelectedLocalHOld_anchor
      src dst base A hcard root := by
  let K := (sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceLiteralY1_transitionTwoRetractable src dst
  let f := K.rootedAllProperCompletedStageHom A hcard hret r
  have hb := K.rootedAllProperCompletedStageHom_bijective A hcard hret r
  have h := f.inverseOfBijective_onVertex_apply
    hb.1 hb.2
    (sourceLiteralY1SelectedLocalHOld_anchor
      src dst base A hcard root)
  change (sourceLiteralY1SelectedRootPlainToNormalizedHLocalHom
    src dst base A hcard root).onVertex
      (f.onVertex (sourceLiteralY1SelectedLocalHOld_anchor
        src dst base A hcard root)) =
    sourceLiteralY1SelectedLocalHOld_anchor
      src dst base A hcard root at h
  rw [sourceLiteralY1SelectedLocalHOld_anchor_to_paper
    src dst base A hcard root] at h
  exact h

/-- The local OLD H[A] tagged root is precisely the image of
the genuine G[A]-pullback OLD identity under the original
H[A] signed skeleton→P_A stage inclusion. This equality
uses the genuine labelled quotient Q_A(1)=1, NOT
a claim about the whole disconnected old pullback. -/
theorem sourceLiteralY1SelectedLocalHOld_anchor_eq_pullbackRoot
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    sourceLiteralY1SelectedLocalHOld_anchor
      src dst base A hcard root =
    ((sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root).pullbackOldToWeakMultiCosetStageHom
        (sourceLiteralY1X2AllLocalQuotient src dst A)
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalHOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1Local_isGenerated src dst A)
        (sourceLiteralY1Local_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalHOld_weakComplete
          src dst base A hcard root)
        ∅
        (empty_mem_allProperCosetFamily A
          (Finset.card_pos.mp (by rw [hcard]; decide)))).onVertex
      (sourceLiteralY1SelectedLocalGOld_identity
        src dst base A root) := by
  let H := sourceLiteralY1SelectedLocalHOldSkeleton src dst base A root
  let Q := sourceLiteralY1X2AllLocalQuotient src dst A
  let P := allProperCosetFamily A
  let hadm := sourceLiteralY1SelectedLocalHOld_admissible
    src dst base A hcard root
  let hgen := sourceLiteralY1Local_isGenerated src dst A
  let hret := sourceLiteralY1Local_retractable src dst A hcard.le
  let hweak := sourceLiteralY1SelectedLocalHOld_weakComplete
    src dst base A hcard root
  have hn : A.Nonempty := Finset.card_pos.mp (by rw [hcard]; decide)
  let hEmpty : (∅ : Finset ι) ∈ P.alphabets :=
    empty_mem_allProperCosetFamily A hn
  let gRoot := sourceLiteralY1SelectedLocalGOld_identity
    src dst base A root
  let hRoot := sourceLiteralY1SelectedLocalHOld_identity
    src dst base A root
  have hProjection : (H.pullbackQuotientHom Q).onVertex gRoot = hRoot := by
    apply Subtype.ext
    change Q.hom (1 : generatedSubgroup
      (sourceLiteralY1X2AllGenerator src dst) A) =
        (1 : generatedSubgroup
          (sourceLiteralY1 src dst).transitionSubgroupGenerator A)
    exact map_one Q.hom
  calc
    sourceLiteralY1SelectedLocalHOld_anchor
        src dst base A hcard root =
      H.multiCosetInclude P hadm hgen hret ∅ hEmpty
        (H.attachedOfSkeletonVertex ∅ hRoot) := rfl
    _ = H.multiCosetInclude P hadm hgen hret ∅ hEmpty
        (H.attachedOfSkeletonVertex ∅
          ((H.pullbackQuotientHom Q).onVertex gRoot)) :=
      congrArg (fun x : H.Vertex =>
        H.multiCosetInclude P hadm hgen hret ∅ hEmpty
          (H.attachedOfSkeletonVertex ∅ x)) hProjection.symm
    _ = (H.pullbackOldToWeakMultiCosetStageHom
        Q P hadm hgen hret hweak ∅ hEmpty).onVertex gRoot :=
      (H.pullbackOldToWeakMultiCosetStageHom_vertex
        Q P hadm hgen hret hweak ∅ hEmpty gRoot).symm

end ABO
end PSTSEPPA
