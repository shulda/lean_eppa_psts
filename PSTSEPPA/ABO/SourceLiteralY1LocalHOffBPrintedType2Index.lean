import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalRootedEmbeddingInputs
import PSTSEPPA.ABO.SourceLiteralY1PrintedRootPAEqualsNormalizedAmbient
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootType2SignedAugmentationIso
import PSTSEPPA.ABO.RootedSourceOffCosetIndexEquiv
import PSTSEPPA.ABO.RootedSourceAllProperCompletedStageIso

/-!
# True original T(Y₁) type-(2) off-B index from normalized H[A]

The corrected rank-one source uses genuine ORIGINAL
T(Y₁)-rooted A-component P_A multiCE quotient vertices as
type-(2) augmentation indices. The locally generated group
H[A] and original ambient-root H-component have separately
tagged coset vertices.

The independently certified rooted local→ambient signed
complete-stage isomorphism agrees on the full old+fresh
P_A vertex quotient with the exact quotient equivalence.
The certified rooted source off-B transport says the
original B-constituent contains a point exactly when its
local preimage lies in the local B-constituent.

Thus any ACTUAL local H[A] P_A vertex off B becomes a
literal original printed old H type-(2) augmentation
index, with the exact old component-tagged vertex, not
just its H ambient group value.

This prepares the concrete original type-(2) based finite
T(X₂^all) Cayley cover. It does NOT by itself prove the
group coordinate of its G[A] source root is compatible
with the cover, correct 4.7(iii), R8 or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- From one TRUE normalized local H[A] off-B tagged
quotient vertex, construct the real original printed
selected type-(2) index based at the precisely translated
OLD multiCE quotient vertex. -/
noncomputable def sourceLiteralY1SelectedLocalHOffB_toPrintedType2
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : (sourceLiteralY1SelectedLocalHOldSkeleton
      src dst base A root).MultiCosetVertex
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalHOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1Local_isGenerated src dst A)
        (sourceLiteralY1Local_retractable src dst A hcard.le))
    (hOff : ¬ ∃ p : (sourceLiteralY1SelectedLocalHOldSkeleton
      src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalHOldSkeleton
        src dst base A root).multiCosetInclude
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalHOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1Local_isGenerated src dst A)
        (sourceLiteralY1Local_retractable src dst A hcard.le)
        B hBP p = z) :
    LiteralPaperSelectedOffBPoint src dst base A hcard root B hBP := by
  let K := (sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let hret := sourceLiteralY1_transitionTwoRetractable src dst
  let P := allProperCosetFamily A
  let T := K.rootedAllProperCompletedStageHom A hcard hret r
  refine ⟨T.onVertex z, ?_⟩
  have h :=
    (K.rootedLocalMultiCosetOffCoset_iff
      A hcard hret r P B hBP z).mp hOff
  change ¬ ∃ q : (K.subalphabetComponentSubgraph A r).AttachedCosetVertex B,
    K.rootedAmbientMultiCosetInclude A hcard hret r P B hBP q =
      (K.rootedLocalMultiCosetVertexQuotientEquiv A hcard hret r P) z at h
  change ¬ ∃ q : (sourceLiteralY1DirectRootComponent
        src dst base A root).AttachedCosetVertex B,
    sourceLiteralY1SelectedRootBInclude
      src dst base A hcard root P B hBP q =
      T.onVertex z
  exact h

end ABO
end PSTSEPPA
