import PSTSEPPA.ABO.SourceOriginalH1PreimageSkeleton
import PSTSEPPA.ABO.AmbientSkeletonAlphabetRestriction
import PSTSEPPA.ABO.RootedSourceMultiCosetCompletedEGraphIso

/-!
# Actual source H₁ original-input rank-two root multi-coset target congruence

The original source H₁ covering is a genuinely INCOMPLETE signed
Cayley preimage of the original input graph, not the artificial
complete X₁ action. Its ambient labelled source group is finite
and 2-retractable, but NOT assumed globally retractable.

For any real source root and any true two-letter alphabet A,
the selected old A-component inherits an exact tagged B∩C
vertex gluing Setoid from the local H₁[A] presentation.
The generic rooted local/source signed EGraph isomorphism
constructs its RAW oriented edge graph and proves exactly the
source-and-SIGNED-label-to-target congruence needed for quotienting
raw edges. This is a concrete no-new-assumption selected-source
application, not a hypothetical global H₁ coset completion.

The result is a prerequisite for transporting the deterministic
source-H₁ selected root multi-coset EGraph to literal paper T(Y₁)
rooted components. It does not claim full printed Z₁ augmentation,
higher rank geometry, Condition 5.2 or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The TRUE original source-H₁ rank-two selected-root RAW
multi-coset signed graph: glued vertices remember intrinsic
component tags, while oriented signed edge tokens remain raw. -/
noncomputable abbrev sourceH1OriginalRankTwoRootRawGraph
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (P : CosetFamilySpec A) :=
  ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A)
    .rootedAmbientMultiCosetRawGraph A hcard
      (sourceH1_twoRetractable src dst)
      (⟨root, by trivial⟩ :
        ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).Vertex) P

/-- For EVERY proper-alphabet family, the ACTUAL source-H₁
selected A-root raw graph satisfies source-and-full-signed-label
target congruence. Hence no two raw edge tokens with the same
glued source and signed label have different target vertices. -/
theorem sourceH1OriginalRankTwoRootRawGraph_target_congruent
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (P : CosetFamilySpec A) :
    (sourceH1OriginalRankTwoRootRawGraph
      src dst base A hcard root P).SourceLabelTargetCongruent := by
  exact
    ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A)
      .rootedAmbientMultiCosetRawGraph_target_congruent
        A hcard (sourceH1_twoRetractable src dst)
        (⟨root, by trivial⟩ :
          ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).Vertex)
        P

/-- The selected original source-H₁ A-root has a TRUE
deterministic signed EGraph obtained by quotienting actual raw
directed tokens by their glued source and complete signed label. -/
noncomputable abbrev sourceH1OriginalRankTwoRootCompletedEGraph
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (P : CosetFamilySpec A) :=
  sourceLabelGraphQuotientEGraph
    (sourceH1OriginalRankTwoRootRawGraph src dst base A hcard root P)
    (sourceH1OriginalRankTwoRootRawGraph_target_congruent
      src dst base A hcard root P)

end ABO
end PSTSEPPA
