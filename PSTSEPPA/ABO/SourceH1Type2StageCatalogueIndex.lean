import PSTSEPPA.ABO.RootedSourceType2CatalogueIndex
import PSTSEPPA.ABO.SourceOriginalH1LocalCoverIndex
import PSTSEPPA.ABO.SourceH1AllLocalG2
import PSTSEPPA.ABO.RankTwoType2IndexedFamily

/-!
# The exact original-H₁ type-(2) stage indices occur in the concrete finite G₂ catalogue

The input-dependent finite group G₂ built by the source construction
synchronizes the genuine three-family completed actions for EVERY
possible local rank-two Cayley skeleton K over H₁[A]. It is not enough
that a given source stage resembles a local graph: one must exhibit
its actual catalogue INDEX and retain all component tags.

An original H₁ source cover component is indexed by (original input
base vertex, two-letter alphabet A, actual H₁ preimage root). The
previously certified mapping sends this to an actual local pair (A,K)
of the finite catalogue used to construct G₂, and normalizes the
true connected source A-component without inventing missing edges.

The source-rooted type-(2) augmentation is indexed by (B,z):
B⊂A, and z is a literal tagged glued source quotient vertex
outside every point of the selected full B-coset constituent.
The preceding source/local equivalence and the explicit identification
with the existing local type-(2) index establish an equivalence on
ENTIRE dependent B,z fibres, without choosing representatives.

Here we assemble that fibrewise equivalence for EVERY genuine
source H₁ cover-component index, preserving its original outer
(base,A,root) tag and the selected B exactly. Thus the entire
original-source type-(2) augmentation INDEX FAMILY maps canonically
into the actual finite local three-family G₂ catalogue.

This concerns the exact indices. The per-index signed complete action
isomorphism and the global corrected source Z₁ catalogue (including
type-(1) augmented clusters) are separate geometric obligations.
Theorems about Condition 5.2, later ranks and PSTS EPPA are OPEN.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The complete EXACT dependent index of source original H₁
rank-two singleton type-(2) B-augmentations. Nothing is identified
merely by equal ambient H₁ coordinate: the old glued vertex is
still an actual component-tagged quotient. -/
abbrev sourceOriginalH1Type2AugmentationIndex
    (src dst : ι → V) :=
  Σ j : SourceOriginalH1CoverIndex src dst,
    ((sourceCoverIndexSkeleton src dst j).restrictAlphabet j.2.1.1).rootedAmbientOffCosetAugmentationIndex
      j.2.1.1 j.2.1.2
      (sourceH1_twoRetractable src dst)
      (sourceCoverIndexRoot src dst j)
      (allProperCosetFamily j.2.1.1)

/-- The genuine corresponding type-(2) summand of the ACTUAL
local Γ[A] three-family stage catalogue indexed by all original
H₁ source-cover components. Each local index is itself one of
the all-local (A,K) skeleton indices used by the finite G₂. -/
abbrev sourceOriginalH1LocalG2Type2Index
    (src dst : ι → V) :=
  Σ j : SourceOriginalH1CoverIndex src dst,
    (sourceCoverIndexLocalSkeleton src dst j).rankTwoType2SingletonIndex
      j.2.1.2
      (isGenerated_trivialCompletionGenerator
        (sourceH1Generator src dst) j.2.1.1)
      (retractable_trivialCompletionGenerator_of_kRetractable
        (sourceH1Generator src dst) 2
        (sourceH1_twoRetractable src dst)
        j.2.1.1 j.2.1.2.le)

/-- Source H₁ original-cover type-(2) B,z stages and
their corresponding ACTUAL local G₂ catalogue stage indices
are canonically equivalent, fibre by fibre, with no arbitrary
coset/skeleton representatives and no lost tagged vertices. -/
noncomputable def sourceOriginalH1Type2CatalogueIndexEquiv
    (src dst : ι → V) :
    sourceOriginalH1Type2AugmentationIndex src dst ≃
      sourceOriginalH1LocalG2Type2Index src dst :=
  Equiv.sigmaCongrRight (fun j =>
    ((sourceCoverIndexSkeleton src dst j).restrictAlphabet
      j.2.1.1).rootedSourceType2CatalogueIndexEquiv
        j.2.1.1 j.2.1.2
        (sourceH1_twoRetractable src dst)
        (sourceCoverIndexRoot src dst j))

/-- The original input base, two-letter alphabet and
original preimage root tag are retained EXACTLY. -/
@[simp] theorem sourceOriginalH1Type2CatalogueIndexEquiv_outer
    (src dst : ι → V)
    (j : sourceOriginalH1Type2AugmentationIndex src dst) :
    (sourceOriginalH1Type2CatalogueIndexEquiv src dst j).1 = j.1 :=
  rfl

/-- The literal selected proper B-summand tag is retained
in every source-to-local stage index. In particular B=∅
is not discarded and different B choices are never merged. -/
@[simp] theorem sourceOriginalH1Type2CatalogueIndexEquiv_alphabet
    (src dst : ι → V)
    (j : sourceOriginalH1Type2AugmentationIndex src dst) :
    (sourceOriginalH1Type2CatalogueIndexEquiv src dst j).2.1 =
      j.2.1 :=
  rfl

end ABO
end PSTSEPPA
