import PSTSEPPA.ABO.Type2G2CatalogueActionOccurrence
import PSTSEPPA.ABO.SourceH1Type2StageCatalogueIndex

/-!
# Locate EVERY actual source H₁ type-(2) augmentation in the real finite G₂ catalogue

The source construction indexes genuine H₁-cover stages by the original
input basepoint, the two-letter parent A and an actual H₁ preimage
root, then by the selected B⊂A and its TRUE component-tagged
off-B vertex z. The finite G₂ catalogue, by contrast, uses an
outer pair (A,K) consisting of the normalized local Cayley skeleton
and then its literal local type-(2) augmented-stage index (B,z).

The source/local *fibrewise* equivalence is already formalized and
integrated, and the local type-(2) complete-action carrier has
its precise tagged occurrence inside G₂. Here we explicitly compose
the source-cover normalization with the source-to-local B,z
equivalence to produce a concrete ACTUAL G₂ (A,K,B,z) index
for every genuine original H₁ type-(2) augmentation.

No component or coset representatives are chosen, no artificial
old edges are created, and tagged vertices with coinciding group
coordinates remain distinct.

IMPORTANT: the locator is NOT claimed injective in the original
(base,A,root) source tag: two different source-cover indices could
yield the same normalized local skeleton. This is harmless for the
desired G₂ COVER property, which needs each source stage to have
a correct indexed action occurrence, NOT a bijection of the
entire source family onto the global catalogue.

The per-index completed-stage ACTION correspondence is addressed
separately by the rooted source/local signed action-isomorphism and
exact local model API. Full Z₁ type-(1), corrected Condition 5.2,
higher ranks and PSTS EPPA remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The dependent index universe of ACTUAL finite-source-G₂
local type-(2) augmented stages: the literal outer
(A,K) local skeleton tag and a true inner (B,z) index
of its fully signed augmented-action family. -/
abbrev actualSourceG2Type2CatalogueIndex (src dst : ι → V) :=
  Σ j : AllLocalRankTwoSkeletonIndex (sourceH1Generator src dst),
    localType2CatalogueIndex
      (sourceH1Generator src dst)
      (sourceH1_twoRetractable src dst) j

/-- Send EVERY genuine original H₁ type-(2) stage selection
to the literal index in the finite all-local G₂ catalogue.
The outer skeleton is precisely the normalized connected
component of the ORIGINAL incomplete source H₁ cover,
and the inner B,z is the exact proper-coset augmentation choice. -/
noncomputable def sourceOriginalH1Type2IntoActualG2Catalogue
    (src dst : ι → V)
    (j : sourceOriginalH1Type2AugmentationIndex src dst) :
    actualSourceG2Type2CatalogueIndex src dst :=
  ⟨sourceCoverIntoAllLocalIndex src dst j.1,
    (sourceOriginalH1Type2CatalogueIndexEquiv src dst j).2⟩

/-- This stage locator retains the LITERAL normalized source
component's (A,K) index, not an arbitrary isomorphic skeleton
or arbitrary root-coordinate quotient. -/
@[simp] theorem sourceOriginalH1Type2IntoActualG2Catalogue_outer
    (src dst : ι → V)
    (j : sourceOriginalH1Type2AugmentationIndex src dst) :
    (sourceOriginalH1Type2IntoActualG2Catalogue src dst j).1 =
      sourceCoverIntoAllLocalIndex src dst j.1 :=
  rfl

/-- It also preserves the exact selected B-subalphabet tag
inside the local type-(2) stage, including the empty B case. -/
@[simp] theorem sourceOriginalH1Type2IntoActualG2Catalogue_alphabet
    (src dst : ι → V)
    (j : sourceOriginalH1Type2AugmentationIndex src dst) :
    (sourceOriginalH1Type2IntoActualG2Catalogue src dst j).2.1 =
      j.2.1 := by
  change (sourceOriginalH1Type2CatalogueIndexEquiv src dst j).2.1 =
    j.2.1
  exact sourceOriginalH1Type2CatalogueIndexEquiv_alphabet src dst j

end ABO
end PSTSEPPA
