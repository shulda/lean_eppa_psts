import PSTSEPPA.ABO.SourceLiteralY1SelectedRootRawGraphIso

/-!
# Exact off-B type-(2) augmentation indices in the genuine paper/source roots

Corrected ABO Definition 5.3 augments the completed proper-family
multi-coset graph at an OLD vertex outside the image of a selected
component-tagged attached B-coset. Being "off B" means exclusion
from the *entire B-CONSTITUENT of the genuine tagged glued quotient*,
not non-membership in its ambient group B-coset.

The certified original paper T(Y₁) / SourceH₁ root-isomorphism
preserves and reflects the exact B-constituent inclusions. Here
we make their actual maps explicit and prove, for every family
P of proper A-subalphabets, that the selected PAPER quotient
vertex is eligible as an off-B index if and only if its exact
SOURCE-H₁ counterpart is eligible. The proof uses the full
component-tagged B-coset equivalence and the bijection of
intersection-supported vertex quotients, and NEVER identifies
different old tagged vertices merely because their group
coordinates happen to agree.

This is the precise selected-root indexing prerequisite for
transporting the source rank-two H₁[A] theorem excluding
all outgoing old B-signed edges and legally attaching one
new full B-left coset.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Include the *genuine tagged* B-constituent into the
selected printed original rank-two proper-family quotient.
No ambient-group-coordinate injectivity is asserted. -/
noncomputable def sourceLiteralY1SelectedRootBInclude
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : (sourceLiteralY1DirectRootComponent src dst base A root).AttachedCosetVertex B) :
    Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root P) :=
  Quotient.mk (sourceLiteralY1DirectRootMultiCosetSetoid
    src dst base A hcard root P)
    (⟨⟨B,hBP⟩,p⟩ :
      (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawVertex P)

/-- The corresponding inclusion of the actual SOURCE-H₁
B-constituent into its exact original-root vertex quotient. -/
noncomputable def sourceH1SelectedRootBInclude
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (P : CosetFamilySpec A)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (q : (sourceH1OriginalRootComponent src dst base A root).AttachedCosetVertex B) :
    Quotient (sourceH1OriginalRootMultiCosetSetoid
      src dst base A hcard root P) :=
  Quotient.mk (sourceH1OriginalRootMultiCosetSetoid
    src dst base A hcard root P)
    (⟨⟨B,hBP⟩,q⟩ :
      (sourceH1OriginalRootComponent src dst base A root).MultiCosetRawVertex P)

/-- The true B-constituent inclusion commutes with the
paper→source quotient equivalence, preserving BOTH the
component path tag and its coset point coordinate. -/
theorem sourceLiteralY1SelectedRootBInclude_natural
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : (sourceLiteralY1DirectRootComponent src dst base A root).AttachedCosetVertex B) :
    sourceLiteralY1RootToH1MultiCosetVertexEquiv
      src dst base A hcard root P
        (sourceLiteralY1SelectedRootBInclude
          src dst base A hcard root P B hBP p) =
      sourceH1SelectedRootBInclude
        src dst base A hcard
          ((sourceH1EquivLiteralY1Transition src dst).symm root)
          P B hBP
          (sourceLiteralY1DirectRootTaggedBCosetEquiv
            src dst base A root B p) := by
  exact sourceLiteralY1RootToH1MultiCosetVertexEquiv_mk
    src dst base A hcard root P
    (⟨⟨B,hBP⟩,p⟩ :
      (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawVertex P)

/-- ACTUAL off-B augmentation eligibility is invariant under the
selected original paper T(Y₁) / SourceH₁ rooted signed-graph
equivalence. In particular, equal AMBIENT coordinates of distinct
component-tagged old vertices never create a false B-membership. -/
theorem sourceLiteralY1SelectedRootOffB_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (z : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root P)) :
    (¬ ∃ p : (sourceLiteralY1DirectRootComponent src dst base A root).AttachedCosetVertex B,
      sourceLiteralY1SelectedRootBInclude
        src dst base A hcard root P B hBP p = z) ↔
    (¬ ∃ q : (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).AttachedCosetVertex B,
      sourceH1SelectedRootBInclude src dst base A hcard
        ((sourceH1EquivLiteralY1Transition src dst).symm root)
        P B hBP q =
      sourceLiteralY1RootToH1MultiCosetVertexEquiv
        src dst base A hcard root P z) := by
  let F := sourceLiteralY1RootToH1MultiCosetVertexEquiv
    src dst base A hcard root P
  let eB := sourceLiteralY1DirectRootTaggedBCosetEquiv
    src dst base A root B
  constructor
  · intro hOff ⟨q,hq⟩
    let p := eB.symm q
    have hpmap :
        F (sourceLiteralY1SelectedRootBInclude
          src dst base A hcard root P B hBP p) =
        sourceH1SelectedRootBInclude src dst base A hcard
          ((sourceH1EquivLiteralY1Transition src dst).symm root)
          P B hBP q := by
      have h := sourceLiteralY1SelectedRootBInclude_natural
        src dst base A hcard root P B hBP p
      simpa [eB, p] using h
    have hPaper :
        sourceLiteralY1SelectedRootBInclude
          src dst base A hcard root P B hBP p = z :=
      F.injective (hpmap.trans hq)
    exact hOff ⟨p,hPaper⟩
  · intro hOff ⟨p,hp⟩
    apply hOff
    refine ⟨eB p, ?_⟩
    calc
      sourceH1SelectedRootBInclude src dst base A hcard
          ((sourceH1EquivLiteralY1Transition src dst).symm root)
          P B hBP (eB p) =
        F (sourceLiteralY1SelectedRootBInclude
          src dst base A hcard root P B hBP p) :=
          (sourceLiteralY1SelectedRootBInclude_natural
            src dst base A hcard root P B hBP p).symm
      _ = F z := congrArg F hp

end ABO
end PSTSEPPA
