import PSTSEPPA.ABO.SourceLiteralY1SelectedRootType2SignedAugmentationIso
import PSTSEPPA.ABO.FiniteRankTwoType2Stages
import PSTSEPPA.ABO.SourceLiteralY1OriginalCoverIndexEquiv
import Mathlib.Data.Fintype.Quotient
import Mathlib.Basic.Finite.Sigma

/-!
# Finiteness of genuine selected PAPER off-B component-tagged roots

At the first corrected Section-5 rank, a type-(2) stage is
indexed by an OLD point of the ACTUAL intersection-support
quotient of independently tagged full B-coset copies. Its
off-B predicate excludes the WHOLE selected tagged B-summand.

We prove those eligible points form a finite type from the
genuine finite printed transition group T(Y₁). The proof is
not an assumption of ambient-coordinate injectivity. Instead:
* real signed-path B-component indices are finite quotients
  of the finite original Cayley skeleton;
* each attached coset with its B-component tag is finite;
* the disjoint union of tagged copies over P_A is finite;
* the precise ABO (B∩C)-gluing quotient is finite, and
* the selected off-B old points inject into that quotient.

The result holds even when distinct original tagged points
share the SAME ambient group coordinate, and for B=∅.
It is a prerequisite for the full selected type-(2) and
three-kind first-rank Z₁ action index finiteness. No
reflecting group, later-rank induction or PSTS EPPA claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The true signed-path-component-tagged raw disjoint union
over all proper B⊊A has finitely many vertices in every
printed original rank-two A-root, independently of whether
two of its points share the same group coordinate. -/
theorem finite_literalPaperSelectedRoot_rawVertices
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup) :
    Finite ((sourceLiteralY1DirectRootComponent
      src dst base A root).MultiCosetRawVertex
        (allProperCosetFamily A)) := by
  classical
  letI : Finite (sourceLiteralY1 src dst).transitionGroup :=
    finite_sourceLiteralY1TransitionGroup src dst
  let K := sourceLiteralY1DirectRootComponent src dst base A root
  let P := allProperCosetFamily A
  change Finite (Σ b : {B : Finset ι // B ∈ P.alphabets},
    K.AttachedCosetVertex b.1)
  exact @Finite.instSigma _ _
    (inferInstance : Finite {B : Finset ι // B ∈ P.alphabets})
    (fun b => K.finite_attachedCosetVertex b.1)

/-- Finiteness of the EXACT printed (B∩C)-glued OLD
multi-coset quotient, with its true component tags, not
a coarser quotient by equal ambient group coordinates. -/
theorem finite_literalPaperSelectedRoot_quotientVertices
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Finite (Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A))) := by
  classical
  let P := allProperCosetFamily A
  let K := sourceLiteralY1DirectRootComponent src dst base A root
  letI : Finite (K.MultiCosetRawVertex P) :=
    finite_literalPaperSelectedRoot_rawVertices src dst base A root
  apply Finite.of_surjective
    (fun p : K.MultiCosetRawVertex P =>
      (Quotient.mk
        (sourceLiteralY1DirectRootMultiCosetSetoid
          src dst base A hcard root P) p :
        Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
          src dst base A hcard root P)))
  intro q
  induction q using Quotient.inductionOn with
  | h p => exact ⟨p, rfl⟩

/-- Genuine original paper type-(2) OFF-B roots are finite
for EVERY actual root and selected B, without forgetting
their component-tags or replacing the quotient by Γ values. -/
theorem finite_LiteralPaperSelectedOffBPoint
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets) :
    Finite (LiteralPaperSelectedOffBPoint
      src dst base A hcard root B hBP) := by
  classical
  letI : Finite (Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A))) :=
    finite_literalPaperSelectedRoot_quotientVertices
      src dst base A hcard root
  apply Finite.of_injective
    (fun p : LiteralPaperSelectedOffBPoint
      src dst base A hcard root B hBP => p.vertex)
  intro p q hp
  cases p with
  | mk vp hvp =>
    cases q with
    | mk vq hvq =>
      cases hp
      rfl

end ABO
end PSTSEPPA
