import PSTSEPPA.ABO.SourceH1OriginalSelectedOffBLocalG2IndexValue

/-!
# Exact original SourceH₁ type-(2) selected OLD root from its local G₂ index

The genuine original SourceH₁ off-B coset-augmentation index is not
a group coordinate: its old root z is a vertex of the intersection-
supported quotient of component-tagged attached B-coset points.
The certified local Γ[A] type-(2) G₂ catalogue index has an old
root w in the independently constructed LOCAL quotient.

The previously verified selected source/local index equivalence
is constructed from the actual bijection of these vertex quotients.
Here we record the precise dependent point-level equation
  e(w) = z
where e is the true LOCAL→ORIGINAL vertex equivalence,
not an equality of ambient group values or an arbitrary choice
of coset representative. The theorem includes B=∅, all old
signed path-component tags, and the actual off-B condition.

Together with the separately certified exact group-anchor formula
sourceValue(z) = r·localValue(w), this supplies BOTH equalities
needed to identify dependent carriers of complete B-augmented
original and root-translated signed stages.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The old ORIGINAL source-H₁ selected off-B glued quotient root
is LITERALLY the image of its actual LOCAL H₁[A] G₂ catalogue
type-(2) index's old vertex, preserving all component tags. -/
theorem sourceH1OriginalSelectedOffBLocalG2Index_root_exact
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : SourceH1 src dst)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : Quotient (sourceH1OriginalRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A)))
    (hOff : ¬ ∃ p : (sourceH1OriginalRootComponent
      src dst base A root).AttachedCosetVertex B,
      sourceH1SelectedRootBInclude
        src dst base A hcard root (allProperCosetFamily A)
        B hBP p = z) :
    ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).rootedLocalMultiCosetVertexQuotientEquiv
        A hcard (sourceH1_twoRetractable src dst)
        (⟨root, by trivial⟩ :
          ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).Vertex)
        (allProperCosetFamily A)
      (sourceH1OriginalSelectedOffBLocalG2Index
        src dst base A hcard root B hBP z hOff).2.1 = z := by
  let K := (sourceH1OriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  let e := K.rootedLocalMultiCosetVertexQuotientEquiv
    A hcard (sourceH1_twoRetractable src dst) r (allProperCosetFamily A)
  have hLocal :
      (sourceH1OriginalSelectedOffBLocalG2Index
        src dst base A hcard root B hBP z hOff).2.1 = e.symm z := by
    rfl
  change e (sourceH1OriginalSelectedOffBLocalG2Index
    src dst base A hcard root B hBP z hOff).2.1 = z
  rw [hLocal]
  exact e.apply_symm_apply z

end ABO
end PSTSEPPA
