import PSTSEPPA.ABO.SourceLiteralY1FirstRankRootedOffBOrbitIsolation
import PSTSEPPA.ABO.RootedFullBConstituentSaturation
import PSTSEPPA.ABO.LocalSubgroupCosetNaturality

/-!
# Unconditional corrected ABO FIRST-RANK ROOTED proper-B bridge reflection

This is the exact checked first-rank consequence of the
source's genuine old/fresh component geometry:

* For a TRUE original signed G=T(X₂^all)[A] P_A
  multiCE with A.card=2 and its actual local H=T(Y₁)[A]
  stable quotient, the entire attached region of ONE
  selected original old G[A] A-component is genuinely
  embedded in the full finite G Cayley group.
* Every such attached region is an ACTUAL signed A-
  connected component, closed under genuine signed edges.
* For each proper B⊊A, full B-constituent endpoints
  already have real B-paths by the full-B saturation theorem.
* For off-B endpoints, the source-specific actual
  based original type-(2) Cayley-G augmentation and
  old signed H-root mapping show the singleton external
  ambient G[B]-orbit contains no second point of the
  selected A-component. The genuine LOCAL G[A][B]
  coset relation is equivalent to the original global
  finite G[B] coset relation for B⊆A.

Therefore every ambient B-coset connection BETWEEN
points of this ONE actual selected original A-component
is realized by a real signed B-word path in the ORIGINAL
INCOMPLETE multiCE graph, including B=empty, both
formal inverse signs and original graph loops.

This is the first-rank component-scoped corrected ABO
Theorem 4.7(iii) bridge property, NOT the unrestricted
full-pullback/global paper theorem. The old G[A] pullback
may contain other disjoint A-components, and the separate
R8 full-B-coset cluster repair, higher k≥2 inductive
history/Condition 5.2, equivariant representative
selection and finite PSTS EPPA remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- No external proper B-orbit of a genuine off-B vertex
contains a different vertex of the chosen original-root
A-component. This is the precise source old/fresh
RootedProperOffBOrbitIsolated predicate, without any
additional cover, group-stability or bridge assumption. -/
theorem sourceLiteralY1SelectedLocal_rootedOffBOrbitIsolated
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).RootedProperOffBOrbitIsolated
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root) := by
  intro B hBA u v hu hv hOff hCoset
  let K := sourceLiteralY1SelectedLocalGOldPullback
    src dst base A root
  let P := allProperCosetFamily A
  let hAdm := sourceLiteralY1SelectedLocalGOld_admissible
    src dst base A hcard root
  let hGen := sourceLiteralY1X2AllLocal_isGenerated src dst A
  let hRet := sourceLiteralY1X2AllLocal_retractable
    src dst A hcard.le
  let S := sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom
    src dst base A hcard root
  have hBP : B ∈ P.alphabets :=
    (mem_allProperCosetFamily A B).mpr hBA
  have hGlobalCoset :
      S.onVertex v ∈
        generatedLeftCoset (sourceLiteralY1X2AllGenerator src dst)
          B (S.onVertex u) := by
    have h := (mem_localGeneratedLeftCoset_iff_ambient
      (sourceLiteralY1X2AllGenerator src dst)
      B A hBA.subset
      (K.multiCosetAmbientValue P hAdm hGen hRet u)
      (K.multiCosetAmbientValue P hAdm hGen hRet v)).mp hCoset
    change
      S.onVertex v ∈
        generatedLeftCoset
          (sourceLiteralY1X2AllGenerator src dst)
          B (S.onVertex u)
    exact h
  exact sourceLiteralY1SelectedLocal_rootedOffB_globalOrbit_isolated
    src dst base A hcard root B hBP u v hu hv hOff hGlobalCoset

/-- ACTUAL finite corrected ABO first-rank ROOTED
PROPER-B BRIDGE REFLECTION. For ALL proper B⊊A
(including the empty alphabet and both singleton B),
two genuinely old/fresh signed P_A quotient vertices
of the SAME selected original old A-component which
belong to the same ambient finite local G[A][B]-coset
are joined by a REAL signed B-word path in the
ORIGINAL, uncompleted G[A] P_A coset extension.

There is no arbitrary bridge-free premise, no new
axiom or sorry, and the entire disconnected old
pullback is explicitly NOT assumed to be one component.
-/
theorem sourceLiteralY1SelectedLocal_rootedProperBridgeReflection
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).RootedProperBridgeReflection
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root) :=
  (sourceLiteralY1SelectedLocal_rootedBridgeReflection_iff_offBOrbitIsolated
    src dst base A hcard root).mpr
      (sourceLiteralY1SelectedLocal_rootedOffBOrbitIsolated
        src dst base A hcard root)

end ABO
end PSTSEPPA
