import PSTSEPPA.ABO.SourceLiteralY1EveryOldRootOffBOrbitIsolation
import PSTSEPPA.ABO.RootedFullBConstituentSaturation
import PSTSEPPA.ABO.LocalSubgroupCosetNaturality

/-!
# Actual first-rank rooted bridge reflection on EVERY original old signed A-component

The accepted original source G=T(X₂^all)→H=T(Y₁) has a
genuinely signed local G[A] Q-pullback which need not be
old A-connected. Each original old A-component nevertheless
has its OWN whole old+fresh tagged P_A extension region.

The certified source rank-two cover establishes ambient
G[A] vertex injection on EVERY individually selected such
A-component (#670), and the true original finite global
G type-(2) based signed cover excludes all external G[B]
orbits for off-B vertices of ANY one selected old A-
component (#675), using only REAL signed A-paths.

For every old root r of this potentially disconnected
G[A] old pullback, this file proves full relative
RootedProperOffBOrbitIsolated and consequently actual
RootedProperBridgeReflection on the WHOLE true old+fresh
A-connected region selected by r.

Unlike globally unqualified corrected ABO Theorem 4.7(iii)
it does NOT prove bridges between DISTINCT originally
disconnected old A-components, and does not conflate
them via ambient G-group coordinates. Other higher-rank
cluster, R8 global assembly, Condition 5.2, equivariant
Z_k selection and finite PSTS EPPA remain separate.
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
theorem sourceLiteralY1SelectedLocal_everyOldRootOffBOrbitIsolated
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).RootedProperOffBOrbitIsolated
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        r := by
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
  exact sourceLiteralY1SelectedLocal_everyOldRootOffB_globalOrbit_isolated
    src dst base A hcard root r B hBP u v hu hv hOff hGlobalCoset

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
theorem sourceLiteralY1SelectedLocal_everyOldRootProperBridgeReflection
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (r : (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).Vertex) :
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).RootedProperBridgeReflection
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        r :=
by
  let K := sourceLiteralY1SelectedLocalGOldPullback src dst base A root
  exact (K.rootedProperBridgeReflection_iff_offBOrbitIsolated
    (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root)
    (sourceLiteralY1X2AllLocal_isGenerated src dst A)
    (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
    hcard.le r
    (sourceLiteralY1SelectedLocal_everyOldRoot_rootedMultiCoset_injOn
      src dst base A hcard root r)).mpr
    (sourceLiteralY1SelectedLocal_everyOldRootOffBOrbitIsolated
      src dst base A hcard root r)

end ABO
end PSTSEPPA
