import PSTSEPPA.ABO.SourceLiteralY1FirstRankRootedOffBOrbitIsolation
import PSTSEPPA.ABO.SourceLiteralY1AllOldRootComponentsEmbedded

/-!
# True type-(2) B-orbit isolation on EVERY original old G[A] A-component

The first-rank globally finite corrected ABO source G=T(X₂^all)
to H=T(Y₁) has an actual original incomplete signed
old G[A] pullback which need NOT be connected in its old A-edges.

The accepted first-rank type-(2) detector on the old-IDENTITY
rooted A-component uses only the genuine signed path between
the chosen off-B old+fresh quotient point and its comparison
point, and the injectivity of ambient G[A] coordinates on
THAT selected signed A-component.

Separately, the certified surjective full Cayley(G[A])
cover of the genuine H[A] completed P_A stage proves that
EVERY original old G[A] A-component's own full old+fresh
attached region is ambient-coordinate embedded (PR #670).

This module combines those two independently verified
properties: for an ARBITRARY chosen original old G[A] root r,
ANY actual off-B quotient point z in the attached A-component
of r has NO distinct point v of that same component in its
ambient GLOBAL finite G[B] left coset for proper B⊊A.

The based type-(2) augmentation is genuinely selected at z
and the global Cayley(G) signed cover is based at the
ACTUAL G-group coordinate S(z); it does NOT need any relation
to the arbitrary original old root r beyond the real A-path
connecting z and v and component-scoped ambient injectivity.

All original oriented signed edge tokens, old/new component
tags and legal loop completions remain actual source objects.
This still does NOT imply GLOBAL multiCE injectivity across
distinct disconnected old A-components, or the full unqualified
corrected ABO 4.7(iii), higher induction/Condition 5.2/PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The genuine FIRST RANK source G=T(X₂^all) based type-(2)
B-augmentation excludes every external global G[B]-bridge
from one off-B point z to another vertex v of the SAME
rooted original signed A-component.

This is an unconditional mathematical source theorem.
It uses the real global Q:G↠H ONE-stability and the
actual original H-paper off-B index and based Cayley cover,
not a locally invented H-graph or a globally embedded
H ambient coset extension. -/
theorem sourceLiteralY1SelectedLocal_everyOldRootOffB_globalOrbit_isolated
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (r : (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).Vertex)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z v : (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).MultiCosetVertex (allProperCosetFamily A) (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root) (sourceLiteralY1X2AllLocal_isGenerated src dst A) (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le))
    (hz : z ∈ (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).rootedMultiCosetImage (allProperCosetFamily A) (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root) (sourceLiteralY1X2AllLocal_isGenerated src dst A) (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le) r)
    (hv : v ∈ (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).rootedMultiCosetImage (allProperCosetFamily A) (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root) (sourceLiteralY1X2AllLocal_isGenerated src dst A) (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le) r)
    (hOff : ¬ ∃ p : (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).AttachedCosetVertex B,
      (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).multiCosetInclude (allProperCosetFamily A) (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root) (sourceLiteralY1X2AllLocal_isGenerated src dst A) (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le) B hBP p = z)
    (hCoset : (sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom src dst base A hcard root).onVertex v ∈
      generatedLeftCoset (sourceLiteralY1X2AllGenerator src dst) B
        ((sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom src dst base A hcard root).onVertex z)) :
    z = v := by
  let K := (sourceLiteralY1SelectedLocalGOldPullback src dst base A root)
  let P := (allProperCosetFamily A)
  let hAdm := (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root)
  let hGen := (sourceLiteralY1X2AllLocal_isGenerated src dst A)
  let hRet := (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
  let oldRoot := r
  let L := K.multiCosetEGraph P hAdm hGen hRet
  let H := sourceLiteralY1SelectedRootCompletedEGraph src dst base A hcard root P
  let genG := sourceLiteralY1X2AllGenerator src dst
  let genH := (sourceLiteralY1 src dst).transitionSubgroupGenerator
  let Q := sourceLiteralY1X2AllToY1 src dst
  let S := (sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom src dst base A hcard root)
  let M := (sourceLiteralY1SelectedLocalGOldToPrintedSignedHom src dst base A hcard root)
  let idx := (sourceLiteralY1SelectedLocalGOffB_toPrintedType2 src dst base A hcard root B hBP z hOff)
  let F := (sourceLiteralY1SelectedLocalGOffB_globalType2BasedHom src dst base A hcard root B hBP z hOff)
  let Hroot := idx.vertex
  let g : (sourceLiteralY1 src dst).transitionGroup :=
    sourceLiteralY1SelectedRootAmbientValue src dst base A hcard root P Hroot
  have hStable : Q.StableAt B := by
    exact (sourceLiteralY1X2AllToY1_oneStable src dst) B
      (rankTwoProper_card_le_one A B hcard (P.proper B hBP))
  have hMissing : H.NoSignedBEdgesAt B Hroot :=
    idx.paper_noOldBEdges src dst base A hcard root B hBP
  have hPaired : H.LocallyPairedLabels :=
    sourceLiteralY1SelectedRootAllProper_locallyPaired
      src dst base A hcard root
  have hOldRoot : M.onVertex z = Hroot :=
    (sourceLiteralY1SelectedLocalGOffB_toPrintedType2_oldRoot
      src dst base A hcard root B hBP z hOff).symm
  have hBased : F.onVertex (S.onVertex z) = Sum.inl Hroot := by
    exact sourceLiteralY1SelectedLocalGOffB_globalType2BasedHom_oldRoot
      src dst base A hcard root B hBP z hOff
  have hRealPath : ∃ w : LabelWord ι, L.Follows z w v := by
    obtain ⟨w, _hw, hwPath⟩ :=
      K.rootedMultiCosetImage_A_connected P hAdm hGen hRet
        oldRoot ∅
        (empty_mem_allProperCosetFamily A
          (Finset.card_pos.mp (by rw [hcard]; decide)))
        z v hz hv
    exact ⟨w, hwPath⟩
  have hPair : S.onVertex v = S.onVertex z → v = z := by
    intro heq
    have hLocal :
        K.multiCosetAmbientValue P hAdm hGen hRet v =
          K.multiCosetAmbientValue P hAdm hGen hRet z := by
      apply Subtype.ext
      exact heq
    exact (sourceLiteralY1SelectedLocal_everyOldRoot_rootedMultiCoset_injOn
      src dst base A hcard root r) hv hz hLocal
  have hOldBased : F.onVertex (S.onVertex z) = Sum.inl (M.onVertex z) := by
    rw [hOldRoot]
    exact hBased
  have hResult : v = z := by
    exact L.basedAugmentedOldLift_B_orbit_vertex_isolated_of_path
      H genG genH Q B hStable g Hroot
      hMissing hPaired S M F
      z v hOldRoot hBased hRealPath hCoset hPair
  exact hResult.symm

end ABO
end PSTSEPPA
