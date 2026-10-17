import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalGOffBGlobalType2BasedCover
import PSTSEPPA.ABO.SourceLiteralY1LocalGOldToPrintedSignedHom
import PSTSEPPA.ABO.AugmentedOldRootedSinglePathDetector
import PSTSEPPA.ABO.RootedMultiCosetAComponentExact
import PSTSEPPA.ABO.LocalSubgroupCosetNaturality

/-!
# REAL FIRST-RANK corrected ABO 4.7(iii): isolate singleton B external bridges
# over ONE selected ORIGINAL signed G[A] old A-component

This theorem invokes the independently checked actual source
first-rank signed geometric constructions, with ZERO new abstract
Cayley covers, fake completion edges or ambient coordinate quotient:
1. the selected original old+fresh G[A] multiCE is an intrinsic
   A-connected, oriented-edge-closed signed component, AND its
   real A-supported signed graph embeds into global finite
   Cayley(G=T(X₂^all)), with vertex injection on this region;
2. its true signed OLD morphism goes to the original
   component-tagged PRINTED H=T(Y₁) rooted P_A multiCE;
3. any G off-B vertex maps to an H off-B vertex using real
   stable pullback B/C support reflection;
4. this H off-B point selects a LITERAL printed type-(2)
   B-augmented legally completed signed action;
5. the original finite G Cayley action covers this ACTUAL type-(2)
   stage, based at EXACTLY the original G global coordinate
   of the off-B vertex, and sends that point to its true
   OLD component-tagged H augmentation root;
6. the already certified generic augmented signed B-word detector
   uses a REAL old A-path from that off-B vertex to every
   candidate vertex of the SAME selected A-component.
   Global Q:G↠H is 1-stable, hence B-stable for every B⊊A.

This proves that an original off-B vertex of the selected
A-component has NO OTHER vertex of that component in the same
ambient G[B]-coset. Existing full-B-coset saturation and
the certified rank-two dichotomy therefore imply the precise
ROOTED RELATIVE proper-B bridge-reflection property for this
one original A-component.

SCOPE IS DELIBERATELY LIMITED: the full original G pullback
can be disconnected, other old A-components are not included,
and this does NOT automatically establish global corrected
4.7(iii), the distinct R8 full-B-coset cluster repair,
Condition 5.2, higher rank, or ordinary finite PSTS EPPA.
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
theorem sourceLiteralY1SelectedLocal_rootedOffB_globalOrbit_isolated
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z v : (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).MultiCosetVertex (allProperCosetFamily A) (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root) (sourceLiteralY1X2AllLocal_isGenerated src dst A) (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le))
    (hz : z ∈ (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).rootedMultiCosetImage (allProperCosetFamily A) (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root) (sourceLiteralY1X2AllLocal_isGenerated src dst A) (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le) (sourceLiteralY1SelectedLocalGOld_identity src dst base A root))
    (hv : v ∈ (sourceLiteralY1SelectedLocalGOldPullback src dst base A root).rootedMultiCosetImage (allProperCosetFamily A) (sourceLiteralY1SelectedLocalGOld_admissible src dst base A hcard root) (sourceLiteralY1X2AllLocal_isGenerated src dst A) (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le) (sourceLiteralY1SelectedLocalGOld_identity src dst base A root))
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
  let oldRoot := (sourceLiteralY1SelectedLocalGOld_identity src dst base A root)
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
  have hMissing :
      ∀ e : H.toLabelledGraph.Edge,
        H.source e = Hroot → signedBase (H.label e) ∉ B := by
    exact idx.paper_noOldBEdges src dst base A hcard root B hBP
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
    exact (sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom_rooted_injOn
      src dst base A hcard root) hv hz heq
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
