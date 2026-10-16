import PSTSEPPA.ABO.KStablePullbackMultiCosetStageCoverEmbedding
import PSTSEPPA.ABO.CompletedFullCosetStage
import PSTSEPPA.ABO.SingleCosetConnectivity
import PSTSEPPA.ABO.PullbackAttachedCosetSupportTransport

/-!
# Source H-stage Cayley cover: OLD-root agreement determines ALL tagged coset points

Corrected ABO Theorem 4.7(ii) uses the TRUE signed Cayley(G)
cover of a LEGALLY completed H-coset stage to obtain the
mixed-support collision at the EXACT quotient-tagged points.

Our certified #614 embedding theorem has an explicit
hypothesis F(g)=transport(p) for EVERY attached G coset
point p with ambient group value g. The source actually
gives a more natural way to verify this hypothesis:
it is enough that F agrees on the ORIGINAL old skeleton
vertices with their exact component-tagged images.

A tagged attached B-coset point p is anchored at an
actual old G vertex x of its intrinsic B-component.
Its ambient G value g belongs to x·G[B], so choose a
chronological signed B-word w from x to g. Mapping
that G-Cayley word through F yields F(g).

Downstairs, starting at the exact tagged old H image
of x, the SAME signed B-word w follows actual FULL
B-coset edges in the genuine H multiCE. Their
endpoint has precisely the transported B-component
tag AND H group value Q(g), so it is exactly the
component-tagged attached H point transport(p).
The completed stage adds only missing loops and
preserves every original signed B-edge.

Therefore OLD-SKELETON agreement ⇒ full attached-point
representation without ever assuming that the H
multiCE ambient-coordinate map is injective.

Combining with certified #614 gives conditional
G-full-multiCE ambient embeddedness under a G-Cayley
cover compatible ONLY with the actual old G-skeleton.

The remaining genuine source gate is the existence
and normalization of such a SINGLE compatible F
for all relevant original old components of each
selected H-stage, not the extension to its tagged
coset vertices. Theorem 4.7(iii), Condition 5.2,
higher ranks and PSTS EPPA remain OPEN.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- A TRUE selected signed B-coset point of the original
G old-edge pullback is represented EXACTLY by the
complete H-stage Cayley morphism whenever the morphism
agrees at ONE old G root of that point's original
intrinsic B-component. No global H ambient injection
or arbitrary coset-component tag identification. -/
theorem weakMultiCosetCompletedStage_attached_representation_of_old_anchor
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (x : (K.pullbackQuotient Q).Vertex)
    (hAnchor :
      F.onVertex x.1 =
        K.multiCosetInclude P hAdmH hGenH hRetH B hBP
          (K.attachedOfSkeletonVertex B
            ((K.pullbackQuotientHom Q).onVertex x)))
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B)
    (hIndex : p.1 = (K.pullbackQuotient Q).componentClass B x) :
    F.onVertex p.2.1 =
      K.multiCosetInclude P hAdmH hGenH hRetH B hBP
        (K.pullbackQuotient_attachedCosetToBase Q B p) := by
  let L := K.pullbackQuotient Q
  let T := K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak
  let p0 : K.AttachedCosetVertex B :=
    K.attachedOfSkeletonVertex B
      ((K.pullbackQuotientHom Q).onVertex x)
  let pH : K.AttachedCosetVertex B :=
    K.pullbackQuotient_attachedCosetToBase Q B p
  have hpCoset : p.2.1 ∈ generatedLeftCoset genΓ B x.1 := by
    have hval : p.2.1 ∈ L.componentAmbientCoset B
        (L.componentClass B x) := by
      simpa only [hIndex] using p.2.2
    exact hval
  obtain ⟨w, hwB, hwEnd⟩ :=
    (mem_generatedLeftCoset_iff_subalphabetReachable
      genΓ B x.1 p.2.1).mp hpCoset
  have hGPath :
      (cayleyGraph genΓ).toEGraph.Follows x.1 w p.2.1 := by
    have h := (cayleyGraph genΓ).follows_followWord x.1 w
    rw [hwEnd] at h
    exact h
  have hFPath : T.toEGraph.Follows
      (F.onVertex x.1) w (F.onVertex p.2.1) :=
    hGPath.map F
  obtain ⟨q, hqPath, hqIndex, hqValue⟩ :=
    K.singleCosetEGraph_follows_word B p0 hwB
  have hp0Index : p0.1 = pH.1 := by
    calc
      p0.1 =
          K.pullbackQuotient_componentIndexToBase Q B
            (L.componentClass B x) := rfl
      _ = K.pullbackQuotient_componentIndexToBase Q B p.1 :=
        congrArg (K.pullbackQuotient_componentIndexToBase Q B)
          hIndex.symm
      _ = pH.1 := rfl
  have hGroupEnd :
      x.1 * PSTS.SignedWord.evalGroup genΓ w = p.2.1 := by
    calc
      x.1 * PSTS.SignedWord.evalGroup genΓ w =
          (cayleyGraph genΓ).followWord x.1 w :=
        (cayleyGraph.followWord_eq_mul_evalGroup genΓ x.1 w).symm
      _ = p.2.1 := hwEnd
  have hqHValue : q.2.1 = pH.2.1 := by
    calc
      q.2.1 = p0.2.1 * PSTS.SignedWord.evalGroup genΔ w := hqValue
      _ = Q.hom x.1 * PSTS.SignedWord.evalGroup genΔ w := rfl
      _ = Q.hom (x.1 * PSTS.SignedWord.evalGroup genΓ w) := by
        rw [map_mul, Q.map_evalGroup]
      _ = Q.hom p.2.1 := congrArg Q.hom hGroupEnd
      _ = pH.2.1 := rfl
  have hqIsTarget : q = pH :=
    K.attachedValue_injective_of_same_index B
      (hqIndex.trans hp0Index) hqHValue
  have hCEPath :
      (K.multiCosetEGraph P hAdmH hGenH hRetH).Follows
        (K.multiCosetInclude P hAdmH hGenH hRetH B hBP p0)
        w
        (K.multiCosetInclude P hAdmH hGenH hRetH B hBP q) :=
    hqPath.map (K.singleCosetToMultiHom P hAdmH hGenH hRetH B hBP)
  have hStagePath :
      T.toEGraph.Follows
        (K.multiCosetInclude P hAdmH hGenH hRetH B hBP p0)
        w
        (K.multiCosetInclude P hAdmH hGenH hRetH B hBP q) := by
    exact hCEPath.map
      ((K.multiCosetEGraph P hAdmH hGenH hRetH).trivialLoopCompletionHom
        (K.multiCoset_locallyPairedLabels_of_weakComplete
          P hAdmH hGenH hRetH hweak))
  have hStagePathFromRoot :
      T.toEGraph.Follows
        (F.onVertex x.1) w
        (K.multiCosetInclude P hAdmH hGenH hRetH B hBP q) := by
    rw [hAnchor]
    exact hStagePath
  calc
    F.onVertex p.2.1 =
        K.multiCosetInclude P hAdmH hGenH hRetH B hBP q :=
      T.toEGraph.follows_right_unique hFPath hStagePathFromRoot
    _ = K.multiCosetInclude P hAdmH hGenH hRetH B hBP pH :=
      congrArg (K.multiCosetInclude P hAdmH hGenH hRetH B hBP) hqIsTarget

/-- To represent ALL tagged G-coset points in the genuine
completed H stage, it is enough to check the selected
Cayley map F ONLY on ORIGINAL G old skeleton vertices,
with exact old H component tags. This avoids the
stronger all-attached-point axiom-like hRepresent from #614. -/
theorem weakMultiCosetCompletedStage_represents_all_attached_of_old_agreement
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (hOld :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (x : (K.pullbackQuotient Q).Vertex),
        F.onVertex x.1 =
          K.multiCosetInclude P hAdmH hGenH hRetH B hBP
            (K.attachedOfSkeletonVertex B
              ((K.pullbackQuotientHom Q).onVertex x))) :
    ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
      (p : (K.pullbackQuotient Q).AttachedCosetVertex B),
      F.onVertex p.2.1 =
        K.multiCosetInclude P hAdmH hGenH hRetH B hBP
          (K.pullbackQuotient_attachedCosetToBase Q B p) := by
  intro B hBP p
  let L := K.pullbackQuotient Q
  obtain ⟨x, hx⟩ :
      ∃ x : L.Vertex, L.componentClass B x = p.1 := by
    induction p.1 using Quotient.inductionOn with
    | h x => exact ⟨x, rfl⟩
  exact K.weakMultiCosetCompletedStage_attached_representation_of_old_anchor
    Q P hAdmH hGenH hRetH hweak B hBP F x
    (hOld B hBP x) p hx.symm

/-- Corrected ABO Theorem 4.7(ii) transfer of
FULL G-multiCE embeddedness under a G-Cayley
cover of the ACTUAL legal completed H-stage,
with compatibility assumed ONLY on genuine OLD
skeleton vertices, not on all G attached vertices.
Mixed B/C original support reflection is certified
by #608 and uses exact G/H old paths, not ambient H
coordinate injectivity. -/
theorem pullbackQuotient_multiCosetAmbient_injective_of_old_agreeing_stageCover
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hStable : ∀ B : Finset ι, B ∈ P.alphabets → Q.StableAt B)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (hOld :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (x : (K.pullbackQuotient Q).Vertex),
        F.onVertex x.1 =
          K.multiCosetInclude P hAdmH hGenH hRetH B hBP
            (K.attachedOfSkeletonVertex B
              ((K.pullbackQuotientHom Q).onVertex x))) :
    Function.Injective
      ((K.pullbackQuotient Q).multiCosetAmbientValue
        P hAdmG hGenG hRetG) :=
  K.pullbackQuotient_multiCosetAmbient_injective_of_stageCover
    Q P hAdmH hGenH hRetH hAdmG hGenG hRetG
      hStable
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak)
      F
      (K.weakMultiCosetCompletedStage_represents_all_attached_of_old_agreement
        Q P hAdmH hGenH hRetH hweak F hOld)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
