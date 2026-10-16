import PSTSEPPA.ABO.CompletedHStageOldAnchorDeterminesAttached
import PSTSEPPA.ABO.BasedCayleyStageOldComponentAgreement
import PSTSEPPA.ABO.CayleyLeftTranslations
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# One ROOTED old G-component controls all tagged attached cosets in an H-stage

The corrected source Theorem 4.7(ii) does not require a
Cayley(G)→completed-H-multiCE-stage cover to satisfy an
axiomatic compatibility at every attached coset vertex.

For the ACTUAL completed multi-coset stage, assume the
Cayley cover F takes the group identity to the TRUE
component-tagged old H image of ONE old G-cover root r.

If the old G-skeleton L=Q⁻¹(K) consists of the single
intrinsic A-component of r, then the corresponding
left-normalized Cayley map
    F_r(g) = F(r⁻¹ g)
automatically agrees on ALL OLD signed G skeleton
vertices with their exact tagged H images. This
follows from the already Lean-checked root-normalized
old-path compatibility theorem and uniqueness of
deterministic signed word endpoints.

The separately staged #617 lemma then shows that
F_r automatically represents ALL attached B-coset
vertices, for ALL selected proper B∈P, by following
genuine single-coset signed B paths from old anchors.
There is no need to check any new-vertex
compatibility separately.

Consequently, when Q is stable on every chosen B,
the entire ORIGINAL component-tagged full G multiCE
has an INJECTIVE ambient Cayley coordinate map.
This no longer assumes H multiCE ambient embeddedness
or an axiom for the attached points, only the
EXISTENCE of one root-compatible G Cayley-to-H-stage
cover on the chosen old connected component.

The real source still has to select and transport
that connected original component, its local
retractable/generated G[A]/H[A] presentations, and
a genuine G-Cayley cover for each needed completed
H-stage. This theorem does not invent those
source data, nor settle Theorem 4.7(iii), R8,
Condition 5.2, higher k, or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- The genuine ORIGINAL G-old-edge → H completed-multiCE
graph morphism. The intermediate maps are the ACTUAL
old-edge quotient cover and old H skeleton embedding,
followed by LEGAL trivial-loop completion; no edge is
invented in the original old G skeleton. -/
noncomputable def pullbackOldToWeakMultiCosetStageHom
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets) :
    LabelledGraphHom
      (K.pullbackQuotient Q).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph :=
  ((K.multiCosetEGraph P hAdmH hGenH hRetH).trivialLoopCompletionHom
    (K.multiCoset_locallyPairedLabels_of_weakComplete
      P hAdmH hGenH hRetH hweak)).comp
    ((K.skeletonToMultiCosetHom P hAdmH hGenH hRetH B₀ hB₀).comp
      (K.pullbackQuotientHom Q))

/-- The chosen old skeleton embedding uses the EXACT
component-tagged H vertex over the quotient-projected
old G vertex. The target is a true quotient CE point. -/
@[simp] theorem pullbackOldToWeakMultiCosetStageHom_vertex
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (x : (K.pullbackQuotient Q).Vertex) :
    (K.pullbackOldToWeakMultiCosetStageHom
      Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex x =
      K.multiCosetInclude P hAdmH hGenH hRetH B₀ hB₀
        (K.attachedOfSkeletonVertex B₀
          ((K.pullbackQuotientHom Q).onVertex x)) :=
  rfl

/-- Fix a single TRUE original G cover root r, and normalize
F(1)=the actual tagged old H image of r.
If L is the real signed A-connected component of r,
then the correctly translated map F_r(g)=F(r⁻¹g)
agrees with the old H skeleton representation on
EVERY old G point AND every selected B support.
This is the only old-vertex hypothesis #617 needs. -/
theorem pullbackOldToWeakMultiCosetStageHom_rooted_agreement
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (root : (K.pullbackQuotient Q).Vertex)
    (hOne :
      F.onVertex (1 : Γ) =
        (K.pullbackOldToWeakMultiCosetStageHom
          Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root)
    (hConnected :
      ∀ x : (K.pullbackQuotient Q).Vertex,
        (K.pullbackQuotient Q).SubalphabetReachable A root x) :
    ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
      (x : (K.pullbackQuotient Q).Vertex),
      F.onVertex (root.1⁻¹ * x.1) =
        K.multiCosetInclude P hAdmH hGenH hRetH B hBP
          (K.attachedOfSkeletonVertex B
            ((K.pullbackQuotientHom Q).onVertex x)) := by
  intro B hBP x
  let old :=
    K.pullbackOldToWeakMultiCosetStageHom
      Q P hAdmH hGenH hRetH hweak B₀ hB₀
  have hAgree :=
    (K.pullbackQuotient Q).basedCayleyStage_agrees_on_old_component
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak)
      old F root hOne x (hConnected x)
  calc
    F.onVertex (root.1⁻¹ * x.1) = old.onVertex x := hAgree
    _ = (K.skeletonToMultiCosetHom P hAdmH hGenH hRetH
          B₀ hB₀).onVertex ((K.pullbackQuotientHom Q).onVertex x) := rfl
    _ = (K.skeletonToMultiCosetHom P hAdmH hGenH hRetH
          B hBP).onVertex ((K.pullbackQuotientHom Q).onVertex x) :=
      K.skeletonToMultiCosetHom_vertex_independent
        P hAdmH hGenH hRetH B₀ B hB₀ hBP
          ((K.pullbackQuotientHom Q).onVertex x)
    _ = K.multiCosetInclude P hAdmH hGenH hRetH B hBP
          (K.attachedOfSkeletonVertex B
            ((K.pullbackQuotientHom Q).onVertex x)) := rfl

/-- The single old-root compatibility forces the
EXACT H component-tagged representation of EVERY
attached G B-coset point p after the necessary
source group-root left normalization.
No global H ambient CE embedding or arbitrary
old-component identification occurs. -/
theorem rootedWeakMultiCosetCompletedStage_represents_all_attached
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (root : (K.pullbackQuotient Q).Vertex)
    (hOne :
      F.onVertex (1 : Γ) =
        (K.pullbackOldToWeakMultiCosetStageHom
          Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root)
    (hConnected :
      ∀ x : (K.pullbackQuotient Q).Vertex,
        (K.pullbackQuotient Q).SubalphabetReachable A root x) :
    ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
      (p : (K.pullbackQuotient Q).AttachedCosetVertex B),
      F.onVertex (root.1⁻¹ * p.2.1) =
        K.multiCosetInclude P hAdmH hGenH hRetH B hBP
          (K.pullbackQuotient_attachedCosetToBase Q B p) := by
  let Froot : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph :=
    F.comp (cayleyLeftTranslateHom genΓ root.1⁻¹)
  have hOld :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (x : (K.pullbackQuotient Q).Vertex),
        Froot.onVertex x.1 =
          K.multiCosetInclude P hAdmH hGenH hRetH B hBP
            (K.attachedOfSkeletonVertex B
              ((K.pullbackQuotientHom Q).onVertex x)) := by
    intro B hBP x
    exact K.pullbackOldToWeakMultiCosetStageHom_rooted_agreement
      Q P hAdmH hGenH hRetH hweak B₀ hB₀ F root
      hOne hConnected B hBP x
  exact K.weakMultiCosetCompletedStage_represents_all_attached_of_old_agreement
    Q P hAdmH hGenH hRetH hweak Froot hOld

/-- Corrected Theorem 4.7(ii) for the full G multi-CE,
CONDITIONAL only on:
* genuine group quotient stable on selected B;
* actual generated/retractable local groups;
* genuine admissible old G/H Cayley skeletons;
* legal weak H coset stage completion;
* ONE rooted based G-Cayley cover whose old skeleton
  is the specified A-connected component.

No axiom about attached stage vertex representation,
and NO false H-ambient multiCE embedding assumption.
The source must still construct the above rooted
compatible cover and correct local component instance. -/
theorem pullbackQuotient_multiCosetAmbient_injective_of_rooted_stageCover
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hStable : ∀ B : Finset ι, B ∈ P.alphabets → Q.StableAt B)
    (hweak : K.MultiCosetWeaklyComplete P hAdmH hGenH hRetH)
    (B₀ : Finset ι) (hB₀ : B₀ ∈ P.alphabets)
    (F : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph)
    (root : (K.pullbackQuotient Q).Vertex)
    (hOne :
      F.onVertex (1 : Γ) =
        (K.pullbackOldToWeakMultiCosetStageHom
          Q P hAdmH hGenH hRetH hweak B₀ hB₀).onVertex root)
    (hConnected :
      ∀ x : (K.pullbackQuotient Q).Vertex,
        (K.pullbackQuotient Q).SubalphabetReachable A root x) :
    Function.Injective
      ((K.pullbackQuotient Q).multiCosetAmbientValue
        P hAdmG hGenG hRetG) := by
  let Froot : LabelledGraphHom
      (cayleyGraph genΓ).toEGraph.toLabelledGraph
      (K.weakMultiCosetCompletedStage P hAdmH hGenH hRetH hweak).toEGraph.toLabelledGraph :=
    F.comp (cayleyLeftTranslateHom genΓ root.1⁻¹)
  have hOld :
      ∀ (B : Finset ι) (hBP : B ∈ P.alphabets)
        (x : (K.pullbackQuotient Q).Vertex),
        Froot.onVertex x.1 =
          K.multiCosetInclude P hAdmH hGenH hRetH B hBP
            (K.attachedOfSkeletonVertex B
              ((K.pullbackQuotientHom Q).onVertex x)) := by
    intro B hBP x
    exact K.pullbackOldToWeakMultiCosetStageHom_rooted_agreement
      Q P hAdmH hGenH hRetH hweak B₀ hB₀ F root
      hOne hConnected B hBP x
  exact K.pullbackQuotient_multiCosetAmbient_injective_of_old_agreeing_stageCover
    Q P hAdmH hGenH hRetH hAdmG hGenG hRetG
      hStable hweak Froot hOld

end CayleySubgraphSpec
end ABO
end PSTSEPPA
