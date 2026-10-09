import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.MultiCosetOffComponentProperPatches
import PSTSEPPA.ABO.MultiCosetVertexSupport

/-!
# Constancy of large tagged-coset support along smaller-alphabet paths

Let B ⊆ C with C a selected alphabet in an arbitrary multi-coset
extension. A genuine B-path can neither enter nor leave the image
of the completed C-coset constituents. This is an immediate but
useful consequence of deterministic global EGraph edges and
completion of every C-labelled edge inside the selected C-copy.

Thus the no-large-coset premise needed for the strict-lower-rank
edge-patch lemma can be verified *only at a starting vertex*
rather than independently at all vertices of its B-component.

The resulting pointwise criterion is a rank-decreasing input
towards the higher-rank whole-component cluster property;
it does not assert a common core for the patches.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Support by a selected C-constituent is invariant along actual
B-paths whenever B ⊆ C. The statement retains component tags;
mere equality of Cayley coordinates would not suffice. -/
theorem multiCoset_selected_superset_support_invariant
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hBC : B ⊆ C)
    (z y : K.MultiCosetVertex P hadm hgen hret)
    (hzy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows z w y) :
    K.MultiCosetVertexSupported P hadm hgen hret C z ↔
      K.MultiCosetVertexSupported P hadm hgen hret C y := by
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨w, hw, hpath⟩ := hzy
  constructor
  · rintro ⟨hCP, p, hp⟩
    have hpath' :
        G.Follows
          (K.multiCosetInclude P hadm hgen hret C hCP p) w y := by
      rw [hp]
      exact hpath
    obtain ⟨q, _, hq⟩ :=
      K.multiCoset_selected_B_path_stays_in_coset
        P hadm hgen hret C hCP w (hw.mono hBC)
        p y hpath'
    exact ⟨hCP, q, hq.symm⟩
  · rintro ⟨hCP, p, hp⟩
    have hpath' :
        G.Follows
          (K.multiCosetInclude P hadm hgen hret C hCP p)
          (PSTS.SignedWord.inv w) z := by
      rw [hp]
      exact G.follows_inverse hpath
    obtain ⟨q, _, hq⟩ :=
      K.multiCoset_selected_B_path_stays_in_coset
        P hadm hgen hret C hCP (PSTS.SignedWord.inv w)
        ((hw.inv).mono hBC) p z hpath'
    exact ⟨hCP, q, hq.symm⟩

/-- To cover all B-edges of an off-skeleton B-component by
strictly lower-alphabet (B∩C)-patches, it suffices to check
at the single starting point z that no selected C ⊇ B
supports z. Both off-skeleton status and the same support
obstruction throughout the B-component then follow automatically. -/
theorem allProperCoset_B_component_pointwise_no_large_strict_patches
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoLargeZ :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C z)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hzy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w y)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (heSource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e = y)
    (heB :
      signedBase ((K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).label e) ∈ B) :
    ∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex C)
      (s : {s : SignedLabel ι // signedBase s ∈ C}),
      (C ∩ B) ⊂ B ∧
      signedBase s.1 ∈ C ∩ B ∧
      e = K.multiCosetEdgeInclude
        (allProperCosetFamily A) hadm hgen hret
        C hCP (Sum.inr (p, s)) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  have hOff :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        G.Follows
          ((K.skeletonToMultiCosetHom P
            hadm hgen hret B hBP).onVertex x) w z := by
    rintro ⟨x, w, hw, hpath⟩
    have hbase :
        K.MultiCosetVertexSupported P hadm hgen hret B
          ((K.skeletonToMultiCosetHom
            P hadm hgen hret B hBP).onVertex x) := by
      refine ⟨hBP, K.attachedOfSkeletonVertex B x, ?_⟩
      rfl
    have hzB :
        K.MultiCosetVertexSupported P hadm hgen hret B z :=
      (K.multiCoset_selected_superset_support_invariant
        P hadm hgen hret B B (subset_rfl)
        _ _ ⟨w, hw, hpath⟩).mp hbase
    exact hNoLargeZ B hBP (subset_rfl) hzB
  have hNoLarge :
      ∀ y : K.MultiCosetVertex P hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          G.Follows z w y) →
        ∀ (C : Finset ι) (hCP : C ∈ P.alphabets),
          B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            P hadm hgen hret C y := by
    intro v hzv C hCP hBC hCv
    exact hNoLargeZ C hCP hBC
      ((K.multiCoset_selected_superset_support_invariant
        P hadm hgen hret B C hBC z v hzv).mpr hCv)
  exact K.allProperCoset_off_B_component_strict_lower_edge_patches
    hadm hgen hret B hBP z hOff hNoLarge y hzy e heSource heB

end CayleySubgraphSpec
end ABO
end PSTSEPPA
