import PSTSEPPA.ABO.MultiCosetOffComponentPatches
import PSTSEPPA.ABO.MultiCosetVertexSupport

/-!
# The strict-lower-alphabet alternative for off-skeleton B-components

ABO's whole-component cluster property distinguishes full B-cosets
from clusters formed by proper subalphabets of B.

The precise local obstruction is whether a B-component
contains a point from a selected full C-coset with B⊆C.
If no such larger/equal attached constituent is met, every
B-labelled edge throughout the off-skeleton B-component
comes from a completed C-coset with C∩B **strictly smaller**
than B.

This turns the earlier local intersection-patch theorem into a
well-founded rank-decreasing input for the remaining cluster
geometry. It does not prove a common core for the patches,
and does not assume the cluster property as an axiom.

All containment uses literal selected component-tagged supports,
not ambient group projections.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If an off-skeleton B-component never meets any completed
C-constituent with B⊆C, its entire oriented B-edge set is
covered by genuine strictly lower (B∩C)-coset patches.

The 'no full constituent' premise is a geometric condition
on all B-reachable vertices, rather than on one chosen
vertex or on untagged group values. -/
theorem allProperCoset_off_B_component_strict_lower_edge_patches
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hOff :
      ¬ ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            B hBP).onVertex x) w z)
    (hNoLarge :
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows z w y) →
        ∀ (C : Finset ι)
          (hCP : C ∈ (allProperCosetFamily A).alphabets),
          B ⊆ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret C y)
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
      signedBase ((K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).label e) ∈ B) :
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
  obtain ⟨C, hCP, p, s, hletter, he⟩ :=
    K.allProperCoset_off_B_component_edges_have_lower_patches
      hadm hgen hret B hBP z hOff y hzy e heSource heB
  have hyCPresentation :
      K.MultiCosetVertexSupported P hadm hgen hret C y := by
    refine ⟨hCP, p, ?_⟩
    have hsrc :
        G.source e =
          K.multiCosetInclude P hadm hgen hret C hCP p := by
      rw [he]
      rfl
    exact hsrc.symm.trans heSource
  have hNotLarge : ¬ B ⊆ C := by
    intro hBC
    exact hNoLarge y hzy C hCP hBC hyCPresentation
  have hStrict : C ∩ B ⊂ B := by
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro hBsub
    apply hNotLarge
    intro t ht
    exact (Finset.mem_inter.mp (hBsub ht)).1
  exact ⟨C, hCP, p, s, hStrict, hletter, he⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
