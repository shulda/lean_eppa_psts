import PSTSEPPA.ABO.MultiCosetMinimalSupportPaths
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Least vertex support detects skeleton-meeting components

An ordinary vertex of the full proper-alphabet coset extension
has a least *component-tagged* support (M,p). Fix any proper
subalphabet B⊂A. We prove two source-facing statements:

* the vertex belongs to the selected full B-coset constituent
  of the extension iff M⊆B;
* equivalently, there is an actual B-labelled path from an
  embedded old skeleton vertex to it iff M⊆B.

This is the precise singleton-support test distinguishing
skeleton-meeting B-components from those which have no old
skeleton anchor. It is a useful preparation for the much
stronger off-skeleton whole-component cluster property of
Definition 3.22; it does NOT assert that property itself.

The proof uses the exact selected-constituent B-component
theorem and finite intersection of component-tagged
supports, not equality in the ambient Cayley projection.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- A quotient vertex's least supporting alphabet lies within
B iff the same vertex has an actual tagged presentation in
the selected complete B-coset constituent. This is an exact
iff, including B=∅ and cases with repeated/trivial generators. -/
theorem allProperCoset_least_support_subset_iff_B_presentation
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (M : Finset ι)
    (hMP : M ∈ (allProperCosetFamily A).alphabets)
    (p : K.AttachedCosetVertex M)
    (hp : K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret M hMP p = z)
    (hmin :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets)
        (q : K.AttachedCosetVertex C),
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP q = z →
        ∃ hMC : M ⊆ C,
          K.attachedSubalphabetMap M C hMC p = q)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets) :
    M ⊆ B ↔
      ∃ q : K.AttachedCosetVertex B,
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret B hBP q = z := by
  constructor
  · intro hMB
    let q := K.attachedSubalphabetMap M B hMB p
    refine ⟨q, ?_⟩
    calc
      K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret B hBP q =
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret M hMP p :=
        (K.multiCosetInclude_alphabet_mono
          (allProperCosetFamily A) hadm hgen hret
          M B hMB hMP hBP p).symm
      _ = z := hp
  · rintro ⟨q, hq⟩
    obtain ⟨hMB, _⟩ := hmin B hBP q hq
    exact hMB

/-- A vertex is B-reachable from some embedded old skeleton point
in the **whole** full multi-CE iff its least supporting alphabet
M is contained in B. This is the singleton test for whether
its genuine B-component meets the old skeleton. -/
theorem allProperCoset_least_support_subset_iff_B_skeleton_reachable
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (M : Finset ι)
    (hMP : M ∈ (allProperCosetFamily A).alphabets)
    (p : K.AttachedCosetVertex M)
    (hp : K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret M hMP p = z)
    (hmin :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets)
        (q : K.AttachedCosetVertex C),
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP q = z →
        ∃ hMC : M ⊆ C,
          K.attachedSubalphabetMap M C hMC p = q)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets) :
    M ⊆ B ↔
      ∃ (x : K.Vertex) (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            B hBP).onVertex x) w z := by
  constructor
  · intro hMB
    have hBPresentation :=
      (K.allProperCoset_least_support_subset_iff_B_presentation
        hadm hgen hret z M hMP p hp hmin B hBP).mp hMB
    obtain ⟨q, hq⟩ := hBPresentation
    obtain ⟨x, hx⟩ := K.componentClass_surjective B q.1
    obtain ⟨w, hw, hpath⟩ :=
      K.singleCosetEGraph_connected_on_index
        B (K.attachedOfSkeletonVertex B x) q hx
    have hMapped := hpath.map
      (K.singleCosetToMultiHom
        (allProperCosetFamily A) hadm hgen hret B hBP)
    change (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
      ((K.skeletonToMultiCosetHom
        (allProperCosetFamily A) hadm hgen hret
        B hBP).onVertex x) w
      (K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret B hBP q) at hMapped
    rw [hq] at hMapped
    exact ⟨x, w, hw, hMapped⟩
  · rintro ⟨x, w, hw, hpath⟩
    have hBPath :
      ∃ u : LabelWord ι, LabelWord.Uses B u ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          (K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret B hBP
            (K.attachedOfSkeletonVertex B x)) u z :=
      ⟨w, hw, hpath⟩
    obtain ⟨q, _, hq⟩ :=
      (K.multiCoset_selected_B_component_exact
        (allProperCosetFamily A) hadm hgen hret B hBP
        (K.attachedOfSkeletonVertex B x) z).mp hBPath
    exact (K.allProperCoset_least_support_subset_iff_B_presentation
      hadm hgen hret z M hMP p hp hmin B hBP).mpr
        ⟨q, hq.symm⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
