import PSTSEPPA.ABO.MultiCosetSupportSkeletonMeet
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Component-invariance of skeleton-meeting support

The full proper-alphabet coset extension may possess B-components
not meeting the old skeleton. Before a whole-component cluster
property can be proved or assumed, it is useful to know that
this off-skeleton status is *intrinsic* to an entire B-component.

We show this directly by concatenating actual signed B-word paths:
B-reachability from some old skeleton point cannot change along a
B-path. Combined with the checked least component-tagged vertex
support criterion, it follows that if z,y are B-connected, the
smallest supporting alphabet of z is contained in B iff the
smallest supporting alphabet of y is contained in B.

Importantly, this is an invariant only of the predicate M⊆B,
not equality of M and N. The latter is generally unwarranted.
No cluster property or ambient Cayley injectivity is used.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Skeleton-meeting status is invariant under realised B-labelled
paths in the *full* multi-coset extension. The skeleton inclusion
is fixed by the selected B-constituent and is injective. -/
theorem allProperCoset_B_component_skeleton_meeting_iff
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hzy : ∃ p : LabelWord ι, LabelWord.Uses B p ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z p y) :
    (∃ (x : K.Vertex) (w : LabelWord ι),
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom
          (allProperCosetFamily A) hadm hgen hret
          B hBP).onVertex x) w z) ↔
    (∃ (x : K.Vertex) (w : LabelWord ι),
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom
          (allProperCosetFamily A) hadm hgen hret
          B hBP).onVertex x) w y) := by
  let G := K.multiCosetEGraph (allProperCosetFamily A)
    hadm hgen hret
  obtain ⟨p, hp, hpath⟩ := hzy
  constructor
  · rintro ⟨x, w, hw, hxz⟩
    refine ⟨x, w ++ p, (LabelWord.uses_append B w p).2
      ⟨hw, hp⟩, ?_⟩
    exact G.follows_append hxz hpath
  · rintro ⟨x, w, hw, hxy⟩
    refine ⟨x, w ++ PSTS.SignedWord.inv p,
      (LabelWord.uses_append B w
        (PSTS.SignedWord.inv p)).2 ⟨hw, hp.inv⟩, ?_⟩
    exact G.follows_append hxy (G.follows_inverse hpath)

/-- For two B-connected vertices with respective least
component-tagged supports (M,p), (N,q), exactly one component
invariant is guaranteed: M⊆B iff N⊆B. These minima need not
be equal and this theorem makes no such false claim. -/
theorem allProperCoset_B_path_least_support_subset_iff
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (M N : Finset ι)
    (hMP : M ∈ (allProperCosetFamily A).alphabets)
    (hNP : N ∈ (allProperCosetFamily A).alphabets)
    (p : K.AttachedCosetVertex M)
    (q : K.AttachedCosetVertex N)
    (hp : K.multiCosetInclude (allProperCosetFamily A)
      hadm hgen hret M hMP p = z)
    (hq : K.multiCosetInclude (allProperCosetFamily A)
      hadm hgen hret N hNP q = y)
    (hminM :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets)
        (r : K.AttachedCosetVertex C),
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP r = z →
        ∃ hMC : M ⊆ C,
          K.attachedSubalphabetMap M C hMC p = r)
    (hminN :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets)
        (r : K.AttachedCosetVertex C),
        K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP r = y →
        ∃ hNC : N ⊆ C,
          K.attachedSubalphabetMap N C hNC q = r)
    (hzy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w y) :
    (M ⊆ B ↔ N ⊆ B) := by
  have hz :=
    K.allProperCoset_least_support_subset_iff_B_skeleton_reachable
      hadm hgen hret z M hMP p hp hminM B hBP
  have hy :=
    K.allProperCoset_least_support_subset_iff_B_skeleton_reachable
      hadm hgen hret y N hNP q hq hminN B hBP
  exact hz.trans
    ((K.allProperCoset_B_component_skeleton_meeting_iff
      hadm hgen hret B hBP z y hzy).trans hy.symm)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
