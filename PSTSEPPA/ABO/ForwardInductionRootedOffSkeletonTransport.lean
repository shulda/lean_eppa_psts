import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedCompletedEGraphIso
import PSTSEPPA.ABO.RootedTaggedAttachedCosetEquiv

/-!
# ABO Definition 3.22: true OFF-SKELETON components under source localization

The source whole-component cluster property quantifies ONLY over
B-components that do not meet the ORIGINAL OLD skeleton.

The arbitrary-rank local Γ[C] / original rooted Γ component
isomorphism is already known to preserve real signed paths
and both positive/inverse original old/fresh edge classes.
Here we identify OLD SKELETON POINTS on the FULL glued
coset extensions exactly, using the actual old-rooted
signed skeleton vertex equivalence and attached D-coset
naturality (not ambient group-coordinate equality).

We then derive invariance of the ACTUAL off-skeleton
B-component condition, for ANY finite signed subalphabet B,
under the exact source/local completed signed EGraph iso.

This is indispensable when transferring source Definition 3.22
cluster property from globally retractable H[C] back to
original Γ which may be only k-retractable. It does NOT assume
or assert that all components are off-skeleton, or identify
different original component tags.
No fictitious old edge, extra axioms, or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An ACTUAL ORIGINAL old-skeleton vertex inside the true
rooted C-component tagged multiCE quotient: some old vertex
is included via one selected attached D-coset copy.
The original ambient Γ need not be globally retractable. -/
def ArbitraryRankRootedOriginalOldPoint
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (z : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)) : Prop :=
  ∃ (D : Finset ι) (hDP : D ∈ P.alphabets)
    (x : (K.subalphabetComponentSubgraph C root).Vertex),
      Quotient.mk
        (K.arbitraryRankRootedOriginalMultiCosetSetoid
          C root P hadm hgen hret)
        (⟨⟨D,hDP⟩,
          (K.subalphabetComponentSubgraph C root).attachedOfSkeletonVertex D x⟩ :
          (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) = z

/-- Genuine local OLD vertex of the normalized Γ[C] proper-coset
extension, represented by a TRUE local old skeleton point. -/
def ArbitraryRankRootedLocalOldPoint
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (z : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) : Prop :=
  ∃ (D : Finset ι) (hDP : D ∈ P.alphabets)
    (x : (K.intrinsicComponentLocalSlice C root).Vertex),
    (K.intrinsicComponentLocalSlice C root).multiCosetInclude
      P hadm hgen hret D hDP
      ((K.intrinsicComponentLocalSlice C root).attachedOfSkeletonVertex D x)
      = z

/-- Source/local ORIGINAL OLD-SKELETON membership is
preserved and REFLECTED through the actual arbitrary-rank
component-tagged glued quotient equivalence.
Both directions use the genuine old signed vertex map,
not an untagged ambient Γ-coordinate equation. -/
theorem arbitraryRankRootedLocalOldPoint_iff_original
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (z : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    K.ArbitraryRankRootedLocalOldPoint C root P hadm hgen hret z ↔
    K.ArbitraryRankRootedOriginalOldPoint C root P hadm hgen hret
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret z) := by
  let L := K.intrinsicComponentLocalSlice C root
  let M := K.subalphabetComponentSubgraph C root
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  let f := K.intrinsicComponentLocalHom C root
  constructor
  · rintro ⟨D, hDP, x, hx⟩
    refine ⟨D, hDP, f.onVertex x, ?_⟩
    calc
      Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D,hDP⟩, M.attachedOfSkeletonVertex D (f.onVertex x)⟩ :
            M.MultiCosetRawVertex P) =
        Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D,hDP⟩,
            K.rootedLocalAttachedCosetMap C D
              (P.proper D hDP).subset root
              (L.attachedOfSkeletonVertex D x)⟩ :
            M.MultiCosetRawVertex P) := by
              rw [K.rootedLocalAttachedCosetMap_oldVertex
                C D (P.proper D hDP).subset root x]
      _ = e (L.multiCosetInclude P hadm hgen hret D hDP
            (L.attachedOfSkeletonVertex D x)) :=
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
            C root P hadm hgen hret
            D hDP (L.attachedOfSkeletonVertex D x)).symm
      _ = e z := congrArg e hx
  · rintro ⟨D,hDP,x,hx⟩
    obtain ⟨y,hy⟩ :=
      K.intrinsicComponentLocalHom_vertex_surjective C root x
    refine ⟨D,hDP,y,?_⟩
    apply e.injective
    calc
      e (L.multiCosetInclude P hadm hgen hret D hDP
            (L.attachedOfSkeletonVertex D y)) =
        Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D,hDP⟩,
            K.rootedLocalAttachedCosetMap C D
              (P.proper D hDP).subset root
              (L.attachedOfSkeletonVertex D y)⟩ :
            M.MultiCosetRawVertex P) :=
          K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
            C root P hadm hgen hret D hDP
            (L.attachedOfSkeletonVertex D y)
      _ = Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D,hDP⟩, M.attachedOfSkeletonVertex D (f.onVertex y)⟩ :
            M.MultiCosetRawVertex P) := by
              rw [K.rootedLocalAttachedCosetMap_oldVertex
                C D (P.proper D hDP).subset root y]
      _ = Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D,hDP⟩, M.attachedOfSkeletonVertex D x⟩ :
            M.MultiCosetRawVertex P) := by rw [hy]
      _ = e z := hx

/-- Source-original B-component is OFF the original OLD
skeleton iff there is NO original old quotient vertex
connected to z by a REAL signed B-word. -/
def ArbitraryRankRootedOriginalOffSkeleton
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (z : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)) : Prop :=
  ¬ ∃ (x : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
        C root P hadm hgen hret)),
    K.ArbitraryRankRootedOriginalOldPoint C root P hadm hgen hret x ∧
    ∃ (w : LabelWord ι), LabelWord.Uses B w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).Follows x w z

/-- The corresponding genuine local Γ[C] off-old-skeleton
signed B-component predicate, using ACTUAL local word paths. -/
def ArbitraryRankRootedLocalOffSkeleton
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (z : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) : Prop :=
  ¬ ∃ (x : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
        P hadm hgen hret),
    K.ArbitraryRankRootedLocalOldPoint C root P hadm hgen hret x ∧
    ∃ (w : LabelWord ι), LabelWord.Uses B w ∧
      (K.arbitraryRankRootedLocalCompletedEGraph
        C root P hadm hgen hret).Follows x w z

/-- EXACT preservation AND reflection of the SOURCE off-skeleton
B-component condition, at arbitrary finite rank, across the
real original/local signed multiCE isomorphism. The source
Γ need not be globally retractable.

Together with existing true signed B-path reflection and
whole tagged support minima, this permits later transfer
of the WHOLE Definition-3.22 cluster property to the
original k-retractable ambient stage. -/
theorem arbitraryRankRootedLocalOffSkeleton_iff_original
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (z : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    K.ArbitraryRankRootedLocalOffSkeleton
      C root P hadm hgen hret B z ↔
    K.ArbitraryRankRootedOriginalOffSkeleton
      C root P hadm hgen hret B
        (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
          C root P hadm hgen hret z) := by
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  have hPaths (x y : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
       P hadm hgen hret) (w : LabelWord ι) :
      (K.arbitraryRankRootedLocalCompletedEGraph
        C root P hadm hgen hret).Follows x w y ↔
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).Follows
          (e x) w (e y) :=
    K.arbitraryRankRootedCompletedEGraphHom_follows_iff
      C root P hadm hgen hret x y w
  constructor
  · intro hOff
    rintro ⟨y, hyOld, w, hw, hp⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    apply hOff
    refine ⟨x,
      (K.arbitraryRankRootedLocalOldPoint_iff_original
        C root P hadm hgen hret x).mpr hyOld,
      w, hw, ?_⟩
    exact (hPaths x z w).mpr hp
  · intro hOff
    rintro ⟨x, hxOld, w, hw, hp⟩
    apply hOff
    refine ⟨e x,
      (K.arbitraryRankRootedLocalOldPoint_iff_original
        C root P hadm hgen hret x).mp hxOld,
      w, hw, ?_⟩
    exact (hPaths x z w).mp hp

end CayleySubgraphSpec
end ABO
end PSTSEPPA
