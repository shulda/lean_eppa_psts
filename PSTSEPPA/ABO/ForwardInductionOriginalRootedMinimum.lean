import PSTSEPPA.ABO.ForwardInductionKLocalCluster
import PSTSEPPA.ABO.ForwardInductionRootedOffSkeletonMinimumTransport
import PSTSEPPA.ABO.ForwardInductionLocalCompletedEGraphAgreement

/-!
# ABO Theorem 4.5: the original signed off-skeleton support clause under k-retractability

The already certified forward induction proves the signed whole-component
cluster property inside the genuinely generated, retractable subgroup H[C].
The exact original/local signed quotient equivalence preserves off-skeleton
status and attained minimal ORIGINAL component tags.

This module makes the remaining logical interface explicit: a source
off-skeleton component really satisfies the STANDARD local cluster theorem's
off-skeleton premise. The standard premise picks one selected proper alphabet
for the embedded old skeleton; the original rooted predicate quantifies
instead over every genuine old attached-summand representative. We prove the
implication using the actual old vertex image and REAL signed B-paths.

Consequently the original rooted Γ-quotient has an attained minimal (D,d)
support of its ENTIRE signed B-component, assuming only the genuine lower
local bridge-free premises, for merely k-retractable Γ. The correct original
component index is obtained via the certified rooted index equivalence.
No claim about the signed full/proper cluster SHAPE is hidden in this theorem.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If the genuine original rooted Γ quotient B-component misses the
old skeleton, then the corresponding STANDARD H[C] component satisfies
the exact off-skeleton premise used by the proved source cluster
induction. This uses real signed paths rather than Cayley word-values. -/
theorem originalRootedOffSkeleton_implies_standardLocalOffSkeleton
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily C).alphabets)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret)
    (hOff : K.ArbitraryRankRootedOriginalOffSkeleton
      C root (allProperCosetFamily C) hadm hgen hret B
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root (allProperCosetFamily C) hadm hgen hret u)) :
    ¬ ∃ (x : (K.intrinsicComponentLocalSlice C root).Vertex)
      (w : LabelWord ι),
      LabelWord.Uses B w ∧
      ((K.intrinsicComponentLocalSlice C root).multiCosetEGraph
        (allProperCosetFamily C) hadm hgen hret).Follows
        (((K.intrinsicComponentLocalSlice C root).skeletonToMultiCosetHom
          (allProperCosetFamily C) hadm hgen hret B hBP).onVertex x)
        w u := by
  let L := K.intrinsicComponentLocalSlice C root
  let P := allProperCosetFamily C
  have hLocalOff : K.ArbitraryRankRootedLocalOffSkeleton
      C root P hadm hgen hret B u :=
    (K.arbitraryRankRootedLocalOffSkeleton_iff_original
      C root P hadm hgen hret B u).mpr hOff
  rintro ⟨x, w, hw, hPath⟩
  apply hLocalOff
  refine ⟨(L.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x,
    ?_, w, hw, ?_⟩
  · exact ⟨B, hBP, x, rfl⟩
  · exact (K.arbitraryRankRootedLocalCompletedFollows_iff_standard
      C root P hadm hgen hret _ _ w).mpr hPath

/-- ORIGINAL Γ-valued source off-skeleton whole-B-component minimum,
provided that the standard normalized H[C] signed cluster property
has been certified. The minimum retains its ORIGINAL old-component
index, not just the ambient Γ group coordinate. -/
theorem originalRootedOffSkeleton_existsMinimum_of_localCluster
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (hCluster :
      (K.intrinsicComponentLocalSlice C root).HasExactSignedWholeComponentClusterProperty
        hadm hgen hret)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily C).alphabets)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret)
    (hOff : K.ArbitraryRankRootedOriginalOffSkeleton
      C root (allProperCosetFamily C) hadm hgen hret B
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root (allProperCosetFamily C) hadm hgen hret u)) :
    ∃ (D : Finset ι)
      (d : (K.subalphabetComponentSubgraph C root).ComponentIndex D),
      K.ArbitraryRankRootedOriginalMinimalTaggedSupportFor
        C root (allProperCosetFamily C) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.arbitraryRankRootedOriginalCompletedEGraph
            C root (allProperCosetFamily C) hadm hgen hret).Follows
              (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
                C root (allProperCosetFamily C) hadm hgen hret u) w y}
        D d := by
  let L := K.intrinsicComponentLocalSlice C root
  let P := allProperCosetFamily C
  have hStdOff :=
    K.originalRootedOffSkeleton_implies_standardLocalOffSkeleton
      C root hadm hgen hret B hBP u hOff
  obtain ⟨D, d, hMin, _hShape, _hCore⟩ := hCluster B hBP u hStdOff
  have hMinSource : L.IsMinimalTaggedSupportFor P hadm hgen hret
      {v | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.arbitraryRankRootedLocalCompletedEGraph
          C root P hadm hgen hret).Follows u w v} D d := by
    change L.IsMinimalTaggedSupportFor P hadm hgen hret
      {v | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (L.multiCosetEGraph P hadm hgen hret).Follows u w v} D d
    exact hMin
  exact ⟨D, K.rootedLocalComponentIndexEquiv C root D d,
    (K.arbitraryRankRootedBComponent_minimum_iff
      C root P hadm hgen hret B D u d).mp hMinSource⟩

/-- Original-rooted Γ signed support part of forward ABO Theorem 4.5:
for FINITE merely k-retractable Γ, the actual original B-component
outside the old skeleton has an ATTAINED minimal original (D,d)
tag, from precisely the standard lower rooted bridge-free premises
of its local H[C] parent stage. No globally retractable Γ is assumed. -/
theorem sourceKLocal_originalOffSkeletonBComponent_hasMinimum
    (hadm : K.AdmissibleForCosetExtension)
    (k : ℕ) (hk : KRetractable gen k)
    (C : Finset ι) (hCA : C ⊆ A) (hCk : C.card ≤ k)
    (root : K.Vertex)
    (hBridge :
      (K.intrinsicComponentLocalSlice C root).HasAllLowerRootedBridgeFree
        (K.sourceInductionLocalAdmissibility hadm C hCA root)
        (isGenerated_trivialCompletionGenerator gen C)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen k hk C hCk))
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily C).alphabets)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk))
    (hOff : K.ArbitraryRankRootedOriginalOffSkeleton
      C root (allProperCosetFamily C)
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk)
      B
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root (allProperCosetFamily C)
        (K.sourceInductionLocalAdmissibility hadm C hCA root)
        (isGenerated_trivialCompletionGenerator gen C)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen k hk C hCk) u)) :
    ∃ (D : Finset ι)
      (d : (K.subalphabetComponentSubgraph C root).ComponentIndex D),
      K.ArbitraryRankRootedOriginalMinimalTaggedSupportFor
        C root (allProperCosetFamily C)
        (K.sourceInductionLocalAdmissibility hadm C hCA root)
        (isGenerated_trivialCompletionGenerator gen C)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen k hk C hCk)
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.arbitraryRankRootedOriginalCompletedEGraph
            C root (allProperCosetFamily C)
            (K.sourceInductionLocalAdmissibility hadm C hCA root)
            (isGenerated_trivialCompletionGenerator gen C)
            (retractable_trivialCompletionGenerator_of_kRetractable
              gen k hk C hCk)).Follows
              (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
                C root (allProperCosetFamily C)
                (K.sourceInductionLocalAdmissibility hadm C hCA root)
                (isGenerated_trivialCompletionGenerator gen C)
                (retractable_trivialCompletionGenerator_of_kRetractable
                  gen k hk C hCk) u) w y}
        D d := by
  exact K.originalRootedOffSkeleton_existsMinimum_of_localCluster
    C root
    (K.sourceInductionLocalAdmissibility hadm C hCA root)
    (isGenerated_trivialCompletionGenerator gen C)
    (retractable_trivialCompletionGenerator_of_kRetractable
      gen k hk C hCk)
    (K.sourceKLocal_forwardExactSignedClusterProperty
      hadm k hk C hCA hCk root hBridge)
    B hBP u hOff

end CayleySubgraphSpec
end ABO
end PSTSEPPA
