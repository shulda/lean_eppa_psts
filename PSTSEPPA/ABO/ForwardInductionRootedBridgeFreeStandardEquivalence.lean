import PSTSEPPA.ABO.ForwardInductionArbitraryRankBridgeProperty
import PSTSEPPA.ABO.ForwardInductionLocalCompletedEGraphAgreement
import PSTSEPPA.ABO.LocalSubgroupCosetNaturality
import PSTSEPPA.ABO.BridgeFreenessInterface

/-!
# ABO 4.5: actual original-rooted versus STANDARD local bridge-freeness

Previously certified original/local rooted signed graph isomorphism
preserves exactly the two source bridge-free clauses, using the
ambient Γ-valued local representation. But the global source
forward induction is stated in terms of the STANDARD locally
retractable H[C] MultiCosetBridgeFree predicate.

We prove the missing equivalence: the original-rooted
Γ bridge-free condition is equivalent to the STANDARD
H[C] signed multiCE bridge-free predicate.

The proof uses the literal subgroup embedding H[C]→Γ for
injectivity, exact coset membership for every proper D⊊C,
and the verified standard-local/source-local signed EGraph
Follows iff. It assumes neither condition as true and
requires no global retractability of original Γ.
No fabricated old signed edges or new axioms/sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Standard local H[C] bridge-free and the genuine local
Γ-valued source-quotient bridge-free interfaces coincide
for all selected proper families and all finite C-ranks. -/
theorem arbitraryRankRootedLocalBridgeProperty_iff_standard
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    K.ArbitraryRankRootedLocalBridgeProperty
      C root P hadm hgen hret ↔
    (K.intrinsicComponentLocalSlice C root).MultiCosetBridgeFree
      P hadm hgen hret := by
  let L := K.intrinsicComponentLocalSlice C root
  constructor
  · rintro ⟨hinj,hpaths⟩
    refine ⟨?_, ?_⟩
    · intro u v huv
      apply hinj
      exact congrArg Subtype.val huv
    · intro D hDC u v hLocalCoset
      have hAmbient :
          ((L.multiCosetAmbientValue P hadm hgen hret v :
              generatedSubgroup gen C) : Γ) ∈
            generatedLeftCoset gen D
              ((L.multiCosetAmbientValue P hadm hgen hret u :
                generatedSubgroup gen C) : Γ) :=
        (mem_localGeneratedLeftCoset_iff_ambient
          gen D C hDC.subset
          (L.multiCosetAmbientValue P hadm hgen hret u)
          (L.multiCosetAmbientValue P hadm hgen hret v)).mp hLocalCoset
      obtain ⟨w, hw, hp⟩ := hpaths D hDC u v hAmbient
      exact ⟨w, hw,
        (K.arbitraryRankRootedLocalCompletedFollows_iff_standard
          C root P hadm hgen hret u v w).mp hp⟩
  · rintro ⟨hinj,hpaths⟩
    refine ⟨?_, ?_⟩
    · intro u v huv
      apply hinj
      apply Subtype.ext
      exact huv
    · intro D hDC u v hAmbient
      have hLocalCoset :
          L.multiCosetAmbientValue P hadm hgen hret v ∈
            generatedLeftCoset (trivialCompletionGenerator gen C) D
              (L.multiCosetAmbientValue P hadm hgen hret u) :=
        (mem_localGeneratedLeftCoset_iff_ambient
          gen D C hDC.subset
          (L.multiCosetAmbientValue P hadm hgen hret u)
          (L.multiCosetAmbientValue P hadm hgen hret v)).mpr hAmbient
      obtain ⟨w, hw, hp⟩ := hpaths D hDC u v hLocalCoset
      exact ⟨w, hw,
        (K.arbitraryRankRootedLocalCompletedFollows_iff_standard
          C root P hadm hgen hret u v w).mpr hp⟩

/-- Two-clause ORIGINAL rooted Γ signed bridge-freeness
is equivalent to bridge-freeness of the actual STANDARD
root-normalized H[C] multiCE. No global retractability of Γ. -/
theorem arbitraryRankRootedOriginalBridgeProperty_iff_standardLocal
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C)) :
    K.ArbitraryRankRootedOriginalBridgeProperty
      C root P hadm hgen hret ↔
    (K.intrinsicComponentLocalSlice C root).MultiCosetBridgeFree
      P hadm hgen hret :=
  (K.arbitraryRankRootedCompletedBridgeProperty_iff
    C root P hadm hgen hret).symm.trans
    (K.arbitraryRankRootedLocalBridgeProperty_iff_standard
      C root P hadm hgen hret)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
