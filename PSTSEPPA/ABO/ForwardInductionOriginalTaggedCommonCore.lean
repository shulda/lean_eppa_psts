import PSTSEPPA.ABO.SourceCanonicalSignedForwardClusterProperty
import PSTSEPPA.ABO.ForwardInductionOriginalRootedMinimum
import PSTSEPPA.ABO.ForwardInductionRootedTagPairTransport
import PSTSEPPA.ABO.Lemma43FiniteTaggedCoatomIndex

/-!
# ABO Theorem 4.5: ORIGINAL Γ-rooted signed common core and all ORIGINAL coatom tags

The globally retractable local H[C] cluster induction already
constructs a genuine signed B-reachable core attaining the WHOLE
component's minimal tagged support and lying in every active
component-tagged coatom slice. The printed source Γ stage need
only be k-retractable, not globally retractable.

This module transports ALL of these data into the actual
ORIGINAL Γ-rooted signed old/fresh quotient, with the original
intrinsic component-index equivalent on every tag:
* minimum (M,m) attained for the ENTIRE original signed B-component;
* an ORIGINAL quotient core vertex reached by a REAL signed B-word;
* actual ORIGINAL tagged support (M,m) of that very core;
* for EACH local active tagged coatom t, actual ORIGINAL core
  support on the corresponding original intrinsic t-alphabet
  and translated old connected-component tag.

The latter is deliberately quantified over the genuine local
active source coatom family. This exposes the full ORIGINAL
support information without pretending the original group Γ
is globally generated/retractable, or treating a tag as just
an ambient Γ coordinate. It is the common-core transport gate
toward the final source k-local Theorem 4.5 assembly.

No missing old signed edges are completed; no axioms or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- ORIGINAL Γ-rooted exact signed cluster common-core clause:
one original old-tagged minimum of the entire B-component,
attained at one ACTUAL original signed B-reachable core point,
simultaneously supported on the original counterparts of
EVERY active tagged local coatom. All indices are intrinsic
old-component quotient indices, not Γ coordinate cosets. -/
def HasOriginalRootedSignedTaggedCommonCore
    (C : Finset ι) (root : K.Vertex)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      (allProperCosetFamily C) hadm hgen hret) : Prop :=
  ∃ (M : Finset ι)
    (m : (K.subalphabetComponentSubgraph C root).ComponentIndex M)
    (core : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root (allProperCosetFamily C) hadm hgen hret)),
    K.ArbitraryRankRootedOriginalMinimalTaggedSupportFor
      C root (allProperCosetFamily C) hadm hgen hret
      {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.arbitraryRankRootedOriginalCompletedEGraph
          C root (allProperCosetFamily C) hadm hgen hret).Follows
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root (allProperCosetFamily C) hadm hgen hret u) w y}
      M m ∧
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root (allProperCosetFamily C) hadm hgen hret).Follows
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root (allProperCosetFamily C) hadm hgen hret u) w core) ∧
    K.ArbitraryRankRootedOriginalTaggedSupportAt
      C root (allProperCosetFamily C) hadm hgen hret M m core ∧
    ∀ t : (K.intrinsicComponentLocalSlice C root).ProperCosetTag,
      t ∈ (K.intrinsicComponentLocalSlice C root).activeTaggedCoatoms
        hadm hgen hret B u →
        K.ArbitraryRankRootedOriginalTaggedSupportAt
          C root (allProperCosetFamily C) hadm hgen hret
          ((K.intrinsicComponentLocalSlice C root).properCosetTagAlphabet t)
          (K.rootedLocalComponentIndexEquiv C root
            ((K.intrinsicComponentLocalSlice C root).properCosetTagAlphabet t)
            ((K.intrinsicComponentLocalSlice C root).properCosetTagIndex t))
          core

/-- Under finite merely k-retractable ORIGINAL Γ, admissibility
of its true old signed skeleton and the actual normalized
H[C] lower rooted bridge-free conditions, EVERY
original off-skeleton B-component has a genuine ORIGINAL
coatom-tagged support-attaining common core with attained
minimum of the ENTIRE original signed B-component.

No additional lower cluster-property hypotheses and no
global retractability of Γ are assumed. -/
theorem sourceKLocal_originalOffSkeleton_hasTaggedCommonCore
    (hadm : K.AdmissibleForCosetExtension)
    (k : ℕ) (hk : KRetractable gen k)
    (C : Finset ι) (hCA : C ⊆ A) (hCk : C.card ≤ k)
    (hcard : 2 ≤ C.card)
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
        gen k hk C hCk) B
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root (allProperCosetFamily C)
        (K.sourceInductionLocalAdmissibility hadm C hCA root)
        (isGenerated_trivialCompletionGenerator gen C)
        (retractable_trivialCompletionGenerator_of_kRetractable
          gen k hk C hCk) u)) :
    K.HasOriginalRootedSignedTaggedCommonCore
      C root
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk) B u := by
  let L := K.intrinsicComponentLocalSlice C root
  let P := allProperCosetFamily C
  let hadmL := K.sourceInductionLocalAdmissibility hadm C hCA root
  let hgenL := isGenerated_trivialCompletionGenerator gen C
  let hretL := retractable_trivialCompletionGenerator_of_kRetractable
    gen k hk C hCk
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadmL hgenL hretL
  have hStdOff :=
    K.originalRootedOffSkeleton_implies_standardLocalOffSkeleton
      C root hadmL hgenL hretL B hBP u hOff
  have hCanonical :
      L.HasCanonicalExactSignedWholeClusterProperty hadmL hgenL hretL :=
    L.canonicalExactSignedWholeClusterProperty_of_lowerBridgeFree
      hadmL hgenL hretL hcard hBridge
  obtain ⟨M, m, hMin, _hShape, coreLocal, hReach, hTag, hAll⟩ :=
    hCanonical B hBP u hStdOff
  refine ⟨M, K.rootedLocalComponentIndexEquiv C root M m,
    e coreLocal, ?_, ?_, ?_, ?_⟩
  · have hMinLocal :
        L.IsMinimalTaggedSupportFor P hadmL hgenL hretL
          {v | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.arbitraryRankRootedLocalCompletedEGraph
              C root P hadmL hgenL hretL).Follows u w v}
          M m := by
      change L.IsMinimalTaggedSupportFor P hadmL hgenL hretL
        {v | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (L.multiCosetEGraph P hadmL hgenL hretL).Follows u w v} M m
      exact hMin
    exact (K.arbitraryRankRootedBComponent_minimum_iff
      C root P hadmL hgenL hretL B M u m).mp hMinLocal
  · obtain ⟨w, hw, hp⟩ := hReach
    refine ⟨w, hw, ?_⟩
    have hLocal :
        (K.arbitraryRankRootedLocalCompletedEGraph
          C root P hadmL hgenL hretL).Follows u w coreLocal :=
      (K.arbitraryRankRootedLocalCompletedFollows_iff_standard
        C root P hadmL hgenL hretL u coreLocal w).mpr hp
    exact (K.arbitraryRankRootedCompletedEGraphHom_follows_iff
      C root P hadmL hgenL hretL u coreLocal w).mp hLocal
  · exact (K.arbitraryRankRootedLocalTaggedSupport_iff_original
      C root P hadmL hgenL hretL M m coreLocal).mp hTag
  · intro t ht
    obtain ⟨_hCoatomReach, q, hTagIndex, hCoreEq⟩ := hAll t ht
    let E := L.properCosetTagAlphabet t
    let hEP : E ∈ P.alphabets := L.properCosetTagAlphabet_mem t
    have hCoreLocalTag :
        L.HasTaggedSupportAt P hadmL hgenL hretL
          E (L.properCosetTagIndex t) coreLocal :=
      ⟨hEP, q, hTagIndex, hCoreEq.symm⟩
    exact (K.arbitraryRankRootedLocalTaggedSupport_iff_original
      C root P hadmL hgenL hretL E
      (L.properCosetTagIndex t) coreLocal).mp hCoreLocalTag

end CayleySubgraphSpec
end ABO
end PSTSEPPA
