import PSTSEPPA.ABO.ForwardInductionOriginalFullSignedAlternative
import PSTSEPPA.ABO.ForwardInductionOriginalGammaProperShape
import PSTSEPPA.ABO.ForwardInductionIntrinsicOriginalActiveCoatoms

/-!
# ABO Theorem 4.5: complete ORIGINAL Γ-rooted signed k-local forward package

This is the collected ORIGINAL Γ-facing finite k-retractable
forward theorem, rather than the theorem for the normalized
globally retractable H[C] local stage.

Let K be an admissible INCOMPLETE Γ-Cayley skeleton, C⊆A with
|C|≤k, and assume only the source actual lower H[C] rooted
bridge-free hypotheses. For EVERY original Γ-rooted signed
off-skeleton B-component of the actual selected multi-coset
extension of the original rooted C-component:

(A) the ENTIRE actual signed B-component has one attained
    MINIMUM original old-component-tagged support (M,m);
(B) one ORIGINAL quotient core lies in that TRUE signed
    B-component, ATTAINS (M,m), and has genuine ORIGINAL
    intrinsic component-tagged support on every active coatom;
(C) either (FULL) the whole original B-component is exactly
    a tagged original Γ-left B-coset in one selected D-copy,
    all its actual oriented signed B-edges are freshly
    completed D-edges with the SAME intrinsic old D-component
    index, and EVERY positive/negative B-step really exists;
    or (PROPER) the whole ORIGINAL signed B-component is
    genuinely isomorphic on BOTH vertices and actual oriented
    signed edge tokens to the CANONICAL proper B-cluster
    in Γ LEFT-TRANSLATED by the ORIGINAL old root and exact
    core group-coordinate.

The real ORIGINAL active coatom finite set is already proved
equal to its transported local counterpart. There is NO global
generation/retractability assumption on Γ, no extra lower
cluster-property premise, no invented original old edges and
NO identification of distinct intrinsic old component indices
from equal ambient Γ-coordinates.

This is the k-local forward *cluster-geometry* theorem. The
source's upward / embeddedness Theorem 4.7, reflecting group
ABO §5, and unconditional PSTS EPPA remain separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Canonical full ORIGINAL Γ-rooted k-local signed forward
Theorem 4.5: attained whole-B-component old D-tagged minimum,
one original signed reachable common core supported at all
genuine original active coatom tags, and a literal full
component-tagged Γ-left B-coset OR canonical translated
PROPER Γ-B-cluster graph isomorphism, both complete on
genuine directed signed edge tokens.

All hypotheses are actual original source admissibility,
finite k-retractability of Γ, bounded selected rank |C|≤k
and lower *rooted bridge-freeness* in the normalized H[C].
No lower cluster assumption, globally retractable Γ or
ambient coordinate-based tag collapse is used. -/
theorem sourceKLocal_originalCanonicalExactSignedWholeClusterProperty
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
    K.HasExactOriginalRootedSignedTaggedCommonCore
      C root
      (K.sourceInductionLocalAdmissibility hadm C hCA root)
      (isGenerated_trivialCompletionGenerator gen C)
      (retractable_trivialCompletionGenerator_of_kRetractable
        gen k hk C hCk)
      B u ∧
    (K.HasOriginalRootedFullSignedBCosetAlternative
       C root
       (K.sourceInductionLocalAdmissibility hadm C hCA root)
       (isGenerated_trivialCompletionGenerator gen C)
       (retractable_trivialCompletionGenerator_of_kRetractable
         gen k hk C hCk)
       B u ∨
     K.ArbitraryRankRootedOriginalCanonicalGammaProperSignedAlternative
       C root
       (K.sourceInductionLocalAdmissibility hadm C hCA root)
       (isGenerated_trivialCompletionGenerator gen C)
       (retractable_trivialCompletionGenerator_of_kRetractable
         gen k hk C hCk)
       B u) := by
  let L := K.intrinsicComponentLocalSlice C root
  let hadmL := K.sourceInductionLocalAdmissibility hadm C hCA root
  let hgenL := isGenerated_trivialCompletionGenerator gen C
  let hretL := retractable_trivialCompletionGenerator_of_kRetractable
    gen k hk C hCk
  have hCore :
      K.HasOriginalRootedSignedTaggedCommonCore
        C root hadmL hgenL hretL B u :=
    K.sourceKLocal_originalOffSkeleton_hasTaggedCommonCore
      hadm k hk C hCA hCk hcard root hBridge B hBP u hOff
  have hOriginalCore :
      K.HasExactOriginalRootedSignedTaggedCommonCore
        C root hadmL hgenL hretL B u :=
    K.exactOriginalRootedSignedTaggedCommonCore_of_localTagged
      C root hadmL hgenL hretL B u hCore
  have hShape :=
    K.sourceKLocal_originalSignedFullOrCanonicalGammaProper
      hadm k hk C hCA hCk hcard root hBridge B hBP u hOff
  refine ⟨hOriginalCore, ?_⟩
  rcases hShape with hFull | hProper
  · exact Or.inl
      (K.originalRootedFullSignedBCoset_of_localFull
        C root hadmL hgenL hretL B u hFull)
  · exact Or.inr hProper

end CayleySubgraphSpec
end ABO
end PSTSEPPA
