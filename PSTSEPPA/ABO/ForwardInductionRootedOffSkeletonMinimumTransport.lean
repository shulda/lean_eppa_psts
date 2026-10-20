import PSTSEPPA.ABO.ForwardInductionRootedBComponentMinimumTransport
import PSTSEPPA.ABO.ForwardInductionRootedOffSkeletonTransport

/-!
# ABO Definition 3.22: entire OFF-SKELETON B-component minimum

The printed cluster-property support clause is not just an
unconditional B-component minimum: it requires an attained
old-component-tagged minimum precisely for B-components
DISJOINT from the original old skeleton.

At every rank C, for genuine original incomplete signed Γ-Cayley
components, we already have exact equivalences of:
  * membership in the OLD skeleton on the complete tagged quotient;
  * off-skeleton status of an entire B-word component;
  * the whole signed B-component as an IMAGE under the true
    local/original quotient equivalence;
  * existence of an attained minimum tagged support (D,c) of
    that WHOLE B-component.

This theorem combines those into the source EXACT
Definition-3.22 support clause: every local off-skeleton
B-component has a minimum iff the corresponding original
off-skeleton B-component does, transporting the TRUE old
component tags rather than ambient Γ-coordinates.

The original Γ need not be globally retractable. The
independent signed full-coset / proper-B-cluster SHAPE
alternative must still be transported before concluding
the full source Definition-3.22 cluster property for
merely k-retractable ambient Γ.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- EXACT original/local off-skeleton B-component minimum-support
clause of the source Definition 3.22, at ANY finite alphabet
rank and for ANY selected proper coset family.

The minimum is attained on the entire TRUE signed B-component,
including both off-skeleton full B-cosets and proper B-clusters;
it retains its original old D-component INDEX in Γ. -/
theorem arbitraryRankRootedOffSkeletonBComponentMinimum_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    (K.ArbitraryRankRootedLocalOffSkeleton
      C root P hadm hgen hret B u →
      ∃ (D : Finset ι)
        (d : (K.intrinsicComponentLocalSlice C root).ComponentIndex D),
        (K.intrinsicComponentLocalSlice C root).IsMinimalTaggedSupportFor
          P hadm hgen hret
          {v | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.arbitraryRankRootedLocalCompletedEGraph
              C root P hadm hgen hret).Follows u w v}
          D d) ↔
    (K.ArbitraryRankRootedOriginalOffSkeleton
      C root P hadm hgen hret B
        (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
          C root P hadm hgen hret u) →
      ∃ (D : Finset ι)
        (d : (K.subalphabetComponentSubgraph C root).ComponentIndex D),
        K.ArbitraryRankRootedOriginalMinimalTaggedSupportFor
          C root P hadm hgen hret
          {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.arbitraryRankRootedOriginalCompletedEGraph
              C root P hadm hgen hret).Follows
                (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
                  C root P hadm hgen hret u) w y}
          D d) := by
  have hOff :=
    K.arbitraryRankRootedLocalOffSkeleton_iff_original
      C root P hadm hgen hret B u
  have hMin :=
    K.arbitraryRankRootedBComponent_exists_minimum_iff
      C root P hadm hgen hret B u
  constructor
  · intro hLocal hOrigOff
    exact hMin.mp (hLocal (hOff.mpr hOrigOff))
  · intro hOriginal hLocalOff
    exact hMin.mpr (hOriginal (hOff.mp hLocalOff))

end CayleySubgraphSpec
end ABO
end PSTSEPPA
