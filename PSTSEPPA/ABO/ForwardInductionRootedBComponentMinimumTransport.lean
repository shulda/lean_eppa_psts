import PSTSEPPA.ABO.ForwardInductionRootedWholeMinimumTransport
import PSTSEPPA.ABO.ForwardInductionRootedWholeComponentImage

/-!
# ABO Definition 3.22: attained tagged support of the WHOLE B-component

The source cluster property requires a uniquely minimum ORIGINAL
old-component-tagged support of the ENTIRE actually signed
B-connected component, not just support of one quotient vertex.

The rooted local/original signed multiCE equivalence preserves
and reflects real B-paths (including positive/inverse old/fresh
edges), maps the entire B-component ONTO the original one,
and preserves and reflects the complete tagged support pair
(D,c) and the minimum of any vertex subset. We combine those
facts without identifying equal ambient Γ coordinates or
assuming globally retractable ambient Γ.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An attained original tagged minimum support (D,c) of
the ENTIRE actual signed B-component of u is equivalent to
the same minimum support of the corresponding ORIGINAL
rooted B-component. The component index is carried by
the genuine root-normalized old component-index equivalence. -/
theorem arbitraryRankRootedBComponent_minimum_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B D : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret)
    (d : (K.intrinsicComponentLocalSlice C root).ComponentIndex D) :
    (K.intrinsicComponentLocalSlice C root).IsMinimalTaggedSupportFor
      P hadm hgen hret
      {v | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.arbitraryRankRootedLocalCompletedEGraph
          C root P hadm hgen hret).Follows u w v}
      D d ↔
    K.ArbitraryRankRootedOriginalMinimalTaggedSupportFor
      C root P hadm hgen hret
      {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.arbitraryRankRootedOriginalCompletedEGraph
          C root P hadm hgen hret).Follows
            (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
              C root P hadm hgen hret u) w y}
      D (K.rootedLocalComponentIndexEquiv C root D d) := by
  rw [← K.arbitraryRankRootedBComponent_image
    C root P hadm hgen hret B u]
  exact K.arbitraryRankRootedLocalMinimalTaggedSupport_iff_original
    C root P hadm hgen hret _ D d

/-- Existence of some attained tagged minimum of the whole B-component
is invariant, using the inverse on genuine OLD component-index tags,
not an inverse on ambient group coordinates. -/
theorem arbitraryRankRootedBComponent_exists_minimum_iff
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    (∃ (D : Finset ι)
      (d : (K.intrinsicComponentLocalSlice C root).ComponentIndex D),
      (K.intrinsicComponentLocalSlice C root).IsMinimalTaggedSupportFor
        P hadm hgen hret
        {v | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.arbitraryRankRootedLocalCompletedEGraph
            C root P hadm hgen hret).Follows u w v}
        D d) ↔
    (∃ (D : Finset ι)
      (d : (K.subalphabetComponentSubgraph C root).ComponentIndex D),
      K.ArbitraryRankRootedOriginalMinimalTaggedSupportFor
        C root P hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.arbitraryRankRootedOriginalCompletedEGraph
            C root P hadm hgen hret).Follows
              (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
                C root P hadm hgen hret u) w y}
        D d) := by
  constructor
  · rintro ⟨D, d, hd⟩
    exact ⟨D, K.rootedLocalComponentIndexEquiv C root D d,
      (K.arbitraryRankRootedBComponent_minimum_iff
        C root P hadm hgen hret B D u d).mp hd⟩
  · rintro ⟨D, d, hd⟩
    let F := K.rootedLocalComponentIndexEquiv C root D
    refine ⟨D, F.symm d, ?_⟩
    apply (K.arbitraryRankRootedBComponent_minimum_iff
      C root P hadm hgen hret B D u (F.symm d)).mpr
    simpa only [Equiv.apply_symm_apply] using hd

end CayleySubgraphSpec
end ABO
end PSTSEPPA
