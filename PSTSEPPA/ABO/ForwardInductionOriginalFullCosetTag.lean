import PSTSEPPA.ABO.ForwardInductionRootedTagPairTransport
import PSTSEPPA.ABO.ForwardInductionLocalCompletedEGraphAgreement
import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents

/-!
# ABO 4.5: a genuine original old-component tag on a full B-coset component

The source Γ-rooted completed coset extension is not obtained by
identifying vertices with equal ambient Γ coordinates: each attached
D-coset retains its ORIGINAL intrinsic old D-component tag.

If B⊆D and an original rooted B-component starts in a selected D-copy,
EVERY vertex of that real signed B-component has support from the
SAME original D-component index. This is stronger than mere local
support over normalized H[C] and is precisely an ingredient needed
for the ORIGINAL (rather than merely locally expressed) full B-coset
alternative of ABO Lemma 4.3 / Theorem 4.5.

The proof uses exact actual signed B-path reflection, the certified
full selected-D-component description INSIDE the local quotient, and
the source-faithful transport of old-component-tagged supporting
pairs. No original old signed edge is invented, and no two original
D-indices are equated because their group coordinates agree.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every original signed B-reachable point from a selected
local D-constituent anchor, B⊆D, belongs to one and the SAME
original old-component-tagged D-copy. The original D-tag is
precisely the image of p.1 through the genuine component-index
equivalence; it is not inferred from any Γ-coordinate equality.

Works for all selected coset families P, all parent ranks C, and
without any ambient-global retractability or generation of Γ. -/
theorem arbitraryRankRootedOriginal_fullBComponent_sameOldDTag
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (B : Finset ι) (hBD : B ⊆ D)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D)
    (y : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret))
    (hy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).Follows
        (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
          C root P hadm hgen hret
          ((K.intrinsicComponentLocalSlice C root).multiCosetInclude
            P hadm hgen hret D hDP p)) w y) :
    K.ArbitraryRankRootedOriginalTaggedSupportAt
      C root P hadm hgen hret D
      (K.rootedLocalComponentIndexEquiv C root D p.1) y := by
  let L := K.intrinsicComponentLocalSlice C root
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  obtain ⟨v, hv⟩ := e.surjective y
  obtain ⟨w, hw, hp⟩ := hy
  have hLocalPath :
      (L.multiCosetEGraph P hadm hgen hret).Follows
        (L.multiCosetInclude P hadm hgen hret D hDP p) w v :=
    (K.arbitraryRankRootedCompletedEGraphHom_follows_iff
      C root P hadm hgen hret
      (L.multiCosetInclude P hadm hgen hret D hDP p) v w).mpr (by
        change (K.arbitraryRankRootedOriginalCompletedEGraph
          C root P hadm hgen hret).Follows
          (e (L.multiCosetInclude P hadm hgen hret D hDP p)) w (e v)
        rw [hv]
        exact hp)
  obtain ⟨q, hIndex, _hBValue, hVertex⟩ :=
    (L.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret D hDP B hBD p v).mp
        ⟨w, hw, hLocalPath⟩
  have hTagged : L.HasTaggedSupportAt P hadm hgen hret
      D p.1 v :=
    ⟨hDP, q, hIndex, hVertex.symm⟩
  have hOriginal :=
    (K.arbitraryRankRootedLocalTaggedSupport_iff_original
      C root P hadm hgen hret D p.1 v).mp hTagged
  rw [hv] at hOriginal
  exact hOriginal

end CayleySubgraphSpec
end ABO
end PSTSEPPA
