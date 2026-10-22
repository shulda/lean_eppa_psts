import PSTSEPPA.ABO.ForwardInductionOriginalFullCosetVertexExact
import PSTSEPPA.ABO.ForwardInductionLocalTaggedCosetMembership
import PSTSEPPA.ABO.RootedTaggedAttachedCosetEquiv

/-!
# ABO Theorem 4.5: exact original Γ-coordinate and ORIGINAL TAGGED D-coset shape

The previous source theorem identifies the actual Γ-rooted B-component
with the exact old-component-tagged D-coset using an H[C]-normalized
representative q. Here we remove that LOCAL coordinate from the
mathematical *statement* and obtain the literal original Γ-coset
classification, while KEEPING the intrinsic original D-component
index as a SEPARATE coordinate.

The two sides are:
  * TRUE original old/fresh oriented signed B-word path connectivity;
  * exactly one original tagged D-copy B-coset: q has the same original
    D-component index as the anchor and its actual Γ coordinate is in
    the original generated left B-coset.

Both directions use the bijective component-tagged attached-coset
transport and genuine root-left-translation subgroup membership.
This does not assume globally generated/retractable Γ, identify
distinct old components having equal Γ coordinates, or invent any
old signed edge.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The entire genuine ORIGINAL Γ-rooted signed B-component
from an actual selected D-constituent point equals a SINGLE
ORIGINAL intrinsic D-tagged full left B-coset inside its
ORIGINAL selected D-copy. The iff explicitly uses original
Γ coordinates and original OLD D-component tags, not
generated H[C] coordinates in the conclusion. -/
theorem arbitraryRankRootedOriginalFullBComponent_exactGammaTaggedCoset
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (B : Finset ι) (hBD : B ⊆ D)
    (p : (K.intrinsicComponentLocalSlice C root).AttachedCosetVertex D)
    (y : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).Follows
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root P hadm hgen hret
            ((K.intrinsicComponentLocalSlice C root).multiCosetInclude
              P hadm hgen hret D hDP p)) w y) ↔
    ∃ q : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex D,
      q.1 = (K.rootedLocalAttachedCosetMap
        C D (P.proper D hDP).subset root p).1 ∧
      q.2.1 ∈ generatedLeftCoset gen B
        (K.rootedLocalAttachedCosetMap
          C D (P.proper D hDP).subset root p).2.1 ∧
      y = Quotient.mk
        (K.arbitraryRankRootedOriginalMultiCosetSetoid
          C root P hadm hgen hret)
        (⟨⟨D,hDP⟩,q⟩ :
          (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) := by
  let L := K.intrinsicComponentLocalSlice C root
  let M := K.subalphabetComponentSubgraph C root
  let hDC : D ⊆ C := (P.proper D hDP).subset
  let hBC : B ⊆ C := hBD.trans hDC
  let r := K.rootedLocalAttachedCosetMap C D hDC root
  have hExact :=
    K.arbitraryRankRootedOriginalFullBComponent_exactTaggedVertices
      C root P hadm hgen hret D hDP B hBD p y
  constructor
  · intro hPath
    obtain ⟨v, hSame, hCoset, hV⟩ := hExact.mp hPath
    refine ⟨r v, ?_, ?_, hV⟩
    · exact congrArg (K.rootedLocalComponentIndexEquiv C root D) hSame
    · exact (mem_rootTranslated_localGeneratedLeftCoset_iff
        gen B C hBC root.1 p.2.1 v.2.1).mp hCoset
  · rintro ⟨q, hTag, hCoset, hV⟩
    let F := K.rootedLocalAttachedCosetEquiv C D hDC root
    let v : L.AttachedCosetVertex D := F.symm q
    have hMap : r v = q := F.apply_symm_apply q
    have hSame : v.1 = p.1 := by
      apply (K.rootedLocalComponentIndexEquiv C root D).injective
      calc
        (K.rootedLocalComponentIndexEquiv C root D) v.1 = (r v).1 := rfl
        _ = q.1 := congrArg (fun z : M.AttachedCosetVertex D => z.1) hMap
        _ = (r p).1 := hTag
        _ = (K.rootedLocalComponentIndexEquiv C root D) p.1 := rfl
    have hLocalCoset : v.2.1 ∈ generatedLeftCoset
        (trivialCompletionGenerator gen C) B p.2.1 :=
      (mem_rootTranslated_localGeneratedLeftCoset_iff
        gen B C hBC root.1 p.2.1 v.2.1).mpr (by
          change root.1 * (v.2.1 : Γ) ∈
            generatedLeftCoset gen B (root.1 * (p.2.1 : Γ))
          have hvCoord : (r v).2.1 = root.1 * (v.2.1 : Γ) := rfl
          have hpCoord : (r p).2.1 = root.1 * (p.2.1 : Γ) := rfl
          rw [←hvCoord, hMap, ←hpCoord]
          exact hCoset)
    apply hExact.mpr
    refine ⟨v, hSame, hLocalCoset, ?_⟩
    change y = Quotient.mk
      (K.arbitraryRankRootedOriginalMultiCosetSetoid
        C root P hadm hgen hret)
      (⟨⟨D, hDP⟩, r v⟩ :
        (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P)
    rw [hMap]
    exact hV

end CayleySubgraphSpec
end ABO
end PSTSEPPA
