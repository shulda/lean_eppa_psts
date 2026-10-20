import PSTSEPPA.ABO.ForwardInductionRootedTaggedSupportTransport
import PSTSEPPA.ABO.Definition322WholeComponentMinimalSupport

/-!
# ABO Definition 3.22: transport the FULL original component-tagged support PAIR

The previous arbitrary-rank source/local support theorem transported
only the supporting ALPHABET D. The source's whole-component
minimum support is actually a PAIR (D,c), where c is the intrinsic
OLD D-component index of the supporting attached coset copy.
Two different component tags with the same Γ-coordinate must
never be identified.

We now preserve and REFLECT the FULL TAGGED SUPPORT PAIR:
(D,c) supports a LOCAL original/fresh quotient vertex z if and
only if the SOURCE pair (D, F_D(c)) supports its original
rooted component-tagged quotient image, where F_D is the
certified true old-component-index equivalence of the
root-normalized signed H[C] skeleton with the original one.

The forward proof tracks each specific attached D-coset point,
and the backward proof uses the inverse of the genuine dependent
attached-coset equivalence, checking the original component
tag via injectivity of F_D. This is exactly the source-facing
gluing/support geometry needed to carry MINIMUM supports of
whole B-components through locality under k-retractability.
No global ambient Γ retractability, invented old signed edges,
coordinate-tag collapse, new axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Literal ORIGINAL rooted component-tagged support (D,d)
of a genuine original glued multiCE quotient point.
The index d is an intrinsic original old D-component tag,
not merely a coset coordinate in Γ. -/
def ArbitraryRankRootedOriginalTaggedSupportAt
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι)
    (d : (K.subalphabetComponentSubgraph C root).ComponentIndex D)
    (z : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)) : Prop :=
  ∃ (hDP : D ∈ P.alphabets)
    (p : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex D),
    p.1 = d ∧
      Quotient.mk
        (K.arbitraryRankRootedOriginalMultiCosetSetoid
          C root P hadm hgen hret)
        (⟨⟨D,hDP⟩,p⟩ :
          (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) = z

/-- Exact original/local full tagged support naturality at
ARBITRARY rank, for EVERY actual quotient vertex. Transports
both the alphabet D and the TRUE intrinsic old component tag
through the rooted index equivalence, and reflects this data
using surjectivity on entire attached D-coset fibres.

This is substantially stronger than ambient Γ-coset membership
or alphabet-only support naturality, and does not require
global retractability of the source Γ. -/
theorem arbitraryRankRootedLocalTaggedSupport_iff_original
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (D : Finset ι)
    (d : (K.intrinsicComponentLocalSlice C root).ComponentIndex D)
    (z : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    (K.intrinsicComponentLocalSlice C root).HasTaggedSupportAt
      P hadm hgen hret D d z ↔
    K.ArbitraryRankRootedOriginalTaggedSupportAt
      C root P hadm hgen hret
      D (K.rootedLocalComponentIndexEquiv C root D d)
      (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret z) := by
  let L := K.intrinsicComponentLocalSlice C root
  let M := K.subalphabetComponentSubgraph C root
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  let F := K.rootedLocalComponentIndexEquiv C root D
  constructor
  · rintro ⟨hDP, p, hpd, hp⟩
    refine ⟨hDP,
      K.rootedLocalAttachedCosetMap C D
        (P.proper D hDP).subset root p, ?_, ?_⟩
    · change F p.1 = F d
      exact congrArg F hpd
    · calc
        Quotient.mk
            (K.arbitraryRankRootedOriginalMultiCosetSetoid
              C root P hadm hgen hret)
            (⟨⟨D, hDP⟩,
              K.rootedLocalAttachedCosetMap C D
                (P.proper D hDP).subset root p⟩ :
              M.MultiCosetRawVertex P) =
          e (L.multiCosetInclude P hadm hgen hret D hDP p) :=
            (K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
              C root P hadm hgen hret D hDP p).symm
        _ = e z := congrArg e hp
  · rintro ⟨hDP, p, hidx, hp⟩
    let E := K.rootedLocalAttachedCosetEquiv C D
      (P.proper D hDP).subset root
    let q : L.AttachedCosetVertex D := E.symm p
    have hMap :
        K.rootedLocalAttachedCosetMap C D
          (P.proper D hDP).subset root q = p :=
      E.apply_symm_apply p
    have hTag : q.1 = d := by
      apply F.injective
      calc
        F q.1 =
          (K.rootedLocalAttachedCosetMap C D
            (P.proper D hDP).subset root q).1 := rfl
        _ = p.1 :=
          congrArg (fun a : M.AttachedCosetVertex D => a.1) hMap
        _ = F d := hidx
    refine ⟨hDP,q,hTag,?_⟩
    apply e.injective
    calc
      e (L.multiCosetInclude P hadm hgen hret D hDP q) =
        Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D,hDP⟩,
            K.rootedLocalAttachedCosetMap C D
              (P.proper D hDP).subset root q⟩ :
            M.MultiCosetRawVertex P) :=
          K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
            C root P hadm hgen hret D hDP q
      _ = Quotient.mk
          (K.arbitraryRankRootedOriginalMultiCosetSetoid
            C root P hadm hgen hret)
          (⟨⟨D,hDP⟩,p⟩ : M.MultiCosetRawVertex P) := by
            rw [hMap]
      _ = e z := hp

end CayleySubgraphSpec
end ABO
end PSTSEPPA
