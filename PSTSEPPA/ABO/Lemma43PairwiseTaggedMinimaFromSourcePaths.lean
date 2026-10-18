import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion
import PSTSEPPA.ABO.Lemma43OverlapMinimumSynchronization

/-!
# ABO Lemma 4.3 Figures 7–8: pairwise synchronization of whole-slice minima

This is the exact COMPOSITION of the previously certified
source geometry and the tagged minimum-support uniqueness result.

In the published proof let Q be an intrinsic signed
B-component of the original full coset extension.
For two maximal constituent copies with original component
tags c and e, set S=Q∩vH[C], T=Q∩wH[E].
Assume the lower-rank cluster-property induction has
provided attained MINIMUM tagged supports (D1,d1) for S
and (D2,d2) for T. Take their attained witnesses z1∈S
and z2∈T, and a common vertex t∈S∩T, as in Figure 7.

The source provides, for each zi, a B_i-labelled path
zi→t inside the constituent piece and a second path
zi→t using the common lower minimum support alphabet D
with D⊆C∩E. The RETRACTABILITY deletion argument
(Figure 7→8) now proves zi lies in BOTH constituent
slices, and both minimum supports are thus ATTAINED
in S∩T. Our previously certified literal
Definition-3.22 support uniqueness then forces the
minima to agree, including the ORIGINAL component
index, and their union inherits that minimum.

This theorem checks that exact logical argument in Lean.
It does NOT conjure the necessary D-paths out of thin air:
their existence is explicitly listed as an input.
Constructing them using the smaller-rank support
hypotheses and source (3.11)/(3.12)/Lemma 3.21
is the remaining connection in the full Lemma-4.3 proof.
The finite n-piece induction and cluster identification
via Corollary 3.12 are likewise separate.

All graph paths are genuine ORIENTED SIGNED paths in the
original incomplete full multiCE, with exact original
component tags. There is no global Cayley embedding,
new axiom, fake loop, or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Published Lemma 4.3's pairwise Figure-7-to-8 induction
step, with its REAL signed input word paths and original
component-indexed minimum-support witnesses explicit.

If each lower minimum is attained at a witness vertex
that can be reached to a common intersection point both
by a constituent-supported word and by a word on the
common D⊆C∩E core alphabet, RETRACTABILITY forces
both witnesses to belong to S∩T and consequently
the whole minimum tagged supports coincide. -/
theorem allProperCoset_two_tagged_slices_minima_agree_of_source_paths
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C E Bfirst Bsecond D : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hEP : E ∈ (allProperCosetFamily A).alphabets)
    (hFirstC : Bfirst ⊆ C)
    (hSecondE : Bsecond ⊆ E)
    (hDC : D ⊆ C) (hDE : D ⊆ E)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C) (e : K.ComponentIndex E)
    (S T : Set (K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret))
    (hS :
      S = K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c)
    (hT :
      T = K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor E hEP e)
    (M N : Finset ι)
    (m : K.ComponentIndex M) (n : K.ComponentIndex N)
    (hMinS : K.IsMinimalTaggedSupportFor
      (allProperCosetFamily A) hadm hgen hret S M m)
    (hMinT : K.IsMinimalTaggedSupportFor
      (allProperCosetFamily A) hadm hgen hret T N n)
    (z1 z2 t : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hz1 : z1 ∈ S)
    (hz2 : z2 ∈ T)
    (htS : t ∈ S) (htT : t ∈ T)
    (hAt1 :
      K.HasTaggedSupportAt (allProperCosetFamily A)
        hadm hgen hret M m z1)
    (hAt2 :
      K.HasTaggedSupportAt (allProperCosetFamily A)
        hadm hgen hret N n z2)
    (p1 q1 p2 q2 : LabelWord ι)
    (hp1Uses : LabelWord.Uses Bfirst p1)
    (hq1Uses : LabelWord.Uses D q1)
    (hp2Uses : LabelWord.Uses Bsecond p2)
    (hq2Uses : LabelWord.Uses D q2)
    (hp1 :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z1 p1 t)
    (hq1 :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z1 q1 t)
    (hp2 :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z2 p2 t)
    (hq2 :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z2 q2 t) :
    z1 ∈ S ∩ T ∧ z2 ∈ S ∩ T ∧
      ∃ (R : Finset ι) (r : K.ComponentIndex R),
        K.IsMinimalTaggedSupportFor
          (allProperCosetFamily A) hadm hgen hret S R r ∧
        K.IsMinimalTaggedSupportFor
          (allProperCosetFamily A) hadm hgen hret T R r ∧
        K.IsMinimalTaggedSupportFor
          (allProperCosetFamily A) hadm hgen hret (S ∪ T) R r := by
  subst S
  subst T
  obtain ⟨hz1InT, _hNewPath1⟩ :=
    K.allProperCoset_taggedSlice_overlap_from_two_paths
      hadm hgen hret
      B C E Bfirst D hCP hEP
      hFirstC hDC hDE
      anchor z1 t c e
      hz1 htS htT
      p1 q1 hp1Uses hq1Uses hp1 hq1
  obtain ⟨hz2InS, _hNewPath2⟩ :=
    K.allProperCoset_taggedSlice_overlap_from_two_paths
      hadm hgen hret
      B E C Bsecond D hEP hCP
      hSecondE hDE hDC
      anchor z2 t e c
      hz2 htT htS
      p2 q2 hp2Uses hq2Uses hp2 hq2
  have hAttS :
      ∃ z, z ∈
          (K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor C hCP c) ∩
          (K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor E hEP e) ∧
        K.HasTaggedSupportAt (allProperCosetFamily A)
          hadm hgen hret M m z :=
    ⟨z1, ⟨hz1, hz1InT⟩, hAt1⟩
  have hAttT :
      ∃ z, z ∈
          (K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor C hCP c) ∩
          (K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor E hEP e) ∧
        K.HasTaggedSupportAt (allProperCosetFamily A)
          hadm hgen hret N n z :=
    ⟨z2, ⟨hz2InS, hz2⟩, hAt2⟩
  refine ⟨⟨hz1, hz1InT⟩, ⟨hz2InS, hz2⟩, ?_⟩
  exact K.minimalTaggedSupport_union_of_both_attained_in_intersection
    (allProperCosetFamily A)
    hadm hgen hret
    (K.allProperCoset_taggedConstituentSlice
      hadm hgen hret B anchor C hCP c)
    (K.allProperCoset_taggedConstituentSlice
      hadm hgen hret B anchor E hEP e)
    M N m n hMinS hMinT hAttS hAttT

end CayleySubgraphSpec
end ABO
end PSTSEPPA
