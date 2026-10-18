import PSTSEPPA.ABO.Lemma43IntersectingTaggedSlicesMinimaAgree
import PSTSEPPA.ABO.Lemma43TaggedSliceBInterCPaths
import PSTSEPPA.ABO.Lemma43MinimumSupportActualPaths
import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion

/-!
# ABO Lemma 4.3: propagate a SAME minimum-support witness through overlapping slices

The full Figure 7->8 proof in the published ABO I Lemma 4.3
does not merely assert equality of minimum supports of
overlapping maximal constituents. It transports each
previously selected vertex attaining that minimum into the
NEXT constituent, so eventually the *same* witness is
present in their total intersection (PDF p.37).

The already accepted pairwise theorem proves equality of
minima for intersecting constituent slices WITHOUT any extra
path assumptions. Here we strengthen it to transport an
ARBITRARILY CHOSEN old-component-tagged minimum-support
witness z in one slice into the adjacent slice.

The proof uses ONLY previously verified source facts:
* genuine component-tagged (3.11) intersection support of
  any vertex t in the two original slices;
* real (B∩C)-word connectivity of each slice;
* a real (C∩E)-word path from a chosen minimum witness z to t
  given by the minimum's exact old component index;
* retractable Figure 7->8 deletion to show z ACTUALLY belongs
  to the other old-component-tagged constituent, not just
  its ambient Cayley group coset;
* pairwise uniqueness of the minimum in the overlap.

This precise witness-propagation interface is designed for
the subsequent FINITE CONNECTED constituent family induction
in the source proof. The source has an extra hypothesis
that H[A] is locally retractable. Our existing generic
interface uses Retractable gen for ambient Γ, and the
localization to the paper's H[A] remains a distinct obligation.
No global source retractability is asserted as a fact.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Figure 8, strong witness propagation:
If the two TRUE original component-tagged slices S_C,S_E
of one B-component have nonempty overlap, S_C has
attained minimum (M,m), and S_E has *some* attained
minimum from the lower-rank induction, then EVERY
vertex z attaining (M,m) in S_C also lies in S_E.
Moreover S_E has exactly the SAME minimum (M,m).

Unlike a merely set-theoretic overlap argument, z's
membership in S_E comes from the ACTUAL signed paths,
source (3.11), and retractable letter deletion. -/
theorem allProperCoset_minimum_witness_propagates_to_adjacent_slice
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C E : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hEP : E ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C) (e : K.ComponentIndex E)
    (M : Finset ι) (m : K.ComponentIndex M)
    (hMinC :
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        (K.allProperCoset_taggedConstituentSlice
          hadm hgen hret B anchor C hCP c) M m)
    (hMinE :
      ∃ (N : Finset ι) (n : K.ComponentIndex N),
        K.IsMinimalTaggedSupportFor
          (allProperCosetFamily A) hadm hgen hret
          (K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor E hEP e) N n)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hzC :
      z ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c)
    (hzMin :
      K.HasTaggedSupportAt (allProperCosetFamily A)
        hadm hgen hret M m z)
    (t : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (htC :
      t ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c)
    (htE :
      t ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor E hEP e) :
    z ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor E hEP e ∧
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        (K.allProperCoset_taggedConstituentSlice
          hadm hgen hret B anchor E hEP e) M m := by
  let P := allProperCosetFamily A
  let S := K.allProperCoset_taggedConstituentSlice
    hadm hgen hret B anchor C hCP c
  let T := K.allProperCoset_taggedConstituentSlice
    hadm hgen hret B anchor E hEP e
  obtain ⟨pCt, _hCtIdx, hCt⟩ := htC.2
  obtain ⟨pEt, _hEtIdx, hEt⟩ := htE.2
  have hDP : (C ∩ E) ∈ P.alphabets :=
    allProperCosetFamily_inter_mem A C E hCP hEP
  obtain ⟨pD, hpDt, _hpDC, _hpDE⟩ :=
    K.multiCosetVertex_two_supports_intersection
      P hadm hgen hret t C E hCP hEP hDP
      pCt pEt hCt.symm hEt.symm
  have htD : K.HasTaggedSupportAt
      P hadm hgen hret (C ∩ E) pD.1 t :=
    ⟨hDP, pD, rfl, hpDt⟩
  obtain ⟨p, hpUses, hp⟩ :=
    K.allProperCoset_taggedSlice_B_inter_C_connected
      hadm hgen hret B C hCP anchor c z t hzC htC
  obtain ⟨q, hqUses, hq⟩ :=
    K.minimalTaggedSupport_real_path_to_supported_vertex
      P hadm hgen hret S M m hMinC
      z hzC hzMin (C ∩ E) pD.1 t htC htD
  have hzE :
      z ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor E hEP e :=
    (K.allProperCoset_taggedSlice_overlap_from_two_paths
      hadm hgen hret B C E (B ∩ C) (C ∩ E)
      hCP hEP Finset.inter_subset_right
      Finset.inter_subset_left Finset.inter_subset_right
      anchor z t c e hzC htC htE
      p q hpUses hqUses hp hq).1
  obtain ⟨N, n, hMinN⟩ := hMinE
  obtain ⟨R, r, hMinR_C, hMinR_E, _hMinRUnion⟩ :=
    K.allProperCoset_intersecting_tagged_slices_minima_agree
      hadm hgen hret B C E hCP hEP
      anchor c e M N m n hMinC hMinN t htC htE
  have hEqAlphabet : M = R :=
    K.minimalTaggedSupport_alphabet_unique
      P hadm hgen hret S M R m r hMinC hMinR_C
  subst R
  have hEqTag : m = r :=
    K.minimalTaggedSupport_tag_unique
      P hadm hgen hret S M m r hMinC hMinR_C
  subst r
  exact ⟨hzE, hMinR_E⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
