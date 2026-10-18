import PSTSEPPA.ABO.Lemma43OverlapWitnessByRetraction

/-!
# ABO Lemma 4.3: the deleted-word witness belongs to BOTH B-component slices

This file records the exact component-theoretic conclusion
of the source's Figure 7 -> Figure 8 argument on pp.36–37.

Fix a real B-path component Q of the ORIGINAL signed proper
coset extension and a constituent copy vH[C] with its precise
intrinsic old C-component index c. The associated constituent
slice B_i = Q ∩ vH[C] consists of TRUE quotient vertices
which (i) can be reached from Q's base by a realised signed
B-word and (ii) belong to that SAME original tagged C-copy.

If z and t lie in the first slice B_i, and t also lies in
another slice B_j, then in the published Lemma 4.3 proof
there are two genuine z-to-t words: p using B_i's alphabet,
and q using a candidate minimum support alphabet D
contained in BOTH constituent alphabets. The source's
retractable deletion argument now shows that z also belongs
to the second tagged C_j-copy: not just that its ambient
Cayley coordinate happens to belong to the second coset.

We formally derive membership z ∈ B_i ∩ B_j from these
precise hypotheses by the independently verified genuine
old-component-tagged overlap witness (#702). The result
is a direct geometry interface needed to transport the
attainment of minimum supports into actual patch overlaps.

This lemma by itself does NOT claim the necessary D-paths
or minimum supports always exist: the source obtains them
from lower-rank cluster property and the earlier support
and bridge-freeness steps. We preserve those obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Literal source B_i = Q ∩ vH[C] for ONE original intrinsic
tagged completed C-constituent. Membership is witnessed
by an actual realised B-word from anchor and a genuine
C-attachment with EXACT component tag c. Neither
ambient group coordinate equality nor arbitrary
support in another C-component qualifies. -/
def allProperCoset_taggedConstituentSlice
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (c : K.ComponentIndex C) :
    Set (K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :=
  { z |
      (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w z) ∧
      ∃ p : K.AttachedCosetVertex C,
        p.1 = c ∧
        z = K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP p }

/-- Genuine Fig. 7 -> Fig. 8 slice-membership assertion.

Let z,t lie in the SAME tagged C-slice of one B-component,
and let t also lie in another genuinely tagged E-slice.
If actual signed paths z --p--> t and z --q--> t use
B_i⊆C and D⊆C∩E respectively, then retractability
forces a true signed (B_i∩D)-path z-->t and
z already lies in the second tagged E-slice.

All three slice-membership premises and both input paths
are REAL source objects. This is exactly the geometrical
attainment transfer the published proof needs before
minimal supports of B_i and B_j can be identified. -/
theorem allProperCoset_taggedSlice_overlap_from_two_paths
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C E Bsmall D : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hEP : E ∈ (allProperCosetFamily A).alphabets)
    (hSmallC : Bsmall ⊆ C)
    (hDC : D ⊆ C) (hDE : D ⊆ E)
    (anchor z t : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C) (e : K.ComponentIndex E)
    (hz :
      z ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c)
    (htC :
      t ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c)
    (htE :
      t ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor E hEP e)
    (p q : LabelWord ι)
    (hpUses : LabelWord.Uses Bsmall p)
    (hqUses : LabelWord.Uses D q)
    (hp :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z p t)
    (hq :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z q t) :
    z ∈ K.allProperCoset_taggedConstituentSlice
      hadm hgen hret B anchor E hEP e ∧
    ∃ w : LabelWord ι, LabelWord.Uses (Bsmall ∩ D) w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w t := by
  obtain ⟨hzReach, pStartC, hStartTag, hStartC⟩ := hz
  obtain ⟨_htReachC, pEndC, hEndTagC, hEndC⟩ := htC
  obtain ⟨_htReachE, pEndE, hEndTagE, hEndE⟩ := htE
  have hSameC : pStartC.1 = pEndC.1 :=
    hStartTag.trans hEndTagC.symm
  obtain ⟨hNewPath, pStartE, hSameE, hStartE⟩ :=
    K.allProperCoset_retractable_overlap_witness
      hadm hgen hret
      C E Bsmall D hCP hEP
      hSmallC hDC hDE z t
      pStartC pEndC pEndE
      hStartC.symm hEndC.symm hEndE.symm
      hSameC p q hpUses hqUses hp hq
  constructor
  · exact ⟨hzReach, pStartE, hSameE.trans hEndTagE, hStartE⟩
  · exact hNewPath

end CayleySubgraphSpec
end ABO
end PSTSEPPA
