import PSTSEPPA.ABO.Lemma43TaggedSliceBInterCPaths
import PSTSEPPA.ABO.Lemma43MinimumSupportActualPaths
import PSTSEPPA.ABO.Lemma43PairwiseTaggedMinimaFromSourcePaths
import PSTSEPPA.ABO.MultiCosetVertexSupport

/-!
# ABO Lemma 4.3: unconditional pairwise overlap alignment FROM lower-rank minima

This is the actual mathematical composition of the already verified
source-faithful building blocks for the Figure 7 -> 8 step of the
published ABO I Lemma 4.3.

Let Q be a TRUE intrinsic signed B-path component of the original
uncompleted component-tagged full proper-coset extension CE(K;P_A).
For selected completed C and E constituents with original OLD
component tags c and e, let S=Q∩vH[C], T=Q∩wH[E].

Assume, exactly as in the LOWER-RANK induction of Lemma 4.3,
that S and T already each have an attained whole-set
minimum original-component-tagged support. Suppose S∩T
is NONEMPTY, witnessed by a genuine quotient vertex t.

We now prove that the two minima agree and their union has the
same attained minimum -- with NO EXTRA hypotheses that paths
to t already exist. All required signed paths are constructed:

(1) t has actual C and E constituent presentations.
    The source (3.11) exact tagged quotient intersection
    produces a genuine D=C∩E support for t.
(2) Each minimum is attained at an actual witness z_i∈S/T.
    The already certified true tagged-slice intersection
    theorem produces a REAL (B∩C)/(B∩E) word path z_i→t.
(3) Minimum tagged support of S/T, together with the
    genuine D-supported point t, gives a REAL signed
    D-path z_i→t by full D-coset connectivity. This is
    the previously checked source minimum-support path lemma.
(4) The certified Figure 7->8 word deletion and true
    constituent overlap theorem moves BOTH minimum witnesses
    into S∩T; the certified Definition-3.22 uniqueness
    gives one minimum for S, T and S∪T.

This is substantially stronger than the previously conditional
lemma that took four arbitrary paths as hypotheses. It is
still an INDUCTION STEP, not the whole Lemma 4.3:
existence of the minima for the lower pieces, treatment of
the full-coset alternative, finite-constituent connected
cover and final cluster identification remain separate.

Scope warning: this general CayleySubgraphSpec interface
currently requires Retractable gen on the AMBIENT Γ.
The printed Lemma 4.3 assumes retractability of H[A]
and uses local H[A_i] accordingly; instantiation in that
exact local group still needs the correct localization
step. We do not silently assume global H retractability.
No fake old edges or new axioms are introduced.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Genuine pairwise Fig.7-to-8 minimum support agreement:

IF two actual intrinsic component-tagged constituent slices
of one B-component overlap, and the previously proven
lower-rank induction gives each its attained minimum
tagged support, THEN both minima agree and their union
has an attained minimum. All source paths and overlap
attainment witnesses are DERIVED, not assumed.

The strong original D-component tag is preserved. -/
theorem allProperCoset_intersecting_tagged_slices_minima_agree
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C E : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hEP : E ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C) (e : K.ComponentIndex E)
    (M N : Finset ι)
    (m : K.ComponentIndex M) (n : K.ComponentIndex N)
    (hMinC :
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        (K.allProperCoset_taggedConstituentSlice
          hadm hgen hret B anchor C hCP c) M m)
    (hMinE :
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        (K.allProperCoset_taggedConstituentSlice
          hadm hgen hret B anchor E hEP e) N n)
    (t : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (htC :
      t ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c)
    (htE :
      t ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor E hEP e) :
    ∃ (R : Finset ι) (r : K.ComponentIndex R),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        (K.allProperCoset_taggedConstituentSlice
          hadm hgen hret B anchor C hCP c) R r ∧
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        (K.allProperCoset_taggedConstituentSlice
          hadm hgen hret B anchor E hEP e) R r ∧
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        ((K.allProperCoset_taggedConstituentSlice
          hadm hgen hret B anchor C hCP c) ∪
         (K.allProperCoset_taggedConstituentSlice
          hadm hgen hret B anchor E hEP e)) R r := by
  let P := allProperCosetFamily A
  let S := K.allProperCoset_taggedConstituentSlice
    hadm hgen hret B anchor C hCP c
  let T := K.allProperCoset_taggedConstituentSlice
    hadm hgen hret B anchor E hEP e
  obtain ⟨z1, hz1S, hSupp1⟩ := hMinC.1
  obtain ⟨z2, hz2T, hSupp2⟩ := hMinE.1
  obtain ⟨pCt, _hCtTag, hCt⟩ := htC.2
  obtain ⟨pEt, _hEtTag, hEt⟩ := htE.2
  have hDP : (C ∩ E) ∈ P.alphabets :=
    allProperCosetFamily_inter_mem A C E hCP hEP
  obtain ⟨pD, hpDt, _hpDC, _hpDE⟩ :=
    K.multiCosetVertex_two_supports_intersection
      P hadm hgen hret t
      C E hCP hEP hDP
      pCt pEt hCt.symm hEt.symm
  have hSuppD :
      K.HasTaggedSupportAt P hadm hgen hret
        (C ∩ E) pD.1 t :=
    ⟨hDP, pD, rfl, hpDt⟩
  obtain ⟨p1, hp1B, hp1⟩ :=
    K.allProperCoset_taggedSlice_B_inter_C_connected
      hadm hgen hret B C hCP
      anchor c z1 t hz1S htC
  obtain ⟨p2, hp2B, hp2⟩ :=
    K.allProperCoset_taggedSlice_B_inter_C_connected
      hadm hgen hret B E hEP
      anchor e z2 t hz2T htE
  obtain ⟨q1, hq1D, hq1⟩ :=
    K.minimalTaggedSupport_real_path_to_supported_vertex
      P hadm hgen hret
      S M m hMinC z1 hz1S hSupp1
      (C ∩ E) pD.1 t htC hSuppD
  obtain ⟨q2, hq2D, hq2⟩ :=
    K.minimalTaggedSupport_real_path_to_supported_vertex
      P hadm hgen hret
      T N n hMinE z2 hz2T hSupp2
      (C ∩ E) pD.1 t htE hSuppD
  obtain ⟨_, _, R, r, hRS, hRT, hRUnion⟩ :=
    K.allProperCoset_two_tagged_slices_minima_agree_of_source_paths
      hadm hgen hret
      B C E (B ∩ C) (B ∩ E) (C ∩ E)
      hCP hEP
      Finset.inter_subset_right Finset.inter_subset_right
      Finset.inter_subset_left Finset.inter_subset_right
      anchor c e S T rfl rfl
      M N m n hMinC hMinE z1 z2 t
      hz1S hz2T htC htE
      hSupp1 hSupp2
      p1 q1 p2 q2 hp1B hq1D hp2B hq2D
      hp1 hq1 hp2 hq2
  exact ⟨R, r, hRS, hRT, hRUnion⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
