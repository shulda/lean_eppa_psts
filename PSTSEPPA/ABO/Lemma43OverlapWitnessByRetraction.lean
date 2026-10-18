import PSTSEPPA.ABO.Lemma43RetractableWordDeletion
import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents
import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.StandardCosetFamily

/-!
# ABO Lemma 4.3 Figure 7->8: word deletion forces a shared tagged constituent

This is the source's NEXT STEP after the retractable word-deletion
lemma, not an independent cluster-property proposal.

Suppose two points z,t of the genuine original signed
component-tagged coset extension lie inside ONE fixed completed
C-constituent (with the SAME original C-component tag), and
t also belongs to a second completed E-constituent. The two
REAL labelled paths z --p--> t and z --q--> t use alphabets
B and D respectively, with B⊆C and D⊆C∩E.

By the published retractability argument, p|D labels an
actual Cayley path with the SAME endpoints, using only B∩D.
Its endpoints occupy the same genuine old C-component tag;
hence completeness of the tagged C-constituent upgrades the
ambient path back to a REAL signed (B∩D)-path inside the
original uncompleted multi-coset extension.

Since B∩D⊆E and t is in the selected E-constituent,
reversing this real path forces z itself into the SAME
component-tagged E-constituent. This is the exact
intersecting-patch witness needed to move from Figure 7
to Figure 8 in the published Lemma 4.3 proof.

The conclusion does NOT use ambient Cayley-coordinate equality
to identify distinct tagged quotient vertices. It does
NOT prove that arbitrary minimum supports of overlapping
pieces are already equal: that subsequent source comparison
uses this new witness, along with attained minimum support
and lower bridge-free/cluster assumptions.

Formal inverses and original missing old edges stay exact.
The deleted word is followed in a COMPLETE Cayley graph;
the new path in the original multiCE is derived from
the independently checked full tagged constituent component theorem.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace LabelWord

/-- If p uses B, then deleting every positive and negative
letter not in D leaves a genuine word supported on B∩D.
This is the extra path-support fact required by ABO
Lemma 4.3, not just the weaker statement that p|D uses D. -/
theorem uses_inter_restrictTo
    (B D : Finset ι) (p : LabelWord ι)
    (hp : Uses B p) :
    Uses (B ∩ D) (restrictTo D p) := by
  induction p with
  | nil =>
      trivial
  | cons s p ih =>
      by_cases hsD : signedBase s ∈ D
      · have hs : signedBase s ∉ (Finset.univ \ D) := by
          simp [hsD]
        change Uses (B ∩ D)
          (if signedBase s ∈ (Finset.univ \ D) then
            deleteGenerators (Finset.univ \ D) p
          else
            s :: deleteGenerators (Finset.univ \ D) p)
        rw [if_neg hs]
        exact ⟨Finset.mem_inter.mpr ⟨hp.1, hsD⟩, ih hp.2⟩
      · have hs : signedBase s ∈ (Finset.univ \ D) := by
          simp [hsD]
        change Uses (B ∩ D)
          (if signedBase s ∈ (Finset.univ \ D) then
            deleteGenerators (Finset.univ \ D) p
          else
            s :: deleteGenerators (Finset.univ \ D) p)
        rw [if_pos hs]
        exact ih hp.2

end LabelWord

variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Source Lemma 4.3, Figure 7->8, in the ACTUAL
old/fresh SIGNED multiCE and with ORIGINAL component tags.

If z and t are in the same full tagged C-constituent,
t also lies in a full tagged E-constituent,
and two genuine z-to-t words use B and D respectively,
then under retractability the starting vertex z lies
in the SAME tagged E-constituent as t.

More precisely, deletion of the B-word outside D yields
a real signed (B∩D)-path INSIDE the original multiCE,
and reversing it proves the E-constituent claim.

The B- and D-word paths, the C/ E presentations, and
their original component-index equality are all TRUE
source objects; no global ambient CE embedding is assumed. -/
theorem allProperCoset_retractable_overlap_witness
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C E B D : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hEP : E ∈ (allProperCosetFamily A).alphabets)
    (hBC : B ⊆ C) (hDC : D ⊆ C) (hDE : D ⊆ E)
    (z t : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (pStartC pEndC : K.AttachedCosetVertex C)
    (pEndE : K.AttachedCosetVertex E)
    (hStartC :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP pStartC = z)
    (hEndC :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP pEndC = t)
    (hEndE :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret E hEP pEndE = t)
    (hSameC : pStartC.1 = pEndC.1)
    (p q : LabelWord ι)
    (hpUsesB : LabelWord.Uses B p)
    (hqUsesD : LabelWord.Uses D q)
    (hpPath :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z p t)
    (hqPath :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z q t) :
    (∃ w : LabelWord ι, LabelWord.Uses (B ∩ D) w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w t) ∧
    ∃ pStartE : K.AttachedCosetVertex E,
      pStartE.1 = pEndE.1 ∧
      z = K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret E hEP pStartE := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let F := K.multiCosetAmbientHom P hadm hgen hret
  let w : LabelWord ι := LabelWord.restrictTo D p
  have hwBD : LabelWord.Uses (B ∩ D) w :=
    LabelWord.uses_inter_restrictTo B D p hpUsesB
  have hpMapped :
      (cayleyGraph gen).toEGraph.Follows
        (F.onVertex z) p (F.onVertex t) :=
    hpPath.map F
  have hqMapped :
      (cayleyGraph gen).toEGraph.Follows
        (F.onVertex z) q (F.onVertex t) :=
    hqPath.map F
  have hMappedRestricted :
      (cayleyGraph gen).toEGraph.Follows
        (F.onVertex z) w (F.onVertex t) :=
    (cayley_restricted_path_of_two_paths
      gen hret D (F.onVertex z) (F.onVertex t)
      p q hpMapped hqMapped hqUsesD).2
  have hEndpoint :
      (cayleyGraph gen).followWord (F.onVertex z) w =
        F.onVertex t :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord (F.onVertex z) w)
      hMappedRestricted
  have hStartValue : F.onVertex z = pStartC.2.1 := by
    change K.multiCosetAmbientValue P hadm hgen hret z = _
    rw [← hStartC]
    rfl
  have hEndValue : F.onVertex t = pEndC.2.1 := by
    change K.multiCosetAmbientValue P hadm hgen hret t = _
    rw [← hEndC]
    rfl
  have hCoset :
      pEndC.2.1 ∈
        generatedLeftCoset gen (B ∩ D) pStartC.2.1 := by
    apply (mem_generatedLeftCoset_iff_subalphabetReachable
      gen (B ∩ D) pStartC.2.1 pEndC.2.1).mpr
    refine ⟨w, hwBD, ?_⟩
    simpa only [hStartValue, hEndValue] using hEndpoint
  have hBDC : B ∩ D ⊆ C :=
    Finset.inter_subset_right.trans hDC
  have hBDE : B ∩ D ⊆ E :=
    Finset.inter_subset_right.trans hDE
  have hCPath :
      ∃ u : LabelWord ι, LabelWord.Uses (B ∩ D) u ∧
        G.Follows
          (K.multiCosetInclude P hadm hgen hret C hCP pStartC)
          u t :=
    (K.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret C hCP (B ∩ D) hBDC pStartC t).mpr
      ⟨pEndC, hSameC.symm, hCoset, hEndC.symm⟩
  obtain ⟨u, hu, hPathC⟩ := hCPath
  have hPath : G.Follows z u t := by
    rw [hStartC] at hPathC
    exact hPathC
  have hReverse : G.Follows
      (K.multiCosetInclude P hadm hgen hret E hEP pEndE)
      (PSTS.SignedWord.inv u) z := by
    rw [hEndE]
    exact G.follows_inverse hPath
  obtain ⟨pStartE, hIdxE, hStartE⟩ :=
    (K.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret E hEP (B ∩ D) hBDE pEndE z).mp
      ⟨PSTS.SignedWord.inv u, hu.inv, hReverse⟩
  exact ⟨⟨u, hu, hPath⟩, pStartE, hIdxE, hStartE⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
