import PSTSEPPA.ABO.Lemma43SingleCoatomNoLowerMinimum
import PSTSEPPA.ABO.Lemma43FiniteActiveCoatomCover
import PSTSEPPA.ABO.Lemma43ActualTranslatedLowerClusterSignedGraphIso

/-!
# ABO Lemma 4.3: an attained coatom minimum gives one genuine cluster core

In the PUBLISHED source's one-constituent/no-smaller-support case,
the whole true signed B-component Q has an attained minimum support
(C,c), where C is an original maximal proper alphabet and c its
intrinsic OLD skeleton C-component tag.

The accepted finite coatom cluster-image theorem needs two things:

1. ONE ACTUAL quotient core vertex belonging to EVERY selected
   original component-tagged coatom constituent slice meeting Q;
2. every selected constituent's B∩E alphabet is a proper
   subalphabet of B, so their union is a genuine ClusterSpec B.

Both follow directly from the WHOLE-COMPONENT minimum support,
without any new group-theoretic argument.

For (1), take a true point core attaining the minimum (M,m).
Every active E-coatom slice contains some true vertex y∈Q with
genuine E-attachment pE. Minimum support implies M⊆E and
the exact original component-index equality after enlargement.
Enlarging core's M-attachment to E thus puts THE SAME actual
quotient vertex core in that precise original E-tagged slice,
not just in the same ambient Cayley coset.

For (2), if the minimum alphabet C is maximal proper, every
active coatom E contains C by minimality and hence E=C.
If B⊄C, then B∩E is strictly smaller than B for every E.

These are the exact remaining source bridge hypotheses for the
already certified translated proper B-cluster signed graph
isomorphism theorem. The extra printed full-B-coset alternative
B⊆C is deliberately not inferred from this proper-cluster case.

All original old component tags, oriented signed tokens and
missing old-edge information remain intact. No new axioms/sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An attained minimum tagged support of the ENTIRE genuine
B-component automatically supplies ONE ACTUAL quotient vertex
belonging to EVERY active coatom constituent slice.

No coatom/maximality hypothesis on M is required.
The crucial component-index equality is part of the accepted
Definition-3.22 whole-component minimum support, not a
consequence of ambient group-coordinate equality. -/
theorem allProperCoset_minimum_attainer_in_all_active_coatoms
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B M : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (m : K.ComponentIndex M)
    (hMinimum :
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        M m) :
    ∃ core : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret,
      (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w core) ∧
      K.HasTaggedSupportAt (allProperCosetFamily A)
        hadm hgen hret M m core ∧
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        core ∈ K.properCosetTagSlice
          hadm hgen hret B anchor t := by
  let P := allProperCosetFamily A
  obtain ⟨core, hCoreReach, ⟨hMP, pM, hpMidx, hpMcore⟩⟩ :=
    hMinimum.1
  refine ⟨core, hCoreReach, ⟨hMP, pM, hpMidx, hpMcore⟩, ?_⟩
  intro t ht
  obtain ⟨_hCard, ⟨y, hySlice⟩⟩ :=
    (K.mem_activeTaggedCoatoms_iff
      hadm hgen hret B anchor t).mp ht
  obtain ⟨hyReach, pE, hpEidx, hyE⟩ := hySlice
  let E := K.properCosetTagAlphabet t
  let hEP : E ∈ P.alphabets := K.properCosetTagAlphabet_mem t
  obtain ⟨hME, hMapTag⟩ :=
    hMinimum.2 E hEP pE y hyReach hyE.symm
  let pCoreE : K.AttachedCosetVertex E :=
    K.attachedSubalphabetMap M E hME pM
  have hCoreTag :
      pCoreE.1 = K.properCosetTagIndex t := by
    calc
      pCoreE.1 = K.componentIndexMap M E hME pM.1 := rfl
      _ = K.componentIndexMap M E hME m :=
        congrArg (K.componentIndexMap M E hME) hpMidx
      _ = pE.1 := hMapTag
      _ = K.properCosetTagIndex t := hpEidx
  have hCoreInclude :
      K.multiCosetInclude P hadm hgen hret E hEP pCoreE =
        core := by
    calc
      K.multiCosetInclude P hadm hgen hret E hEP pCoreE =
        K.multiCosetInclude P hadm hgen hret M hMP pM :=
          (K.multiCosetInclude_alphabet_mono
            P hadm hgen hret M E hME hMP hEP pM).symm
      _ = core := hpMcore
  exact ⟨hCoreReach, pCoreE, hCoreTag, hCoreInclude.symm⟩

/-- If the ENTIRE signed B-component has a minimum support
on an original maximal proper coatom C, then EVERY active
tagged coatom has alphabet exactly C.

Thus if B⊄C, every B∩E used by the accepted translated
cluster construction is PROPER in B. No assertion that
distinct original old component tags can be identified
from their ambient Cayley group coordinates is used. -/
theorem allProperCoset_coatom_minimum_all_active_pieces_proper
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCcard : C.card + 1 = A.card)
    (hBnotC : ¬ B ⊆ C)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (hMinimum :
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y}
        C c) :
    ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
      B ∩ K.properCosetTagAlphabet t ⊂ B := by
  let P := allProperCosetFamily A
  have hStrict : B ∩ C ⊂ B := by
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro hBC
    apply hBnotC
    intro i hi
    exact (Finset.mem_inter.mp (hBC hi)).2
  intro t ht
  obtain ⟨_hCard, ⟨y, hySlice⟩⟩ :=
    (K.mem_activeTaggedCoatoms_iff
      hadm hgen hret B anchor t).mp ht
  obtain ⟨hyReach, pE, _hpEidx, hyE⟩ := hySlice
  let E := K.properCosetTagAlphabet t
  let hEP : E ∈ P.alphabets := K.properCosetTagAlphabet_mem t
  obtain ⟨hCE, _hTagEq⟩ :=
    hMinimum.2 E hEP pE y hyReach hyE.symm
  have hEeqC : E = C :=
    allProperCoset_coatom_maximal A C hCcard E hEP hCE
  change B ∩ E ⊂ B
  rw [hEeqC]
  exact hStrict

/-- Source one-coatom/no-lower-support cluster-core interface.

If a genuine signed B-component Q lies in ONE tagged
maximal completed C-constituent and no Q-vertex has
support smaller than C, then the already accepted
single-coatom minimum theorem produces a REAL common
quotient core in all selected active coatom slices.

When B⊄C, all active lower pieces are proper in B,
exactly as required by the translated proper B-cluster
graph-isomorphism theorem. This does not cover B⊆C,
which is the distinct FULL B-COSET alternative. -/
theorem allProperCoset_one_coatom_no_lower_common_core
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
    (hBnotC : ¬ B ⊆ C)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (hContained :
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) →
        ∃ pC : K.AttachedCosetVertex C,
          pC.1 = c ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP pC)
    (hNoLower :
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) →
        ∀ (D : Finset ι), D ⊂ C →
          ¬ K.MultiCosetVertexSupported
            (allProperCosetFamily A) hadm hgen hret D y) :
    ∃ core : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret,
      (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w core) ∧
      (∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        core ∈ K.properCosetTagSlice hadm hgen hret B anchor t) ∧
      (∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B) := by
  have hMin :=
    K.allProperCoset_single_coatom_no_lower_minimal_support
      hadm hgen hret B C hCP hCcard
      anchor c hContained hNoLower
  obtain ⟨core, hReach, _hSupported, hAll⟩ :=
    K.allProperCoset_minimum_attainer_in_all_active_coatoms
      hadm hgen hret B C anchor c hMin
  have hProper :=
    K.allProperCoset_coatom_minimum_all_active_pieces_proper
      hadm hgen hret B C hCcard hBnotC anchor c hMin
  exact ⟨core, hReach, hAll, hProper⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
