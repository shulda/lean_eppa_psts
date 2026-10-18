import PSTSEPPA.ABO.Definition322WholeComponentMinimalSupport

/-!
# ABO Lemma 4.3: synchronize minimum supports once they are attained in an overlap

This is the EXACT SET-THEORETIC conclusion of the source's
Figure 7 -> Figure 8 argument in ABO I Lemma 4.3,
PDF pp.36–37. The harder, preceding geometric argument
uses retractability to prove that the OLD minimum-support
witnesses of two B-component constituent pieces B_i and B_j
actually belong to their SHARED intersection.

We prove the next necessary fact, on the actual ORIGINAL
component-tagged support API of Definition 3.22:

* S and T have attained whole-set minimum tagged supports
  (D_S,c_S) and (D_T,c_T).
* There is an actual vertex in S ∩ T attaining (D_S,c_S).
* There is an actual vertex in S ∩ T attaining (D_T,c_T).

Then BOTH source minima are the SAME minimum pair, including
the intrinsic original skeleton component tag, and their
union inherits that attained minimum.

This is not proved from an arbitrary nonempty intersection
alone. The special attainment assumptions are indispensable:
establishing them by genuine word deletion and source (3.11)/
(3.12) overlap is the actual remaining geometric gate in
the full published Lemma 4.3. No ambient Cayley projection
injectivity, new axioms, or unproved cluster property
enters this formal set-theoretic consequence.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The pair of minimal tagged supports of two constituent
subgraphs agrees EXACTLY when each is known to be
attained at a vertex of their intersection. The
conclusion includes the attained common minimum
on their union, which is the corresponding finite
induction step in source ABO Lemma 4.3.

The preservation of the ORIGINAL component tag is
essential; alphabet equality by itself would be too weak. -/
theorem minimalTaggedSupport_union_of_both_attained_in_intersection
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (S T : Set (K.MultiCosetVertex P hadm hgen hret))
    (D E : Finset ι)
    (c : K.ComponentIndex D)
    (d : K.ComponentIndex E)
    (hS : K.IsMinimalTaggedSupportFor P hadm hgen hret S D c)
    (hT : K.IsMinimalTaggedSupportFor P hadm hgen hret T E d)
    (hAttainedS :
      ∃ z, z ∈ S ∩ T ∧
        K.HasTaggedSupportAt P hadm hgen hret D c z)
    (hAttainedT :
      ∃ z, z ∈ S ∩ T ∧
        K.HasTaggedSupportAt P hadm hgen hret E d z) :
    ∃ (M : Finset ι) (m : K.ComponentIndex M),
      K.IsMinimalTaggedSupportFor P hadm hgen hret S M m ∧
      K.IsMinimalTaggedSupportFor P hadm hgen hret T M m ∧
      K.IsMinimalTaggedSupportFor P hadm hgen hret (S ∪ T) M m := by
  have hSInter :
      K.IsMinimalTaggedSupportFor P hadm hgen hret (S ∩ T) D c := by
    refine ⟨hAttainedS, ?_⟩
    intro F hFP p z hz hpz
    exact hS.2 F hFP p z hz.1 hpz
  have hTInter :
      K.IsMinimalTaggedSupportFor P hadm hgen hret (S ∩ T) E d := by
    refine ⟨hAttainedT, ?_⟩
    intro F hFP p z hz hpz
    exact hT.2 F hFP p z hz.2 hpz
  have hDE : D = E :=
    K.minimalTaggedSupport_alphabet_unique
      P hadm hgen hret (S ∩ T)
      D E c d hSInter hTInter
  subst E
  have hcd : c = d :=
    K.minimalTaggedSupport_tag_unique
      P hadm hgen hret (S ∩ T)
      D c d hSInter hTInter
  subst d
  exact ⟨D, c, hS, hT,
    K.minimalTaggedSupport_union
      P hadm hgen hret S T D c hS hT⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
