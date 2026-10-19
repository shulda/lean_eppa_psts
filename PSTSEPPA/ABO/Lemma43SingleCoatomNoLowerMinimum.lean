import PSTSEPPA.ABO.Definition322WholeComponentMinimalSupport
import PSTSEPPA.ABO.MaximalProperAlphabets
import PSTSEPPA.ABO.MultiCosetVertexSupport
import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso

/-!
# ABO Lemma 4.3: one coatom and no smaller support

The PUBLISHED proof of ABO I, Lemma 4.3 (PDF pp.35–36)
first separates the case where the actual signed B-component
Q is contained in a single original completed maximal
C-constituent and no point of Q has support on a
strictly smaller alphabet D ⊊ C.

The paper then states that Q has minimum support (C,c),
where c is the ORIGINAL skeleton C-component indexing
that constituent. This is not merely a claim about a
minimal alphabet: every other support of EVERY point of Q
has to refine the same original C-component index.

The present source-facing theorem proves exactly this
using genuine tagged coset gluing:

* a TRUE vertex of Q has a specific original C-tag;
* any other E-support of that same point intersects
  it in an actual (C ∩ E)-support (source (3.11));
* by hypothesis no point of Q has a smaller-than-C
  supporting alphabet, so C ⊆ E;
* since C is a maximal proper alphabet of A, E=C;
* injectivity inside the ORIGINAL completed C-copy
  forces equality of the intrinsic C-component indices.

The unique minimum (C,c) is ACTUALLY attained by
the anchor of Q. Every signed B-path, inverse token
and missing old edge is retained in the original
uncompleted multi-coset extension.

No lower-rank cluster induction, global ambient Cayley
injectivity, extra axiom or sorry is used here. This
is the one-constituent/no-lower-support branch
complementary to the already certified multi-constituent
signed-cluster theorem.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- SOURCE Lemma 4.3, the maximal-C / no-lower-support case.

If a TRUE B-component of the ORIGINAL signed multiCE
is contained in ONE specified original C-component-tagged
coatom and NO vertex of that B-component has a
genuine D⊊C supporting coset, then the entire component
has the unique attained Definition-3.22 minimum
support (C,c).

This conclusion compares every tagged support of every
vertex, even supports at incomparable alphabets E.
Those are eliminated using the actual C∩E quotient
support and maximality of the coatom C. -/
theorem allProperCoset_single_coatom_no_lower_minimal_support
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
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
    K.IsMinimalTaggedSupportFor
      (allProperCosetFamily A) hadm hgen hret
      {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows anchor w y} C c := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  have hAnchor :
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        G.Follows anchor w anchor :=
    ⟨[], LabelWord.uses_nil B, EGraph.Follows.nil anchor⟩
  obtain ⟨pAnchor, hpAnchorTag, hpAnchor⟩ :=
    hContained anchor hAnchor
  constructor
  · exact ⟨anchor, hAnchor, hCP, pAnchor,
      hpAnchorTag, hpAnchor.symm⟩
  · intro E hEP q y hy hEy
    obtain ⟨pC, hpCTag, hyC⟩ := hContained y hy
    have hSuppC : K.MultiCosetVertexSupported
        P hadm hgen hret C y :=
      ⟨hCP, pC, hyC.symm⟩
    have hSuppE : K.MultiCosetVertexSupported
        P hadm hgen hret E y :=
      ⟨hEP, q, hEy⟩
    have hSuppInter :
        K.MultiCosetVertexSupported
          P hadm hgen hret (C ∩ E) y :=
      K.allProperCosetVertex_support_inter
        hadm hgen hret y C E hSuppC hSuppE
    have hCE : C ⊆ E := by
      by_contra hNotCE
      have hStrict : C ∩ E ⊂ C := by
        refine ⟨Finset.inter_subset_left, ?_⟩
        intro hCI
        apply hNotCE
        intro i hi
        exact (Finset.mem_inter.mp (hCI hi)).2
      exact hNoLower y hy (C ∩ E) hStrict hSuppInter
    have hEC : E = C :=
      (allProperCoset_coatom_maximal A C hCcard E hEP hCE).symm
    subst E
    have hEqC : pC = q :=
      K.multiCosetInclude_injective
        P hadm hgen hret C hCP
        (hyC.symm.trans hEy.symm)
    refine ⟨subset_rfl, ?_⟩
    calc
      K.componentIndexMap C C (subset_rfl) c = c :=
        K.componentIndexMap_self C c
      _ = pC.1 := hpCTag.symm
      _ = q.1 := congrArg Sigma.fst hEqC

end CayleySubgraphSpec
end ABO
end PSTSEPPA
