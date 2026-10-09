import PSTSEPPA.ABO.CoatomConstituentCover
import PSTSEPPA.ABO.MultiCosetComponentSupportDichotomy

/-!
# The no-large-support test only needs the coatom alphabets

The full-constituent/strictly-lower-patch dichotomy previously
required checking whether a vertex has support by *any*
selected proper C⊊A containing B. The coatom cover theorem
shows that such a support exists iff one exists at a coatom
C of codimension one containing B.

This reduces the universal test from all proper subalphabets
to the maximal-rank cosets used explicitly in the proof of
ABO Lemma 4.3. The reduction is TAG-EXACT: extension of a
supporting C-point to a coatom preserves the same global
quotient vertex, not just its Cayley-group coordinate.

As a consequence the strict-lower B-edge patch cover of an
entire off-skeleton component can be invoked under only
a no-coatom-support condition at its chosen root vertex.
This does not yet produce a common core or cluster property.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- For a vertex z and subalphabet B, there is no selected
support C⊇B iff there is no coatom support C⊇B.
The test only quantifies over |A| possible maximal alphabets
rather than the entire proper-subalphabet family. -/
theorem allProperCosetVertex_no_superset_support_iff_no_coatom
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    (∀ (C : Finset ι)
       (hCP : C ∈ (allProperCosetFamily A).alphabets),
       B ⊆ C →
       ¬ K.MultiCosetVertexSupported (allProperCosetFamily A)
           hadm hgen hret C z) ↔
    (∀ (C : Finset ι)
       (hCP : C ∈ (allProperCosetFamily A).alphabets),
       C.card + 1 = A.card →
       B ⊆ C →
       ¬ K.MultiCosetVertexSupported (allProperCosetFamily A)
           hadm hgen hret C z) := by
  constructor
  · intro hAll C hCP _hcard hBC
    exact hAll C hCP hBC
  · intro hCo C hCP hBC hs
    obtain ⟨hCP', p, hp⟩ := hs
    obtain ⟨D, hDP, hCD, hcard, hInclude⟩ :=
      K.allProperCoset_constituent_extend_to_coatom
        hadm hgen hret C hCP' p
    have hsD :
        K.MultiCosetVertexSupported
          (allProperCosetFamily A) hadm hgen hret D z :=
      ⟨hDP, K.attachedSubalphabetMap C D hCD p,
        hInclude.trans hp⟩
    exact hCo D hDP hcard (hBC.trans hCD) hsD

/-- On the no-full-constituent side of the component dichotomy,
a check against the maximal proper alphabets alone suffices
to force EVERY actual B-labelled edge of the B-component to
lie in a genuine completed patch with strictly smaller alphabet
C∩B⊊B. The no-large condition is required at only one vertex. -/
theorem allProperCoset_B_component_no_coatom_strict_lower_edge_patches
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hNoCo :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        C.card + 1 = A.card →
        B ⊆ C →
        ¬ K.MultiCosetVertexSupported
          (allProperCosetFamily A) hadm hgen hret C z)
    (y : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hzy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w y)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (heSource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e = y)
    (heB :
      signedBase
        ((K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).label e) ∈ B) :
    ∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex C)
      (s : {s : SignedLabel ι // signedBase s ∈ C}),
      (C ∩ B) ⊂ B ∧
      signedBase s.1 ∈ C ∩ B ∧
      e = K.multiCosetEdgeInclude
        (allProperCosetFamily A) hadm hgen hret
        C hCP (Sum.inr (p, s)) := by
  have hNoLarge :=
    (K.allProperCosetVertex_no_superset_support_iff_no_coatom
      hadm hgen hret B z).mpr hNoCo
  exact K.allProperCoset_B_component_pointwise_no_large_strict_patches
    hadm hgen hret B hBP z hNoLarge
    y hzy e heSource heB

end CayleySubgraphSpec
end ABO
end PSTSEPPA
