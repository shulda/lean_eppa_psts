import PSTSEPPA.ABO.Lemma43NoLowerSingleCoatomSignedEdge
import PSTSEPPA.ABO.Lemma43SingleCoatomNoLowerMinimum
import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso

/-!
# ABO Lemma 4.3: a one-coatom/no-lower B-component has only C-edges

The accepted pointwise signed-edge rigidity theorem shows
that, when a vertex has no support smaller than a selected
maximal C-constituent supporting it, EVERY REAL signed
edge leaving that vertex actually lies in the SAME
old-component-tagged C-copy.

Apply this to ALL vertices of one true B-component Q
which is wholly contained in that original tagged C-copy
and has NO smaller-than-C supporting point.
Then the ENTIRE actual oriented signed B-edge set of Q
has a genuine presentation in the selected C-constituent,
with its source carrying the precise original old C-tag.
Moreover its signed label belongs to B∩C.

This is the stronger E-graph-level half of the source's
one-constituent/no-smaller-support case (ABO I,
Lemma 4.3, PDF pp.35–36). Its vertex half follows from
the certified selected-C exact B-component slice theorem.

The conclusion is a statement about the true original
edge QUOTIENT, including distinct formal inverses of
geometric loops and without adding any missing old edges.
It does NOT infer the edge property merely from ambient
B- and C-coset membership.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every TRUE signed B-edge of an original B-component
contained in ONE coatom tagged C-copy, and with no
strictly smaller source support anywhere in Q, is an
actual original completed C-edge. Its genuine signed
label belongs to B∩C, and its source attached point
has the specified original C-component index.

This holds WITHOUT global ambient group-coordinate
injectivity, cluster property, or fictitious old edges. -/
theorem allProperCoset_single_coatom_no_lower_all_signed_B_edges
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 2 ≤ A.card)
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
            (allProperCosetFamily A) hadm hgen hret D y)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (he :
      e ∈ (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).BComponentEdgeSet B anchor) :
    ∃ (p : K.AttachedCosetVertex C)
      (s : {s : SignedLabel ι // signedBase s ∈ C}),
      p.1 = c ∧
      e = K.multiCosetEdgeInclude (allProperCosetFamily A)
        hadm hgen hret C hCP (Sum.inr (p, s)) ∧
      signedBase s.1 ∈ B ∩ C := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨heB, hReach⟩ := he
  obtain ⟨pC, hpCTag, hSrc⟩ :=
    hContained (G.source e) hReach
  obtain ⟨s, hEdge⟩ :=
    K.allProperCoset_coatom_edge_from_no_lower_source
      hadm hgen hret hAcard C hCP hCcard pC e
      hSrc.symm (fun D hDC =>
        hNoLower (G.source e) hReach D hDC)
  have hLabel : G.label e = s.1 := by
    rw [hEdge]
    rfl
  have hsB : signedBase s.1 ∈ B := by
    rw [hLabel] at heB
    exact heB
  exact ⟨pC, s, hpCTag, hEdge,
    Finset.mem_inter.mpr ⟨hsB, s.2⟩⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
