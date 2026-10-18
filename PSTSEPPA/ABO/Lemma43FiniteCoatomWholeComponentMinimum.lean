import PSTSEPPA.ABO.Lemma43FiniteActiveCoatomCover
import PSTSEPPA.ABO.Lemma43FiniteConnectedTaggedCommonCore

/-!
# ABO Lemma 4.3: one attained tagged minimum for the ENTIRE B-component

This is the exact FINITE-COATOM-ASSEMBLY conclusion of
the PUBLISHED proof of ABO I Lemma 4.3 (PDF pp.35–38),
under its still explicit LOWER-RANK cluster-property
induction hypothesis.

Assume the source's group Γ is FINITE and |A|>=2.
Fix any TRUE intrinsic B-path component Q of the
original, uncompleted, component-tagged full coset
extension, specified by its original quotient anchor z.

The previous certified source steps give:
- finitely many actual tagged coatom constituent
  identities (C,c), retaining intrinsic OLD C-tags;
- a finite family I consisting of exactly those
  selected coatom copies intersecting Q;
- a TRUE vertex- and oriented signed-edge cover of
  Q by the corresponding actual constituent slices;
- connectedness of their literal intersection graph.

Assume, just as in the lower-rank step of Lemma 4.3,
that each NONEMPTY selected coatom slice S_i has an
attained minimum tagged support. By the certified
finite connected-family common-core induction, one
genuine quotient vertex u belongs to ALL selected
coatom slices and carries one support pair (M,m) that
is minimum for their entire union. By the exact
vertex cover, this union is LITERALLY Q, not just a
subset of an ambient Cayley coset.

The theorem below therefore proves the WHOLE-COMPONENT
MINIMUM-SUPPORT clause of the ABO cluster property,
subject solely to those EXPLICIT lower-rank minima
hypotheses and the global Retractable gen interface.
It does NOT yet identify Q as a B-cluster in the
source's separate Corollary-3.12 sense, handle the
full-B-coset alternative, derive the lower minima,
or replace local H[A] retractability by global H
retractability. Those are the remaining published
induction gates, not new mathematical conjectures.

No new axioms, sorry, fabricated old signed edges,
or untagged Cayley coset identification occur.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Source Lemma-4.3 whole-component minimum-support conclusion.

Finite Γ, |A|>=2, source admissibility, generation and
retractability, and an attained lower-rank minimum support
for EACH selected coatom constituent slice meeting the
chosen TRUE signed B-component are the ONLY premises.

The result constructs an original component-tagged minimum
(M,m) ATTAINED at one genuine vertex u, which belongs
to EVERY active coatom slice, and is a MINIMUM support
of the ENTIRE intrinsic signed B-component Q. -/
theorem allProperCoset_B_component_minimum_from_finite_coatoms
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hEachMinimum :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        ∃ (M : Finset ι) (m : K.ComponentIndex M),
          K.IsMinimalTaggedSupportFor
            (allProperCosetFamily A) hadm hgen hret
            (K.properCosetTagSlice
              hadm hgen hret B anchor t) M m) :
    ∃ (M : Finset ι) (m : K.ComponentIndex M)
      (u : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret),
      K.HasTaggedSupportAt (allProperCosetFamily A)
        hadm hgen hret M m u ∧
      (∀ t ∈ K.activeTaggedCoatoms
          hadm hgen hret B anchor,
        u ∈ K.properCosetTagSlice
          hadm hgen hret B anchor t) ∧
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        { y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y }
        M m := by
  classical
  let I := K.activeTaggedCoatoms hadm hgen hret B anchor
  let S := K.properCosetTagSlice hadm hgen hret B anchor
  let G := K.multiCosetEGraph
    (allProperCosetFamily A) hadm hgen hret
  obtain ⟨root, hRoot, hConnected⟩ :=
    K.activeTaggedCoatoms_intersection_graph_connected
      hadm hgen hret hcard B anchor
  have hMin :
      ∀ t ∈ I, ∃ (M : Finset ι) (m : K.ComponentIndex M),
        K.IsMinimalTaggedSupportFor
          (allProperCosetFamily A) hadm hgen hret
          (S t) M m :=
    hEachMinimum
  obtain ⟨M, m, u, hSupport, hForAll, hUnion⟩ :=
    K.allProperCoset_connected_tagged_family_common_minimum
      hadm hgen hret B anchor
      K.properCosetTagAlphabet
      (fun t => K.properCosetTagAlphabet_mem t)
      K.properCosetTagIndex
      I root hRoot hConnected hMin
  have hQ :
      { y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret |
          ∃ t ∈ I, y ∈ S t } =
      { y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        G.Follows anchor w y } := by
    ext y
    constructor
    · rintro ⟨t, ht, hy⟩
      exact hy.1
    · intro hReach
      exact K.activeTaggedCoatoms_vertex_cover
        hadm hgen hret B anchor y hReach
  refine ⟨M, m, u, hSupport, ?_, ?_⟩
  · intro t ht
    exact (hForAll t ht).1
  · rw [← hQ]
    exact hUnion

end CayleySubgraphSpec
end ABO
end PSTSEPPA
