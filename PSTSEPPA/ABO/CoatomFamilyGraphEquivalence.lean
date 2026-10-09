import PSTSEPPA.ABO.MultiCosetFamilyInclusion
import PSTSEPPA.ABO.CoatomConstituentCover
import PSTSEPPA.ABO.CoatomEdgeCover

/-!
# Coatom-only extension is the FULL coset extension as a labelled graph

The full proper-alphabet extension selects all D⊊A, but the
codimension-one (coatom) family suffices to realize the same
vertices and, at ambient rank at least two, the same oriented
signed edges, with exactly the same component-tagged gluing.

The canonical inclusion of any selected subfamily of cosets is a
vertex- and edge-injective labelled graph homomorphism. Here
every full-family quotient vertex is in a coatom constituent,
as proved in CoatomConstituentCover. Moreover, at |A|≥2,
the weak-completeness plus coatom-edge-cover theorem guarantees
every edge of the full extension has an exact completed coatom
representation. Both canonical maps are therefore surjective.

Consequently the inclusion homomorphism is *bijective on both
vertices and oriented edge tokens*; it is a labelled-graph
isomorphism in the usual mathematical sense. No global ambient
Cayley projection injectivity or higher-rank cluster property
is assumed.

The rank restriction applies only to the EDGE surjectivity
statement. The vertex theorem works even at |A|=0,1
(vacuously when the full family is empty).
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- The finite family of all codimension-one proper alphabets. -/
def coatomCosetFamily (A : Finset ι) : CosetFamilySpec A where
  alphabets :=
    (allProperCosetFamily A).alphabets.filter
      (fun C => C.card + 1 = A.card)
  proper := by
    intro C hC
    exact (mem_allProperCosetFamily A C).mp
      (Finset.mem_filter.mp hC).1

/-- A coatom is in the selected family exactly when it is
proper in A and has cardinality one less than A. -/
theorem mem_coatomCosetFamily (A C : Finset ι) :
    C ∈ (coatomCosetFamily A).alphabets ↔
      C ⊂ A ∧ C.card + 1 = A.card := by
  constructor
  · intro h
    have hc := Finset.mem_filter.mp h
    exact ⟨(mem_allProperCosetFamily A C).mp hc.1, hc.2⟩
  · rintro ⟨hproper, hcard⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_allProperCosetFamily A C).mpr hproper, hcard⟩

/-- Coatom-only selected alphabets form a subfamily of
the full proper-alphabet coset family. -/
theorem coatomCosetFamily_subset_allProper (A : Finset ι) :
    (coatomCosetFamily A).alphabets ⊆
      (allProperCosetFamily A).alphabets := by
  intro C hC
  exact (Finset.mem_filter.mp hC).1

variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Canonical actual labelled E-graph inclusion of the coatom-only
extension into the complete proper-subalphabet extension.
Injectivity on both sorts follows from the general family API. -/
noncomputable def coatomToFullCosetHom
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    LabelledGraphHom
      (K.multiCosetEGraph (coatomCosetFamily A)
        hadm hgen hret).toLabelledGraph
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).toLabelledGraph :=
  K.multiCosetFamilyHom
    (coatomCosetFamily A) (allProperCosetFamily A)
    hadm hgen hret (coatomCosetFamily_subset_allProper A)

/-- Every full-extension vertex is represented by a tagged
coatom vertex, hence lies in the canonical inclusion's image. -/
theorem coatomToFullCosetHom_vertex_surjective
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Function.Surjective
      (K.coatomToFullCosetHom hadm hgen hret).onVertex := by
  intro z
  obtain ⟨C, hCP, hcard, hSupport⟩ :=
    K.allProperCosetVertex_exists_coatom_support
      hadm hgen hret z
  obtain ⟨_, p, hp⟩ := hSupport
  have hCo :
      C ∈ (coatomCosetFamily A).alphabets :=
    (mem_coatomCosetFamily A C).mpr
      ⟨(mem_allProperCosetFamily A C).mp hCP, hcard⟩
  refine ⟨K.multiCosetInclude (coatomCosetFamily A)
    hadm hgen hret C hCo p, ?_⟩
  change
    K.multiCosetInclude (allProperCosetFamily A)
      hadm hgen hret C hCP p = z
  exact hp

/-- For rank at least two, exact coatom coverage holds for
every *oriented signed edge token* of the full extension.
There is no need to identify an edge merely via Cayley values. -/
theorem coatomToFullCosetHom_edge_surjective
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card) :
    Function.Surjective
      (K.coatomToFullCosetHom hadm hgen hret).onEdge := by
  intro e
  obtain ⟨C, hCP, p, s, hCoCard, he⟩ :=
    K.allProperCosetEdge_exists_coatom_completed_presentation
      hadm hgen hret hcard e
  have hCo : C ∈ (coatomCosetFamily A).alphabets :=
    (mem_coatomCosetFamily A C).mpr
      ⟨(mem_allProperCosetFamily A C).mp hCP, hCoCard⟩
  refine ⟨K.multiCosetEdgeInclude (coatomCosetFamily A)
    hadm hgen hret C hCo (Sum.inr (p, s)), ?_⟩
  change
    K.multiCosetEdgeInclude (allProperCosetFamily A)
      hadm hgen hret C hCP (Sum.inr (p, s)) = e
  exact he

/-- Complete graph-level equivalence: for |A|≥2 the
canonical coatom-only→full multi-coset homomorphism is
bijective on both vertices and signed directed edges.
It already preserves source, reversal and signed labels.
This is NOT a proof of any further cluster geometry. -/
theorem coatomToFullCosetHom_bijective
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card) :
    Function.Bijective
      (K.coatomToFullCosetHom hadm hgen hret).onVertex ∧
    Function.Bijective
      (K.coatomToFullCosetHom hadm hgen hret).onEdge := by
  constructor
  · constructor
    · exact K.multiCosetFamilyVertexMap_injective
        (coatomCosetFamily A) (allProperCosetFamily A)
        hadm hgen hret (coatomCosetFamily_subset_allProper A)
    · exact K.coatomToFullCosetHom_vertex_surjective
        hadm hgen hret
  · constructor
    · exact K.multiCosetFamilyEdgeMap_injective
        (coatomCosetFamily A) (allProperCosetFamily A)
        hadm hgen hret (coatomCosetFamily_subset_allProper A)
    · exact K.coatomToFullCosetHom_edge_surjective
        hadm hgen hret hcard

end CayleySubgraphSpec
end ABO
end PSTSEPPA
