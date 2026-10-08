import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.SingleCosetConnectivity

/-!
# Uniqueness in ABO Proposition 3.18

The canonical morphism from a multi-alphabet coset extension to the
ambient Cayley graph was constructed already. Here we prove it is the
*unique* labelled graph morphism extending the literal skeleton
inclusion, provided the selected alphabet family contains at least
one alphabet.

The argument is not a disguised global injectivity claim. Every
multi-coset vertex is accessible from an actual skeleton vertex by
a path inside its constituent coset. A labelled morphism is therefore
uniquely determined on all vertices by its values on the skeleton,
since the ambient Cayley E-graph is deterministic. Edge uniqueness
then follows from source/label determinism.

The chosen alphabet may be empty as a subset of A. What is required
here is that the *family of cosets* is nonempty. For an empty family
the sum-of-cosets model contains no copy of K; that separate
source-level degenerate convention must not be silently conflated
with Proposition 3.18.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every vertex of the multi-coset extension is accessible from
some literal skeleton vertex by an actual path. -/
theorem multiCosetVertex_accessible_from_skeleton
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    ∃ (B : Finset ι) (hBP : B ∈ P.alphabets)
      (x : K.Vertex) (w : LabelWord ι),
      (K.multiCosetEGraph P hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x)
        w z := by
  induction z using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨B, p⟩
      obtain ⟨x, hx⟩ := K.componentClass_surjective B.1 p.1
      obtain ⟨w, hw, hpath⟩ :=
        K.singleCosetEGraph_connected_on_index
          B.1 (K.attachedOfSkeletonVertex B.1 x) p hx
      refine ⟨B.1, B.2, x, w, ?_⟩
      exact hpath.map
        (K.singleCosetToMultiHom P hadm hgen hret B.1 B.2)

/-- The canonical Cayley morphism is unique on vertices among
morphisms agreeing with the literal skeleton inclusion, as long
as the family contains a chosen constituent alphabet B. -/
theorem multiCosetAmbientHom_vertex_unique
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (f : LabelledGraphHom
      (K.multiCosetEGraph P hadm hgen hret).toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph)
    (hf : ∀ x : K.Vertex,
      f.onVertex
        ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x) =
      x.1)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    f.onVertex z =
      (K.multiCosetAmbientHom P hadm hgen hret).onVertex z := by
  obtain ⟨C, hCP, x, w, hpath⟩ :=
    K.multiCosetVertex_accessible_from_skeleton P hadm hgen hret z
  let s : K.MultiCosetVertex P hadm hgen hret :=
    (K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x
  have hs : f.onVertex s = x.1 := by
    have hsame :=
      K.skeletonToMultiCosetHom_vertex_independent
        P hadm hgen hret C B hCP hBP x
    change s =
      (K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x
      at hsame
    rw [hsame]
    exact hf x
  have hsCanonical :
      (K.multiCosetAmbientHom P hadm hgen hret).onVertex s = x.1 :=
    rfl
  have hpathF :
      (cayleyGraph gen).toEGraph.Follows
        (f.onVertex s) w (f.onVertex z) := hpath.map f
  have hpathCanonical :
      (cayleyGraph gen).toEGraph.Follows
        ((K.multiCosetAmbientHom P hadm hgen hret).onVertex s)
        w
        ((K.multiCosetAmbientHom P hadm hgen hret).onVertex z) :=
    hpath.map (K.multiCosetAmbientHom P hadm hgen hret)
  rw [hs] at hpathF
  rw [hsCanonical] at hpathCanonical
  exact (cayleyGraph gen).toEGraph.follows_right_unique
    hpathF hpathCanonical

/-- The canonical morphism is also unique on oriented edge tokens:
equal source images and preservation of signed labels force equal
ambient Cayley edges. -/
theorem multiCosetAmbientHom_edge_unique
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (f : LabelledGraphHom
      (K.multiCosetEGraph P hadm hgen hret).toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph)
    (hf : ∀ x : K.Vertex,
      f.onVertex
        ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x) =
      x.1)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    f.onEdge e =
      (K.multiCosetAmbientHom P hadm hgen hret).onEdge e := by
  apply (cayleyGraph gen).toEGraph.deterministic
  · calc
      (cayleyGraph gen).source (f.onEdge e) =
          f.onVertex ((K.multiCosetEGraph P hadm hgen hret).source e) :=
        f.map_source e
      _ = (K.multiCosetAmbientHom P hadm hgen hret).onVertex
          ((K.multiCosetEGraph P hadm hgen hret).source e) :=
        K.multiCosetAmbientHom_vertex_unique
          P hadm hgen hret B hBP f hf
          ((K.multiCosetEGraph P hadm hgen hret).source e)
      _ = (cayleyGraph gen).source
          ((K.multiCosetAmbientHom P hadm hgen hret).onEdge e) :=
        ((K.multiCosetAmbientHom P hadm hgen hret).map_source e).symm
  · exact (f.map_label e).trans
      ((K.multiCosetAmbientHom P hadm hgen hret).map_label e).symm

/-- Source-facing unique-extension clause of ABO Proposition 3.18,
restricted to the nonempty family required by the current disjoint
union presentation. There are no extra hypotheses on a putative
ambient morphism beyond agreement with the skeleton. -/
theorem multiCosetAmbientHom_unique
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (f : LabelledGraphHom
      (K.multiCosetEGraph P hadm hgen hret).toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph)
    (hf : ∀ x : K.Vertex,
      f.onVertex
        ((K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x) =
      x.1) :
    (∀ z : K.MultiCosetVertex P hadm hgen hret,
      f.onVertex z =
        (K.multiCosetAmbientHom P hadm hgen hret).onVertex z) ∧
    (∀ e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret,
      f.onEdge e =
        (K.multiCosetAmbientHom P hadm hgen hret).onEdge e) := by
  constructor
  · exact K.multiCosetAmbientHom_vertex_unique
      P hadm hgen hret B hBP f hf
  · exact K.multiCosetAmbientHom_edge_unique
      P hadm hgen hret B hBP f hf

end CayleySubgraphSpec
end ABO
end PSTSEPPA
