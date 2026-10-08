import PSTSEPPA.ABO.MultiCosetEGraph
import PSTSEPPA.ABO.SingleCosetSkeletonEmbedding

/-!
# Canonical morphisms of the multi-alphabet coset extension (ABO 3.18)

The multi-coset E-graph admits a canonical labelled graph morphism to
the ambient Cayley graph. This morphism preserves sources, targets,
formal inverse edge tokens and signed labels. It is NOT asserted to
be globally injective.

For each chosen subalphabet B, the original skeleton embeds through
the single-B coset extension into the full multi-alphabet extension.
The embedding is injective on vertices and directed edge tokens.

If B and C are both in the selected family, these embeddings agree
on every original skeleton vertex; they also agree on every edge by
determinism of the target multi-alphabet E-graph. This is the
alphabet-independent graph embedding component of ABO Proposition 3.18.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The canonical labelled-graph morphism from the glued multi-coset
extension to the original ambient Cayley graph. It is intentionally
not claimed globally injective. -/
noncomputable def multiCosetAmbientHom
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    LabelledGraphHom
      (K.multiCosetEGraph P hadm hgen hret).toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph where
  onVertex := K.multiCosetAmbientValue P hadm hgen hret
  onEdge := K.multiCosetEdgeQuotientAmbient P hadm hgen hret
  map_source := by
    intro e
    induction e using Quotient.inductionOn with
    | h e =>
      exact K.multiCosetRawEdgeAmbient_source P hadm hgen hret e
  map_inv := by
    intro e
    induction e using Quotient.inductionOn with
    | h e =>
      exact K.multiCosetRawEdgeAmbient_inv P e
  map_label := by
    intro e
    induction e using Quotient.inductionOn with
    | h e =>
      exact K.multiCosetRawEdgeAmbient_label P e

/-- Canonical labelled-graph inclusion of the original skeleton through
a chosen B-summand into the multi-alphabet coset extension. -/
noncomputable def skeletonToMultiCosetHom
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    LabelledGraphHom
      (K.toEGraph).toLabelledGraph
      (K.multiCosetEGraph P hadm hgen hret).toLabelledGraph :=
  (K.singleCosetToMultiHom P hadm hgen hret B hBP).comp
    (K.skeletonToSingleCosetHom B)

/-- The skeleton-to-multi-coset morphism is vertex-injective. -/
theorem skeletonToMultiCosetHom_vertex_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    Function.Injective
      (K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex :=
  (K.singleCosetToMultiHom_vertex_injective P hadm hgen hret B hBP).comp
    (K.skeletonToSingleCosetHom_vertex_injective B)

/-- The skeleton-to-multi-coset morphism is also injective on signed
directed edge tokens, including the two tokens of a geometric loop. -/
theorem skeletonToMultiCosetHom_edge_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    Function.Injective
      (K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onEdge :=
  (K.singleCosetToMultiHom_edge_injective P hadm hgen hret B hBP).comp
    (K.skeletonToSingleCosetHom_edge_injective B)

/-- The skeleton images of a vertex do not depend on the chosen
alphabet summand of the multi-coset extension. -/
theorem skeletonToMultiCosetHom_vertex_independent
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (x : K.Vertex) :
    (K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onVertex x =
      (K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x :=
  K.multiCosetInclude_skeleton_independent
    P hadm hgen hret B C hBP hCP x

/-- The same independence holds for original directed edge tokens.
It follows from target E-graph determinism once source vertices and
signed labels have already been shown independent. -/
theorem skeletonToMultiCosetHom_edge_independent
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (e : K.Edge) :
    (K.skeletonToMultiCosetHom P hadm hgen hret B hBP).onEdge e =
      (K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onEdge e := by
  let fB := K.skeletonToMultiCosetHom P hadm hgen hret B hBP
  let fC := K.skeletonToMultiCosetHom P hadm hgen hret C hCP
  apply (K.multiCosetEGraph P hadm hgen hret).deterministic
  · calc
      (K.multiCosetEGraph P hadm hgen hret).source (fB.onEdge e) =
          fB.onVertex ((K.toEGraph).source e) := fB.map_source e
      _ = fC.onVertex ((K.toEGraph).source e) :=
        K.skeletonToMultiCosetHom_vertex_independent
          P hadm hgen hret B C hBP hCP ((K.toEGraph).source e)
      _ = (K.multiCosetEGraph P hadm hgen hret).source (fC.onEdge e) :=
        (fC.map_source e).symm
  · exact (fB.map_label e).trans (fC.map_label e).symm

end CayleySubgraphSpec
end ABO
end PSTSEPPA
