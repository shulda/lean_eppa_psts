import PSTSEPPA.ABO.MultiCosetCompletedEdgeOverlap
import PSTSEPPA.ABO.MultiCosetOldEdgeOverlap
import PSTSEPPA.ABO.MultiCosetMixedEdgeOverlap
import PSTSEPPA.ABO.MultiCosetConditionalEGraph

/-!
# Unconditional multi-alphabet ABO coset-extension E-graph

The source-and-label edge quotient can be promoted to a genuine ABO
E-graph once we prove the concrete target-congruence lemma.

There are four ordered edge-type combinations:
  * old skeleton / old skeleton;
  * old skeleton / completed coset;
  * completed coset / old skeleton (the symmetric case);
  * completed coset / completed coset.

Each component case has been proved independently with exact component
tags, not ambient-group injectivity. Combining them discharges
MultiCosetTargetCongruent without any new hypothesis beyond the
admissibility, retractability and group-generation assumptions already
used by the vertex gluing quotient.

The conditional formal-inversion construction then supplies a
deterministic E-graph with the literal source quotient of ABO (3.10).
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Actual target congruence for ALL raw multi-coset edge tokens.

Equal sources in the quotient of tagged coset vertices and equal signed
labels imply equal targets in that same quotient. Every edge combination
is handled explicitly, including geometric loops, empty/equal alphabets
and repeated/trivial generators. -/
theorem multiCosetTargetCongruent_of_admissible
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    K.MultiCosetTargetCongruent P hadm hgen hret := by
  intro e f hrel
  change
    K.multiCosetRawEdgeSource P hadm hgen hret e =
      K.multiCosetRawEdgeSource P hadm hgen hret f ∧
    K.multiCosetRawEdgeLabel P e =
      K.multiCosetRawEdgeLabel P f at hrel
  rcases hrel with ⟨hs, hl⟩
  rcases e with ⟨B, e⟩
  rcases f with ⟨C, f⟩
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      exact K.multiCosetOldEdge_targets_eq
        P hadm hgen hret B.1 C.1 B.2 C.2 e f hs hl
    | inr f =>
      exact K.multiCosetOldCompletedEdge_targets_eq
        P hadm hgen hret B.1 C.1 B.2 C.2 e f hs hl
  | inr e =>
    cases f with
    | inl f =>
      exact (K.multiCosetOldCompletedEdge_targets_eq
        P hadm hgen hret C.1 B.1 C.2 B.2 f e
        hs.symm hl.symm).symm
    | inr f =>
      exact K.multiCosetCompletedEdge_targets_eq
        P hadm hgen hret B.1 C.1 B.2 C.2 e f hs hl

/-- The actual deterministic multi-alphabet coset-extension E-graph.
The target-congruence obligation has been discharged, so this definition
is unconditional under the source construction's own hypotheses. -/
noncomputable def multiCosetEGraph
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    EGraph
      (K.MultiCosetVertex P hadm hgen hret)
      (K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) ι :=
  K.multiCosetQuotientEGraph P hadm hgen hret
    (K.multiCosetTargetCongruent_of_admissible P hadm hgen hret)

/-- Every single-alphabet coset extension maps canonically into the
full multi-alphabet extension, preserving vertices, directed edges,
formal edge reversal and signed labels. -/
noncomputable def singleCosetToMultiHom
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    LabelledGraphHom
      (K.singleCosetEGraph B).toLabelledGraph
      (K.multiCosetEGraph P hadm hgen hret).toLabelledGraph where
  onVertex := K.multiCosetInclude P hadm hgen hret B hBP
  onEdge := K.multiCosetEdgeInclude P hadm hgen hret B hBP
  map_source e := rfl
  map_inv e := rfl
  map_label e := rfl

/-- No constituent B-coset vertex collapses in the full E-graph. -/
theorem singleCosetToMultiHom_vertex_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    Function.Injective
      (K.singleCosetToMultiHom P hadm hgen hret B hBP).onVertex :=
  K.multiCosetInclude_injective P hadm hgen hret B hBP

/-- No constituent B-coset directed edge collapses in the full E-graph.
This is strictly weaker than ambient Cayley-map global injectivity. -/
theorem singleCosetToMultiHom_edge_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    Function.Injective
      (K.singleCosetToMultiHom P hadm hgen hret B hBP).onEdge :=
  K.multiCosetEdgeInclude_injective P hadm hgen hret B hBP

end CayleySubgraphSpec
end ABO
end PSTSEPPA
