import PSTSEPPA.ABO.MultiCosetEGraph
import PSTSEPPA.ABO.TrivialCompletionOutsideSupport
import PSTSEPPA.ABO.CompletedFullCosetStage

/-!
# Every genuine full multi-coset edge stays inside the parent alphabet

The partial EGraph underlying an ABO full proper-alphabet
coset extension of an A-labelled Cayley skeleton is formed
by gluing single-C extensions for proper C⊂A.

A directed edge of a single-C extension is either an old
K-edge with its original A-label or a newly completed
C-coset edge with label in C⊆A. This fact survives
the actual source-and-label QUOTIENT of all raw multi-CE
edge tokens, not merely the ambient Cayley projection.

We record the resulting exact edge-support theorem. It
implies that every label OUTSIDE A is absent at every
vertex of the raw multi-CE; after the legal loop-only
completion, arbitrary words supported in a disjoint
alphabet act as the identity everywhere.

There is no assumption of ambient CE→Cayley injectivity,
bridge-freeness, full cluster property or higher induction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every directed edge of a genuine single-C full coset
extension has its unsigned label in A whenever C⊆A:
old edges belong to the original A-skeleton and new
coset edges belong to C. -/
theorem singleCosetEdge_label_mem_parent
    (C : Finset ι) (hCA : C ⊆ A)
    (e : K.SingleCosetEdge C) :
    signedBase (K.singleCosetLabel C e) ∈ A := by
  cases e with
  | inl e =>
      exact K.label_mem e.1.1 e.1.2
  | inr e =>
      exact hCA e.2.2

/-- The signed label of EVERY quotient-edge class of
the actual all-proper multi-coset EGraph belongs to A.
This is a quotient-induction proof on real tagged
directed edge tokens, not a coordinate-only assertion. -/
theorem allProperCosetEdge_label_mem_parent
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret) :
    signedBase
      ((K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).label e) ∈ A := by
  induction e using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨⟨C, hCA⟩, edge⟩
      change signedBase (K.singleCosetLabel C edge) ∈ A
      exact K.singleCosetEdge_label_mem_parent
        C (((mem_allProperCosetFamily A C).mp hCA).subset) edge

/-- All words on labels outside A act trivially in the
ACTUAL legal loop-completed all-proper coset extension
at every vertex, provided |A|≥2 so that the source's
weak-completeness theorem constructs its completion. -/
theorem allProperCompletedStage_disjoint_word_fixes
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (C : Finset ι) (hdis : Disjoint C A)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (x : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    (K.allProperCompletedStage hadm hgen hret hcard).followWord x w = x := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let hpaired : G.LocallyPairedLabels :=
    K.multiCoset_locallyPairedLabels_of_weakComplete
      P hadm hgen hret
      (allProperCosetFamily_weaklyComplete K hadm hgen hret hcard)
  exact G.trivialLoopCompletion_disjoint_word_fixes A C
    (K.allProperCosetEdge_label_mem_parent hadm hgen hret)
    hpaired hdis w hw x

end CayleySubgraphSpec
end ABO
end PSTSEPPA
