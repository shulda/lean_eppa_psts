import PSTSEPPA.ABO.CoatomConstituentCover
import PSTSEPPA.ABO.MultiCosetWeakCompleteness

/-!
# Exact signed-edge cover by tagged codimension-one constituents

The finite coatom-cover step in ABO Lemma 4.3 has two logically
different aspects: vertices and directed labelled edges. Pointwise
coatom support alone does not ensure that a graph subcomponent is
covered by the corresponding completed coatom graphs.

For |A|>=2, every oriented edge of the full proper-family coset
extension already has some completed selected D-coset presentation,
by the checked weak-completeness theorem. Enlarge D to a coatom C
using the exact tagged vertex-support embedding. Because the
signed label of the edge belongs to D⊆C, the completed C-copy
contains an outgoing edge at exactly the same glued source with
exactly the same signed label. Determinism identifies these
ORIENTED EDGE TOKENS in the genuine multi-coset EGraph.

Thus not only the vertices, but every edge of the full extension
is represented inside a component-tagged coatom constituent.
The rank assumption is sharp for an arbitrary skeleton: when
|A|=1 its only nonempty edge label cannot belong to a proper
subalphabet. This is NOT a whole-component cluster theorem.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every actual signed directed edge of the full coset extension
at ambient rank at least two equals a completed edge in some
selected codimension-one C-coset copy (including formal inverses
and geometric loops). Exact edge-token equality, not merely an
equality of ambient Cayley coordinates, is the conclusion. -/
theorem allProperCosetEdge_exists_coatom_completed_presentation
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret) :
    ∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex C)
      (s : {s : SignedLabel ι // signedBase s ∈ C}),
      C.card + 1 = A.card ∧
      K.multiCosetEdgeInclude (allProperCosetFamily A)
        hadm hgen hret C hCP (Sum.inr (p, s)) = e := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨D, hDP, p, s, he⟩ :=
    (allProperCosetFamily_weaklyComplete K
      hadm hgen hret hcard) e
  obtain ⟨C, hCP, hDC, hCcard, hsource⟩ :=
    K.allProperCoset_constituent_extend_to_coatom
      hadm hgen hret D hDP p
  let q : K.AttachedCosetVertex C :=
    K.attachedSubalphabetMap D C hDC p
  let t : {s : SignedLabel ι // signedBase s ∈ C} :=
    ⟨s.1, hDC s.2⟩
  have hedges :
      K.multiCosetEdgeInclude P hadm hgen hret
          C hCP (Sum.inr (q,t)) =
      K.multiCosetEdgeInclude P hadm hgen hret
          D hDP (Sum.inr (p,s)) := by
    apply G.deterministic
    · change K.multiCosetInclude P hadm hgen hret C hCP q =
        K.multiCosetInclude P hadm hgen hret D hDP p
      exact hsource
    · rfl
  exact ⟨C, hCP, q, t, hCcard, hedges.trans he⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
