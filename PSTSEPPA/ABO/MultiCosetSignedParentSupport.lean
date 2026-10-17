import PSTSEPPA.ABO.AllProperCosetEdgeSupport
import PSTSEPPA.ABO.TrivialCompletionOutsideSupport
import PSTSEPPA.ABO.StandardCosetFamily

/-!
# Every real edge of a tagged P_A coset extension has support inside A

Corrected ABO's original full P_A extension uses ONLY
true original skeleton edges labelled inside A and
fresh complete signed B-coset edges with B strictly
contained in A. The exact B∩C-gluing of vertices
and the separate signed source-label quotient of
edge tokens cannot create any new signed alphabet
outside A.

We prove this from the ACTUAL old/fresh tagged
edge constructors, then descend it through the
genuine raw signed edge quotient to the complete
component-tagged multi-CE EGraph.

Consequently LEGAL stationary-loop completion of
such a P_A extension fixes every vertex for every
signed label OUTSIDE A. This is not an assumption
about group generators or an artificial completion
of the original X₁ old skeleton. It is an actual
statement about the genuine chosen H stage action.

This is the missing input for promoting the local
A-Cayley skeleton map to a FULL signed Cayley(G[A])
action cover of the printed H rooted P_A stage:
outside-A letters are identity in G[A] and now
also in the selected completed stage. Construction
of the source-specific full local cover and the
subsequent corrected Theorem 4.7(ii)/(iii) remain
separate gates. No ambient-coordinate injectivity,
equivariance of the full Z₁ catalogue, or PSTS EPPA
is asserted.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

/-- After quotienting ALL component-tagged raw
B-constituent signed edges by their ACTUAL
glued source and FULL signed label, every
resulting edge still has its original label
inside the parent alphabet A. No edge outside
A is manufactured by the vertex/edge gluing. -/
theorem multiCosetEGraph_label_mem_parent
    (K : CayleySubgraphSpec gen A)
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret) :
    signedBase ((K.multiCosetEGraph P hadm hgen hret).label e) ∈ A := by
  induction e using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨B, edge⟩
      change signedBase (K.singleCosetLabel B.1 edge) ∈ A
      exact K.singleCosetEdge_label_mem_parent
        B.1 (P.proper B.1 B.2).subset edge

/-- All labels OUTSIDE the true parent A act by
stationary loops after LEGAL completion of the
original tagged P_A coset extension. Thus
inverse labels and geometric old loops are
treated without making up nonloop old edges. -/
theorem multiCoset_trivialCompletion_outside_A_fixes
    (K : CayleySubgraphSpec gen A)
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hpaired :
      (K.multiCosetEGraph P hadm hgen hret).LocallyPairedLabels)
    (s : SignedLabel ι) (hs : signedBase s ∉ A)
    (u : K.MultiCosetVertex P hadm hgen hret) :
    ((K.multiCosetEGraph P hadm hgen hret).trivialLoopCompletion
      hpaired).target
      (((K.multiCosetEGraph P hadm hgen hret).trivialLoopCompletion
        hpaired).edgeAt u s) = u := by
  exact (K.multiCosetEGraph P hadm hgen hret).trivialLoopCompletion_outside_label_fixes
      A
      (K.multiCosetEGraph_label_mem_parent
        P hadm hgen hret)
      hpaired s hs u

end CayleySubgraphSpec
end ABO
end PSTSEPPA
