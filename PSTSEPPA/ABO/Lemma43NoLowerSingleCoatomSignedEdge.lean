import PSTSEPPA.ABO.CoatomEdgeCover
import PSTSEPPA.ABO.MaximalProperAlphabets
import PSTSEPPA.ABO.MultiCosetVertexSupport

/-!
# ABO Lemma 4.3: no lower support forces ACTUAL signed edges into one coatom

The one-constituent case in the PUBLISHED source Lemma 4.3
requires more than the vertex statement Q ⊆ vH[C]:
to identify the entire original SIGNED B-component as
a (B ∩ C)-coset GRAPH, we must rule out real edges of Q
coming from OTHER constituent copies.

This file gives the exact source edge refinement, with
NO assumptions about the entire B-component beyond
the indicated TRUE starting vertex.

Let C be a maximal proper selected alphabet, and let the
source of a TRUE oriented signed old+fresh edge e lie in
a specific ORIGINAL old-component-tagged full C-copy.
If the source has NO tagged support on D⊊C, then e
itself has an actual completed C-edge presentation
with EXACTLY the same source attached vertex p_C.

Proof: the accepted coatom edge-cover presents every real
signed token e inside some coatom D. Thus the source
has both original C- and D-supports. Exact component-tagged
gluing (3.11) gives an actual (C∩D)-support.
If D≠C, maximality of C forces C∩D⊊C, forbidden
by the source hypothesis. Hence D=C, and the accepted
injectivity inside the original tagged C-copy identifies
the source attached vertex of e with p_C itself.

This proves a real ORIGINAL signed edge statement,
not merely a Cayley coordinate equality or a vertex
reachability shortcut. Both formal inverse tokens and
geometric loops are covered, with no artificial edges
from a later completion.

In the source one-constituent/no-lower-support branch,
apply this lemma to EVERY original B-edge inside Q:
its signed label must lie in B∩C and the exact signed
edge is a genuine edge of the selected C-copy. This
is the remaining edge-geometric ingredient for the
one-constituent coset-graph alternative.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Source maximal-C edge rigidity in the original full proper
coset extension. Any true oriented signed edge whose source
is on one precise original tagged coatom C and has no
STRICTLY SMALLER original support must already be a true
C-completed edge from that SAME attached C-point.

No assumption of GLOBAL ambient Cayley injectivity or
whole-component cluster property is made. -/
theorem allProperCoset_coatom_edge_from_no_lower_source
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 2 ≤ A.card)
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCcard : C.card + 1 = A.card)
    (pC : K.AttachedCosetVertex C)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (hSource :
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP pC =
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e)
    (hNoLowerSource :
      ∀ D : Finset ι, D ⊂ C →
        ¬ K.MultiCosetVertexSupported
          (allProperCosetFamily A) hadm hgen hret D
          ((K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).source e)) :
    ∃ s : {s : SignedLabel ι // signedBase s ∈ C},
      e = K.multiCosetEdgeInclude (allProperCosetFamily A)
        hadm hgen hret C hCP (Sum.inr (pC, s)) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨D, hDP, pD, s, hDcard, he⟩ :=
    K.allProperCosetEdge_exists_coatom_completed_presentation
      hadm hgen hret hAcard e
  have hDsrc :
      K.multiCosetInclude P hadm hgen hret D hDP pD =
        G.source e := by
    rw [← he]
    rfl
  have hSuppC :
      K.MultiCosetVertexSupported P hadm hgen hret C
        (G.source e) :=
    ⟨hCP, pC, hSource⟩
  have hSuppD :
      K.MultiCosetVertexSupported P hadm hgen hret D
        (G.source e) :=
    ⟨hDP, pD, hDsrc⟩
  have hDCeq : D = C := by
    by_contra hDistinct
    have hCnotD : ¬ C ⊆ D := by
      intro hCD
      have hDEqC : D = C :=
        allProperCoset_coatom_maximal A C hCcard D hDP hCD
      exact hDistinct hDEqC
    have hInterStrict : C ∩ D ⊂ C := by
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro hEqual
      apply hCnotD
      intro i hi
      exact (Finset.mem_inter.mp (hEqual hi)).2
    have hInterSupport :
        K.MultiCosetVertexSupported P hadm hgen hret
          (C ∩ D) (G.source e) :=
      K.allProperCosetVertex_support_inter
        hadm hgen hret (G.source e)
        C D hSuppC hSuppD
    exact hNoLowerSource (C ∩ D)
      hInterStrict hInterSupport
  subst D
  have hpEq : pD = pC :=
    K.multiCosetInclude_injective P hadm hgen hret C hCP
      (hDsrc.trans hSource.symm)
  refine ⟨s, ?_⟩
  simpa only [hpEq] using he.symm

end CayleySubgraphSpec
end ABO
end PSTSEPPA
