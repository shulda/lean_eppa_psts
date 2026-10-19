import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents
import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso
import PSTSEPPA.ABO.MultiCosetEGraph

/-!
# ABO Lemma 4.3: the full B-coset alternative has ALL real signed B-edges

The PUBLISHED Lemma 4.3 has a full-B-coset alternative distinct
from its proper-cluster alternative. If the chosen actual
B-component starts in one ORIGINAL component-tagged completed
C-constituent with B ⊆ C, then the accepted exact
`multiCoset_selected_C_subalphabet_B_component_exact` theorem
already identifies its entire VERTEX component with the genuine
tagged full B-coset inside that C-constituent.

To identify the ORIGINAL oriented signed graph, rather than
only its vertices or ambient Cayley coordinates, we also need
that every real signed B-edge of this component comes from
the SAME C-copy, and conversely that every signed B-step from
each reachable vertex exists in the original multiCE.

Both statements follow from the accepted genuine completed
C-edge inclusion and determinism of the original signed
edge-token quotient. They apply for ANY selected C containing
B, without a minimum support, no-lower-support hypothesis,
finite group, or global multiCE→Cayley injection.

This is the missing original signed-edge completeness
statement for the full-B-coset side of ABO Lemma 4.3.
It includes both formal inverse orientations and genuine
signed loops but never adds a missing OLD skeleton edge:
completed attached C-coset edges are REAL edges of the
original coset extension itself.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every real oriented signed B-edge in the ORIGINAL
B-component of a tagged C-constituent point with B⊆C
has an ACTUAL completed signed C-edge representation
with the SAME original old C-component tag.

This is stronger than ambient coset membership and uses
the source-and-label DETERMINISM of the genuine edge
quotient: a signed edge from a C-supported source is
equal as an ORIGINAL edge token to its completed C-step.
It is not necessary to assume that the old skeleton
contained that edge. -/
theorem multiCoset_full_B_component_all_signed_edges_in_C
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (B : Finset ι) (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex C)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret)
    (he :
      e ∈ (K.multiCosetEGraph P hadm hgen hret).BComponentEdgeSet
        B (K.multiCosetInclude P hadm hgen hret C hCP p)) :
    ∃ (q : K.AttachedCosetVertex C)
      (s : {s : SignedLabel ι // signedBase s ∈ C}),
      q.1 = p.1 ∧
      e = K.multiCosetEdgeInclude P hadm hgen hret
        C hCP (Sum.inr (q,s)) := by
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨heB, hSourceReach⟩ := he
  obtain ⟨w, hwB, hReal⟩ := hSourceReach
  obtain ⟨q, hqIndex, _hqCoset, hSourceC⟩ :=
    (K.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret C hCP B hBC
      p (G.source e)).mp ⟨w, hwB, hReal⟩
  let s : {s : SignedLabel ι // signedBase s ∈ C} :=
    ⟨G.label e, hBC heB⟩
  let eC : K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret :=
    K.multiCosetEdgeInclude P hadm hgen hret
      C hCP (Sum.inr (q,s))
  have hSameSource : G.source eC = G.source e := by
    change K.multiCosetInclude P hadm hgen hret C hCP q = G.source e
    exact hSourceC.symm
  have hSameLabel : G.label eC = G.label e := rfl
  have hSameEdge : eC = e :=
    G.deterministic hSameSource hSameLabel
  exact ⟨q, s, hqIndex, hSameEdge.symm⟩

/-- ACTUAL signed B-edge completeness of the original full
B-coset component: for EVERY reachable quotient vertex y
and EVERY positive or inverse signed B-letter s, there
is a GENUINE original edge token with exact source y
and exact signed label s.

The witness is an edge of the selected completed C-copy
with the correct intrinsic old C-component tag, not an
artificial edge introduced after the coset extension. -/
theorem multiCoset_full_B_component_all_signed_steps_exist
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (B : Finset ι) (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex C)
    (y : K.MultiCosetVertex P hadm hgen hret)
    (hy :
      y ∈ (K.multiCosetEGraph P hadm hgen hret).BComponentVertexSet
        B (K.multiCosetInclude P hadm hgen hret C hCP p))
    (s : SignedLabel ι) (hsB : signedBase s ∈ B) :
    ∃ e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret,
      e ∈ (K.multiCosetEGraph P hadm hgen hret).BComponentEdgeSet
        B (K.multiCosetInclude P hadm hgen hret C hCP p) ∧
      (K.multiCosetEGraph P hadm hgen hret).source e = y ∧
      (K.multiCosetEGraph P hadm hgen hret).label e = s := by
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨w, hwB, hReal⟩ := hy
  obtain ⟨q, _hqIndex, _hqCoset, hY⟩ :=
    (K.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret C hCP B hBC p y).mp ⟨w,hwB,hReal⟩
  let sC : {s : SignedLabel ι // signedBase s ∈ C} :=
    ⟨s, hBC hsB⟩
  let e : K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret :=
    K.multiCosetEdgeInclude P hadm hgen hret
      C hCP (Sum.inr (q,sC))
  have hSource : G.source e = y := by
    change K.multiCosetInclude P hadm hgen hret C hCP q = y
    exact hY.symm
  have hLabel : G.label e = s := rfl
  refine ⟨e, ?_, hSource, hLabel⟩
  exact ⟨by simpa only [hLabel] using hsB,
    by simpa only [hSource] using hy⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
