import PSTSEPPA.ABO.MultiCosetWeakCompleteness

/-!
# Weak completeness gives paired positive/negative outgoing generator labels

The corrected ABO Section 5 uses TRIVIAL completion of certain
multi-coset E-graphs by adjoining only geometric loops for missing
generator labels. For a general E-graph this is NOT legal: at a
vertex the positive edge for label i may exist while the negative
edge is missing, in which case adding a loop pair would violate
determinism. This module records and proves the essential
structural invariant that makes the loop-only completion legal
for the weakly complete ABO coset extensions.

Every edge of a weakly complete CE lies inside a selected complete
B-coset constituent. If it has signed label +i (or -i), that
same constituent has an outgoing -i (or +i) edge at the SAME
tagged source vertex. Therefore every vertex has either BOTH
outgoing signs for a generator i or NEITHER.

This is not global E-graph completeness, and no graph edges
or quotient identifications are invented in this module. It is
the precise input for the next loop-only trivial completion.
-/

namespace PSTSEPPA
namespace ABO

variable {V Edge ι Γ : Type*}

/-- Local balancing of signed generator labels: at every vertex,
an outgoing positive i-edge exists if and only if an outgoing
negative i-edge exists. This is not assumed by a general EGraph. -/
def EGraph.LocallyPairedLabels
    (G : EGraph V Edge ι) : Prop :=
  ∀ (u : V) (i : ι),
    (∃ e : Edge,
      G.source e = u ∧ G.label e = PSTS.SignedLetter.pos i) ↔
    (∃ e : Edge,
      G.source e = u ∧ G.label e = PSTS.SignedLetter.neg i)

variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- In a weakly complete multi-coset EGraph, every directed edge
is accompanied at its SAME SOURCE by an outgoing edge with the
inverse SIGNED LABEL. This uses completeness within a tagged
constituent, not the global formal inverse (which starts at
the edge target and would not suffice). -/
theorem multiCoset_oppositeLabel_at_same_source
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hweak : K.MultiCosetWeaklyComplete P hadm hgen hret)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    ∃ f : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret,
      (K.multiCosetEGraph P hadm hgen hret).source f =
        (K.multiCosetEGraph P hadm hgen hret).source e ∧
      (K.multiCosetEGraph P hadm hgen hret).label f =
        PSTS.SignedLetter.inv
          ((K.multiCosetEGraph P hadm hgen hret).label e) := by
  obtain ⟨B, hBP, p, s, he⟩ := hweak e
  let G := K.multiCosetEGraph P hadm hgen hret
  let F := K.singleCosetToMultiHom P hadm hgen hret B hBP
  let s' : {s : SignedLabel ι // signedBase s ∈ B} :=
    ⟨PSTS.SignedLetter.inv s.1, by
      simpa only [signedBase_inv] using s.2⟩
  let oldEdge : K.SingleCosetEdge B := Sum.inr (p, s)
  let newEdge : K.SingleCosetEdge B := Sum.inr (p, s')
  have hOld : F.onEdge oldEdge = e := he
  refine ⟨F.onEdge newEdge, ?_, ?_⟩
  · calc
      G.source (F.onEdge newEdge) =
          F.onVertex ((K.singleCosetEGraph B).source newEdge) :=
        F.map_source newEdge
      _ = F.onVertex ((K.singleCosetEGraph B).source oldEdge) := rfl
      _ = G.source (F.onEdge oldEdge) :=
        (F.map_source oldEdge).symm
      _ = G.source e := by rw [hOld]
  · calc
      G.label (F.onEdge newEdge) =
          (K.singleCosetEGraph B).label newEdge :=
        F.map_label newEdge
      _ = PSTS.SignedLetter.inv
            ((K.singleCosetEGraph B).label oldEdge) := rfl
      _ = PSTS.SignedLetter.inv (G.label (F.onEdge oldEdge)) := by
        rw [F.map_label oldEdge]
      _ = PSTS.SignedLetter.inv (G.label e) := by rw [hOld]

/-- The concrete ABO weakly complete coset extension has paired
outgoing signed labels at every point, even if it is not globally
complete on some unsigned generators. -/
theorem multiCoset_locallyPairedLabels_of_weakComplete
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hweak : K.MultiCosetWeaklyComplete P hadm hgen hret) :
    (K.multiCosetEGraph P hadm hgen hret).LocallyPairedLabels := by
  intro u i
  constructor
  · rintro ⟨e, hsrc, hlab⟩
    obtain ⟨f, hfsrc, hflab⟩ :=
      K.multiCoset_oppositeLabel_at_same_source
        P hadm hgen hret hweak e
    refine ⟨f, hfsrc.trans hsrc, ?_⟩
    rw [hflab, hlab]
    rfl
  · rintro ⟨e, hsrc, hlab⟩
    obtain ⟨f, hfsrc, hflab⟩ :=
      K.multiCoset_oppositeLabel_at_same_source
        P hadm hgen hret hweak e
    refine ⟨f, hfsrc.trans hsrc, ?_⟩
    rw [hflab, hlab]
    rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
