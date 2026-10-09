import PSTSEPPA.ABO.MultiCosetComponentSupportDichotomy
import PSTSEPPA.ABO.MultiCosetOffSkeletonEdgeSupport
import PSTSEPPA.ABO.MultiCosetVertexSupport

/-!
# Strict support drop at the boundary of a maximal constituent

In the higher-rank cluster-property induction, a maximal
proper constituent C may contain some vertices of a B-component
without containing its whole vertex set. An edge crossing the
boundary of the C-summand forces a lower-alphabet support.
This is the local starting point of the first paragraph of
ABO Lemma 4.3; it does not use its induction hypotheses.

Here the "maximal" assumption is given exactly: among the
selected proper alphabets, no strict extension of C exists.
For the full proper family, it is satisfied by C of
cardinality |A|-1. We assume C nonempty (the relevant
higher-rank case); otherwise a skeleton edge may leave
a ∅-constituent without any smaller support being possible.

We work with true tagged quotient vertices and *directed
edge tokens*. Original skeleton edges and completed edges
are treated separately. There is no global ambient-map
injectivity or assumed cluster property.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If the source of a signed edge is supported in a maximal
selected proper alphabet C, but the edge has a label outside C,
then the source admits tagged support over a *strictly smaller*
alphabet D⊊C.

For a surviving old skeleton edge take D=∅. For a completed
E-edge intersect the two exact tagged supports C and E. By
maximality, C⊆E would force E=C, contrary to the edge label. -/
theorem allProperCoset_maximal_support_exit_label_lower
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCnonempty : C.Nonempty)
    (hMax :
      ∀ (E : Finset ι)
        (hEP : E ∈ (allProperCosetFamily A).alphabets),
        C ⊆ E → E = C)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (hSourceC :
      K.MultiCosetVertexSupported
        (allProperCosetFamily A) hadm hgen hret C
        ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).source e))
    (hOutside :
      signedBase
        ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).label e)
          ∉ C) :
    ∃ D : Finset ι,
      D ⊂ C ∧
      K.MultiCosetVertexSupported
        (allProperCosetFamily A) hadm hgen hret D
        ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).source e) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  induction e using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨E, edge⟩
      cases edge with
      | inl old =>
          let x : K.Vertex := (K.toEGraph).source old.1
          have hEmptyC : (∅ : Finset ι) ⊂ C := by
            refine ⟨Finset.empty_subset C, ?_⟩
            intro hCE
            obtain ⟨t, ht⟩ := hCnonempty
            have htEmpty : t ∈ (∅ : Finset ι) := hCE ht
            simpa using htEmpty
          have hEmptyA : (∅ : Finset ι) ⊂ A := by
            refine ⟨Finset.empty_subset A, ?_⟩
            intro hAE
            obtain ⟨t, ht⟩ := hCnonempty
            have htA : t ∈ A :=
              ((mem_allProperCosetFamily A C).mp hCP).1 ht
            have htEmpty : t ∈ (∅ : Finset ι) := hAE htA
            simpa using htEmpty
          have hEmptyP :
              (∅ : Finset ι) ∈ P.alphabets :=
            (mem_allProperCosetFamily A ∅).mpr hEmptyA
          refine ⟨∅, hEmptyC, hEmptyP,
            K.attachedOfSkeletonVertex ∅ x, ?_⟩
          change
            K.multiCosetInclude P hadm hgen hret
                ∅ hEmptyP (K.attachedOfSkeletonVertex ∅ x) =
              K.multiCosetInclude P hadm hgen hret
                E.1 E.2 (K.attachedOfSkeletonVertex E.1 x)
          exact K.multiCosetInclude_skeleton_independent
            P hadm hgen hret ∅ E.1 hEmptyP E.2 x
      | inr completed =>
          have hLabelOutside : signedBase completed.2.1 ∉ C := by
            change signedBase completed.2.1 ∉ C at hOutside
            exact hOutside
          have hNotCE : ¬ C ⊆ E.1 := by
            intro hCE
            have hEq : E.1 = C := hMax E.1 E.2 hCE
            have hsC : signedBase completed.2.1 ∈ C := by
              rw [← hEq]
              exact completed.2.2
            exact hLabelOutside hsC
          have hStrict : C ∩ E.1 ⊂ C := by
            refine ⟨Finset.inter_subset_left, ?_⟩
            intro hCsub
            apply hNotCE
            intro t ht
            exact (Finset.mem_inter.mp (hCsub ht)).2
          let x : K.MultiCosetVertex P hadm hgen hret :=
            K.multiCosetInclude P hadm hgen hret
              E.1 E.2 completed.1
          have hC : K.MultiCosetVertexSupported
              P hadm hgen hret C x := by
            change K.MultiCosetVertexSupported P hadm hgen hret C
              (K.multiCosetInclude P hadm hgen hret
                E.1 E.2 completed.1) at hSourceC
            exact hSourceC
          have hE : K.MultiCosetVertexSupported
              P hadm hgen hret E.1 x :=
            ⟨E.2, completed.1, rfl⟩
          have hCE : K.MultiCosetVertexSupported
              P hadm hgen hret (C ∩ E.1) x :=
            K.allProperCosetVertex_support_inter
              hadm hgen hret x C E.1 hC hE
          exact ⟨C ∩ E.1, hStrict, hCE⟩

/-- The source of an edge actually *leaving* a selected maximal
C-constituent is supported over some strict D⊊C.
The target's lack of C-support forces the edge label to be
outside C, because C-labelled edges are fully completed
in every selected tagged C-copy. -/
theorem allProperCoset_maximal_support_exit_step_lower
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCnonempty : C.Nonempty)
    (hMax :
      ∀ (E : Finset ι)
        (hEP : E ∈ (allProperCosetFamily A).alphabets),
        C ⊆ E → E = C)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (hSourceC :
      K.MultiCosetVertexSupported
        (allProperCosetFamily A) hadm hgen hret C
        ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).source e))
    (hTargetOff :
      ¬ K.MultiCosetVertexSupported
        (allProperCosetFamily A) hadm hgen hret C
        ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).target e)) :
    ∃ D : Finset ι,
      D ⊂ C ∧
      K.MultiCosetVertexSupported
        (allProperCosetFamily A) hadm hgen hret D
        ((K.multiCosetEGraph
          (allProperCosetFamily A) hadm hgen hret).source e) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  have hOutside : signedBase (G.label e) ∉ C := by
    intro hLabel
    obtain ⟨hCP', p, hp⟩ := hSourceC
    obtain ⟨q, _, hq⟩ :=
      K.multiCoset_selected_B_step_stays_in_coset
        P hadm hgen hret C hCP' p e hp.symm hLabel
    exact hTargetOff ⟨hCP', q, hq.symm⟩
  exact K.allProperCoset_maximal_support_exit_label_lower
    hadm hgen hret C hCP hCnonempty hMax
    e hSourceC hOutside

end CayleySubgraphSpec
end ABO
end PSTSEPPA
