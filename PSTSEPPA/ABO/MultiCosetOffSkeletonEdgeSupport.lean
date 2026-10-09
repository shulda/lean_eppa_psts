import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.MultiCosetEGraph
import PSTSEPPA.ABO.StandardCosetFamily

/-!
# Local coset patches supporting edges away from the skeleton

The raw signed edges of a multi-coset extension are either
old skeleton edges or completed attached-coset edges.
The corresponding *quotient* source map is not globally
injective in ambient Cayley coordinates.

Nevertheless, whenever a quotient directed edge has its source
outside the embedded original skeleton, it must have a
representation as a genuine completed edge of some selected
tagged C-coset. In particular a B-labelled such edge is
labelled in the intersection C∩B.

This is the first exact graph-theoretic local-patch lemma for
off-skeleton B-components in ABO Definition 3.22. It avoids
assuming the cluster property and makes no claim about
assembled whole-component cluster geometry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An oriented edge of a multi-CE whose source lies outside
the embedded skeleton is represented by a *completed* signed
edge of one constituent tagged coset, not by an old skeleton
edge. The conclusion retains exact edge-token equality. -/
theorem multiCoset_off_skeleton_edge_is_completed
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret)
    (hOff : ∀ x : K.Vertex,
      (K.skeletonToMultiCosetHom P hadm hgen hret D hDP).onVertex x ≠
        (K.multiCosetEGraph P hadm hgen hret).source e) :
    ∃ (C : Finset ι) (hCP : C ∈ P.alphabets)
      (p : K.AttachedCosetVertex C)
      (s : {s : SignedLabel ι // signedBase s ∈ C}),
      e = K.multiCosetEdgeInclude P hadm hgen hret
        C hCP (Sum.inr (p, s)) := by
  induction e using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨C, edge⟩
      cases edge with
      | inr completed =>
          exact ⟨C.1, C.2, completed.1, completed.2, rfl⟩
      | inl old =>
          let x : K.Vertex := (K.toEGraph).source old.1
          have hx :
              (K.skeletonToMultiCosetHom
                P hadm hgen hret D hDP).onVertex x =
              (K.multiCosetEGraph P hadm hgen hret).source
                (K.multiCosetEdgeInclude P hadm hgen hret
                  C.1 C.2 (Sum.inl old)) := by
            change
              K.multiCosetInclude P hadm hgen hret D hDP
                (K.attachedOfSkeletonVertex D x) =
              K.multiCosetInclude P hadm hgen hret C.1 C.2
                (K.attachedOfSkeletonVertex C.1 x)
            exact K.skeletonToMultiCosetHom_vertex_independent
              P hadm hgen hret D C.1 hDP C.2 x
          exact False.elim (hOff x hx)

/-- If an off-skeleton outgoing edge has label in B, it lies
in an actual completed coset alphabet C meeting B in that
very label. This exhibits the local (B∩C)-patch from which
the off-skeleton B-component structure must be assembled. -/
theorem multiCoset_off_skeleton_B_edge_in_intersection_patch
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι) (hDP : D ∈ P.alphabets)
    (B : Finset ι)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret)
    (hB : signedBase
      ((K.multiCosetEGraph P hadm hgen hret).label e) ∈ B)
    (hOff : ∀ x : K.Vertex,
      (K.skeletonToMultiCosetHom P hadm hgen hret D hDP).onVertex x ≠
        (K.multiCosetEGraph P hadm hgen hret).source e) :
    ∃ (C : Finset ι) (hCP : C ∈ P.alphabets)
      (p : K.AttachedCosetVertex C)
      (s : {s : SignedLabel ι // signedBase s ∈ C}),
      signedBase s.1 ∈ C ∩ B ∧
      e = K.multiCosetEdgeInclude P hadm hgen hret
        C hCP (Sum.inr (p, s)) := by
  obtain ⟨C, hCP, p, s, he⟩ :=
    K.multiCoset_off_skeleton_edge_is_completed
      P hadm hgen hret D hDP e hOff
  refine ⟨C, hCP, p, s, ?_, he⟩
  refine Finset.mem_inter.mpr ⟨s.2, ?_⟩
  rw [he] at hB
  exact hB

end CayleySubgraphSpec
end ABO
end PSTSEPPA
