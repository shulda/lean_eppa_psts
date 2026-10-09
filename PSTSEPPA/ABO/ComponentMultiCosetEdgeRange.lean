import PSTSEPPA.ABO.ComponentMultiCosetPathImage
import PSTSEPPA.ABO.ComponentMultiCosetHom
import PSTSEPPA.ABO.ComponentAttachmentRange
import PSTSEPPA.ABO.MultiCosetParentFold

/-!
# Exact B-labelled directed-edge image of a local multi-coset extension

For a literal B-component L of an admissible skeleton K, we already
have an injective labelled graph morphism from CE(G,L;P) into CE(G,K;P).

Here we address the edge universe. Every edge of the local extension
is B-labelled. Conversely a B-labelled edge in the global extension
whose source belongs to the selected parent B-component has a
preimage in the local extension.

The two raw cases are intentionally separate:
* A completed C-edge lifts using the component-tagged coset range lemma.
* An old skeleton edge with label in B lifts using the actual
  skeleton B-path component, not merely its ambient group coordinate.

Thus no labels outside B are accidentally included in the local
edge component; directed inverse tokens and repeated generators are
handled by the checked edge quotient itself.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every directed edge of the local lower-family multi-CE has its
signed label inside the parent alphabet B. This includes original
skeleton edges and every completed coset edge. -/
theorem componentMultiCoset_local_label_mem
    (B : Finset ι) (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadmL : (K.subalphabetComponentSubgraph B root).AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
      P hadmL hgen hret) :
    signedBase
      (((K.subalphabetComponentSubgraph B root).multiCosetEGraph
        P hadmL hgen hret).label e) ∈ B := by
  let L := K.subalphabetComponentSubgraph B root
  induction e using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨C, edge⟩
      cases edge with
      | inl old =>
          change signedBase old.1.1.2 ∈ B
          exact L.label_mem old.1.1 old.1.2
      | inr completed =>
          change signedBase completed.2.1 ∈ B
          exact (P.proper C.1 C.2).subset completed.2.2

/-- Every completed C-edge of the global multi-CE whose component
index belongs to the selected parent B-component is the image of a
completed edge of the local multi-CE. -/
theorem componentMultiCoset_completed_edge_in_range
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex) (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (p : K.AttachedCosetVertex C)
    (s : {s : SignedLabel ι // signedBase s ∈ C})
    (hparent :
      K.componentIndexMap C B (P.proper C hCP).subset p.1 =
        K.componentClass B root) :
    ∃ e : (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret,
      (K.componentMultiCosetHom B hBA root P hadm hgen hret).onEdge e =
        K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C hCP
          (Sum.inr (p, s)) := by
  let L := K.subalphabetComponentSubgraph B root
  let hadmL := K.subalphabetComponentSubgraph_admissible hadm B hBA root
  obtain ⟨q, hq⟩ :=
    K.componentSubgraphAttachedMap_surj_of_parent
      B C (P.proper C hCP).subset root p hparent
  refine ⟨L.multiCosetEdgeInclude P hadmL hgen hret C hCP
      (Sum.inr (q, s)), ?_⟩
  change
    K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C hCP
      (Sum.inr (K.componentSubgraphAttachedMap B C
        (P.proper C hCP).subset root q, s)) =
    K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C hCP
      (Sum.inr (p, s))
  rw [hq]

/-- Every B-labelled old skeleton edge with its source in the
chosen intrinsic B-component has a local directed-edge preimage,
even when its label lies outside the chosen constituent C. -/
theorem componentMultiCoset_old_edge_in_range
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex) (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (old : K.OutsideEdge C)
    (hB : signedBase old.1.1.2 ∈ B)
    (hroot : K.SubalphabetReachable B root ((K.toEGraph).source old.1)) :
    ∃ e : (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret,
      (K.componentMultiCosetHom B hBA root P hadm hgen hret).onEdge e =
        K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C hCP
          (Sum.inl old) := by
  let L := K.subalphabetComponentSubgraph B root
  let hadmL := K.subalphabetComponentSubgraph_admissible hadm B hBA root
  let lifted := K.componentLiftEdge B root old.1 hB hroot
  let localOld : L.OutsideEdge C := ⟨lifted, old.2⟩
  refine ⟨L.multiCosetEdgeInclude P hadmL hgen hret C hCP
      (Sum.inl localOld), ?_⟩
  change
    K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C hCP
      (K.componentSubgraphSingleCosetEdgeMap B C
        (P.proper C hCP).subset root (Sum.inl localOld)) =
    K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C hCP
      (Sum.inl old)
  apply congrArg
    (K.multiCosetEdgeInclude (P.intoLarger hBA) hadm hgen hret C hCP)
  apply congrArg Sum.inl
  apply Subtype.ext
  exact K.subalphabetComponentSubgraphHom_liftEdge
    B root old.1 hB hroot

/-- B-labelled global multi-CE edges with source in the selected
parent B-component are exactly lifted local edges: the critical
surjectivity direction for the intrinsic B-component graph. -/
theorem componentMultiCoset_B_edge_in_range_of_parent
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex) (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (P.intoLarger hBA) hadm hgen hret)
    (hB :
      signedBase ((K.multiCosetEGraph (P.intoLarger hBA)
        hadm hgen hret).label e) ∈ B)
    (hparent :
      (K.multiCosetVertexToParent (P.intoLarger hBA)
        hadm hgen hret B (componentFamily_subset_parent B hBA P)
        ((K.multiCosetEGraph (P.intoLarger hBA)
          hadm hgen hret).source e)).1 =
        K.componentClass B root) :
    ∃ localEdge :
      (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret,
      (K.componentMultiCosetHom B hBA root P hadm hgen hret).onEdge localEdge = e := by
  induction e using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨C, edge⟩
      cases edge with
      | inl old =>
          change signedBase old.1.1.2 ∈ B at hB
          have hclass :
              K.componentClass B ((K.toEGraph).source old.1) =
                K.componentClass B root := by
            change K.componentIndexMap C.1 B
              (P.proper C.1 C.2).subset
              (K.componentClass C.1 ((K.toEGraph).source old.1)) =
                K.componentClass B root at hparent
            rwa [K.componentIndexMap_class] at hparent
          have hroot : K.SubalphabetReachable B root
              ((K.toEGraph).source old.1) :=
            K.subalphabetReachable_symm B
              ((K.componentClass_eq_iff B _ _).mp hclass)
          exact K.componentMultiCoset_old_edge_in_range
            B hBA root P hadm hgen hret C.1 C.2 old hB hroot
      | inr completed =>
          have hp :
              K.componentIndexMap C.1 B
                (P.proper C.1 C.2).subset completed.1 =
                K.componentClass B root := by
            change K.componentIndexMap C.1 B
                (P.proper C.1 C.2).subset completed.1 =
                  K.componentClass B root at hparent
            exact hparent
          exact K.componentMultiCoset_completed_edge_in_range
            B hBA root P hadm hgen hret
            C.1 C.2 completed.1 completed.2 hp

/-- Exact characterization of the image on directed edges. A global
directed edge comes from the local multi-CE iff it has label in B
and its source is in the image of the local vertex morphism.
Neither condition can be replaced by ambient coset equality. -/
theorem componentMultiCoset_edge_range_iff
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex) (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (P.intoLarger hBA) hadm hgen hret) :
    (∃ localEdge :
      (K.subalphabetComponentSubgraph B root).MultiCosetEdgeVertexIncidenceQuotient
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret,
      (K.componentMultiCosetHom B hBA root P hadm hgen hret).onEdge localEdge = e) ↔
    (signedBase ((K.multiCosetEGraph (P.intoLarger hBA)
       hadm hgen hret).label e) ∈ B ∧
      ∃ localVertex :
        (K.subalphabetComponentSubgraph B root).MultiCosetVertex
          P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
          hgen hret,
        (K.componentMultiCosetHom B hBA root P hadm hgen hret).onVertex
          localVertex =
          (K.multiCosetEGraph (P.intoLarger hBA)
            hadm hgen hret).source e) := by
  let L := K.subalphabetComponentSubgraph B root
  let hadmL := K.subalphabetComponentSubgraph_admissible hadm B hBA root
  let f := K.componentMultiCosetHom B hBA root P hadm hgen hret
  constructor
  · rintro ⟨localEdge, hEdge⟩
    constructor
    · rw [← hEdge, f.map_label]
      exact K.componentMultiCoset_local_label_mem B root P hadmL hgen hret localEdge
    · refine ⟨(L.multiCosetEGraph P hadmL hgen hret).source localEdge, ?_⟩
      rw [← hEdge]
      exact (f.map_source localEdge).symm
  · rintro ⟨hlabel, ⟨localVertex, hVertex⟩⟩
    have hparent :
        (K.multiCosetVertexToParent (P.intoLarger hBA)
          hadm hgen hret B (componentFamily_subset_parent B hBA P)
          ((K.multiCosetEGraph (P.intoLarger hBA)
            hadm hgen hret).source e)).1 =
          K.componentClass B root := by
      rw [← hVertex]
      exact K.componentMultiCosetVertexMap_parent_index
        B _ root P hadm hgen hret localVertex
    exact K.componentMultiCoset_B_edge_in_range_of_parent
      B hBA root P hadm hgen hret e hlabel hparent

end CayleySubgraphSpec
end ABO
end PSTSEPPA
