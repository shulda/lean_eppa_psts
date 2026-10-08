import PSTSEPPA.ABO.ComponentCosetNaturality
import PSTSEPPA.ABO.MultiCosetVertexQuotient
import PSTSEPPA.ABO.ComponentSubgraphAdmissibility

/-!
# The multi-coset vertex map induced by an intrinsic component inclusion

Let L be the actual B-component of an admissible A-skeleton K,
with B ⊂ A. A family P of proper subalphabets of B is also a
family of proper subalphabets of A.

Every intrinsic C-component of L, C∈P, injects into the
corresponding C-component of K. Naturality of these attachments
preserves the exact (C∩D)-support gluing relation.

We therefore construct a well-defined map of multi-coset quotient
VERTICES
  CE(G,L;P) → CE(G,K;P)
which preserves ambient group coordinates and agrees with all
constituent C-coset inclusions and original skeleton points.

This file does not yet assert that this quotient map is injective
or that it extends to a labelled edge morphism. Reflection of
intersection support and edge compatibility are separate gates
towards the full local comparison in ABO Lemma 3.20.
-/

namespace PSTSEPPA
namespace ABO

variable {ι : Type*}

/-- View a family of proper subalphabets of B as a family of
proper subalphabets of A whenever B is itself proper in A. -/
def CosetFamilySpec.intoLarger
    {B A : Finset ι}
    (P : CosetFamilySpec B) (hBA : B ⊂ A) : CosetFamilySpec A where
  alphabets := P.alphabets
  proper := by
    intro C hCP
    exact lt_trans (P.proper C hCP) hBA

@[simp]
theorem CosetFamilySpec.mem_intoLarger
    {B A : Finset ι}
    (P : CosetFamilySpec B) (hBA : B ⊂ A)
    (C : Finset ι) :
    C ∈ (P.intoLarger hBA).alphabets ↔ C ∈ P.alphabets :=
  Iff.rfl

variable {Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The actual vertex quotient of the local B-component extension
maps into the corresponding whole-K multi-coset vertex quotient.
The two sides use the SAME selected proper alphabets P. -/
noncomputable def componentMultiCosetVertexMap
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (x :
      (K.subalphabetComponentSubgraph B root).MultiCosetVertex
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret) :
    K.MultiCosetVertex (P.intoLarger hBA) hadm hgen hret :=
  Quotient.liftOn x
    (fun raw =>
      K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret
        raw.1.1 raw.1.2
        (K.componentSubgraphAttachedMap B raw.1.1
          (P.proper raw.1.1 raw.1.2).subset root raw.2))
    (by
      intro p q hpq
      apply Quotient.sound
      change K.ShareIntersectionSupport p.1.1 q.1.1
        (K.componentSubgraphAttachedMap B p.1.1
          (P.proper p.1.1 p.1.2).subset root p.2)
        (K.componentSubgraphAttachedMap B q.1.1
          (P.proper q.1.1 q.1.2).subset root q.2)
      change (K.subalphabetComponentSubgraph B root).ShareIntersectionSupport
        p.1.1 q.1.1 p.2 q.2 at hpq
      exact K.componentSubgraphShareIntersectionSupport_map
        B p.1.1 q.1.1
        (P.proper p.1.1 p.1.2).subset
        (P.proper q.1.1 q.1.2).subset
        root p.2 q.2 hpq)

/-- The vertex map is literally the checked injection on each
individual C-coset constituent. -/
theorem componentMultiCosetVertexMap_include
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (p : (K.subalphabetComponentSubgraph B root).AttachedCosetVertex C) :
    K.componentMultiCosetVertexMap B hBA root P hadm hgen hret
        ((K.subalphabetComponentSubgraph B root).multiCosetInclude
          P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
          hgen hret C hCP p) =
      K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret
        C hCP
        (K.componentSubgraphAttachedMap B C
          (P.proper C hCP).subset root p) :=
  rfl

/-- The component-wise map preserves the ambient Cayley vertex
coordinate, with no global injectivity assertion in either graph. -/
theorem componentMultiCosetVertexMap_ambient_value
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (x :
      (K.subalphabetComponentSubgraph B root).MultiCosetVertex
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret) :
    K.multiCosetAmbientValue (P.intoLarger hBA) hadm hgen hret
      (K.componentMultiCosetVertexMap B hBA root P hadm hgen hret x) =
    (K.subalphabetComponentSubgraph B root).multiCosetAmbientValue
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret x := by
  induction x using Quotient.inductionOn with
  | h raw =>
      rfl

/-- On actual skeleton vertices, local multi-coset inclusion
agrees with the canonical global inclusion after embedding the
literal B-component back into K. -/
theorem componentMultiCosetVertexMap_skeleton
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (x : (K.subalphabetComponentSubgraph B root).Vertex) :
    K.componentMultiCosetVertexMap B hBA root P hadm hgen hret
        ((K.subalphabetComponentSubgraph B root).multiCosetInclude
          P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
          hgen hret C hCP
          ((K.subalphabetComponentSubgraph B root).attachedOfSkeletonVertex
            C x)) =
      K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret
        C hCP (K.attachedOfSkeletonVertex C
          ((K.subalphabetComponentSubgraphHom B root).onVertex x)) := by
  change K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret
    C hCP
    (K.componentSubgraphAttachedMap B C
      (P.proper C hCP).subset root
      ((K.subalphabetComponentSubgraph B root).attachedOfSkeletonVertex C x)) =
    K.multiCosetInclude (P.intoLarger hBA) hadm hgen hret
      C hCP (K.attachedOfSkeletonVertex C
        ((K.subalphabetComponentSubgraphHom B root).onVertex x))
  rw [K.componentSubgraphAttachedMap_skeleton]

end CayleySubgraphSpec
end ABO
end PSTSEPPA
