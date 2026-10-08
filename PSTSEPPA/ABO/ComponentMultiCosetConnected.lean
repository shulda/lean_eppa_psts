import PSTSEPPA.ABO.MultiCosetParentComponentExact
import PSTSEPPA.ABO.ComponentFullCosetEmbedding
import PSTSEPPA.ABO.ComponentSubgraphAdmissibility

/-!
# B-connectedness of the multi-coset extension of one B-component

Let L be the literal B-path-component of an admissible A-skeleton K,
with B proper in A. Every vertex of L is connected to every other
by a realised B-word path.

For any selected family P of proper subalphabets of B, the full
multi-coset E-graph CE(G,L;P) is likewise B-connected. We use the
already checked exact criterion for B-path reachability in a multi-CE
via its intrinsic B-parent component index. But L has only one such
index, by actual connectivity of its original skeleton.

No nonempty-family assumption is needed in the statement: when P
is empty, the disjoint-union multi-CE has no vertices and the
universal pairwise-connectivity property holds vacuously.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The lower-family multi-coset extension of one actual B-component
is B-path-connected on all its quotient vertices. -/
theorem componentMultiCosetEGraph_B_connected
    (B : Finset ι) (hBA : B ⊂ A)
    (root : K.Vertex)
    (P : CosetFamilySpec B)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (p q : (K.subalphabetComponentSubgraph B root).MultiCosetVertex
      P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
      hgen hret) :
    ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      ((K.subalphabetComponentSubgraph B root).multiCosetEGraph
        P (K.subalphabetComponentSubgraph_admissible hadm B hBA root)
        hgen hret).Follows p w q := by
  let L := K.subalphabetComponentSubgraph B root
  let hadmL := K.subalphabetComponentSubgraph_admissible hadm B hBA root
  have hPsub : ∀ C ∈ P.alphabets, C ⊆ B := by
    intro C hCP
    exact (P.proper C hCP).subset
  apply (L.multiCosetEGraph_B_reachable_iff_parent_index
    P hadmL hgen hret B hPsub p q).2
  obtain ⟨x, hx⟩ :=
    L.componentClass_surjective B
      (L.multiCosetVertexToParent P hadmL hgen hret B hPsub p).1
  obtain ⟨y, hy⟩ :=
    L.componentClass_surjective B
      (L.multiCosetVertexToParent P hadmL hgen hret B hPsub q).1
  calc
    (L.multiCosetVertexToParent P hadmL hgen hret B hPsub p).1 =
        L.componentClass B x := hx.symm
    _ = L.componentClass B y :=
      K.componentSubgraph_one_component B root x y
    _ = (L.multiCosetVertexToParent P hadmL hgen hret B hPsub q).1 := hy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
