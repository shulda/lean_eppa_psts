import PSTSEPPA.ABO.Definition322WholeComponentMinimalSupport
import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.SingleCosetConnectivity
import PSTSEPPA.ABO.MultiCosetVertexSupport

/-!
# ABO Lemma 4.3: actual D-paths follow from minimum component-tagged support

In the published Lemma 4.3 argument (Figure 7), the
minimum support (D_i,u_i) of an entire B_i-slice gives
an actual D_i-word path from a vertex attaining this
support to its skeleton anchor. When a vertex of B_i
also has support (D,u), the source compares the two:
minimum support guarantees D_i ⊆ D AND the exact
original D-component tag compatibility.

Here we prove the directly useful and more precise
consequence for ANY genuine multi-coset extension:

If S has an attained minimum tagged support (M,m), a
vertex z∈S actually attains this minimum, and another
vertex t∈S has ANY actual tagged D-support, then z and
t can be connected by a REAL signed word using only D
in the ORIGINAL uncompleted multi-coset EGraph.

The proof is the literal source construction:
  (1) minimum support gives M⊆D and maps original
      M-component index m to t's D-component index;
  (2) lift z's M-attachment into its canonical completed
      D-attachment (source gluing (3.11));
  (3) z and t now have D-presentations with EXACTLY
      the same intrinsic ORIGINAL D-component tag;
  (4) the already certified full D-constituent
      has an ACTUAL D-signed word path between them,
      and its labelled graph inclusion preserves it.

This is stronger than mere ambient Cayley membership.
No arbitrary global Cayley injection, fake missing old
edge, new axiom or unproved whole-component
cluster-property implication is used. The minimum for S
remains an EXPLICIT published lower-rank induction input.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- From the actual attained minimum tagged support of
a whole vertex set S, find a TRUE signed D-word path
from a minimum-attainment vertex z to ANY other
vertex t ∈ S which is supported over alphabet D.

The source minimum condition supplies both M⊆D
and ORIGINAL component-index equality, which is
essential for the path to exist in the original
tagged quotient rather than just the ambient Cayley graph. -/
theorem minimalTaggedSupport_real_path_to_supported_vertex
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (S : Set (K.MultiCosetVertex P hadm hgen hret))
    (M : Finset ι) (m : K.ComponentIndex M)
    (hMin : K.IsMinimalTaggedSupportFor
      P hadm hgen hret S M m)
    (z : K.MultiCosetVertex P hadm hgen hret)
    (hz : z ∈ S)
    (hzMin : K.HasTaggedSupportAt
      P hadm hgen hret M m z)
    (D : Finset ι) (d : K.ComponentIndex D)
    (t : K.MultiCosetVertex P hadm hgen hret)
    (ht : t ∈ S)
    (htD : K.HasTaggedSupportAt
      P hadm hgen hret D d t) :
    ∃ w : LabelWord ι, LabelWord.Uses D w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows z w t := by
  obtain ⟨hMP, pM, hpMIdx, hpMz⟩ := hzMin
  obtain ⟨hDP, pD, hpDIdx, hpDt⟩ := htD
  obtain ⟨hMD, hMinIndex⟩ :=
    hMin.2 D hDP pD t ht hpDt
  let pZ : K.AttachedCosetVertex D :=
    K.attachedSubalphabetMap M D hMD pM
  have hpZIdx : pZ.1 = pD.1 := by
    calc
      pZ.1 = K.componentIndexMap M D hMD pM.1 := rfl
      _ = K.componentIndexMap M D hMD m :=
        congrArg (K.componentIndexMap M D hMD) hpMIdx
      _ = pD.1 := hMinIndex
  have hpZ : K.multiCosetInclude
      P hadm hgen hret D hDP pZ = z := by
    calc
      K.multiCosetInclude P hadm hgen hret D hDP pZ =
        K.multiCosetInclude P hadm hgen hret M hMP pM :=
        (K.multiCosetInclude_alphabet_mono
          P hadm hgen hret M D hMD hMP hDP pM).symm
      _ = z := hpMz
  obtain ⟨w, hwD, hPath⟩ :=
    K.singleCosetEGraph_connected_on_index D pZ pD hpZIdx
  have hMapped :=
    hPath.map (K.singleCosetToMultiHom
      P hadm hgen hret D hDP)
  change
    (K.multiCosetEGraph P hadm hgen hret).Follows
      (K.multiCosetInclude P hadm hgen hret D hDP pZ)
      w
      (K.multiCosetInclude P hadm hgen hret D hDP pD) at hMapped
  rw [hpZ, hpDt] at hMapped
  exact ⟨w, hwD, hMapped⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
