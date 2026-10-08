import PSTSEPPA.ABO.MultiCosetParentHom
import PSTSEPPA.ABO.SingleCosetComponentInvariant

/-!
# Intrinsic B-path separation in a multi-coset extension

Suppose all selected extension alphabets lie inside B. The canonical
folding morphism from the full multi-coset E-graph into the single-B
coset extension preserves every signed path and its word.

In the single-B extension every actual B-labelled path preserves
its intrinsic B-component tag. Consequently the same tag cannot
change along a B-labelled path in the multi-coset extension.

The result is entirely about actual realised graph paths and
component-indexed coset copies. It does not infer B-connectivity
from ambient group coordinates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every actual B-path in a multi-coset extension whose alphabets
lie in B preserves the B-component tag of its parent-coset image. -/
theorem multiCoset_follows_parent_B_index
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    {x y : K.MultiCosetVertex P hadm hgen hret}
    {w : LabelWord ι}
    (hpath : (K.multiCosetEGraph P hadm hgen hret).Follows x w y)
    (hw : LabelWord.Uses B w) :
    (K.multiCosetVertexToParent P hadm hgen hret B hPsub x).1 =
      (K.multiCosetVertexToParent P hadm hgen hret B hPsub y).1 := by
  exact K.singleCosetEGraph_follows_B_preserves_index B
    (hpath.map (K.multiCosetToParentHom P hadm hgen hret B hPsub))
    hw

/-- Source-facing form: distinct parent B-component tags certify
non-reachability by any realised B-labelled path of the glued graph. -/
theorem multiCoset_no_B_path_of_parent_index_ne
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (x y : K.MultiCosetVertex P hadm hgen hret)
    (hneq :
      (K.multiCosetVertexToParent P hadm hgen hret B hPsub x).1 ≠
      (K.multiCosetVertexToParent P hadm hgen hret B hPsub y).1) :
    ¬ ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows x w y := by
  rintro ⟨w, hw, hpath⟩
  exact hneq (K.multiCoset_follows_parent_B_index
    P hadm hgen hret B hPsub hpath hw)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
