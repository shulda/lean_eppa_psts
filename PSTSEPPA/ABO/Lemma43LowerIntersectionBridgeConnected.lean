import PSTSEPPA.ABO.BridgeFreenessInterface
import PSTSEPPA.ABO.ComponentMultiCosetHom
import PSTSEPPA.ABO.MultiCosetFamilyInclusion
import PSTSEPPA.ABO.BridgeFreenessCoatomTransfer

/-!
# ABO Lemma 4.3: bridge-free connectedness of lower-stage intersections

This module follows the EXISTING PUBLISHED proof of ABO I, Lemma 4.3,
specifically the step on PDF p.36:

  "Bridge freeness of CE(H,A_i;P_{A_i}) (assumption (1))
   implies that B_i ∩ CE(H,A_i;P_{A_i}) is connected."

No novel whole-component cluster argument is claimed here.
The needed lower-stage embedding is built from the ACTUAL original
intrinsic subalphabet component and its component-tagged multi-coset
graph, followed by the certified injection of a lower proper coset
family into the whole proper family.

The signed Cayley ambient map commutes with this embedding, on REAL
old/fresh vertices and edge tokens. Hence any B-word path between
two lower-stage points in the upper multiCE gives a B-coset relation
in the ambient group. The ASSUMED lower-stage bridge-freeness
reflects this relation to a REAL B-word path inside the lower stage.
Mapping the latter signed path back to the original upper stage
provides connectedness *inside the intersection*.

The bridge-freeness assumption is not hidden or proved here: it is
EXACTLY the lower-rank inductive hypothesis in ABO Lemma 4.3.
Likewise the properness D ⊊ C of the intersection alphabet is
explicit. The source obtains this in its no-skeleton-intersection
branch; the more global Lemma 4.3 remains a separate next gate.

All oriented signed edge tokens, original missing old edges, and
intrinsic component tags are preserved. Ambient coordinate
equality is never used to identify distinct tagged quotient points.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

/-- The lower-rank full proper coset family is literally a subfamily
of the parent's full proper family. This uses strict subalphabet
containment, including empty alphabets and equality edge cases. -/
theorem lowerAllProperFamily_subset
    (C : Finset ι) (hCA : C ⊂ A) :
    ((allProperCosetFamily C).intoLarger hCA).alphabets ⊆
      (allProperCosetFamily A).alphabets := by
  intro D hD
  change D ∈ (allProperCosetFamily C).alphabets at hD
  exact (mem_allProperCosetFamily A D).mpr
    (lt_trans ((mem_allProperCosetFamily C D).mp hD) hCA)

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The genuine lower-rank coset-extension inclusion used in ABO
Lemma 4.3: the full proper extension of one ORIGINAL intrinsic
C-component, as an actual labelled graph morphism into the
full proper extension of K.

Both steps preserve actual old/fresh signed edges and
the precise quotient gluing of component-tagged cosets. -/
noncomputable def lowerComponentToFullMultiCosetHom
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    LabelledGraphHom
      ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret).toLabelledGraph
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).toLabelledGraph :=
  (K.multiCosetFamilyHom
    ((allProperCosetFamily C).intoLarger hCA)
    (allProperCosetFamily A)
    hadm hgen hret (lowerAllProperFamily_subset C hCA)).comp
    (K.componentMultiCosetHom C hCA root
      (allProperCosetFamily C) hadm hgen hret)

/-- This lower-stage embedding is injective on actual TAGGED vertices.
Do not replace it by any assertion that the upper coset extension
is globally embedded into the ambient Cayley graph. -/
theorem lowerComponentToFullMultiCosetHom_vertex_injective
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Function.Injective
      (K.lowerComponentToFullMultiCosetHom
        C hCA root hadm hgen hret).onVertex := by
  exact
    (K.multiCosetFamilyVertexMap_injective
      ((allProperCosetFamily C).intoLarger hCA)
      (allProperCosetFamily A) hadm hgen hret
      (lowerAllProperFamily_subset C hCA)).comp
      (K.componentMultiCosetHom_vertex_injective
        C hCA root (allProperCosetFamily C)
        hadm hgen hret)

/-- The LOWER and UPPER canonical ambient Cayley coordinates
of the same actual tagged local quotient point are EQUAL.
This compatibility is stronger than an abstract graph embedding
and is the exact geometric reason that lower bridge-freeness
applies to a B-path witnessed in the whole extension. -/
theorem lowerComponentToFullMultiCosetHom_ambient_value
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (x : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret) :
    K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret
      ((K.lowerComponentToFullMultiCosetHom
        C hCA root hadm hgen hret).onVertex x) =
    (K.subalphabetComponentSubgraph C root).multiCosetAmbientValue
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret x := by
  change
    K.multiCosetAmbientValue (allProperCosetFamily A)
      hadm hgen hret
      (K.multiCosetFamilyVertexMap
        ((allProperCosetFamily C).intoLarger hCA)
        (allProperCosetFamily A)
        hadm hgen hret (lowerAllProperFamily_subset C hCA)
        (K.componentMultiCosetVertexMap C hCA root
          (allProperCosetFamily C) hadm hgen hret x)) = _
  rw [K.multiCosetFamilyVertexMap_ambient_value]
  exact K.componentMultiCosetVertexMap_ambient_value
    C hCA root (allProperCosetFamily C) hadm hgen hret x

/-- SOURCE Lemma 4.3, bridge-free intersection step:
if two tagged lower-stage vertices are B-connected in the
ACTUAL UPPER full multiCE, the lower inductive
bridge-freeness hypothesis supplies a REAL B-path inside
the LOWER proper-coset extension.

We also produce its signed path image in the upper extension,
showing that connectivity is witnessed *within the image*
of the embedded lower stage, not through imaginary old
edges or through an ambient Cayley shortcut. -/
theorem lowerComponent_bridgeFree_reflect_upper_path
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι) (hDC : D ⊂ C)
    (hBridge :
      (K.subalphabetComponentSubgraph C root).MultiCosetBridgeFree
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret)
    (u v : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret)
    (hUpperPath :
      ∃ w : LabelWord ι, LabelWord.Uses D w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex u)
          w
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex v)) :
    ∃ w : LabelWord ι, LabelWord.Uses D w ∧
      ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret).Follows u w v ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex u)
          w
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex v) := by
  let U := K.multiCosetEGraph (allProperCosetFamily A)
    hadm hgen hret
  let J := K.lowerComponentToFullMultiCosetHom
    C hCA root hadm hgen hret
  obtain ⟨w, hw, hp⟩ := hUpperPath
  have hMapped :
      (cayleyGraph gen).toEGraph.Follows
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret (J.onVertex u))
        w
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret (J.onVertex v)) :=
    hp.map (K.multiCosetAmbientHom
      (allProperCosetFamily A) hadm hgen hret)
  have hCanonical :=
    (cayleyGraph gen).follows_followWord
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret (J.onVertex u)) w
  have heq :
      (cayleyGraph gen).followWord
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret (J.onVertex u)) w =
      K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret (J.onVertex v) :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      hCanonical hMapped
  have hCosetUpper :
      K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret (J.onVertex v) ∈
      generatedLeftCoset gen D
        (K.multiCosetAmbientValue (allProperCosetFamily A)
          hadm hgen hret (J.onVertex u)) :=
    (mem_generatedLeftCoset_iff_subalphabetReachable
      gen D _ _).mpr ⟨w, hw, heq⟩
  have hCosetLower :
      (K.subalphabetComponentSubgraph C root).multiCosetAmbientValue
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret v ∈
      generatedLeftCoset gen D
        ((K.subalphabetComponentSubgraph C root).multiCosetAmbientValue
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C hCA root) hgen hret u) := by
    simpa only [
      K.lowerComponentToFullMultiCosetHom_ambient_value
        C hCA root hadm hgen hret u,
      K.lowerComponentToFullMultiCosetHom_ambient_value
        C hCA root hadm hgen hret v] using hCosetUpper
  obtain ⟨q, hqD, hLowerPath⟩ :=
    hBridge.2 D hDC u v hCosetLower
  exact ⟨q, hqD, hLowerPath, hLowerPath.map J⟩

/-- Literal "B_i ∩ lower extension is connected" step of
the published ABO Lemma 4.3: for any ambient upper B-component
root z, ALL lower extension vertices whose actual images lie
in this B-component are mutually joined by a genuine
B-path INSIDE the embedded lower extension.

The two input witnesses may involve arbitrary differently
labelled signed words. The lower path is produced anew from
bridge-freeness, and its upper image never exits the
lower embedded stage. -/
theorem lowerComponent_bridgeFree_intersection_connected
    (C : Finset ι) (hCA : C ⊂ A)
    (root : K.Vertex)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι) (hDC : D ⊂ C)
    (hBridge :
      (K.subalphabetComponentSubgraph C root).MultiCosetBridgeFree
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (u v : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
      (allProperCosetFamily C)
      (K.subalphabetComponentSubgraph_admissible
        hadm C hCA root) hgen hret)
    (hu :
      ∃ w : LabelWord ι, LabelWord.Uses D w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows z w
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex u))
    (hv :
      ∃ w : LabelWord ι, LabelWord.Uses D w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows z w
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex v)) :
    ∃ w : LabelWord ι, LabelWord.Uses D w ∧
      ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C hCA root) hgen hret).Follows u w v ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex u)
          w
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex v) := by
  let U := K.multiCosetEGraph (allProperCosetFamily A)
    hadm hgen hret
  obtain ⟨p, hpD, hp⟩ := hu
  obtain ⟨q, hqD, hq⟩ := hv
  have hUpper :
      ∃ w : LabelWord ι, LabelWord.Uses D w ∧
        U.Follows
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex u)
          w
          ((K.lowerComponentToFullMultiCosetHom
            C hCA root hadm hgen hret).onVertex v) :=
    ⟨PSTS.SignedWord.inv p ++ q,
      (LabelWord.uses_append D _ _).mpr ⟨hpD.inv, hqD⟩,
      U.follows_append (U.follows_inverse hp) hq⟩
  exact K.lowerComponent_bridgeFree_reflect_upper_path
    C hCA root hadm hgen hret
    D hDC hBridge u v hUpper

end CayleySubgraphSpec
end ABO
end PSTSEPPA
