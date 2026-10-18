import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion
import PSTSEPPA.ABO.RootedFullBConstituentSaturation
import PSTSEPPA.ABO.CosetIntersections

/-!
# ABO Lemma 4.3: one true tagged B-component slice is B∩C-connected

This is the original source's exact assertion on PDF p.36:
for a B-component Q of the full proper coset extension and
one completed maximal constituent vH[C], the intersection
B_i = Q ∩ vH[C] is a genuine (B ∩ C)-coset subgraph
INSIDE the constituent, and therefore connected by
actual signed words using only B ∩ C.

The key issue is that the upper B-path joining two points
of B_i could leave vH[C], so its word need not use C.
Ambient B-coset equality alone is insufficient to claim
a true B∩C-component in an arbitrary incomplete EGraph.

Here both vertices lie in the SAME original component-tagged
complete C-constituent. The REAL B-path gives an ambient
left B-coset relation, and the exact COMMON old C tag
gives an ambient left C-coset relation. RETRACTABILITY
of the labelled group supplies the genuine identity
G[B] ∩ G[C] = G[B∩C] (source (3.12)), so their
ambient displacement lies in G[B∩C]. Finally, the
already certified exact intrinsic subalphabet-component
theorem of a selected complete C-constituent converts
that displacement back to a REAL signed B∩C-path
in the ORIGINAL uncompleted multi-coset EGraph.

This is a source-facing geometrical prerequisite of
Lemma 4.3, NOT a whole-cluster property assertion,
and does not invent old edges or equate distinct
intrinsic coset tags from their ambient values.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Two vertices of the TRUE tagged constituent slice
B_i=Q∩vH[C] are connected by an ACTUAL signed B∩C
path inside the original full multi-coset extension.

The B-component witness is required to be a REAL
signed path from one fixed component anchor. The C
membership witness remembers its original intrinsic
old skeleton component tag. Both are indispensable. -/
theorem allProperCoset_taggedSlice_B_inter_C_connected
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (z t : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hz :
      z ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c)
    (ht :
      t ∈ K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor C hCP c) :
    ∃ w : LabelWord ι, LabelWord.Uses (B ∩ C) w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w t := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let F := K.multiCosetAmbientHom P hadm hgen hret
  obtain ⟨⟨wz, hwz, hRZ⟩, pZ, hpZTag, hZC⟩ := hz
  obtain ⟨⟨wt, hwt, hRT⟩, pT, hpTTag, hTC⟩ := ht
  have hSameTag : pZ.1 = pT.1 :=
    hpZTag.trans hpTTag.symm
  have hBPath : ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧ G.Follows z w t :=
    ⟨PSTS.SignedWord.inv wz ++ wt,
      (LabelWord.uses_append B _ _).mpr ⟨hwz.inv, hwt⟩,
      G.follows_append (G.follows_inverse hRZ) hRT⟩
  obtain ⟨wB, hwB, hRealB⟩ := hBPath
  have hMapped :
      (cayleyGraph gen).toEGraph.Follows
        (F.onVertex z) wB (F.onVertex t) :=
    hRealB.map F
  have hEndpoint :
      (cayleyGraph gen).followWord (F.onVertex z) wB =
        F.onVertex t :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord (F.onVertex z) wB)
      hMapped
  have hBGroup :
      F.onVertex t ∈ generatedLeftCoset gen B (F.onVertex z) :=
    (mem_generatedLeftCoset_iff_subalphabetReachable
      gen B (F.onVertex z) (F.onVertex t)).mpr
        ⟨wB, hwB, hEndpoint⟩
  have hZValue : F.onVertex z = pZ.2.1 := by
    change K.multiCosetAmbientValue P hadm hgen hret z = _
    rw [hZC]
    rfl
  have hTValue : F.onVertex t = pT.2.1 := by
    change K.multiCosetAmbientValue P hadm hgen hret t = _
    rw [hTC]
    rfl
  have hBGroup' :
      pT.2.1 ∈ generatedLeftCoset gen B pZ.2.1 := by
    simpa only [hZValue, hTValue] using hBGroup
  have hCtagCoset :
      K.componentAmbientCoset C pZ.1 =
        generatedLeftCoset gen C pZ.2.1 :=
    K.componentAmbientCoset_eq_generatedLeftCoset_of_member
      C pZ.1 pZ.2.1 pZ.2.2
  have hCGroup' :
      pT.2.1 ∈ generatedLeftCoset gen C pZ.2.1 := by
    rw [← hCtagCoset, hSameTag]
    exact pT.2.2
  have hIntersection :
      generatedLeftCoset gen B pZ.2.1 ∩
        generatedLeftCoset gen C pZ.2.1 =
      generatedLeftCoset gen (B ∩ C) pZ.2.1 :=
    generatedLeftCoset_inter gen hgen hret B C
      pZ.2.1 pZ.2.1 pZ.2.1
      (self_mem_generatedLeftCoset gen B pZ.2.1)
      (self_mem_generatedLeftCoset gen C pZ.2.1)
  have hBCoset :
      pT.2.1 ∈ generatedLeftCoset gen (B ∩ C) pZ.2.1 := by
    rw [← hIntersection]
    exact ⟨hBGroup', hCGroup'⟩
  have hSelectedPath :
      ∃ w : LabelWord ι, LabelWord.Uses (B ∩ C) w ∧
        G.Follows
          (K.multiCosetInclude P hadm hgen hret C hCP pZ)
          w t :=
    (K.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret C hCP
      (B ∩ C) Finset.inter_subset_right pZ t).mpr
      ⟨pT, hSameTag.symm, hBCoset, hTC⟩
  obtain ⟨w, hw, hPath⟩ := hSelectedPath
  rw [← hZC] at hPath
  exact ⟨w, hw, hPath⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
