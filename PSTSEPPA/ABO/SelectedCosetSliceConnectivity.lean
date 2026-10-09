import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents
import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.CosetIntersections
import PSTSEPPA.ABO.SingleCosetConnectivity

/-!
# Intrinsic B-connectivity inside an arbitrary selected C-coset slice

Let B be any alphabet, NOT assumed to be a subset of the selected
constituent alphabet C. Consider two vertices of the SAME intrinsic
component-tagged full C-coset. If they can be joined by any actual
B-word path in the full multi-coset EGraph -- even one that leaves
the selected C-copy in between -- then they can already be joined
inside that same C-copy by a real (B∩C)-word path.

Proof: project the given B-path into the ambient Cayley graph
(without claiming global injectivity); since both vertices carry
the same C-component tag, they also differ by a C-group element.
Retractability gives G[B]∩G[C]=G[B∩C]. The genuine completed
C-coset connectivity theorem then constructs the B∩C-path
inside the original tagged C-copy. The converse is immediate.

This is the exact *component-slice* form of an important assertion
in the first paragraph of the forward induction proof: when a
B-component intersects an attached C-constituent, the slice inside
one C-tag is an intrinsic (B∩C)-component. No ambient embedding,
bridge freeness, or cluster-property hypothesis is needed for
this special, fully completed constituent slice.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Within a fixed tagged C-coset, global B-reachability of two
vertices is equivalent to ambient B∩C-coset membership of their
coordinates. This holds even when B is incomparable with C and
the witnessing global B-path exits that C-copy along the way. -/
theorem multiCoset_selected_C_slice_B_reachable_iff_inter_coset
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hCP : C ∈ P.alphabets)
    (p q : K.AttachedCosetVertex C)
    (hIdx : p.1 = q.1) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C hCP p)
        w
        (K.multiCosetInclude P hadm hgen hret C hCP q)) ↔
    q.2.1 ∈ generatedLeftCoset gen (B ∩ C) p.2.1 := by
  let G := K.multiCosetEGraph P hadm hgen hret
  constructor
  · rintro ⟨w, hw, hpath⟩
    have hMapped :
        (cayleyGraph gen).toEGraph.Follows p.2.1 w q.2.1 := by
      have hmapped :=
        hpath.map (K.multiCosetAmbientHom P hadm hgen hret)
      change (cayleyGraph gen).toEGraph.Follows
        (K.multiCosetAmbientValue P hadm hgen hret
          (K.multiCosetInclude P hadm hgen hret C hCP p))
        w
        (K.multiCosetAmbientValue P hadm hgen hret
          (K.multiCosetInclude P hadm hgen hret C hCP q)) at hmapped
      simpa only [K.multiCosetAmbientValue_include] using hmapped
    have hCanonical :=
      (cayleyGraph gen).follows_followWord p.2.1 w
    have hVal :
        (cayleyGraph gen).followWord p.2.1 w = q.2.1 :=
      (cayleyGraph gen).toEGraph.follows_right_unique
        hCanonical hMapped
    have hB :
        p.2.1⁻¹ * q.2.1 ∈ generatedSubgroup gen B :=
      (mem_generatedLeftCoset_iff_subalphabetReachable
        gen B p.2.1 q.2.1).mpr ⟨w, hw, hVal⟩
    have hqC : q.2.1 ∈ K.componentAmbientCoset C p.1 := by
      rw [hIdx]
      exact q.2.2
    have hC :
        p.2.1⁻¹ * q.2.1 ∈ generatedSubgroup gen C :=
      K.componentAmbientCoset_relative_mem C p.1 p.2.2 hqC
    have hInter :
        p.2.1⁻¹ * q.2.1 ∈ generatedSubgroup gen (B ∩ C) := by
      have hinf :
          p.2.1⁻¹ * q.2.1 ∈
            generatedSubgroup gen B ⊓ generatedSubgroup gen C :=
        ⟨hB, hC⟩
      rwa [generatedSubgroup_inf gen hgen hret B C]
    exact hInter
  · intro hInter
    obtain ⟨w, hw, hpath⟩ :=
      (K.multiCoset_selected_C_subalphabet_B_component_exact
        P hadm hgen hret C hCP (B ∩ C)
        Finset.inter_subset_right p
        (K.multiCosetInclude P hadm hgen hret C hCP q)).mpr
          ⟨q, hIdx.symm, hInter, rfl⟩
    exact ⟨w, hw.mono Finset.inter_subset_left, hpath⟩

/-- The same result stated purely in realised signed-word paths:
between two points of one selected tagged C-copy, allowing
arbitrary global B-paths adds NO reachability beyond genuine
(B∩C)-paths wholly inside that copy. -/
theorem multiCoset_selected_C_slice_B_reachable_iff_inter_reachable
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι) (hCP : C ∈ P.alphabets)
    (p q : K.AttachedCosetVertex C)
    (hIdx : p.1 = q.1) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C hCP p)
        w
        (K.multiCosetInclude P hadm hgen hret C hCP q)) ↔
    (∃ w : LabelWord ι, LabelWord.Uses (B ∩ C) w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C hCP p)
        w
        (K.multiCosetInclude P hadm hgen hret C hCP q)) := by
  constructor
  · intro hB
    have hInterCoset :=
      (K.multiCoset_selected_C_slice_B_reachable_iff_inter_coset
        P hadm hgen hret B C hCP p q hIdx).mp hB
    exact
      (K.multiCoset_selected_C_subalphabet_B_component_exact
        P hadm hgen hret C hCP (B ∩ C)
        Finset.inter_subset_right p
        (K.multiCosetInclude P hadm hgen hret C hCP q)).mpr
          ⟨q, hIdx.symm, hInterCoset, rfl⟩
  · rintro ⟨w, hw, hpath⟩
    exact ⟨w, hw.mono Finset.inter_subset_left, hpath⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
