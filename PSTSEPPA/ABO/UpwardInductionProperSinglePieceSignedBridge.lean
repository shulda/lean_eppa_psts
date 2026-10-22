import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents
import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.CayleyStageProjection

/-!
# Corrected ABO 4.7(iii): off-skeleton PROPER B-cluster with ONE constituent

The published source's upward bridge proof explicitly distinguishes
the proper n=1 B-cluster from the n≥2 proper cluster and the
skeleton-meeting FULL B-coset branch (repair R8).

For a proper cluster supported by a SINGLE selected C constituent,
the substantive geometry is simple but must be EXACT:
two points must genuinely belong to the SAME intrinsic old
C-component-tagged attached C-copy; equality of their ambient G
coordinates does NOT imply equality of their original quotient
vertices when the tags differ.

For B⊆C, the certified exact subalphabet-component theorem
identifies the TRUE directed signed B-component inside that
selected C-copy with its actual full left G[B]-coset, with
the SAME original component tag. This yields an ACTUAL
B-signed word path between the two original quotient points.

We moreover prove that if p is the original ambient B-word
between the group coordinates, the REAL G-multiCE path word
w we have produced has the SAME G group value as p.
That is the exact n=1 branch of the source's bridge-word
reflection, not just existence of an unrelated path.

No globally G-embedded CE assumption, artificial common
core, imaginary old signed edges, quotient tag collapse,
custom axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- PROPER B-cluster of exactly ONE selected C-constituent:
the complete selected C-copy already contains a REAL signed
B-path between any two vertices of the SAME true old
C-component tag whose G coordinates lie in the same G[B]
left coset. This holds even if B is not itself a selected
coset alphabet, and without global CE embeddedness. -/
theorem upwardProperSinglePiece_actualSignedBPath
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (B : Finset ι) (hBC : B ⊆ C)
    (p q : K.AttachedCosetVertex C)
    (hTag : p.1 = q.1)
    (hCoset : q.2.1 ∈ generatedLeftCoset gen B p.2.1) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C hCP p)
        w
        (K.multiCosetInclude P hadm hgen hret C hCP q) := by
  exact (K.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret C hCP B hBC p
        (K.multiCosetInclude P hadm hgen hret C hCP q)).mpr
    ⟨q, hTag, hCoset, rfl⟩

/-- Exact source n=1 UPWARD signed BRIDGE-WORD reflection:
for one original component-tagged selected C constituent,
any original ambient B-word p connecting its two points
can be replaced by a REAL original signed multiCE B-path
word w having the SAME actual G group value as p.

This not only establishes true signed path connectivity,
but also preserves the chronological positive/inverse
word value required in the published 4.7(iii) argument. -/
theorem upwardProperSinglePiece_signedBridgeWord
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (B : Finset ι) (hBC : B ⊆ C)
    (p q : K.AttachedCosetVertex C)
    (hTag : p.1 = q.1)
    (u : LabelWord ι) (hu : LabelWord.Uses B u)
    (hAmbient :
      q.2.1 = p.2.1 * PSTS.SignedWord.evalGroup gen u) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C hCP p)
        w
        (K.multiCosetInclude P hadm hgen hret C hCP q) ∧
      PSTS.SignedWord.evalGroup gen w =
        PSTS.SignedWord.evalGroup gen u := by
  have hCoset : q.2.1 ∈ generatedLeftCoset gen B p.2.1 := by
    change p.2.1⁻¹ * q.2.1 ∈ generatedSubgroup gen B
    rw [hAmbient]
    simpa only [inv_mul_cancel_left] using
      (evalGroup_mem_generatedSubgroup_of_uses gen B hu)
  obtain ⟨w, hw, hPath⟩ :=
    K.upwardProperSinglePiece_actualSignedBPath
      P hadm hgen hret C hCP B hBC p q hTag hCoset
  let F := K.multiCosetAmbientHom P hadm hgen hret
  have hMapped :
      (cayleyGraph gen).toEGraph.Follows p.2.1 w q.2.1 := by
    have h := hPath.map F
    change (cayleyGraph gen).toEGraph.Follows
      (K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetInclude P hadm hgen hret C hCP p))
      w
      (K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetInclude P hadm hgen hret C hCP q)) at h
    simpa only [K.multiCosetAmbientValue_include] using h
  have hFollow :
      (cayleyGraph gen).followWord p.2.1 w = q.2.1 :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord p.2.1 w)
      hMapped
  have hWordValue :
      p.2.1 * PSTS.SignedWord.evalGroup gen w = q.2.1 := by
    simpa only [cayleyGraph.followWord_eq_mul_evalGroup] using hFollow
  have hGroup :
      PSTS.SignedWord.evalGroup gen w =
        PSTS.SignedWord.evalGroup gen u :=
    mul_left_cancel (hWordValue.trans hAmbient)
  exact ⟨w, hw, hPath, hGroup⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
