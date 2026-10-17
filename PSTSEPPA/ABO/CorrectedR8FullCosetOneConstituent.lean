import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents
import PSTSEPPA.ABO.MultiCosetOverlap
import PSTSEPPA.ABO.MultiCosetFullComponentFromSuperset

/-!
# Corrected ABO 4.7(iii), repair R8: genuine FULL B-coset is a one-constituent case

The source's cluster property admits TWO alternatives for an
off-skeleton B-component: a genuine B-cluster supported on
lower subalphabets, OR an existing completed full B-coset.
The printed proof of corrected Theorem 4.7(iii) addresses
the cluster branch but omits the FULL B-coset branch (R8).

The latter is not an additional nontrivial cluster core case.
Whenever a complete B-constituent is present and B⊆C with
C a selected (typically maximal proper) alphabet, the entire
real signed B-path component is inside ONE true C-constituent.
In particular no B-path can escape that C-tagged copy to
form an external B-bridge.

The proof is about the EXACT quotient of component-tagged
vertices and genuine directed signed path tokens. It uses
common-(B∩C)-support gluing of B and C at the same old
component tag, followed by the already certified
one-constituent B-component path classification. It does
not assume that ambient group coordinates identify
distinct B/C coset tags.

The lemma is UNIFORM IN RANK and applies to any admissible
genuine coset skeleton. For higher-rank cluster arguments
one separately chooses a maximal proper C containing B;
the theorem below then supplies the R8 one-constituent
alternative without any hypothesized cluster property,
bridge freeness or group-cover compatibility.

This closes only the *local full-B alternative* R8,
NOT the separate genuine B-cluster case of 4.7(iii),
nor the entire rank-two first-rank proof or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- In the ACTUAL source+signed-label glued multiCE, each
genuine B-constituent vertex equals its canonical image in
EVERY selected containing C-constituent. This equality is
witnessed by actual OLD (B∩C)-support, not ambient group
coordinate agreement. -/
theorem multiCoset_full_B_to_selected_superset_eq
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets)
    (hCP : C ∈ P.alphabets)
    (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex B) :
    K.multiCosetInclude P hadm hgen hret B hBP p =
      K.multiCosetInclude P hadm hgen hret C hCP
        (K.attachedSubalphabetMap B C hBC p) := by
  apply Quotient.sound
  exact K.shareIntersectionSupport_of_subset B C hBC p

/-- R8's missing FULL B-coset alternative, in its precise
ONE C-CONSTITUENT signed path form.

For ANY true signed B-word path beginning at a point of
the full, intrinsically indexed B-coset constituent,
if B⊆C and C is another selected complete constituent,
then its endpoint lies in ONE specific original C-copy,
with EXACT component index determined by the B-old anchor
and ambient displacement belonging to its genuine G[B]
coset. This is a statement about the path's endpoint
VERTEX in the real quotient; no "ambient equality
implies source quotient equality" shortcut is used. -/
theorem multiCoset_R8_full_B_component_one_constituent
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets)
    (hCP : C ∈ P.alphabets)
    (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex B)
    (y : K.MultiCosetVertex P hadm hgen hret)
    (hPath : ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret B hBP p)
        w y) :
    ∃ q : K.AttachedCosetVertex C,
      q.1 = (K.attachedSubalphabetMap B C hBC p).1 ∧
      q.2.1 ∈ generatedLeftCoset gen B p.2.1 ∧
      y = K.multiCosetInclude P hadm hgen hret C hCP q := by
  let q0 := K.attachedSubalphabetMap B C hBC p
  obtain ⟨w, hw, hpath⟩ := hPath
  have hEqual :=
    K.multiCoset_full_B_to_selected_superset_eq
      P hadm hgen hret B C hBP hCP hBC p
  rw [hEqual] at hpath
  have hResult :=
    (K.multiCoset_selected_C_subalphabet_B_component_exact
      P hadm hgen hret C hCP B hBC q0 y).mp
      ⟨w, hw, hpath⟩
  rcases hResult with ⟨q, hqIndex, hqCoset, hqy⟩
  refine ⟨q, hqIndex, ?_, hqy⟩
  have hSameVal : (q0.2.1 : Γ) = p.2.1 := rfl
  simpa only [hSameVal] using hqCoset

end CayleySubgraphSpec
end ABO
end PSTSEPPA
