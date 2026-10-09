import PSTSEPPA.ABO.MultiCosetSelectedComponentExact
import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.SingleCosetConnectivity
import PSTSEPPA.ABO.CosetConnectivity

/-!
# Subalphabet B-components inside arbitrary selected full C-coset copies

Let C be a selected coset alphabet and B⊆C. Even if B itself
is not selected, and even if other incomparable cosets were
simultaneously attached, every *actual* B-labelled path
starting inside one tagged completed C-coset stays inside
that C constituent. Its endpoint is determined by the same
tag and an ambient left B-coset relative to the starting
point. Conversely every point of that tagged B-coset is
connected by an actual B-word path.

This proves an important "full-coset" alternative of the
off-skeleton cluster-property geometry: an actual
B-component meeting a selected C-coset for C⊇B is
literally a full B-coset with its intrinsic C-component tag.
No ambient Cayley morphism is declared globally injective;
injectivity is used only inside the same C-tagged copy.

It is independent of the source's higher-rank cluster
property. The group needs only source retractability and
generation already used to construct the multi-coset EGraph.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact subalphabet path component inside a selected C-coset.

For B⊆C and a point p in the component-tagged complete C-coset,
the image of its global intrinsic B-component is exactly the
left B-coset inside the same *tagged* C-copy.
There is no assumption that B is itself in the selected family. -/
theorem multiCoset_selected_C_subalphabet_B_component_exact
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (B : Finset ι) (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex C)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C hCP p) w z) ↔
    ∃ q : K.AttachedCosetVertex C,
      q.1 = p.1 ∧
      q.2.1 ∈ generatedLeftCoset gen B p.2.1 ∧
      z = K.multiCosetInclude P hadm hgen hret C hCP q := by
  let G := K.multiCosetEGraph P hadm hgen hret
  constructor
  · rintro ⟨w, hwB, hpath⟩
    obtain ⟨q, hidx, hq⟩ :=
      K.multiCoset_selected_B_path_stays_in_coset
        P hadm hgen hret C hCP w (hwB.mono hBC)
        p z hpath
    have hambient :
        (cayleyGraph gen).toEGraph.Follows p.2.1 w q.2.1 := by
      have hmapped :=
        hpath.map (K.multiCosetAmbientHom P hadm hgen hret)
      rw [hq] at hmapped
      simpa only [K.multiCosetAmbientValue_include] using hmapped
    have hcanonical :=
      (cayleyGraph gen).follows_followWord p.2.1 w
    have hvalue :
        (cayleyGraph gen).followWord p.2.1 w = q.2.1 :=
      (cayleyGraph gen).toEGraph.follows_right_unique
        hcanonical hambient
    have hcoset :
        q.2.1 ∈ generatedLeftCoset gen B p.2.1 :=
      (mem_generatedLeftCoset_iff_subalphabetReachable
        gen B p.2.1 q.2.1).2 ⟨w, hwB, hvalue⟩
    exact ⟨q, hidx, hcoset, hq⟩
  · rintro ⟨q, hidx, hcoset, hq⟩
    have hrelative :
        p.2.1⁻¹ * q.2.1 ∈ generatedSubgroup gen B := hcoset
    obtain ⟨w, hwB, hvalue⟩ :=
      exists_word_uses_eq_of_mem_generatedSubgroup
        gen B hrelative
    obtain ⟨r, hpath, hridx, hrval⟩ :=
      K.singleCosetEGraph_follows_word C p (hwB.mono hBC)
    have hrqval : r.2.1 = q.2.1 := by
      rw [hrval, hvalue]
      simp [mul_assoc]
    have hrq : r = q :=
      K.attachedValue_injective_of_same_index C
        (hridx.trans hidx.symm) hrqval
    have hmapped :=
      hpath.map
        (K.singleCosetToMultiHom P hadm hgen hret C hCP)
    change G.Follows
      (K.multiCosetInclude P hadm hgen hret C hCP p)
      w
      (K.multiCosetInclude P hadm hgen hret C hCP r) at hmapped
    rw [hrq, ← hq] at hmapped
    exact ⟨w, hwB, hmapped⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
