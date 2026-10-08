import PSTSEPPA.ABO.AdmissibleAttachedIntersection

/-!
# Multi-alphabet coset gluing: overlap relation

For two component-indexed coset copies with alphabets B and C, the precise
identification proposed by ABO (3.10) is that both points descend from one
tagged (B ∩ C)-coset point.  Equality of their ambient group coordinates
alone is insufficient.

Here we formulate that relation without silently taking transitive closure,
and prove identity/composition laws for the canonical alphabet-enlargement
maps together with reflexivity, symmetry, same-alphabet rigidity and ambient
value compatibility.

Transitivity across three *different* alphabets is the next separate gate;
its proof must handle nesting and repeated/equal alphabet parameters, as
required by repair R5.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Alphabet enlargement is the identity when the alphabet is unchanged. -/
theorem attachedSubalphabetMap_self
    (B : Finset ι) (p : K.AttachedCosetVertex B) :
    K.attachedSubalphabetMap B B (subset_rfl) p = p := by
  apply K.attachedValue_injective_of_same_index B
  · exact K.componentIndexMap_self B p.1
  · rfl

/-- Two successive alphabet enlargements equal one direct enlargement.
The statement explicitly includes B=C and C=D. -/
theorem attachedSubalphabetMap_comp
    (B C D : Finset ι)
    (hBC : B ⊆ C) (hCD : C ⊆ D)
    (p : K.AttachedCosetVertex B) :
    K.attachedSubalphabetMap C D hCD
        (K.attachedSubalphabetMap B C hBC p) =
      K.attachedSubalphabetMap B D (hBC.trans hCD) p := by
  apply K.attachedValue_injective_of_same_index D
  · exact K.componentIndexMap_comp B C D hBC hCD p.1
  · rfl

/-- Literal overlap of tagged B- and C-coset points: a *single*
(B ∩ C)-tagged point maps to both. This is the vertex relation underlying
ABO equation (3.10), before quotienting the union of all alphabets. -/
def ShareIntersectionSupport
    (B C : Finset ι)
    (p : K.AttachedCosetVertex B)
    (q : K.AttachedCosetVertex C) : Prop :=
  ∃ r : K.AttachedCosetVertex (B ∩ C),
    K.attachedSubalphabetMap (B ∩ C) B
        Finset.inter_subset_left r = p ∧
    K.attachedSubalphabetMap (B ∩ C) C
        Finset.inter_subset_right r = q

/-- Reflexivity of the exact intersection-support relation, even for the
empty alphabet. -/
theorem shareIntersectionSupport_refl
    (B : Finset ι) (p : K.AttachedCosetVertex B) :
    K.ShareIntersectionSupport B B p p := by
  have hBB : B ⊆ B ∩ B := by
    intro i hi
    exact Finset.mem_inter.mpr ⟨hi, hi⟩
  let r : K.AttachedCosetVertex (B ∩ B) :=
    K.attachedSubalphabetMap B (B ∩ B) hBB p
  refine ⟨r, ?_, ?_⟩
  · calc
      K.attachedSubalphabetMap (B ∩ B) B
          Finset.inter_subset_left r =
          K.attachedSubalphabetMap B B
            (hBB.trans Finset.inter_subset_left) p :=
        K.attachedSubalphabetMap_comp B (B ∩ B) B
          hBB Finset.inter_subset_left p
      _ = p := K.attachedSubalphabetMap_self B p
  · calc
      K.attachedSubalphabetMap (B ∩ B) B
          Finset.inter_subset_right r =
          K.attachedSubalphabetMap B B
            (hBB.trans Finset.inter_subset_right) p :=
        K.attachedSubalphabetMap_comp B (B ∩ B) B
          hBB Finset.inter_subset_right p
      _ = p := K.attachedSubalphabetMap_self B p

/-- Symmetry just swaps the two supports and their intersection factors. -/
theorem shareIntersectionSupport_symm
    (B C : Finset ι)
    {p : K.AttachedCosetVertex B}
    {q : K.AttachedCosetVertex C}
    (h : K.ShareIntersectionSupport B C p q) :
    K.ShareIntersectionSupport C B q p := by
  rcases h with ⟨r, hrp, hrq⟩
  have hswap : B ∩ C ⊆ C ∩ B := by
    intro i hi
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hi).2, (Finset.mem_inter.mp hi).1⟩
  let r' : K.AttachedCosetVertex (C ∩ B) :=
    K.attachedSubalphabetMap (B ∩ C) (C ∩ B) hswap r
  refine ⟨r', ?_, ?_⟩
  · calc
      K.attachedSubalphabetMap (C ∩ B) C
          Finset.inter_subset_left r' =
          K.attachedSubalphabetMap (B ∩ C) C
            (hswap.trans Finset.inter_subset_left) r :=
        K.attachedSubalphabetMap_comp
          (B ∩ C) (C ∩ B) C hswap Finset.inter_subset_left r
      _ = K.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right r := rfl
      _ = q := hrq
  · calc
      K.attachedSubalphabetMap (C ∩ B) B
          Finset.inter_subset_right r' =
          K.attachedSubalphabetMap (B ∩ C) B
            (hswap.trans Finset.inter_subset_right) r :=
        K.attachedSubalphabetMap_comp
          (B ∩ C) (C ∩ B) B hswap Finset.inter_subset_right r
      _ = K.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left r := rfl
      _ = p := hrp

/-- Two points with equal alphabet admit a common intersection support
if and only if they are literally equal as component-tagged points.
This does not rely on any ambient-group injectivity. -/
theorem shareIntersectionSupport_self_iff
    (B : Finset ι)
    (p q : K.AttachedCosetVertex B) :
    K.ShareIntersectionSupport B B p q ↔ p = q := by
  constructor
  · rintro ⟨r, hp, hq⟩
    exact hp.symm.trans hq
  · rintro rfl
    exact K.shareIntersectionSupport_refl B p

/-- If two tagged coset points have intersection support, their ambient
group values agree. The converse is generally false. -/
theorem shareIntersectionSupport_value_eq
    (B C : Finset ι)
    {p : K.AttachedCosetVertex B}
    {q : K.AttachedCosetVertex C}
    (h : K.ShareIntersectionSupport B C p q) :
    K.attachedValue B p = K.attachedValue C q := by
  rcases h with ⟨r, hp, hq⟩
  calc
    K.attachedValue B p =
        K.attachedValue B
          (K.attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left r) :=
      congrArg (K.attachedValue B) hp.symm
    _ = K.attachedValue (B ∩ C) r := rfl
    _ = K.attachedValue C
          (K.attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right r) := rfl
    _ = K.attachedValue C q :=
      congrArg (K.attachedValue C) hq

/-- If B ⊆ C, a tagged B-point and its canonical C-image have precisely the
common intersection support expected from ABO (3.10). -/
theorem shareIntersectionSupport_of_subset
    (B C : Finset ι) (hBC : B ⊆ C)
    (p : K.AttachedCosetVertex B) :
    K.ShareIntersectionSupport B C p
      (K.attachedSubalphabetMap B C hBC p) := by
  have hinto : B ⊆ B ∩ C := by
    intro i hi
    exact Finset.mem_inter.mpr ⟨hi, hBC hi⟩
  let r : K.AttachedCosetVertex (B ∩ C) :=
    K.attachedSubalphabetMap B (B ∩ C) hinto p
  refine ⟨r, ?_, ?_⟩
  · calc
      K.attachedSubalphabetMap (B ∩ C) B
          Finset.inter_subset_left r =
          K.attachedSubalphabetMap B B
            (hinto.trans Finset.inter_subset_left) p :=
        K.attachedSubalphabetMap_comp
          B (B ∩ C) B hinto Finset.inter_subset_left p
      _ = p := K.attachedSubalphabetMap_self B p
  · calc
      K.attachedSubalphabetMap (B ∩ C) C
          Finset.inter_subset_right r =
          K.attachedSubalphabetMap B C
            (hinto.trans Finset.inter_subset_right) p :=
        K.attachedSubalphabetMap_comp
          B (B ∩ C) C hinto Finset.inter_subset_right p
      _ = K.attachedSubalphabetMap B C hBC p := rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
