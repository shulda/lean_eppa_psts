import PSTSEPPA.ABO.StandardCosetFamily
import PSTSEPPA.ABO.MultiCosetVertexQuotient

/-!
# Exact component-tagged supports in multi-coset extensions

Definition 3.22 and Proposition 3.23 of Auinger--Bitterlich--Otto
use *support* of a vertex in a coset extension: a vertex is supported
by an alphabet B and a constituent B-coset indexed by an actual
B-component of the skeleton.

The multi-coset quotient already records all of these tags. Here we
expose them in a source-facing predicate and show that any two
presentations of the same quotient vertex by B- and C-points share
a single tagged (B ∩ C)-support. For the full family of all proper
subalphabets, the intersection is itself selected, so supports are
closed under intersection. This is the exact vertex-support gate
behind equation (3.11) and the singleton case of the minimal-support
argument preceding Definition 3.22.

The support witness preserves intrinsic component tags. Equality of
group coordinates alone would not justify any of these assertions.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An alphabet B supports a multi-coset vertex z when some point
of a component-tagged B-coset copy maps to z.  This is not
a condition on the ambient Cayley coordinate alone. -/
def MultiCosetVertexSupported
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (z : K.MultiCosetVertex P hadm hgen hret) : Prop :=
  ∃ (hBP : B ∈ P.alphabets) (p : K.AttachedCosetVertex B),
    K.multiCosetInclude P hadm hgen hret B hBP p = z

/-- Every quotient vertex has some constituent-coset support,
including when the selected alphabet is empty. No nonempty
family hypothesis is required since there are no quotient
vertices when the family is empty. -/
theorem multiCosetVertex_exists_support
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    ∃ B : Finset ι,
      K.MultiCosetVertexSupported P hadm hgen hret B z := by
  induction z using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨⟨B, hBP⟩, p⟩
      exact ⟨B, hBP, p, rfl⟩

/-- Inclusion of a tagged smaller coset point is independent
of whether it first travels through the larger constituent
or is directly inserted at the smaller alphabet. -/
theorem multiCosetInclude_alphabet_mono
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D B : Finset ι) (hDB : D ⊆ B)
    (hDP : D ∈ P.alphabets) (hBP : B ∈ P.alphabets)
    (r : K.AttachedCosetVertex D) :
    K.multiCosetInclude P hadm hgen hret D hDP r =
      K.multiCosetInclude P hadm hgen hret B hBP
        (K.attachedSubalphabetMap D B hDB r) := by
  apply Quotient.sound
  exact K.shareIntersectionSupport_of_subset D B hDB r

/-- Exact intersection-support refinement of two arbitrary
presentations of the *same* multi-coset quotient vertex.
This is the component-tagged content of ABO equation (3.11). -/
theorem multiCosetVertex_two_supports_intersection
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex P hadm hgen hret)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (hBCP : B ∩ C ∈ P.alphabets)
    (p : K.AttachedCosetVertex B)
    (q : K.AttachedCosetVertex C)
    (hp : K.multiCosetInclude P hadm hgen hret B hBP p = z)
    (hq : K.multiCosetInclude P hadm hgen hret C hCP q = z) :
    ∃ r : K.AttachedCosetVertex (B ∩ C),
      K.multiCosetInclude P hadm hgen hret
        (B ∩ C) hBCP r = z ∧
      K.attachedSubalphabetMap (B ∩ C) B
        Finset.inter_subset_left r = p ∧
      K.attachedSubalphabetMap (B ∩ C) C
        Finset.inter_subset_right r = q := by
  have heq :
      K.multiCosetInclude P hadm hgen hret B hBP p =
        K.multiCosetInclude P hadm hgen hret C hCP q :=
    hp.trans hq.symm
  have hshare : K.ShareIntersectionSupport B C p q := by
    have h := Quotient.exact heq
    change K.MultiCosetRawRelated P
      (⟨⟨B, hBP⟩, p⟩ : K.MultiCosetRawVertex P)
      (⟨⟨C, hCP⟩, q⟩ : K.MultiCosetRawVertex P) at h
    exact h
  obtain ⟨r, hrp, hrq⟩ := hshare
  refine ⟨r, ?_, hrp, hrq⟩
  calc
    K.multiCosetInclude P hadm hgen hret
        (B ∩ C) hBCP r =
      K.multiCosetInclude P hadm hgen hret B hBP
        (K.attachedSubalphabetMap (B ∩ C) B
          Finset.inter_subset_left r) :=
      K.multiCosetInclude_alphabet_mono P hadm hgen hret
        (B ∩ C) B Finset.inter_subset_left hBCP hBP r
    _ = K.multiCosetInclude P hadm hgen hret B hBP p :=
      congrArg _ hrp
    _ = z := hp

end CayleySubgraphSpec

/-- The full ABO family of all proper subalphabets is closed under
binary intersection, including coincident/nested/empty alphabets. -/
theorem allProperCosetFamily_inter_mem
    (A B C : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (_hCP : C ∈ (allProperCosetFamily A).alphabets) :
    B ∩ C ∈ (allProperCosetFamily A).alphabets := by
  have hBA := (mem_allProperCosetFamily A B).mp hBP
  apply (mem_allProperCosetFamily A (B ∩ C)).2
  constructor
  · exact Finset.inter_subset_left.trans hBA.1
  · intro hA
    exact hBA.2 (hA.trans Finset.inter_subset_left)

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- For the full proper-alphabet coset extension, any two
supporting alphabets have a supporting intersection alphabet.
The witness is actual component-indexed coset support, not just
an ambient subgroup containment statement. -/
theorem allProperCosetVertex_support_inter
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (B C : Finset ι)
    (hB : K.MultiCosetVertexSupported (allProperCosetFamily A)
      hadm hgen hret B z)
    (hC : K.MultiCosetVertexSupported (allProperCosetFamily A)
      hadm hgen hret C z) :
    K.MultiCosetVertexSupported (allProperCosetFamily A)
      hadm hgen hret (B ∩ C) z := by
  obtain ⟨hBP, p, hp⟩ := hB
  obtain ⟨hCP, q, hq⟩ := hC
  let hD := allProperCosetFamily_inter_mem A B C hBP hCP
  obtain ⟨r, hr, _, _⟩ :=
    K.multiCosetVertex_two_supports_intersection
      (allProperCosetFamily A) hadm hgen hret z
      B C hBP hCP hD p q hp hq
  exact ⟨hD, r, hr⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
