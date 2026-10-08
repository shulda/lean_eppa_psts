import PSTSEPPA.ABO.LocalCosetEmbedding
import PSTSEPPA.ABO.MultiCosetVertexQuotient

/-!
# Folding lower coset extensions into a containing B-coset extension

Fix a proper B⊂A, and let P consist only of alphabets C⊆B.
Each component-tagged C-coset point has a canonical image in the
containing component-tagged B-coset. These maps are compatible with
the literal intersection-support gluing equivalence relation, so
they descend to a map CE(G,K;P) → CE(G,K;B) on vertices.

Admissibility forces this map to be injective: two lower coset points
with the same image in a B-copy have an actual shared intersection
support. This is the structural local embedding mechanism behind
ABO (3.9) and Lemma 3.20, and covers equal/nested/empty alphabets.

If B itself belongs to P, the map is also surjective, and therefore
a bijection on vertices. We do not yet assert a labelled graph
morphism here; preservation of directed edge tokens is a subsequent
obligation.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The canonical component-tagged map from a coset-extension family
of subalphabets C⊆B into the single B-extension's vertex set. -/
def multiCosetVertexToParent
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    K.AttachedCosetVertex B :=
  Quotient.liftOn z
    (fun raw : K.MultiCosetRawVertex P =>
      K.attachedSubalphabetMap raw.1.1 B
        (hPsub raw.1.1 raw.1.2) raw.2)
    (by
      intro p q hpq
      change K.ShareIntersectionSupport p.1.1 q.1.1
        p.2 q.2 at hpq
      obtain ⟨r, hrp, hrq⟩ := hpq
      calc
        K.attachedSubalphabetMap p.1.1 B
            (hPsub p.1.1 p.1.2) p.2 =
          K.attachedSubalphabetMap p.1.1 B
            (hPsub p.1.1 p.1.2)
            (K.attachedSubalphabetMap
              (p.1.1 ∩ q.1.1) p.1.1
              Finset.inter_subset_left r) := by rw [hrp]
        _ = K.attachedSubalphabetMap (p.1.1 ∩ q.1.1) B
              (Finset.inter_subset_left.trans
                (hPsub p.1.1 p.1.2)) r :=
          K.attachedSubalphabetMap_comp
            (p.1.1 ∩ q.1.1) p.1.1 B
            Finset.inter_subset_left (hPsub p.1.1 p.1.2) r
        _ = K.attachedSubalphabetMap (p.1.1 ∩ q.1.1) B
              (Finset.inter_subset_right.trans
                (hPsub q.1.1 q.1.2)) r := rfl
        _ = K.attachedSubalphabetMap q.1.1 B
              (hPsub q.1.1 q.1.2)
              (K.attachedSubalphabetMap
                (p.1.1 ∩ q.1.1) q.1.1
                Finset.inter_subset_right r) :=
          (K.attachedSubalphabetMap_comp
            (p.1.1 ∩ q.1.1) q.1.1 B
            Finset.inter_subset_right (hPsub q.1.1 q.1.2) r).symm
        _ = K.attachedSubalphabetMap q.1.1 B
              (hPsub q.1.1 q.1.2) q.2 := by rw [hrq])

@[simp]
theorem multiCosetVertexToParent_include
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (p : K.AttachedCosetVertex C) :
    K.multiCosetVertexToParent P hadm hgen hret B hPsub
        (K.multiCosetInclude P hadm hgen hret C hCP p) =
      K.attachedSubalphabetMap C B (hPsub C hCP) p :=
  rfl

/-- The parent-coset map preserves the ambient group coordinate. -/
theorem multiCosetVertexToParent_value
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    K.attachedValue B
        (K.multiCosetVertexToParent P hadm hgen hret B hPsub z) =
      K.multiCosetAmbientValue P hadm hgen hret z := by
  induction z using Quotient.inductionOn with
  | h raw =>
    rfl

/-- The vertex map into the B-extension is injective under
admissibility, even when two different lower alphabets overlap. -/
theorem multiCosetVertexToParent_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBA : B ⊂ A)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B) :
    Function.Injective
      (K.multiCosetVertexToParent P hadm hgen hret B hPsub) := by
  intro p q hpq
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      rcases p with ⟨C, p⟩
      rcases q with ⟨D, q⟩
      have hindex :=
        congrArg (K.attachedIndex B) hpq
      have hvalue :=
        congrArg (K.attachedValue B) hpq
      exact K.multiCosetInclude_eq_of_same_parent_and_value
        P hadm hgen hret B C.1 D.1 hBA C.2 D.2
        (hPsub C.1 C.2) (hPsub D.1 D.2)
        p q hindex hvalue

/-- If B itself is among the selected alphabets, the parent map
is surjective. Together with injectivity this gives a bijection of
vertex sets CE(G,K;P) ≅ CE(G,K;B), whenever P⊆P(B) and B∈P. -/
theorem multiCosetVertexToParent_surjective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (hBP : B ∈ P.alphabets) :
    Function.Surjective
      (K.multiCosetVertexToParent P hadm hgen hret B hPsub) := by
  intro p
  refine ⟨K.multiCosetInclude P hadm hgen hret B hBP p, ?_⟩
  change K.attachedSubalphabetMap B B (hPsub B hBP) p = p
  exact K.attachedSubalphabetMap_self B p

end CayleySubgraphSpec
end ABO
end PSTSEPPA
