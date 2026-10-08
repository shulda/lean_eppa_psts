import PSTSEPPA.ABO.MultiCosetTransitivity

/-!
# The genuine multi-alphabet coset-extension vertex quotient (ABO 3.10)

For a finite family P of proper subalphabets of A, take the disjoint
union of all component-indexed coset vertices, tagging each summand
by its alphabet. Identify two points only when they have a common
component-indexed representative over the intersection alphabet.

The checked transitivity lemma makes this literal overlap relation
a Setoid, so no transitive closure (which could create unintended
identifications) is taken. We construct the quotient, its canonical
ambient-group projection, and prove that each individual coset extension
embeds injectively in the quotient on vertices.

Moreover, the embeddings of a skeleton vertex through two different
alphabet summands always coincide. This is the vertex part of the
construction behind ABO Proposition 3.18. Directed edges and the
resulting E-graph are separate, still open obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

/-- The family of alphabets to be glued, all proper in A. -/
structure CosetFamilySpec (A : Finset ι) where
  alphabets : Finset (Finset ι)
  proper : ∀ B ∈ alphabets, B ⊂ A

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Disjoint union of component-tagged points from all selected alphabets. -/
abbrev MultiCosetRawVertex (P : CosetFamilySpec A) :=
  Σ B : {B : Finset ι // B ∈ P.alphabets},
    K.AttachedCosetVertex B.1

/-- Literal gluing relation: the two points share a representative over
their alphabet intersection. Neither equality of ambient values nor
equality of the containing component suffices by itself. -/
def MultiCosetRawRelated (P : CosetFamilySpec A)
    (p q : K.MultiCosetRawVertex P) : Prop :=
  K.ShareIntersectionSupport p.1.1 q.1.1 p.2 q.2

/-- Under admissibility and retractability, the literal source gluing
relation is already an equivalence relation, including degenerate
intersection/equal-subset cases (repair R5). -/
def multiCosetSetoid
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :
    Setoid (K.MultiCosetRawVertex P) where
  r := K.MultiCosetRawRelated P
  iseqv := {
    refl := fun p =>
      K.shareIntersectionSupport_refl p.1.1 p.2
    symm := fun h =>
      K.shareIntersectionSupport_symm _ _ h
    trans := fun hpq hqr =>
      K.shareIntersectionSupport_trans
        hadm hgen hret _ _ _ (P.proper _ _)
        hpq hqr
  }

/-- Vertices of the P-coset extension, as a genuine quotient by ABO 3.10. -/
def MultiCosetVertex
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) :=
  Quotient (K.multiCosetSetoid P hadm hgen hret)

/-- Forget all component and alphabet tags. This canonical morphism into
the ambient group is well-defined but *not* assumed globally injective. -/
def multiCosetAmbientValue
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (x : K.MultiCosetVertex P hadm hgen hret) : Γ :=
  Quotient.liftOn x
    (fun p : K.MultiCosetRawVertex P => K.attachedValue p.1.1 p.2)
    (by
      intro p q hpq
      exact K.shareIntersectionSupport_value_eq
        p.1.1 q.1.1 hpq)

/-- Inject the B-summand into the glued quotient. -/
def multiCosetInclude
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : K.AttachedCosetVertex B) :
    K.MultiCosetVertex P hadm hgen hret :=
  Quotient.mk (K.multiCosetSetoid P hadm hgen hret)
    (⟨⟨B, hBP⟩, p⟩ : K.MultiCosetRawVertex P)

/-- The ambient value of an included B-point is its original group
coordinate; this does not require ambient-map injectivity. -/
@[simp]
theorem multiCosetAmbientValue_include
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : K.AttachedCosetVertex B) :
    K.multiCosetAmbientValue P hadm hgen hret
        (K.multiCosetInclude P hadm hgen hret B hBP p) =
      K.attachedValue B p :=
  rfl

/-- No individual coset summand collapses in the multi-alphabet quotient.
This is the vertex-level embedding claim following ABO 3.10. -/
theorem multiCosetInclude_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    Function.Injective (K.multiCosetInclude P hadm hgen hret B hBP) := by
  intro p q hpq
  have hrel : K.ShareIntersectionSupport B B p q :=
    Quotient.exact hpq
  exact (K.shareIntersectionSupport_self_iff B p q).1 hrel

/-- The image of an old skeleton vertex does not depend on which
selected alphabet is used to include it in the multi-coset quotient. -/
theorem multiCosetInclude_skeleton_independent
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hBP : B ∈ P.alphabets) (hCP : C ∈ P.alphabets)
    (x : K.Vertex) :
    K.multiCosetInclude P hadm hgen hret B hBP
        (K.attachedOfSkeletonVertex B x) =
      K.multiCosetInclude P hadm hgen hret C hCP
        (K.attachedOfSkeletonVertex C x) := by
  apply Quotient.sound
  exact
    ⟨K.attachedOfSkeletonVertex (B ∩ C) x,
      K.attachedSubalphabetMap_ofSkeletonVertex
        (B ∩ C) B Finset.inter_subset_left x,
      K.attachedSubalphabetMap_ofSkeletonVertex
        (B ∩ C) C Finset.inter_subset_right x⟩

/-- Choosing any one alphabet in P provides an injective map of the
original skeleton's vertices into the glued vertex quotient. -/
theorem multiCosetInclude_skeleton_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBP : B ∈ P.alphabets) :
    Function.Injective
      (fun x : K.Vertex =>
        K.multiCosetInclude P hadm hgen hret B hBP
          (K.attachedOfSkeletonVertex B x)) := by
  intro x y hxy
  have hvalue :=
    congrArg (K.multiCosetAmbientValue P hadm hgen hret) hxy
  apply Subtype.ext
  simpa only [K.multiCosetAmbientValue_include,
    K.attachedValue_ofSkeletonVertex] using hvalue

end CayleySubgraphSpec
end ABO
end PSTSEPPA
