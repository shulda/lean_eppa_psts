import PSTSEPPA.ABO.SourceLiteralY1ActionKernel
import PSTSEPPA.ABO.UnaryDetectorSynchronizedCover
import PSTSEPPA.ABO.SynchronizedLabelledGroups

/-!
# Exact word-kernel equivalence between literal T(Y₁) and source-shaped H₁

The literal complete first source stage Y₁ consists of
  X₁ ⊔ (⨆_{i∈ι} Cayley(G₁[{i}]))
with all letters outside the singleton label completed by identity.
Its TRUE transition group is T(Y₁). The separately constructed H₁
is the synchronously generated subgroup of
  G₁ × ⟨(unary singleton detector letters)⟩.

The source H₁ word is one exactly when (i) its first G₁ coordinate
is one and (ii) every true singleton detector coordinate is one.
This is the EXACT signed word-kernel criterion already obtained
for the literal T(Y₁). Thus all chronological signed relations
in T(Y₁) and H₁ agree, even for geometric loops, repeated labels,
noncommuting input edges and an empty alphabet.

No assumption that arbitrary tagged coset-quotient vertices have
distinct ambient G₁ or H₁ coordinates is made. This is a genuinely
two-sided kernel equivalence, not a mere one-stability statement.

The induced GENERATOR-PRESERVING GROUP ISOMORPHISM H₁ ≃* T(Y₁)
still needs a separate explicit map/inverse based on these kernels;
it is not constructed in this file. The selected Z₁ catalogue,
corrected Condition 5.2, Theorem 4.7 and PSTS EPPA remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The concrete synchronized group H₁ has EXACTLY the same
identity signed words as the original X₁-transition group G₁
together with all true trivially completed singleton G₁[{i}]
subgroup detectors. Both directions are proved on the ACTUAL
generated synchronous subgroup, not on the full direct product. -/
theorem sourceH1_wordValue_eq_one_iff_unary_coordinates
    (src dst : ι → V) (w : LabelWord ι) :
    PSTS.SignedWord.evalGroup (sourceH1Generator src dst) w = 1 ↔
      PSTS.SignedWord.evalGroup
        (sourceG1Generator src dst) w = 1 ∧
      ∀ i : ι,
        PSTS.SignedWord.evalGroup
          (trivialCompletionGenerator
            (sourceG1Generator src dst) ({i} : Finset ι)) w = 1 := by
  let gen := sourceG1Generator src dst
  let det := unaryGeneratedDetectorGenerator gen
  change PSTS.SignedWord.evalGroup
      (SynchronizedProduct.generator gen det) w = 1 ↔ _
  constructor
  · intro h
    have hFirst :
        PSTS.SignedWord.evalGroup gen w = 1 := by
      have hImage :=
        congrArg (SynchronizedProduct.fstHom gen det) h
      calc
        PSTS.SignedWord.evalGroup gen w =
          SynchronizedProduct.fstHom gen det
            (PSTS.SignedWord.evalGroup
              (SynchronizedProduct.generator gen det) w) :=
          (SynchronizedProduct.fstHom_evalGroup gen det w).symm
        _ = 1 := by simpa using hImage
    have hDetector :
        PSTS.SignedWord.evalGroup det w = 1 := by
      have hImage :=
        congrArg (SynchronizedProduct.sndHom gen det) h
      calc
        PSTS.SignedWord.evalGroup det w =
          SynchronizedProduct.sndHom gen det
            (PSTS.SignedWord.evalGroup
              (SynchronizedProduct.generator gen det) w) :=
          (SynchronizedProduct.sndHom_evalGroup gen det w).symm
        _ = 1 := by simpa using hImage
    have hWhole :
        PSTS.SignedWord.evalGroup (unaryDetectorGenerator gen) w = 1 := by
      have hCoe :=
        congrArg
          (fun x : UnaryGeneratedDetectorGroup gen =>
            (x : UnaryDetectorGroup gen)) hDetector
      change
        ((PSTS.SignedWord.evalGroup
          (unaryGeneratedDetectorGenerator gen) w :
            UnaryGeneratedDetectorGroup gen) : UnaryDetectorGroup gen) = 1 at hCoe
      rw [coe_evalGroup_unaryGeneratedDetector] at hCoe
      exact hCoe
    refine ⟨hFirst, ?_⟩
    intro i
    have hi :=
      congrArg (fun f : UnaryDetectorGroup gen => f i) hWhole
    calc
      PSTS.SignedWord.evalGroup
          (trivialCompletionGenerator gen ({i} : Finset ι)) w =
        (PSTS.SignedWord.evalGroup (unaryDetectorGenerator gen) w) i :=
          (evalGroup_unaryDetector_apply gen w i).symm
      _ = 1 := by simpa using hi
  · rintro ⟨hFirst, hAll⟩
    have hWhole :
        PSTS.SignedWord.evalGroup (unaryDetectorGenerator gen) w = 1 := by
      funext i
      exact (evalGroup_unaryDetector_apply gen w i).trans (hAll i)
    have hDetector :
        PSTS.SignedWord.evalGroup det w = 1 := by
      apply Subtype.ext
      change
        ((PSTS.SignedWord.evalGroup det w :
          UnaryGeneratedDetectorGroup gen) : UnaryDetectorGroup gen) = 1
      rw [coe_evalGroup_unaryGeneratedDetector]
      exact hWhole
    apply Subtype.ext
    apply Prod.ext
    · change
        SynchronizedProduct.fstHom gen det
          (PSTS.SignedWord.evalGroup
            (SynchronizedProduct.generator gen det) w) = 1
      exact (SynchronizedProduct.fstHom_evalGroup gen det w).trans hFirst
    · change
        SynchronizedProduct.sndHom gen det
          (PSTS.SignedWord.evalGroup
            (SynchronizedProduct.generator gen det) w) = 1
      exact (SynchronizedProduct.sndHom_evalGroup gen det w).trans hDetector

/-- The literal paper transition action T(Y₁) and the
constructed first-rank source synchronized H₁ have precisely
THE SAME identity signed words, without ANY bound on alphabet
size or word length. Hence the canonical generator map has
no extra kernel at either side; an explicit group isomorphism
and its generator-law verification remain the next interface. -/
theorem sourceLiteralY1_wordValue_eq_one_iff_sourceH1
    (src dst : ι → V) (w : LabelWord ι) :
    (sourceLiteralY1 src dst).wordValue w = 1 ↔
      PSTS.SignedWord.evalGroup (sourceH1Generator src dst) w = 1 := by
  exact (sourceLiteralY1_wordValue_eq_one_iff src dst w).trans
    (sourceH1_wordValue_eq_one_iff_unary_coordinates src dst w).symm

end ABO
end PSTSEPPA
