import PSTSEPPA.ABO.CosetConnectivity
import PSTSEPPA.ABO.Retractability

/-!
# ABO Lemma 4.3 (Figure 7 -> Figure 8): delete redundant letters

This is exactly the RETRACTABILITY step of the existing published
proof, not a new route to the cluster property. In the proof of
ABO I Lemma 4.3 (PDF p.37), two actual Cayley paths have the
same starting and terminal vertices:

* one is labelled by p, a word using the path alphabet B_i;
* another is labelled by q, a word using a smaller minimum
  support alphabet D.

The authors delete every occurrence of a letter outside D
from p. Since H[A_i] is retractable and [p]=[q], deletion
does not change its group value. The resulting word p|D
uses only D and therefore genuinely runs, inside the
COMPLETE Cayley graph of H[A_i], between the same endpoints.

This file isolates and verifies that precise algebraic
lemma in a labelled retractable group. To apply it in the
paper's locally retractable H[A_i], instantiate the group
parameter with that true local group and its generators.
It does NOT claim that deleting letters from a path in an
arbitrary incomplete EGraph still gives a legal path:
the Cayley completeness is essential and explicit.

The subsequent argument that the earlier selected B_i
core vertex itself lies in the shared intersection
of the A_i and A_j constituent cosets, and therefore
the minimum supports synchronize, remains a separate
source Lemma 4.3 step.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace LabelWord

/-- A signed word supported on D is unchanged by deleting
all positive and inverse occurrences of generators
outside D. The statement includes the empty word. -/
theorem restrictTo_eq_self_of_uses
    (D : Finset ι) (w : LabelWord ι)
    (hw : Uses D w) :
    restrictTo D w = w := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      have hs : signedBase s ∉ (Finset.univ \ D) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
        exact hw.1
      change
        (if signedBase s ∈ (Finset.univ \ D) then
          deleteGenerators (Finset.univ \ D) w
        else
          s :: deleteGenerators (Finset.univ \ D) w) = s :: w
      rw [if_neg hs]
      exact congrArg (List.cons s) (ih hw.2)

/-- Restricting a signed word to D really produces a
D-word; formal inverse letters are handled as well. -/
theorem uses_restrictTo
    (D : Finset ι) (w : LabelWord ι) :
    Uses D (restrictTo D w) := by
  induction w with
  | nil =>
      trivial
  | cons s w ih =>
      by_cases hD : signedBase s ∈ D
      · have hs : signedBase s ∉ (Finset.univ \ D) := by
          simp [hD]
        change Uses D
          (if signedBase s ∈ (Finset.univ \ D) then
            deleteGenerators (Finset.univ \ D) w
          else
            s :: deleteGenerators (Finset.univ \ D) w)
        rw [if_neg hs]
        exact ⟨hD, ih⟩
      · have hs : signedBase s ∈ (Finset.univ \ D) := by
          simp [hD]
        change Uses D
          (if signedBase s ∈ (Finset.univ \ D) then
            deleteGenerators (Finset.univ \ D) w
          else
            s :: deleteGenerators (Finset.univ \ D) w)
        rw [if_pos hs]
        exact ih

end LabelWord

/-- Source Lemma-4.3 algebraic deletion principle:
if p and a D-word q represent the SAME element in a
retractable labelled group, then deleting all letters
outside D from p preserves its exact group value. -/
theorem evalGroup_restrictTo_eq_of_equal_D_word
    (gen : ι → Γ) (hret : Retractable gen)
    (D : Finset ι) (p q : LabelWord ι)
    (hpq :
      PSTS.SignedWord.evalGroup gen p =
        PSTS.SignedWord.evalGroup gen q)
    (hq : LabelWord.Uses D q) :
    PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo D p) =
      PSTS.SignedWord.evalGroup gen p := by
  calc
    PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo D p) =
        PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo D q) :=
      hret.restrictTo_eq D hpq
    _ = PSTS.SignedWord.evalGroup gen q := by
      rw [LabelWord.restrictTo_eq_self_of_uses D q hq]
    _ = PSTS.SignedWord.evalGroup gen p := hpq.symm

/-- Pointwise Cayley action version of the published deletion
argument: for every actual Cayley starting group value g,
the path labelled p and its D-restriction have identical
terminal group values whenever a D-word q is equal to p. -/
theorem cayley_followWord_restrictTo_eq_of_equal_D_word
    (gen : ι → Γ) (hret : Retractable gen)
    (D : Finset ι) (g : Γ) (p q : LabelWord ι)
    (hpq :
      PSTS.SignedWord.evalGroup gen p =
        PSTS.SignedWord.evalGroup gen q)
    (hq : LabelWord.Uses D q) :
    (cayleyGraph gen).followWord g (LabelWord.restrictTo D p) =
      (cayleyGraph gen).followWord g p := by
  calc
    (cayleyGraph gen).followWord g (LabelWord.restrictTo D p) =
        g * PSTS.SignedWord.evalGroup gen (LabelWord.restrictTo D p) :=
      cayleyGraph.followWord_eq_mul_evalGroup gen g _
    _ = g * PSTS.SignedWord.evalGroup gen p :=
      congrArg (fun t : Γ => g * t)
        (evalGroup_restrictTo_eq_of_equal_D_word
          gen hret D p q hpq hq)
    _ = (cayleyGraph gen).followWord g p :=
      (cayleyGraph.followWord_eq_mul_evalGroup gen g p).symm

/-- EXACT Figure-7 / Figure-8 signed path statement:
given TWO REAL Cayley paths g --p--> h and g --q--> h,
with q using only D, retractability produces the
CONCRETE deleted word p|D and a TRUE signed D-path
g --p|D--> h in that same Cayley graph.

The original path p need not be D-supported.
There is no unproved 'shortened paths exist' axiom:
the new path is the true Cayley path obtained by
following the explicitly constructed word. -/
theorem cayley_restricted_path_of_two_paths
    (gen : ι → Γ) (hret : Retractable gen)
    (D : Finset ι)
    (g h : Γ) (p q : LabelWord ι)
    (hp :
      (cayleyGraph gen).toEGraph.Follows g p h)
    (hq :
      (cayleyGraph gen).toEGraph.Follows g q h)
    (hqD : LabelWord.Uses D q) :
    LabelWord.Uses D (LabelWord.restrictTo D p) ∧
      (cayleyGraph gen).toEGraph.Follows
        g (LabelWord.restrictTo D p) h := by
  have hEndP :
      (cayleyGraph gen).followWord g p = h :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord g p) hp
  have hEndQ :
      (cayleyGraph gen).followWord g q = h :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord g q) hq
  have hEvalP :
      g * PSTS.SignedWord.evalGroup gen p = h := by
    rw [← cayleyGraph.followWord_eq_mul_evalGroup gen g p]
    exact hEndP
  have hEvalQ :
      g * PSTS.SignedWord.evalGroup gen q = h := by
    rw [← cayleyGraph.followWord_eq_mul_evalGroup gen g q]
    exact hEndQ
  have hEq :
      PSTS.SignedWord.evalGroup gen p =
        PSTS.SignedWord.evalGroup gen q :=
    mul_left_cancel (hEvalP.trans hEvalQ.symm)
  have hRestrictedEnd :
      (cayleyGraph gen).followWord g (LabelWord.restrictTo D p) = h :=
    (cayley_followWord_restrictTo_eq_of_equal_D_word
      gen hret D g p q hEq hqD).trans hEndP
  refine ⟨LabelWord.uses_restrictTo D p, ?_⟩
  rw [← hRestrictedEnd]
  exact (cayleyGraph gen).follows_followWord g (LabelWord.restrictTo D p)

end ABO
end PSTSEPPA
