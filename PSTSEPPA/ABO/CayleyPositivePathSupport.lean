import PSTSEPPA.ABO.CayleyGraph
import Mathlib.Data.Finset.Basic

/-!
# Actual positive-edge traces of signed paths in a Cayley graph

The audited PSTS Cayley/MAX transfer uses the ORIENTED Cayley graph
of a finite permutation group Q, whose positive edge set is
E = Q × P. Paths may traverse a positive edge in the forward or
backward direction. The underlying positive edge must be recorded
consistently in both cases:

* a positive letter p at vertex q uses positive edge (q,p);
* a negative letter p⁻¹ at vertex q traverses backwards the
  positive edge (q * lift(p)⁻¹, p).

This is the exact edge support notion in the path-inclusion
lemma needed for finite fibre-MAX. We define the underlying
positive edge trace of a signed word, and prove formal reversal
of one edge preserves its positive edge, left Q-translation
transports the trace, and the successive group vertices use the
same chronological convention as PSTS partial word evaluation.

No reflecting group or content theorem is assumed here.
-/

namespace PSTSEPPA
namespace ABO

variable {Q ι : Type*} [Group Q]

/-- The underlying oriented POSITIVE edge traversed at q by a signed
letter s. Negative traversal takes the inverse of the positive edge
based at the endpoint, not a new positive edge at q. -/
def cayleyPositiveEdgeOfSigned
    (gen : ι → Q) (q : Q) : SignedLabel ι → Q × ι
  | .pos i => (q, i)
  | .neg i => (q * (gen i)⁻¹, i)

/-- The vertex reached after one signed Cayley step. -/
def cayleySignedStep (gen : ι → Q) (q : Q) (s : SignedLabel ι) : Q :=
  q * PSTS.SignedWord.evalGroupLetter gen s

@[simp]
theorem cayleySignedStep_pos
    (gen : ι → Q) (q : Q) (i : ι) :
    cayleySignedStep gen q (.pos i) = q * gen i := rfl

@[simp]
theorem cayleySignedStep_neg
    (gen : ι → Q) (q : Q) (i : ι) :
    cayleySignedStep gen q (.neg i) = q * (gen i)⁻¹ := rfl

/-- Reversing a signed traversal records the SAME positive edge.
This includes geometric loops and trivial permutation labels. -/
theorem cayleyPositiveEdgeOfSigned_inv
    (gen : ι → Q) (q : Q) (s : SignedLabel ι) :
    cayleyPositiveEdgeOfSigned gen q s =
      cayleyPositiveEdgeOfSigned gen
        (cayleySignedStep gen q s) (PSTS.SignedLetter.inv s) := by
  cases s with
  | pos i =>
      simp [cayleyPositiveEdgeOfSigned, cayleySignedStep,
        PSTS.SignedWord.evalGroupLetter, mul_assoc]
  | neg i =>
      rfl

/-- Under LEFT translation of the Cayley graph, positive edge
(e,p) becomes (g*e,p). Both traversal orientations obey this law. -/
theorem cayleyPositiveEdgeOfSigned_left
    (gen : ι → Q) (g q : Q) (s : SignedLabel ι) :
    cayleyPositiveEdgeOfSigned gen (g * q) s =
      (g * (cayleyPositiveEdgeOfSigned gen q s).1,
       (cayleyPositiveEdgeOfSigned gen q s).2) := by
  cases s <;> simp [cayleyPositiveEdgeOfSigned, mul_assoc]

/-- Exact LIST of positive edge tokens traversed by a signed word
from a chosen starting Cayley group vertex. Keeps repetitions; the
finite support of the path is obtained by List.toFinset. -/
def cayleyWordPositiveTrace
    (gen : ι → Q) (q : Q) : LabelWord ι → List (Q × ι)
  | [] => []
  | s :: w =>
      cayleyPositiveEdgeOfSigned gen q s ::
        cayleyWordPositiveTrace gen (cayleySignedStep gen q s) w

@[simp]
theorem cayleyWordPositiveTrace_nil
    (gen : ι → Q) (q : Q) :
    cayleyWordPositiveTrace gen q ([] : LabelWord ι) = [] := rfl

@[simp]
theorem cayleyWordPositiveTrace_cons
    (gen : ι → Q) (q : Q)
    (s : SignedLabel ι) (w : LabelWord ι) :
    cayleyWordPositiveTrace gen q (s :: w) =
      cayleyPositiveEdgeOfSigned gen q s ::
        cayleyWordPositiveTrace gen (cayleySignedStep gen q s) w := rfl

/-- The visited positive edge SET of a signed Cayley path, used
when formalizing inclusion of the underlying spanned subgraphs.
It records the positive edge of a backwards step correctly. -/
def cayleyWordPositiveSupport [DecidableEq Q] [DecidableEq ι]
    (gen : ι → Q) (q : Q) (w : LabelWord ι) : Finset (Q × ι) :=
  (cayleyWordPositiveTrace gen q w).toFinset

/-- Left Q-translation commutes with each signed word's group-step. -/
theorem cayleySignedStep_left
    (gen : ι → Q) (g q : Q) (s : SignedLabel ι) :
    cayleySignedStep gen (g * q) s =
      g * cayleySignedStep gen q s := by
  simp [cayleySignedStep, mul_assoc]

/-- Left Q-translations carry the entire literal positive-edge
TRACE to the left-translated trace. This is the exact symmetry of
edge content needed by the Cayley-GRL application. -/
theorem cayleyWordPositiveTrace_left
    (gen : ι → Q) (g q : Q) (w : LabelWord ι) :
    cayleyWordPositiveTrace gen (g * q) w =
      (cayleyWordPositiveTrace gen q w).map
        (fun e => (g * e.1, e.2)) := by
  induction w generalizing q with
  | nil =>
      rfl
  | cons s w ih =>
      simp only [cayleyWordPositiveTrace_cons, List.map_cons]
      congr 1
      · exact cayleyPositiveEdgeOfSigned_left gen g q s
      · rw [cayleySignedStep_left]
        exact ih (q := cayleySignedStep gen q s)

end ABO
end PSTSEPPA
