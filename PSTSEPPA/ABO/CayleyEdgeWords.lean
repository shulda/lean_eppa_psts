import PSTSEPPA.ABO.CayleySemidirectWordValue

/-!
# True Cayley paths as signed words in the POSITIVE EDGE alphabet E = Q × ι

The corrected ABO Lemma 5.6 operates on signed E-words, where E is
the set of actual positive oriented edges, NOT on the smaller label
alphabet ι of selected PSTS partial automorphisms.

A Cayley path written as a signed ι-word has a precise, position-
dependent signed E-word. For a forward step i from q its letter is
+(q,i); for a reverse step i⁻¹ from q it is -(q*gen(i)⁻¹,i).
This module constructs that word and proves:

* evaluating the E-word in any group G gives exactly the previously
  certified actual Cayley path G-value;
* forgetting signs from the E-word gives the exact positive-edge
  trace used for fibre-MAX, with repetitions and inverse traversals.

These identities prepare the group-generator deletion/retraction
part of ABO Lemma 5.6. In particular, deleting an E-generator
must not be mistaken for deleting an ι-letter, since the latter
changes the intervening Cayley path vertices.
-/

namespace PSTSEPPA
namespace ABO

variable {G Q ι : Type*} [Group Q] [Group G]

/-- The signed positive-edge token for a genuine signed Cayley
step from q, including the correct base of a reverse traversal. -/
def cayleySignedEdge (gen : ι → Q) (q : Q) :
    SignedLabel ι → SignedLabel (Q × ι)
  | .pos i => .pos (q,i)
  | .neg i => .neg (q * (gen i)⁻¹,i)

/-- Forget the traversal direction but retain the ORIENTED
positive-edge identity, including the initial vertex coordinate. -/
def signedPositiveBase : SignedLabel (Q × ι) → Q × ι
  | .pos e => e
  | .neg e => e

@[simp]
theorem signedPositiveBase_cayleySignedEdge
    (gen : ι → Q) (q : Q) (s : SignedLabel ι) :
    signedPositiveBase (cayleySignedEdge gen q s) =
      cayleyPositiveEdgeOfSigned gen q s := by
  cases s <;> rfl

/-- Convert a signed label word into the actual signed word
of visited positive Cayley edges, with position-dependent bases. -/
def cayleyEdgeWord
    (gen : ι → Q) (q : Q) : LabelWord ι → LabelWord (Q × ι)
  | [] => []
  | s :: w =>
      cayleySignedEdge gen q s ::
        cayleyEdgeWord gen (cayleySignedStep gen q s) w

@[simp]
theorem cayleyEdgeWord_nil
    (gen : ι → Q) (q : Q) :
    cayleyEdgeWord gen q ([] : LabelWord ι) = [] := rfl

@[simp]
theorem cayleyEdgeWord_cons
    (gen : ι → Q) (q : Q) (s : SignedLabel ι)
    (w : LabelWord ι) :
    cayleyEdgeWord gen q (s :: w) =
      cayleySignedEdge gen q s ::
        cayleyEdgeWord gen (cayleySignedStep gen q s) w := rfl

/-- The TRUE signed positive-edge word evaluates to exactly the
Cayley path's previously verified G-value, including reverse edges. -/
theorem cayleyEdgeWord_eval
    (gen : ι → Q) (edge : Q × ι → G)
    (q : Q) (w : LabelWord ι) :
    PSTS.SignedWord.evalGroup edge (cayleyEdgeWord gen q w) =
      cayleyPathGroupValue gen edge q w := by
  induction w generalizing q with
  | nil =>
      rfl
  | cons s w ih =>
      cases s with
      | pos i =>
          change edge (q,i) *
              PSTS.SignedWord.evalGroup edge
                (cayleyEdgeWord gen (q * gen i) w) =
            edge (q,i) * cayleyPathGroupValue gen edge (q * gen i) w
          rw [ih]
      | neg i =>
          change (edge (q * (gen i)⁻¹,i))⁻¹ *
              PSTS.SignedWord.evalGroup edge
                (cayleyEdgeWord gen (q * (gen i)⁻¹) w) =
            (edge (q * (gen i)⁻¹,i))⁻¹ *
              cayleyPathGroupValue gen edge (q * (gen i)⁻¹) w
          rw [ih]

/-- Forgetting signs of the genuine signed E-word gives the
complete literal list of positive Cayley edges traversed,
with repeats and both orientations handled correctly. -/
theorem cayleyEdgeWord_bases
    (gen : ι → Q) (q : Q) (w : LabelWord ι) :
    (cayleyEdgeWord gen q w).map signedPositiveBase =
      cayleyWordPositiveTrace gen q w := by
  induction w generalizing q with
  | nil =>
      rfl
  | cons s w ih =>
      simp only [cayleyEdgeWord_cons, List.map_cons,
        cayleyWordPositiveTrace_cons,
        signedPositiveBase_cayleySignedEdge,
        ih (q := cayleySignedStep gen q s)]

end ABO
end PSTSEPPA
