import PSTSEPPA.PSTS.SelectedCayleyWordGeometry
import PSTSEPPA.ABO.CayleyPositivePathSupport

/-!
# Actual PSTS Cayley path-inclusion lemma (the first non-setup C2 gate)

This is the genuine nontrivial "path inclusion" lemma from the
audited finite partial-algebras/PSTS transfer note.

Let v,u be SIGNED words in chosen partial PSTS automorphisms.
Let the positive oriented-edge set of the Cayley path of u,
starting at the identity in Q, be contained in that of v.
If the two paths have the same endpoint in Q, then the
partial transformation of v is a restriction of that of u.

The crucial subtlety is formal inverse edges: traversing i^-1
from q uses the same POSITIVE edge (q*g_i^-1,i) as traversing
i from its other endpoint. To prove path inclusion we first
show that every edge actually traversed by a *defined* partial
v-word respects the actual corresponding partial generator
on the points of the original PSTS obtained by the Q-action.
Next we lift any path whose positive edges all have that
property. This argument is local to the actual Cayley graph,
and is independent of any general ABO reflection theorem.

No group content, bridge freeness, F-inverse monoid, generic
partial algebra, or maximal transporter assumption is used.
The only input is the concrete chosen TOTAL permutation lifts
(which are themselves separately constructed for any finite PSTS).
-/

namespace PSTSEPPA
namespace PSTS

variable {V ι : Type*} {A : PSTS V}
variable {gen : ι → PartialAut A}
variable (L : TotalPermutationLifts A gen)

namespace TotalPermutationLifts

/-- Value attached to a Cayley vertex q when starting the partial
word at x: apply its actual total permutation value to x. -/
def atCayleyVertex (x : V) (q : L.generatedQ) : V :=
  MulOpposite.unop (q : ABO.RightPerm V) x

@[simp]
theorem atCayleyVertex_one (x : V) :
    L.atCayleyVertex x 1 = x := by
  rfl

/-- The opposite-permutation convention ensures that multiplying
on the RIGHT by a generator applies it after the current word,
exactly matching partial-PEquiv chronological composition. -/
theorem atCayleyVertex_step (x : V)
    (q : L.generatedQ) (s : SignedLetter ι) :
    L.atCayleyVertex x
      (ABO.cayleySignedStep L.cayleyGenerator q s) =
    ABO.signedPerm L.perm s (L.atCayleyVertex x q) := by
  cases s with
  | pos i => rfl
  | neg i => rfl

/-- A positive Cayley edge e=(q,i) is validated at original
point x when the ACTUAL partial generator i is defined on
the permutation value attached to q, and maps it to the value
attached to the edge's positive endpoint q*g_i. -/
def respectsPositiveEdge (x : V)
    (e : L.generatedQ × ι) : Prop :=
  (gen e.2).toPEquiv (L.atCayleyVertex x e.1) =
    some (L.atCayleyVertex x (e.1 * L.cayleyGenerator e.2))

/-- A signed letter that is genuinely defined on its current
partial state validates the underlying positive Cayley edge,
regardless of whether that edge was traversed forwards or backwards. -/
theorem respectsPositiveEdge_of_signed_letter
    (x : V) (q : L.generatedQ) (s : SignedLetter ι)
    (hs :
      (SignedWord.evalLetter gen s).toPEquiv
        (L.atCayleyVertex x q) =
      some (L.atCayleyVertex x
        (ABO.cayleySignedStep L.cayleyGenerator q s))) :
    L.respectsPositiveEdge x
      (ABO.cayleyPositiveEdgeOfSigned L.cayleyGenerator q s) := by
  cases s with
  | pos i =>
      exact hs
  | neg i =>
      have hs' :
          (gen i).toPEquiv
            (L.atCayleyVertex x (q * (L.cayleyGenerator i)⁻¹)) =
          some (L.atCayleyVertex x q) :=
        ((gen i).toPEquiv.eq_some_iff).mp hs
      simpa [respectsPositiveEdge, ABO.cayleyPositiveEdgeOfSigned,
        mul_assoc] using hs'

/-- Conversely, if the underlying positive edge is validated,
its partial generator can be followed in EITHER signed direction. -/
theorem signed_letter_of_respectsPositiveEdge
    (x : V) (q : L.generatedQ) (s : SignedLetter ι)
    (hs : L.respectsPositiveEdge x
      (ABO.cayleyPositiveEdgeOfSigned L.cayleyGenerator q s)) :
    (SignedWord.evalLetter gen s).toPEquiv
      (L.atCayleyVertex x q) =
    some (L.atCayleyVertex x
      (ABO.cayleySignedStep L.cayleyGenerator q s)) := by
  cases s with
  | pos i => exact hs
  | neg i =>
      have hs' :
          (gen i).toPEquiv
            (L.atCayleyVertex x (q * (L.cayleyGenerator i)⁻¹)) =
          some (L.atCayleyVertex x q) := by
        simpa [respectsPositiveEdge, ABO.cayleyPositiveEdgeOfSigned,
          mul_assoc] using hs
      exact ((gen i).toPEquiv.eq_some_iff).mpr hs'

/-- Every oriented positive edge appearing in a realised signed
Cayley path of a DEFINED partial word v is validated at the
corresponding value of the actual TOTAL Q-permutation action.
Repeated visits to a Cayley vertex cause no inconsistency:
the total permutation value already forces agreement. -/
theorem respectsPositiveEdge_of_defined_word
    (x : V) (q : L.generatedQ)
    (v : SignedWord ι) (y : V)
    (hv : (SignedWord.eval gen v).toPEquiv
       (L.atCayleyVertex x q) = some y)
    (e : L.generatedQ × ι)
    (he : e ∈ ABO.cayleyWordPositiveTrace
      L.cayleyGenerator q v) :
    L.respectsPositiveEdge x e := by
  induction v generalizing q y with
  | nil =>
      simp [ABO.cayleyWordPositiveTrace] at he
  | cons s w ih =>
      change
        ((SignedWord.evalLetter gen s).toPEquiv.trans
          (SignedWord.eval gen w).toPEquiv)
          (L.atCayleyVertex x q) = some y at hv
      rw [PEquiv.trans_eq_some] at hv
      obtain ⟨mid, hs, ht⟩ := hv
      have hmid :
          mid = L.atCayleyVertex x
              (ABO.cayleySignedStep L.cayleyGenerator q s) := by
        calc
          mid = ABO.signedPerm L.perm s
              (L.atCayleyVertex x q) :=
            (L.signedLetter_extends s hs).symm
          _ = _ := (L.atCayleyVertex_step x q s).symm
      have hs' :
          (SignedWord.evalLetter gen s).toPEquiv
            (L.atCayleyVertex x q) =
          some (L.atCayleyVertex x
            (ABO.cayleySignedStep L.cayleyGenerator q s)) := by
        rw [← hmid]
        exact hs
      have htail :
          (SignedWord.eval gen w).toPEquiv
            (L.atCayleyVertex x
              (ABO.cayleySignedStep L.cayleyGenerator q s)) =
          some y := by
        rw [← hmid]
        exact ht
      have hmem : e =
            ABO.cayleyPositiveEdgeOfSigned L.cayleyGenerator q s ∨
          e ∈ ABO.cayleyWordPositiveTrace L.cayleyGenerator
            (ABO.cayleySignedStep L.cayleyGenerator q s) w := by
        simpa only [ABO.cayleyWordPositiveTrace_cons,
          List.mem_cons] using he
      rcases hmem with heq | hrest
      · subst e
        exact L.respectsPositiveEdge_of_signed_letter x q s hs'
      · exact ih (q := ABO.cayleySignedStep L.cayleyGenerator q s)
          (y := y) htail hrest

/-- Conversely, if every positive edge traversed by a signed
word u is validated at x, the ENTIRE signed partial u-word
is defined at the Q-permutation value of its starting vertex,
and its endpoint agrees with the group-valued path endpoint. -/
theorem defined_word_of_respected_trace
    (x : V) (q : L.generatedQ) (u : SignedWord ι)
    (hgood : ∀ e,
      e ∈ ABO.cayleyWordPositiveTrace L.cayleyGenerator q u →
      L.respectsPositiveEdge x e) :
    (SignedWord.eval gen u).toPEquiv (L.atCayleyVertex x q) =
    some (L.atCayleyVertex x
      (q * SignedWord.evalGroup L.cayleyGenerator u)) := by
  induction u generalizing q with
  | nil =>
      change (PEquiv.refl V) (L.atCayleyVertex x q) =
        some (L.atCayleyVertex x (q * 1))
      simp
  | cons s w ih =>
      let q' := ABO.cayleySignedStep L.cayleyGenerator q s
      have hs :
          L.respectsPositiveEdge x
            (ABO.cayleyPositiveEdgeOfSigned L.cayleyGenerator q s) := by
        apply hgood
        simp only [ABO.cayleyWordPositiveTrace_cons,
          List.mem_cons, true_or]
      have htailgood : ∀ e,
          e ∈ ABO.cayleyWordPositiveTrace L.cayleyGenerator q' w →
          L.respectsPositiveEdge x e := by
        intro e he
        apply hgood
        simpa only [ABO.cayleyWordPositiveTrace_cons, List.mem_cons]
          using (Or.inr he :
            e = ABO.cayleyPositiveEdgeOfSigned L.cayleyGenerator q s ∨
            e ∈ ABO.cayleyWordPositiveTrace L.cayleyGenerator q' w)
      have hfirst :
          (SignedWord.evalLetter gen s).toPEquiv
            (L.atCayleyVertex x q) =
          some (L.atCayleyVertex x q') :=
        L.signed_letter_of_respectsPositiveEdge x q s hs
      have hrest := ih (q := q') htailgood
      have hend :
          q' * SignedWord.evalGroup L.cayleyGenerator w =
          q * SignedWord.evalGroup L.cayleyGenerator (s :: w) := by
        simp [q', ABO.cayleySignedStep,
          SignedWord.evalGroup_cons, mul_assoc]
      have hrest' :
          (SignedWord.eval gen w).toPEquiv
            (L.atCayleyVertex x q') =
          some (L.atCayleyVertex x
            (q * SignedWord.evalGroup L.cayleyGenerator (s :: w))) := by
        rw [← hend]
        exact hrest
      change
        ((SignedWord.evalLetter gen s).toPEquiv.trans
          (SignedWord.eval gen w).toPEquiv)
          (L.atCayleyVertex x q) =
        some (L.atCayleyVertex x
          (q * SignedWord.evalGroup L.cayleyGenerator (s :: w)))
      rw [PEquiv.trans_eq_some]
      exact ⟨L.atCayleyVertex x q', hfirst, hrest'⟩

/-- THE CONCRETE CAYLEY PATH-INCLUSION LEMMA used to obtain
fibre-MAX from the reflecting finite group.

Let u,v be signed words, with the SAME Cayley Q-value.
If every underlying positive oriented edge traversed by u
also occurs somewhere on the Cayley path v starting at 1,
then the partial transformation of v is a restriction of u.

The theorem handles inverse traversals, repeated Cayley
vertices, trivial selected permutations and empty words,
using no unproved group reflection/content hypothesis. -/
theorem partial_le_of_positiveCayleyTrace_subset
    (u v : SignedWord ι)
    (hQ : L.valueQ u = L.valueQ v)
    (hIncluded : ∀ e : L.generatedQ × ι,
      e ∈ ABO.cayleyWordPositiveTrace
        L.cayleyGenerator 1 u →
      e ∈ ABO.cayleyWordPositiveTrace
        L.cayleyGenerator 1 v) :
    (SignedWord.eval gen v).toPEquiv ≤
      (SignedWord.eval gen u).toPEquiv := by
  intro x y hv
  have hv' :
      (SignedWord.eval gen v).toPEquiv x = some y := by
    simpa only [Option.mem_def] using hv
  have hGoodV : ∀ e : L.generatedQ × ι,
      e ∈ ABO.cayleyWordPositiveTrace L.cayleyGenerator 1 v →
      L.respectsPositiveEdge x e := by
    intro e he
    apply L.respectsPositiveEdge_of_defined_word
      x 1 v y
    · simpa only [L.atCayleyVertex_one] using hv'
    · exact he
  have hGoodU : ∀ e : L.generatedQ × ι,
      e ∈ ABO.cayleyWordPositiveTrace L.cayleyGenerator 1 u →
      L.respectsPositiveEdge x e := by
    intro e he
    exact hGoodV e (hIncluded e he)
  have hu :=
    L.defined_word_of_respected_trace x 1 u hGoodU
  have hvPoint : L.atCayleyVertex x (L.valueQ v) = y := by
    have h := L.partial_word_agrees_with_total v hv'
    exact h
  have huPoint : L.atCayleyVertex x (L.valueQ u) = y := by
    rw [hQ]
    exact hvPoint
  have hu' :
      (SignedWord.eval gen u).toPEquiv x = some y := by
    rw [L.atCayleyVertex_one, one_mul,
      L.selectedCayley_wordValue_eq_valueQ, huPoint] at hu
    exact hu
  simpa only [Option.mem_def] using hu'

end TotalPermutationLifts
end PSTS
end PSTSEPPA
