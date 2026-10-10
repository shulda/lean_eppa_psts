import PSTSEPPA.ABO.RankTwoComponentBase

/-!
# Singleton-alphabet dichotomy relative to a rank-two parent

The corrected ABO k=1 stage-kernel test is quantified over
ALL subalphabets of cardinality at most one, not merely over
the proper subalphabets selected in the rank-two coset family.

When the parent A has cardinality two, every C with |C|≤1
is either a PROPER subalphabet of A, or is DISJOINT from A:
a nonempty such C is exactly one singleton, so any shared
letter forces C⊆A; cardinality then rules out C=A.

We formalize this exact dichotomy independently of stage
geometry, to combine the certified proper-C word kernels
with the separate outside-A trivial-loop kernel. Empty
C, arbitrary finite generator alphabets and degenerate
generator values pose no exceptions.
-/

namespace PSTSEPPA
namespace ABO

variable {ι : Type*} [DecidableEq ι]

/-- Every empty/singleton alphabet is either contained
in A or disjoint from A, even if A is empty. -/
theorem small_alphabet_subset_or_disjoint
    (A C : Finset ι)
    (hCcard : C.card ≤ 1) :
    C ⊆ A ∨ Disjoint C A := by
  classical
  by_cases hCA : C ⊆ A
  · exact Or.inl hCA
  · right
    apply Finset.disjoint_left.mpr
    intro i hiC hiA
    apply hCA
    intro j hjC
    have hji : j = i :=
      (Finset.card_le_one.mp hCcard) j hjC i hiC
    simpa [hji] using hiA

/-- Under |A|=2, every alphabet on at most one letter
either is a selected PROPER subalphabet or is disjoint
from A. This is the finite combinatorial dichotomy used
to close ALL singleton labels in Proposition 5.4 R2. -/
theorem small_alphabet_proper_or_disjoint_rank_two
    (A C : Finset ι)
    (hAcard : A.card = 2)
    (hCcard : C.card ≤ 1) :
    C ⊂ A ∨ Disjoint C A := by
  rcases small_alphabet_subset_or_disjoint A C hCcard with
    hCA | hdis
  · left
    have hne : C ≠ A := by
      intro hCAeq
      have hn : C.card = A.card :=
        congrArg Finset.card hCAeq
      omega
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hCA, hne⟩
  · exact Or.inr hdis

end ABO
end PSTSEPPA
