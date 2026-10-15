import PSTSEPPA.ABO.SourceLiteralY1DirectTransportedCoverIso
import PSTSEPPA.ABO.SourceOriginalH1LocalCoverIndex

/-!
# Reindex the literal original H₁ cover components over the paper's T(Y₁)

The first-rank source-index catalogue was previously constructed using
the synchronized SourceH₁ model. Every index remembers:
  original source basepoint, an actual two-letter alphabet A,
  and a specified group point h above that basepoint.
The old A-component of the original incomplete cover at that
point is the intrinsic connected skeleton used for the G₂
all-local stage catalogue.

The literal paper presentation has group T(Y₁), and its independently
DIRECT original-edge cover is now certified to be isomorphic to the
source model over the same input EGraph.

This module gives a genuine equivalence between the ENTIRE FINITE
source and literal paper cover-index types: simply transport the
specified H₁ group root under the generator-preserving
SourceH₁ ≃* T(Y₁) isomorphism, without choosing a representative
of any quotient class. Basepoint and alphabet are unchanged.

We verify that the corresponding roots project to exactly the same
original input vertex, that every original oriented signed edge
at the specified roots is present on one side if and only if on
the other side, and that the literal index catalogue is finite.
Each index names the ACTUAL intrinsic A-component in the literal
paper original-edge preimage, not the entire ambient H₁[A] coset.

This is the exact original-cover source-index comparison.
It does NOT by itself classify the selected full/augmented completed
Z₁ stages or establish their equivalence/equivariance; those are
the next genuinely geometric Definition-5.3 gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- A literal paper T(Y₁) original-input-cover index:
one original base vertex, one genuine rank-two alphabet,
and one ACTUAL T(Y₁) Cayley preimage root (not a chosen
coset representative or a completed graph vertex). -/
abbrev SourceLiteralY1CoverIndex
    (src dst : ι → V) :=
  Σ base : V, Σ a : {A : Finset ι // A.card = 2},
    (sourceLiteralY1 src dst).transitionGroup

/-- The exact bijection between ALL true source model H₁-cover
indices and ALL paper T(Y₁)-cover indices, preserving the original
basepoint and the two-letter alphabet literally. There is no
quotient by ambient group coordinates or arbitrary root choice. -/
noncomputable def sourceOriginalH1CoverIndexEquivLiteral
    (src dst : ι → V) :
    SourceOriginalH1CoverIndex src dst ≃
      SourceLiteralY1CoverIndex src dst where
  toFun j :=
    ⟨j.1, j.2.1,
      sourceH1EquivLiteralY1Transition src dst j.2.2⟩
  invFun j :=
    ⟨j.1, j.2.1,
      (sourceH1EquivLiteralY1Transition src dst).symm j.2.2⟩
  left_inv := by
    intro j
    rcases j with ⟨base, ⟨a, h⟩⟩
    simp
  right_inv := by
    intro j
    rcases j with ⟨base, ⟨a, h⟩⟩
    simp

/-- Exactly the same original INPUT basepoint, with no
identification of otherwise distinct preimage Cayley roots. -/
@[simp] theorem sourceOriginalH1CoverIndexEquivLiteral_base
    (src dst : ι → V) (j : SourceOriginalH1CoverIndex src dst) :
    (sourceOriginalH1CoverIndexEquivLiteral src dst j).1 = j.1 :=
  rfl

/-- Exactly the same original two-letter alphabet, not a
different or larger generated subgroup. -/
@[simp] theorem sourceOriginalH1CoverIndexEquivLiteral_alphabet
    (src dst : ι → V) (j : SourceOriginalH1CoverIndex src dst) :
    (sourceOriginalH1CoverIndexEquivLiteral src dst j).2.1 = j.2.1 :=
  rfl

/-- This is a LITERAL finite family of all possible original
paper H₁ preimage roots at all original input base vertices
and all two-letter generator alphabets. The finiteness is
derived from finite T(Y₁), not postulated as an index axiom. -/
theorem finite_SourceLiteralY1CoverIndex
    (src dst : ι → V) :
    Finite (SourceLiteralY1CoverIndex src dst) := by
  classical
  letI : Finite (sourceLiteralY1 src dst).transitionGroup :=
    finite_sourceLiteralY1TransitionGroup src dst
  infer_instance

/-- The actual old signed two-letter skeleton at a literal
paper cover index, retaining ONLY real original input edges. -/
noncomputable abbrev sourceLiteralY1CoverIndexSkeleton
    (src dst : ι → V) (j : SourceLiteralY1CoverIndex src dst) :=
  (sourceLiteralY1DirectOriginalSkeleton src dst j.1).restrictAlphabet
    j.2.1.1

/-- The selected literal T(Y₁) root point in the exact old
two-letter preimage graph, independently of any component
or coset quotient representative selection. -/
noncomputable def sourceLiteralY1CoverIndexRoot
    (src dst : ι → V) (j : SourceLiteralY1CoverIndex src dst) :
    (sourceLiteralY1CoverIndexSkeleton src dst j).Vertex :=
  ⟨j.2.2, by trivial⟩

/-- The TRUE rooted A-connected component in the direct
paper-H₁ old-edge preimage. This is NOT its complete ambient
group coset and not the artificial initial X₁ action. -/
noncomputable abbrev sourceLiteralY1CoverIndexComponent
    (src dst : ι → V) (j : SourceLiteralY1CoverIndex src dst) :=
  (sourceLiteralY1CoverIndexSkeleton src dst j).subalphabetComponentSubgraph
    j.2.1.1 (sourceLiteralY1CoverIndexRoot src dst j)

/-- Under the finite cover-index equivalence, the actual T(Y₁)
original-edge Cayley root projects to exactly the SAME original
input vertex as the corresponding synchronized SourceH₁ root. -/
theorem sourceOriginalH1CoverIndexEquivLiteral_root_projection
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst) :
    sourceLiteralY1Orbit src dst j.1
      (sourceOriginalH1CoverIndexEquivLiteral src dst j).2.2 =
    sourceH1Orbit src dst j.1 j.2.2 := by
  exact sourceLiteralY1Orbit_equiv_sourceH1Orbit
    src dst j.1 j.2.2

/-- A genuine old oriented signed input edge begins at the
literal paper cover root precisely when that same signed edge
begins at the corresponding SourceH₁ root. This equality is
stronger than equality of the initial complete X₁ endpoints. -/
theorem sourceOriginalH1CoverIndexEquivLiteral_root_edge_iff
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst)
    (s : SignedLabel ι) :
    ((sourceOriginalH1CoverIndexEquivLiteral src dst j).2.2,s) ∈
        (sourceLiteralY1DirectOriginalSkeleton src dst j.1).edges ↔
      (j.2.2,s) ∈
        (sourceH1OriginalSkeleton src dst j.1).edges := by
  exact sourceLiteralY1DirectOriginal_edge_iff_sourceH1
    src dst j.1 j.2.2 s

end ABO
end PSTSEPPA
