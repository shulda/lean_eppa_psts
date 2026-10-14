import PSTSEPPA.ABO.SourceH1Type1ActualG2WordAction
import PSTSEPPA.ABO.DependentDisjointWordCongruence
import PSTSEPPA.ABO.Type1OriginalLocalStageIndexEquiv

/-!
# Entire ORIGINAL source H₁ type-(1) Z₁ complete family is G₂-word-controlled

The concrete source-specific G₂ word-value equality theorem already
covers one true ambient type-(1) augmented cluster `P∪vH₁[D]`
whose anchor v lies in H₁[A]. Every genuinely anchored ORIGINAL
cluster index `(P,D,v)` has this property: the cluster P is
the union of proper A-subalphabet generated subgroups.

We therefore transfer the local theorem to EVERY original anchored
stage index and then to the complete dependent disjoint signed
action of the ENTIRE original type-(1) stage family. This is
equality of full signed word actions, not equality of ambient H₁
coordinates. It retains every (P,D,v) tag, all old/new vertices,
both signs and every legal fixed loop.

The complete original Definition-5.3 Z₁ also contains plain and
type-(2) coset-extension stages. Theorem 4.7 and higher ranks remain
independent downstream obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Actual source G₂ group-value equality induces equal
completed signed-word actions on every individual ORIGINAL
ambient source H₁ anchored augmented type-(1) stage (P,D,v). -/
theorem sourceG2OriginalH1AllType1_fibre_wordValue_congr
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ (j : ClusterSpec.augmentedType1Index
        (sourceH1Generator src dst) A)
      (x : ClusterSpec.augmentedType1Vertex j),
      (ClusterSpec.augmentedType1Stage j).followWord x p =
      (ClusterSpec.augmentedType1Stage j).followWord x q := by
  intro j x
  let gen := sourceH1Generator src dst
  let v : generatedSubgroup gen A :=
    ⟨j.2.2.1, j.1.vertexSet_mem_parentSubgroup
      gen j.2.2.1 j.2.2.2⟩
  have hv :
      v ∈ j.1.VertexSet (trivialCompletionGenerator gen A) :=
    (j.1.localVertexSet_iff_ambient gen v).mpr j.2.2.2
  exact sourceG2OriginalType1_wordValue_congr
    src dst A hcard j.1 j.2.1 v hv p q hpq x

/-- The REAL entire source original H₁ dependent signed action
of all anchored type-(1) augmented clusters has group-value
congruence containing the kernel of actual input-dependent G₂.
The family can be empty; no arbitrary representatives are added. -/
theorem sourceG2OriginalH1AllType1_family_wordValue_congr
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ x : Σ j : ClusterSpec.augmentedType1Index
        (sourceH1Generator src dst) A,
      ClusterSpec.augmentedType1Vertex j,
      (ClusterSpec.augmentedType1FamilyStage
        (sourceH1Generator src dst) A).followWord x p =
      (ClusterSpec.augmentedType1FamilyStage
        (sourceH1Generator src dst) A).followWord x q := by
  exact (dependentDisjointStage_wordEquality_all_iff
    (fun j : ClusterSpec.augmentedType1Index
      (sourceH1Generator src dst) A =>
        ClusterSpec.augmentedType1Stage j) p q).mpr
    (sourceG2OriginalH1AllType1_fibre_wordValue_congr
      src dst A hcard p q hpq)

end ABO
end PSTSEPPA
