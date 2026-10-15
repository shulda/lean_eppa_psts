import PSTSEPPA.ABO.SourceOriginalH1Z1StageFiniteness
import PSTSEPPA.ABO.LabelledGroupSubalphabetCosetTransport
import PSTSEPPA.ABO.SourceLiteralY1TaggedCosetAttachments

/-!
# Finite exact literal paper T(Y₁) type-(1) anchored-augmentation indices

The corrected ABO Definition-5.3 first-rank anchored type-(1)
stages are indexed by:
* an actual two-letter alphabet A;
* a finite family P of genuine strictly proper A-subalphabets;
* a proper attached subalphabet D⊊A; and
* a REAL cluster anchor v in the union of the P-subgroups.

The source-H₁ indices have already been checked to be finite.
Here we define the same *literal-paper* type with ambient group
T(Y₁), independently of any undocumented representatives, and
construct an exact bijection between EVERY printed paper anchor
and its unique SourceH₁ cluster anchor by the certified
generator-preserving group isomorphism. Crucially, old cluster
membership is transported piece-by-piece, not by ambient value
comparison after an unexplained quotient.

The full dependent paper/source type-(1) index sets are therefore
equivalent and genuinely finite. Comparing the corresponding
SIGNED and legally loop-completed augmented action fibres (and
G₂ word kernels) is a separate following gate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Exactly the LITERAL printed paper-H₁=T(Y₁) original type-(1)
anchored augmentation stage index, retaining (A,P,D,v) and
membership proof in the true subgroup-cluster vertex union. -/
abbrev sourceLiteralY1Type1Index (src dst : ι → V) :=
  Σ A : {A : Finset ι // A.card = 2},
    ClusterSpec.augmentedType1Index
      (sourceLiteralY1 src dst).transitionSubgroupGenerator A.1

/-- Exact equivalence of REAL old cluster anchored vertex carriers
under the same-labelled source/paper group equivalence.
Each original P-subgroup tag survives; no ambient coset folding. -/
noncomputable def sourceLiteralY1Type1ClusterAnchorEquiv
    (src dst : ι → V)
    {A : Finset ι} (P : ClusterSpec A) :
    {v : (sourceLiteralY1 src dst).transitionGroup //
      v ∈ P.VertexSet (sourceLiteralY1 src dst).transitionSubgroupGenerator} ≃
    {v : SourceH1 src dst // v ∈ P.VertexSet (sourceH1Generator src dst)} where
  toFun x :=
    ⟨(sourceH1EquivLiteralY1Transition src dst).symm x.1, by
      obtain ⟨C, hCP, hC⟩ := x.2
      refine ⟨C, hCP, ?_⟩
      exact (labelledMulEquiv_mem_generatedSubgroup_iff
        (sourceLiteralY1 src dst).transitionSubgroupGenerator
        (sourceH1Generator src dst)
        (sourceH1EquivLiteralY1Transition src dst).symm
        (sourceLiteralY1Generator_to_sourceH1 src dst)
        C x.1).mpr hC⟩
  invFun y :=
    ⟨sourceH1EquivLiteralY1Transition src dst y.1, by
      obtain ⟨C, hCP, hC⟩ := y.2
      refine ⟨C, hCP, ?_⟩
      exact (labelledMulEquiv_mem_generatedSubgroup_iff
        (sourceH1Generator src dst)
        (sourceLiteralY1 src dst).transitionSubgroupGenerator
        (sourceH1EquivLiteralY1Transition src dst)
        (sourceH1EquivLiteralY1Transition_generator src dst)
        C y.1).mpr hC⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    simp

/-- The complete genuine printed (A,P,D,v) anchored type-(1)
stage INDEX is equivalent to the previously certified exact
source-H₁ index, with A,P,D unchanged and v transported
through the unique generator-preserving group equivalence. -/
noncomputable def sourceLiteralY1Type1IndexEquiv
    (src dst : ι → V) :
    sourceLiteralY1Type1Index src dst ≃
      sourceOriginalH1Type1Index src dst where
  toFun j :=
    ⟨j.1, ⟨j.2.1, ⟨j.2.2.1,
      sourceLiteralY1Type1ClusterAnchorEquiv src dst j.2.1 j.2.2.2⟩⟩⟩
  invFun j :=
    ⟨j.1, ⟨j.2.1, ⟨j.2.2.1,
      (sourceLiteralY1Type1ClusterAnchorEquiv src dst j.2.1).symm j.2.2.2⟩⟩⟩
  left_inv := by
    rintro ⟨a, ⟨p, ⟨d, v⟩⟩⟩
    change (⟨a, ⟨p, ⟨d,
      (sourceLiteralY1Type1ClusterAnchorEquiv src dst p).symm
        (sourceLiteralY1Type1ClusterAnchorEquiv src dst p v)⟩⟩⟩ :
        sourceLiteralY1Type1Index src dst) =
      ⟨a, ⟨p, ⟨d, v⟩⟩⟩
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨a, ⟨p, ⟨d, v⟩⟩⟩
    change (⟨a, ⟨p, ⟨d,
      sourceLiteralY1Type1ClusterAnchorEquiv src dst p
        ((sourceLiteralY1Type1ClusterAnchorEquiv src dst p).symm v)⟩⟩⟩ :
        sourceOriginalH1Type1Index src dst) =
      ⟨a, ⟨p, ⟨d, v⟩⟩⟩
    rw [Equiv.apply_symm_apply]

/-- The actual printed type-(1) stage INDEX set is finite,
derived from the independently constructed concrete finite
source-H₁ group and exact anchor equivalence, not postulated. -/
theorem finite_sourceLiteralY1Type1Index
    (src dst : ι → V) :
    Finite (sourceLiteralY1Type1Index src dst) := by
  classical
  letI : Finite (sourceOriginalH1Type1Index src dst) :=
    finite_sourceOriginalH1Type1Index src dst
  exact Finite.of_injective
    (sourceLiteralY1Type1IndexEquiv src dst)
    (sourceLiteralY1Type1IndexEquiv src dst).injective

end ABO
end PSTSEPPA
