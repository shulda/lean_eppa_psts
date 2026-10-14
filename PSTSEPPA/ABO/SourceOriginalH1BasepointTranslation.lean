import PSTSEPPA.ABO.SourceOriginalH1PreimageSkeleton
import PSTSEPPA.ABO.CayleyLeftTranslations

/-!
# Basepoint translation of the ORIGINAL incomplete H₁ Cayley preimage

The canonical source H₁ cover depends on an initial vertex of the
complete X₁ action. When a second initial vertex belongs to the
same actual H₁ orbit, changing basepoint corresponds EXACTLY
to a left translation of the H₁ Cayley coordinate.

Crucially, this acts on the *genuine old-edge preimage graph*,
not on the artificially completed X₁ graph. It is a signed
labelled graph isomorphism with a bijection of all original
vertices and oriented edge tokens, even with inverse letters,
parallel labels and geometric loops.

This is the source-specific basepoint normalization required
when comparing EVERY Definition-5.3 original H₁-cover to the
finite source rank-one stage catalogue. It does not assert the
remaining completed stage selection/augmentation equivalences,
Condition 5.2, Theorem 4.7 or unconditional PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The true X₁ orbit of the generated H₁ group is a right
action in the precise chronological word convention.
Left multiplication by t in the H₁ Cayley coordinate
therefore changes the canonical X₁ basepoint to its t-image. -/
theorem sourceH1Orbit_mul
    (src dst : ι → V) (base : V)
    (t h : SourceH1 src dst) :
    sourceH1Orbit src dst base (t * h) =
      sourceH1Orbit src dst
        (sourceH1Orbit src dst base t) h := by
  let Q := unarySynchronizedCoverQuotient
    (sourceG1Generator src dst)
    (sourceG1Generator_isGenerated src dst)
  change CompleteEGraph.rightApply (Q.hom (t * h)) base =
    CompleteEGraph.rightApply (Q.hom h)
      (CompleteEGraph.rightApply (Q.hom t) base)
  rw [map_mul]
  change CompleteEGraph.rightApply ((Q.hom t).1 * (Q.hom h).1) base =
    CompleteEGraph.rightApply (Q.hom h).1
      (CompleteEGraph.rightApply (Q.hom t).1 base)
  exact CompleteEGraph.rightApply_mul (Q.hom t).1 (Q.hom h).1 base

/-- Exact old-oriented-edge support under source basepoint
translation. Both sides are the real ORIGINAL edge-preimage
predicate, not the completion-edge predicate of X₁. -/
theorem sourceH1OriginalSkeleton_translate_edge_iff
    (src dst : ι → V) (base : V)
    (t : SourceH1 src dst) (e : ActionEdge (SourceH1 src dst) ι) :
    (t * e.1, e.2) ∈ (sourceH1OriginalSkeleton src dst base).edges ↔
      e ∈ (sourceH1OriginalSkeleton src dst
        (sourceH1Orbit src dst base t)).edges := by
  change sourceH1Orbit src dst base (t * e.1) =
      sourceInputSignedSource src dst e.2 ↔
    sourceH1Orbit src dst (sourceH1Orbit src dst base t) e.1 =
      sourceInputSignedSource src dst e.2
  rw [sourceH1Orbit_mul]

/-- Actual labelled EGraph morphism from the original-edge
H₁ preimage at the shifted basepoint to that at the old
basepoint. On both signed vertices and directed edge tokens
this map is LITERAL LEFT MULTIPLICATION BY t.
No completion edges or arbitrary component representatives. -/
noncomputable def sourceH1OriginalSkeleton_translateHom
    (src dst : ι → V) (base : V) (t : SourceH1 src dst) :
    LabelledGraphHom
      ((sourceH1OriginalSkeleton src dst
        (sourceH1Orbit src dst base t)).toEGraph).toLabelledGraph
      ((sourceH1OriginalSkeleton src dst base).toEGraph).toLabelledGraph where
  onVertex x := ⟨t * x.1, by trivial⟩
  onEdge e := ⟨(t * e.1.1, e.1.2),
    (sourceH1OriginalSkeleton_translate_edge_iff
      src dst base t e.1).mpr e.2⟩
  map_source := by
    intro e
    apply Subtype.ext
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    exact (cayleyLeftTranslateHom
      (sourceH1Generator src dst) t).map_inv e.1
  map_label := by
    intro e
    rfl

/-- The basepoint-translation graph morphism is an ISOMORPHISM:
it is bijective on actual H₁ vertices AND on every original
oriented signed edge token, including formal inverse tokens
for geometric loops. This is not just surjectivity of X₁
vertex coordinates. -/
theorem sourceH1OriginalSkeleton_translateHom_bijective
    (src dst : ι → V) (base : V) (t : SourceH1 src dst) :
    Function.Bijective
      (sourceH1OriginalSkeleton_translateHom src dst base t).onVertex ∧
    Function.Bijective
      (sourceH1OriginalSkeleton_translateHom src dst base t).onEdge := by
  have hcancel (x : SourceH1 src dst) :
      t * (t⁻¹ * x) = x := by
    calc
      t * (t⁻¹ * x) = (t * t⁻¹) * x := (mul_assoc t t⁻¹ x).symm
      _ = x := by simp
  constructor
  · constructor
    · intro x y h
      apply Subtype.ext
      exact mul_left_cancel (congrArg Subtype.val h)
    · intro y
      refine ⟨⟨t⁻¹ * y.1, by trivial⟩, ?_⟩
      apply Subtype.ext
      exact hcancel y.1
  · constructor
    · intro e f hef
      have heq :
          (t * e.1.1, e.1.2) = (t * f.1.1, f.1.2) :=
        congrArg Subtype.val hef
      have hparts :
          t * e.1.1 = t * f.1.1 ∧ e.1.2 = f.1.2 := by
        simpa only [Prod.mk.injEq] using heq
      apply Subtype.ext
      exact Prod.ext (mul_left_cancel hparts.1) hparts.2
    · intro e
      have hmem :
          (t⁻¹ * e.1.1, e.1.2) ∈
            (sourceH1OriginalSkeleton src dst
              (sourceH1Orbit src dst base t)).edges := by
        apply (sourceH1OriginalSkeleton_translate_edge_iff
          src dst base t (t⁻¹ * e.1.1, e.1.2)).mp
        have hold : sourceH1Orbit src dst base e.1.1 =
            sourceInputSignedSource src dst e.1.2 := e.2
        change sourceH1Orbit src dst base
          (t * (t⁻¹ * e.1.1)) =
          sourceInputSignedSource src dst e.1.2
        rw [hcancel]
        exact hold
      refine ⟨⟨(t⁻¹ * e.1.1, e.1.2), hmem⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact hcancel e.1.1
      · rfl

end ABO
end PSTSEPPA
