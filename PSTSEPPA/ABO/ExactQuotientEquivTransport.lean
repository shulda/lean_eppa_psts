import PSTSEPPA.ABO.MultiCosetVertexQuotient

/-!
# Exact transport of quotient setoids under a bijective relation morphism

The corrected ABO coset-extension vertex object is the QUOTIENT of
the actual alphabet-indexed, component-tagged attached coset pieces
by common intersection support (not by ambient coordinate equality).

When a genuine signed-graph/component/coset translation provides a
bijection of these raw tagged pieces preserving AND reflecting the
literal gluing relation, two things follow:

* The target gluing relation is an equivalence relation whenever
  the source one is (even if the target ambient group is only
  k-retractable and not globally retractable).
* The resulting glued VERTEX QUOTIENTS are genuinely equivalent;
  the induced map sends each raw quotient class to precisely the
  class of its transported raw representative.

We formalize these two source-agnostic logical steps to permit the
next source-specific lemma using the actual ABO MultiCosetRawRelated
and the previously checked rooted attached-coset/gluing naturality.
No blanket ambient-coordinate identification or global group
retractability is introduced.
-/

namespace PSTSEPPA
namespace ABO

variable {X Y : Type*}

/-- Equivalence of a relation transports forward across an
actual bijection when the relation is preserved AND reflected.
Importantly this also proves equivalence of the source-side
coset-gluing relation without globally retractable H1. -/
theorem equivalence_of_equiv_iff
    (e : X ≃ Y)
    (rX : X → X → Prop)
    (rY : Y → Y → Prop)
    (hrX : Equivalence rX)
    (hRel : ∀ x x', rX x x' ↔ rY (e x) (e x')) :
    Equivalence rY := by
  constructor
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (hRel x x).mp (hrX.refl x)
  · intro y z hyz
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective z
    exact (hRel x' x).mp
      (hrX.symm ((hRel x x').mpr hyz))
  · intro y z t hyz hzt
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective z
    obtain ⟨x'', rfl⟩ := e.surjective t
    exact (hRel x x'').mp
      (hrX.trans ((hRel x x').mpr hyz) ((hRel x' x'').mpr hzt))

/-- A target-side quotient setoid whose relation is precisely
the requested rY (not a transitive closure, not a coarser
ambient-value equality), certified by transport from the
already established source setoid. -/
def setoidOfEquivRelation
    (e : X ≃ Y)
    (sX : Setoid X)
    (rY : Y → Y → Prop)
    (hRel : ∀ x x', sX.r x x' ↔ rY (e x) (e x')) :
    Setoid Y where
  r := rY
  iseqv := equivalence_of_equiv_iff e sX.r rY sX.iseqv hRel

/-- The induced map of the exact raw gluing quotients is a
genuine equivalence. No injectivity hypothesis of ambient
coordinates, or retractability hypothesis on a target ambient
group, is concealed here. -/
noncomputable def quotientEquivOfEquivRelation
    (e : X ≃ Y)
    (sX : Setoid X)
    (rY : Y → Y → Prop)
    (hRel : ∀ x x', sX.r x x' ↔ rY (e x) (e x')) :
    Quotient sX ≃ Quotient (setoidOfEquivRelation e sX rY hRel) where
  toFun q :=
    Quotient.liftOn q
      (fun x => Quotient.mk _ (e x))
      (by
        intro x x' hxx'
        apply Quotient.sound
        exact (hRel x x').mp hxx')
  invFun q :=
    Quotient.liftOn q
      (fun y => Quotient.mk _ (e.symm y))
      (by
        intro y y' hyy'
        apply Quotient.sound
        apply (hRel (e.symm y) (e.symm y')).mpr
        have hrelY : rY y y' := hyy'
        simpa only [e.apply_symm_apply] using hrelY)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      change Quotient.mk sX (e.symm (e x)) = Quotient.mk sX x
      rw [e.symm_apply_apply]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h y =>
      change Quotient.mk (setoidOfEquivRelation e sX rY hRel)
          (e (e.symm y)) =
        Quotient.mk (setoidOfEquivRelation e sX rY hRel) y
      rw [e.apply_symm_apply]

/-- The quotient equivalence maps each TRUE raw class to the
class of its transported raw point. There is no additional
identification of vertices with coinciding ambient values. -/
@[simp] theorem quotientEquivOfEquivRelation_mk
    (e : X ≃ Y) (sX : Setoid X)
    (rY : Y → Y → Prop)
    (hRel : ∀ x x', sX.r x x' ↔ rY (e x) (e x'))
    (x : X) :
    quotientEquivOfEquivRelation e sX rY hRel
      (Quotient.mk sX x) =
    Quotient.mk (setoidOfEquivRelation e sX rY hRel) (e x) :=
  rfl

/-- The reverse map likewise reflects the exact original
quotient class, not merely some ambient coordinate. -/
@[simp] theorem quotientEquivOfEquivRelation_symm_mk
    (e : X ≃ Y) (sX : Setoid X)
    (rY : Y → Y → Prop)
    (hRel : ∀ x x', sX.r x x' ↔ rY (e x) (e x'))
    (y : Y) :
    (quotientEquivOfEquivRelation e sX rY hRel).symm
      (Quotient.mk (setoidOfEquivRelation e sX rY hRel) y) =
    Quotient.mk sX (e.symm y) :=
  rfl

end ABO
end PSTSEPPA
