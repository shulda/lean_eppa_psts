import PSTSEPPA.PSTS.DevelopmentAction
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Finite.Prod

/-!
# Conditional EPPA from a maximum-transporter extension

This is the hard Gate T2 theorem.  Given a finite PSTS, a selected family of
closed partial automorphisms, and a finite fibre-MAX extension, the quotient
development is a finite PSTS containing a closed induced copy of the original
system, and every selected partial automorphism extends to a total
automorphism.
-/

namespace PSTSEPPA
namespace PSTS

variable {V ι : Type*} {A : PSTS V} {gen : ι → PartialAut A}

/-- Packaged finite witness for a selected family of partial automorphisms. -/
structure SelectedEPPAWitness (A : PSTS V) (gen : ι → PartialAut A) where
  /-- Vertex type of the witness. -/
  W : Type*
  /-- The witness is finite. -/
  [fintypeW : Fintype W]
  /-- PSTS structure on the witness. -/
  B : PSTS W
  /-- Canonical copy of the original vertex set. -/
  embed : V → W
  /-- The canonical copy is injective. -/
  embed_injective : Function.Injective embed
  /-- Its image is closed in the witness. -/
  embed_closed : B.Closed (Set.range embed)
  /-- Exact induced-substructure formula on the base copy. -/
  embed_op_iff : ∀ {a b : V} {z : W},
    B.op (embed a) (embed b) = some z ↔
      ∃ c : V, A.op a b = some c ∧ z = embed c
  /-- Chosen total extensions of the selected partial automorphisms. -/
  extend : ι → PartialAut B
  /-- The extensions are total. -/
  extend_total : ∀ i, PEquivSource (extend i).toPEquiv = (Set.univ : Set W)
  /-- The extension ranges are total as well. -/
  extend_target_total : ∀ i,
    PEquivTarget (extend i).toPEquiv = (Set.univ : Set W)
  /-- Each chosen extension agrees with the original map on the base copy. -/
  extends_gen : ∀ i {a b : V},
    (gen i).toPEquiv a = some b →
      (extend i).toPEquiv (embed a) = some (embed b)

namespace MaxTransporterExtension

variable (X : MaxTransporterExtension A gen)

/-- The quotient development is finite whenever the original vertex type is
finite. -/
noncomputable instance developmentFintype [Fintype V] :
    Fintype X.Development := by
  letI : Finite V := Finite.of_fintype V
  letI : Finite X.H := Finite.of_fintype X.H
  letI : Finite (DevelopmentRaw X) := inferInstance
  letI : Finite X.Development :=
    Quotient.finite X.developmentSetoid
  exact Fintype.ofFinite X.Development

/-- A finite fibre-MAX extension produces a finite EPPA witness for the selected
family of partial automorphisms. -/
noncomputable def selectedEPPAWitness [Fintype V] :
    SelectedEPPAWitness A gen where
  W := X.Development
  fintypeW := X.developmentFintype
  B := X.developmentPSTS
  embed := X.baseMap
  embed_injective := X.baseMap_injective
  embed_closed := X.baseSet_closed
  embed_op_iff := by
    intro a b z
    exact X.developmentPSTS_base_eq_some_iff
  extend i := X.developmentRightAut (X.liftGen i)
  extend_total i := by
    ext q
    simp [PEquivSource, developmentRightAut, Equiv.toPEquiv_apply]
  extend_target_total i := by
    ext q
    simp [PEquivTarget, PEquivSource, developmentRightAut,
      ← Equiv.toPEquiv_symm]
  extends_gen := by
    intro i a b hab
    exact X.developmentRightAut_extends i hab

/-- `selectedEPPAWitness` is the constructive conditional transfer theorem:
given a finite PSTS and a fibre-MAX extension, it returns the finite closed
EPPA witness together with explicit total extensions.  No separate existential
wrapper is needed; the construction is stronger and also keeps the universe of
the quotient witness explicit. -/

end MaxTransporterExtension

end PSTS
end PSTSEPPA
