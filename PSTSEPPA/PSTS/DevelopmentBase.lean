import PSTSEPPA.PSTS.DevelopmentOperation

/-!
# The closed base copy inside the quotient development

This file proves that the canonical map `a ↦ [a,1]` identifies the original
PSTS with a closed induced substructure of the quotient development.
-/

namespace PSTSEPPA
namespace PSTS

variable {V ι : Type*} {A : PSTS V} {gen : ι → PartialAut A}

namespace MaxTransporterExtension

variable (X : MaxTransporterExtension A gen)

/-- Exact description of the quotient operation on two base points.

The difficult direction uses one fibre-maximum word to transport both input
points of an arbitrary common chart, and then transports the output using
closedness and operation preservation of that partial automorphism. -/
theorem developmentPSTS_base_eq_some_iff
    {a b : V} {z : X.Development} :
    X.developmentPSTS.op (X.baseMap a) (X.baseMap b) = some z ↔
      ∃ c : V, A.op a b = some c ∧ z = X.baseMap c := by
  constructor
  · intro hzop
    have hzrel :
        X.DevelopmentOpRel (X.baseMap a) (X.baseMap b) z := by
      exact X.developmentOp_eq_some_iff.mp hzop
    rcases hzrel with
      ⟨a', b', c, g, hxa, hyb, hzc, ha'b'c⟩

    have hxa' :
        X.developmentMk a 1 = X.developmentMk a' g := by
      simpa [baseMap] using hxa
    have hyb' :
        X.developmentMk b 1 = X.developmentMk b' g := by
      simpa [baseMap] using hyb

    rcases X.developmentMk_eq_iff.mp hxa' with
      ⟨u, huH, hua⟩
    rcases X.developmentMk_eq_iff.mp hyb' with
      ⟨v, hvH, hvb⟩

    have huH' :
        SignedWord.evalGroup X.liftGen u = g⁻¹ := by
      simpa using huH
    have hvH' :
        SignedWord.evalGroup X.liftGen v = g⁻¹ := by
      simpa using hvH

    have huLe := X.dominates u huH'
    have hvLe := X.dominates v hvH'

    have huaMem :
        a' ∈ (SignedWord.eval gen u).toPEquiv a := by
      simpa only [Option.mem_def] using hua
    have hvbMem :
        b' ∈ (SignedWord.eval gen v).toPEquiv b := by
      simpa only [Option.mem_def] using hvb

    have hmaMem :=
      huLe a a' huaMem
    have hmbMem :=
      hvLe b b' hvbMem

    have hma :
        (SignedWord.eval gen (X.maxWord g⁻¹)).toPEquiv a =
          some a' := by
      simpa only [Option.mem_def] using hmaMem
    have hmb :
        (SignedWord.eval gen (X.maxWord g⁻¹)).toPEquiv b =
          some b' := by
      simpa only [Option.mem_def] using hmbMem

    have hmc :=
      (SignedWord.eval gen (X.maxWord g⁻¹)).map_op hma hmb
    rw [ha'b'c] at hmc
    rcases Option.bind_eq_some_iff.mp hmc with
      ⟨d, habd, hdc⟩

    have hdcEq :
        X.developmentMk d 1 = X.developmentMk c g := by
      apply X.developmentMk_eq_iff.mpr
      refine ⟨X.maxWord g⁻¹, ?_, hdc⟩
      simpa using X.maxWord_value g⁻¹

    refine ⟨d, habd, ?_⟩
    have hbase :
        X.baseMap d = X.developmentMk c g := by
      simpa [baseMap] using hdcEq
    exact hzc.trans hbase.symm

  · rintro ⟨c, habc, rfl⟩
    apply X.developmentOp_eq_some_iff.mpr
    exact ⟨a, b, c, 1, rfl, rfl, rfl, habc⟩

/-- The base map preserves and reflects defined operation values. -/
theorem developmentPSTS_base_eq_some_iff_base
    {a b c : V} :
    X.developmentPSTS.op (X.baseMap a) (X.baseMap b) =
        some (X.baseMap c) ↔
      A.op a b = some c := by
  constructor
  · intro h
    rcases X.developmentPSTS_base_eq_some_iff.mp h with
      ⟨d, habd, hcd⟩
    have hdc : d = c := by
      apply X.baseMap_injective
      exact hcd.symm
    simpa [hdc] using habd
  · intro habc
    exact X.developmentPSTS_base_eq_some_iff.mpr
      ⟨c, habc, rfl⟩

/-- Image of the canonical base copy. -/
def baseSet : Set X.Development :=
  Set.range X.baseMap

/-- The canonical copy of `A` is closed in the quotient PSTS. -/
theorem baseSet_closed :
    X.developmentPSTS.Closed X.baseSet := by
  intro x y z hx hy hxyz
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  rcases X.developmentPSTS_base_eq_some_iff.mp hxyz with
    ⟨c, hc, hzc⟩
  exact ⟨c, hzc.symm⟩

/-- The base map is an operation embedding into the quotient PSTS. -/
theorem baseMap_map_op
    {a b c : V} (h : A.op a b = some c) :
    X.developmentPSTS.op (X.baseMap a) (X.baseMap b) =
      some (X.baseMap c) :=
  X.developmentPSTS_base_eq_some_iff_base.mpr h

/-- Undefinedness is also reflected by the base map. -/
theorem baseMap_op_eq_none_iff
    {a b : V} :
    X.developmentPSTS.op (X.baseMap a) (X.baseMap b) = none ↔
      A.op a b = none := by
  constructor
  · intro hdev
    cases hA : A.op a b with
    | none =>
        exact hA
    | some c =>
        have hsome := X.baseMap_map_op hA
        rw [hdev] at hsome
        cases hsome
  · intro hA
    cases hdev : X.developmentPSTS.op (X.baseMap a) (X.baseMap b) with
    | none =>
        exact hdev
    | some z =>
        rcases X.developmentPSTS_base_eq_some_iff.mp hdev with
          ⟨c, hac, hzc⟩
        rw [hA] at hac
        cases hac

end MaxTransporterExtension

end PSTS
end PSTSEPPA
