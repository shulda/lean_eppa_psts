import PSTSEPPA.PSTS.Development

/-!
# The PSTS operation on the quotient development

A triple of quotient points is a chart triple when it has representatives
`(a,g)`, `(b,g)`, `(c,g)` at one common group coordinate and
`A.op a b = some c`.

The fibre-MAX property is used exactly where it should be: to prove that two
overlapping charts assign the same third quotient point.
-/

namespace PSTSEPPA
namespace PSTS

variable {V ι : Type*} {A : PSTS V} {gen : ι → PartialAut A}

namespace MaxTransporterExtension

variable (X : MaxTransporterExtension A gen)

/-- The chart relation defining the partial operation on the development. -/
def DevelopmentOpRel
    (x y z : X.Development) : Prop :=
  ∃ a b c : V, ∃ g : X.H,
    x = X.developmentMk a g ∧
    y = X.developmentMk b g ∧
    z = X.developmentMk c g ∧
    A.op a b = some c

/-- The chart relation is functional in its output.

If two charts represent the same two input quotient points, the corresponding
transport words have the same group value.  The chosen MAX word in that fibre
extends both transports.  Since its source is closed and it preserves the PSTS
operation, it also transports the third point. -/
theorem developmentOpRel_functional
    {x y z₁ z₂ : X.Development}
    (h₁ : X.DevelopmentOpRel x y z₁)
    (h₂ : X.DevelopmentOpRel x y z₂) :
    z₁ = z₂ := by
  rcases h₁ with ⟨a, b, c, g, hx, hy, hz, habc⟩
  rcases h₂ with ⟨a', b', c', h, hx', hy', hz', ha'b'c'⟩
  have hxa :
      X.developmentMk a g = X.developmentMk a' h :=
    hx.symm.trans hx'
  have hyb :
      X.developmentMk b g = X.developmentMk b' h :=
    hy.symm.trans hy'
  rcases X.developmentMk_eq_iff.mp hxa with ⟨u, huH, hua⟩
  rcases X.developmentMk_eq_iff.mp hyb with ⟨v, hvH, hvb⟩

  have huLe := X.dominates u huH
  have hvLe := X.dominates v hvH

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
      (SignedWord.eval gen (X.maxWord (g * h⁻¹))).toPEquiv a =
        some a' := by
    simpa only [Option.mem_def] using hmaMem
  have hmb :
      (SignedWord.eval gen (X.maxWord (g * h⁻¹))).toPEquiv b =
        some b' := by
    simpa only [Option.mem_def] using hmbMem

  have hmc :=
    (SignedWord.eval gen (X.maxWord (g * h⁻¹))).map_op hma hmb
  rw [habc, ha'b'c'] at hmc
  simp only [Option.bind_some] at hmc

  have hcc' :
      X.developmentMk c g = X.developmentMk c' h := by
    apply X.developmentMk_eq_iff.mpr
    exact ⟨X.maxWord (g * h⁻¹), X.maxWord_value _, hmc⟩

  exact hz.trans (hcc'.trans hz'.symm)

/-- Swapping the two inputs preserves the chart relation. -/
theorem developmentOpRel_comm
    {x y z : X.Development} :
    X.DevelopmentOpRel x y z ↔ X.DevelopmentOpRel y x z := by
  constructor
  · rintro ⟨a, b, c, g, hx, hy, hz, habc⟩
    refine ⟨b, a, c, g, hy, hx, hz, ?_⟩
    exact (A.symm b a).trans habc
  · rintro ⟨a, b, c, g, hy, hx, hz, habc⟩
    refine ⟨b, a, c, g, hx, hy, hz, ?_⟩
    exact (A.symm b a).trans habc

/-- The option-valued operation selected from the functional chart relation. -/
noncomputable def developmentOp
    (x y : X.Development) : Option X.Development := by
  classical
  exact if h : ∃ z, X.DevelopmentOpRel x y z
    then some (Classical.choose h)
    else none

/-- The selected operation is defined exactly by the chart relation. -/
theorem developmentOp_eq_some_iff
    {x y z : X.Development} :
    X.developmentOp x y = some z ↔ X.DevelopmentOpRel x y z := by
  classical
  unfold developmentOp
  split
  next h =>
    constructor
    · intro heq
      have hz : Classical.choose h = z :=
        Option.some.inj heq
      rw [← hz]
      exact Classical.choose_spec h
    · intro hz
      have heq :=
        X.developmentOpRel_functional (Classical.choose_spec h) hz
      exact congrArg some heq
  next h =>
    constructor
    · intro heq
      cases heq
    · intro hz
      exact (h ⟨z, hz⟩).elim

/-- The quotient development carries a PSTS structure. -/
noncomputable def developmentPSTS : PSTS X.Development where
  op := X.developmentOp
  diag := by
    intro x
    apply X.developmentOp_eq_some_iff.mpr
    refine Quotient.inductionOn x ?_
    intro p
    rcases p with ⟨a, g⟩
    exact ⟨a, a, a, g, rfl, rfl, rfl, A.diag a⟩
  symm := by
    intro x y
    apply Option.ext
    intro z
    rw [X.developmentOp_eq_some_iff, X.developmentOp_eq_some_iff]
    exact X.developmentOpRel_comm
  steiner_left := by
    intro x y z hxyz
    apply X.developmentOp_eq_some_iff.mpr
    rcases X.developmentOp_eq_some_iff.mp hxyz with
      ⟨a, b, c, g, hx, hy, hz, habc⟩
    exact ⟨a, c, b, g, hx, hz, hy, A.steiner_left habc⟩

end MaxTransporterExtension

end PSTS
end PSTSEPPA
