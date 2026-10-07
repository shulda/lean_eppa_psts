import PSTSEPPA.PSTS.Closed
import Mathlib.Data.PEquiv

/-!
# Partial automorphisms of a PSTS

We use mathlib's option-valued `PEquiv`. This is deliberately concrete: its
composition and restriction order are exactly the calculus needed later for
word evaluation and the fibre-MAX statement.
-/

namespace PSTSEPPA
namespace PSTS

variable {V W : Type*}

/-- Domain of an option-valued partial equivalence. -/
def PEquivSource (p : V ≃. W) : Set V :=
  {x | ∃ y, p x = some y}

/-- Range of an option-valued partial equivalence. -/
def PEquivTarget (p : V ≃. W) : Set W :=
  PEquivSource p.symm

/-- Preimage of a set under a partial equivalence, requiring the map to be
actually defined at the source point. -/
def PEquivPreimage (p : V ≃. W) (T : Set W) : Set V :=
  {x | ∃ y, p x = some y ∧ y ∈ T}

@[simp]
theorem mem_pEquivSource_iff (p : V ≃. W) (x : V) :
    x ∈ PEquivSource p ↔ ∃ y, p x = some y :=
  Iff.rfl

@[simp]
theorem mem_pEquivTarget_iff (p : V ≃. W) (y : W) :
    y ∈ PEquivTarget p ↔ ∃ x, p.symm y = some x :=
  Iff.rfl

@[simp]
theorem mem_pEquivPreimage_iff (p : V ≃. W) (T : Set W) (x : V) :
    x ∈ PEquivPreimage p T ↔ ∃ y, p x = some y ∧ y ∈ T :=
  Iff.rfl

@[simp]
theorem pEquivSource_symm (p : V ≃. W) :
    PEquivSource p.symm = PEquivTarget p :=
  rfl

@[simp]
theorem pEquivTarget_symm (p : V ≃. W) :
    PEquivTarget p.symm = PEquivSource p := by
  simp [PEquivTarget]

@[simp]
theorem pEquivSource_single [DecidableEq V] [DecidableEq W] (a : V) (b : W) :
    PEquivSource (PEquiv.single a b) = ({a} : Set V) := by
  ext x
  simp [PEquivSource, PEquiv.single]

@[simp]
theorem pEquivTarget_single [DecidableEq V] [DecidableEq W] (a : V) (b : W) :
    PEquivTarget (PEquiv.single a b) = ({b} : Set W) := by
  simp [PEquivTarget]

/-- Source of a composite partial equivalence. -/
theorem pEquivSource_trans (p : V ≃. W) {U : Type*} (q : W ≃. U) :
    PEquivSource (p.trans q) = PEquivPreimage p (PEquivSource q) := by
  ext x
  simp only [mem_pEquivSource_iff, mem_pEquivPreimage_iff, PEquiv.trans_eq_some]
  constructor
  · rintro ⟨z, y, hxy, hyz⟩
    exact ⟨y, hxy, z, hyz⟩
  · rintro ⟨y, hxy, z, hyz⟩
    exact ⟨z, y, hxy, hyz⟩

/-- A partial automorphism is a partial equivalence between closed induced
substructures, preserving and reflecting the partial operation.

The `map_op` equation is intentionally stated with `Option.bind`: if the
ambient operation is undefined on `(x,y)`, then it is undefined on the image
pair as well; if it is defined, closedness forces the value to remain in the
source and hence be transported by the partial equivalence. -/
structure PartialAut (A : PSTS V) where
  toPEquiv : V ≃. V
  source_closed : A.Closed (PEquivSource toPEquiv)
  target_closed : A.Closed (PEquivTarget toPEquiv)
  map_op : ∀ {x y x' y'},
    toPEquiv x = some x' →
    toPEquiv y = some y' →
    (A.op x y).bind toPEquiv = A.op x' y'

namespace PartialAut

variable {A : PSTS V}

/-- The source subset of a partial automorphism. -/
def source (p : PartialAut A) : Set V :=
  PEquivSource p.toPEquiv

/-- The target subset of a partial automorphism. -/
def target (p : PartialAut A) : Set V :=
  PEquivTarget p.toPEquiv

/-- The inverse map also satisfies the operation-isomorphism equation. -/
theorem map_op_symm (p : PartialAut A) {x y x' y' : V}
    (hx : p.toPEquiv.symm x = some x')
    (hy : p.toPEquiv.symm y = some y') :
    (A.op x y).bind p.toPEquiv.symm = A.op x' y' := by
  have hx' : p.toPEquiv x' = some x := (p.toPEquiv.eq_some_iff).1 hx
  have hy' : p.toPEquiv y' = some y := (p.toPEquiv.eq_some_iff).1 hy
  have hmap := p.map_op hx' hy'
  rw [← hmap]
  cases hop : A.op x' y' with
  | none => simp
  | some z =>
      have hzsource : z ∈ PEquivSource p.toPEquiv :=
        p.source_closed ⟨x, hx'⟩ ⟨y, hy'⟩ hop
      rcases hzsource with ⟨z', hz'⟩
      have hzinv : p.toPEquiv.symm z' = some z :=
        (p.toPEquiv.eq_some_iff).2 hz'
      simp [hz', hzinv]

/-- Inverse partial automorphism. -/
def symm (p : PartialAut A) : PartialAut A where
  toPEquiv := p.toPEquiv.symm
  source_closed := p.target_closed
  target_closed := by
    simpa [PEquivTarget] using p.source_closed
  map_op := p.map_op_symm

/-- Identity partial automorphism. -/
def refl (A : PSTS V) : PartialAut A where
  toPEquiv := PEquiv.refl V
  source_closed := by
    intro x y z hx hy hxy
    exact ⟨z, PEquiv.refl_apply z⟩
  target_closed := by
    intro x y z hx hy hxy
    exact ⟨z, PEquiv.refl_apply z⟩
  map_op := by
    intro x y x' y' hx hy
    simp only [PEquiv.refl_apply, Option.some.injEq] at hx hy
    subst x'
    subst y'
    cases A.op x y <;> simp

/-- The partial automorphism between two singleton closed substructures. -/
def single [DecidableEq V] (A : PSTS V) (a b : V) : PartialAut A where
  toPEquiv := PEquiv.single a b
  source_closed := by
    rw [pEquivSource_single]
    exact A.closed_singleton a
  target_closed := by
    rw [pEquivTarget_single]
    exact A.closed_singleton b
  map_op := by
    intro x y x' y' hx hy
    have hxmem : x' ∈ PEquiv.single a b x := by
      simpa only [Option.mem_def] using hx
    have hymem : y' ∈ PEquiv.single a b y := by
      simpa only [Option.mem_def] using hy
    rcases (PEquiv.mem_single_iff x a x' b).1 hxmem with ⟨hxa, hxb⟩
    rcases (PEquiv.mem_single_iff y a y' b).1 hymem with ⟨hya, hyb⟩
    subst x
    subst x'
    subst y
    subst y'
    rw [A.diag a, A.diag b]
    simp

/-- A closed set pulls back to a closed set under a partial automorphism. -/
theorem closed_preimage (p : PartialAut A) {T : Set V} (hT : A.Closed T) :
    A.Closed (PEquivPreimage p.toPEquiv T) := by
  intro x y z hx hy hxy
  rcases hx with ⟨x', hxmap, hxT⟩
  rcases hy with ⟨y', hymap, hyT⟩
  have hzsource : z ∈ PEquivSource p.toPEquiv :=
    p.source_closed ⟨x', hxmap⟩ ⟨y', hymap⟩ hxy
  rcases hzsource with ⟨z', hzmap⟩
  have hmap := p.map_op hxmap hymap
  rw [hxy] at hmap
  simp only [Option.bind_some] at hmap
  have htarget : A.op x' y' = some z' := hmap.symm.trans hzmap
  exact ⟨z', hzmap, hT hxT hyT htarget⟩

/-- Composition of partial automorphisms, in the same order as `PEquiv.trans`:
first `p`, then `q`. -/
def trans (p q : PartialAut A) : PartialAut A where
  toPEquiv := p.toPEquiv.trans q.toPEquiv
  source_closed := by
    rw [pEquivSource_trans]
    exact p.closed_preimage q.source_closed
  target_closed := by
    rw [PEquivTarget, PEquiv.symm_trans_rev, pEquivSource_trans]
    exact q.symm.closed_preimage p.target_closed
  map_op := by
    intro x y x'' y'' hx hy
    rw [PEquiv.trans_eq_some] at hx hy
    rcases hx with ⟨x', hx₁, hx₂⟩
    rcases hy with ⟨y', hy₁, hy₂⟩
    change (A.op x y).bind (fun z => (p.toPEquiv z).bind q.toPEquiv) = A.op x'' y''
    rw [← Option.bind_assoc, p.map_op hx₁ hy₁, q.map_op hx₂ hy₂]

end PartialAut

end PSTS
end PSTSEPPA
