import Mathlib.Tactic.Group
import PSTSEPPA.ABO.IsolatedCosetGluing
import PSTSEPPA.ABO.LocalSubgroupCosetNaturality

/-!
# Translation of the ACTUAL fresh B-coset points under rooted local normalization

The corrected ABO Definition 5.3 type-(2) augmentation attaches
a FULL B-coset at a singleton root outside the old B-constituent.
Its new vertices have exactly the type of B-coset points OTHER THAN
the basepoint, not just some ambient value equivalence class.

Fix B⊆A, the actual subgroup H=Γ[A] with its trivial-completion
generator map, a local coset basepoint g∈H, and an arbitrary
ambient source-root translation r∈Γ. The entire coset
g H[B] corresponds bijectively to r*g Γ[B] in ambient Γ.
In particular the root g is sent precisely to the root r*g,
so their FRESH point carriers are genuinely equivalent.

This requires NO global retractability of Γ, no injectivity or
independence of generators, and no assumption that Γ is generated
by the selected labels. It is a literal carrier equivalence,
preparing the new signed B-edges in the source/local augmented
EGraph isomorphism; it does not by itself construct that graph.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Root translation produces an actual equivalence between
all NEW attached B-coset points of a local Γ[A] augmentation
and those of the corresponding original ambient Γ augmentation.
The common old root itself is excluded from both carriers. -/
noncomputable def rootedLocalFreshCosetEquiv
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    IsolatedCosetGluing.FreshPoint
        (trivialCompletionGenerator gen A) B g ≃
      IsolatedCosetGluing.FreshPoint gen B (r * (g : Γ)) where
  toFun p := by
    have hpAmbient : (p.1 : Γ) ∈ generatedLeftCoset gen B (g : Γ) :=
      (mem_localGeneratedLeftCoset_iff_ambient gen B A hBA g p.1).mp p.2.1
    have hcoset : r * (p.1 : Γ) ∈
        generatedLeftCoset gen B (r * (g : Γ)) := by
      change (r * (g : Γ))⁻¹ * (r * (p.1 : Γ)) ∈
        generatedSubgroup gen B
      have hmul :
          (r * (g : Γ))⁻¹ * (r * (p.1 : Γ)) =
            (g : Γ)⁻¹ * (p.1 : Γ) := by group
      rw [hmul]
      exact hpAmbient
    have hfresh : r * (p.1 : Γ) ≠ r * (g : Γ) := by
      intro h
      apply p.2.2
      apply Subtype.ext
      exact mul_left_cancel h
    exact ⟨r * (p.1 : Γ), hcoset, hfresh⟩
  invFun q := by
    let yΓ : Γ := r⁻¹ * q.1
    have hyA : yΓ ∈ generatedSubgroup gen A := by
      have hb : (r * (g : Γ))⁻¹ * q.1 ∈
          generatedSubgroup gen B := q.2.1
      have hab : (r * (g : Γ))⁻¹ * q.1 ∈
          generatedSubgroup gen A :=
        (generatedSubgroup_mono gen hBA) hb
      have hyExpr :
          yΓ = (g : Γ) * ((r * (g : Γ))⁻¹ * q.1) := by
        dsimp [yΓ]
        group
      rw [hyExpr]
      exact (generatedSubgroup gen A).mul_mem g.property hab
    let y : generatedSubgroup gen A := ⟨yΓ, hyA⟩
    have hyCoset :
        y ∈ generatedLeftCoset
          (trivialCompletionGenerator gen A) B g := by
      apply (mem_localGeneratedLeftCoset_iff_ambient gen B A hBA g y).mpr
      change (g : Γ)⁻¹ * (y : Γ) ∈ generatedSubgroup gen B
      have heq :
          (g : Γ)⁻¹ * yΓ = (r * (g : Γ))⁻¹ * q.1 := by
        dsimp [yΓ]
        group
      rw [heq]
      exact q.2.1
    have hyFresh : y ≠ g := by
      intro h
      apply q.2.2
      have hyEval : r * (y : Γ) = q.1 := by
        change r * (r⁻¹ * q.1) = q.1
        group
      exact hyEval.symm.trans
        (congrArg (fun x : generatedSubgroup gen A => r * (x : Γ)) h)
    exact ⟨y, hyCoset, hyFresh⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    change r⁻¹ * (r * (p.1 : Γ)) = (p.1 : Γ)
    group
  right_inv := by
    intro q
    apply Subtype.ext
    change r * (r⁻¹ * q.1) = q.1
    group

/-- The new fresh point maps to its exact rooted translate,
keeping the ambient group coordinate ONLY as a diagnostic
projection rather than identifying distinct component tags. -/
@[simp] theorem rootedLocalFreshCosetEquiv_value
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A)
    (p : IsolatedCosetGluing.FreshPoint
        (trivialCompletionGenerator gen A) B g) :
    (rootedLocalFreshCosetEquiv gen A B hBA r g p).1 =
      r * (p.1 : Γ) :=
  rfl

end ABO
end PSTSEPPA
