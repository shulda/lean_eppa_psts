import Mathlib.Tactic.Group
import PSTSEPPA.ABO.RootedFreshCosetEquiv
import PSTSEPPA.ABO.IsolatedCosetGluing
import PSTSEPPA.ABO.RootedCompletedCosetStepNaturality

/-!
# Exact rooted local / source transport of full-B coset signed edges

To compare genuine corrected ABO Definition-5.3 type-(2) B-augmentations,
the already certified fresh-point bijection is NOT enough. We must also
transport the FULL B-coset including its glued basepoint, and all actual
oriented signed B-edge TOKENS. Merely comparing coordinates in ambient
Γ is not a graph isomorphism.

For any B⊆A, let H=Γ[A] with the trivially completed local generators,
g∈H a genuine coset anchor, and r∈Γ a root translation. We construct
literal equivalences:
  g H[B] ≃ r*g Γ[B]
and on the corresponding sets of every signed B-Cayley edge token,
including formal inverses and geometric loops.

The maps are exactly x ↦ r*x on the group-coordinate source and
IDENTITY on the entire signed label. The key transport identity
for a signed letter in B shows compatibility of the true targets:
  r*(x*evalLetter(local,s)) = (r*x)*evalLetter(ambient,s).

No global Γ retractability, independent generators, transitive
closure of coset tags or identification of separately tagged old
multi-CE vertices is used. This supplies the missing new-edge
bijection needed for the full augmented EGraph isomorphism.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- The actual full coset point map, including its common root:
LEFT-translate the Γ[A]-point to its ambient Γ coordinate.
The cosine membership is translated using B⊆A exactly. -/
noncomputable def rootedLocalFullCosetPointMap
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    IsolatedCosetGluing.CosetPoint
      (trivialCompletionGenerator gen A) B g →
    IsolatedCosetGluing.CosetPoint gen B (r * (g : Γ)) := by
  intro p
  have hpAmbient : (p.1 : Γ) ∈ generatedLeftCoset gen B (g : Γ) :=
    (mem_localGeneratedLeftCoset_iff_ambient
      gen B A hBA g p.1).mp p.2
  have hcoset :
      r * (p.1 : Γ) ∈
        generatedLeftCoset gen B (r * (g : Γ)) := by
    change (r * (g : Γ))⁻¹ * (r * (p.1 : Γ)) ∈
      generatedSubgroup gen B
    have hsame :
        (r * (g : Γ))⁻¹ * (r * (p.1 : Γ)) =
          (g : Γ)⁻¹ * (p.1 : Γ) := by group
    rw [hsame]
    exact hpAmbient
  exact ⟨r * (p.1 : Γ), hcoset⟩

theorem rootedLocalFullCosetPointMap_injective
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    Function.Injective (rootedLocalFullCosetPointMap
      gen A B hBA r g) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel
    (congrArg (fun x : IsolatedCosetGluing.CosetPoint
      gen B (r * (g : Γ)) => x.1) hpq)

theorem rootedLocalFullCosetPointMap_surjective
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    Function.Surjective (rootedLocalFullCosetPointMap
      gen A B hBA r g) := by
  intro q
  let yΓ : Γ := r⁻¹ * q.1
  have hyA : yΓ ∈ generatedSubgroup gen A := by
    have hb : (r * (g : Γ))⁻¹ * q.1 ∈
        generatedSubgroup gen B := q.2
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
    apply (mem_localGeneratedLeftCoset_iff_ambient
      gen B A hBA g y).mpr
    change (g : Γ)⁻¹ * (y : Γ) ∈ generatedSubgroup gen B
    have heq :
        (g : Γ)⁻¹ * yΓ = (r * (g : Γ))⁻¹ * q.1 := by
      dsimp [yΓ]
      group
    rw [heq]
    exact q.2
  refine ⟨⟨y, hyCoset⟩, ?_⟩
  apply Subtype.ext
  change r * (r⁻¹ * q.1) = q.1
  group

/-- The full attached B-coset, INCLUDING its identified basepoint,
is bijective under the honest source-root translation. -/
noncomputable def rootedLocalFullCosetPointEquiv
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    IsolatedCosetGluing.CosetPoint
      (trivialCompletionGenerator gen A) B g ≃
    IsolatedCosetGluing.CosetPoint gen B (r * (g : Γ)) :=
  Equiv.ofBijective (rootedLocalFullCosetPointMap
    gen A B hBA r g)
    ⟨rootedLocalFullCosetPointMap_injective
      gen A B hBA r g,
      rootedLocalFullCosetPointMap_surjective
        gen A B hBA r g⟩

/-- For ANY signed B-letter (both orientations), translating
the actual local Γ[A]-right multiplication agrees exactly
with the ambient signed generator step. This is a true
GROUP EQUALITY, not a path claim without edges. -/
theorem rootedLocalFullCoset_signedStep
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (x : generatedSubgroup gen A)
    (s : SignedLabel ι) (hs : signedBase s ∈ B) :
    r * ((x * PSTS.SignedWord.evalGroupLetter
          (trivialCompletionGenerator gen A) s :
          generatedSubgroup gen A) : Γ) =
      (r * (x : Γ)) * PSTS.SignedWord.evalGroupLetter gen s := by
  cases s with
  | pos i =>
      have hi : i ∈ A := hBA hs
      change r * (((x * trivialCompletionGenerator gen A i :
        generatedSubgroup gen A) : Γ)) =
        (r * (x : Γ)) * gen i
      rw [Subgroup.coe_mul, trivialCompletionGenerator_mem gen A hi]
      simp only [mul_assoc]
  | neg i =>
      have hi : i ∈ A := hBA hs
      change r * (((x * (trivialCompletionGenerator gen A i)⁻¹ :
        generatedSubgroup gen A) : Γ)) =
        (r * (x : Γ)) * (gen i)⁻¹
      rw [Subgroup.coe_mul, Subgroup.coe_inv,
        trivialCompletionGenerator_mem gen A hi]
      simp only [mul_assoc]

/-- Map an ACTUAL old-orientation signed local B-coset edge,
preserving its full signed label and translating its source
coordinate. This is a map of REAL edge subtypes, not a map of
ambient group values alone. -/
noncomputable def rootedLocalFullCosetEdgeMap
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    IsolatedCosetGluing.CosetEdge
        (trivialCompletionGenerator gen A) B g →
    IsolatedCosetGluing.CosetEdge gen B (r * (g : Γ)) := by
  intro e
  have hp :
      (⟨e.1.1, e.2.1⟩ :
        IsolatedCosetGluing.CosetPoint
          (trivialCompletionGenerator gen A) B g) =
      ⟨e.1.1, e.2.1⟩ := rfl
  have hx :
      r * (e.1.1 : Γ) ∈
        generatedLeftCoset gen B (r * (g : Γ)) :=
    (rootedLocalFullCosetPointMap
      gen A B hBA r g ⟨e.1.1, e.2.1⟩).2
  exact ⟨(r * (e.1.1 : Γ), e.1.2), ⟨hx, e.2.2⟩⟩

theorem rootedLocalFullCosetEdgeMap_injective
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    Function.Injective (rootedLocalFullCosetEdgeMap
      gen A B hBA r g) := by
  intro e f hef
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact mul_left_cancel
      (congrArg
        (fun x : IsolatedCosetGluing.CosetEdge
          gen B (r * (g : Γ)) => x.1.1) hef)
  · exact congrArg
      (fun x : IsolatedCosetGluing.CosetEdge
        gen B (r * (g : Γ)) => x.1.2) hef

theorem rootedLocalFullCosetEdgeMap_surjective
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    Function.Surjective (rootedLocalFullCosetEdgeMap
      gen A B hBA r g) := by
  intro e
  let q : IsolatedCosetGluing.CosetPoint gen B (r * (g : Γ)) :=
    ⟨e.1.1, e.2.1⟩
  obtain ⟨p, hp⟩ :=
    rootedLocalFullCosetPointMap_surjective gen A B hBA r g q
  refine ⟨⟨(p.1, e.1.2), ⟨p.2, e.2.2⟩⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change r * (p.1 : Γ) = e.1.1
    exact congrArg Subtype.val hp
  · rfl

/-- An equivalence on ALL true oriented signed full B-coset
edge tokens, including their formal negative counterparts
and loops. There is no edge quotienting by ambient Γ-values. -/
noncomputable def rootedLocalFullCosetEdgeEquiv
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    IsolatedCosetGluing.CosetEdge
      (trivialCompletionGenerator gen A) B g ≃
    IsolatedCosetGluing.CosetEdge gen B (r * (g : Γ)) :=
  Equiv.ofBijective (rootedLocalFullCosetEdgeMap
    gen A B hBA r g)
    ⟨rootedLocalFullCosetEdgeMap_injective gen A B hBA r g,
      rootedLocalFullCosetEdgeMap_surjective gen A B hBA r g⟩

end ABO
end PSTSEPPA
