import PSTSEPPA.ABO.RootedFullCosetSignedEdgeTransport
import PSTSEPPA.ABO.RootedFreshCosetEquiv

/-!
# Exact gluing-root naturality for original-source B-augmentations

The corrected ABO type-(2) extension is not simply an abstract
disjoint union: the basepoint of each newly attached full B-coset
is identified with exactly ONE old multi-coset quotient vertex.
All other coset points remain freshly tagged.

An isomorphism of old vertices and an equivalence of fresh
B-coset points must therefore be compatible with the actual
`IsolatedCosetGluing.gluePoint` map of the ENTIRE full coset,
including its old root. We prove this compatibility for the
literal rooted translation of Γ[A] to ambient Γ.

This is the vertex-summand gluing bridge needed to combine the
old multi-coset EGraph isomorphism (#390) and the new full B-coset
signed graph equivalence (#399/#400) into an actual isomorphism
of the entire type-(2) augmented original-source EGraph.
No ambient group coordinate is used to identify different
old tagged quotient vertices.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V W : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- The underlying group-coordinate value of the translated FULL
B-coset point is literally the rooted translation r*x. -/
@[simp] theorem rootedLocalFullCosetPointEquiv_value
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A)
    (p : IsolatedCosetGluing.CosetPoint
      (trivialCompletionGenerator gen A) B g) :
    (rootedLocalFullCosetPointEquiv gen A B hBA r g p).1 =
      r * (p.1 : Γ) :=
  rfl

/-- The exact new+old augmentation VERTEX carrier equivalence,
given any old vertex equivalence. Old tagged vertices are
transferred only by that equivalence; fresh B-points only
by their honest root-translation equivalence. -/
noncomputable def rootedLocalAugmentedVertexEquiv
    (f : V ≃ W)
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    IsolatedCosetGluing.Vertex V
        (trivialCompletionGenerator gen A) B g ≃
    IsolatedCosetGluing.Vertex W gen B (r * (g : Γ)) :=
  Equiv.sumCongr f (rootedLocalFreshCosetEquiv gen A B hBA r g)

/-- Root translation sends the actual local B-coset basepoint
precisely to the ambient basepoint, with no fresh copy created. -/
theorem rootedLocalFullCosetPointEquiv_root
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A)
    (p : IsolatedCosetGluing.CosetPoint
      (trivialCompletionGenerator gen A) B g)
    (hp : p.1 = g) :
    (rootedLocalFullCosetPointEquiv gen A B hBA r g p).1 =
      r * (g : Γ) := by
  rw [rootedLocalFullCosetPointEquiv_value, hp]

/-- The *actual glued point* of every local full B-coset
point transports exactly to its source-rooted glued point,
INCLUDING the basepoint identified with the OLD root.

For a non-root point both sides use separately tagged fresh
points, and for the basepoint both sides use the old root via f.
No distinct old tagged vertices are identified by Γ-values. -/
theorem rootedLocal_gluePoint_natural
    (f : V ≃ W)
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A)
    (oldRoot : V)
    (p : IsolatedCosetGluing.CosetPoint
      (trivialCompletionGenerator gen A) B g) :
    rootedLocalAugmentedVertexEquiv f gen A B hBA r g
      (IsolatedCosetGluing.gluePoint
        (trivialCompletionGenerator gen A) B g oldRoot p) =
    IsolatedCosetGluing.gluePoint gen B (r * (g : Γ))
      (f oldRoot)
      (rootedLocalFullCosetPointEquiv gen A B hBA r g p) := by
  classical
  by_cases hp : p.1 = g
  · have htarget :
        (rootedLocalFullCosetPointEquiv gen A B hBA r g p).1 =
          r * (g : Γ) :=
      rootedLocalFullCosetPointEquiv_root gen A B hBA r g p hp
    simp [IsolatedCosetGluing.gluePoint, hp, htarget,
      rootedLocalAugmentedVertexEquiv]
  · have htarget :
        (rootedLocalFullCosetPointEquiv gen A B hBA r g p).1 ≠
          r * (g : Γ) := by
      rw [rootedLocalFullCosetPointEquiv_value]
      intro h
      apply hp
      apply Subtype.ext
      exact mul_left_cancel h
    simp only [IsolatedCosetGluing.gluePoint,
      dif_neg hp, dif_neg htarget]
    change Sum.inr (rootedLocalFreshCosetEquiv gen A B hBA r g
      ⟨p.1, p.2, hp⟩) =
      Sum.inr
        (⟨(rootedLocalFullCosetPointEquiv
          gen A B hBA r g p).1,
          (rootedLocalFullCosetPointEquiv
            gen A B hBA r g p).2, htarget⟩ :
          IsolatedCosetGluing.FreshPoint gen B (r * (g : Γ)))
    apply congrArg Sum.inr
    apply Subtype.ext
    exact (rootedLocalFreshCosetEquiv_value
      gen A B hBA r g ⟨p.1, p.2, hp⟩).trans
      (rootedLocalFullCosetPointEquiv_value gen A B hBA r g p).symm

end ABO
end PSTSEPPA
