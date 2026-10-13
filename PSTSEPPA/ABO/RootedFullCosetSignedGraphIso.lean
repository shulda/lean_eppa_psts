import PSTSEPPA.ABO.RootedFullCosetSignedEdgeTransport
import PSTSEPPA.ABO.BijectiveGraphPathReflection

/-!
# Actual signed graph isomorphism of a newly attached full B-coset

The pending source/local type-(2) augmentation comparison requires
the actual NEW B-Coset subgraph on both sides to be isomorphic,
not just bijective on fresh vertices or ambient group coordinates.

We use the two exact coset equivalences and signed B-generator
step identity from RootedFullCosetSignedEdgeTransport. The map
x ↦ r*x takes all local full B-coset vertices and directed signed
B-edge tokens to the ambient Γ, preserving SOURCES, complete
signed labels and FORMAL INVERSION of oriented edge tokens.
Every genuine signed path in the new B-coset is preserved and
REFLECTED (including loops and both orientations).

The glued old+new augmented graph still requires verifying the
common root and separately tagged old multi-CE edge preservation;
this file proves the genuine new-coset graph isomorphism that
will be one summand in that final argument.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- The entire genuinely attached local B-coset Cayley
EGraph is an EXACT labelled-graph isomorphic copy of the
corresponding original source-rooted ambient B-coset.
The root is translated, and every signed directed edge
has the same signed label and correctly translated target. -/
noncomputable def rootedLocalFullCosetSignedGraphHom
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph
        (trivialCompletionGenerator gen A) B g).toEGraph).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph
        gen B (r * (g : Γ))).toEGraph).toLabelledGraph where
  onVertex := rootedLocalFullCosetPointEquiv gen A B hBA r g
  onEdge := rootedLocalFullCosetEdgeEquiv gen A B hBA r g
  map_source := by
    intro e
    rfl
  map_label := by
    intro e
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · change
        r * (((cayleyGraph (trivialCompletionGenerator gen A)).target
            e.1 : generatedSubgroup gen A) : Γ) =
          (cayleyGraph gen).target (r * (e.1.1 : Γ), e.1.2)
      rw [cayleyGraph.target_eq_mul_evalGroupLetter
            (trivialCompletionGenerator gen A) e.1.1 e.1.2,
          cayleyGraph.target_eq_mul_evalGroupLetter
            gen (r * (e.1.1 : Γ)) e.1.2]
      exact rootedLocalFullCoset_signedStep
        gen A B hBA r e.1.1 e.1.2 e.2.2
    · rfl

/-- The new full B-coset graph morphism is bijective on
every actual vertex and every oriented signed edge token.
This is strictly stronger than a fresh-vertex equivalence. -/
theorem rootedLocalFullCosetSignedGraphHom_bijective
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A) :
    Function.Bijective
      (rootedLocalFullCosetSignedGraphHom
        gen A B hBA r g).onVertex ∧
    Function.Bijective
      (rootedLocalFullCosetSignedGraphHom
        gen A B hBA r g).onEdge := by
  exact ⟨(rootedLocalFullCosetPointEquiv
      gen A B hBA r g).bijective,
    (rootedLocalFullCosetEdgeEquiv
      gen A B hBA r g).bijective⟩

/-- The local Γ[A] and original ambient Γ fully attached
B-cosets realise EXACTLY the same signed paths after
translation, even for identity-labelled loops and inverse
letters. This uses the REAL signed graph isomorphism,
not mere equivalence of group word evaluations. -/
theorem rootedLocalFullCosetSignedGraphHom_follows_iff
    (gen : ι → Γ) (A B : Finset ι) (hBA : B ⊆ A)
    (r : Γ) (g : generatedSubgroup gen A)
    (u v : IsolatedCosetGluing.CosetPoint
      (trivialCompletionGenerator gen A) B g)
    (w : LabelWord ι) :
    ((IsolatedCosetGluing.fullCosetSubgraph
      (trivialCompletionGenerator gen A) B g).toEGraph).Follows u w v ↔
    ((IsolatedCosetGluing.fullCosetSubgraph
      gen B (r * (g : Γ))).toEGraph).Follows
        ((rootedLocalFullCosetSignedGraphHom
          gen A B hBA r g).onVertex u)
        w
        ((rootedLocalFullCosetSignedGraphHom
          gen A B hBA r g).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (rootedLocalFullCosetSignedGraphHom gen A B hBA r g)
    (rootedLocalFullCosetSignedGraphHom_bijective
      gen A B hBA r g).1
    (rootedLocalFullCosetSignedGraphHom_bijective
      gen A B hBA r g).2
    u v w

end ABO
end PSTSEPPA
