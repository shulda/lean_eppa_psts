import PSTSEPPA.ABO.BijectiveGraphPathReflection
import PSTSEPPA.ABO.ComponentIndexMonotonicity

/-!
# Intrinsic path-component tags transported by genuine signed graph isomorphisms

The actual ABO coset extensions do not attach one undifferentiated
ambient B-coset: they attach a DIFFERENT copy for each intrinsic
signed B-reachability component of the incomplete old skeleton.
Therefore translating a source H1-cover component into its honest
local H1[A] skeleton must preserve the entire quotient set of
component tags, not merely the original vertex or edge sets.

For ANY bijective labelled graph morphism between arbitrary
incomplete Cayley skeletons (their ambient groups may differ),
we construct, for every subalphabet B, a genuine equivalence
between the corresponding QUOTIENT component-index types.
It is induced by the actual vertex map, with inverse induced
by the genuine inverse graph morphism. The equivalence preserves
the component tag of each vertex and COMMUTES with enlargement
B⊆C of subalphabets.

This is the exact component-index part of the future functorial
comparison of source/normalized multi-coset quotient stages:
gluing by intersections B∩C must respect these tags as well as
the separate ambient-coset point coordinates.

No global ambient Cayley injection, retractability, completion,
or higher-rank historical action is asserted here.
-/

namespace PSTSEPPA
namespace ABO

namespace CayleySubgraphSpec

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A D : Finset ι}
variable (L : CayleySubgraphSpec genΓ A)
variable (K : CayleySubgraphSpec genΔ D)
variable (f : LabelledGraphHom
  (L.toEGraph).toLabelledGraph
  (K.toEGraph).toLabelledGraph)
variable (hv : Function.Bijective f.onVertex)
variable (he : Function.Bijective f.onEdge)

/-- Every ACTUAL signed B-path is preserved AND reflected
under a labelled graph isomorphism, even if both graphs
are incomplete and their ambient groups have different types. -/
theorem subalphabetReachable_iff_graphIso
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (B : Finset ι) (x y : L.Vertex) :
    L.SubalphabetReachable B x y ↔
      K.SubalphabetReachable B (f.onVertex x) (f.onVertex y) := by
  constructor
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw, hp.map f⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw, EGraph.follows_reflect_of_bijective f hv he hp⟩

/-- The genuine quotient of signed B-components is transported
bijectively. Distinct intrinsic component tags remain distinct,
even when their ambient B-coset values happen to coincide. -/
noncomputable def componentIndexEquiv_of_graphIso
    (B : Finset ι) :
    L.ComponentIndex B ≃ K.ComponentIndex B where
  toFun c :=
    Quotient.liftOn c
      (fun x => K.componentClass B (f.onVertex x))
      (by
        intro x y hxy
        apply Quotient.sound
        exact (L.subalphabetReachable_iff_graphIso K f hv he B x y).mp hxy)
  invFun d :=
    Quotient.liftOn d
      (fun y =>
        L.componentClass B
          ((f.inverseOfBijective hv he).onVertex y))
      (by
        intro x y hxy
        apply Quotient.sound
        obtain ⟨w,hw,hp⟩ := hxy
        exact ⟨w,hw,hp.map (f.inverseOfBijective hv he)⟩)
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
      change
        L.componentClass B
          ((f.inverseOfBijective hv he).onVertex (f.onVertex x)) =
        L.componentClass B x
      rw [f.inverseOfBijective_onVertex_apply]
  right_inv := by
    intro d
    induction d using Quotient.inductionOn with
    | h y =>
      change
        K.componentClass B
          (f.onVertex ((f.inverseOfBijective hv he).onVertex y)) =
        K.componentClass B y
      have hright :
          f.onVertex ((f.inverseOfBijective hv he).onVertex y) = y :=
        (f.vertexEquivOfBijective hv).apply_symm_apply y
      rw [hright]

/-- The image of an actual source component tag is literally
the component tag of the transported original vertex. -/
@[simp] theorem componentIndexEquiv_of_graphIso_class
    (B : Finset ι) (x : L.Vertex) :
    (L.componentIndexEquiv_of_graphIso K f hv he B)
      (L.componentClass B x) =
    K.componentClass B (f.onVertex x) :=
  rfl

/-- The intrinsic component equivalences commute with
B⊆C alphabet enlargement, including equal and empty
alphabets. This is essential for intersection-support
gluing between attached B- and C-coset copies. -/
theorem componentIndexEquiv_of_graphIso_natural
    (B C : Finset ι) (hBC : B ⊆ C)
    (c : L.ComponentIndex B) :
    K.componentIndexMap B C hBC
      ((L.componentIndexEquiv_of_graphIso K f hv he B) c) =
    (L.componentIndexEquiv_of_graphIso K f hv he C)
      (L.componentIndexMap B C hBC c) := by
  induction c using Quotient.inductionOn with
  | h x =>
    rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
