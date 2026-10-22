import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso
import PSTSEPPA.ABO.IsolatedCosetGluing

/-!
# Exact old+fresh carrier for an ENTIRE nonisolated original B-component augmentation

The published corrected ABO upward Theorem 4.7(iii) replaces ONE
true original old B-component of the component-tagged signed
coset-extension H by an entire full H[B] coset. Unlike the
rank-one isolated-root augmentation, this old B-component can
contain multiple original vertices and actual old signed B-edges.

It is WRONG to quotient ALL original H vertices by equality
of their ambient H-group coordinate: two different original
component tags may have equal coordinates, yet remain DISTINCT.

Given an explicit INJECTIVE coordinate map from vertices
of the ONE CHOSEN TRUE ORIGINAL B-component into its
specified actual full H[B] coset, we construct the honest
replacement carrier as the disjoint union

  {old v // v NOT in this actual B-component} ⊕ full H[B] coset.

The canonical old-vertex map sends an old v INSIDE the
chosen B-component into its exact certified coset point;
old v OUTSIDE the component remains literally left-tagged.
It is injective, and the full coset inclusion is also
injective. In particular unrelated old tagged vertices
are NEVER identified by ambient group coordinates.

This is the exact carrier needed to attach full H[B]
coset B-actions inside the replacement and retain the
original old permutation actions outside B by injection
extension. Signed edge maps, completed action and G-cover
are the next genuine source-geometric obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace EGraph

/-- Exactly the ORIGINAL vertices of an incomplete signed graph
outside ONE selected genuine signed B-connected component.
All source intrinsic old-component tags are retained. -/
abbrev OutsideOriginalBComponent
    (G : EGraph V OldEdge ι) (B : Finset ι) (anchor : V) :=
  {v : V // v ∉ G.BComponentVertexSet B anchor}

/-- Exactly the ORIGINAL vertices of the one selected
genuinely signed B-path-connected component. -/
abbrev InsideOriginalBComponent
    (G : EGraph V OldEdge ι) (B : Finset ι) (anchor : V) :=
  {v : V // v ∈ G.BComponentVertexSet B anchor}

/-- The CORRECT actual original-old-plus-fresh carrier for an
entire-component B-augmentation. The coset summand includes
ALL old selected-component coordinates PLUS genuinely fresh
full B-coset points, not only the latter; old vertices not in
the selected component remain separately tagged. -/
abbrev FullBComponentReplacementVertex
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (anchor : V) (g : Γ) :=
  (G.OutsideOriginalBComponent B anchor) ⊕
    IsolatedCosetGluing.CosetPoint gen B g

/-- An old vertex is represented by its EXACT injective
selected-component full-coset coordinate if inside the
chosen original B-component; otherwise its ORIGINAL
old vertex and component tags are preserved in the
distinct outside-left summand. -/
noncomputable def originalVertexToFullBReplacement
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (v : V) :
    G.FullBComponentReplacementVertex gen B anchor g := by
  classical
  exact if h : v ∈ G.BComponentVertexSet B anchor then
    .inr (coord ⟨v, h⟩)
  else
    .inl ⟨v, h⟩

/-- NO original old quotient vertices collapse in the
whole-component replacement, PROVIDED the true original
B-component has a signed-Cayley-coordinate INJECTION.
There is no global ambient H-multiCE injection assumption. -/
theorem originalVertexToFullBReplacement_injective
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (hcoord : Function.Injective coord) :
    Function.Injective
      (G.originalVertexToFullBReplacement gen B anchor g coord) := by
  classical
  intro v w heq
  by_cases hv : v ∈ G.BComponentVertexSet B anchor
  · by_cases hw : w ∈ G.BComponentVertexSet B anchor
    · have hsub :
          coord ⟨v, hv⟩ = coord ⟨w, hw⟩ := by
        simpa only [originalVertexToFullBReplacement,
          dif_pos hv, dif_pos hw, Sum.inr.injEq] using heq
      exact congrArg Subtype.val (hcoord hsub)
    · have hbad := heq
      simp [originalVertexToFullBReplacement, hv, hw] at hbad
  · by_cases hw : w ∈ G.BComponentVertexSet B anchor
    · have hbad := heq
      simp [originalVertexToFullBReplacement, hv, hw] at hbad
    · have hsub :
          (⟨v, hv⟩ : G.OutsideOriginalBComponent B anchor) =
            (⟨w, hw⟩ : G.OutsideOriginalBComponent B anchor) := by
        simpa only [originalVertexToFullBReplacement,
          dif_neg hv, dif_neg hw, Sum.inl.injEq] using heq
      exact congrArg Subtype.val hsub

/-- The full H[B] coset is LITERALLY injected into the
replacement carrier as the right summand, including all
old selected component vertices and all fresh points. -/
theorem fullBCosetToReplacement_injective
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (anchor : V) (g : Γ) :
    Function.Injective
      (fun p : IsolatedCosetGluing.CosetPoint gen B g =>
        (Sum.inr p :
          G.FullBComponentReplacementVertex gen B anchor g)) := by
  intro p q hpq
  exact Sum.inr.inj hpq

/-- Explicit original old selected-component image in the
whole full B-coset replacement. -/
theorem originalVertexToFullBReplacement_inside
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (v : V) (hv : v ∈ G.BComponentVertexSet B anchor) :
    G.originalVertexToFullBReplacement gen B anchor g coord v =
      Sum.inr (coord ⟨v, hv⟩) := by
  classical
  simp only [originalVertexToFullBReplacement, dif_pos hv]

/-- Explicit old tagged vertex image in the OUTSIDE
summand: no group-value map or quotient identification. -/
theorem originalVertexToFullBReplacement_outside
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (B : Finset ι) (anchor : V) (g : Γ)
    (coord :
      G.InsideOriginalBComponent B anchor →
        IsolatedCosetGluing.CosetPoint gen B g)
    (v : V) (hv : v ∉ G.BComponentVertexSet B anchor) :
    G.originalVertexToFullBReplacement gen B anchor g coord v =
      Sum.inl (⟨v, hv⟩ :
        G.OutsideOriginalBComponent B anchor) := by
  classical
  simp only [originalVertexToFullBReplacement, dif_neg hv]

end EGraph
end ABO
end PSTSEPPA
