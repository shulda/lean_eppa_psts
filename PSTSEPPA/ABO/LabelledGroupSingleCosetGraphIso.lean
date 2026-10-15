import PSTSEPPA.ABO.LabelledIsoTaggedCosetTransport
import PSTSEPPA.ABO.SingleCosetEGraph
import PSTSEPPA.ABO.GraphHomInjectivity
import PSTSEPPA.ABO.BijectiveGraphPathReflection

/-!
# Actual signed single-B coset-extension isomorphism under labelled group isomorphism

Suppose two incomplete Cayley skeletons are isomorphic as *directed signed
graphs* and their group coordinates are related by a generator-preserving
group isomorphism. The component-tagged coset equivalence then extends
to a genuine graph isomorphism of the whole single-B coset extensions.

This checks BOTH kinds of actual directed edge tokens:
* original outside-B edges, which are transported by the true skeleton
  graph isomorphism, and
* the newly completed inside-B edges on every independently tagged
  full B-coset, whose signed positive and negative steps commute
  with the group isomorphism.

We explicitly preserve source, complete signed label and formal edge
reversal, and prove bijectivity on vertices AND directed edge tokens.
No missing old edge is invented and distinct intrinsic B-components
with coinciding ambient coset coordinates are never conflated.

The multi-alphabet glued signed edge quotient, legal loop completion
and augmented original Z-stage isomorphisms are separate later gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

/-- A genuine same-labelled group isomorphism respects BOTH orientations
of every signed generator, even for identity or repeated generators. -/
theorem labelledMulEquiv_evalGroupLetter
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (E : Γ ≃* Δ)
    (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
    (s : SignedLabel ι) :
    E (PSTS.SignedWord.evalGroupLetter genΓ s) =
      PSTS.SignedWord.evalGroupLetter genΔ s := by
  cases s with
  | pos i =>
      exact hgen i
  | neg i =>
      change E ((genΓ i)⁻¹) = (genΔ i)⁻¹
      rw [map_inv, hgen i]

namespace CayleySubgraphSpec

variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A D : Finset ι}
variable (L : CayleySubgraphSpec genΓ A)
variable (K : CayleySubgraphSpec genΔ D)
variable (f : LabelledGraphHom
  (L.toEGraph).toLabelledGraph
  (K.toEGraph).toLabelledGraph)
variable (hv : Function.Bijective f.onVertex)
variable (he : Function.Bijective f.onEdge)
variable (E : Γ ≃* Δ)
variable (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
variable (hcoord : ∀ x : L.Vertex, E x.1 = (f.onVertex x).1)

include hgen hcoord

/-- A true newly completed signed B-step on a component-tagged
coset vertex transports to the corresponding B-step of its image.
This checks the *intrinsic component tag* as well as group coordinates. -/
theorem labelledGroupIso_attachedCosetStep
    (B : Finset ι)
    (p : L.AttachedCosetVertex B)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    L.attachedCosetEquivOfLabelledGroupIso K f hv he E hgen hcoord B
      (L.cosetStep B p s) =
    K.cosetStep B
      (L.attachedCosetEquivOfLabelledGroupIso K f hv he E hgen hcoord B p)
      s := by
  apply K.attachedValue_injective_of_same_index B
  · rfl
  · calc
      K.attachedValue B
          (L.attachedCosetEquivOfLabelledGroupIso
            K f hv he E hgen hcoord B (L.cosetStep B p s)) =
          E (L.attachedValue B (L.cosetStep B p s)) :=
        L.attachedCosetEquivOfLabelledGroupIso_value
          K f hv he E hgen hcoord B (L.cosetStep B p s)
      _ = E (p.2.1 * PSTS.SignedWord.evalGroupLetter genΓ s.1) := rfl
      _ = E p.2.1 * E (PSTS.SignedWord.evalGroupLetter genΓ s.1) :=
        E.map_mul _ _
      _ = E p.2.1 * PSTS.SignedWord.evalGroupLetter genΔ s.1 :=
        congrArg (E p.2.1 * ·)
          (labelledMulEquiv_evalGroupLetter genΓ genΔ E hgen s.1)
      _ = K.attachedValue B
          (K.cosetStep B
            (L.attachedCosetEquivOfLabelledGroupIso
              K f hv he E hgen hcoord B p) s) := by
          rw [K.cosetStep_value,
            L.attachedCosetEquivOfLabelledGroupIso_value]
          rfl

/-- The whole non-complete signed single-B coset extension is mapped
as a REAL labelled graph. The map distinguishes old outside-B oriented
edge tokens from new full-coset B-edges. -/
noncomputable def labelledGroupIsoSingleCosetGraphHom
    (B : Finset ι) :
    LabelledGraphHom
      (L.singleCosetEGraph B).toLabelledGraph
      (K.singleCosetEGraph B).toLabelledGraph := by
  let vEquiv :=
    L.attachedCosetEquivOfLabelledGroupIso
      K f hv he E hgen hcoord B
  refine
    { onVertex := vEquiv
      onEdge := ?_
      map_source := ?_
      map_inv := ?_
      map_label := ?_ }
  · intro e
    cases e with
    | inl old =>
        refine Sum.inl ⟨f.onEdge old.1, ?_⟩
        change signedBase ((K.toEGraph).label (f.onEdge old.1)) ∉ B
        rw [f.map_label old.1]
        exact old.2
    | inr fresh =>
        exact Sum.inr (vEquiv fresh.1, fresh.2)
  · intro e
    cases e with
    | inl old =>
        change
          K.attachedOfSkeletonVertex B
            ((K.toEGraph).source (f.onEdge old.1)) =
          vEquiv (L.attachedOfSkeletonVertex B
            ((L.toEGraph).source old.1))
        rw [L.attachedCosetEquivOfLabelledGroupIso_oldVertex
          K f hv he E hgen hcoord]
        exact congrArg (K.attachedOfSkeletonVertex B) (f.map_source old.1)
    | inr fresh =>
        rfl
  · intro e
    cases e with
    | inl old =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact f.map_inv old.1
    | inr fresh =>
        apply congrArg Sum.inr
        apply Prod.ext
        · exact L.labelledGroupIso_attachedCosetStep
            K f hv he E hgen hcoord B fresh.1 fresh.2
        · rfl
  · intro e
    cases e with
    | inl old =>
        exact f.map_label old.1
    | inr fresh =>
        rfl

/-- The genuine graph morphism is surjective on BOTH old-outside-B
and new-inside-B oriented edge tokens. The inverse image of an
old edge is taken from the original incomplete graph, never its
ambient full Cayley completion. -/
theorem labelledGroupIsoSingleCosetGraphHom_edge_surjective
    (B : Finset ι) :
    Function.Surjective
      (L.labelledGroupIsoSingleCosetGraphHom
        K f hv he E hgen hcoord B).onEdge := by
  let vEquiv :=
    L.attachedCosetEquivOfLabelledGroupIso
      K f hv he E hgen hcoord B
  intro e
  cases e with
  | inl old =>
      obtain ⟨q, hq⟩ := he.2 old.1
      have hOutside : signedBase q.1.2 ∉ B := by
        change signedBase ((L.toEGraph).label q) ∉ B
        have hlabel :
            (L.toEGraph).label q =
              (K.toEGraph).label old.1 := by
          calc
            (L.toEGraph).label q =
                (K.toEGraph).label (f.onEdge q) :=
              (f.map_label q).symm
            _ = (K.toEGraph).label old.1 := by rw [hq]
        rw [hlabel]
        exact old.2
      refine ⟨Sum.inl ⟨q, hOutside⟩, ?_⟩
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hq
  | inr fresh =>
      obtain ⟨q, hq⟩ := vEquiv.surjective fresh.1
      refine ⟨Sum.inr (q, fresh.2), ?_⟩
      apply congrArg Sum.inr
      exact Prod.ext hq rfl

/-- Bijective on all actual vertices and signed oriented edge tokens.
In particular an old loop's two formal inverse tokens remain distinct. -/
theorem labelledGroupIsoSingleCosetGraphHom_bijective
    (B : Finset ι) :
    Function.Bijective
      (L.labelledGroupIsoSingleCosetGraphHom
        K f hv he E hgen hcoord B).onVertex ∧
    Function.Bijective
      (L.labelledGroupIsoSingleCosetGraphHom
        K f hv he E hgen hcoord B).onEdge := by
  constructor
  · exact (L.attachedCosetEquivOfLabelledGroupIso
      K f hv he E hgen hcoord B).bijective
  · constructor
    · exact (L.labelledGroupIsoSingleCosetGraphHom
        K f hv he E hgen hcoord B).edge_injective_of_vertex_injective
        (L.attachedCosetEquivOfLabelledGroupIso
          K f hv he E hgen hcoord B).injective
    · exact L.labelledGroupIsoSingleCosetGraphHom_edge_surjective
        K f hv he E hgen hcoord B

/-- All genuinely realised signed paths are preserved AND reflected
by the isomorphism of complete component-tagged B-coset attachments,
including old absent edges, geometric loops and inverse labels. -/
theorem labelledGroupIsoSingleCosetGraphHom_follows_iff
    (B : Finset ι)
    (u v : L.AttachedCosetVertex B) (w : LabelWord ι) :
    (L.singleCosetEGraph B).Follows u w v ↔
    (K.singleCosetEGraph B).Follows
      ((L.labelledGroupIsoSingleCosetGraphHom
        K f hv he E hgen hcoord B).onVertex u) w
      ((L.labelledGroupIsoSingleCosetGraphHom
        K f hv he E hgen hcoord B).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (L.labelledGroupIsoSingleCosetGraphHom
      K f hv he E hgen hcoord B)
    (L.labelledGroupIsoSingleCosetGraphHom_bijective
      K f hv he E hgen hcoord B).1
    (L.labelledGroupIsoSingleCosetGraphHom_bijective
      K f hv he E hgen hcoord B).2 u v w

end CayleySubgraphSpec
end ABO
end PSTSEPPA
