import PSTSEPPA.ABO.LocalRankRetractableSubalphabet
import PSTSEPPA.ABO.ComponentSubgraph

/-!
# Localize a TRUE ambient Cayley skeleton to the generated subgroup

The local rank-two ABO stage theorems take their Cayley skeleton over
the *actual* subgroup Γ[A], completed by identity generators outside
A. The source Section-5 input is instead a possibly disconnected
A-labelled skeleton in the original ambient Γ, or an H₁-cover of one.

There is a literal geometric bridge: fix any left A-coset representative
g. Translate the intersection of a given A-labelled skeleton with
g·Γ[A] by g⁻¹. The result is a TRUE `CayleySubgraphSpec` over the
completed subgroup Γ[A], with the exact vertex and signed-edge tokens
and a label-preserving embedding back into the source skeleton.

The construction needs NO global or bounded retractability hypothesis,
and preserves formal inverse edge tokens even for loops, trivial and
repeated generators. We establish both vertex/edge injectivity and the
precise image criterion: an old vertex is represented if and only if
it lies in g·Γ[A]. In particular the entire intrinsic A-component
of any chosen source vertex is represented.

This bridges the ambient-skeleton vs local-skeleton domains of the
rank-two stage construction. It does NOT yet choose all H₁-cover
skeletons of source Definition 5.3 or prove their cluster property.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- Under an A-label, inverse signed Cayley edges commute literally
with the left translation x ↦ g·x of the subgroup Γ[A] into Γ.
This does NOT assert a homomorphism on labels outside A. -/
theorem localCayley_inv_leftTranslate
    (gen : ι → Γ) (A : Finset ι) (g : Γ)
    (e : ActionEdge (generatedSubgroup gen A) ι)
    (he : signedBase e.2 ∈ A) :
    (g * (((cayleyGraph (trivialCompletionGenerator gen A)).inv e).1 : Γ),
      ((cayleyGraph (trivialCompletionGenerator gen A)).inv e).2) =
      (cayleyGraph gen).inv (g * (e.1 : Γ), e.2) := by
  rcases e with ⟨x, s⟩
  cases s with
  | pos i =>
      change i ∈ A at he
      apply Prod.ext
      · change
          g * (((x * trivialCompletionGenerator gen A i) :
            generatedSubgroup gen A) : Γ) =
            (g * (x : Γ)) * gen i
        rw [Subgroup.coe_mul, trivialCompletionGenerator_mem gen A he]
        exact mul_assoc _ _ _
      · rfl
  | neg i =>
      change i ∈ A at he
      apply Prod.ext
      · change
          g * (((x * (trivialCompletionGenerator gen A i)⁻¹) :
            generatedSubgroup gen A) : Γ) =
            (g * (x : Γ)) * (gen i)⁻¹
        rw [Subgroup.coe_mul, Subgroup.coe_inv,
          trivialCompletionGenerator_mem gen A he]
        exact mul_assoc _ _ _
      · rfl

namespace CayleySubgraphSpec

variable {gen : ι → Γ} {A : Finset ι}
variable (K : CayleySubgraphSpec gen A)

/-- An honest local Cayley skeleton over Γ[A], obtained by
left-translating the full intersection of K with g·Γ[A].
The source skeleton may be disconnected or even empty. -/
noncomputable def leftCosetSlice (g : Γ) :
    CayleySubgraphSpec (trivialCompletionGenerator gen A) A where
  vertices :=
    {x : generatedSubgroup gen A | g * (x : Γ) ∈ K.vertices}
  edges :=
    {e : ActionEdge (generatedSubgroup gen A) ι |
      (g * (e.1 : Γ), e.2) ∈ K.edges}
  source_mem := by
    intro e he
    have hsource := K.source_mem (g * (e.1 : Γ), e.2) he
    change g * (e.1 : Γ) ∈ K.vertices at hsource
    exact hsource
  inv_mem := by
    intro e he
    have hlabel : signedBase e.2 ∈ A := by
      have h := K.label_mem (g * (e.1 : Γ), e.2) he
      change signedBase e.2 ∈ A at h
      exact h
    change
      (g * (((cayleyGraph (trivialCompletionGenerator gen A)).inv e).1 : Γ),
        ((cayleyGraph (trivialCompletionGenerator gen A)).inv e).2) ∈ K.edges
    rw [localCayley_inv_leftTranslate gen A g e hlabel]
    exact K.inv_mem _ he
  label_mem := by
    intro e he
    have h := K.label_mem (g * (e.1 : Γ), e.2) he
    change signedBase e.2 ∈ A at h
    exact h

/-- The literal signed-graph embedding from the localized slice
back into the original ambient skeleton. No vertex identification
or quotienting occurs; it is left multiplication by g on vertices
and leaves every signed label untouched. -/
noncomputable def leftCosetSliceHom (g : Γ) :
    LabelledGraphHom
      ((K.leftCosetSlice g).toEGraph).toLabelledGraph
      (K.toEGraph).toLabelledGraph where
  onVertex x := ⟨g * (x.1 : Γ), x.2⟩
  onEdge e := ⟨(g * (e.1.1 : Γ), e.1.2), e.2⟩
  map_source := by
    intro e
    apply Subtype.ext
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    exact localCayley_inv_leftTranslate gen A g e.1
      ((K.leftCosetSlice g).label_mem e.1 e.2)
  map_label := by
    intro e
    rfl

/-- Left multiplication is injective on the translated old
vertex set, even when a generator acts trivially. -/
theorem leftCosetSliceHom_vertex_injective (g : Γ) :
    Function.Injective (K.leftCosetSliceHom g).onVertex := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have hg : g * (x.1 : Γ) = g * (y.1 : Γ) :=
    congrArg Subtype.val h
  exact mul_left_cancel hg

/-- The same embedding is injective on *formal signed edge tokens*.
This remains valid for parallel labels and graph-theoretic loops. -/
theorem leftCosetSliceHom_edge_injective (g : Γ) :
    Function.Injective (K.leftCosetSliceHom g).onEdge := by
  intro e f hef
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    have hg :
        g * (e.1.1 : Γ) = g * (f.1.1 : Γ) :=
      congrArg (fun z : K.Edge => z.1.1) hef
    exact mul_left_cancel hg
  · exact congrArg (fun z : K.Edge => z.1.2) hef

/-- The embedded local slice contains PRECISELY the vertices of K
lying in the selected left A-coset, not just some subset or a
chosen intrinsic connected component. -/
theorem leftCosetSliceHom_vertex_range_iff
    (g : Γ) (y : K.Vertex) :
    (∃ x : (K.leftCosetSlice g).Vertex,
      (K.leftCosetSliceHom g).onVertex x = y) ↔
      y.1 ∈ generatedLeftCoset gen A g := by
  constructor
  · rintro ⟨x, hx⟩
    change g⁻¹ * y.1 ∈ generatedSubgroup gen A
    have hxy : g * (x.1 : Γ) = y.1 :=
      congrArg Subtype.val hx
    rw [← hxy]
    simpa [mul_assoc] using x.1.property
  · intro hy
    change g⁻¹ * y.1 ∈ generatedSubgroup gen A at hy
    let t : generatedSubgroup gen A := ⟨g⁻¹ * y.1, hy⟩
    have hxy : g * (t : Γ) = y.1 := by
      simp [t, mul_assoc]
    have ht : t ∈ (K.leftCosetSlice g).vertices := by
      change g * (t : Γ) ∈ K.vertices
      rw [hxy]
      exact y.2
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- In particular, the ENTIRE intrinsic A-component of any source
vertex is represented in this one explicit Γ[A]-local skeleton. -/
theorem intrinsicAComponent_mem_leftCosetSliceHom_range
    (root y : K.Vertex)
    (h : K.SubalphabetReachable A root y) :
    ∃ x : (K.leftCosetSlice root.1).Vertex,
      (K.leftCosetSliceHom root.1).onVertex x = y := by
  apply (K.leftCosetSliceHom_vertex_range_iff root.1 y).2
  exact K.subalphabetReachable_implies_coset A root y h

end CayleySubgraphSpec
end ABO
end PSTSEPPA
