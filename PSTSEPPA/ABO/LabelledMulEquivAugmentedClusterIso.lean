import PSTSEPPA.ABO.AugmentedClusterTransport
import PSTSEPPA.ABO.LabelledGroupSubalphabetCosetTransport

/-!
# Signed augmented type-(1) clusters under TRUE labelled group isomorphisms

The ordinary augmented cluster is the union of a cluster of generated
proper-alphabet subgroups and ONE full attached left B-coset. It is
a signed Cayley subgraph with real positive/negative oriented edges.
The general ABO Lemma 3.14 transport under SURJECTIVE group
quotients uses stability and global target retractability.

For a generator-preserving actual GROUP ISOMORPHISM
E : Γ ≃* Δ, those hypotheses should NOT be needed: the exact
B-subgroup and gΓ[B] coset membership iff, already certified,
identifies every cluster/attached vertex and every signed
directed edge in BOTH directions, without assuming either
group globally retractable. This is relevant for the literal
T(Y₁) ≃* SourceH₁ equivalence, where each group is only known
2-retractable.

We construct a genuine vertex- and signed-edge-bijective
labelled graph isomorphism for EVERY cluster family P and
augmentation alphabet B, including empty/nested alphabets,
identity generators, geometric loops and distinct inverse edge
tokens. Matching the precise printed selected anchored type-(1)
Z₁ catalogue and legal fixed-loop completion remain later tasks.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable (genΓ : ι → Γ) (genΔ : ι → Δ)
variable (E : Γ ≃* Δ)
variable (hgen : ∀ i : ι, E (genΓ i) = genΔ i)

/-- A labelled group isomorphism as an actual surjective
labelled quotient, allowing reuse of the already certified
signed augmented-cluster graph morphism construction. -/
noncomputable def labelledMulEquivAsQuotient :
    LabelledGroupQuotient genΓ genΔ where
  hom := E.toMonoidHom
  map_gen := hgen
  surjective := E.surjective

/-- Honest signed augmented-cluster graph morphism under a
group ISOMORPHISM. Its vertex map is exactly E and it retains
the signed edge token label, not an ambient word choice. -/
noncomputable def labelledMulEquivAugmentedClusterHom
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :
    LabelledGraphHom
      (P.augmentedToLabelledGraph genΓ B v)
      (P.augmentedToLabelledGraph genΔ B (E v)) :=
  (labelledMulEquivAsQuotient genΓ genΔ E hgen).augmentedClusterHom P B v

/-- True bijectivity on ALL component/cluster/attached-coset
vertices of the signed B-augmented cluster. No stability
or globally retractable target group assumptions are used. -/
theorem labelledMulEquivAugmentedClusterHom_vertex_bijective
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :
    Function.Bijective
      (labelledMulEquivAugmentedClusterHom genΓ genΔ E hgen P B v).onVertex := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply E.injective
    exact congrArg Subtype.val hxy
  · intro y
    let x : Γ := E.symm y.1
    have hx : x ∈ P.AugmentedVertexSet genΓ B v := by
      rcases y.2 with hy | hy
      · rcases hy with ⟨C, hCP, hC⟩
        apply Or.inl
        refine ⟨C, hCP, ?_⟩
        apply (labelledMulEquiv_mem_generatedSubgroup_iff
          genΓ genΔ E hgen C x).mp
        simpa [x] using hC
      · apply Or.inr
        apply (labelledMulEquiv_mem_generatedLeftCoset_iff
          genΓ genΔ E hgen B v x).mp
        simpa [x] using hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simp [x, labelledMulEquivAugmentedClusterHom,
      labelledMulEquivAsQuotient]

/-- True bijectivity on ALL formal oriented signed old-cluster
and new-full-B-coset edge tokens, including positive/negative
loops and repeated labelled generators. No global retraction. -/
theorem labelledMulEquivAugmentedClusterHom_edge_bijective
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :
    Function.Bijective
      (labelledMulEquivAugmentedClusterHom genΓ genΔ E hgen P B v).onEdge := by
  constructor
  · intro e f hef
    apply Subtype.ext
    have hpair :
        (E e.1.1, e.1.2) = (E f.1.1, f.1.2) :=
      congrArg Subtype.val hef
    exact Prod.ext (E.injective (congrArg Prod.fst hpair))
      (congrArg Prod.snd hpair)
  · rintro ⟨⟨y, s⟩, hy⟩
    let x : Γ := E.symm y
    have hx : (x, s) ∈ P.AugmentedEdgeSet genΓ B v := by
      rcases hy with hy | hy
      · rcases hy with ⟨C, hCP, hC, hS⟩
        apply Or.inl
        refine ⟨C, hCP, ?_, hS⟩
        apply (labelledMulEquiv_mem_generatedSubgroup_iff
          genΓ genΔ E hgen C x).mp
        simpa [x] using hC
      · rcases hy with ⟨hC, hS⟩
        apply Or.inr
        refine ⟨?_, hS⟩
        apply (labelledMulEquiv_mem_generatedLeftCoset_iff
          genΓ genΔ E hgen B v x).mp
        simpa [x] using hC
    refine ⟨⟨(x, s), hx⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · simp [x, labelledMulEquivAugmentedClusterHom,
        labelledMulEquivAsQuotient]
    · rfl

/-- ACTUAL labelled-group isomorphisms automatically induce
augmented cluster isomorphisms on vertices and oriented signed
edges, even for merely k-retractable groups where the generic
quotient stability/retractability theorem cannot be applied. -/
theorem labelledMulEquivAugmentedClusterHom_bijective
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :
    Function.Bijective
      (labelledMulEquivAugmentedClusterHom genΓ genΔ E hgen P B v).onVertex ∧
    Function.Bijective
      (labelledMulEquivAugmentedClusterHom genΓ genΔ E hgen P B v).onEdge :=
  ⟨labelledMulEquivAugmentedClusterHom_vertex_bijective
      genΓ genΔ E hgen P B v,
    labelledMulEquivAugmentedClusterHom_edge_bijective
      genΓ genΔ E hgen P B v⟩

end ABO
end PSTSEPPA
