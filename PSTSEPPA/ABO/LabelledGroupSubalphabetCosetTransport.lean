import PSTSEPPA.ABO.SourceLiteralY1H1GroupEquiv
import PSTSEPPA.ABO.CosetConnectivity

/-!
# Generated-subalphabet and coset transport along labelled group isomorphisms

The true source group H₁ is already certified isomorphic, on every
distinguished generator, to the paper's literal T(Y₁). This is not
enough by itself to identify the SOURCE Definition-5.3 full/augmented
coset-extension data: one must also show that every genuine
subalphabet-generated group and LEFT coset is transported exactly.

We first prove GENERIC, orientation-safe statements for ANY
generator-preserving MulEquiv e : Γ ≃* Δ:

* evaluation of every chronological signed word commutes with e;
* membership in Γ[B] is equivalent to membership of e(g) in Δ[B];
* the actual generated subgroups Γ[B] and Δ[B] are isomorphic
  as groups, not merely equinumerous underlying point sets;
* every LEFT coset g Γ[B] transports pointwise to e(g) Δ[B].

We then specialize to the literal paper T(Y₁) and source-synchronized
H₁, proving genuine H₁[B] and B-coset compatibility for EVERY
subalphabet B, including ∅ and the whole alphabet. The result
is not an identification of differently tagged full-coset extension
vertices: it supplies the algebraic maps needed for the later
component-tagged quotient and signed-edge transport.

No source Z₁ selected-stage completeness, Condition 5.2, Theorem 4.7,
higher rank induction or unconditional PSTS EPPA is claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

/-- The chronological value of EVERY signed word is preserved by
a group isomorphism respecting the original generator labels.
This includes inverses, trivial generators and repeated labels. -/
theorem labelledMulEquiv_evalGroup
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (E : Γ ≃* Δ)
    (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
    (w : LabelWord ι) :
    E (PSTS.SignedWord.evalGroup genΓ w) =
      PSTS.SignedWord.evalGroup genΔ w := by
  induction w with
  | nil =>
      simp [PSTS.SignedWord.evalGroup]
  | cons s w ih =>
      cases s with
      | pos i =>
          change E (genΓ i *
            PSTS.SignedWord.evalGroup genΓ w) =
              genΔ i * PSTS.SignedWord.evalGroup genΔ w
          rw [map_mul, hgen, ih]
      | neg i =>
          change E ((genΓ i)⁻¹ *
            PSTS.SignedWord.evalGroup genΓ w) =
              (genΔ i)⁻¹ * PSTS.SignedWord.evalGroup genΔ w
          rw [map_mul, map_inv, hgen, ih]

/-- Exact equivalence of membership in ALL genuinely
subalphabet-generated groups under an isomorphism of labelled
groups. No retractability or finiteness of Γ/Δ is assumed. -/
theorem labelledMulEquiv_mem_generatedSubgroup_iff
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (E : Γ ≃* Δ)
    (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
    (B : Finset ι) (g : Γ) :
    E g ∈ generatedSubgroup genΔ B ↔
      g ∈ generatedSubgroup genΓ B := by
  constructor
  · intro hg
    obtain ⟨w, hw, hval⟩ :=
      exists_word_uses_eq_of_mem_generatedSubgroup genΔ B hg
    have heval := labelledMulEquiv_evalGroup genΓ genΔ E hgen w
    have hgval : PSTS.SignedWord.evalGroup genΓ w = g :=
      E.injective (heval.trans hval)
    rw [← hgval]
    exact evalGroup_mem_generatedSubgroup_of_uses genΓ B hw
  · intro hg
    obtain ⟨w, hw, hval⟩ :=
      exists_word_uses_eq_of_mem_generatedSubgroup genΓ B hg
    rw [← hval, labelledMulEquiv_evalGroup genΓ genΔ E hgen]
    exact evalGroup_mem_generatedSubgroup_of_uses genΔ B hw

/-- The map of generated subgroups is itself a TRUE group
isomorphism. In particular the target subgroup is neither
enlarged by artificial Y₁-completion edges nor reduced by
projecting away the original source-component tags. -/
noncomputable def labelledMulEquivGeneratedSubgroup
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (E : Γ ≃* Δ)
    (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
    (B : Finset ι) :
    generatedSubgroup genΓ B ≃* generatedSubgroup genΔ B := by
  let F : generatedSubgroup genΓ B →*
      generatedSubgroup genΔ B where
    toFun x :=
      ⟨E x.1, (labelledMulEquiv_mem_generatedSubgroup_iff
        genΓ genΔ E hgen B x.1).mpr x.2⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' x y := by
      apply Subtype.ext
      exact E.map_mul x.1 y.1
  apply MulEquiv.ofBijective F
  constructor
  · intro x y h
    apply Subtype.ext
    apply E.injective
    exact congrArg Subtype.val h
  · intro y
    let x : Γ := E.symm y.1
    have hx : x ∈ generatedSubgroup genΓ B := by
      apply (labelledMulEquiv_mem_generatedSubgroup_iff
        genΓ genΔ E hgen B x).mp
      simpa [x] using y.2
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change E x = y.1
    simp [x]

/-- Exact preservation of LEFT coset membership, for all
coset roots and all B. The direction matters: this is
g Γ[B], not Γ[B] g, in the source's chronological right
Cayley-step convention. -/
theorem labelledMulEquiv_mem_generatedLeftCoset_iff
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    (E : Γ ≃* Δ)
    (hgen : ∀ i : ι, E (genΓ i) = genΔ i)
    (B : Finset ι) (g x : Γ) :
    E x ∈ generatedLeftCoset genΔ B (E g) ↔
      x ∈ generatedLeftCoset genΓ B g := by
  change (E g)⁻¹ * E x ∈ generatedSubgroup genΔ B ↔
    g⁻¹ * x ∈ generatedSubgroup genΓ B
  have hEq : (E g)⁻¹ * E x = E (g⁻¹ * x) := by
    simp
  rw [hEq]
  exact labelledMulEquiv_mem_generatedSubgroup_iff
    genΓ genΔ E hgen B (g⁻¹ * x)

/-- Specialization to the TRUE algebraic identification of
our synchronized source H₁ with the printed T(Y₁):
membership in H₁[B] is exactly membership of the corresponding
printed group element in T(Y₁)[B]. -/
theorem sourceH1_literalY1_generatedSubgroup_mem_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (src dst : ι → V) (B : Finset ι)
    (g : SourceH1 src dst) :
    sourceH1EquivLiteralY1Transition src dst g ∈
      generatedSubgroup
        (sourceLiteralY1 src dst).transitionSubgroupGenerator B ↔
      g ∈ generatedSubgroup (sourceH1Generator src dst) B := by
  exact labelledMulEquiv_mem_generatedSubgroup_iff
    (sourceH1Generator src dst)
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1EquivLiteralY1Transition src dst)
    (sourceH1EquivLiteralY1Transition_generator src dst)
    B g

/-- Canonical actual isomorphism between every original H₁[B]
and the corresponding literal printed T(Y₁)[B], preserving
the same-labelled generators within that subgroup. -/
noncomputable def sourceH1_literalY1_generatedSubgroupEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (src dst : ι → V) (B : Finset ι) :
    generatedSubgroup (sourceH1Generator src dst) B ≃*
      generatedSubgroup
        (sourceLiteralY1 src dst).transitionSubgroupGenerator B :=
  labelledMulEquivGeneratedSubgroup
    (sourceH1Generator src dst)
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1EquivLiteralY1Transition src dst)
    (sourceH1EquivLiteralY1Transition_generator src dst) B

/-- The same printed/source identification transports every
generated LEFT coset, including B=∅ and B=univ. Crucial for
mapping the actual connected-component-tagged attached cosets
in corrected Definition 5.3. -/
theorem sourceH1_literalY1_generatedLeftCoset_mem_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (src dst : ι → V) (B : Finset ι)
    (g x : SourceH1 src dst) :
    sourceH1EquivLiteralY1Transition src dst x ∈
      generatedLeftCoset
        (sourceLiteralY1 src dst).transitionSubgroupGenerator B
        (sourceH1EquivLiteralY1Transition src dst g) ↔
      x ∈ generatedLeftCoset (sourceH1Generator src dst) B g := by
  exact labelledMulEquiv_mem_generatedLeftCoset_iff
    (sourceH1Generator src dst)
    (sourceLiteralY1 src dst).transitionSubgroupGenerator
    (sourceH1EquivLiteralY1Transition src dst)
    (sourceH1EquivLiteralY1Transition_generator src dst)
    B g x

end ABO
end PSTSEPPA
