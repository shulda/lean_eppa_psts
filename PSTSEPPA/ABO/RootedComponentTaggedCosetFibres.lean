import PSTSEPPA.ABO.RootedLocalProperCosetExactness
import PSTSEPPA.ABO.BijectiveComponentIndexTransport
import PSTSEPPA.ABO.IntrinsicComponentLocalSliceIso

/-!
# Exact tagged component B-coset fibres of rooted source/local skeletons

The first-rank source H1-cover graph is incomplete: distinct signed
path-components with the same ambient coset MUST have separate tags.
The certified rooted localization of any true A-component of a
Cayley skeleton into Γ[A] is an isomorphism on its OLD vertices
and formal directed edge tokens (#352). Under that graph isomorphism,
the quotient indices of every genuine D-path component agree (#361).

We now prove the other half of an attached-coset correspondence:
for EACH D⊆A, and EACH *specific intrinsic component tag* c in
the local rooted skeleton, membership of a local group point z
in the attached D-coset of c is EXACTLY membership of the ambient
point root*z in the corresponding D-coset of the original component.
Conversely, EVERY point in this latter ambient D-coset has a
UNIQUE local predecessor. This is not global surjectivity of
Γ[A] -> Γ and does not identify component tags by coordinates.

Combining these fibre-level facts with the tag bijection is
the remaining finite set-theoretic step towards the complete
tagged attached-coset bijections. The actual CE glued quotient,
old/new directed-edge transport and ALL B-augmentations still
need separate proofs before source Condition 5.2 or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- Every LOCAL component tag of the translated rooted A-component
is carried to the exact corresponding component of the original
A-path skeleton. This retains quotient indices; ambient group values
are never used to equate two different components. -/
noncomputable abbrev rootedLocalComponentIndexEquiv
    (A : Finset ι) (root : K.Vertex) (D : Finset ι) :=
  (K.intrinsicComponentLocalSlice A root).componentIndexEquiv_of_graphIso
    (K.subalphabetComponentSubgraph A root)
    (K.intrinsicComponentLocalHom A root)
    (K.intrinsicComponentLocalHom_bijective A root).1
    (K.intrinsicComponentLocalHom_bijective A root).2 D

/-- Forward AND reverse membership for a fixed tagged component
of every D⊆A attached D-coset. This uses the real graph-isomorphism
component-index equivalence and the exact local/ambient rooted
group coset lemma, not just an untagged ambient-coset equality. -/
theorem rootedLocal_componentAmbientCoset_translate_iff
    (A D : Finset ι) (hDA : D ⊆ A)
    (root : K.Vertex)
    (c : (K.intrinsicComponentLocalSlice A root).ComponentIndex D)
    (z : generatedSubgroup gen A) :
    z ∈ (K.intrinsicComponentLocalSlice A root).componentAmbientCoset D c ↔
      root.1 * (z : Γ) ∈
        (K.subalphabetComponentSubgraph A root).componentAmbientCoset D
          (K.rootedLocalComponentIndexEquiv A root D c) := by
  induction c using Quotient.inductionOn with
  | h x =>
      change z ∈
          generatedLeftCoset (trivialCompletionGenerator gen A) D x.1 ↔
        root.1 * (z : Γ) ∈
          generatedLeftCoset gen D (root.1 * (x.1 : Γ))
      exact localLeftCoset_translate_iff gen A D hDA root.1 x.1 z

/-- Each point of the ambient D-coset attached to the
translated component has a UNIQUE predecessor in Γ[A],
within the correct LOCAL D-component's attached coset.
The support restriction D⊆A is necessary. -/
theorem rootedLocal_componentAmbientCoset_unique_preimage
    (A D : Finset ι) (hDA : D ⊆ A)
    (root : K.Vertex)
    (c : (K.intrinsicComponentLocalSlice A root).ComponentIndex D)
    (y : Γ)
    (hy : y ∈
      (K.subalphabetComponentSubgraph A root).componentAmbientCoset D
        (K.rootedLocalComponentIndexEquiv A root D c)) :
    ∃! z : generatedSubgroup gen A,
      z ∈ (K.intrinsicComponentLocalSlice A root).componentAmbientCoset D c ∧
      root.1 * (z : Γ) = y := by
  induction c using Quotient.inductionOn with
  | h x =>
      have hx :
          y ∈ generatedLeftCoset gen D (root.1 * (x.1 : Γ)) := hy
      change ∃! z : generatedSubgroup gen A,
          z ∈ generatedLeftCoset
            (trivialCompletionGenerator gen A) D x.1 ∧
          root.1 * (z : Γ) = y
      exact localLeftCoset_translate_exists_unique
        gen A D hDA root.1 x.1 y hx

end CayleySubgraphSpec
end ABO
end PSTSEPPA
