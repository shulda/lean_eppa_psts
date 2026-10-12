import PSTSEPPA.ABO.RootedTaggedAttachedCosetEquiv
import PSTSEPPA.ABO.SingleCosetExtension

/-!
# Signed completed-coset steps commute with source/local H1-root translation

The source-rooted map of genuine component-tagged attached B-coset
vertices (#367) must preserve the actual positive and INVERSE signed
B-edges of the completed coset extension. Vertex bijectivity by itself
does NOT supply this: the source and local groups have different
labelled generators outside their common parent alphabet.

For each B⊆A and any B-signed label s, the actual local transition
p -> p · evalLetter(trivialCompletionGenerator gen A,s)
transports to the genuine ambient H1 transition
(root·p) -> (root·p) · evalLetter(gen,s).
This equality is valid precisely because s is IN B⊆A and
the trivially completed local generator agrees with gen on A.
It handles both signed orientations, loops and repeated/identity
generator labels, without relying on global retractability of gen.

Together with #367's old-skeleton vertex correspondence, this is
the core next step toward a true labelled E-graph isomorphism of
the completed B-coset constituents. The outside-B original
edges, glued directed edge quotient and all augmentations remain
separate obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The normalized source-H1/local-H1[A] transport sends each
REAL completed signed B-edge to the correct ambient completed
signed B-edge, for every B⊆A. This is a literal equality of
tagged target vertices, not of just projected group coordinates. -/
theorem rootedLocalAttachedCosetMap_cosetStep
    (A B : Finset ι) (hBA : B ⊆ A)
    (root : K.Vertex)
    (p : (K.intrinsicComponentLocalSlice A root).AttachedCosetVertex B)
    (s : {s : SignedLabel ι // signedBase s ∈ B}) :
    K.rootedLocalAttachedCosetMap A B hBA root
      ((K.intrinsicComponentLocalSlice A root).cosetStep B p s) =
    (K.subalphabetComponentSubgraph A root).cosetStep B
      (K.rootedLocalAttachedCosetMap A B hBA root p) s := by
  apply (K.subalphabetComponentSubgraph A root).
    attachedValue_injective_of_same_index B
  · rfl
  · change root.1 *
        (((p.2.1 * PSTS.SignedWord.evalGroupLetter
          (trivialCompletionGenerator gen A) s.1 :
          generatedSubgroup gen A) : Γ)) =
      (root.1 * (p.2.1 : Γ)) *
        PSTS.SignedWord.evalGroupLetter gen s.1
    rcases s with ⟨s, hs⟩
    cases s with
    | pos i =>
        have hi : i ∈ A := hBA hs
        change root.1 *
            (((p.2.1 * trivialCompletionGenerator gen A i :
              generatedSubgroup gen A) : Γ)) =
          (root.1 * (p.2.1 : Γ)) * gen i
        rw [Subgroup.coe_mul, trivialCompletionGenerator_mem gen A hi]
        simp only [mul_assoc]
    | neg i =>
        have hi : i ∈ A := hBA hs
        change root.1 *
            (((p.2.1 * (trivialCompletionGenerator gen A i)⁻¹ :
              generatedSubgroup gen A) : Γ)) =
          (root.1 * (p.2.1 : Γ)) * (gen i)⁻¹
        rw [Subgroup.coe_mul, Subgroup.coe_inv,
          trivialCompletionGenerator_mem gen A hi]
        simp only [mul_assoc]

end CayleySubgraphSpec
end ABO
end PSTSEPPA
