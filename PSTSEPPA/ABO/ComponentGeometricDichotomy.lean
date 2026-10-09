import PSTSEPPA.ABO.StrictCoatomEdgePatches
import PSTSEPPA.ABO.MultiCosetFullComponentFromSuperset
import PSTSEPPA.ABO.CoatomConstituentCover

/-!
# Whole B-component dichotomy: full B-coset or strict coatom patches

This packages the strongest certified unconditional geometry of
the full proper-alphabet multi-coset extension at ambient rank
|A|>=2, independently of the still-open cluster property.

For any root z and B⊊A, either z has a supporting selected maximal
C⊊A with B⊆C; then the ENTIRE intrinsic B-component of z is exactly
a full left B-coset within the particular component-tagged C-copy.
Or no such coatom exists; then EVERY directed B-edge at EVERY
B-reachable point lies in some completed coatom C with C∩B⊊B,
and its target has the very same intrinsic C-component tag.

Both alternatives use genuine path-connected components, the literal
glued quotient vertices, and actual signed oriented edge tokens.
No global Cayley embedding or bridge-freeness is assumed.

This is a *weak geometric dichotomy*, NOT the full cluster property:
the strictly lower patches in the second branch have NOT been
proved to share one component-wide common core or least support.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every B-component is either an exact full B-coset in a
selected tagged coatom C⊇B, or all of its actual signed B-edges
are contained in strict (B∩C)-patches inside selected tagged
coatoms, with their endpoints sharing the same C tag.
The missing global common-core condition is not asserted. -/
theorem allProperCoset_B_component_full_or_strict_coatom_patches
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 2 ≤ A.card)
    (B : Finset ι)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    (∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (p : K.AttachedCosetVertex C),
      C.card + 1 = A.card ∧
      B ⊆ C ∧
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret C hCP p = z ∧
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows z w y) ↔
        ∃ q : K.AttachedCosetVertex C,
          q.1 = p.1 ∧
          q.2.1 ∈ generatedLeftCoset gen B p.2.1 ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP q) ∨
    (∀ (y : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret),
      (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows z w y) →
      ∀ (e : K.MultiCosetEdgeVertexIncidenceQuotient
        (allProperCosetFamily A) hadm hgen hret),
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).source e = y →
        signedBase
          ((K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).label e) ∈ B →
        ∃ (C : Finset ι)
          (hCP : C ∈ (allProperCosetFamily A).alphabets)
          (p q : K.AttachedCosetVertex C)
          (s : {s : SignedLabel ι // signedBase s ∈ C}),
          C.card + 1 = A.card ∧
          (C ∩ B) ⊂ B ∧
          signedBase s.1 ∈ C ∩ B ∧
          q.1 = p.1 ∧
          e = K.multiCosetEdgeInclude
            (allProperCosetFamily A) hadm hgen hret C hCP
            (Sum.inr (p,s)) ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).target e =
              K.multiCosetInclude (allProperCosetFamily A)
                hadm hgen hret C hCP q) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  by_cases hLarge :
      ∃ (C : Finset ι) (hCP : C ∈ P.alphabets),
        C.card + 1 = A.card ∧
        B ⊆ C ∧
        K.MultiCosetVertexSupported P hadm hgen hret C z
  · left
    obtain ⟨C, hCP, hCard, hBC, _, p, hp⟩ := hLarge
    refine ⟨C, hCP, p, hCard, hBC, hp, ?_⟩
    intro y
    apply K.multiCoset_B_component_full_if_meets_selected_superset
      P hadm hgen hret C hCP B hBC p z
    exact ⟨[], LabelWord.uses_nil B,
      G.follows_nil_iff.mpr hp⟩
  · right
    intro y hzy e heSource heB
    apply K.allProperCoset_B_component_strict_coatom_edge_patches
      hadm hgen hret hAcard B z
    · intro C hCP hCard hBC hSupp
      exact hLarge ⟨C, hCP, hCard, hBC, hSupp⟩
    · exact hzy
    · exact heSource
    · exact heB

end CayleySubgraphSpec
end ABO
end PSTSEPPA
