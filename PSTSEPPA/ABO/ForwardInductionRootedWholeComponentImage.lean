import PSTSEPPA.ABO.ForwardInductionArbitraryRankSignedComponentTransport

/-!
# ABO Definition 3.22: FULL true signed B-component image under localization

Transport of individual signed paths is NOT YET enough for the
published cluster property. It quantifies over the entire genuine
B-component of a root in the old/fresh signed coset extension,
and its minimum supporting component-tagged pair must be attained
somewhere in that WHOLE set.

The exact original/local rooted signed EGraph quotient
isomorphism already preserves and reflects EVERY ACTUAL
signed B-word, including arbitrary missing original old edges,
both positive/inverse signs and fresh coset edges. It is also
surjective on all original tagged quotient vertices.

We deduce that the exact image of the ENTIRE local B-component
is precisely the ENTIRE original B-component of the corresponding
original rooted vertex. This is a set IMAGE identity, not
merely existence of some path, or equality of ambient Cayley
group word values.

It combines with source whole-minimum tagged-support transport
to transfer the full minimum of the whole component, as demanded
by ABO Definition 3.22. No ambient Γ retractability, original
component-tag collapse, new axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The true source B-component of a locally normalized
rooted multiCE is carried ONTO (not just INTO) the corresponding
true original B-component by the tagged quotient equivalence,
for every B, every selected proper coset family and any parent
rank C.

The original ambient Γ may be only k-retractable; this theorem
requires only the genuine LOCAL H[C] prerequisites. -/
theorem arbitraryRankRootedBComponent_image
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
      C root P hadm hgen hret) ''
      {v | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.arbitraryRankRootedLocalCompletedEGraph
          C root P hadm hgen hret).Follows u w v} =
    {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.arbitraryRankRootedOriginalCompletedEGraph
        C root P hadm hgen hret).Follows
          (K.arbitraryRankRootedLocalMultiCosetVertexEquiv
            C root P hadm hgen hret u) w y} := by
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  ext y
  constructor
  · rintro ⟨v, ⟨w, hw, hp⟩, hv⟩
    subst y
    exact ⟨w, hw,
      (K.arbitraryRankRootedCompletedEGraphHom_follows_iff
        C root P hadm hgen hret u v w).mp hp⟩
  · rintro ⟨w, hw, hp⟩
    obtain ⟨v, rfl⟩ := e.surjective y
    refine ⟨v, ?_, rfl⟩
    exact ⟨w, hw,
      (K.arbitraryRankRootedCompletedEGraphHom_follows_iff
        C root P hadm hgen hret u v w).mpr hp⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
