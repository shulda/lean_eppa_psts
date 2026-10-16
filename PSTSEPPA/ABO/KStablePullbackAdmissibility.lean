import PSTSEPPA.ABO.LabelledQuotientSkeletonPathLift
import PSTSEPPA.ABO.KStableTranslatedCosetEquiv
import PSTSEPPA.ABO.KRetractableCosetIntersections
import PSTSEPPA.ABO.CayleySubgraphAdmissibility

/-!
# Upward admissibility of the ACTUAL incomplete Cayley quotient pullback

This proves the corrected ABO Theorem 4.7(i) mechanism for
the canonical G-level pullback L_G of an admissible H-level
incomplete Cayley A-skeleton L_H, with a labelled
quotient Q : G ↠ H stable on all proper B⊊A.

Admissibility (Def. 3.16) requires: if x,y are actually
connected by a B-path in the old skeleton, and their
ambient B₁,B₂ cosets intersect for B₁,B₂⊊B⊊A,
there is an ACTUAL old common vertex reachable from
x by B₁ and from y by B₂.

Project the G-level old B-path and a witness of coset
intersection downstairs. H-admissibility gives a common
old endpoint z of two genuine B₁/B₂ signed paths.
Lift BOTH old paths under the real group quotient,
one from x and the other from y. Since x,y are
genuinely B-connected, the two lifted endpoints
lie inside the SAME ambient G[B]-coset. Their
H coordinates agree, so B-stability forces them
to be THE SAME upstairs point. This constructs
the required actual G-level intersection witness.

The theorem works for arbitrary finite alphabets,
including empty lower supports, nonfaithful generators,
loops and disconnected ambient skeletons. No global
retractability or ambient-coordinate collapse is used.

This is a certified-or-pending formal realization of
one full admissibility CLAUSE for canonical pullbacks,
NOT Theorem 4.7(ii) full multi-coset embeddedness,
Theorem 4.7(iii) bridge freeness, or the full
historical Yₖ/Zₖ induction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- Actual lifted admissibility at every required proper
subalphabet B⊊A, assuming precisely the LOCAL stability
on those proper subalphabets. This does not rely on
a fabricated injection of the full multi-coset quotient. -/
theorem pullbackQuotient_admissible_of_properStable
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (hAdm : K.AdmissibleForCosetExtension)
    (hStable : ∀ B : Finset ι, B ⊂ A → Q.StableAt B) :
    (K.pullbackQuotient Q).AdmissibleForCosetExtension := by
  let L := K.pullbackQuotient Q
  let F := K.pullbackQuotientHom Q
  intro B B₁ B₂ hBA hB₁ hB₂ x y hxy hInter
  have hDownReach :
      K.SubalphabetReachable B (F.onVertex x) (F.onVertex y) := by
    obtain ⟨w, hw, hPath⟩ := hxy
    exact ⟨w, hw, hPath.map F⟩
  have hDownInter :
      (generatedLeftCoset genΔ B₁ (F.onVertex x).1 ∩
        generatedLeftCoset genΔ B₂ (F.onVertex y).1).Nonempty := by
    obtain ⟨v, hv₁, hv₂⟩ := hInter
    refine ⟨Q.hom v, ?_, ?_⟩
    · change v ∈ generatedLeftCoset genΓ B₁ x.1 at hv₁
      change Q.hom v ∈ generatedLeftCoset genΔ B₁ (Q.hom x.1)
      exact Q.map_mem_generatedLeftCoset B₁ x.1 v hv₁
    · change v ∈ generatedLeftCoset genΓ B₂ y.1 at hv₂
      change Q.hom v ∈ generatedLeftCoset genΔ B₂ (Q.hom y.1)
      exact Q.map_mem_generatedLeftCoset B₂ y.1 v hv₂
  obtain ⟨z, hz₁, hz₂⟩ :=
    hAdm B B₁ B₂ hBA hB₁ hB₂
      (F.onVertex x) (F.onVertex y) hDownReach hDownInter
  obtain ⟨w₁, hw₁, hPath₁⟩ := hz₁
  obtain ⟨w₂, hw₂, hPath₂⟩ := hz₂
  obtain ⟨u, hLift₁, huMap⟩ :=
    K.pullbackQuotientHom_follows_lift Q hPath₁ x rfl
  obtain ⟨v, hLift₂, hvMap⟩ :=
    K.pullbackQuotientHom_follows_lift Q hPath₂ y rfl
  have hUses₁ : LabelWord.Uses B w₁ :=
    LabelWord.Uses.mono_explicit B₁ B hB₁.subset w₁ hw₁
  have hUses₂ : LabelWord.Uses B w₂ :=
    LabelWord.Uses.mono_explicit B₂ B hB₂.subset w₂ hw₂
  have huCoset : u.1 ∈ generatedLeftCoset genΓ B x.1 :=
    L.subalphabetReachable_implies_coset B x u
      ⟨w₁, hUses₁, hLift₁⟩
  have hyCoset : y.1 ∈ generatedLeftCoset genΓ B x.1 :=
    L.subalphabetReachable_implies_coset B x y hxy
  have hvCosetY : v.1 ∈ generatedLeftCoset genΓ B y.1 :=
    L.subalphabetReachable_implies_coset B y v
      ⟨w₂, hUses₂, hLift₂⟩
  have hCosetEq :
      generatedLeftCoset genΓ B x.1 =
        generatedLeftCoset genΓ B y.1 :=
    generatedLeftCoset_eq_of_mem genΓ B hyCoset
  have hvCosetX : v.1 ∈ generatedLeftCoset genΓ B x.1 := by
    rw [hCosetEq]
    exact hvCosetY
  have hMapValues : Q.hom u.1 = Q.hom v.1 := by
    have hu := congrArg (fun t : K.Vertex => t.1) huMap
    have hv := congrArg (fun t : K.Vertex => t.1) hvMap
    exact hu.trans hv.symm
  have huv : u = v := by
    apply Subtype.ext
    exact Q.injective_on_generatedLeftCoset_of_stableAt
      B (hStable B hBA) x.1 huCoset hvCosetX hMapValues
  refine ⟨u, ⟨w₁, hw₁, hLift₁⟩, ?_⟩
  refine ⟨w₂, hw₂, ?_⟩
  simpa [huv] using hLift₂

/-- Rank-k form matching the source Theorem 4.7:
a k-stable labelled group quotient transports
admissibility to the genuine G-pullback of an
H-admissible skeleton on at most k+1 labels.
The k+1 rank bound is used ONLY to infer stability
on every proper B⊊A. -/
theorem pullbackQuotient_admissible_of_kStable
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (k : ℕ)
    (hk : Q.KStable k)
    (hCard : A.card ≤ k + 1)
    (hAdm : K.AdmissibleForCosetExtension) :
    (K.pullbackQuotient Q).AdmissibleForCosetExtension := by
  apply K.pullbackQuotient_admissible_of_properStable Q hAdm
  intro B hBA
  have hlt : B.card < k + 1 :=
    lt_of_lt_of_le (Finset.card_lt_card hBA) hCard
  exact hk B (Nat.lt_succ_iff.mp hlt)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
