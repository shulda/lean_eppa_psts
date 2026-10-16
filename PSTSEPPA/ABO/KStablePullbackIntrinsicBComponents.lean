import PSTSEPPA.ABO.LabelledQuotientSkeletonPathLift
import PSTSEPPA.ABO.KStableTranslatedCosetEquiv
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Exact relative intrinsic B-components of incomplete Cayley quotient pullbacks

Corrected ABO Theorem 4.7(i)-(iii) compares the ACTUAL
intrinsic B-path components of an H-level incomplete
Cayley skeleton K with its true G-level old-edge
pullback under a k-stable labelled quotient Q:G↠H.

This is not equality of ambient group coset coordinates:
a disconnected input K may have several intrinsic B-components
INSIDE a single H[B]-coset, and their G-pullback counterparts
must preserve those distinct path tags.

We prove the exact needed conditional comparison:

Given x,y in the true G-pullback, with y INSIDE the SAME
ambient translated G[B]-coset of x, the points are connected
by a genuine old B-labelled signed path upstairs IF AND ONLY
IF their images are connected by a genuine old B-labelled
signed path downstairs.

Forward implication maps real paths. Reverse implication
uses the certified lift of the SAME signed downstairs path
from the chosen upstairs point x, producing z in G[B].
The k-stable quotient is injective on this ONE G[B]-coset,
so its lifted endpoint z must equal the prescribed y.

The hypothesis y∈x G[B] CANNOT be omitted: distinct
upstairs cosets can project into the same downstairs
coset under a noninjective quotient. No conclusion about
different original component tags or full CE embedding
is silently inferred.

This is a genuine two-group, all-rank path-component
interface for the corrected Theorem 4.7 admissibility
and support arguments. It does not yet establish the
full multi-CE embeddedness or bridge-freeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- Exact old signed B-path correspondence for TWO points
of the genuine G-pullback lying in the SAME ambient
G[B]-coset, under stability of Q on B. Both signs,
B=∅, repeated labels, original loops and disconnected
old skeletons are allowed. -/
theorem pullbackQuotient_subalphabetReachable_iff_of_stableAt
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hB : Q.StableAt B)
    (x y : (K.pullbackQuotient Q).Vertex)
    (hyCoset : y.1 ∈ generatedLeftCoset genΓ B x.1) :
    (K.pullbackQuotient Q).SubalphabetReachable B x y ↔
      K.SubalphabetReachable B
        ((K.pullbackQuotientHom Q).onVertex x)
        ((K.pullbackQuotientHom Q).onVertex y) := by
  let L := K.pullbackQuotient Q
  let F := K.pullbackQuotientHom Q
  constructor
  · rintro ⟨w, hw, hPath⟩
    exact ⟨w, hw, hPath.map F⟩
  · rintro ⟨w, hw, hPath⟩
    obtain ⟨z, hzPath, hzMap⟩ :=
      K.pullbackQuotientHom_follows_lift Q hPath x rfl
    have hzCoset : z.1 ∈ generatedLeftCoset genΓ B x.1 :=
      L.subalphabetReachable_implies_coset B x z
        ⟨w, hw, hzPath⟩
    have hValues : Q.hom z.1 = Q.hom y.1 :=
      congrArg (fun t : K.Vertex => t.1) hzMap
    have hzy : z.1 = y.1 :=
      Q.injective_on_generatedLeftCoset_of_stableAt
        B hB x.1 hzCoset hyCoset hValues
    have hEqual : z = y := Subtype.ext hzy
    exact ⟨w, hw, hEqual ▸ hzPath⟩

/-- Reusable rank-k version of the SAME relative intrinsic
B-component result. Only |B|≤k stability is used; NO
global injectivity or retractability is assumed. -/
theorem pullbackQuotient_subalphabetReachable_iff_of_kStable
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (k : ℕ) (hk : Q.KStable k)
    (B : Finset ι) (hB : B.card ≤ k)
    (x y : (K.pullbackQuotient Q).Vertex)
    (hyCoset : y.1 ∈ generatedLeftCoset genΓ B x.1) :
    (K.pullbackQuotient Q).SubalphabetReachable B x y ↔
      K.SubalphabetReachable B
        ((K.pullbackQuotientHom Q).onVertex x)
        ((K.pullbackQuotientHom Q).onVertex y) :=
  K.pullbackQuotient_subalphabetReachable_iff_of_stableAt
    Q B (hk B hB) x y hyCoset

end CayleySubgraphSpec
end ABO
end PSTSEPPA
