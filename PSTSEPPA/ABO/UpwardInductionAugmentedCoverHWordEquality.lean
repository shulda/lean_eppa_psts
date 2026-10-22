import PSTSEPPA.ABO.UpwardInductionAugmentedFullBCosetWordEquality
import PSTSEPPA.ABO.CayleyStageProjection

/-!
# Corrected ABO Theorem 4.7(iii): actual G cover of B-augmentation yields H word equality

The source's key off-skeleton PROPER n≥2 step does not
ASSUME a mysterious group relation [p]_H=[p₁ inv(p₂)]_H.
It produces it from:

* an ACTUAL signed labelled Cayley(G)→T cover of the
  legally completed H-stage with an attached FULL H[B] coset;
* the true original G Cayley B-word p from u to
  u*[p]_G, so its image under the genuine stage cover
  is a REAL T signed p-path;
* the accurate stage basepoint F(u) in the glued
  full H[B] coset, including the old root case;
* an independently REAL signed path in the augmented
  stage with word p₁ inv(p₂) from exactly the SAME
  basepoint to F(u*[p]_G).

The true signed G Cayley path maps to the correct
signed completed-stage path. Deterministic signed paths
from the same source to the same target have identical
true completed-stage endpoints under their respective
word-following operations. The independently certified
exact full-B-augmentation detector now proves
[p]_H=[p₁ inv(p₂)]_H.

No assumption that the entire legally loop-completed H
stage embeds in Cayley(H), no false fixed outside-B
loop treated as an H-group relation, no invented
missing old signed edge and no old tag collapse.

The remaining source geometry must furnish the
actual B-augmentation H path p₁ inv(p₂) ending at
the required image of the G ambient endpoint, using
the true proper H cluster/core. This is more concrete
than assuming equality of H group words directly.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

/-- A real G→legally completed H B-AUGMENTATION cover and
one ACTUAL completed-stage constituent-piece B-path from
its correct glued full-B source to the image of the genuine
G ambient p endpoint yield EXACTLY the group-word equality
used by the proper n≥2 source upward bridge argument.

Every signed path is witnessed using genuine positive and
inverse edge tokens; the proof does NOT presuppose
ambient H-embedding of the loop-completed stage. -/
theorem augmentedStage_HWordEquality_of_realGCayleyCover
    (H : EGraph V OldEdge ι)
    (genH : ι → Δ) (B : Finset ι) (gH : Δ) (root : V)
    (hMissing : ∀ e : OldEdge,
      H.source e = root → signedBase (H.label e) ∉ B)
    (hpaired : H.LocallyPairedLabels)
    (p₀ : CosetPoint genH B gH)
    (genG : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      (completedStage H genH B gH root hMissing hpaired).toEGraph.toLabelledGraph)
    (u : Γ)
    (C₁ C₂ : Finset ι)
    (p w₁ w₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hw₁ : LabelWord.Uses (B ∩ C₁) w₁)
    (hw₂ : LabelWord.Uses (B ∩ C₂) w₂)
    (hBase :
      F.onVertex u = gluePoint genH B gH root p₀)
    (hAugmentedPiecePath :
      (completedStage H genH B gH root hMissing hpaired).toEGraph.Follows
        (gluePoint genH B gH root p₀)
        (w₁ ++ PSTS.SignedWord.inv w₂)
        (F.onVertex (u * PSTS.SignedWord.evalGroup genG p))) :
    PSTS.SignedWord.evalGroup genH p =
      PSTS.SignedWord.evalGroup genH
        (w₁ ++ PSTS.SignedWord.inv w₂) := by
  let T := completedStage H genH B gH root hMissing hpaired
  have hCayley :
      (cayleyGraph genG).toEGraph.Follows
        u p (u * PSTS.SignedWord.evalGroup genG p) := by
    simpa only [cayleyGraph.followWord_eq_mul_evalGroup] using
      (cayleyGraph genG).follows_followWord u p
  have hMapped :
      T.toEGraph.Follows
        (gluePoint genH B gH root p₀) p
        (F.onVertex (u * PSTS.SignedWord.evalGroup genG p)) := by
    have h := hCayley.map F
    rw [hBase] at h
    exact h
  have hPEnd :
      T.followWord (gluePoint genH B gH root p₀) p =
        F.onVertex (u * PSTS.SignedWord.evalGroup genG p) :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord (gluePoint genH B gH root p₀) p)
      hMapped
  have hQEnd :
      T.followWord (gluePoint genH B gH root p₀)
          (w₁ ++ PSTS.SignedWord.inv w₂) =
        F.onVertex (u * PSTS.SignedWord.evalGroup genG p) :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord
        (gluePoint genH B gH root p₀)
        (w₁ ++ PSTS.SignedWord.inv w₂))
      hAugmentedPiecePath
  have hSameEndpoint :
      T.followWord (gluePoint genH B gH root p₀) p =
      T.followWord (gluePoint genH B gH root p₀)
          (w₁ ++ PSTS.SignedWord.inv w₂) :=
    hPEnd.trans hQEnd.symm
  exact completedStage_properTwoPiece_BWordEquality
    H genH B gH root hMissing hpaired p₀
    C₁ C₂ p w₁ w₂ hp hw₁ hw₂ hSameEndpoint

end IsolatedCosetGluing
end ABO
end PSTSEPPA
