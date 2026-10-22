import PSTSEPPA.ABO.UpwardInductionAugmentedClusterBWordEquality
import PSTSEPPA.ABO.CayleyStageProjection
import PSTSEPPA.ABO.KRetractableCosetIntersections

/-!
# A REAL Cayley(G) cover forces H-word equality in a NONISOLATED augmented cluster

Corrected ABO Theorem 4.7(iii) requires a G-Cayley cover of the
H-stage where the WHOLE proper B-cluster is augmented by a full
H[B]-coset. Unlike a single-point isolated-root attachment, the
original cluster can already contain many actual B-labelled edges.

The previous `augmentedTrivialStage_B_sameEndpoint_evalGroup_eq`
proves exact B-word-endpoint detection for the literal canonical
augmented cluster, whose old signed edges are ALL retained.

Here a genuine labelled Cayley(G) -> this actual complete H-stage
takes the original ambient signed B-word p to an actual stage path.
If another real signed path q begins at the same full B-coset
point and ends exactly at the image of the G endpoint of p,
determinism implies that the two H B-word evaluations are equal.

The specialization q=w₁ ++ inv(w₂) has the exact source
B∩C₁/B∩C₂ support. There is NO false requirement that the
cluster core lacks outgoing old B-labelled edges.

This does not yet construct the specific HISTORY-SELECTED
component-tagged H-stage augmentation or its G-cover. That is
a separate remaining geometric equivalence and lifting task.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*} [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ] {A : Finset ι}

namespace ClusterSpec

variable (P : ClusterSpec A)

/-- Cover-forced B-word equality in a genuine NONISOLATED
canonical H-cluster augmentation. The cover sends the original
G Cayley B-word into the actual signed completed H-stage,
not into a hypothetical Cayley(H) image of missing loops. -/
theorem augmentedTrivialStage_HWordEquality_of_realGCayleyCover
    (genH : ι → Δ) (B : Finset ι) (hBA : B ⊆ A) (vH : Δ)
    (x : (P.augmentedCayleySubgraph genH B hBA vH).Vertex)
    (hx : x.1 ∈ generatedLeftCoset genH B vH)
    (genG : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      (P.augmentedTrivialStage (gen := genH) B hBA vH).toEGraph.toLabelledGraph)
    (u : Γ)
    (p q : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hq : LabelWord.Uses B q)
    (hBase : F.onVertex u = x)
    (hSecondPath :
      (P.augmentedTrivialStage (gen := genH) B hBA vH).toEGraph.Follows
        x q (F.onVertex (u * PSTS.SignedWord.evalGroup genG p))) :
    PSTS.SignedWord.evalGroup genH p =
      PSTS.SignedWord.evalGroup genH q := by
  let T := P.augmentedTrivialStage (gen := genH) B hBA vH
  have hCayley :
      (cayleyGraph genG).toEGraph.Follows
        u p (u * PSTS.SignedWord.evalGroup genG p) := by
    simpa only [cayleyGraph.followWord_eq_mul_evalGroup] using
      (cayleyGraph genG).follows_followWord u p
  have hMapped :
      T.toEGraph.Follows x p
        (F.onVertex (u * PSTS.SignedWord.evalGroup genG p)) := by
    have h := hCayley.map F
    rw [hBase] at h
    exact h
  have hPEnd :
      T.followWord x p =
        F.onVertex (u * PSTS.SignedWord.evalGroup genG p) :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord x p) hMapped
  have hQEnd :
      T.followWord x q =
        F.onVertex (u * PSTS.SignedWord.evalGroup genG p) :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord x q) hSecondPath
  exact P.augmentedTrivialStage_B_sameEndpoint_evalGroup_eq
    (gen := genH) B hBA vH x hx p q hp hq
    (hPEnd.trans hQEnd.symm)

/-- Two-constituent proper-cluster signed H-word equality in
the TRUE canonical B-augmentation, once the actual G-cover
and genuine H-piece signed path are supplied. In particular,
the original cluster need NOT be B-edge-isolated. -/
theorem augmentedTrivialStage_properTwoPiece_HWordEquality_of_realGCayleyCover
    (genH : ι → Δ) (B : Finset ι) (hBA : B ⊆ A) (vH : Δ)
    (x : (P.augmentedCayleySubgraph genH B hBA vH).Vertex)
    (hx : x.1 ∈ generatedLeftCoset genH B vH)
    (genG : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      (P.augmentedTrivialStage (gen := genH) B hBA vH).toEGraph.toLabelledGraph)
    (u : Γ) (C₁ C₂ : Finset ι)
    (p w₁ w₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hw₁ : LabelWord.Uses (B ∩ C₁) w₁)
    (hw₂ : LabelWord.Uses (B ∩ C₂) w₂)
    (hBase : F.onVertex u = x)
    (hAugmentedPiecePath :
      (P.augmentedTrivialStage (gen := genH) B hBA vH).toEGraph.Follows
        x (w₁ ++ PSTS.SignedWord.inv w₂)
        (F.onVertex (u * PSTS.SignedWord.evalGroup genG p))) :
    PSTS.SignedWord.evalGroup genH p =
      PSTS.SignedWord.evalGroup genH
        (w₁ ++ PSTS.SignedWord.inv w₂) := by
  have hW₁ : LabelWord.Uses B w₁ :=
    LabelWord.Uses.mono_explicit
      (B ∩ C₁) B Finset.inter_subset_left w₁ hw₁
  have hW₂ : LabelWord.Uses B (PSTS.SignedWord.inv w₂) :=
    LabelWord.Uses.mono_explicit
      (B ∩ C₂) B Finset.inter_subset_left
      (PSTS.SignedWord.inv w₂) hw₂.inv
  have hConcat : LabelWord.Uses B
      (w₁ ++ PSTS.SignedWord.inv w₂) :=
    (LabelWord.uses_append B w₁ (PSTS.SignedWord.inv w₂)).mpr
      ⟨hW₁, hW₂⟩
  exact P.augmentedTrivialStage_HWordEquality_of_realGCayleyCover
    genH B hBA vH x hx genG F u
    p (w₁ ++ PSTS.SignedWord.inv w₂)
    hp hConcat hBase hAugmentedPiecePath

end ClusterSpec
end ABO
end PSTSEPPA
