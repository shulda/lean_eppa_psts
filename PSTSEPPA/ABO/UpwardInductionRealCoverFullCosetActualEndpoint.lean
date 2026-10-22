import PSTSEPPA.ABO.UpwardInductionEmbeddedFullBCosetStageWordEquality
import PSTSEPPA.ABO.CayleyStageProjection
import PSTSEPPA.ABO.UpwardInductionStageSignedWordEndpoint

/-!
# Corrected ABO 4.7(iii): REAL G Cayley cover endpoint in an embedded H[B] coset

The proper nonisolated B-cluster source argument requires
F(g₂)=i_H(s₂) for an ACTUAL labelled Cayley(G)→completed
H-augmentation cover F, where g₂=g₁*[p]_G and the two
TRUE original H endpoint vertices are represented inside
the newly full H[B] coset. This target equality must NOT
be inferred merely by equating the ambient H coordinates
of arbitrary differently tagged old H quotient vertices.

Instead, fix ONE genuine labelled full H[B]-coset graph
embedding J into ANY complete signed H-stage T. In that
coset the true completed-stage endpoint of each actual
B-supported signed word p, from its genuine coset point c₁,
is J(c₂) if and ONLY if c₂.coord=c₁.coord*[p]_H.

Thus if a real labelled Cayley(G)→T cover F is based at
the EXACT stage vertex J(c₁), the original signed
G-word endpoint g₁*[p]_G maps to the exact stage vertex
J(c₂) as soon as the H-coordinate condition holds.

No prior asserted equality of distinct old tagged quotient
vertices, no stage→Cayley(H) global morphism, no missing
old signed edge, no isolated-old-B-root hypothesis. This
is the precise missing **target endpoint detector** for
the source-forward-derived historical B-component→full
H[B] signed coset embedding and the actual source
Cayley(G)-to-augmented-stage cover.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ V StageEdge : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

namespace CompleteEGraph

variable (T : CompleteEGraph V StageEdge ι)

/-- Every genuine B-supported signed word from an embedded
full H[B] coset point ends at the precisely specified
coset point with the correct H-group coordinate. This
is equality of ACTUAL signed stage vertices, not merely
of ambient H group values. No global T→Cayley(H) map. -/
theorem embeddedFullBCoset_B_word_actualEndpoint
    (genH : ι → Δ) (B : Finset ι) (gH : Δ)
    (J : LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph genH B gH).toEGraph).toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (c₁ c₂ : IsolatedCosetGluing.CosetPoint genH B gH)
    (p : LabelWord ι) (hp : LabelWord.Uses B p)
    (hCoord :
      c₂.1 = c₁.1 * PSTS.SignedWord.evalGroup genH p) :
    T.followWord (J.onVertex c₁) p = J.onVertex c₂ := by
  obtain ⟨c, hEnd, hVal⟩ :=
    T.embeddedFullBCoset_B_followWord_exact
      genH B gH J c₁ p hp
  have hc : c = c₂ := by
    apply Subtype.ext
    exact hVal.trans hCoord.symm
  simpa only [hc] using hEnd

/-- EXACT original H-stage endpoint of an arbitrary REAL
signed Cayley(G)→T cover based at one ACTUAL full
H[B] coset point. The target is the genuine full-coset
point with correct H coordinate, not a fabricated
equality of unrelated original component tags.

The group quotient G→H can separately provide hCoord
from the known G signed word relation; this theorem
handles the ACTUAL signed stage graph geometry. -/
theorem cayleyGCover_original_B_word_exactHStageEndpoint
    (genG : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (genH : ι → Δ) (B : Finset ι) (gH : Δ)
    (J : LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph genH B gH).toEGraph).toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (g₁ : Γ)
    (c₁ c₂ : IsolatedCosetGluing.CosetPoint genH B gH)
    (p : LabelWord ι) (hp : LabelWord.Uses B p)
    (hBase : F.onVertex g₁ = J.onVertex c₁)
    (hCoord :
      c₂.1 = c₁.1 * PSTS.SignedWord.evalGroup genH p) :
    F.onVertex (g₁ * PSTS.SignedWord.evalGroup genG p) =
      J.onVertex c₂ := by
  have hCayley :
      (cayleyGraph genG).followWord g₁ p =
        g₁ * PSTS.SignedWord.evalGroup genG p :=
    cayleyGraph.followWord_eq_mul_evalGroup genG g₁ p
  have hMapped :
      T.followWord (F.onVertex g₁) p =
        F.onVertex ((cayleyGraph genG).followWord g₁ p) :=
    CompleteEGraph.hom_followWord (cayleyGraph genG) T F g₁ p
  calc
    F.onVertex (g₁ * PSTS.SignedWord.evalGroup genG p) =
        F.onVertex ((cayleyGraph genG).followWord g₁ p) :=
      congrArg F.onVertex hCayley.symm
    _ = T.followWord (F.onVertex g₁) p := hMapped.symm
    _ = T.followWord (J.onVertex c₁) p := by rw [hBase]
    _ = J.onVertex c₂ :=
      T.embeddedFullBCoset_B_word_actualEndpoint
        genH B gH J c₁ c₂ p hp hCoord

end CompleteEGraph
end ABO
end PSTSEPPA
