import PSTSEPPA.ABO.SourceLiteralY1X2AllRankOne
import PSTSEPPA.ABO.SourceLiteralY1ThreeKindG2Action
import PSTSEPPA.ABO.DependentDisjointFibreTransitionQuotient
import PSTSEPPA.ABO.CayleyStageProjection
import PSTSEPPA.ABO.CayleyLeftTranslations

/-!
# Real literal T(X₂^all) → EACH original printed type-(2) augmented action

The accepted corrected ABO rank-one literal complete graph
X₂^all = Y₁ ⊔ original-input-derived 3-kind signed Z₁^all
contains EVERY selected type-(2) augmentation:
a genuine old H=T(Y₁) component-index-tagged P_A quotient
vertex z OFF the FULL selected B-coset, with a complete
new B-left coset attached exactly at z's group coordinate
and only legal fixed signed stationary loops thereafter.

Previously certified:
  - actual finite transition group G=T(X₂^all);
  - genuine generator-preserving quotient from G onto the
    transition group of the full *dependent* original
    three-kind Z₁ action;
  - exact labelled quotient from that dependent disjoint
    action onto ANY indexed component stage.

We compose these two genuine labelled quotients for the
precise .inr (.inr j) selected type-(2) index j. This
produces the ACTUAL labelled transition quotient of G
onto the named type-(2) augmented stage, without replacing
its original/fresh points by H ambient coordinates or
assuming a quotient that was not produced by X₂^all.

Consequently for ANY actual old or new vertex u of that
specific legally completed stage there is a concrete
based labelled signed Cayley(G) → T_j graph morphism whose
group identity maps EXACTLY to u, preserving both formal
inverse orientations, geometric loops and legal fixed loops.

This quotient/cover is a key SOURCE input for the now
certified type-(2) based old-component B-orbit detector.
The further local G[A] and original G[A] root coordinate
translation/alignment must be proved independently;
there is NO assertion that an arbitrary old G[A]
component maps into the OLD H side of an unbased cover.

R8, all corrected 4.7(iii), higher rank, Condition 5.2
and final finite PSTS EPPA are not claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The genuine finite source G=T(X₂^all) surjects, letter by
letter, onto the COMPLETE transition group of EVERY ACTUAL
original printed T(Y₁) type-(2) selected augmented stage.
No source-PSTS or quotient existence hypothesis remains. -/
noncomputable def sourceLiteralY1X2AllToType2Stage
    (src dst : ι → V)
    (j : sourceLiteralY1Type2Index src dst) :
    LabelledGroupQuotient
      (sourceLiteralY1X2AllGenerator src dst)
      ((sourceLiteralY1Type2ActionDatum src dst j).stage)
        .transitionSubgroupGenerator := by
  let idx : sourceLiteralY1ThreeKindIndex src dst :=
    Sum.inr (Sum.inr j)
  exact (sourceLiteralY1X2AllToThreeKind src dst).comp
    (dependentDisjointStage_fibreTransitionQuotient
      (fun t : sourceLiteralY1ThreeKindIndex src dst =>
        (sourceLiteralY1ThreeKindActionDatum src dst t).stage) idx)

/-- True labelled signed Cayley map from the actual
finite printed G=T(X₂^all), based at ANY vertex u of one
literal type-(2) augmented COMPLETE stage (old or fresh).
Original source component tags remain part of u. -/
noncomputable def sourceLiteralY1X2AllType2BasedCayleyHom
    (src dst : ι → V)
    (j : sourceLiteralY1Type2Index src dst)
    (u : (sourceLiteralY1Type2ActionDatum src dst j).Carrier) :
    LabelledGraphHom
      (cayleyGraph (sourceLiteralY1X2AllGenerator src dst))
        .toEGraph.toLabelledGraph
      ((sourceLiteralY1Type2ActionDatum src dst j).stage)
        .toEGraph.toLabelledGraph :=
  ((sourceLiteralY1Type2ActionDatum src dst j).stage)
    .cayleyProjectionFromGroup
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllToType2Stage src dst j).hom
      (sourceLiteralY1X2AllToType2Stage src dst j).map_gen
      u

/-- Genuine original component-tagged based stage vertex
is precisely the Cayley group identity's image. -/
@[simp] theorem sourceLiteralY1X2AllType2BasedCayleyHom_one
    (src dst : ι → V)
    (j : sourceLiteralY1Type2Index src dst)
    (u : (sourceLiteralY1Type2ActionDatum src dst j).Carrier) :
    (sourceLiteralY1X2AllType2BasedCayleyHom src dst j u)
      .onVertex 1 = u :=
  ((sourceLiteralY1Type2ActionDatum src dst j).stage)
    .cayleyProjectionFromGroup_one
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllToType2Stage src dst j).hom
      (sourceLiteralY1X2AllToType2Stage src dst j).map_gen u

/-- Full signed chronological word-action formula: the
actual original finite G word g_w sends 1 to the TRUE
old/new type-(2) vertex reached by w from chosen u.
No ambient H coset-tag erasure or unproved orbit action. -/
theorem sourceLiteralY1X2AllType2BasedCayleyHom_word
    (src dst : ι → V)
    (j : sourceLiteralY1Type2Index src dst)
    (u : (sourceLiteralY1Type2ActionDatum src dst j).Carrier)
    (w : LabelWord ι) :
    (sourceLiteralY1X2AllType2BasedCayleyHom src dst j u)
      .onVertex
        (PSTS.SignedWord.evalGroup
          (sourceLiteralY1X2AllGenerator src dst) w) =
      ((sourceLiteralY1Type2ActionDatum src dst j).stage)
        .followWord u w :=
  ((sourceLiteralY1Type2ActionDatum src dst j).stage)
    .cayleyProjectionFromGroup_evalGroup
      (sourceLiteralY1X2AllGenerator src dst)
      (sourceLiteralY1X2AllToType2Stage src dst j).hom
      (sourceLiteralY1X2AllToType2Stage src dst j).map_gen u w


/-- Translate the actual signed Cayley-G cover so that an
ARBITRARY genuine global group coordinate g, rather than
only the identity, maps EXACTLY to the specified original
component-tagged old/fresh type-(2) stage point u.

This is PRECOMPOSITION with a real signed Cayley LEFT
translation by g⁻¹. It does not assume a global input
graph embedding, transitivity of old H-component labels,
or equality of different original coset tags. -/
noncomputable def sourceLiteralY1X2AllType2BasedAtHom
    (src dst : ι → V)
    (j : sourceLiteralY1Type2Index src dst)
    (u : (sourceLiteralY1Type2ActionDatum src dst j).Carrier)
    (g : (sourceLiteralY1X2AllStage src dst).transitionGroup) :
    LabelledGraphHom
      (cayleyGraph (sourceLiteralY1X2AllGenerator src dst))
        .toEGraph.toLabelledGraph
      ((sourceLiteralY1Type2ActionDatum src dst j).stage)
        .toEGraph.toLabelledGraph :=
  (sourceLiteralY1X2AllType2BasedCayleyHom src dst j u).comp
    (cayleyLeftTranslateHom
      (sourceLiteralY1X2AllGenerator src dst) g⁻¹)

/-- At the EXACT specified genuine global group point g,
the translated Cayley cover is based at the genuine
old/fresh selected original type-(2) vertex u. -/
@[simp] theorem sourceLiteralY1X2AllType2BasedAtHom_base
    (src dst : ι → V)
    (j : sourceLiteralY1Type2Index src dst)
    (u : (sourceLiteralY1Type2ActionDatum src dst j).Carrier)
    (g : (sourceLiteralY1X2AllStage src dst).transitionGroup) :
    (sourceLiteralY1X2AllType2BasedAtHom src dst j u g)
      .onVertex g = u := by
  change
    (sourceLiteralY1X2AllType2BasedCayleyHom src dst j u)
      .onVertex (g⁻¹ * g) = u
  simpa using (sourceLiteralY1X2AllType2BasedCayleyHom_one
    src dst j u)

end ABO
end PSTSEPPA
