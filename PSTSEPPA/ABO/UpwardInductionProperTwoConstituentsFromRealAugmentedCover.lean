import PSTSEPPA.ABO.UpwardInductionProperTwoConstSignedCosetLift
import PSTSEPPA.ABO.UpwardInductionEmbeddedFullBCosetStageWordEquality
import PSTSEPPA.ABO.KRetractableCosetIntersections

/-!
# ABO upward 4.7(iii): real proper n>=2 G B-bridge FROM A GENUINE H-STAGE COVER

This is the complete conditional algebraic/path-reassembly gate for
the corrected source off-skeleton proper B-cluster with >=2 selected
constituents. Its hypotheses no longer posit any abstract H-word
equality, any fake original G constituent paths, or any equality
between two different original-component-tagged G core points.

Required genuine source data:
* a B-supported ORIGINAL ambient Cayley(G) word p joining two
  actual selected component-tagged G attached coset anchor points;
* genuine B∩C₁ and B∩C₂ supported constituent words w₁,w₂;
* the actual source-G multi-coset ambient embedding already
  established by the corrected Theorem 4.7(ii);
* stable G→H at B;
* an actual complete H augmented stage T, with a TRUE injectively
  embedded full H[B] coset J (old B edges are PERMITTED);
* a real signed Cayley(G)→T labelled stage cover F, based at the
  precise image of the first original G anchor;
* an ACTUAL B-piece path w₁ ++ inv(w₂) from that same full
  H[B]-coset basepoint to the image of the TRUE G p endpoint.

Then the signed Cayley path plus genuine H[B] endpoint injectivity
FORCES [p]_H=[w₁ inv(w₂)]_H. B-stability reflects the equality
to G; actual signed G constituent coset paths are constructed,
their different tagged cores coalesce by the proved G ambient
embedding, and a REAL original G multiCE B-path w emerges, with
exact group value [w]_G=[p]_G.

The difficult remaining publication-specific work is constructing
the actual HISTORICAL H CE B-augmentation and its G-cover and
providing the real H two-piece path. This conditional theorem does
not silently assume those constructions or assert PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {V Edge ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable {genG : ι → Γ} {genH : ι → Δ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec genG A)

/-- Source-facing proper >=2 constituent bridge without an explicit
H-word-equality assumption. The real complete augmented H-stage
Cayley cover, injective full B-coset embedding, and an ACTUAL signed
augmented path with the mapped ambient endpoint imply the real
original G signed B-bridge of EXACTLY the expected G word value.

Every old/fresh original quotient tag and both directed inverse
edge tokens are retained. Old B-edges at the H core are permitted,
unlike the isolated-root special case. -/
theorem upwardProperTwoConstituents_signedBridge_of_realAugmentedCover
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated genG) (hret : Retractable genG)
    (Q : LabelledGroupQuotient genG genH)
    (B : Finset ι) (hStable : Q.StableAt B)
    (C₁ C₂ : Finset ι)
    (hC₁ : C₁ ∈ P.alphabets)
    (hC₂ : C₂ ∈ P.alphabets)
    (a₁ : K.AttachedCosetVertex C₁)
    (a₂ : K.AttachedCosetVertex C₂)
    (p w₁ w₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hw₁ : LabelWord.Uses (B ∩ C₁) w₁)
    (hw₂ : LabelWord.Uses (B ∩ C₂) w₂)
    (hAmbient :
      a₂.2.1 = a₁.2.1 * PSTS.SignedWord.evalGroup genG p)
    (hEmbed :
      Function.Injective
        (K.multiCosetAmbientValue P hadm hgen hret))
    (T : CompleteEGraph V Edge ι)
    (gH : Δ)
    (J : LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph genH B gH).toEGraph).toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (hJInjective : Function.Injective J.onVertex)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (p₀ : IsolatedCosetGluing.CosetPoint genH B gH)
    (hBase : F.onVertex a₁.2.1 = J.onVertex p₀)
    (hAugmentedPiecePath :
      T.toEGraph.Follows
        (J.onVertex p₀)
        (w₁ ++ PSTS.SignedWord.inv w₂)
        (F.onVertex
          (a₁.2.1 * PSTS.SignedWord.evalGroup genG p))) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        (K.multiCosetInclude P hadm hgen hret C₁ hC₁ a₁)
        w
        (K.multiCosetInclude P hadm hgen hret C₂ hC₂ a₂) ∧
      PSTS.SignedWord.evalGroup genG w =
        PSTS.SignedWord.evalGroup genG p := by
  have hW₁B : LabelWord.Uses B w₁ :=
    LabelWord.Uses.mono_explicit
      (B ∩ C₁) B Finset.inter_subset_left w₁ hw₁
  have hW₂B : LabelWord.Uses B (PSTS.SignedWord.inv w₂) :=
    LabelWord.Uses.mono_explicit
      (B ∩ C₂) B Finset.inter_subset_left
      (PSTS.SignedWord.inv w₂) hw₂.inv
  have hCombined :
      LabelWord.Uses B (w₁ ++ PSTS.SignedWord.inv w₂) :=
    (LabelWord.uses_append B w₁ (PSTS.SignedWord.inv w₂)).mpr
      ⟨hW₁B, hW₂B⟩
  have hH :
      PSTS.SignedWord.evalGroup genH p =
        PSTS.SignedWord.evalGroup genH
          (w₁ ++ PSTS.SignedWord.inv w₂) :=
    T.embeddedFullBCoset_HWordEquality_of_realGCayleyCover
      genH B gH J hJInjective genG F a₁.2.1 p₀
      p (w₁ ++ PSTS.SignedWord.inv w₂)
      hp hCombined hBase hAugmentedPiecePath
  exact K.upwardProperTwoConstituents_signedBridge_of_HWordEquality
    P hadm hgen hret Q B hStable C₁ C₂ hC₁ hC₂
    a₁ a₂ p w₁ w₂ hp hw₁ hw₂ hAmbient hH hEmbed

end CayleySubgraphSpec
end ABO
end PSTSEPPA
