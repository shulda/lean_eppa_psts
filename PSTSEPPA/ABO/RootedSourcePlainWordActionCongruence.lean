import PSTSEPPA.ABO.RootedSourceAllProperCompletedStageIso
import PSTSEPPA.ABO.CompleteStageWordKernelTransport

/-!
# Full signed-word congruence of the TRUE plain H₁ source proper-coset stages

An unaugmented full proper-alphabet coset-extension stage is
one of the actual corrected source Z₁ completed stages. The
independently certified original-rooted/local Γ[A] geometric
comparison is bijective on ALL quotient vertices and on directed
signed edge tokens, including the fixed loops of the LEGAL
trivial completion.

Therefore the ENTIRE complete signed-word action congruence is
identical for the local Γ[A] plain stage and the original
rooted Γ-ambient plain stage. This holds for arbitrary incomplete
Cayley input skeleton K, merely 2-retractable Γ and |A|=2,
without ambient Cayley injectivity or chosen representatives.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- True original plain P_A completed stage and its actual rooted
local Γ[A] model have the same complete signed-word action
congruence (two arbitrary words act identically on EVERY vertex). -/
theorem rootedAllProperCompletedStage_wordActionCongr_iff
    (A : Finset ι) (hcard : A.card = 2)
    (hret : KRetractable gen 2) (root : K.Vertex)
    (p q : LabelWord ι) :
    (∀ x,
      (K.rootedLocalAllProperCompletedStage
        A hcard hret root).followWord x p =
      (K.rootedLocalAllProperCompletedStage
        A hcard hret root).followWord x q) ↔
    (∀ y,
      (K.rootedAmbientAllProperCompletedStage
        A hcard hret root).followWord y p =
      (K.rootedAmbientAllProperCompletedStage
        A hcard hret root).followWord y q) := by
  exact
    (K.rootedLocalAllProperCompletedStage
      A hcard hret root).wordActionCongr_iff_of_bijectiveHom
      (K.rootedAmbientAllProperCompletedStage A hcard hret root)
      (K.rootedAllProperCompletedStageHom A hcard hret root)
      (K.rootedAllProperCompletedStageHom_bijective
        A hcard hret root).1 p q

end CayleySubgraphSpec
end ABO
end PSTSEPPA
