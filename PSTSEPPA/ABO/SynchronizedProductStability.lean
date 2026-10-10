import PSTSEPPA.ABO.SynchronizedLabelledGroups
import PSTSEPPA.ABO.StageStabilityWordKernel

/-!
# Rank stability under synchronized labelled products

The corrected ABO Section 5 builds finite transition groups of disjoint
unions by synchronizing equally labelled generators. A quotient of each
component transition group onto the same ambient labelled group should
induce a quotient of the synchronized product onto that group.

For rank stability the key is stronger: if every factor kills each
ambient-identity word supported on at most k letters, then the synchronized
product also kills it. We prove this directly from the signed-word
evaluation formulas for both coordinate projections and the exact
word-kernel characterization of k-stability.

This is a genuine group-theoretic assembly lemma. The existence and
k-stability of the individual ABO Section 5 stages, the finite Z_k
family, and the reflecting-group construction are separate obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ Θ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ] [Group Θ]

namespace SynchronizedProduct

/-- Synchronizing two labelled groups and then taking the first
factor's labelled quotient produces a genuine labelled quotient
to the common target. Surjectivity is inherited from the first
projection, assuming its generators generate that factor. -/
def commonQuotient
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    {genΘ : ι → Θ}
    (hgenΓ : IsGenerated genΓ)
    (QΓ : LabelledGroupQuotient genΓ genΘ) :
    LabelledGroupQuotient (generator genΓ genΔ) genΘ :=
  (fstQuotient genΓ genΔ hgenΓ).comp QΓ

/-- Rank-k stability is preserved by synchronized products of
labelled groups admitting k-stable quotients to a common target.
A single identity-valued word vanishes in BOTH coordinates;
as the synchronized product is a concrete subgroup of their
product, it must vanish there as well. -/
theorem commonQuotient_kStable
    (genΓ : ι → Γ) (genΔ : ι → Δ)
    {genΘ : ι → Θ}
    (hgenΓ : IsGenerated genΓ)
    (QΓ : LabelledGroupQuotient genΓ genΘ)
    (QΔ : LabelledGroupQuotient genΔ genΘ)
    (k : ℕ)
    (hΓ : QΓ.KStable k)
    (hΔ : QΔ.KStable k) :
    (commonQuotient genΓ genΔ hgenΓ QΓ).KStable k := by
  apply (commonQuotient genΓ genΔ hgenΓ QΓ).kStable_of_word_kernel k
  intro A hA w hw hvalue
  have hΓword : PSTS.SignedWord.evalGroup genΓ w = 1 :=
    ((QΓ.kStable_iff_word_kernel k).mp hΓ) A hA w hw hvalue
  have hΔword : PSTS.SignedWord.evalGroup genΔ w = 1 :=
    ((QΔ.kStable_iff_word_kernel k).mp hΔ) A hA w hw hvalue
  apply Subtype.ext
  apply Prod.ext
  · change fstHom genΓ genΔ
      (PSTS.SignedWord.evalGroup (generator genΓ genΔ) w) = (1 : Γ)
    exact (fstHom_evalGroup genΓ genΔ w).trans hΓword
  · change sndHom genΓ genΔ
      (PSTS.SignedWord.evalGroup (generator genΓ genΔ) w) = (1 : Δ)
    exact (sndHom_evalGroup genΓ genΔ w).trans hΔword

end SynchronizedProduct
end ABO
end PSTSEPPA
