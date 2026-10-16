import PSTSEPPA.ABO.KStableLocalGeneratedSubgroupQuotient
import PSTSEPPA.ABO.LocalCosetCayleySlice
import PSTSEPPA.ABO.LabelledQuotientSkeletonPullback

/-!
# Localizing genuine incomplete G/H Cayley old covers commutes with pullback

Source-corrected ABO Theorem 4.7(ii) works in TRUE local
groups G[A], H[A] (not globally 2-retractable G, H).
We already have the genuine labelled generated-subgroup
quotient Q_A:G[A]↠H[A], with outside-A letters trivial.

Let Q:G↠H, and let K be ANY original INCOMPLETE
H-Cayley A-skeleton, with arbitrary missing old signed
edges and disconnected input components. Its G-cover
L=Q⁻¹(K) is the exact old-edge pullback, no completed
fictional X₁ edges.

Fix ANY group point g∈G and form the actual left-coset
slice of L on g·G[A], translated by g⁻¹ to G[A].
Downstairs form the H left-coset slice of K on
Q(g)·H[A], translated by Q(g)⁻¹ to H[A].

We prove the strict equality of the two independently
defined LOCAL ORIGINAL skeletons, on vertex and directed
signed-edge membership:

  slice_g(Q⁻¹(K)) = Q_A⁻¹(slice_Q(g)(K)).

Both sides retain exactly the SAME old vertices
and EXACT formal signed oriented edges. The proof
uses only that Q respects multiplication and that
the concrete subgroup hom Q_A is its restriction,
not generator faithfulness, ambient injectivity,
full retractability or artificial edge completion.

Together with the true local A-retractability and
A-labelled generation results, this is the precise
geometric interface needed to instantiate the
FULL local multiCE embedding proof after the
source's completed H-stage cover collision is
established. It does not itself prove any such
collision or bridge freeness.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- An exact equality of ORIGINAL old VERTEX SETS
for localization of a genuine G-cover and pullback
of the corresponding H-local skeleton. No choice
of path representatives or completion is involved. -/
theorem pullbackQuotient_leftCosetSlice_vertices_eq
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (g : Γ) :
    ((K.pullbackQuotient Q).leftCosetSlice g).vertices =
      ((K.leftCosetSlice (Q.hom g)).pullbackQuotient
        (Q.localGeneratedSubgroupQuotient A)).vertices := by
  ext x
  change Q.hom (g * (x : Γ)) ∈ K.vertices ↔
    Q.hom g *
      (((Q.subgroupHom A x : generatedSubgroup genΔ A) : Δ)) ∈
        K.vertices
  simp only [map_mul, Q.subgroupHom_val]

/-- The stronger edge-level equality: localizing a
TRUE original incomplete G skeleton and lifting the
TRUE local H skeleton under Q_A yield precisely
the SAME formal oriented signed old edge tokens,
including inverses and original input loops.
No missing old edge is inserted by either route. -/
theorem pullbackQuotient_leftCosetSlice_edges_eq
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (g : Γ) :
    ((K.pullbackQuotient Q).leftCosetSlice g).edges =
      ((K.leftCosetSlice (Q.hom g)).pullbackQuotient
        (Q.localGeneratedSubgroupQuotient A)).edges := by
  ext e
  change
    (Q.hom (g * (e.1 : Γ)), e.2) ∈ K.edges ↔
      (Q.hom g *
        (((Q.subgroupHom A e.1 : generatedSubgroup genΔ A) : Δ)),
        e.2) ∈ K.edges
  simp only [map_mul, Q.subgroupHom_val]

end CayleySubgraphSpec
end ABO
end PSTSEPPA
