import PSTSEPPA.ABO.LabelledQuotientSkeletonPullback
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# A connected labelled Cayley-cover morphism is a left-translated quotient map

Suppose a generator-preserving labelled group quotient Q : H ↠ Γ
and two TRUE incomplete A-Cayley skeletons L in H and K in Γ
are given, together with an actual labelled-graph morphism
f : L → K (preserving signed directed edge tokens).

For ANY realised signed path from x to y in L, its endpoints
must satisfy an exact group-coordinate equation:

   f(y) = f(x) · Q(x)⁻¹ · Q(y).

This is NOT merely a setwise coset condition: it arises from the
SAME original signed word, mapped simultaneously through the
graph morphism and the quotient's group homomorphism.

Consequently the translation displacement f(z)·Q(z)⁻¹ is
constant on each intrinsic path-component of L. In particular,
if f agrees with the canonical quotient map at one component
root then it agrees everywhere on that entire component.

This is the first source-facing uniqueness/normalization step
toward proving that all selected connected H₁-Cayley covers
occur as left translates of subsets of the canonical quotient
pullback. That larger universality theorem, and the exact
source Y₁/Z₁ catalogue, are NOT claimed here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι H Γ : Type*} [Fintype ι] [DecidableEq ι]
variable [Group H] [Group Γ]
variable {genH : ι → H} {genΓ : ι → Γ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

variable (L : CayleySubgraphSpec genH A)
variable (K : CayleySubgraphSpec genΓ A)
variable (Q : LabelledGroupQuotient genH genΓ)

variable
  (f : LabelledGraphHom
    (L.toEGraph).toLabelledGraph
    (K.toEGraph).toLabelledGraph)

/-- Exact group-coordinate relation forced by a TRUE signed
path in the incomplete H-Cayley skeleton and its actual
label-preserving graph morphism to K. The path need not use
all A, and inverse letters and loops are permitted. -/
theorem labelledHom_vertex_eq_leftTranslate_on_path
    {u v : L.Vertex} {w : LabelWord ι}
    (hp : (L.toEGraph).Follows u w v) :
    (f.onVertex v).1 =
      (f.onVertex u).1 * (Q.hom u.1)⁻¹ * Q.hom v.1 := by
  have hpK :
      (K.toEGraph).Follows (f.onVertex u) w (f.onVertex v) :=
    hp.map f
  have hpΓ :
      (cayleyGraph genΓ).toEGraph.Follows
        (f.onVertex u).1 w (f.onVertex v).1 :=
    hpK.map K.inclusion
  have hpH :
      (cayleyGraph genH).toEGraph.Follows u.1 w v.1 :=
    hp.map L.inclusion
  have hF :
      (f.onVertex u).1 * PSTS.SignedWord.evalGroup genΓ w =
        (f.onVertex v).1 := by
    have hCanonical :=
      (cayleyGraph genΓ).follows_followWord (f.onVertex u).1 w
    have hEnd :=
      (cayleyGraph genΓ).toEGraph.follows_right_unique
        hCanonical hpΓ
    rw [cayleyGraph.followWord_eq_mul_evalGroup] at hEnd
    exact hEnd
  have hH :
      u.1 * PSTS.SignedWord.evalGroup genH w = v.1 := by
    have hCanonical := (cayleyGraph genH).follows_followWord u.1 w
    have hEnd :=
      (cayleyGraph genH).toEGraph.follows_right_unique
        hCanonical hpH
    rw [cayleyGraph.followWord_eq_mul_evalGroup] at hEnd
    exact hEnd
  have hQ :
      Q.hom u.1 * PSTS.SignedWord.evalGroup genΓ w = Q.hom v.1 := by
    have hMapped := congrArg Q.hom hH
    rw [map_mul, Q.map_evalGroup] at hMapped
    exact hMapped
  have hEval :
      PSTS.SignedWord.evalGroup genΓ w =
        (Q.hom u.1)⁻¹ * Q.hom v.1 := by
    have h :=
      congrArg (fun z : Γ => (Q.hom u.1)⁻¹ * z) hQ
    simpa [mul_assoc] using h
  calc
    (f.onVertex v).1 =
        (f.onVertex u).1 * PSTS.SignedWord.evalGroup genΓ w :=
      hF.symm
    _ = (f.onVertex u).1 * ((Q.hom u.1)⁻¹ * Q.hom v.1) := by
      rw [hEval]
    _ = (f.onVertex u).1 * (Q.hom u.1)⁻¹ * Q.hom v.1 := by
      simp only [mul_assoc]

/-- On each ACTUAL intrinsic C-path component, the value of f
is obtained from Q by a single left group translation depending
only on the component's chosen root. -/
theorem labelledHom_vertex_eq_leftTranslate_on_component
    (C : Finset ι)
    (root y : L.Vertex)
    (hreach : L.SubalphabetReachable C root y) :
    (f.onVertex y).1 =
      (f.onVertex root).1 * (Q.hom root.1)⁻¹ * Q.hom y.1 := by
  obtain ⟨w, _hw, hpath⟩ := hreach
  exact L.labelledHom_vertex_eq_leftTranslate_on_path K Q f hpath

/-- A cover morphism which agrees with Q at ONE old root has
exactly Q's group coordinate on its ENTIRE intrinsic connected
component. The graph may be incomplete or disconnected globally. -/
theorem labelledHom_eq_quotient_on_component
    (C : Finset ι) (root y : L.Vertex)
    (hroot : (f.onVertex root).1 = Q.hom root.1)
    (hreach : L.SubalphabetReachable C root y) :
    (f.onVertex y).1 = Q.hom y.1 := by
  have h :=
    L.labelledHom_vertex_eq_leftTranslate_on_component
      K Q f C root y hreach
  simpa [hroot, mul_assoc] using h

end CayleySubgraphSpec
end ABO
end PSTSEPPA
