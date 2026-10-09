import PSTSEPPA.ABO.MultiCosetSkeletonComponentIntersections
import PSTSEPPA.ABO.Stability

/-!
# Corrected ABO Lemma 5.6: selected-coset path reconstruction and stable G-values

The audited Lemma 5.6 has a decisive group-value subtlety.
The replacement q is first obtained as a B-labelled path in the
H_k-skeleton; it must have the same value as the competing B-word r
in the FINAL group G, not merely in the intermediate group H_k.

This module proves the corresponding source-exact, reusable bridge:

* In any E-graph admitting a labelled homomorphism into the complete
  Cayley graph of H, two genuine paths with the same start and end
  have equal evaluated H group values. No injectivity of the graph
  homomorphism is required.
* If a B-word r connects two embedded original skeleton vertices
  in the **selected complete B-coset constituent** of a multi-coset
  extension, the already checked A2 path-reflection theorem yields
  an actual B-path q between the original skeleton vertices.
* As q and r have the same endpoints in the multi-extension,
  the preceding Cayley argument gives [q]_H = [r]_H.
* If G -> H is k-stable and |B| <= k, then [q]_G = [r]_G.

These conclusions are proved without assuming a global injective
map from the multi-CE into the Cayley group. The missing Section 5
work is to build the finite intermediate H_k, the correct skeleton
and the projection from the final G-path to this selected extension;
those are NOT supplied by this conditional bridge.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ V Edge : Type*}

namespace EGraph

/-- Two realised words from one vertex to another have equal
group values whenever the labelled E-graph maps into a complete
Cayley graph. The map need NOT be injective: both paths have
the same target before mapping.

This is the precise group-coordinate argument needed when
following two paths in a coset extension. -/
theorem equal_groupValues_of_shared_endpoints_in_cayley
    [Group Δ]
    (K : EGraph V Edge ι) (gen : ι → Δ)
    (f : LabelledGraphHom
      K.toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph)
    (x y : V) (p q : LabelWord ι)
    (hp : K.Follows x p y)
    (hq : K.Follows x q y) :
    PSTS.SignedWord.evalGroup gen p =
      PSTS.SignedWord.evalGroup gen q := by
  have hpMapped :
      (cayleyGraph gen).toEGraph.Follows
        (f.onVertex x) p (f.onVertex y) :=
    hp.map f
  have hqMapped :
      (cayleyGraph gen).toEGraph.Follows
        (f.onVertex x) q (f.onVertex y) :=
    hq.map f
  have hpEnd :
      (cayleyGraph gen).followWord (f.onVertex x) p =
        f.onVertex y :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord (f.onVertex x) p)
      hpMapped
  have hqEnd :
      (cayleyGraph gen).followWord (f.onVertex x) q =
        f.onVertex y :=
    (cayleyGraph gen).toEGraph.follows_right_unique
      ((cayleyGraph gen).follows_followWord (f.onVertex x) q)
      hqMapped
  have hValues :
      f.onVertex x * PSTS.SignedWord.evalGroup gen p =
        f.onVertex x * PSTS.SignedWord.evalGroup gen q := by
    calc
      f.onVertex x * PSTS.SignedWord.evalGroup gen p =
          (cayleyGraph gen).followWord (f.onVertex x) p :=
        (cayleyGraph.followWord_eq_mul_evalGroup gen (f.onVertex x) p).symm
      _ = f.onVertex y := hpEnd
      _ = (cayleyGraph gen).followWord (f.onVertex x) q := hqEnd.symm
      _ = f.onVertex x * PSTS.SignedWord.evalGroup gen q :=
        cayleyGraph.followWord_eq_mul_evalGroup gen (f.onVertex x) q
  exact mul_left_cancel hValues

end EGraph

variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec genΔ A)

/-- The key already-available A2-to-A3 bridge of the *geometric*
part of corrected Lemma 5.6.

A B-word r which is realised between two embedded skeleton
vertices in the complete multi-coset extension can be
replaced by an actual B-path q in K. The values q,r are equal
in H=Δ because the two CE paths share start and endpoint,
even if the CE ambient-coordinate morphism is non-injective.

If the labelled quotient G=Γ -> H=Δ is k-stable and B has at
most k generators, then q and r have equal values ALREADY IN
THE FINAL G, as required in audited Lemma 5.6. -/
theorem selected_coset_path_replacement_final_value
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated genΔ) (hret : Retractable genΔ)
    (k : ℕ) (hStable : Q.KStable k)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (hBcard : B.card ≤ k)
    (x y : K.Vertex)
    (r : LabelWord ι)
    (hrUses : LabelWord.Uses B r)
    (hrPath :
      (K.multiCosetEGraph P hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom
          P hadm hgen hret B hBP).onVertex x)
        r
        ((K.skeletonToMultiCosetHom
          P hadm hgen hret B hBP).onVertex y)) :
    ∃ q : LabelWord ι,
      LabelWord.Uses B q ∧
      (K.toEGraph).Follows x q y ∧
      PSTS.SignedWord.evalGroup genΓ q =
        PSTS.SignedWord.evalGroup genΓ r := by
  let CE := K.multiCosetEGraph P hadm hgen hret
  let inclusion :=
    K.skeletonToMultiCosetHom P hadm hgen hret B hBP
  obtain ⟨q, hqUses, hqPath⟩ :=
    (K.multiCoset_selected_skeleton_B_reachable_iff
      P hadm hgen hret B hBP x y).mp
      ⟨r, hrUses, hrPath⟩
  have hqCE :
      CE.Follows (inclusion.onVertex x) q
        (inclusion.onVertex y) := by
    exact hqPath.map inclusion
  have hValueDown :
      PSTS.SignedWord.evalGroup genΔ q =
        PSTS.SignedWord.evalGroup genΔ r :=
    CE.equal_groupValues_of_shared_endpoints_in_cayley
      genΔ (K.multiCosetAmbientHom P hadm hgen hret)
      (inclusion.onVertex x) (inclusion.onVertex y)
      q r hqCE hrPath
  have hValueFinal :
      PSTS.SignedWord.evalGroup genΓ q =
        PSTS.SignedWord.evalGroup genΓ r :=
    Q.evalGroup_eq_of_stableAt (hStable B hBcard)
      hqUses hrUses hValueDown
  exact ⟨q, hqUses, hqPath, hValueFinal⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
