import PSTSEPPA.ABO.MultiCosetParentPathInvariant
import PSTSEPPA.ABO.MultiCosetMorphismsUnique
import PSTSEPPA.ABO.CayleySubgraphComponents

/-!
# Exact intrinsic B-components of a lower-alphabet multi-coset extension

Let P be a family of selected coset alphabets all lying inside B.
The checked parent-fold homomorphism shows that an actual B-labelled
path in CE(G,K;P) preserves the intrinsic B-component tag.

Conversely each vertex of the multi-CE admits a path with labels
inside its own constituent alphabet from a literal old skeleton point.
If two quotient points have the same parent B-tag, their respective
skeleton anchors are B-connected in K. Transport that old B-path
through the skeleton inclusion, concatenate with the two constituent
attachment paths, and obtain a genuine B-path in the multi-CE.

Thus the intrinsic B-path components are exactly the fibres of the
parent B-component index. Ambient B-coset equality is never substituted
for actual path reachability.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Strengthening the ambient-accessibility lemma: the connecting
word from an old skeleton point to a coset point uses only the
alphabet of the chosen coset constituent. -/
theorem multiCosetVertex_accessible_from_skeleton_uses
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex P hadm hgen hret) :
    ∃ (C : Finset ι) (hCP : C ∈ P.alphabets)
      (x : K.Vertex) (w : LabelWord ι),
      LabelWord.Uses C w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows
        ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x)
        w z := by
  induction z using Quotient.inductionOn with
  | h raw =>
      rcases raw with ⟨C, p⟩
      obtain ⟨x, hx⟩ := K.componentClass_surjective C.1 p.1
      obtain ⟨w, hw, hpath⟩ :=
        K.singleCosetEGraph_connected_on_index
          C.1 (K.attachedOfSkeletonVertex C.1 x) p hx
      exact ⟨C.1, C.2, x, w, hw,
        hpath.map (K.singleCosetToMultiHom
          P hadm hgen hret C.1 C.2)⟩

/-- Every original skeleton vertex acquires its original B-component
index under the multi-CE folding map, independently of the constituent
alphabet through which the skeleton point was included. -/
theorem multiCosetVertexToParent_skeleton
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (x : K.Vertex) :
    K.multiCosetVertexToParent P hadm hgen hret B hPsub
      ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x) =
        K.attachedOfSkeletonVertex B x := by
  change
    K.attachedSubalphabetMap C B (hPsub C hCP)
      (K.attachedOfSkeletonVertex C x) =
      K.attachedOfSkeletonVertex B x
  exact K.attachedSubalphabetMap_ofSkeletonVertex
    C B (hPsub C hCP) x

/-- Full B-component classification for multi-coset extensions all
of whose attached alphabets lie inside B. This includes nested,
equal and empty selected alphabets, and needs no choice of an ambient
B-coset representative. -/
theorem multiCosetEGraph_B_reachable_iff_parent_index
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (p q : K.MultiCosetVertex P hadm hgen hret) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph P hadm hgen hret).Follows p w q) ↔
      (K.multiCosetVertexToParent P hadm hgen hret B hPsub p).1 =
      (K.multiCosetVertexToParent P hadm hgen hret B hPsub q).1 := by
  constructor
  · rintro ⟨w, hw, hpq⟩
    exact K.multiCoset_follows_parent_B_index
      P hadm hgen hret B hPsub hpq hw
  · intro hpqIndex
    let G := K.multiCosetEGraph P hadm hgen hret
    obtain ⟨C, hCP, x, wx, hwx, hpx⟩ :=
      K.multiCosetVertex_accessible_from_skeleton_uses
        P hadm hgen hret p
    obtain ⟨D, hDP, y, wy, hwy, hpy⟩ :=
      K.multiCosetVertex_accessible_from_skeleton_uses
        P hadm hgen hret q
    have hxB :
        K.componentClass B x =
          (K.multiCosetVertexToParent P hadm hgen hret B hPsub p).1 := by
      calc
        K.componentClass B x =
          (K.multiCosetVertexToParent P hadm hgen hret B hPsub
            ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x)).1 := by
              rw [K.multiCosetVertexToParent_skeleton]
              rfl
        _ = (K.multiCosetVertexToParent P hadm hgen hret B hPsub p).1 :=
          K.multiCoset_follows_parent_B_index
            P hadm hgen hret B hPsub hpx
            (hwx.mono (hPsub C hCP))
    have hyB :
        K.componentClass B y =
          (K.multiCosetVertexToParent P hadm hgen hret B hPsub q).1 := by
      calc
        K.componentClass B y =
          (K.multiCosetVertexToParent P hadm hgen hret B hPsub
            ((K.skeletonToMultiCosetHom P hadm hgen hret D hDP).onVertex y)).1 := by
              rw [K.multiCosetVertexToParent_skeleton]
              rfl
        _ = (K.multiCosetVertexToParent P hadm hgen hret B hPsub q).1 :=
          K.multiCoset_follows_parent_B_index
            P hadm hgen hret B hPsub hpy
            (hwy.mono (hPsub D hDP))
    have hxyB : K.SubalphabetReachable B x y :=
      (K.componentClass_eq_iff B x y).mp
        (hxB.trans (hpqIndex.trans hyB.symm))
    obtain ⟨w, hw, hpath⟩ := hxyB
    have hmiddle :
        G.Follows
          ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x)
          w
          ((K.skeletonToMultiCosetHom P hadm hgen hret D hDP).onVertex y) := by
      have hm := hpath.map
        (K.skeletonToMultiCosetHom P hadm hgen hret C hCP)
      rw [K.skeletonToMultiCosetHom_vertex_independent
        P hadm hgen hret C D hCP hDP y] at hm
      exact hm
    have hback : G.Follows p (PSTS.SignedWord.inv wx)
        ((K.skeletonToMultiCosetHom P hadm hgen hret C hCP).onVertex x) :=
      G.follows_inverse hpx
    have hwhole : G.Follows p (PSTS.SignedWord.inv wx ++ w ++ wy) q := by
      simpa only [List.append_assoc] using
        (G.follows_append (G.follows_append hback hmiddle) hpy)
    refine ⟨PSTS.SignedWord.inv wx ++ w ++ wy, ?_, hwhole⟩
    exact (LabelWord.uses_append B _ _).2
      ⟨(LabelWord.uses_append B _ _).2
          ⟨(hwx.mono (hPsub C hCP)).inv, hw⟩,
        hwy.mono (hPsub D hDP)⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
