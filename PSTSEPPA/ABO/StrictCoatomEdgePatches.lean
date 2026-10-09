import PSTSEPPA.ABO.NoLargeCoatomSupport
import PSTSEPPA.ABO.CoatomEdgeCover
import PSTSEPPA.ABO.MultiCosetSelectedComponentExact

/-!
# Every lower-branch B-edge lies inside a strict coatom patch

At ambient rank |A|>=2, we can simultaneously use:

* exact coatom coverage of *all signed edge tokens* (#200);
* invariance of support by any coatom C⊇B along actual B-paths (#181);
* the root-level no-large-coatom support test (#198);
* exact complete-coset preservation of intrinsic component tags (#153).

Consequently every B-labelled edge of the entire B-component rooted
at a point without larger/equal coatom support belongs to a genuine
completed coatom C-copy with **C∩B⊊B**. Its target is still in the
SAME C-component tag. Both endpoints and the directed edge token
are actual points/edges of the glued EGraph; no global injectivity
of ambient Cayley coordinates is used.

This is a graph-level, rank-reducing patch cover. It does NOT establish
the missing common core or the assembled whole-component cluster property.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- In the no-large-coatom branch of the full proper-family extension,
every B-labelled edge at a B-reachable vertex is realised in a single
completed codimension-one C-coset with strict C∩B⊊B. Furthermore its
target lies in the very same tagged C-copy; this is stronger than a
statement about the edge's Cayley projection. -/
theorem allProperCoset_B_component_strict_coatom_edge_patches
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 2 ≤ A.card)
    (B : Finset ι)
    (z : K.MultiCosetVertex (allProperCosetFamily A) hadm hgen hret)
    (hNoCo :
      ∀ (C : Finset ι)
        (hCP : C ∈ (allProperCosetFamily A).alphabets),
        C.card + 1 = A.card →
        B ⊆ C →
        ¬ K.MultiCosetVertexSupported
          (allProperCosetFamily A) hadm hgen hret C z)
    (y : K.MultiCosetVertex (allProperCosetFamily A) hadm hgen hret)
    (hzy : ∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).Follows z w y)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (heSource :
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).source e = y)
    (heB :
      signedBase
        ((K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).label e) ∈ B) :
    ∃ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (p q : K.AttachedCosetVertex C)
      (s : {s : SignedLabel ι // signedBase s ∈ C}),
      C.card + 1 = A.card ∧
      (C ∩ B) ⊂ B ∧
      signedBase s.1 ∈ C ∩ B ∧
      q.1 = p.1 ∧
      e = K.multiCosetEdgeInclude
        (allProperCosetFamily A) hadm hgen hret C hCP
        (Sum.inr (p, s)) ∧
      (K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).target e =
        K.multiCosetInclude
          (allProperCosetFamily A) hadm hgen hret C hCP q := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨C, hCP, p, s, hCard, he⟩ :=
    K.allProperCosetEdge_exists_coatom_completed_presentation
      hadm hgen hret hAcard e
  have hsrc :
      G.source e = K.multiCosetInclude P hadm hgen hret C hCP p := by
    rw [← he]
    rfl
  have hSuppY :
      K.MultiCosetVertexSupported P hadm hgen hret C y :=
    ⟨hCP, p, hsrc.symm.trans heSource⟩
  have hNotBC : ¬ B ⊆ C := by
    intro hBC
    exact hNoCo C hCP hCard hBC
      ((K.multiCoset_selected_superset_support_invariant
        P hadm hgen hret B C hBC z y hzy).mpr hSuppY)
  have hStrict : C ∩ B ⊂ B := by
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro hBInter
    apply hNotBC
    intro a ha
    exact (Finset.mem_inter.mp (hBInter ha)).1
  have hsB : signedBase s.1 ∈ B := by
    rw [← he] at heB
    exact heB
  have hsCB : signedBase s.1 ∈ C ∩ B :=
    Finset.mem_inter.mpr ⟨s.2, hsB⟩
  have hsC : signedBase (G.label e) ∈ C := by
    rw [← he]
    exact s.2
  obtain ⟨q, hTag, hTarget⟩ :=
    K.multiCoset_selected_B_step_stays_in_coset
      P hadm hgen hret C hCP p e hsrc hsC
  exact ⟨C, hCP, p, q, s, hCard, hStrict, hsCB,
    hTag, he.symm, hTarget⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
