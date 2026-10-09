import PSTSEPPA.ABO.CoatomFamilyPathEquivalence
import PSTSEPPA.ABO.ComponentSelectedSliceExact

/-!
# Exact component slices in the smaller coatom-only coset extension

The source's forward induction can now work entirely in the
coatom-only presentation. The previously checked exact selected-C
slice theorem concerns the full proper-subalphabet multi-CE; its
literal C-component-tagged geometry transfers across the certified
coatom/full graph isomorphism and the reflection of *actual*
signed-word paths (not just ambient Cayley values).

Fix an arbitrary B, a selected coatom C, a tagged point p of its
completed C-copy, and a global B-component root z not necessarily
inside that copy. If a genuine B-path joins p to z, the intersection
of the B-component with that specific C-tag is precisely the
completed left (B ∩ C)-coset based at p. This holds for B,C
incomparable, and does not assume bridge-freeness or the cluster
property.

Proofs transport the exact B-reachability iff through the
coatom-to-full labelled graph isomorphism, retaining the original
C-component indices. This identifies one component slice but still
does NOT assemble all coatom slices into a single common-core cluster.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- For ambient |A|≥2, the intersection of a true intrinsic
B-component of the coatom-only extension with one chosen selected
tagged C-constituent is exactly a (B∩C)-coset, with an iff of real
signed-labelled B-paths from the global root. -/
theorem coatomCoset_B_component_selected_C_slice_exact
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 2 ≤ A.card)
    (B C : Finset ι)
    (hCP : C ∈ (coatomCosetFamily A).alphabets)
    (p : K.AttachedCosetVertex C)
    (z : K.MultiCosetVertex (coatomCosetFamily A)
      hadm hgen hret)
    (hMeet :
      ∃ u : LabelWord ι, LabelWord.Uses B u ∧
        (K.multiCosetEGraph (coatomCosetFamily A)
          hadm hgen hret).Follows
          (K.multiCosetInclude (coatomCosetFamily A)
            hadm hgen hret C hCP p) u z)
    (q : K.AttachedCosetVertex C)
    (hIndex : p.1 = q.1) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph (coatomCosetFamily A)
        hadm hgen hret).Follows z w
        (K.multiCosetInclude (coatomCosetFamily A)
          hadm hgen hret C hCP q)) ↔
    q.2.1 ∈ generatedLeftCoset gen (B ∩ C) p.2.1 := by
  let P := coatomCosetFamily A
  let Q := allProperCosetFamily A
  let F := K.coatomToFullCosetHom hadm hgen hret
  have hCQ : C ∈ Q.alphabets :=
    coatomCosetFamily_subset_allProper A hCP
  have hMeetQ :
      ∃ u : LabelWord ι, LabelWord.Uses B u ∧
        (K.multiCosetEGraph Q hadm hgen hret).Follows
          (K.multiCosetInclude Q hadm hgen hret C hCQ p)
          u (F.onVertex z) := by
    obtain ⟨u, hu, hpath⟩ := hMeet
    have hmapped := hpath.map F
    change
      (K.multiCosetEGraph Q hadm hgen hret).Follows
        (K.multiCosetInclude Q hadm hgen hret C hCQ p)
        u (F.onVertex z) at hmapped
    exact ⟨u, hu, hmapped⟩
  have hSlice :=
    K.multiCoset_B_component_selected_C_slice_exact
      Q hadm hgen hret B C hCQ p (F.onVertex z)
      hMeetQ q hIndex
  constructor
  · rintro ⟨w, hw, hp⟩
    have hmapped := hp.map F
    have hpathQ :
        (K.multiCosetEGraph Q hadm hgen hret).Follows
          (F.onVertex z) w
          (K.multiCosetInclude Q hadm hgen hret C hCQ q) := by
      change
        (K.multiCosetEGraph Q hadm hgen hret).Follows
          (F.onVertex z) w
          (K.multiCosetInclude Q hadm hgen hret C hCQ q)
        at hmapped
      exact hmapped
    exact hSlice.mp ⟨w, hw, hpathQ⟩
  · intro hCoset
    obtain ⟨w, hw, hpathQ⟩ := hSlice.mpr hCoset
    have hpathP :
        (K.multiCosetEGraph P hadm hgen hret).Follows
          z w
          (K.multiCosetInclude P hadm hgen hret C hCP q) := by
      apply (K.coatomToFullCosetHom_follows_iff
        hadm hgen hret hAcard z
        (K.multiCosetInclude P hadm hgen hret C hCP q) w).mpr
      change
        (K.multiCosetEGraph Q hadm hgen hret).Follows
          (F.onVertex z) w
          (K.multiCosetInclude Q hadm hgen hret C hCQ q)
      exact hpathQ
    exact ⟨w, hw, hpathP⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
