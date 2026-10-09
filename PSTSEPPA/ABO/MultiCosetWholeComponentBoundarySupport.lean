import PSTSEPPA.ABO.MultiCosetMaximalConstituentPathExit
import PSTSEPPA.ABO.MultiCosetComponentSupportDichotomy

/-!
# Whole B-component boundary support inside a maximal constituent

The proof of ABO Lemma 4.3 begins with the following component-level
claim. If a genuine B-component intersects a selected maximal
C-constituent but is NOT contained in that one tagged C-copy, then
the intersection with C contains a vertex supported by a strictly
smaller alphabet D⊊C.

The previously certified first-exit theorem works with a concrete
B-path starting in C. To obtain the source-facing assertion, take
a B-path from the chosen C-point to a component root z, then a
second B-path from z to a vertex outside the C-copy. Concatenate.
The first-exit theorem provides a boundary point in that C-tag
with a smaller support. Reversing the initial path connects
this boundary point to the component root as required.

This theorem does not use a cluster-property assumption,
bridge-freeness, or ambient Cayley injectivity. The chosen C-copy
has its specific intrinsic component tag throughout; the union
of all copies labelled C would be insufficient.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- If the true B-component of z meets a specific maximal
tagged C-copy but contains a point outside it, then
its intersection with that same C-copy has a vertex
supported over some strict D⊊C. Both reachability statements
are given by realised B-words in the multi-CE EGraph. -/
theorem allProperCoset_B_component_maximal_C_boundary_support
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (hCnonempty : C.Nonempty)
    (hMax :
      ∀ (E : Finset ι)
        (hEP : E ∈ (allProperCosetFamily A).alphabets),
        C ⊆ E → E = C)
    (p : K.AttachedCosetVertex C)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hMeet :
      ∃ u : LabelWord ι, LabelWord.Uses B u ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows
          (K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP p) u z)
    (hNotContained :
      ∃ (y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret)
        (w : LabelWord ι),
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows z w y ∧
        ¬ ∃ q : K.AttachedCosetVertex C,
          q.1 = p.1 ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP q) :
    ∃ x : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret,
      (∃ q : K.AttachedCosetVertex C,
        q.1 = p.1 ∧
        x = K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret C hCP q) ∧
      (∃ u : LabelWord ι, LabelWord.Uses B u ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows z u x) ∧
      ∃ D : Finset ι,
        D ⊂ C ∧
        K.MultiCosetVertexSupported
          (allProperCosetFamily A) hadm hgen hret D x := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨u, hu, hPZ⟩ := hMeet
  obtain ⟨y, w, hw, hZY, hOutside⟩ := hNotContained
  have hPY : G.Follows
      (K.multiCosetInclude P hadm hgen hret C hCP p)
      (u ++ w) y :=
    G.follows_append hPZ hZY
  obtain ⟨x, hxCopy, ⟨pref, hPref, hPX⟩,
      D, hD, hDsupport⟩ :=
    K.allProperCoset_maximal_constituent_path_exit_lower
      hadm hgen hret B C hCP hCnonempty hMax
      p y hOutside
      ⟨u ++ w, (LabelWord.uses_append B u w).2
        ⟨hu, hw⟩, hPY⟩
  have hZX : G.Follows z
      (PSTS.SignedWord.inv u ++ pref) x :=
    G.follows_append (G.follows_inverse hPZ) hPX
  have hUses : LabelWord.Uses B
      (PSTS.SignedWord.inv u ++ pref) :=
    (LabelWord.uses_append B (PSTS.SignedWord.inv u) pref).2
      ⟨hu.inv, hPref⟩
  exact ⟨x, hxCopy,
    ⟨PSTS.SignedWord.inv u ++ pref, hUses, hZX⟩,
    D, hD, hDsupport⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
