import PSTSEPPA.ABO.ForwardInductionLocalTaggedCosetBackward

/-!
# ABO Theorem 4.5: a bijection of ACTUAL attached D-coset fibres

The accepted old signed skeleton localization and original
D-component-index equivalence provide only the OLD graph data.
The preceding forward/backward constituent lemmas identify the
entire newly attached full D-coset membership, D⊆C, under
normalization at one genuine original root.

We package those exact membership facts as an explicit bijection
between the local and ambient FULL constituent point fibres for
EACH genuine original component tag c. The map is ordinary
root-left-translation on the local group element; it is injective
because left multiplication is cancellative and surjective by
the certified local backward lift x = root^{-1} y. Both sides
are properly *component-tagged* by c and the existing genuine
signed D-component-index equivalence.

This is precisely the constituent FIBRE bijectivity used when
the published ABO forward induction identifies its lower
C-stage coset extension with one from the genuine group H[C].

The theorem is restricted to selected D⊆C, rather than
mistakenly attempting an equivalence on labels outside C.
Remaining gluing naturality under D⊆E and actual signed
edge token transport to the entire coset-extension quotient
are the next independent gates. No global ambient Γ
retractability, imaginary old edge, new axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- For any TRUE local D-component index c, the COMPLETE
attached local D-coset fibre is in explicit bijection with
the COMPLETE original rooted D-coset fibre with the
CORRESPONDING ORIGINAL intrinsic D-component tag.

Both sides contain new attached points not necessarily in
the corresponding incomplete old skeleton. Their
coordinates are mapped by left translation at the genuine
original old root, and not by arbitrary ambient projection. -/
noncomputable def intrinsicComponentLocalAttachedCosetFibreEquiv
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex)
    (c : (K.intrinsicComponentLocalSlice C root).ComponentIndex D) :
    { v : generatedSubgroup gen C //
        v ∈ (K.intrinsicComponentLocalSlice C root).componentAmbientCoset
          D c } ≃
    { y : Γ //
        y ∈ (K.subalphabetComponentSubgraph C root).componentAmbientCoset
          D (K.intrinsicComponentLocalIndexEquiv C D root c) } :=
  Equiv.ofBijective
    (fun v =>
      (⟨root.1 * (v.1 : Γ),
        (K.intrinsicComponentLocalIndex_ambientCoset_mem_iff
          C D hDC root c v.1).mp v.2⟩ :
        { y : Γ //
          y ∈ (K.subalphabetComponentSubgraph C root).componentAmbientCoset
            D (K.intrinsicComponentLocalIndexEquiv C D root c) }))
    (by
      constructor
      · intro v w hvw
        apply Subtype.ext
        apply Subtype.ext
        exact mul_left_cancel (congrArg Subtype.val hvw)
      · intro y
        obtain ⟨v, hvD, hvRoot⟩ :=
          K.intrinsicComponentLocal_attachedCosetBackward
            C D hDC root c y.1 y.2
        refine ⟨⟨v, hvD⟩, ?_⟩
        apply Subtype.ext
        exact hvRoot)

/-- The full new attached D-point equivalence has exactly
the translated ambient group coordinate, including
fresh points and inverse signed labels. -/
theorem intrinsicComponentLocalAttachedCosetFibreEquiv_value
    (C D : Finset ι) (hDC : D ⊆ C)
    (root : K.Vertex)
    (c : (K.intrinsicComponentLocalSlice C root).ComponentIndex D)
    (v : { x : generatedSubgroup gen C //
      x ∈ (K.intrinsicComponentLocalSlice C root).componentAmbientCoset
        D c }) :
    (K.intrinsicComponentLocalAttachedCosetFibreEquiv
      C D hDC root c v).1 = root.1 * (v.1 : Γ) :=
  rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
