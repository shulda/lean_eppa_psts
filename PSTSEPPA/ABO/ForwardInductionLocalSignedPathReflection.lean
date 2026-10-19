import PSTSEPPA.ABO.IntrinsicComponentLocalSliceIso
import PSTSEPPA.ABO.LocalSubalphabetGeneratedRetractable
import PSTSEPPA.ABO.BijectiveComponentIndexTransport

/-!
# Actual source-to-local component transport for ABO forward induction

ABO Theorem 4.5 works inside the TRUE subgroup H[C], not
an arbitrary globally retractable ambient H. The previously
certified developments already establish:

* `IntrinsicComponentLocalSliceIso`: the ORIGINAL intrinsic
  C-component of an INCOMPLETE signed Cayley skeleton and its
  root-normalized local skeleton over H[C] are bijectively
  isomorphic on VERTICES and actual ORIENTED SIGNED EDGE TOKENS.
* `BijectiveGraphPathReflection`: such morphisms preserve and
  reflect every GENUINELY REALISED signed word path.
* `BijectiveComponentIndexTransport`: for every alphabet D,
  their quotients of intrinsic D-components are equivalent
  and these equivalences COMMUTE with D⊆E enlargement.
* `LocalSubalphabetGeneratedRetractable`: when H is k-retractable
  and |C|≤k, the actual H[C] with labels outside C trivial
  is generated and GLOBALLY retractable.

This file does NOT reprove any of those generic facts.
It specializes them to the EXACT normalized rooted source
C-component and packages the data required by the published
forward/upward induction construction, including both formal
inverse edge tokens and actual signed reachability.

Still OPEN IN LEAN: extending this signed old-skeleton
isomorphism to the original COMPONENT-TAGGED FULL PROPER
COSET-EXTENSION quotients with their actual attached
coset fibres; that is a separate source naturality gate.
No equality of ambient group coordinates is used to
identify distinct original component tags.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An actual oriented signed path in the original incomplete
rooted C-component is realised iff its root-normalized
local H[C]-skeleton realises the SAME signed word.

This is NOT completeness of either skeleton. -/
theorem intrinsicComponentLocalHom_follows_iff
    (C : Finset ι) (root : K.Vertex)
    (u v : (K.intrinsicComponentLocalSlice C root).Vertex)
    (w : LabelWord ι) :
    ((K.subalphabetComponentSubgraph C root).toEGraph).Follows
      ((K.intrinsicComponentLocalHom C root).onVertex u)
      w
      ((K.intrinsicComponentLocalHom C root).onVertex v) ↔
    ((K.intrinsicComponentLocalSlice C root).toEGraph).Follows
      u w v := by
  have hBij := K.intrinsicComponentLocalHom_bijective C root
  exact (EGraph.follows_iff_bijective
      (G := (K.intrinsicComponentLocalSlice C root).toEGraph)
      (H := (K.subalphabetComponentSubgraph C root).toEGraph)
      (K.intrinsicComponentLocalHom C root)
      hBij.1 hBij.2 u v w).symm

/-- The intrinsic signed D-path component relation is
preserved AND reflected by root localization, for
EVERY D (in particular each D⊆C and D=∅).
The words and their formal signed inverses stay literal. -/
theorem intrinsicComponentLocalHom_reachable_iff
    (C D : Finset ι) (root : K.Vertex)
    (u v : (K.intrinsicComponentLocalSlice C root).Vertex) :
    (K.subalphabetComponentSubgraph C root).SubalphabetReachable D
      ((K.intrinsicComponentLocalHom C root).onVertex u)
      ((K.intrinsicComponentLocalHom C root).onVertex v) ↔
    (K.intrinsicComponentLocalSlice C root).SubalphabetReachable D
      u v := by
  constructor
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw,
      (K.intrinsicComponentLocalHom_follows_iff C root u v w).mp hp⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨w, hw,
      (K.intrinsicComponentLocalHom_follows_iff C root u v w).mpr hp⟩

/-- Canonical equivalence between ACTUAL D-component quotient
TAGS of the local H[C]-skeleton and the original rooted
intrinsic C-component. This is defined by the signed
vertex-and-edge isomorphism, not by ambient Γ coordinates. -/
noncomputable def intrinsicComponentLocalIndexEquiv
    (C D : Finset ι) (root : K.Vertex) :
    (K.intrinsicComponentLocalSlice C root).ComponentIndex D ≃
    (K.subalphabetComponentSubgraph C root).ComponentIndex D :=
  (K.intrinsicComponentLocalSlice C root).componentIndexEquiv_of_graphIso
    (K.subalphabetComponentSubgraph C root)
    (K.intrinsicComponentLocalHom C root)
    (K.intrinsicComponentLocalHom_bijective C root).1
    (K.intrinsicComponentLocalHom_bijective C root).2 D

/-- Compatibility of the ACTUAL original/local component tag
equivalences with every original alphabet inclusion D⊆E.
This is exactly what source coset-gluing intersection
naturality (3.10)/(3.11) later requires. -/
theorem intrinsicComponentLocalIndexEquiv_natural
    (C D E : Finset ι) (root : K.Vertex)
    (hDE : D ⊆ E)
    (d : (K.intrinsicComponentLocalSlice C root).ComponentIndex D) :
    (K.subalphabetComponentSubgraph C root).componentIndexMap
      D E hDE (K.intrinsicComponentLocalIndexEquiv C D root d) =
    K.intrinsicComponentLocalIndexEquiv C E root
      ((K.intrinsicComponentLocalSlice C root).componentIndexMap
        D E hDE d) := by
  exact
    (K.intrinsicComponentLocalSlice C root).componentIndexEquiv_of_graphIso_natural
      (K.subalphabetComponentSubgraph C root)
      (K.intrinsicComponentLocalHom C root)
      (K.intrinsicComponentLocalHom_bijective C root).1
      (K.intrinsicComponentLocalHom_bijective C root).2
      D E hDE d

/-- The local H[C] group and the original intrinsic
C-component are usable together in the forward induction:
the local signed labels generate, the local group is
globally retractable, and the true old source/local signed
graph morphism is bijective on BOTH directed edges and vertices.

A LOCAL GROUP/SKELETON statement, not an unproved multiCE
quotient transport. -/
theorem intrinsicComponent_local_algebra_and_signed_iso
    (k : ℕ) (hret : KRetractable gen k)
    (C : Finset ι) (hC : C.card ≤ k)
    (root : K.Vertex) :
    (IsGenerated (trivialCompletionGenerator gen C) ∧
      Retractable (trivialCompletionGenerator gen C)) ∧
    (Function.Bijective
       (K.intrinsicComponentLocalHom C root).onVertex ∧
     Function.Bijective
       (K.intrinsicComponentLocalHom C root).onEdge) := by
  exact ⟨generated_and_retractable_local_subalphabet
    gen k hret C hC,
    K.intrinsicComponentLocalHom_bijective C root⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
