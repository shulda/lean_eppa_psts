import PSTSEPPA.ABO.SingleCosetEGraph

/-!
# No B-path crosses between tagged B-coset copies

The graph CE(G,K;B) retains old skeleton edges only for labels outside B.
Every B-labelled edge is therefore an edge inside a single attached
component-indexed full B-coset, and its endpoints have the same tag.

By induction, every actual B-labelled path preserves that tag. Together
with the converse connectedness theorem, this identifies the intrinsic
B-components of CE(G,K;B) exactly as its attached B-coset copies.
No ambient-coset injectivity is needed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every B-labelled edge in CE(G,K;B) preserves its component index.
An outside-B skeleton edge cannot have such a label. -/
theorem singleCosetEGraph_B_edge_preserves_index
    (B : Finset ι) (e : K.SingleCosetEdge B)
    (he : signedBase ((K.singleCosetEGraph B).label e) ∈ B) :
    ((K.singleCosetEGraph B).source e).1 =
      ((K.singleCosetEGraph B).target e).1 := by
  cases e with
  | inl e =>
      have hbad : signedBase e.1.1.2 ∈ B := he
      exact (e.2 hbad).elim
  | inr e =>
      rfl

/-- A realised B-word path in the single-B coset extension cannot cross
between different component-indexed copies. -/
theorem singleCosetEGraph_follows_B_preserves_index
    (B : Finset ι)
    {p q : K.AttachedCosetVertex B} {w : LabelWord ι}
    (hpath : (K.singleCosetEGraph B).Follows p w q)
    (hw : LabelWord.Uses B w) :
    p.1 = q.1 := by
  induction hpath generalizing hw with
  | nil u =>
      rfl
  | @cons u v s w e hs hl hrest ih =>
      have hletter :
          signedBase ((K.singleCosetEGraph B).label e) ∈ B := by
        rw [hl]
        exact hw.1
      have hstep :=
        K.singleCosetEGraph_B_edge_preserves_index B e hletter
      calc
        u.1 = ((K.singleCosetEGraph B).source e).1 :=
          congrArg (fun t : K.AttachedCosetVertex B => t.1) hs.symm
        _ = ((K.singleCosetEGraph B).target e).1 := hstep
        _ = v.1 := ih hw.2

end CayleySubgraphSpec
end ABO
end PSTSEPPA
