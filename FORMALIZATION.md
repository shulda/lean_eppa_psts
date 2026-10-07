# Formalization status

This file is the live map from the mathematical proof plan to Lean.
A statement is called **Formalized** only after the corresponding declaration
is on `main` and GitHub Actions is green.

**Status meanings**

- **API formalized** — definitions compile and are used by later files.
- **Formalized** — theorem and proof are checked by Lean on green `main`.
- **Current target** — active work frontier.
- **Planned** — intentionally not opened yet.

| Mathematical item / gate | Lean declaration / file | Status | Notes |
| --- | --- | --- | --- |
| Repository / CI bootstrap | `PSTSEPPA.lean`, `.github/workflows/lean.yml` | **Formalized** | Lean/mathlib 4.34.1; full build and axiom audit are green. |
| T0: PSTS basic API | `PSTSEPPA/PSTS/Basic.lean` | **API formalized** | `Option`-valued partial operation; diagonal is total; symmetry plus one companion identity, with the other derived. |
| T0: closed subsets / induced systems | `PSTSEPPA/PSTS/Closed.lean` | **API formalized** | Closed sets are closed under defined operation values; restriction to a closed subtype is a PSTS. |
| T0: partial automorphisms | `PSTSEPPA/PSTS/PartialAut.lean` | **API formalized** | Uses option-valued `PEquiv`; source/target are closed; inverse and composition are checked. Composition means first `p`, then `q`, matching `PEquiv.trans`. |
| T0: regression examples | `PSTSEPPA/PSTS/Examples.lean` | **Formalized** | Discrete systems on 0/1/2 points, one Steiner triple, a non-closed two-point subset, and a genuinely partial singleton automorphism. |
| T1: signed words and partial evaluation | `PSTSEPPA/PSTS/WordEval.lean` | **Formalized** | Signed letters, left-to-right evaluation, append/composition and inverse-word calculus; orientation regressions include `p ; p⁻¹` being only a partial identity. |
| T2: abstract MAX interface | `PSTSEPPA/PSTS/MaxTransporter.lean` | **Formalized** | Finite ambient group, group-valued word evaluation, fibre maxima in the `PEquiv` restriction order, and the corrected identity-fibre lemma. |
| T2: quotient development | `PSTSEPPA/PSTS/Development.lean` | **Formalized** | Equality criterion with orientation `g * h⁻¹`, injective base copy, and right-`H` action are checked. |
| T2: quotient PSTS operation | `PSTSEPPA/PSTS/DevelopmentOperation.lean` | **Formalized** | Common-chart operation; fibre-MAX proves functionality; resulting quotient PSTS is checked. |
| T2: closed base copy | `PSTSEPPA/PSTS/DevelopmentBase.lean` | **Formalized** | Exact base-copy operation formula, reflection of undefinedness, and closedness of the base image. |\n| T2: quotient automorphism action | `PSTSEPPA/PSTS/DevelopmentAction.lean` | **Formalized** | Right multiplication gives total PSTS automorphisms; distinguished lifts extend the selected partial automorphisms. |\n| T2: conditional EPPA transfer | `PSTSEPPA/PSTS/EPPAFromMax.lean` | **Formalized** | Constructive hard gate: `selectedEPPAWitness` packages finiteness, closed induced base copy, and explicit total extensions. |
| A1: oriented labelled graphs / transition groups | `PSTSEPPA/ABO/...` | **Current target** | Start with a custom finite oriented labelled multigraph API supporting loops, formal inverses, repeated labels and trivial generators. |
| A2: clusters / coset extensions | `PSTSEPPA/ABO/...` | Planned | Include degenerate/equal-parameter cases explicitly. |
| A3: corrected ABO Theorem 4.7 | `PSTSEPPA/ABO/UpwardInduction.lean` | Planned | Incorporate repairs R1, R7, R8. Highest-risk gate. |
| A4: corrected Section 5 induction | `PSTSEPPA/ABO/FiniteConstruction.lean` | Planned | Separate repaired `k = 1` base case R2. |
| A5: corrected ABO Lemma 2.5 | `PSTSEPPA/ABO/MainLemma.lean` | Planned | Include final-group equality and equivariance. |
| C1: Cayley / semidirect-product bridge | `PSTSEPPA/ABO/CayleyApplication.lean`, `PSTSEPPA/ABO/MaxTransporter.lean` | Planned | Derive the concrete fibre-MAX property. |
| FINAL: unconditional PSTS-EPPA | `PSTSEPPA/PSTS/EPPA.lean` | Planned | Instantiate T2 with C1. |

## Gate discipline

Do not begin the long ABO construction merely because its definitions are
available. The first major milestone is a compiled conditional theorem of the
form

```text
finite PSTS A + finite selected partial automorphisms + MAX extension
    => finite PSTS witness extending the selected maps.
```

If that transfer layer does not compile cleanly, repair it or use the documented
fallback ladder before investing in ABO Sections 3–5.


### Gate T0 design note

The PSTS API deliberately uses a partial binary operation
`op : V → V → Option V` rather than a ternary relation.  Diagonal values are
total (`op x x = some x`).  Symmetry and one Steiner companion identity are
stored; the second companion identity is derived.  This keeps the structure
nonredundant while making closure under the partial operation literal.

Partial automorphisms are built on mathlib's option-valued `PEquiv`.  The
operation-isomorphism condition is a single `Option.bind` equality, so it
simultaneously preserves and reflects definedness.  Their domains and ranges
are required to be closed.  Inversion, closed preimages and composition are
proved in Lean; the composition convention is the one used by
`PEquiv.trans`: first the left map, then the right map.  This convention is
the one to be used by the signed-word layer.


### Gate T1 checkpoint

Signed words use the same left-to-right convention as `PartialAut.trans`.
Group-valued evaluation uses the matching multiplication order.  Formal
inversion reverses a word and inverts its letters; both group evaluation and
partial-automorphism evaluation respect this inversion.  Regression examples
explicitly prevent the false simplification `p ; p⁻¹ = refl`: for a proper
partial automorphism the composite is only the identity on its source.

### Gate T2 checkpoint: MAX and the quotient skeleton

The abstract input is intentionally only fibre-MAX: for every group value
`h`, a selected word `maxWord h` has that group value and its partial
evaluation extends every other word in the same fibre.  No inverse-monoid API
and no generation hypothesis on the ambient finite group are assumed.

The identity fibre uses the repaired argument:
`refl ≤ eval(maxWord 1)`; since `refl` is total, the latter partial
equivalence equals `refl`.  Hence every identity-fibre word is a partial
identity.

The quotient development is generated by
`(a, liftGen i * k) ~ (gen i a, k)`.  Lean now proves the exact equality
criterion

```text
[a,g] = [b,h]
  iff
there is a signed word w with
  evalH(w) = g * h⁻¹
  and evalPartial(w)(a) = b.
```

This fixes the orientation permanently and yields injectivity of the base map
`a ↦ [a,1]`.  Simultaneous right multiplication of group coordinates
descends to the quotient.  A common-chart relation also defines an
option-valued PSTS operation on the quotient; fibre-MAX is used to prove this
relation functional.

The base image is then proved closed, with an exact formula showing that the
induced partial operation is precisely the original operation on `A`.  Right
multiplication by every `h : H` is lifted to a total automorphism of the
quotient PSTS, and the distinguished lift of each selected generator extends
the corresponding partial automorphism on the base copy.

Finally `EPPAFromMax.lean` packages the construction as
`selectedEPPAWitness`: for finite `V`, any finite fibre-MAX extension
constructively returns a finite PSTS witness, an injective closed induced base
embedding, and explicit total automorphism extensions (with both source and
target equal to `Set.univ`).  This is the completed hard gate; ABO is now the
active frontier.
