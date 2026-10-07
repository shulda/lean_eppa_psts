# EPPA for partial Steiner triple systems — Lean formalization

Lean formalization of ordinary EPPA for finite partial Steiner triple systems
(PSTS) with **closed** substructures/embeddings.

The intended route is modular:

1. formalize PSTS, closed substructures, partial automorphisms and partial-word
   evaluation;
2. prove a conditional transfer theorem from a finite
   `MaxTransporterExtension`-style interface to a finite PSTS EPPA witness;
3. formalize the corrected Auinger–Bitterlich–Otto (ABO I) reflecting-group
   construction needed for Lemma 2.5;
4. derive the concrete fibre-MAX property via the Cayley/semidirect-product
   bridge and instantiate the transfer theorem.

The planning material motivating this route is **advice, not an authoritative
specification**. Lean is expected to verify every simplification. If a proposed
streamlining fails, the project should fall back toward the audited corrected
ABO source rather than force the abstraction.

See [FORMALIZATION.md](FORMALIZATION.md) for the live dependency/status map and
[RESEARCH_LEDGER.md](RESEARCH_LEDGER.md) for repairs, deviations, failed
approaches, and the current proof frontier.

## Development policy

The repository follows the workflow used in
`shulda/lean_all_those_eppa_classes`:

- Lean and mathlib are pinned to a stable release.
- `main` is kept at a CI-green checkpoint; substantive work is done on named
  branches.
- GitHub Actions builds the whole Lean library on every push and pull request.
- CI runs an axiom audit.
- Project declarations must not depend on `sorryAx` or custom axioms; only
  Lean/mathlib's standard logical axioms (`propext`, `Classical.choice`,
  `Quot.sound`) are allowed.
- Mathematically substantive deviations from the source proof are recorded
  explicitly in the ledger rather than hidden inside implementation details.

## Primary theorem

The target is:

> Every finite partial Steiner triple system has a finite EPPA witness with
> respect to closed substructures/embeddings.

For the first phase, generic partial-algebra or inverse-monoid abstractions are
deliberately postponed unless they make the Lean proof genuinely simpler.
