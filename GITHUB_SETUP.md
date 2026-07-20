# GitHub Repository Setup

## Repository settings

**Recommended name**

`OBS-Dissipation-Coherence-Counterexample`

**Description**

Certified 12-state counterexample to the OBS dissipation–coherence conjecture, with exact numerical certificates, causal spectral analysis, and Lean 4 formalization.

**Visibility**

Public

**Suggested topics**

- `stochastic-thermodynamics`
- `markov-chains`
- `entropy-production`
- `spectral-theory`
- `lean4`
- `computer-assisted-proof`
- `reproducible-research`

## Creation

Create an empty public repository. Do not ask GitHub to generate a README, license, or `.gitignore`, because all three are already supplied here.

Upload the contents of this directory so that `README.md` is at the repository root.

## Before the first release

1. Reserve or obtain the paper DOI.
2. Add that DOI to `.zenodo.json` as an `isSupplementTo` related identifier.
3. Add the paper DOI to the preferred citation in `CITATION.cff`.
4. Replace Appendix C in the paper with the final repository URL and software DOI wording.
5. Commit the updated manuscript PDF and source.
6. Connect the repository in Zenodo.
7. Confirm GitHub Actions completes successfully.
8. Tag and publish release `v1.0.0` using `RELEASE_NOTES_v1.0.0.md`.

Zenodo will archive the enabled GitHub release and mint the software DOI.
