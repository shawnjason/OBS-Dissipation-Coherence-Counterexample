# Certified Counterexample to the OBS Dissipation–Coherence Conjecture

This repository is the reproducibility companion for:

> Shawn Kevin Jason (2026), *Current-Weighted Localization and Dynamic Spectral Spacing in a Certified Counterexample to the Dissipation–Coherence Conjecture*.

The paper gives an exact 12-state, 13-edge, cycle-rank-two continuous-time Markov generator whose unique visible spectral-leading oscillatory mode satisfies

\[
Y=\frac{\sigma\lambda_R}{\lambda_I^2}=0.9011753725957478<1,
\]

thereby disproving the unrestricted Oberreiter–Barato–Seifert dissipation–coherence conjecture. The violating mode lies near the visibility threshold; the high-coherence regime remains open.

## What this repository contains

- `paper/` — manuscript PDF, LaTeX source, figures, and source crosswalks.
- `packages/` — authoritative exact and validated numerical certificate archives.
- `lean/` — directly buildable Lean 4 project for the symbolic theorem layer.
- `lean_audit/` — final independent clean-build, proof-bypass, theorem-signature, and formalization-boundary audit.
- `logs/` — pinned Python/Lean environments and promoted certificate logs.
- `tools/` — archive extraction and SHA-256 verification utilities.
- `REPRODUCTION_MATRIX.md` — claim-to-artifact and checker map.

The original package archives are retained unchanged in `packages/`. The Lean project is also exposed directly in `lean/` so that GitHub CI and referees can build it without unpacking an archive.

## Integrity check

From the repository root:

```bash
python tools/verify_sha256.py
```

A successful run ends with:

```text
PASS: repository SHA-256 manifest verified
```

## Lean build

Pinned environment:

- Lean `4.29.0`
- Lake `5.0.0`
- Mathlib revision `8a178386ffc0f5fef0b77738bb5449d50efeea95`

Build from the repository root:

```bash
cd lean
lake update
lake exe cache get
lake build
```

The final independent clean-build audit reports:

- exit status `0`;
- `8,275` jobs completed;
- zero warnings or errors;
- zero proof bypasses;
- none of the former bridge assumptions in the public theorem.

See `lean_audit/FINAL_LEAN_BUILD_VERDICT.md` and the accompanying logs.

## Numerical certificates

The authoritative numerical packages are distributed as immutable ZIP archives. This preserves their internal manifests and exact source layout.

Because the 12-state package contains Windows-style ZIP path separators, use the included normalizing extractor:

```bash
mkdir -p build
python tools/extract_normalized.py \
  packages/OBS_sub12_package_v0.1.zip \
  build/sub12
```

Then follow the package-level reproduction guide:

```bash
cd build/sub12/OBS_sub12_package_v0.1
python -m pip install -r requirements.txt
python run_all.py
```

For the causal-window package:

```bash
python tools/extract_normalized.py \
  packages/OBS_theta_causal_completion_package_v0.1.zip \
  build/causal
cd build/causal
python -m pip install -r requirements.txt
python scripts/gershgorin_window_certificate.py
python scripts/verify_exact_gershgorin_certificate.py
```

The corrected spectral-bridge package is:

```text
packages/OBS_theta_spectral_bridge_package_v0.2.1_corrected.zip
```

Its internal README and scripts distinguish the exact 11-state contraction from the separately reoptimized 11-state frontier.

## Formalization boundary

Lean verifies the general symbolic layer, including:

- the generator-level three-factor theorem;
- strict refinements and the equality characterization;
- matched-subdivision algebra;
- the exact local-invariants obstruction.

Lean does not verify the witness-specific spectrum, logarithmic interval evaluation, Rouché/Gershgorin root isolation, or finite role-layer classification. Those are supported by separate exact and validated numerical certificates.

## Citation

Use the paper as the preferred scientific citation. GitHub citation metadata are provided in `CITATION.cff`. The archived software DOI will be added after the first GitHub release is deposited by Zenodo.

## Licensing

- Code, scripts, and Lean source: MIT License (`LICENSE`).
- Manuscript, figures, reports, and documentation: CC BY 4.0 (`LICENSE-DOCUMENTATION.md`).

## AI-use disclosure

AI systems assisted computational search, theorem discovery, code generation, adversarial audit, synthesis, and manuscript preparation. The human author selected and framed the scientific problem, directed the research program, reviewed and reran the certificates, determined the claims, and accepts responsibility for the work. The load-bearing claims are supported by machine-checked proofs and exact or validated computational certificates rather than reliance on AI-generated reasoning.
