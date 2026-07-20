# Appendix C Update Required Before Release

The manuscript currently names the internal archive:

```text
OBS_Mechanism_Submission_Companion_v0.2
```

and describes a separate manuscript source package. That wording does not match the intended public GitHub–Zenodo release structure.

After the GitHub repository exists and the Zenodo software DOI is minted, replace the current Data and Code Availability appendix with wording of this form:

```latex
\section{Data and code availability}

The complete reproducibility materials for this work are available in the
associated public GitHub repository and its archived Zenodo software release.
The repository contains the exact 12-state witness data, corrected spectral
analysis, causal-window certificates, Lean 4 formalization, successful clean-build
audit, manuscript source, figures, reproduction instructions, environment records,
and SHA-256 manifests.

The validated numerical certificates require Python and \texttt{python-flint}.
The Lean component is pinned to Lean 4.29.0 and Mathlib revision
\texttt{8a178386ffc0f5fef0b77738bb5449d50efeea95}. Its umbrella build includes
\texttt{rowMarkov\_paperCore},
\texttt{rowMarkov\_etaCur\_eq\_eta\_iff},
the matched-subdivision modules, and the exact local-obstruction module.
A fresh clean build completed successfully with 8,275 jobs and no proof bypasses.

Lean verifies the general symbolic theorems but does not verify the
witness-specific spectrum, logarithmic interval evaluation, or causal-window
root isolation; those claims are supported by separate exact and validated
computational certificates in the same repository.

Repository: \url{GITHUB-REPOSITORY-URL}

Archived software release:
\href{https://doi.org/SOFTWARE-DOI}{doi:SOFTWARE-DOI}.
```

Do not finalize the paper PDF until both placeholders are replaced.
