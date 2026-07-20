# Final Lean Build Verdict

**PASS — CLEAN BUILD INDEPENDENTLY REPRODUCED**

The finalized `OBSMechanismLean_v0.2_core_closed` source was rebuilt from a
deleted root-project `.lake/build` directory under the pinned environment.
Dependency caches, including Mathlib, were reused; no prior root-project build
artifact was reused.

- Command: `bash build_wsl.sh`
- Filesystem-observed build start: `2026-07-20T12:31:39.822-07:00`
- Build finish: `2026-07-20T12:45:16.507-07:00`
- Time zone: America/Los_Angeles (`UTC-07:00`)
- Exit status: `0`
- Result: `Build completed successfully (8275 jobs).`
- Warnings: `0`
- Errors: `0`
- Proof-bypass count: `0`
- Former bridge assumptions remaining in the closed public interface: `0`

The project directory is not a Git worktree, so Git status is not applicable.
Source identity is established by SHA-256 comparison with the supplied release
archive and its embedded manifest.

The axiom audit reports only Lean's standard foundational axioms `propext`,
`Classical.choice`, and `Quot.sound`.  It reports no project axiom and no former
bridge assumption.

