# Angular Hecke L-functions: the strict 23/24 zero-free bound

This timestamp package freezes the Lean source and existing native Windows
verification evidence for the strict half-plane **Re(s) > 23/24** for the
unit-compatible angular Hecke family over Q(sqrt(-3)), including real unitary
norm twists. The exact statements and exceptions are in [THEOREM_SCOPE.md](THEOREM_SCOPE.md).

**The stronger 0.8748389 theorem remains unfinished and is not claimed here.**

The final bundle has recorded successful copied-statement/recursive-definition
comparison, permitted-axiom audit, fresh same-Lean-kernel replay and quotient
postcheck on native Windows. The only permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Original receipts are preserved unchanged.

**Clean portable reproduction and Linux replay remain pending.** Preparing this
release did not rebuild the 130-module source chain or perform another replay.
It checked source/object/receipt hashes and the compressed and uncompressed
proof-stream hashes against the existing records. This is an evidence release,
not a newly tested standalone Lake project.

## Start here

- [Exact theorem and scope](THEOREM_SCOPE.md).
- [The theorem source](snapshot/outputs/ANGULAR_LEAN/v30/AngularFullFamilySeed.lean).
- [The full-family replay log](evidence/windows/v30/AngularPrincipalExceptionBundle.replay.log)
  and [receipt](evidence/windows/v30/AngularPrincipalExceptionBundle.replay.json).
- [Dependency pins](DEPENDENCY_PINS.json), [unchanged source closure](SOURCE_CLOSURE.json),
  and [package integrity audit](PACKAGE_INTEGRITY_AUDIT.json).
- [Evidence interpretation and remaining reproduction work](VERIFICATION_STATUS.md).
- [Release-asset hashes](RELEASE_ASSETS.json) and [tracked-file hashes](SHA256SUMS).

The snapshot contains the 130 unchanged angular source modules on the theorem's
import chain, together with their native compile receipts. The original OAI-003
Lean dependency closure is supplied as a separate unchanged source archive at its pinned
Git revision. Mathlib and the other Lake dependencies are pinned in the original
manifest. No portability refactoring was applied.

The two compressed final proof exports are release assets, not Git objects.
Their SHA-256 hashes are bound to this repository by RELEASE_ASSETS.json.
The authored Windows comparator adaptation and its upstream revision/pins are
included. Original receipts retain local paths for provenance; those paths are
not instructions to recreate the author's filesystem layout.

This package has a frozen local commit and tag. It becomes a public timestamp
only when that commit/tag and the listed assets are uploaded. The author will
perform the upload; local preparation is not evidence of public publication.
