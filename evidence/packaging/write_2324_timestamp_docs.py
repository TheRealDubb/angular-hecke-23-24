from pathlib import Path
import datetime, json
ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT/'outputs/ANGULAR_23_24_TIMESTAMP_2026-10-18'
REPO = DEST/'repository'
assert (REPO/'SOURCE_CLOSURE.json').exists()
docs = {
'README.md': r'''# Angular Hecke L-functions: the strict 23/24 zero-free bound

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
''',
'THEOREM_SCOPE.md': r'''# Exact theorem and scope

The field is K = Q(sqrt(-3)), with its Eisenstein integer ring O. The Lean
`AngularCharacter` consists of an integer k, a nonzero integral ideal modulus,
a finite residue character, and the unit-compatibility equation

    alpha(u)^k * residue(u mod modulus) = 1  for every global unit u.

For nonzero elements, the physical coefficient is
`alpha(a)^k * residue(a mod modulus)`. The coefficient at zero is defined as
zero; unit compatibility lets these coefficients descend to ideals. The
function in the theorem is `FamilyContinuation.LFunction`, linked by the source
chain to the actual ideal Dirichlet series in its half-plane of convergence.
See [AngularCharacter.lean](snapshot/outputs/ANGULAR_LEAN/v1/AngularCharacter.lean)
and the definition dependencies listed in SOURCE_CLOSURE.json.

The principal theorem is exactly:

```lean
theorem physical_seed (χ : AngularCharacter) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re)
    (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1) :
    FamilyContinuation.LFunction χ s ≠ 0
```

Its qualified name is
`OAI.SevenEighths.Angular.FullFamilySeed.physical_seed`.
The inequality is strict. No claim is made on Re(s) = 23/24.
All integer angular types admitted by the compatibility equation are covered;
there is no primitivity assumption in this statement.

The sole exception is the actual type-zero principal pole at s = 1. Type-zero
nonprincipal functions are included at s = 1. A totalized value at a pole is
not being classified as an analytic zero.

For every real unitary norm-twist parameter tau the second theorem is exactly:

```lean
theorem physical_seed_norm_twist (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re)
    (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1+(τ:ℂ)*I) :
    NormTwist.LFunction χ τ s ≠ 0
```

Its qualified name is
`OAI.SevenEighths.Angular.FullFamilySeed.physical_seed_norm_twist`.
The twist uses the shift s -> s - i*tau, so the principal pole shifts to
1 + i*tau. The bound is independent of the selected character in this
qualitative nonvanishing statement. No quantitative estimates uniform in
growing angular order, nor effective uniform thresholds for such estimates,
are claimed by this release.

The adjacent source proves nonprincipal entireness and half-plane transport.
The final v30 bundle contains 14 theorem targets across two modules. This
target count is not the size of the entire proof dependency closure.

The claim is 23/24 = 0.958333..., not 7/8, 0.8748389, GRH, or RH. The stronger
angular target remains unfinished. The theorem refers to the explicit Lean
family and continuation above, not an unspecified collection of all Hecke
characters over arbitrary number fields.
''',
'VERIFICATION_STATUS.md': r'''# Verification status and trust scope

## Existing completed evidence

The v30 receipt records a successful run at 2026-10-17T01:22:07 UTC. Its log
contains all four required markers:

```
STATEMENT_COMPARISON_PASSED
AXIOM_AUDIT_PASSED
KERNEL_REPLAY_AND_QUOTIENT_POSTCHECK_PASSED
OFFLINE_REPLAY_PASSED: native Windows; production sandbox not exercised
```

The comparison targets, permitted axioms, proof-export hashes, exact local
command and checker/runtime executable hashes are retained in the original
receipt and manifest. No definition holes were permitted. The statement
fixtures copy the authored statements and definition bodies, replacing theorem
proofs with placeholders only in the expected/challenge environment. They are
kept distinct from the solution source. Expected fixtures are not proofs.

The proof export is replayed into a fresh kernel environment by the same Lean
implementation. The proof closure is audited for the three permitted axioms;
the quotient constants receive the recorded postcheck. This is not an alternate
kernel, a second independently authored analytic specification, or independent
human review. The prior development and checks were performed within one
auditor's workflow.

The supplied `evidence/checker-source/OfflineReplay.lean` is the native Windows
driver. It calls the upstream comparator's statement and axiom routines and
the Lean kernel replay. Its local source/configuration and upstream pins are
preserved; the Linux Landlock production sandbox was not used. The pinned
exporter revision is recorded in DEPENDENCY_PINS.json.

## Scope wording in inherited receipts

Some original receipts contain generic status text such as "No full angular
zero-free theorem claimed" or "not ... a zero-free theorem." Those inherited
template fields are retained byte-for-byte. They are not used as proof of any
claim. The precise v30 `scope`, theorem target list, actual Lean statements,
and replay result identify the 23/24 seed proved here. The broader 0.8748389
project was and remains incomplete. This README does not reinterpret a receipt
as establishing the stronger target.

## Release preparation checks

PACKAGE_INTEGRITY_AUDIT.json records the release preparation audit:

- All 130 imported angular sources and their local objects match their recorded
  successful compilation hashes; source copies remain byte-for-byte identical.
- The final genuine modules and copied fixtures match the verified manifest.
- The final receipt, members, log and bundle hashes match existing evidence.
- Both supplied gzip proof exports match compressed hashes, and streaming
  decompression matches their recorded raw hashes and lengths.
- The original tracked OAI-003 checkout is clean at the pinned revision.

The v25 and v29 receipts are included as earlier seed/norm-twist provenance.
Their separate proof streams are not release assets; the supplied v30 streams
are the final bundle evidence. Locally compiled objects, giant setup maps,
runtime binaries and package caches are not included. The original source
archive and dependency manifests supply the source pins. The upstream checkout
is a partial clone, so the archive contains the required OAI source closure and
build manifests, rather than unrelated upstream files. Every included upstream
file is checked against its committed Git blob; ORIGINAL_DEPENDENCY_SNAPSHOT.json
records any working-tree CRLF versus committed LF normalization explicitly.

## Pending work

Clean portable source reproduction, a fresh clean dependency rebuild, and Linux
production replay remain pending. No such checks were performed for this
timestamp. The source snapshot preserves its original module/version layout;
it has not been converted into a tested standalone Lake project. Harness files
are provenance copies and retain their original workspace assumptions.

The stronger 0.8748389 theorem is unfinished and has been preserved separately
as CHECKPOINT B. Research drafts and their partial native checks are not part of
the present theorem claim.
''',
'NOTICE.md': r'''# Source notices

The unchanged OAI-003 source comes from openai/math at revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Its original copyright and Apache-2.0
license are preserved in the pinned source archive and dependencies/oai003/LICENSE.

The comparator sources retain the upstream license in
evidence/checker-source/LICENSE and the upstream revision in DEPENDENCY_PINS.json.
Existing source headers and notices are preserved. Dependency repositories and
their revisions appear in the supplied Lake manifests. This timestamp package
does not alter the license notices on any copied source.
''',
'RELEASE_NOTES.md': r'''# Angular Hecke 23/24 — frozen source and Windows verification evidence

This release timestamps the exact Lean theorem for nonvanishing in Re(s) > 23/24
for the unit-compatible angular Hecke family over Q(sqrt(-3)), including all
integer angular types and real unitary norm twists. Only the genuine type-zero
principal pole is excluded, shifted to 1+i*tau for a norm twist.

It contains unchanged source dependencies and existing native Windows
statement-comparison, axiom-audit, fresh kernel-replay and quotient-postcheck
receipts. Attach all files listed in RELEASE_ASSETS.json; their hashes bind
the proof exports and pinned OAI-003 source archive to the tagged commit.

Clean portable reproduction and Linux replay remain pending. The stronger
0.8748389 theorem remains unfinished and is not claimed by this release.
'''
}
for name, value in docs.items():
    (REPO/name).write_text(value,encoding='utf-8')
(REPO/'.gitattributes').write_text('* -text\n',encoding='utf-8')
(REPO/'.gitignore').write_text('.lake/\n*.olean\n*.ilean\n*.setup.json\n',encoding='utf-8')
now = datetime.datetime.now(datetime.timezone.utc)
budget_anchor = datetime.datetime.fromisoformat('2026-10-18T02:26:03+00:00')
budget = {'recorded_utc':now.isoformat(),'user_estimate_total_hours':8,
    'hard_release_reserve_hours':3,'max_stronger_research_hours':5,
    'basis':'User estimate: weekly allowance about 2.5h, automatic credits about 5h, possible reset; conservative total 8h.',
    'reset_redeemed':False,'research_state':'CHECKPOINT B frozen while upload-ready package is prepared',
    'publication':'User will upload; prepare frozen local commit/tag and assets only.',
    'budget_anchor_utc':budget_anchor.isoformat(),
    'conservative_research_cutoff_utc':(budget_anchor+datetime.timedelta(hours=5)).isoformat(),
    'note':'Use cutoff as conservative wall-clock guard, not a provider guarantee. Do not consume hard reserve on research.'}
(ROOT/'work/angular_lean/successor_risk/RELEASE_RESERVE_BUDGET.json').write_text(json.dumps(budget,indent=2)+'\n')
print(json.dumps({'documents':list(docs),'research_cutoff_utc':budget['conservative_research_cutoff_utc']}))
