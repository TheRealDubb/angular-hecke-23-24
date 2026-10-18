# Verification status and trust scope

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
