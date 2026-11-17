# Environment traps that have already cost time

Each entry is a mistake that was actually made and cost real hours. Written so it is not made a
third time. Read before touching the toolchain or the `.lake` directory.

## 1. `*.olean.server` is NOT a regenerable artifact — deleting it breaks Mathlib

This was documented backwards in an earlier version of `HANDOFF.md`, and acting on that
documentation caused the single most expensive incident in this project.

`lake/Build/Module.lean` (the `noServerOLeanError` path) requires a `.olean.server` sidecar for
every module declared `module`. All 8311 Mathlib files are. On this device **8321 of 8322** sidecars
were missing, so:

    lean  ->  failed to open file '.../Mathlib/Data/Nat/Prime/Defs.olean.server'

Recovery by renaming `.olean` to `.olean.server` **does not work**:

    region_reader: own region overlaps a dep region's base_addr range

It cannot be faked; Mathlib needs a genuine rebuild. That rebuild is thousands of modules, made the
phone unusable for hours (load average 9.5, free memory down to 202 MB), and was abandoned.

**Rule: any check that needs Mathlib runs in CI.** `.github/workflows/verify.yml` builds Mathlib
itself. Locally, only core-only modules are checkable, and they import nothing from Mathlib.

## 2. `lake env lean` re-clones Mathlib from GitHub

Observed and killed. It does not merely resolve the existing dependency; it fetches. On this device
that is a multi-GB download onto a nearly full disk.

**Rule: never run bare `lake env lean`.** Use the plain `lean` invocation with an explicit
`LEAN_PATH`, as in `~/p2m_scratch/check-module.sh`.

## 3. Stale `.olean` produces phantom type errors

If you change an upstream module and do not rebuild it, downstream modules are checked against the
OLD `.olean` and report type mismatches that do not exist in the source. This cost an hour chasing
a non-existent `isqrt` name clash (the real cause was `CanonicalTravel.olean` being a day older
than `Isqrt.lean`).

**Rule: rebuild the dependency chain in order**, or delete the stale `.olean` and rebuild.

A related trap: `import A166944.X` fails with "object file does not exist" whenever `X.olean` was
never built locally — CI builds it, your working tree may not have. Build it explicitly with
`lean -o A166944/X.olean ./A166944/X.lean` before importing.

## 4. `omega` leaks `Classical.choice` on certain goal shapes

Not every goal: the small purely-linear ones are fine. The leaking shapes observed are (a) mixed
`Nat` goals with products, (b) `iff` goals closed by a bare `omega`, (c) the inductive step of a
path recursion over truncated subtraction.

Three fixes that worked:
* replace the terminal `omega` with an explicit `calc` chain over `Nat.add_le_add` /
  `Nat.mul_le_mul_left`;
* split an `iff` into `constructor <;> intro h <;> omega`;
* replace `by_cases` with `Nat.lt_or_ge` (which is constructive) where possible.

`CLASSICAL_CHOICE_AUDIT.md` records the four declarations this affected and the two that remain.

## 5. `pkill -f <pattern>` matches the agent's own shell

Used twice, killed the running command both times (SIGTERM to itself). A process pattern broad
enough to find the target also matches the `bash -c` that is running `pkill`.

**Rule: use `ps -eo pid,args | grep <pattern>` to find the PID, then `kill <pid>`.** Or, for a
yes/no check, just use `pgrep -af` and do not kill at all.

## 6. Overlapping heavy runs make the device unusable

The pattern that caused four separate crashes: starting a heavy Python scan, waiting with
`job_output`, and **starting another scan while waiting**. `job_output` with `wait` does not free
the process — it keeps running while the new one starts.

Also: `proot-distro login` + `lean` running concurrently multiplies the cost, since each `proot`
login is its own container invocation and each `lean` peaks around 530 MB.

**Rule: one heavy process at a time.** Check with `pgrep -af` before starting. Do not start work
while a `job_output` wait is pending — that is not waiting, it is overlapping.

## 7. Large `M` makes jump-form replay effectively hang

The jump form scans candidate indices with a `gcd` each, so its cost grows with the gap. Replaying
from `M ~ 1.5e9` did not finish in 15 minutes, twice. Record verification for large `M` belongs in
Lean (`decide +kernel`, as `VerifiedLaterRecordExtension` does it), not in Python.

**Rule: Python only for `M <= 1e6`.** Above that, cite the verified record list or prove in Lean.
