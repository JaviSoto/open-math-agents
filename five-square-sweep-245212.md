# Parallel fixed-support check for A245212

This checks every positive exponent tuple for a given support
`n = 3² · 5ᵃ · 7ᵇ · qᶜ · rᵈ`, using the [finite exponent bound and congruence argument](four-odd-primes-245212.md).
The two inputs below are inclusive intervals; the runner selects every prime pair with `7 < q < r`.
The command prints one JSON summary and stores one row per completed support, including its counts and CPU and elapsed times.

    python3 five_square_sweep_245212.py --q 11 11 --r 998 10000 --state five-square-results.sqlite3

Run without Python's `-O`. Use `--jobs 6` to request six worker processes, or `--jobs 1` for a serial comparison. By default the runner uses at most eight workers; it subtracts the machine's existing one-minute load and leaves two cores available. When available-memory measurements are accessible, it also reserves 2 GiB and budgets 512 MiB per worker. These are scheduling estimates, not mathematical restrictions. The [original CLI](five_square_boxes_245212.py) still accepts an explicit list of primes and prints one row per support.

## Resume or inspect a sweep

Re-run the same command, or extend either range, with the same SQLite file. A completed row is committed in its own transaction. If the checker finds a solution or raises an exception the command exits unsuccessfully, prints the affected support and does not save it as excluded. An interruption preserves completed rows. For a fresh timing comparison use `--state :memory:` in each run.

Every row is keyed by `(proof SHA-256, q, r)`. The hash includes the driver and the transitive local arithmetic modules. Code changes cause old rows to be ignored without deleting their evidence. `results_sha256` hashes the sorted lines `q r boxes prefixes two_hits four_hits\n`; it does not depend on execution order or machine timing. To see individual results, substitute the current fingerprint from the summary:

    sqlite3 five-square-results.sqlite3 "SELECT q,r,boxes,prefixes,two_hits,four_hits,round(elapsed,3) FROM verified WHERE fingerprint='FINGERPRINT' ORDER BY elapsed DESC LIMIT 10"

The four counts are the boxes left after interval/rounding rejection, two-exponent prefix comparisons, candidates passing the first pair of congruences, and candidates passing all four congruences. The checker evaluates the original equality on any candidate in the last group. On supports with `34·∏p ≤ 54·∏(p−1)` over the four tail primes, all counts are zero: the normalized expression is affine in each `Yₚ`, with `Xₚ=(p−Yₚ)/(p−1)`; every corner containing zero has score at most 2, and the all-ones corner has score 47/27. All actual `Yₚ` lie strictly between 0 and 1, so the weighted average is strictly below 2.

## Reproduction and scope

The new range `q=11, 997<r≤10,000` contains **1,061 primes**. The exact computation gives **150,887 boxes**, **36,194,184 prefix comparisons**, and no tuples passing the first pair of congruences. The per-support result digest is `1b5960904a210460612f8051b8106af03a87c8ad68294aeaaa2afb06124d1f30`. This rules out those supports by computation; it does not settle larger last primes or constitute a Lean certificate.

The contiguous check `--q 11 11 --r 12 10000` covers **all 1,224 eligible prime supports** through 10,000. It gives **176,098 boxes**, **40,773,889 prefix comparisons**, and again no two-congruence survivors. Its result digest is `65c3c69df8695f85a416f34d9cc0e187d91616fcbd75d9a02e8234350db6f826`.

On the same Mac and the same 33 prime supports (`q=11`, `1009≤r≤1229`), the original serial CLI took 12.10 s. Six workers using the same arithmetic took 2.39 s. Multiplying the positive integer denominators directly in the rounding comparison reduced that to 1.84 s (9.39 s using one worker). All three computations produced the same per-support counts: 4,589 boxes, 1,121,160 prefix comparisons and no survivors. These wall times describe this machine, with other work running.

For the 1,061 new supports, the two six-worker implementations took 84.69 s and 61.62 s respectively. Every one of the 1,061 per-support rows matched. Repeating the final command with the same database took 0.022 s and did not start a worker.

    python3 -m unittest test_five_square_sweep_245212
    python3 five_square_sweep_245212.py --q 11 11 --r 1009 1229 --jobs 1 --state :memory:
    python3 five_square_sweep_245212.py --q 11 11 --r 1009 1229 --jobs 6 --state :memory:

Both benchmark commands must return result digest `49a94cb2b39c9b5e0f2af89e07d32c20bf9da169ed7008a7796f16c6757baa69`. The tests cover failed workers, resume without rechecking, transitive source changes, an excluded corner-bound support and a reference result from the original serial checker.
