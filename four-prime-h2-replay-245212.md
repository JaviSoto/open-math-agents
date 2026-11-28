# A245212: exact four-prime H2 replay

**Accepted registered parent:** the project checker also accepted
`proofs/OeisA245212.conjecture.R1.H1.R1.H2.R1.H2.lean` in **24 min 50.28 s**
at **3,701.2 MiB**. This single file proves the unbounded and bounded cases
together; its receipt is `four-prime-parent-accepted-245212.json`.

**Accepted single-file proof:** `proofs/OeisA245212.conjecture.R1.H1.R1.H2.R1.H2.R1.H2.lean`
and `BalancedHybridFull245212.lean` are the same 520,262-byte verified source.
The unmodified official checker accepted `OMA.solution` in **24 min 43.46 s**,
with peak physical memory **3,701.8 MiB**. The complete verdict, exact source
hash, runtime and memory measurements are in `four-prime-h2-accepted-245212.json`.

The 499-module source archive `odd-four-lean-source.zip` proves the stronger
theorem `OMA.OddSupportClass245212.odd_four` for all odd integers with at most
four distinct prime divisors. Its replay instructions are in
`four-odd-primes-245212.md`. The last two of the ten finite support cases
are proved in `Q511All.lean` and `Q513WheelAll.lean`.
`ModularH2245212.lean` separately applies the ten cases to the **exact
registered H2**. Pinned Lean audited `OMA.solution` with exactly
`propext, Classical.choice, Quot.sound`.

## Single-file submission candidate

Original frozen candidate (superseded; do not submit):
`Thin88Full245212.lean`,
522,262 bytes, SHA-256
`a7b8277f1175b588d98112245fa4550ed9272c7cbff4b649f029eaa18f5586bd`.
The official linter accepts it; the analytic helpers, generic tree verifier,
and transfer from the ten support boxes compiled together. On Nov 27 the
official checker rejected this file in 486.75 s, peak 7,497.6 MiB.
Checkpoint 97 exceeded Lean’s default 200,000 elaborator heartbeats at
`abstract nested proofs`. Later checkpoints then had no preceding declaration.
Independent kernel tests of its neighboring 52 arithmetic rows all passed.

Starting in this task's workspace, regenerate and run:

```sh
python3 thin_tape_245212.py --block 88 --depth 4 --batch 13 --fast-primes --lean CombinedTapes245212.lean
python3 assemble_four_h2_245212.py --output Thin88Full245212.lean
python3 check_four_h2_245212.py --source Thin88Full245212.lean --limit-mib 10240 --label thin88
```

The last command invokes the upstream `tools/check.sh` unchanged with
its 30-minute Lean timeout, plus a local 10 GiB physical-memory stop for
its own Lean process. Results are written to
`/private/tmp/oma-complete-four-h2-thin88-verdict.json` and
`/private/tmp/oma-complete-four-h2-thin88-metrics.json`.

There are 6,928 short checked records and 857 explicit starting boxes; the
rest recover their box from at most four checked parent splits. The
complete (5,7) pilot with this 88-node representation, batch 16 and
`FastPrimeTrim245212.rule` passed in 119.62 s, peak 3,517.1 MiB. This is
one support, not a timing or memory guarantee for the complete file.

Two earlier end-to-end attempts were stopped by their local memory monitors:
the 192-node original at 7,038.5 MiB in 80.62 s; the shared two-lane
version at 10,273.8 MiB in 156.66 s. Both official scripts wrote
“does not compile” with no Lean diagnostic. Neither source passed. Their
JSON receipts have the same paths above without `-thin88`, and with
`-lanes2`, respectively.

## November 27 alternate single-file replay

`DeltaFull245212.lean` is 523,504 bytes, SHA-256
`99b47511e14cc4c7e61b86316833edd83902afa01421cad81888d5ba10177204`.
It stores the changes in box endpoints directly and uses the opposite
prime-power digit to prune the four exponent axes. The independently checked
arithmetic rule appears in `ReverseRule245212.lean`. This reduces the
largest support from 66,147 to 44,283 branch-and-bound nodes; the ten cases
use 4,158 postorder proof records. The (5,7) replay passed in 100.84 s,
peak 3,432.9 MiB. Checkpoints use literal start/end indices and a scoped
`set_option maxHeartbeats 0 in`; the official 30-minute wall-clock limit remains.

```sh
python3 thin_tape_245212.py --block 88 --depth 4 --batch 13 --inverse --delta --lean DeltaCombined245212.lean
python3 assemble_four_h2_245212.py --tapes DeltaCombined245212 --output DeltaFull245212.lean
python3 check_four_h2_245212.py --source DeltaFull245212.lean --limit-mib 10240 --label delta88
```

The upstream checker rejected this file on November 27 at 9:04 p.m. Pacific:
`timeout: over 30 minutes`. The process exited after 1,806.34 s; its peak
physical memory was 9,932.8 MiB. The 10 GiB memory monitor did not stop it.
The file passed the static project checks; the upstream Lean process did not
return before its deadline. The verdict and resource samples are summarized
in `/private/tmp/oma-complete-four-h2-delta88-verdict.json` and
`/private/tmp/oma-complete-four-h2-delta88-metrics.json`. The wrapper uses
a temporary link under the registered proof name; the frozen thin88 file
remains unchanged. This run predates the accepted balanced layout above.

The same numerical checkpoint that failed in thin88 passed after adding the
scoped heartbeat setting. A local compiled-evaluator diagnostic also exposed
an eager construction of an unused list of up to 10¹⁸ prospective primes.
`OMA.GuardedWheel245212.rule_eq` proves that moving that construction into
the branch for short intervals preserves every answer. This issue affected
the diagnostic; it does not explain the official kernel’s heartbeat failure.
The compiled checker verified **all 4,158 records**. `CellTape245212.lean`
stores the five intervals as data between instructions, so repeated
coordinate reads don't redo earlier numeric cuts. This diagnostic checks
the witness data; the official single-file kernel result is separate.
Regenerate the diagnostic with
`python3 diagnose_tape_245212.py DeltaCombined245212.lean /private/tmp/CellProgress245212.lean 0 4158 --cells`;
in the pinned Lake environment with the local modules on `LEAN_PATH`, run
`lean --run /private/tmp/CellProgress245212.lean`.

One smaller alternative, `ResidueFull245212.lean` (463,699 bytes, SHA-256
`85f8799ebdf2dad288ef220384c24fc8319f9675ed25a185bce747bcb8f6ace9`),
adds a prime-square test for the last exponent and uses 3,358 records.
`ResidueFront245212.lean` and the entire (5,7) pilot passed pinned Lean.
The pilot took 119.30 s, versus 100.84 s for the previous variant.
On a common (5,13) subtree with 753 original search nodes it also took
34.48 s, versus 16.17 s without this residue pass. The smaller file was
not sent to the 30-minute checker: both matched trials were slower. For a
future attempt, test a new arithmetic rule against the same subtree and
the complete (5,7) pilot before attempting another end-to-end run.
To reproduce it use the delta commands above with
`--residue 1400`, tape `ResidueCombined245212`, output
`ResidueFull245212.lean`, and receipt label `residue88`.

## Resume with a short kernel benchmark

At this point the fastest measured complete (5,7) layout was the delta/inverse tape:
100.84 seconds for its 195 records. A matched 753-node (5,13) subtree takes
16.17 seconds. The largest families are (5,13), with 2,153 records; (5,11),
773; and (5,17), 557. Together they account for 84% of the 4,158 records.
One fast subtree does not establish the total runtime.

The fixed-prime cache experiment uses a lookup for `FastFactor245212.smallQuot`
at fixed small primes. For `e ≥ 31`, put `h = p^32` and precompute the
integer `c(p) = (2^256*p*(h-1))/((p-1)*h)` for the fixed primes. The exact
answer is then `c(p)/(e+1)` by composition of natural-number divisions.
For `e < 31`, use the existing expression or a small exact lookup; retain
the general expression for the variable prime. `CacheQuot245212.lean`
proves the replacement equal to `smallQuot` at every input and the modified
interval/reverse-digit checker equal to the original for every instruction.
For the same 753-node (5,13) subtree the prototype caching 3, 5 and 13 took
19.52 s wall (18.95 s CPU; 1,792.3 MiB), versus 16.17 s for the baseline.
Keep the baseline. Neither this cache nor the extra prime-square test
justifies another full run. A different search certificate that avoids
whole subtrees without scanning their exponent triples is a more useful
next experiment than replacing another individual arithmetic operation.

From the task workspace, reproduce the existing short benchmarks with the
task’s built local modules in `/private/tmp` and the pinned Lake checkout:

```sh
wk="$PWD"
fc=/Users/javi/code/open-math-agents/.oma/formal-conjectures
bench() { (cd "$fc" && lake env python3 "$wk/profile_box_lean_245212.py" "$1" --max-mib 6400); }
bench "$wk/BaseCost513245212.lean"
bench "$wk/CacheCost513245212.lean"
bench "$wk/DeltaPilot57245212.lean"
python3 diagnose_tape_245212.py DeltaCombined245212.lean /private/tmp/DeltaSample513245212.lean 2000 2039 --kernel --chunks 13
bench /private/tmp/DeltaSample513245212.lean
```

Run the same inputs with the proposed rule. If the two matched tests are
faster, sample early, middle and late 13-record blocks of each major family
with `diagnose_tape_245212.py --kernel --chunks 13`. Global index ranges
are `[195,968)` for (5,11), `[968,3121)` for (5,13), and `[3121,3678)`
for (5,17). Multiply the measured per-record costs by the family sizes;
allow for the analytic front, the other families and a timing margin. An
estimate below 25 minutes gives a reason to try the 30-minute project
checker again. These are local kernel timings; only the upstream receipt
determines whether the standalone submission passes.

## Packed congruence and geometric-series replay

`GeoFull245212.lean` is 412,290 bytes, SHA-256
`4d882f0643bf0963adf67819e449a6ba0e87b8fe44338ccf68a1183c7061af5b`.
For each possible last prime, the sieve can choose any of the four prime
powers. Its modulus constrains only the three other exponents. The actual
four-prime congruence is proved in `FourCofactor245212.lean`. One integer
multiplication then tests a whole range of one exponent, one residue per
slot (`PackedResidues245212.lean`). Two finite geometric sums compute the
packed divisor sums directly (`ClosedPanel245212.lean`). All three arguments
pass the pinned kernel; the tree only invokes a new test where its estimated
cost is less than that of its original subtree.

```sh
python3 thin_tape_245212.py --block 88 --depth 4 --batch 13 --inverse --delta --broad --geometric --sieve-rate 0.10 --lean GeoCombined245212.lean
python3 assemble_four_h2_245212.py --tapes GeoCombined245212 --output GeoFull245212.lean
python3 forecast_four_245212.py GeoCombined245212.lean --groups 3 --width 8
```

The registered single-file front compiled. The matched (5,13) theorem passed
in 10.37 s (2,081.5 MiB), versus 16.17 s before the sieve. Checking three
separate 8-row samples in each family, including a measured 6.45 s startup
per file, took 34.74 s for (5,11), 15.05 s for (5,13), 12.54 s for (5,17),
10.78 s for (5,19), and 18.23 s for (7,11). The complete tape has 2,468
rows. The uniform (5,13) sample missed every exact-prefix tuple; the full
family has 164,098. Do not use those uniform samples to estimate total time.
The unchanged official checker did not finish: at 27 min 15.67 s the
11,264 MiB monitor stopped its Lean process, which had reached **11,530.2
MiB**. There was no compiler verdict on the theorem. The receipts are
`/private/tmp/oma-complete-four-h2-geometric10-{metrics,verdict}.json`.

The complete (5,7) support passed in 134.64 s, peak 5,522.1 MiB. The
official command writes temporary Lean inputs in the pinned checkout,
outside this task's writable workspace, so grant the scoped filesystem
permission when using the canonical checker.

## Fixed-width replay and exact-prefix sweep

The smaller proof tree leaves room to store every initial box and its
six-bit instructions directly. `DirectTape245212.lean` checks them
independently; no delta-chain reconstruction or rANS decoding is needed.
On the fixed (5,13) subtree the direct form took 8.60 s, versus 10.37 s
with the geometric-series tape. The 24-row (5,11) sample took 31.86 s.
With only the exact-prefix test omitted for diagnosis the latter took
11.43 s; omitting the congruence-panel test alone took 31.18 s.

`SweepPrefix245212.lean` uses the fact that, for fixed cofactor exponents,
both the numerator and denominator defining the last prime are affine in
its exponent. Their values can be advanced by addition. A checked pass
rejects every candidate outside the prime interval or failing divisibility.
The full exact test still runs if this pass is inconclusive. The 24 sampled
(5,11) rows covered 45,136 prospective exponents in 1,992 triples from
the wider prime intervals. The new rule and its standalone analytic front
passed the pinned kernel. Matched samples took 25.42 s at (5,11), 12.94 s
at (5,13) and 11.10 s at (5,17); startup 6.80 s.

```sh
python3 direct_tape_245212.py GeoCombined245212.lean SweepCombined245212.lean --rule SweepPrefix245212
python3 assemble_four_h2_245212.py --tapes SweepCombined245212 --output SweepFull245212.lean
python3 forecast_four_245212.py SweepCombined245212.lean --groups 3 --width 8
```

`SweepFull245212.lean` is 515,304 bytes, SHA-256
`10babb94bc7ab07da9458304d8619163353d44c8f1f8c2ea3b145d40bce8ac6b`.
Its entire (5,7) pilot passed in 91.72 s (3,857.6 MiB), versus 134.64 s
(5,522.1 MiB) for the geometric tape. The same individual (5,11) workload
was also tested with a tightened prime interval, primorial landmarks,
a shared exponent cap and an indexed sweep: none materially improved
on the addition-only sweep. Only the unmodified upstream checker can
issue its full receipt.

The independent compiled evaluator returned true on all 2,468 direct
rows. Reproduce it with
`python3 check_direct_rows_245212.py SweepCombined245212.lean /private/tmp/SweepSanity245212.lean`
and, in the pinned Lake environment with `/private/tmp` on `LEAN_PATH`,
`lean --run /private/tmp/SweepSanity245212.lean`.

## Workload-balanced single-file replay

In the (5,13) tree, lowering the maximum exact-prefix Cartesian product
from 100 triples to 32 reduces the estimated wide-interval exponent sweep
from 3,013,536 to 1,467,808 candidates. The new tree has 92,735 actual
prefix triples, versus 164,098. `work_ratio_245212.py` computes exact
tuple/instruction counts and estimates sweep cost using the middle tuple
of each box. Its independent 24-row samples each cover six strata and
match the whole-family counts; the earlier uniformly spaced samples do not.

```sh
python3 thin_tape_245212.py --block 88 --depth 4 --batch 13 --inverse --delta --broad --geometric --sieve-rate 0.10 --limit-513 32 --lean Short513Combined245212.lean
python3 direct_tape_245212.py Short513Combined245212.lean HybridSweep245212.lean --rule SweepPrefix245212 --closed-pages --coded-supports 5,13
python3 work_ratio_245212.py 7 --save /private/tmp/GeoWeights5_7.json
python3 work_ratio_245212.py 11 --save /private/tmp/GeoWeights5_11.json
python3 work_ratio_245212.py 13 --prefix-limit 32 --tapes HybridSweep245212.lean --save /private/tmp/SmallWeights5_13.json
python3 schedule_sweep_245212.py HybridSweep245212.lean BalancedHybrid245212.lean --target 250 --weights 5,7=/private/tmp/GeoWeights5_7.json 5,11=/private/tmp/GeoWeights5_11.json 5,13=/private/tmp/SmallWeights5_13.json
python3 assemble_four_h2_245212.py --tapes BalancedHybrid245212 --output BalancedHybridFull245212.lean
python3 check_four_h2_245212.py --source BalancedHybridFull245212.lean --limit-mib 10240 --label balancedhybrid32
```

`BalancedHybridFull245212.lean` is 520,262 bytes, SHA-256
`3353e6013c215b6fe045dc2cbf1b1224ef0260f8e5f4c4a7c09c160d6e3e1bc8`.
On a single file with the complete arithmetic front, tables and six
heavy check groups, Lean passed in 52.38 s at 2,967.4 MiB. The official
check began Nov 27 at 10:19 p.m. Pacific; the `balancedhybrid32` JSON
receipts report acceptance in 1,483.46 s, with no monitor stop and a
3,701.8 MiB peak. The preserved receipt at the top of this note contains
both JSON objects.

### Forward-decoded, dyadic fallback

`RankTape245212.lean` reads each action using the preceding action and an
eight-bit lookahead. There is no reverse decoder or intermediate raw word.
`rank_tape_245212.py` checks a full encoding–decoding round trip on every
row before writing the data. The kernel checks the decoded actions and the
two child boxes using `OMA.RankTape245212.close`, regardless of how the
generator chose its codes. This saved 27,505 bytes on the proof before
adding the exponent restriction. The same balanced (5,13) sample took
15.76 s (2,117.9 MiB), down from 17.89 s (2,196.0 MiB).

`ParitySweep245212.lean` uses the proven `16 ∣ (k+2)(e+2)(f+2)(g+2)` to
scan just one congruence class for the final exponent. `FastTopCap245212`
evaluates the frequently used fourth-exponent cut directly using the
established log table. The resulting frozen fallback is
`RankParityFull245212.lean`, 513,300 bytes, SHA-256
`ca3f97bfadce4708d79a409c2a0b44660ca3bdb60d44e8056b9453b937932ee7`.
Its full (5,7) check, including the complete single-file arithmetic and
all ten tables, passed in **80.98 s at 2,781.3 MiB**. The isolated prior
geometric and sweep (5,7) runs took 134.64 and 91.72 s, respectively.

To rebuild this family pilot, transcode `HybridSweep245212.lean` with
`python3 rank_tape_245212.py HybridSweep245212.lean RankParityTape245212.lean --rule ParitySweep245212`.
Run the schedule command above with `RankParityTape245212.lean` and
`BalancedRankParity245212.lean` as its two positional paths. Assemble
that module, then repeat the same schedule command with
`--stress RankParityFull245212.lean /private/tmp/RankParityFullPilot245212.lean --family 5,7`.
Use the pinned `lake env python3 …/profile_box_lean_245212.py /private/tmp/RankParityFullPilot245212.lean --max-mib 7000`.
The generalized progression lemma now in `ParitySweep245212.lean`
also accepts arbitrary offsets; the preserved 513,300-byte full source
is the exact revision measured by that pilot.

`OrderSweep245212.lean` further uses `DyadicPrefix245212.necessary` to
select at most one odd and one even arithmetic progression. Its soundness
proof covers arbitrary offsets, including the exact order-of-two case.
The matched (5,11) and (5,13) diagnostics took respectively 17.92 and
14.33 s, peaking at 2,473.1 and 1,805.5 MiB. At (5,11) the extra rule
barely moved the previous 17.93 s result, while at (5,13) it reduced
15.40 s to 14.33 s. A separate Python test applying the same restriction
to *whole* (5,13) boxes saved only 61 of 81,052 instructions and 1,144 of
92,735 prefix tuples (`python3 order_box_245212.py 13 --cap 32`); this
whole-box opcode is not included in the source.

The complete data and mathematical front with every tenth balanced checkpoint
also passed for the rank/order version: 354 of 2,964 rows, 9.49% of the
estimated cost, 149.73 s at 3,821.1 MiB. That was a timed sample; the complete
accepted H2 receipt uses the balanced hybrid layout identified at the top.

## Direct proof of the registered parent

The parent is `OeisA245212.conjecture.R1.H1.R1.H2.R1.H2`, from DomTheDeveloper’s
reduction [#3429](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3429).
The direct proof includes both the bounded and the unbounded largest-prime
cases, and does not import the pending reduction #17100. Its source is
`FourParent245212.lean`, also staged under the registered `proofs/` filename.
It is 519,143 bytes, SHA-256 `459273eba241725a2c731c1224e205b551283d67b08f05eccc8d3de2bdbcb2ab`.

For a largest prime at least 10¹⁸, the other prime bases are 3, 5, and one of
7, 11, 13. `Infinity245212.lean` bounds the possible last exponent on a box
of the three other exponents using 256-bit fixed-point interval arithmetic.
It splits the exponent interval with the largest weighted uncertainty, caches
the two unchanged intervals, and uses the exact cofactor identity at singleton
prefixes. This constructs the tree from its root, including unbounded initial
exponent intervals. The three trees contain 11,167, 27,023, and 104,281 nodes.

`InfinityJoin245212.lean` divides each tree into separately checked subtrees.
The only data stored for a subtree are its binary path from the root: adjacent
dyadic intervals allow sixteen such paths to share a single starting point.
Lean evaluates the numerical cuts and checks that the sibling pairs join back
to the original root. Python supplies the indexing data. The full three-tree
Lean replay finished in **90.62 s, 1,509.9 MiB**. Its predecessor reached the
6,400 MiB monitor threshold after 209.42 s while repeatedly reconstructing
function-valued exponent boxes. The fixed three-coordinate frame avoids that work.

```sh
python3 assemble_four_parent_245212.py --mode tail --output InfinityAll245212.lean
python3 assemble_four_parent_245212.py --mode interfaces --output ParentInterfaces245212.lean
python3 assemble_four_parent_245212.py --output FourParent245212.lean
python3 check_four_h2_245212.py --source FourParent245212.lean --target OeisA245212.conjecture.R1.H1.R1.H2.R1.H2 --limit-mib 8000 --label parentRankTail
```

The official linter accepts that exact registered ID. `--mode interfaces` checks
the final theorem with the exact finite row checks as inputs; the full source
proves all those inputs internally. The final official command accepted it,
reporting only `propext`, `Classical.choice`, and `Quot.sound`. The preserved
receipt includes the formal-conjectures pin and the checker and linter hashes.
