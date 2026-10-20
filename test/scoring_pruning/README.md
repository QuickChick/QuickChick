Build the local plugin with `dune build --build-dir _build-validated @install`,
then run `python3 test/scoring_pruning/check.py` with the local `coqc` on `PATH`.
The script passes an explicit `-I` to avoid loading an older installed plugin.

`QC_SCHEDULE_SCORE_PRUNING=verify` enumerates every candidate and checks each
prefix bound against its completed descendants. It also compares leaf scores
obtained during search with the final candidate scores. Setting the variable
to `1` enables strict pruning. Both are internal experiments; unset is the
unchanged public behavior.

The three-premise fixture has four unpruned root candidates. Under both the
default and counted-density rankings, the bounded run scores one and keeps
the same winner. The script also verifies the connected mutual-cycle fixture.
The added floor counts unprocessed positive hypotheses whose variables are
already bound, since they can only become checks. The typed scheduler test
checks that count against every descendant of exhaustive and nested cases.
These cases are evidence for the adapter, not a proof for every typed source
rewrite or proof context.

`python3 test/scoring_pruning/check_semgus.py` runs a reduced version of
`examples/Sygus.v` with `eval` merged with itself twice. It compares the
ordinary, comparable `baseline`, verified, and pruned runs using the local
plugin. `baseline` activates the same scheduler and candidate-isolated scoring
as pruning without calculating bounds. The test also runs `baseline` with
`QC_SCHEDULE_REUSE_STABLE=0` to compare cold scoring against shared completed
dependencies and step-multiset grades. The ordinary diagnostic shares
dependency memo state across candidates and is faster, so its timing is not
a like-for-like pruning comparison. The diagnostic
has 12 root candidates over 25 prefixes. The root verifier runs directly,
selection is unchanged across modes, and the bound makes no cuts: all 12
candidates have the same scored density, histogram, and variable uses. Score probes
suspend nested experimental pruning to avoid re-entering dependency searches.
The verifier records each leaf with the internal `QC_SCHEDULE_TRACE_BOUNDS=1`
trace and asserts that exact tie.
The fixture checks the merged relation's ten-argument type and constructs a
single expression `X` that evaluates under three distinct input pairs.
Pruned ranking reuses completed-leaf scores and rescores only the winner to
recover its dependency memo. Verification keeps an independent final rescore
and checks repeated step-multiset grades. Cycle-dependent entries are never
shared merely by their dependency key.
The legacy `Merge` command emits a large debug log, so this test captures its
output in temporary files. This is a stress test for bound correctness, and
currently exposes the cost of cold recursive scoring and the gain from reuse.
