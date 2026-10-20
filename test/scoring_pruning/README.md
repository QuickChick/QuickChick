Build the local plugin with `dune build --build-dir _build-validated @install`,
then run `python3 test/scoring_pruning/check.py` with the local `coqc` on `PATH`.
The script passes an explicit `-I` to avoid loading an older installed plugin.

`QC_SCHEDULE_SCORE_PRUNING=verify` enumerates every candidate and checks each
prefix bound against its completed descendants. It also compares leaf scores
obtained during search with the final candidate scores. Setting the variable
to `1` enables strict pruning. Both are internal experiments; unset is the
unchanged public behavior.

The three-premise fixture has four unpruned root candidates. Under both the
default and counted-density rankings, the bounded run scores three and keeps
the same winner. The script also verifies the connected mutual-cycle fixture.
These cases are evidence for the adapter, not a proof for every typed source
rewrite or proof context.

`python3 test/scoring_pruning/check_semgus.py` runs a reduced version of
`examples/Sygus.v` with `eval` merged with itself twice. It compares the
unpruned, verified, and pruned runs using the local plugin. The diagnostic
has 12 root candidates. Selection is unchanged across modes, while pruning
cuts search in recursive dependencies. `Valid Schedules` does not emit a pruning
trace for the root diagnostic. The legacy `Merge` command emits a large
debug log, so this test captures its output in temporary files. It is a
stress test for bound correctness; it does not establish a speedup.
