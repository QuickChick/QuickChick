# STLC live demo in Emacs

For the talk, run:

```sh
./open-demo.sh
```

The launcher evaluates the `rocq-rewrite` opam environment, opens a dedicated maximized Emacs frame, enlarges every Proof General pane, and stops immediately before `Theorem preservation`. Press `C-c C-n` to step through the theorem, `Proof.`, and `quickchick.`.

To use a different switch, set `QUICKCHICK_DEMO_SWITCH`, for example:

```sh
QUICKCHICK_DEMO_SWITCH=my-switch ./slides/testing_theorems_svg_storyboard_v2/testing_theorems_svg_storyboard_v2/demo/open-demo.sh
```

The two premises, `typing [] e t` and `Step e e'`, are inductive. A local `_CoqProject` points Proof General to the built QuickChick libraries.

After the result, reveal the mutation: `shift` fails to increment its cutoff under `Abs`. The intended branch uses `go (1 + cutoff)%Z body`. Finding this requires reduction with capture-avoiding substitution under a binder.
