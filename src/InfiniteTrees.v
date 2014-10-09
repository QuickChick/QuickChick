Require Import ssreflect.

CoInductive RandomGen : Type :=
| Node : bool -> RandomGen -> RandomGen -> RandomGen.

Definition rndSplit (s : RandomGen) :=
  match s with
  | Node b s1 s2 => (s1,s2)
  end.

Lemma rndSplitAssumption :
  forall s1 s2 : RandomGen, exists s, rndSplit s = (s1,s2).
Proof.
  move => s1 s2. by exists (Node true s1 s2).
Qed.
