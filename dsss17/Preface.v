(** * Preface *)

(** QuickChick is a clone of Haskell's property-based random testing
    tool, QuickCheck, with a number of Coq-specific extensions.  These
    tutorial notes introduce the basic concepts of random testing and
    show how to use both basic and advanced features of QuickChick. 

    Why a random-testing tool for a proof assistant?

    It is not uncommon during a verification project to spend many
    hours attempting to prove a slightly false theorem, only to result
    in frustration when the mistake is realized and one needs to start
    over. Other theorem provers have testing tools to quickly find
    counterexamples before embarking on the work of a formal proof.
    Isabelle has its own QuickCheck clone, as well as Nitpick and a
    variety of other tools. ACL2 goes a step further, using random
    testing to facilitate automation. QuickChick is meant to fill this
    role in the Coq ecosystem. *)

(** ** Installation *)

(* NOW: Detailed installation instructions... *)
