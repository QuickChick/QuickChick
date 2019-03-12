From QuickChick Require Import Classes GenLow GenHigh Instances Show.
Import GenLow GenHigh.

Require Export Coq.FSets.FMapInterface.
Require Export Coq.FSets.FMapWeakList.

Import MonadNotation.
Open Scope monad_scope.

(* Arbitrary, Show, and Fuzzy instances for standard library maps. *)

Module Type S (X : DecidableType).
  Include FMapInterface.WSfun X.

  Section elt.
    Variable elt : Type.
    Parameter from_list : list (X.t * elt) -> t elt.

    Declare Instance genSizedMap `{GenSized X.t} `{GenSized elt} : GenSized (t elt).
    Declare Instance shrinkMap `{Shrink X.t} `{Shrink elt} : Shrink (t elt).

    Declare Instance showMap `{Show X.t} `{Show elt} : Show (t elt).

    Declare Instance fuzzyMap `{GenSized X.t} `{GenSized elt} `{Fuzzy X.t} `{Fuzzy elt} : Fuzzy (t elt).

  End elt.

End S.

Module Make (X : DecidableType) <: S X.
  Include FMapWeakList.Make X.

  Section elt.
    Variable elt : Type.

    Definition from_list (l : list (X.t * elt)) : t elt :=
      List.fold_left (fun acc kv => add (fst kv) (snd kv) acc) l (empty elt).
  
    (* Generate two arbitrary vectors of the given sizefor keys and values,
       zip them together and build up into a map. *)
    Global Instance genSizedMap `{GenSized X.t} `{GenSized elt} : GenSized (t elt) :=
    {| arbitrarySized s := 
         keys <- vectorOf s (@arbitrarySized X.t _ s);;
         vals <- vectorOf s (@arbitrarySized elt _ s);;
         ret (from_list (combine keys vals))
    |}.

    (* The rest of the operations are derived from their list counterparts. *)
    Global Instance shrinkMap `{Shrink X.t} `{Shrink elt} : Shrink (t elt) :=
    {| shrink m := List.map from_list (shrink (elements m)) |}.

    Global Instance showMap `{Show X.t} `{Show elt} : Show (t elt) :=
    {| show m := show (elements m) |}.

    Global Instance fuzzyMap `{GenSized X.t} `{GenSized elt} `{Fuzzy X.t} `{Fuzzy elt} : Fuzzy (t elt) :=
    {| fuzz m :=
         m' <- fuzz (elements m);;
         ret (from_list m')
    |}.

  End elt.
End Make.

