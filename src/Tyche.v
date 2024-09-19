Require Import State Test Checker Show.
From JSON Require Import Printer. 
Import ListNotations. Open Scope list_scope.
Set Warnings "-extraction".

Axiom tyche_output : string -> nat.
Extract Constant tyche_output =>
  "(fun l -> 
    let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 ""tyche.jsonl"" in
    let s = Bytes.create (List.length l) in
    let rec copy i = function
     | [] -> s
     | c :: l -> Bytes.set s i c; copy (i+1) l
    in 
    output_string oc (Bytes.to_string (copy 0 l));
    close_out oc;
    0)".

Definition create_json (name value : string)
           (features : list (string * (string + Z)))
           (st : State) (sr : SmallResult) :=
  let '(MkSmallResult ok expect reason interrupted stamp result_tag) := sr in
  let status :=
    match ok with
    | Some true => "passed"
    | Some false => "failed"
    | None => "gave_up"
    end in
  let features_json :=
    List.map (fun '(s, sz) =>
                match sz with
                | inl str => (s, JSON__String str)
                | inr z => (s, JSON__Number z)
                end) features in
  JSON__Object
    [ ("type", JSON__String "test_case")
    ; ("status", JSON__String status)
    ; ("status_reason", JSON__String "")
    ; ("representation", JSON__String value)
    ; ("arguments", JSON__Null)
    ; ("how_generated", JSON__String "")
    ; ("features", JSON__Object features_json)
    ; ("coverage", JSON__Null)
    ; ("property", JSON__String name)
    ; ("run_start", JSON__Number (start_time st))
    ].

Definition tyche {prop : Type} `{Checkable prop} (name value : string) : prop -> Checker :=
  callback
    (PostTest NotCounterexample
              (fun st sr =>
                 let j := create_json name value nil st sr in
                 tyche_output (to_string j ++ nl))).

Definition tyche_with_features {prop : Type} `{Checkable prop} (name value : string) (features : list (string * (string + Z))) : prop -> Checker :=
  callback
    (PostTest NotCounterexample
              (fun st sr =>
                 let j := create_json name value features st sr in
                 tyche_output (to_string j ++ nl))).
  
                                                                                        
