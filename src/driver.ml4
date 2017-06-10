open Pp
open Loc
open Names
open Extract_env
open Tacmach
open Entries
open Declarations
open Declare
open Libnames
open Util
open Constrintern
open Topconstr
open Constrexpr
open Constrexpr_ops
open Decl_kinds
open Names
open GenericLib
open SetLib
open CoqLib
open Sized
open SizeMon
open SizeSMon
open SizeCorr
open Constrarg
open Error

type derivation = SimpleDer of SimplDriver.derivable list
                | DepDer of DepDriver.derivable 

let simpl_dispatch ind classes name1 name2 = 
  let ind_name = match ind with 
    | CRef (r, _) -> string_of_qualid (snd (qualid_of_reference r))
    | _ -> failwith "Implement me for functions" 
  in
  List.iter (fun cn -> SimplDriver.derive cn ind (SimplDriver.mk_instance_name cn ind_name) name1 name2) classes

let dep_dispatch ind class_name = 
  (* TODO: turn this into a much once Zoe figures out what she wants *)
  (* let DepDriver.ArbitrarySizedSuchThat = class_name in  *)
  match ind with 
  | CLambdaN (_loc1, [([(_loc2, Name id)], _kind, _type)], CApp (_loc3, (_flag, constructor), args)) ->
    let n = fst (List.find (fun (_,(CRef (r,_), _)) -> Id.to_string id = string_of_reference r) (List.mapi (fun i x -> (i+1,x)) args)) in
     let ctr_name = 
       match constructor with 
       | CRef (r,_) -> string_of_reference r
     in 
     DepDriver.deriveDependent class_name constructor n (DepDriver.mk_instance_name class_name ctr_name)
  | _ -> failwith "wrongformat"

let dispatch cn ind name1 name2 = 
  let convert_reference_to_string c = 
    match c with 
    | CRef (r, _) -> string_of_qualid (snd (qualid_of_reference r))
    | _ -> failwith "Usage: Derive <class_name> for <inductive_name> OR  Derive (<class_name>, ... , <class_name>) for <inductive_name>" in
  let ss = match cn with 
     | CNotation (_,_,([a],[b],_)) -> begin 
         let c = convert_reference_to_string a in
         let cs = List.map convert_reference_to_string b in
         c :: cs
       end
     | _ -> [convert_reference_to_string cn]
  in 

  let get_class_names = function
    | "Arbitrary" -> SimpleDer [SimplDriver.GenSized; SimplDriver.Shrink]
    | "Show" -> SimpleDer [SimplDriver.Show]
    | "Sized" -> SimpleDer [SimplDriver.Sized]
    | "CanonicalSized" -> SimpleDer [SimplDriver.CanonicalSized]
    | "SizeMonotonic" -> SimpleDer [SimplDriver.SizeMonotonic]
    | "SizedMonotonic" -> SimpleDer [SimplDriver.SizedMonotonic]
    | "SizedCorrect" -> SimpleDer [SimplDriver.SizedCorrect]
    | "ArbitrarySizedSuchThat" -> DepDer DepDriver.ArbitrarySizedSuchThat
    | "SizeMonotonicSuchThat" -> DepDer DepDriver.GenSizedSuchThatMonotonic
    | "SizedProofEqs" -> DepDer DepDriver.SizedProofEqs
    | "GenSizedSuchThatCorrect" -> DepDer DepDriver.GenSizedSuchThatCorrect
  in

  let class_names = 
    match ss with 
    | s::ss -> List.fold_left (fun der s ->
                               match der, get_class_names s with 
                               | SimpleDer ds1, SimpleDer ds2 -> SimpleDer (ds1 @ ds2)
                               | DepDer ds1, DepDer ds2 -> 
                                  qcfail "Implement dependent derive for multiple classes"
                              ) (get_class_names s) ss
    | _ -> qcfail "At least one class name expected" in

  match class_names with 
  | SimpleDer classes -> simpl_dispatch ind classes name1 name2
  | DepDer classes -> dep_dispatch ind classes 

VERNAC COMMAND EXTEND Derive CLASSIFIED AS SIDEFF
   | ["Derive" constr(class_name) "for" constr(inductive)] -> 
     [dispatch class_name inductive "" ""]
   | ["Derive" constr(class_name) "for" constr(inductive) "using" ident(genInst)] -> 
     [dispatch class_name inductive (Names.string_of_id genInst) ""]
   | ["Derive" constr(class_name) "for" constr(inductive) "using" ident(genInst) "and" ident(monInst) ] -> 
     [dispatch class_name inductive (Names.string_of_id genInst) (Names.string_of_id monInst)]
END;;

(*

VERNAC COMMAND EXTEND DeriveArbitrarySized
  | ["DeriveArbitrarySized" constr(c) "as" string(s1)] -> [derive ArbitrarySized c s1 "aux" ""]
END;;

VERNAC COMMAND EXTEND DeriveSized
  | ["DeriveSized" constr(c) "as" string(s1)] -> [derive Sized c s1 "aux" ""]
END;;

VERNAC COMMAND EXTEND DeriveCanonicalSized
  | ["DeriveCanonicalSized" constr(c) "as" string(s1)] -> [derive CanonicalSized c s1 "aux" ""]
END;;

VERNAC COMMAND EXTEND DeriveArbitrarySizedMonotonic
  | ["DeriveArbitrarySizedMonotonic" constr(c) "as" string(s1) "using" string(s2)] ->
  (* s2 is the instance name for ArbitrarySized *)
    [derive SizeMonotonic c s1 s2 ""]
END;;

VERNAC COMMAND EXTEND DeriveArbitrarySizedSizeMonotonic
  | ["DeriveArbitrarySizedSizeMonotonic" constr(c) "as" string(s1)] ->
    [derive SizeSMonotonic c s1 "" ""]
END;;


VERNAC COMMAND EXTEND DeriveArbitrarySizedCorrect
  | ["DeriveArbitrarySizedCorrect" constr(c) "as" string(s1) "using" string(s2) "and" string(s3)] ->
    [derive GenSizeCorrect c s1 s2 s3]
END;;
 *)
