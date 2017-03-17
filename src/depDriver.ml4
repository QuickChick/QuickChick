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
open GenericLib
open SetLib
open CoqLib
open ArbitrarySizedST

type derivable =
    ArbitrarySizedSuchThat
  | ArbSizeSTMonotonic
  | ArbSizeSTSizeMonotonic
  | ArbSizeCorrect

let print_der = function
  | ArbitrarySizedSuchThat -> "ArbitrarySizedSuchThat"
  | ArbSizeSTMonotonic -> ""
  | ArbSizeSTSizeMonotonic -> ""
  | ArbSizeCorrect -> ""


(* Generic derivation function *)
let deriveDependent (cn : derivable) (c : constr_expr) nc (instance_name : string) =
  let n = parse_integer nc in
  let (ty_ctr, ty_params, ctrs, dep_type) = 
    match coerce_reference_to_dep_dt c with
    | Some dt -> msgerr (str (dep_dt_to_string dt) ++ fnl()); dt 
    | None -> failwith "Not supported type" in
  msgerr (str (string_of_int n) ++ fnl ());
  debug_coq_expr (gType ty_params dep_type);

  let input_types =
    let rec aux acc i = function
      | DArrow (dt1, dt2) 
      | DProd ((_,dt1), dt2) ->
        if i == n then (* i == n means this is what we generate for - ignore *) 
          aux acc (i+1) dt2
        else (* otherwise this needs to be an input argument *)
          aux (dt1 :: acc) (i+1) dt2
      | DTyParam tp -> acc
      | DTyCtr (c,dts) -> acc
      | DTyVar _ -> acc
    in List.rev (aux [] 1 dep_type) (* 1 because of using 1-indexed counting for the arguments *)       
  in

  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gTyParam ty_params in

  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  let input_names = List.mapi (fun i _ -> Printf.sprintf "input%d_" i) input_types in

  let forGen = "_forGen" in

  let params = List.map (fun tp -> gArg ~assumName:(gTyParam tp) ()) ty_params in
  let inputs = List.map (fun (n,t) -> gArg ~assumName:(gVar (fresh_name n)) ~assumType:(gType ty_params t) ()) (List.combine input_names input_types) in



  let class_name = match cn with
    | ArbitrarySizedSuchThat -> "ArbitrarySizedSuchThat"
    | ArbSizeSTMonotonic -> ""
    | ArbSizeSTSizeMonotonic -> ""
    | ArbSizeCorrect -> ""
  in

  (* TODO: These should be generated through some writer monad *)
  (* XXX Put dec_needed in ArbitrarySizedSuchThat *)
  let gen_needed = [] in
  let dec_needed = [] in

  let self_dec = [] in 
  (*     (* Maybe somethign about type paramters here *)
     if !need_dec then [gArg ~assumType:(gApp (gInject (Printf.sprintf "DepDec%n" (dep_type_len dep_type))) [gTyCtr ty_ctr]) 
                            ~assumGeneralized:true ()] 
     else [] in*)


  let arbitraries = ref ArbSet.empty in

  (* this is passed as an arg to arbitrarySizedST. Yikes! *)
  let register_arbitrary dt =
    arbitraries := ArbSet.add dt !arbitraries
  in

  (* Leo, I hate myself for doing this.... *)
  let gen_type = gGen (gOption (gType ty_params (nthType n dep_type))) in
  let gen = arbitrarySizedST ty_ctr dep_type gen_type ctrs input_names inputs n register_arbitrary (* XXX *) in 

  let arb_needed = 
    ArbSet.fold
      (fun dt acc ->
        (gArg ~assumType:(gApp (gInject "Arbitrary") [gType ty_params dt]) ~assumGeneralized:true ()) :: acc
      ) (!arbitraries) []
  in

  (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
  let instance_arguments = params
                         @ gen_needed
                         @ dec_needed
                         @ self_dec
                         @ arb_needed
                         @ inputs
  in

  (* The instance type *)
  let instance_type iargs = match cn with
    | ArbitrarySizedSuchThat ->
      gApp (gInject class_name)
        [gType ty_params (nthType n dep_type);
         gFun [forGen] (fun [fg] -> gApp (full_dt) (list_insert_nth (gVar fg) (List.map (fun n -> gVar (fresh_name n)) input_names) (n-1)))]
    | _ -> failwith "Unimplemented"
  in
  
  let instance_record iargs =
    (* Copying code for Arbitrary, Sized from derive.ml *)
    match cn with
    | ArbitrarySizedSuchThat -> gen
    | _ -> failwith "Unimplemented"
  in

  msgerr (str "Instance Type: " ++ fnl ());
  debug_coq_expr (instance_type [gInject "input0"; gInject "input1"]);
  declare_class_instance instance_arguments instance_name instance_type instance_record
;;


VERNAC COMMAND EXTEND DeriveArbitrarySizedSuchThat
  | ["DeriveArbitrarySizedSuchThat" constr(c) "for" constr(n) "as" string(s1)] -> [deriveDependent ArbitrarySizedSuchThat c n s1]
END;;
