(* Compiled Rocq scoring policies, registered by the modules PolicyLoader
   compiles and loads. A policy's score type is its own; the plugin holds its
   scores as opaque values and only compares them with the policy's own
   comparison. *)

type score = Obj.t

type compiled = {
  score : score PolicyViews.score_context -> PolicyViews.schedule_view -> score;
  compare : score -> score -> PolicyViews.comparison;
  bound : score PolicyViews.score_context -> score PolicyViews.search_node_view -> score;
}

let table : (string, compiled) Hashtbl.t = Hashtbl.create 4

let register key policy = Hashtbl.replace table key policy

let find key = Hashtbl.find_opt table key
