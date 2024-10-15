type derivable =
    Shrink
  | Show
  | GenSized
  | Sized
  | EnumSized
  | Nullary
val derivable_to_string : derivable -> string
val mk_instance_name : derivable -> string -> string
val repeat_instance_name : derivable -> string -> string
val derive :
  derivable -> Constrexpr.constr_expr -> string -> string -> string -> unit
