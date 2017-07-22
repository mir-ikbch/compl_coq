(*i camlp4deps: "grammar/grammar.cma" i*)

open Genarg
open Constrarg
open Pp
let wit_ident_list = Genarg.wit_list Constrarg.wit_ident
(* let wit_reference = Constrarg.wit_ref *)
(*
let wit_constr_int = (Genarg.wit_pair Constrarg.wit_constr Constrarg.wit_int_or_var)
let constr_int = Pcoq.create_generic_entry "constr_int" (Genarg.rawwit wit_constr_int)
*)

let pr_constr_int _ _ _ (c, n) = str ""

type int_or_var = int Misctypes.or_var

let pr_ac _ _ _ x = str ""

ARGUMENT EXTEND ac
  TYPED AS constr * constr * constr
  PRINTED BY pr_ac
| [ "(" constr(f) "," constr(t) "," constr(s) ")" ] -> [ ((f, t), s) ]
END

ARGUMENT EXTEND constr_int
  TYPED AS constr * int_or_var
  PRINTED BY pr_constr_int
| [ "(" constr(c) "," int_or_var(n) ")"] -> [ (c, n) ]
END

let pr_ordered_const _ _ _ _ = str ""

ARGUMENT EXTEND ordered_const
  TYPED AS (constr * constr) * int_or_var
  PRINTED BY pr_ordered_const
| [ "(" constr(c0) "," constr(c) "," int_or_var(n) ")" ] -> [ ((c0, c), n) ]
END

DECLARE PLUGIN "compl_coq"
VERNAC COMMAND EXTEND Showp CLASSIFIED AS QUERY

| [ "Complete" ne_constr_list(l) ":" preident(db) "sigs" ne_constr_list(a) ] ->
  [ Compl.completion l false db a [] ]

| [ "Complete" ne_constr_list(l) "," "AC" ne_ac_list(acs) ":" preident(db) "sigs" ne_constr_list(a) ] ->
  [ Compl.completion l true db a acs ]
END

TACTIC EXTEND ordered_rewrite
  [ "ordered_rewrite" "[" constr_list(cs) "]" "sigs" ne_constr_list(l) ] -> [ Compl.ordered_rewrites cs l ]
| [ "srewrite" constr(c) "sigs" ne_constr_list(l) ] -> [ Compl.srewrite c l ]
| [ "autorewrite_ac" preident(db) "sigs" ne_constr_list(l) ] -> [ Compl.autorewrite_ac db l ]
| [ "congruence" "using" ne_constr_list(cs) ] -> [ Compl.congruence_using cs ]
END
