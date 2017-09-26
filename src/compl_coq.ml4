(*i camlp4deps: "grammar/grammar.cma" i*)

open Genarg
open Constrarg
open Pp
let wit_ident_list = Genarg.wit_list Constrarg.wit_ident
(* let wit_reference = Constrarg.wit_ref *)

type int_or_var = int Misctypes.or_var

let pr_ac _ _ _ x = str ""

ARGUMENT EXTEND ac
  TYPED AS constr * constr * constr
  PRINTED BY pr_ac
| [ "(" constr(f) "," constr(t) "," constr(s) ")" ] -> [ ((f, t), s) ]
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
  [ Compl.completion l Compl.Normal db a [] ]

| [ "Complete" ne_constr_list(l) "," "AC" ne_ac_list(acs) ":" preident(db) "sigs" ne_constr_list(a) ] ->
  [ Compl.completion l Compl.Sorting db a acs ]

| [ "OComplete" ne_constr_list(l) ":" preident(db) "sigs" ne_constr_list(a) ] ->
  [ Compl.completion l Compl.Ordered db a [] ]
END

TACTIC EXTEND autorewrite_ac
| [ "autorewrite_ac" preident(db) "sigs" ne_constr_list(l) ] -> [ Compl.autorewrite_ac db l ]
END

TACTIC EXTEND ordered_autorewrite
| ["ordered_rewrite" constr(c) "sigs" ne_constr_list(l) ] -> [ Compl.ordered_rewrite Locus.AllOccurrences l c ]
| ["ordered_autorewrite" preident(db) "sigs" ne_constr_list(l) ] -> [ Compl.ordered_autorewrite db l ]
END
