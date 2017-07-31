open Constr
open Locus
open Names
open Rewrite
open Autorewrite
open Proofview.Notations
open Pp
open Pretype_errors

(* find Coq references *)
let make_dir l = DirPath.make (List.rev_map Id.of_string l)

let try_find_global_reference dir s =
  let sp = Libnames.make_path (make_dir ("Coq"::dir)) (Id.of_string s) in
    try Nametab.global_of_path sp
    with Not_found -> 
      Errors.anomaly (str "Global reference " ++ str s ++ str " not found in generalized rewriting")

let find_reference dir s () =
  try_find_global_reference dir s

let find_global dir s =
  let gr = lazy (try_find_global_reference dir s) in
    fun (evd,cstrs) -> 
      let evd, c = Evarutil.new_global evd (Lazy.force gr) in
	(evd, cstrs), c

let sigP = find_global ["Init"; "Specif"] "sig"
let proj1_sig evd = find_global ["Init"; "Specif"] "proj1_sig" (evd, Evar.Set.empty)
let proj2_sig evd = find_global ["Init"; "Specif"] "proj2_sig" (evd, Evar.Set.empty)

let flip_coq = find_global ["Program"; "Basics"] "flip"
let const_coq = find_global ["Program"; "Basics"] "const"

let filter b xs = List.fold_left (fun res x -> if b x then x :: res else res) [] xs


(* [add_rewrite_hint env siga bases ort t lcsr loc] adds [lcsr] to the rewrite hintDBs [bases]
 * with rewrite direction [ort], a tactic [t] and a location [loc] *)
let add_rewrite_hint env sigma bases ort t lcsr loc =
  let poly = Flags.use_polymorphic_flag () in
  let f c = 
    let ctx = Evd.evar_universe_context sigma in
    let ctx =
      let ctx = Evd.evar_universe_context_set Univ.UContext.empty ctx in
      if poly then ctx
              else (Global.push_context_set false ctx; Univ.ContextSet.empty)
    in
    loc, (c, ctx), ort, t
  in
  let eqs = List.map f lcsr in
  let add_hints base = add_rew_rules base eqs in
  List.iter add_hints bases


type compare = Eq | Lt | Gt | Nc

module SC = Set.Make(struct
                      type t = constr
                      let compare = compare
                     end)

let rec subterms c =
  match kind c with
  | App (c', args) -> SC.add c' (Array.fold_left SC.union (SC.empty) (Array.map subterms args))
  | _ -> SC.singleton c

let rec size c =
  match kind c with
  | App (c', args) -> 1 + Array.fold_left (fun res x -> res + size x) 0 args
  | _ -> 1

(* orders *)
let rec ord_of_list equiv l x y =
  if equiv x y then Eq else
    match l with
    | [] -> Nc
    | z::l' -> if equiv x z then Lt else if equiv y z then Gt else ord_of_list equiv l' x y

let rec lex ord cs1 cs2 =
  match cs1, cs2 with
  | [], [] -> Eq
  | _, [] -> Gt
  | [], _ -> Lt
  | c1::cs1', c2::cs2' ->
      match ord c1 c2 with
      | Eq -> lex ord cs1' cs2'
      | o -> o

(* lexicographic recursive path order with weight [l] *)
let rec lex_pathord l c1 c2 = if equal c1 c2 then Eq else
  match kind c1, kind c2 with
  | Evar _, Evar _ -> Nc
  | _, Evar _ -> if SC.mem c2 (subterms c1) then Gt else Nc
  | Evar _, _ -> if SC.mem c1 (subterms c2) then Lt else Nc
  | Const _, Const _ -> ord_of_list equal l c1 c2
  | Var _, Var _ -> ord_of_list equal l c1 c2
  | App (c1', args1), App (c2', args2) ->
      if Array.exists (fun a -> let o = lex_pathord l a c2 in o = Gt || o = Eq) args1
        then Gt
        else if Array.exists (fun a -> let o = lex_pathord l c1 a in o = Lt || o = Eq) args2
          then Lt
          else (match ord_of_list equal l c1' c2' with
               | Gt -> if Array.for_all (fun a -> lex_pathord l c1 a = Gt) args2
                          then Gt else Nc
               | Lt -> if Array.for_all (fun a -> lex_pathord l a c2 = Lt) args1
                          then Lt else Nc
               | Eq -> lex (lex_pathord l) (Array.to_list args1) (Array.to_list args2)
               | Nc -> Errors.error "unknown signature\n")
  | _, App (c2', args) -> if Array.exists (fun a -> let o = lex_pathord l c1 a in o = Lt || o = Eq) args then Lt else
      (match ord_of_list equal l c1 c2' with
      | Lt -> Lt
      | Gt -> if Array.for_all (fun a -> lex_pathord l c1 a = Gt) args
                then Gt else Nc
      | Eq -> Lt
      | Nc -> Errors.error "unknown signature\n")
  | App (c1', args), _ -> if Array.exists (fun a -> let o = lex_pathord l a c2 in o = Gt || o = Eq) args then Gt else
      (match ord_of_list equal l c1' c2 with
      | Gt -> Gt
      | Lt -> if Array.for_all (fun a -> lex_pathord l a c2 = Lt) args
                then Lt else Nc
      | Eq -> Gt
      | Nc -> Errors.error "unknown signature\n")
  | _, _ -> Nc


(* conversion from [constr] into [Tacexpr.glob_constr_and_expr] *)
let extern_constr_to_glob b env evd c =
  let cexpr = Constrextern.extern_constr b env evd c in
  let gexpr = Tacintern.intern_constr {ltacvars=Names.Id.Set.empty; genv=env} cexpr in
  gexpr

(* core unification flags (used for [Unification.w_unify] and its variants) which does not allow
 * beta/iota/delta/eta conversion *)
let compl_default_core_unify_flags () = { (Unification.default_core_unify_flags ()) with
  modulo_delta = Names.empty_transparent_state;
  modulo_delta_types = Names.empty_transparent_state;
  modulo_betaiota = false;
  modulo_eta = false;
}

let compl_default_unify_flags () =
  let f = compl_default_core_unify_flags () in
  { (Unification.default_unify_flags ()) with
    core_unify_flags = f;
    merge_unify_flags = f;
    subterm_unify_flags = f;
  }

(* same as [compl_default_core_unify_flags] but freezes the evars in [c] *)
let compl_default_core_unify_flags_with_freeze c () = { (Unification.default_core_unify_flags ()) with
  modulo_delta = Names.empty_transparent_state;
  modulo_delta_types = Names.empty_transparent_state;
  frozen_evars = Evd.evars_of_term c;
  modulo_betaiota = false;
  modulo_eta = false;
}

let compl_unify_flags_with_freeze c () =
  let f = compl_default_core_unify_flags_with_freeze c () in
  { (Unification.default_unify_flags ()) with
    core_unify_flags = f;
    merge_unify_flags = f;
    subterm_unify_flags = f;
  }

let hyp_from hinfo =
  if hinfo.hyp_l2r then hinfo.hyp_left else hinfo.hyp_right

let hyp_to hinfo =
  if hinfo.hyp_l2r then hinfo.hyp_right else hinfo.hyp_left


(* In the whole completion procedure here, we treat variables in the sense of TRS as evars of [constr].
 * Unification between two terms is done by [Unification.w_unify] (or its variants).
 * To handle rewrite rules [forall x1 x2 ... xn, equiv l r] with their additional information like
 * proof terms or which (setoid) relation is used, [Autorewrite.hypinfo] works. *)
(* [overlaps env evd hinfo1 hinfo2] returns a list of pairs of [ev] and [c];
 * [c] is a subterm of the left hand side of [hinfo2] which unify to the left hand side of [hinfo1] with [evar_map] [ev].
 * The pairs whose [c] is a single evar are excluded since they are redundant in the completion procedure. *)
let overlaps env evd hinfo1 hinfo2 =
  let open Evarutil in
  let ovlps = try Unification.w_unify_to_subterm_all env evd ~flags:(compl_default_unify_flags ()) (hinfo2.hyp_left, hinfo1.hyp_left)
    with PretypeError (_, _, NoOccurrenceFound _) -> [] in
  let ovlps = filter (fun (ev,c) ->
    match kind c with
    | Evar _ -> false
    | _ -> true)
    ovlps
  in
  ovlps

(* [crit_pairs env evd hinfo1 hinfo2 rule] returns a list of 7-ples [(x, c, c1, c2, hinfo1, hinfo2, rule)] with
 * following properties:
 * - [x] is an evar map obtained by [overlaps],
 * - [c] is the constr which is obtained by normalizing the left hand side of [hinfo1] with [x],
 * - The pair of [c1] and [c2] is a critical pair between [hinfo1] and [hinfo2] obtained by [x].
 * [rule] must be a proof term of [hinfo2.hyp_ty].
 * This function is used mainly for [critical_pairs]. *)
let crit_pairs env evd hinfo1 hinfo2 rule =
  let ovlps = overlaps env evd hinfo1 hinfo2 in
  let c ev = Evarutil.nf_evar ev (hyp_from hinfo1) in
  let c1 ev = Evarutil.nf_evar ev (hyp_to hinfo1) in
  let c2 (ev, t) = Evarutil.nf_evar ev (Termops.replace_term t hinfo2.hyp_right hinfo1.hyp_left) in
  List.fold_left (fun res (x, y) -> 
    let c1 = c1 x in
    let c2 = c2 (x, y) in
    if equal c1 c2 then res else (x, c x, c1, c2, hinfo1, hinfo2, rule) :: res) [] ovlps
 

(* [abstract_scheme prod env (locc, a) (c, sigma)] returns [forall x, c[x/a] ] if [prod] is true
 * and returns [fun x => c[x/a] ] if not. Here, [c[x/a]] means the term which is obtained by
 * replacing [a] with [x] in [c] at occurrences [locc]. *)
let abstract_scheme prod env (locc, a) (c, sigma) =
  let ta = Retyping.get_type_of env sigma a in
  let na = Namegen.named_hd env ta Anonymous in
  let mk = if prod then mkProd else mkLambda in
  if Termops.occur_meta ta then Errors.error "Cannot find a type for the generalisation.";
  if Termops.occur_meta a then
    mk (na,ta,c), sigma
  else
    let c', sigma' = Find_subterm.subst_closed_term_occ env sigma (AtOccs locc) a c in
    mk (na,ta,c'), sigma'

let evars_to_fun env evd c =
  let evars = Evd.evars_of_term c in
  Evar.Set.fold (fun evar (res, sigma) -> abstract_scheme false env (AllOccurrences, mkEvar (evar, [||])) (res, sigma)) evars (c, evd)

let evars_to_prod env evd ty =
  let evars = Evd.evars_of_term ty in
  Evar.Set.fold (fun evar (res, sigma) -> abstract_scheme true env (AllOccurrences, mkEvar (evar, [||])) (res, sigma)) evars (ty, evd)

let evars_to_prod_list env evd ty =
  let evars = Evd.evar_list ty in
  List.fold_left (fun (res, sigma) evar -> abstract_scheme true env (AllOccurrences, mkEvar evar) (res, sigma)) (ty, evd) evars,
  List.rev_map (fun evar -> mkEvar evar) evars

let make_eq_statement env evd equiv eqfrom eqto =
  let eq_with_evar = mkApp (equiv, [|eqfrom; eqto|]) in
  evars_to_prod env evd eq_with_evar

let make_sig_eq env evd equiv c =
  let ty = Retyping.get_type_of env evd c in
  let name = Namegen.named_hd env ty Anonymous in
  let eq = mkLambda (name, ty, mkApp (equiv, [|c; mkRel 1|])) in
  evars_to_prod_list env evd (mkApp (snd (sigP (evd, Evar.Set.empty)), [|ty; eq|]))

let make_sig_eq_with env evd equiv c c' =
  let ty = Retyping.get_type_of env evd c in
  let name = Namegen.named_hd env ty Anonymous in
  let cwith = mkApp (snd (flip_coq (evd, Evar.Set.empty)), [|ty; ty; ty; mkApp (snd (const_coq (evd, Evar.Set.empty)), [|ty; ty|]); c'; c|]) in
  let eq = mkLambda (name, ty, mkApp (equiv, [|cwith; mkRel 1|])) in
  evars_to_prod_list env evd (mkApp (snd (sigP (evd, Evar.Set.empty)), [|ty; eq|]))

let unshelve t = 
  Proofview.with_shelf t >>= fun (gls, ()) ->
  Proofview.Unsafe.tclGETGOALS >>= fun ogls ->
  Proofview.Unsafe.tclSETGOALS (gls @ ogls)


let pt_of_rew_proof = function
  | RewPrf (_, p) -> p
  | RewCast _ -> Errors.error "???"

let destLambdas c =
  let rec aux c vars =
    if Term.isLambda c
    then let n,t,c' = Term.destLambda c in aux c' ((n, t)::vars)
    else c, vars
  in
  aux c []

let prod_sig_to_prod env c =
  let c', vars = destLambdas c in
  let p1, p2 =
    match kind c' with
    | App (cc, args) -> if Term.isConstruct cc then args.(2), args.(3) else Errors.error "Not a constructor"
    | _ -> Errors.error "Not an application"
  in
  List.fold_left (fun (c1, c2) (n,t) -> mkLambda (n,t,c1), mkLambda (n,t,c2)) (p1, p2) vars

let congruence_using cs =
  List.fold_left (fun tac c -> tac <*> Tactics.pose_proof Name.Anonymous c) (Proofview.tclUNIT()) cs
  <*> Cctac.congruence_tac 1000 []

let congruence_using_tac cs =
  Proofview.Goal.nf_enter begin fun gl ->
    let cs = List.rev_map (fun c -> fst (Tacmach.New.pf_apply (fun env evd c -> Constrintern.interp_constr env evd c) gl c)) cs in
    congruence_using cs
  end

let ordered_rewrite c ord =
  let open Evarutil in
  Proofview.Goal.nf_enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let hinfo = Tacmach.New.pf_apply (find_applied_relation false Loc.ghost) gl c true in
    let w_unify_to_subterm_all = Unification.w_unify_to_subterm_all hinfo.hyp_cl.env ~flags:(compl_unify_flags_with_freeze concl ()) hinfo.hyp_cl.evd in
    let evs = try
                w_unify_to_subterm_all (hinfo.hyp_left, concl)
              with PretypeError (_, _, NoOccurrenceFound _) -> []
    in
    let rec tac = function
      | [] -> Tacticals.New.tclIDTAC
      | (ev,_)::rest ->
        match ord (nf_evar ev hinfo.hyp_left) (nf_evar ev hinfo.hyp_right) with
        | Gt -> Equality.rewriteLR (nf_evar ev hinfo.hyp_prf)
        | _ -> tac rest
    in
    tac evs
  end

let ordered_rewrites cs weights =
  Tacticals.New.tclTHENLIST (List.map (fun c -> ordered_rewrite c (lex_pathord weights)) cs)

let ordered_autorewrite_core rules ord =
  Tacticals.New.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (List.fold_left (fun tac rule ->
        Tacticals.New.tclTHEN tac
          (ordered_rewrite rule ord))
        (Proofview.tclUNIT()) rules))

let ordered_autorewrite base ord =
  let rules = List.rev_map (fun x -> x.rew_lemma) (find_rewrites base) in
  ordered_autorewrite_core rules ord 


let rec var_list c = match kind c with
  | Evar _ -> [c]
  | Var _ -> [c]
  | App (f, args) -> var_list f @ List.concat (Array.to_list (Array.map var_list args))
  | _ -> []

let varlex c1 c2 =
  let v1 = var_list c1 in
  let v2 = var_list c2 in
  lex (ord_of_list equal v1) v1 v2

let orderable c1 c2 ord = ord c1 c2 = Gt || ord c1 c2 = Lt

let orderable_rule ?(env=Global.env ()) ?(evd=Evd.from_env env) rew ord =
  let hinfo = find_applied_relation false Loc.ghost env evd rew true in
  orderable hinfo.hyp_left hinfo.hyp_right ord

let rewrite_with_sorting occs ord c =
  Proofview.Goal.nf_enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    if Tacmach.New.pf_apply (fun env evd -> orderable_rule ~env:env ~evd:evd) gl c ord
      then Equality.rewriteLR c
      else
        let hinfo = Tacmach.New.pf_apply (find_applied_relation false Loc.ghost) gl c true in
        let unifs = 
          try
            Unification.w_unify_to_subterm_all hinfo.hyp_cl.env hinfo.hyp_cl.evd
              ~flags:(compl_unify_flags_with_freeze concl ()) (hinfo.hyp_left, concl)
          with PretypeError (_, _, NoOccurrenceFound _) -> []
        in
        let rec aux = function
          | [] -> Tacticals.New.tclFAIL 0 (str "Nothing to rewrite")
          | (ev,_)::rest -> if lex (ord_of_list equal (var_list concl)) (var_list (Evarutil.nf_evar ev hinfo.hyp_left)) (var_list (Evarutil.nf_evar ev hinfo.hyp_right)) = Gt
                          then Equality.rewriteLR (Evarutil.nf_evar ev hinfo.hyp_prf)
                          else aux rest
        in
        aux unifs
  end

let srewrite c l =
  rewrite_with_sorting AllOccurrences (lex_pathord l) c

let autorewrite_ac base l =
  Tacticals.New.tclREPEAT (
    (List.fold_left (fun tac rew ->
      Tacticals.New.tclTHEN tac
        (Tacticals.New.tclORELSE (srewrite rew.rew_lemma l) Tacticals.New.tclIDTAC))
      (Proofview.tclUNIT()) (find_rewrites base)))

let raw_srewrites ord cs =
  Tacticals.New.tclREPEAT (
    (List.fold_left (fun tac rule ->
      Tacticals.New.tclTHEN tac
        (Tacticals.New.tclORELSE (rewrite_with_sorting AllOccurrences ord rule) Tacticals.New.tclIDTAC))
      (Proofview.tclUNIT()) cs))

let rewrites cs =
  Tacticals.New.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (List.fold_left (fun tac rule ->
      Tacticals.New.tclTHEN tac
        (Equality.rewriteLR rule <+> Tacticals.New.tclIDTAC))
      (Proofview.tclUNIT()) cs))

let teq env evd c1 c2 =
  try let _ = Unification.w_unify env evd Reduction.CONV ~flags:(compl_unify_flags_with_freeze c1 ()) c1 c2 in true
  with PretypeError (_, _, CannotUnify _) -> false

let rewrite_fun env evd scompl ord c rule =
  let h = find_applied_relation false Loc.ghost env evd rule true in
  let env = h.hyp_cl.env in
  let evd = h.hyp_cl.evd in
  let ovlps = try Unification.w_unify_to_subterm_all env ~flags:(compl_unify_flags_with_freeze c ()) evd (h.hyp_left, c)
          with PretypeError (_, _, NoOccurrenceFound _) -> [] in
  let rec aux = function
    | [] -> c
    | (ev,t)::rest ->
        let c' = 
          Evarutil.nf_evar ev (Termops.replace_term t h.hyp_right c) in
        if orderable_rule rule ord || not scompl then
          c' else
          if varlex c c' = Gt then c' else aux rest
  in
  aux ovlps

let rec reduce_fun env evd scompl ord c rules =
  let c' = List.fold_left (fun res rule -> rewrite_fun env evd scompl ord res rule) c rules in
  if equal c c' then c' else reduce_fun env evd scompl ord c' rules

let proofterm_of_cp c c1 c2 hinfo1 hinfo2 rule ord scompl basename rews =
  let env = hinfo2.hyp_cl.env in
  let evd = hinfo2.hyp_cl.evd in
  let equiv = hinfo1.hyp_rel in

  let env' = Global.env () in
  let evd' = Evd.from_env env' in
  let evd' = Evd.fold_undefined (fun ev evi res -> 
    if Evd.mem res ev then res else Evd.add res ev evi) evd evd' in
  let eqred = reduce_fun env' evd' scompl ord (mkApp (equiv, [|c1; c2|])) rews in
  let c1', c2' =
    match kind eqred with
    | App (_, args) -> args.(1), args.(2)
    | _ -> Errors.error "error"
  in
  let r = equal c1' c2' || (List.length (var_list c1') = List.length (var_list c2') && List.for_all2 equal (var_list c1') (var_list c2') && ord c1' c2' <> Gt) in
  if r then None else (
  let euc = Evd.make_evar_universe_context env None in
  let rew_tac ev rews =
    if scompl then
      raw_srewrites ord rews
    else 
      rewrites rews
  in
  let (stmt1, ev1), (stmt2, ev2) = make_eq_statement env evd equiv c c1, make_eq_statement env evd equiv c c2 in

  let tac1 = Auto.auto !Auto.default_search_depth [ev1, hinfo1.hyp_prf] [] in
  let tac2 =
    Tactics.intros <*> congruence_using [rule]
  in
  let pt1,_,euc1 = Pfedit.build_by_tactic env euc stmt1 tac1 in
  let pt2,_,euc2 = Pfedit.build_by_tactic env euc stmt2 tac2 in

  let normalize ev c euc =
    let tac = Tactics.intros <*> Tactics.any_constructor true None <*>
              (rew_tac ev rews <+> Tacticals.New.tclIDTAC) <*>
              Tactics.reflexivity
    in
    let (sig_eq,_), evars = make_sig_eq env ev equiv c in
    let (pt,_,euc) = Pfedit.build_by_tactic env euc sig_eq tac in
    let cnew, ptnew = prod_sig_to_prod env pt in
    Reduction.nf_betaiota env (Term.applist (cnew, evars)), fst (evars_to_fun env ev (Reduction.nf_betaiota env (Term.applist (ptnew, evars)))), euc
  in
  let normalize' ev c c' euc =
    let tac = Tactics.intros <*> Tactics.any_constructor true None <*>
              (rew_tac ev rews <+> Tacticals.New.tclIDTAC) <*>
              Proofview.V82.tactic (Tactics.unfold_constr (find_reference ["Program"; "Basics"] "flip" ())) <*>
              Proofview.V82.tactic (Tactics.unfold_constr (find_reference ["Program"; "Basics"] "const" ())) <*>
              Tactics.reflexivity
    in
    let (sig_eq,_), evars = make_sig_eq_with env ev equiv c c' in
    let (pt,_,euc) = Pfedit.build_by_tactic env euc sig_eq tac in
    let cnew, ptnew = prod_sig_to_prod env pt in
    Reduction.nf_betaiota env (Term.applist (cnew, evars)), fst (evars_to_fun env ev (Reduction.nf_betaiota env (Term.applist (ptnew, evars)))), euc
  in
  let c1',p1',euc1 = normalize ev1 c1 euc1 in
  let c2',p2',euc2 = normalize' ev2 c2 c1' euc2 in

  let stmt,_ = make_eq_statement env evd equiv c2 c2' in
  let stmt' = Retyping.get_type_of env ev2 p2' in
  let p2',_,euc2 =
    let tac = Tacticals.New.tclTHENS
                (Tactics.cut stmt')
                [ Proofview.V82.tactic (Tactics.unfold_constr (find_reference ["Program"; "Basics"] "flip" ())) <*>
                  Proofview.V82.tactic (Tactics.unfold_constr (find_reference ["Program"; "Basics"] "const" ())) <*>
                  Tactics.intros <*>
                  Auto.default_auto
                ; Tactics.Simple.apply p2']
    in
    Pfedit.build_by_tactic env euc2 stmt tac
  in

  let fin e = match e with Some const -> Tactics.Simple.apply const | None -> Tacticals.New.tclIDTAC in
  let tac' p p' e =
    Tactics.intros <*> Tacticals.New.tclTHENS Tactics.etransitivity [unshelve (Tactics.Simple.apply p); unshelve (Tactics.Simple.apply p')] <*> Auto.default_auto <*> fin e
  in
  let g ev c c' p p' euc =
    let e = if Evarutil.has_undefined_evars ev c then None else Some c in
    let pt,_,euc =
      Pfedit.build_by_tactic env euc (fst (make_eq_statement env ev equiv c c')) (tac' p p' e) in
    pt, c', euc
  in
  let p1,c1',euc1 = g ev1 c c1' pt1 p1' euc1 in
  let p2,c2',euc2 = g ev2 c c2' pt2 p2' euc2 in

  let tac pt1 pt2 e =
    Tactics.intros <*> Tacticals.New.tclTHENS Tactics.etransitivity [Tactics.symmetry <*> unshelve (Tactics.Simple.apply pt1); unshelve (Tactics.Simple.apply pt2)] <*> Auto.default_auto <*> fin e
  in
  let f rews' ((p1, c1', euc1), (p2, c2', euc2), ev) =
    if teq env ev c1' c2' then None else (
    let (p1, c1', euc1), (p2, c2', euc2) =
      match ord c1' c2' with
      | Lt -> (p2, c2', euc2), (p1, c1', euc1)
      | Gt -> (p1, c1', euc1), (p2, c2', euc2)
      | _ -> if scompl then if size c1' >= size c2' then (p1, c1', euc1), (p2, c2', euc2) else (p2,c2',euc2), (p1,c1',euc1) else
          Errors.errorlabstrm "Completion failure"
                  (str "Completion failed: cannot orient " ++ 
                  Ppconstr.pr_constr_expr (Constrextern.extern_constr true env ev c1') ++
                  str ", " ++ 
                  Ppconstr.pr_constr_expr (Constrextern.extern_constr true env ev c2'))
    in
    let s, _ =  make_eq_statement env ev equiv c1' c2' in
    let e = if Evarutil.has_undefined_evars ev c1' then None else Some c1' in
    let p, _, _ = Pfedit.build_by_tactic env euc2 s (tac p1 p2 e) in
    let senv = Global.safe_env() in
    let id = Namegen.next_ident_away_from (Id.of_string (basename ^ "_lemma")) (fun x -> Nametab.exists_cci (Libnames.make_path (Safe_typing.current_dirpath senv) x)) in
    let _ , prfc = 
      (match Obligations.add_definition id ~term:p s euc [||] with
      | Defined ref -> Evarutil.new_global ev ref
      | _ -> Errors.error "error")
    in
    msg (Ppconstr.pr_constr_expr (Constrextern.extern_constr true env ev prfc) ++  str " : " ++ Ppconstr.pr_constr_expr (Constrextern.extern_constr true env ev s) ++ str "\n");
    Some prfc)
  in
  f rews ((p1,c1',euc1),(p2,c2',euc2),ev1))

let critical_pairs env evd rews newrules =
  let rs = List.rev_append rews newrules in
  let f res c =
    let g res' c' =
      let h = find_applied_relation false Loc.ghost env evd c true in
      let h' = find_applied_relation false Loc.ghost h.hyp_cl.env h.hyp_cl.evd c' true in
      let cs = crit_pairs h'.hyp_cl.env h'.hyp_cl.evd h h' c' in
      let h = find_applied_relation false Loc.ghost h'.hyp_cl.env h'.hyp_cl.evd c true in
      let cs = List.rev_append cs (crit_pairs h.hyp_cl.env h.hyp_cl.evd h' h c) in
      List.rev_append cs res'
    in
    List.rev_append (List.fold_left g [] rs) res
  in
  let l = List.fold_left f [] newrules in
  List.sort (fun (_,c1,_,_,_,_,_)(_,c2,_,_,_,_,_) -> size c1 - size c2) l

let remove env evd ord scompl rews rews' =
  let rec aux result  = function
    | [] -> result
    | c'::rews ->
        let h = find_applied_relation false Loc.ghost env evd c' true in
        let rules = List.rev_append result (List.rev_append rews rews') in
        let h' = reduce_fun h.hyp_cl.env h.hyp_cl.evd scompl ord (mkApp (h.hyp_rel, [|h.hyp_left; h.hyp_right|])) rules in
        let reducible =
          match kind h' with
          | App (_, args) -> equal args.(1) args.(2)
          | _ -> false
        in
        if reducible then
            msg (Ppconstr.pr_constr_expr (Constrextern.extern_constr true env evd c') ++ str " is removed\n");
        if reducible then aux result rews else aux (c' :: result) rews
  in
  aux [] rews

let completion_core ord scompl basename rews newrules comms =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let rews = remove env evd ord scompl rews (List.rev_append comms newrules) in
  let newrules = remove env evd ord scompl newrules (List.rev_append comms rews) in
  msg (str "newrules:\n");
  List.iter (fun x -> msg (Ppconstr.pr_constr_expr (Constrextern.extern_constr true env evd x) ++ str "\n")) newrules;
  let cps = critical_pairs env evd (List.rev_append comms rews) newrules in
  let whole_rews = List.rev_append comms (List.rev_append newrules rews) in
  let aux newrs (ev, c, c1, c2, hinfo1, hinfo2, rule) =
    match proofterm_of_cp c c1 c2 hinfo1 hinfo2 rule ord scompl basename (List.rev_append newrs whole_rews) with
    | Some prfc -> prfc::newrs
    | None -> newrs
  in
  List.fold_left aux [] cps, whole_rews

let rec completion_aux ord scompl basename rews newrules comms =
  let newrules, rews = completion_core ord scompl basename rews newrules comms in
  match newrules with
  | [] -> let env = Global.env () in
          let evd = Evd.from_env env in
          add_rewrite_hint env evd [basename] true None rews Loc.ghost
  | _ -> completion_aux ord scompl basename rews newrules comms

let classes_dirpath =
  Names.DirPath.make (List.map Id.of_string ["Classes";"Coq"])

let init_setoid () =
  if Libnames.is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else Coqlib.check_required_library ["Coq";"Setoids";"Setoid"]

let completion cs scompl base weights acs =
  init_setoid ();
  let env = Global.env () in
  let evd = Evd.from_env env in
  let euc = Evd.make_evar_universe_context env None in
  let interp c = fst (Constrintern.interp_constr env evd c) in
  let csl = List.rev_map interp cs in
  let weights = List.map interp weights in

  let acs = List.rev_map (fun ((f, assoc), comm) ->
    let f, assoc, comm = interp f, interp assoc, interp comm in
    let h = find_applied_relation false Loc.ghost env evd assoc true in
    let evd, ev1 = Evarutil.new_pure_evar (Environ.named_context_val h.hyp_cl.env) h.hyp_cl.evd h.hyp_car in
    let evd, ev2 = Evarutil.new_pure_evar (Environ.named_context_val h.hyp_cl.env) evd h.hyp_car in
    let evd, ev3 = Evarutil.new_pure_evar (Environ.named_context_val h.hyp_cl.env) evd h.hyp_car in
    let assocl = mkApp (f, [| mkApp (f, [| mkEvar (ev1, [||]); mkEvar (ev2, [||]) |]); mkEvar (ev3, [||]) |]) in
    let assocr = mkApp (f, [| mkEvar (ev1,[||]); mkApp (f, [| mkEvar (ev2,[||]); mkEvar (ev3,[||]) |]) |]) in
    let ev, l2r =
      try Unification.w_unify h.hyp_cl.env evd Reduction.CONV ~flags:(compl_unify_flags_with_freeze assocl ()) assocl h.hyp_left, true
      with PretypeError (_,_,CannotUnify _) ->
        try Unification.w_unify h.hyp_cl.env evd Reduction.CONV ~flags:(compl_unify_flags_with_freeze assocr ()) assocr h.hyp_left, false
        with PretypeError (_,_,CannotUnify _) ->
          Errors.error "invalid associative law"
    in
    let _ = if l2r then
      if equal assocr (Evarutil.nf_evar ev h.hyp_right) then ()
        else Errors.error "invalid associative law"
      else if equal assocl (Evarutil.nf_evar ev h.hyp_right) then ()
        else Errors.error "invalid associative law"
    in
    let assoc = if l2r then assoc else
      (let senv = Global.safe_env() in
      let id = Namegen.next_ident_away_from (Id.of_string (base ^ "_assoc")) (fun x -> Nametab.exists_cci (Libnames.make_path (Safe_typing.current_dirpath senv) x)) in
      let s,_ = make_eq_statement h.hyp_cl.env h.hyp_cl.evd h.hyp_rel h.hyp_right h.hyp_left in
      msg (Ppconstr.pr_constr_expr(Constrextern.extern_constr true env evd s) ++ str "\n");
      match Obligations.add_definition id s euc ~tactic:(Tactics.intros <*> congruence_using [assoc]) [||] with
      | Defined ref -> snd (Evarutil.new_global evd ref)
      | _ -> Errors.error "failed to add associativity")
    in
    let h = find_applied_relation false Loc.ghost env evd comm true in
    let evd, ev1 = Evarutil.new_pure_evar (Environ.named_context_val h.hyp_cl.env) h.hyp_cl.evd h.hyp_car in
    let evd, ev2 = Evarutil.new_pure_evar (Environ.named_context_val h.hyp_cl.env) evd h.hyp_car in
    let comml = mkApp (f, [| mkEvar (ev1,[||]); mkEvar (ev2,[||]) |]) in
    let commr = mkApp (f, [| mkEvar (ev2,[||]); mkEvar (ev1,[||]) |]) in
    let ev =
      try Unification.w_unify h.hyp_cl.env evd Reduction.CONV ~flags:(compl_unify_flags_with_freeze comml ()) comml h.hyp_left
      with PretypeError (_,_,CannotUnify _) -> Errors.error "invalid commutative law"
    in
    if not (equal commr (Evarutil.nf_evar ev h.hyp_right)) then
      Errors.error "invalid commutative law";
    f, assoc, comm
    ) acs
  in

  let env = Global.env () in
  let evd = Evd.from_env env in
  let comms = List.fold_left (fun res (f, assoc, comm) ->
    let tac =
      Proofview.Goal.nf_enter begin fun gl ->
        let commg = Tacmach.New.pf_apply (extern_constr_to_glob true) gl comm in
        Tactics.intros <*>
        Tacticals.New.tclREPEAT_MAIN (Equality.rewriteRL assoc) <*>
        Proofview.V82.tactic (cl_rewrite_clause (Tacinterp.default_ist (), (commg, NoBindings)) true (OnlyOccurrences [2]) None) <*>
        Tactics.reflexivity
      end
    in
    let h = find_applied_relation false Loc.ghost env evd assoc true in
    let car = h.hyp_car in
    let stmt = mkProd (Namegen.named_hd env car Anonymous, car,
                (mkProd (Namegen.named_hd env car Anonymous, car,
                  (mkProd (Namegen.named_hd env car Anonymous, car,
                    mkApp (h.hyp_rel, [| mkApp (f, [| mkRel 1; mkApp (f, [| mkRel 2; mkRel 3 |]) |]);
                                         mkApp (f, [| mkRel 2; mkApp (f, [| mkRel 1; mkRel 3 |]) |]) |]))))))
    in
    let senv = Global.safe_env() in
    let id = Namegen.next_ident_away_from (Id.of_string (base ^ "_helper")) (fun x -> Nametab.exists_cci (Libnames.make_path (Safe_typing.current_dirpath senv) x)) in
    match Obligations.add_definition id stmt euc ~tactic:tac [||] with
    | Defined ref -> comm :: snd (Evarutil.new_global evd ref) :: res
    | _ -> Errors.error "error"
    ) [] acs
  in

  let rews = List.rev_map (fun c ->
    let hinfo = find_applied_relation false Loc.ghost env evd c true in
    match lex_pathord weights hinfo.hyp_left hinfo.hyp_right with
    | Lt ->
        (let senv = Global.safe_env () in
        let id = Namegen.next_ident_away_from (Id.of_string (base ^ "_lemma")) (fun x -> Nametab.exists_cci (Libnames.make_path (Safe_typing.current_dirpath senv) x)) in
        let s,_ = make_eq_statement hinfo.hyp_cl.env hinfo.hyp_cl.evd hinfo.hyp_rel hinfo.hyp_right hinfo.hyp_left in
        msg (Ppconstr.pr_constr_expr(Constrextern.extern_constr true env evd s) ++ str "\n");
        match Obligations.add_definition id s euc ~tactic:(Tactics.intros <*> congruence_using [c]) [||] with
        | Defined ref -> snd (Evarutil.new_global evd ref)
        | _ -> Errors.error "error")
    | _ -> c) csl
  in
  completion_aux (lex_pathord weights) scompl base [] (List.rev_map (fun (_,assoc,_) -> assoc) acs @ rews) comms
