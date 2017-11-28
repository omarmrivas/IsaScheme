(*  Title:      src/completion.ML
    ID:         $Id: completion.ML,v 2.000 2012/04/20 12:42:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Politecnica de San Luis Potosi
    Copyright   Universidad Politecnica de San Luis Potosi 2011

An implementation of Unfailing Knuth Bendix (Baader and Nipkow's "Term Rewriting and All That" 
and Leo Bachmair, Nachum Dershowwitz and David A. Plaisted's "Completion without Failure")
Completion Algorithm for Isabelle.
*)

signature CONDITIONAL_COMPLETION =
sig
  val run_completion                : thm list -> Proof.context -> (thm list -> bool) ->
                                      thm list -> thm -> thm list
  val run_completion'               : thm list -> Proof.context -> (thm list -> bool) ->
                                      thm list -> thm -> thm list * thm list

  val discriminate_cpairs           : thm list -> Proof.context -> (thm list -> bool) ->
                                      thm list -> thm -> thm list

  val memoized_discriminate_rules   : Proof.context -> (thm list -> bool) -> thm list -> 
                                      thm list * thm list

  val discriminate_object_rules     :  Proof.context -> (thm list -> bool) -> thm list -> 
                                      thm list * thm list
  
  val modify   : thm -> thm

  val memoized_joinable :  Proof.context -> (thm list -> bool) ->
                           (term * int) list -> thm list -> thm -> bool

end

structure DB_Conditional_Completion
(* : CONDITIONAL_COMPLETION *)
= struct

local
(* A method to apply the rewrite step r1 to r2 *)
fun rw_method r1 r2 =
  let fun frule_method r ctxt = Method.SIMPLE_METHOD (forward_tac ctxt [r] 1)
      fun auto_method ctxt = Method.SIMPLE_METHOD (auto_tac ctxt)
      val text = Method.Combinator (Method.no_combinator_info,
                  Method.Then,
                  [Method.Basic (frule_method r1),
                   Method.Basic (frule_method r2),
                   Method.Basic auto_method])
  in (text,Position.no_range) end
in
  fun rewrite_step ctxt r1 r2 conv =
    let val thy = Proof_Context.theory_of ctxt
        val (_,rhs) = (Utils.dest_meta_equation o Thm.unvarify_global thy o Drule.zero_var_indexes) r1
        val crhs = Thm.cterm_of ctxt rhs
        val conj =
            r2 |> Drule.zero_var_indexes
               |> Thm.unvarify_global thy
               |> Thm.cprop_of
               |> conv (fn _ => Thm.reflexive crhs)
               |> fst o Utils.dest_meta_equation
        val timeOut = Config.get ctxt Prover.max_time_in_proof
        val res = Prover.prove ctxt (SOME [r1, r2]) (rw_method r1 r2) conj timeOut
    in res
    end
end

(*
  val unifiers: Context.generic * Envir.env * ((term * term) list) ->
    (Envir.env * (term * term) list) Seq.seq

  val match: theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

*)

local
(* rewrite step of th1 and th2 *)
fun scpairs' ctxt (th1, th2) =
    let
(*      val _ = tracing ("th1: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th1))
      val _ = tracing ("th2: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th2))*)
      val thy = Proof_Context.theory_of ctxt
      val (pat, rhs1) = Utils.dest_meta_equation th1
      val th2' = Drule.incr_indexes th1 th2
      val (obj, rhs2) = Utils.dest_meta_equation th2'
      val paty = type_of pat
      val valid_rewrites = Pattern.pattern pat andalso Pattern.pattern obj (* Higher-order patterns *)
                           andalso not (is_Var pat) andalso not (is_Var obj) (* Not a var on lhs *)
                           andalso not (Ground_Completion.rewrite_rule_extra_vars [] pat rhs1)
                           andalso not (Ground_Completion.rewrite_rule_extra_vars [] obj rhs2) (* does not introduce new Vars or TVars *)
      (* Does pat match a subterm of obj? *)
      fun msub bounds frees obj f =
          (case obj of
             Abs (_, T, t) =>
             let
               val matcher = if can (Sign.typ_match thy (T,paty)) Vartab.empty
                             then Unify.matchers (Context.Theory thy) [(pat,obj)]
                                        handle ListPair.UnequalLengths => Seq.empty
                                              | TERM _ => Seq.empty
                             else Seq.empty
               val (new_free,new_abs) = Term.dest_abs (Name.bound bounds, T, t)
             in Seq.append (Seq.map (pair (f,obj)) matcher)
                           (msub (bounds + 1) (new_free :: frees)
                                 new_abs
                                 (f o (Ground_Completion.my_abs_conv ctxt))) end
           | t $ u => (case (fst o Term.strip_comb) obj of
                         (* According to Nipkow's definition of critical pairs, the head must not be a variable *)
                         Var _ =>  Seq.append (msub bounds frees t (f o Conv.fun_conv)) (msub bounds frees u (f o Conv.arg_conv))
                       | _ => let
                           val unifier = if can (Sign.typ_match thy (type_of obj,paty)) Vartab.empty
                                         then Unify.matchers (Context.Theory thy) [(pat,obj)]
                                                  handle ListPair.UnequalLengths => Seq.empty
                                                       | TERM _ => Seq.empty
                                         else Seq.empty
                         in Seq.append (Seq.map (pair (f,obj)) unifier)
                                       (Seq.append (msub bounds frees t (f o Conv.fun_conv)) (msub bounds frees u (f o Conv.arg_conv))) end)
           | _ => Seq.empty)
    in if valid_rewrites then
         msub 0 [] obj I
              |> Seq.list_of
(*              |> tap (map (fn ((_, obj),_) => tracing (Syntax.string_of_term ctxt obj)))*)
              |> map_filter (fn ((conv, _),env) => SOME (conv, Utils.unify_inst ctxt env))
              |> map (fn (conv,inst) => (conv,apply2 (Drule.instantiate_normalize inst) (th1,th2')))
              (* Conv.concl_conv (Thm.nprems_of th) *)
              |> map (fn (conv,(r1,r2)) =>
                    let (*val prems_r1 = Thm.prems_of r1
                        val prems_r2 = Thm.prems_of r2
                        val prems = prems_r1 |> filter (not o member (op =) prems_r2)
                                             |> map (Thm.cterm_of ctxt)
                        val r2 = Library.foldl (fn (r, prem) => Thm.implies_intr prem r) (r2,prems)*)
                    in
                      if Thm.nprems_of r1 = 0
                      then Conv.fconv_rule
                             ((Conv.concl_conv (Thm.nprems_of r2) o Conv.fun_conv o Conv.arg_conv o conv)
                                 (Conv.rewr_conv r1)) r2
                      else case rewrite_step (clear_simpset ctxt) r1 r2
                                   ((Conv.concl_conv (Thm.nprems_of r2) o
                                         Conv.fun_conv o Conv.arg_conv o conv)) of
                             SOME thm => thm
                           | NONE => ((*tracing "Could not find a proof for the critical pair";
                                      tracing ("rules: " ^ Utils.str_of_thms [r1,r2]);
                                      tracing ("original rules: " ^ Utils.str_of_thms [th1,th2]);*)
                                      r2)
                    end)
              |> map Drule.zero_var_indexes
              |> distinct (Thm.equiv_thm thy)
              |> filter_out (fn th =>
                              let val th' = Utils.commute_meta_eq th
                              in EQUAL = (Term_Ord.term_ord o Utils.dest_meta_equation) th orelse
                                 Thm.equiv_thm thy (th, th1) orelse
                                 Thm.equiv_thm thy (th, th2) orelse
                                 Thm.equiv_thm thy (th', th1) orelse
                                 Thm.equiv_thm thy (th', th2)
                              end)
       else []
    end
in

fun rewrite_steps ctxt rule th =
  scpairs' ctxt (rule, th) @ map Utils.commute_meta_eq (scpairs' ctxt (rule, Utils.commute_meta_eq th))

fun rewrite_lhs ctxt rule th =
  let (*val thy = Proof_Context.theory_of ctxt*)
      val termless = (#termless o Raw_Simplifier.internal_ss) (simpset_of ctxt)
      val rewrites = termless o swap o apply2 Thm.full_prop_of
      fun it th =
        case filter (rewrites o pair th) (scpairs' ctxt (rule, th)) of
            th' :: _ => it th'
            | [] => th
  in it th end

fun normalize_lhs ctxt TRS th =
  let val thy = Proof_Context.theory_of ctxt
      val TRS = filter_out Utils.permutative_rule TRS
      val th' = fold (rewrite_lhs ctxt) TRS th
  in if Thm.equiv_thm thy (th, th')
     then th'
     else normalize_lhs ctxt TRS th'
  end

fun normalize_rhs thy TRS th =
  th |> Utils.commute_meta_eq
     |> normalize_lhs thy TRS
     |> Utils.commute_meta_eq


end

(* Semi-Critical pairs of th1 and th2 *)
fun scpairs thy (th1, th2) =
    let
(*      val _ = tracing ("th1: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th1))
      val _ = tracing ("th2: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th2))*)
      val ctxt = Context.proof_of (Context.Theory thy)
      val (pat, rhs1) = Utils.dest_meta_equation th1
      val th2' = Drule.incr_indexes th1 th2
      val (obj, rhs2) = Utils.dest_meta_equation th2'
      val paty = type_of pat
      val maxidx_typ = Term.maxidx_typ paty 0
      val valid_rewrites = Pattern.pattern pat andalso Pattern.pattern obj (* Higher-order patterns *)
                           andalso not (is_Var pat) andalso not (is_Var obj) (* Not a var on lhs *)
                           andalso not (Ground_Completion.rewrite_rule_extra_vars [] pat rhs1)
                           andalso not (Ground_Completion.rewrite_rule_extra_vars [] obj rhs2) (* does not introduce new Vars or TVars *)
      (* Does pat match a subterm of obj? *)
      fun msub bounds frees obj f =
          (case obj of
             Abs (_, T, t) =>
             let
               val unifier = if can (Sign.typ_unify thy (T,paty)) (Vartab.empty,Term.maxidx_typ T maxidx_typ)
                             then Unify.unifiers (Context.Theory thy,(Envir.empty 1),[(pat,obj)]) handle ListPair.UnequalLengths => Seq.empty
                                                                                        | TERM _ => Seq.empty
                             else Seq.empty
               val (new_free,new_abs) = Term.dest_abs (Name.bound bounds, T, t)
             in Seq.append (Seq.map (pair f) unifier)
                           (msub (bounds + 1) (new_free :: frees)
                                 new_abs
                                 (f o (Ground_Completion.my_abs_conv ctxt))) end
           | t $ u => (case (fst o Term.strip_comb) obj of
                         (* According to Nipkow's definition of critical pairs, the head must not be a variable *)
                         Var _ =>  Seq.append (msub bounds frees t (f o Conv.fun_conv)) (msub bounds frees u (f o Conv.arg_conv))
                       | _ => let
                           val unifier = if can (Sign.typ_unify thy (type_of obj,paty)) (Vartab.empty,Term.maxidx_typ (type_of obj) maxidx_typ)
                                         then Unify.unifiers (Context.Theory thy,(Envir.empty 1),[(pat,obj)]) handle ListPair.UnequalLengths => Seq.empty
                                                                                                    | TERM _ => Seq.empty
                                         else Seq.empty
                         in Seq.append (Seq.map (pair f) unifier)
                                       (Seq.append (msub bounds frees t (f o Conv.fun_conv)) (msub bounds frees u (f o Conv.arg_conv))) end)
           | _ => Seq.empty)
    in if valid_rewrites then
         msub 0 [] obj I
              |> Seq.list_of
              |> map_filter (fn (conv,(env,_)) => SOME (conv, Utils.unify_inst ctxt env))
              |> map (fn (conv,inst) => (conv,apply2 (Drule.instantiate_normalize inst) (th1,th2')))
              (* Conv.concl_conv (Thm.nprems_of th) *)
              |> map (fn (conv,(r1,r2)) =>
                    let val prems_r1 = Thm.prems_of r1
                        val prems_r2 = Thm.prems_of r2
                        val prems = prems_r1 |> filter (not o member (op =) prems_r2)
                                             |> map (Thm.cterm_of ctxt)
                        val r2 = Library.foldl (fn (r, prem) => Thm.implies_intr prem r) (r2,prems)
                    in
                      if Thm.nprems_of r1 = 0
                      then Conv.fconv_rule
                             ((Conv.concl_conv (Thm.nprems_of r2) o Conv.fun_conv o Conv.arg_conv o conv)
                                 (Conv.rewr_conv r1)) r2
                      else case rewrite_step (clear_simpset ctxt) r1 r2 
                                   ((Conv.concl_conv (Thm.nprems_of r2) o 
                                         Conv.fun_conv o Conv.arg_conv o conv)) of
                             SOME thm => thm
                           | NONE => (tracing "Could not find a proof for the critical pair";
                                      tracing ("rules: " ^ Utils.str_of_thms [r1,r2]);
                                      r2)
                    end)
              |> filter_out (fn th =>
                              let val th' = Utils.commute_meta_eq th
                              in EQUAL = (Term_Ord.term_ord o Utils.dest_meta_equation) th orelse
                                 Thm.equiv_thm thy (th, th1) orelse
                                 Thm.equiv_thm thy (th, th2) orelse
                                 Thm.equiv_thm thy (th', th1) orelse
                                 Thm.equiv_thm thy (th', th2)
                              end)
       else []
    end

fun scpairs_aux thy (th1, th2) =
    let
      val cth1 = Utils.commute_meta_eq th1
      val cth2 = Utils.commute_meta_eq th2
    in
      scpairs thy (th1, th2) @
      scpairs thy (th1, cth2) @
      scpairs thy (cth1, th2) @
      scpairs thy (cth1, cth2)
    end

fun semi_critical_pairs thy ord R1 R2 =
  ([],R1) |> Library.foldl (fn (pairs,th1) => maps (fn th2 => scpairs_aux thy (th1, th2)) R2 @ pairs)
          |> map (Utils.orient_meta_rule thy ord)
          |> Utils.make_theorem_set

(* Ordered Rewriting *)

fun ac_termination_obj ctxt simps th =
  if can Utils.dest_object_equation th
  then let val simps = filter (can Utils.dest_object_equation) (th :: simps)
           fun update_net thm net =
                net |> Net.insert_term (is_equal o Thm.thm_ord)
                                       (Thm.full_prop_of thm, thm)
           fun test_simp net (rule :: rules) thm =
              let val thm' = simplify (ctxt addsimps [rule]) thm
              in if is_equal (Thm.thm_ord (thm, thm'))
                 then test_simp net rules thm
                 else if can (update_net thm') net
                 then test_simp (update_net thm' net) rules thm'
                 else false
              end
             | test_simp _ [] _ = true
       in test_simp (update_net th Net.empty) simps th andalso
          test_simp (update_net th Net.empty) (rev simps) th
      end
  else true

(*fun rewrite_step' ctxt rule th =
  let val r = Unsynchronized.ref true
      val (pat, rhs1) = Utils.dest_meta_equation rule
      val th' = Drule.incr_indexes rule th
      val (obj, rhs2) = Utils.dest_meta_equation th'
      val paty = type_of pat
      val maxidx_typ = Term.maxidx_typ paty 0
      val subterms = exists_subterm
      fun proc _ _ _ = if !r = true
                       then (r:=false; SOME rule)
                       else NONE
      val spec = {lhss = [], proc = proc}
      val simproc = Simplifier.make_simproc ctxt "test_simproc" spec
  in simplify (ctxt addsimprocs [simproc]) th end*)
  

(* Empirical test for termination of ac rewriting *)
(* This test is necessarily incomplete due to the halting problem *)
fun ac_termination ctxt (equations, rules) th =
    let (*val _ = tracing ("Equations: " ^ Utils.str_of_thms equations)
        val _ = tracing ("Rules: " ^ Utils.str_of_thms rules)
        val _ = tracing ("Th: " ^ Utils.str_of_thms [th])*)
        val thy = Proof_Context.theory_of ctxt
        val termless = (#termless o Raw_Simplifier.internal_ss) (simpset_of ctxt)
        val rewrites = termless o swap o apply2 Thm.full_prop_of
        val max_size = (equations @ rules)
                         |> map size_of_thm
                         |> pair 0
                         |> Library.foldl (op +)
                         |> (fn c => if c = 0 then 1000 else
                                     c + Drule.size_of_thm th)
        fun update_net thm net =
          Net.insert_term (is_equal o Thm.thm_ord) (Thm.full_prop_of thm, thm) net
        fun test_procs set s (proc :: procs) term =
              let val ts = rewrite_steps ctxt proc s
                            |> filter (rewrites o pair s)
              in (case ts of
                     _ :: _ => forall (fn t => test_procs (update_net t set) t procs term) ts
                   | [] => test_procs set s procs term)
                  handle Net.INSERT => false
              end
          | test_procs set s [] term = test_rules set s (th :: rules) term
        and test_rules set s (rule :: rules) term =
              let val ts = rewrite_steps ctxt rule s
              in (case ts of
                     _ :: _ => forall (fn t => test_rules (update_net t set) t rules term) ts
                   | [] => test_rules set s rules term)
                  handle Net.INSERT => false
              end
          | test_rules set s [] term =
              if Thm.equiv_thm thy (s, term)
              then true
              else if size_of_thm s < max_size
              then test_procs set s equations s
              else false
    fun test thm = 
      test_procs (update_net thm Net.empty) thm equations thm
  in forall test [th]
  end

(* This function uses only a subset of thms which is guarantied to terminate *)
fun discriminate_rules ctxt terminates thms =
  let val thy = Proof_Context.theory_of ctxt
      val schemes = Utils.get_orientation_schemes ()
      fun orient_scheme equation =
        let val eq =  (HOLogic.mk_eq o Utils.dest_meta_equation) equation
            val eq' = (HOLogic.mk_eq o swap o HOLogic.dest_eq) eq
        in case get_first (fn scheme => 
              if Pattern.matchess thy ([scheme], [eq])
              then SOME equation
              else if Pattern.matchess thy ([scheme], [eq'])
                   then SOME (Utils.commute_meta_eq equation)
                   else NONE) schemes of
              SOME eq => eq
            | NONE => equation
        end
      fun is_index th' th =
        if Thm.equiv_thm thy (th', th)
        then SOME false
        else if Thm.equiv_thm thy (th', Utils.commute_meta_eq th)
        then SOME true
        else NONE
  in
    thms (*|> Utils.make_theorem_set*)
         |> map orient_scheme
         |> map (fn th => (th, Drule.size_of_thm th))
         |> sort (int_ord o (apply2 snd))
         |> map fst
         |> pair ([],[])
         |> Library.foldl
         (fn ((equations,rules),th) =>
             if Utils.permutative_rule th
             then (th :: equations, rules)
             else (equations, th :: rules))
         |> (fn (equations, potential_rules) => ((equations, []), rev potential_rules))
         |> Library.foldl
         (fn ((equations,rules),th) =>
             if terminates (th :: rules) andalso
                ac_termination ctxt (equations, rules) th
             then (equations, th :: rules)
             else if terminates ((Utils.commute_meta_eq th) :: rules) andalso
                     ac_termination ctxt (equations, rules) (Utils.commute_meta_eq th)
             then (equations, Utils.commute_meta_eq th :: rules)
             else
               let (*val thy = Thm.theory_of_thm th
                   val _ = tracing ("Incompatible rule: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th))
                   val _ = tracing ("with: " ^ Utils.str_of_thms (equations @ rules))*)
               in (equations, rules)
               end)
         |> (fn (equations, rules) =>
                (map_filter (fn s => get_index (is_index s) thms) equations,
                 map_filter (fn s => get_index (is_index s) thms) rules))
(*         |> apply2 Utils.make_theorem_set*)
  end

val discriminate_rules_var
      = Synchronized.var "discriminate_rules"
                         (Term_List_Tab.empty : ((int * bool) list * (int * bool) list) Term_List_Tab.table)

fun memoized_discriminate_rules ctxt terminates thms =
  let val thms = thms |> Utils.make_theorem_set
                      |> sort Thm.thm_ord
      val transform = map Thm.full_prop_of
      fun dest_index thms (i, comm) =
            if comm
            then Utils.commute_meta_eq (nth thms i)
            else nth thms i
  in Utils.memoize_function Term_List_Tab.lookup Term_List_Tab.update transform discriminate_rules_var
                            (discriminate_rules ctxt terminates) thms
       |> (fn (equations, rules) => (map (dest_index thms) equations,
                                     map (dest_index thms) rules))
  end handle Subscript => (tracing "memoized_discriminate_rules"; raise Subscript)

fun discriminate_object_rules ctxt terminates =
  apply2 (map Utils.meta_to_obj) o memoized_discriminate_rules ctxt terminates o map Utils.obj_to_meta

(*fun memoized_discriminate_rules ctxt terminates (thms as th :: _) =
  let val thms = thms |> Utils.make_theorem_set
                      |> sort Thm.thm_ord
      val (eqs, rules) = Utils.memoize_function Thm_List_Tab.lookup Thm_List_Tab.update discriminate_rules_var
                            (discriminate_rules ctxt terminates) thms
      val thy = Thm.theory_of_thm th
      fun test thm1 thm2 = (Pattern.equiv thy o apply2 Thm.full_prop_of) (thm1, thm2)
  in Library.foldl (fn ((eqs', rules'), th) => if exists (test th) eqs
                                               then (th :: eqs', rules')
                                               else if exists (test th) rules
                                               then (eqs', th :: rules')
                                               else (eqs', rules')) (([], []), thms)
  end
| memoized_discriminate_rules _ _ [] = ([], [])*)

fun ordered_simpset_without_simprocs ctxt terminates thms =
    let (*val ctxt = clear_simpset ctxt*)
(*        val (_,rules) = memoized_discriminate_rules ctxt terminates thms*)
        val (_,rules) = memoized_discriminate_rules ctxt terminates thms
    in ctxt addsimps rules
    end

(*fun ordered_simpset ctxt terminates thms =
    let val ctxt = clear_simpset ctxt
        val (equations, rules) = memoized_discriminate_rules ctxt terminates thms
    in ctxt addsimps (equations @ rules)
    end*)

fun rewrite_rule ctxt terminates thms =
  let val ctxt = ordered_simpset_without_simprocs ctxt terminates thms
  in simplify ctxt end

(* Ordered Rewriting *)

fun normalize_part ctxt terminates fun_arg TRS thm =
  let val ctxt = ordered_simpset_without_simprocs ctxt terminates TRS
  in Conv.fconv_rule (fun_arg (Simplifier.rewrite ctxt)) thm end
(*  in Conv.fconv_rule (fun_arg (Raw_Simplifier.rewrite ctxt true [])) thm end*)

val ground_debug = Unsynchronized.ref false
val ground_debug2 = Unsynchronized.ref false
val completion_debug = Unsynchronized.ref false

(* Ground joinability test *)

fun print_orders ctxt orders = ([], orders)
                                 |> Library.foldl (fn (s, (t, i)) => ((Syntax.string_of_term ctxt t) ^ " : " ^ Int.toString i) :: s)
                                 |> space_implode ", "
                                 |> enclose "[" "]"

fun ground_joinable ctxt terminates f_map (e, E) =
  let (*val s_t = Thm.full_prop_of e
      val thy = Thm.theory_of_thm e*)
      val ctxt = clear_simpset ctxt
(*      val _ = tracing ("E: " ^ Utils.str_of_thms E)
      val _ = tracing ("e: " ^ Utils.str_of_thms [e])*)
(*      val (equations, rules) = memoized_discriminate_rules ctxt terminates E*)
      val (equations, rules) = memoized_discriminate_rules ctxt terminates E
(*      val _ = tracing ("Equations: " ^ Utils.str_of_thms equations)
      val _ = tracing ("Rules: " ^ Utils.str_of_thms rules)*)
      val f_map = sort (int_ord o (apply2 snd)) f_map
      val vars = e |> Thm.full_prop_of
                   |> (fn t => Term.add_vars t [])
                   |> map Var
  in vars
        |> Orders.extend_ord_eval
        (fn ord =>
                 ord |> pair ([],[])
                     |> Library.foldl (fn ((consts_map, vars_map), (Var V, I)) => (consts_map, (V, I) :: vars_map)
                                        | ((consts_map, vars_map), (Const C, I)) => ((C, I) :: consts_map, vars_map)
                                        | ((consts_map, vars_map), (_, _)) => (consts_map, vars_map))
(*                     |> tap (fn (cs, vs) =>
                                let val r = (map (apfst Const) cs @ map (apfst Var) vs)
                                in (tracing o print_orders ctxt) r end)*)
                     |> Orders.map_term_to_int
                     |> Term_Ord.term_lpo
                     |> (fn g_ord =>
                            let fun termless tu = (g_ord tu = LESS)
                                val ctxt = ctxt |> Simplifier.set_termless termless
                                                |> (fn ctxt => ctxt addsimps (equations @ rules))
                            in
(*                            e |> asm_full_simplify ctxt*)
                            e |> simplify ctxt
                              |> Utils.dest_meta_equation
                              |> (op =)
(*                              |> tap (fn foo => if foo
                                                then tracing "true"
                                                else tracing "false")*)
(*                              |> (is_equal o g_ord)*)
                            end)) f_map
(*        |> tap (fn foo => if foo then tracing "joinable" else tracing "not joinable")*)
 end

(*fun ground_joinable' ctxt terminates f_maps (e, E) =
  Par_List.forall (fn f_map => ground_joinable ctxt terminates f_map (e, E)) f_maps*)

val memoized_joinability_var = Synchronized.var "memoized_joinability"
                      (Term_Term_List_Tab.empty : bool Term_Term_List_Tab.table)

fun memoized_joinable ctxt terminates f_map E e =
  let val E = sort Thm.thm_ord E
      fun transform (e,E) = (Thm.full_prop_of e, (sort Term_Ord.term_ord o map Thm.full_prop_of) E)
  in Utils.memoize_function Term_Term_List_Tab.lookup Term_Term_List_Tab.update transform memoized_joinability_var
                            (ground_joinable ctxt terminates f_map) (e, E) end

fun memoized_joinable' ctxt terminates f_map E e =
  let val e = Prover.cheat_prover ctxt e
  in memoized_joinable ctxt terminates f_map E e end

(* Heuristics to speed up completion *)

(* improve simplification by transforming something of the form *)
(* c(x) = x(y) into x = y (if the latter is a theorem) *)
local
  val pat = @{term_pat "?X (?lhs :: ?'a) \<equiv> ?X (?rhs :: ?'a)"}
  val pat' = @{term_pat "(?lhs :: ?'a) = (?rhs :: ?'a)"}
in
fun heuristic1 ctxt proof_timeOut lemmas rule : thm option =
  let val thy = Proof_Context.theory_of ctxt
      val obj = rule |> Thm.full_prop_of
                     |> Logic.unvarify_global o Term_Subst.zero_var_indexes
      val matchers = Pattern.first_order_match thy (pat,obj) (Vartab.empty, Vartab.empty)
      val conj = pat' |> Envir.subst_term matchers
                      |> HOLogic.mk_Trueprop
      val timeOut = Config.get ctxt Counter_Example.max_time_in_counter_ex
  in case Counter_Example.unfalsified_conjecture ctxt timeOut conj of
      SOME conj => Prover.prove ctxt (SOME lemmas) (Prover.induct_auto_method ctxt) conj proof_timeOut
    | NONE => NONE
  end handle Pattern.MATCH => NONE
end

fun add_rule ctxt terminates (th,E,S,R) =
    let
(*      val thy = Proof_Context.theory_of ctxt*)
      fun simpl ([],E',R') = (E',R')
        | simpl (u :: U,E',U') = 
          let
            val (g,_) = Utils.dest_meta_equation u
(*            val u' = normalize_part ctxt terminates (Conv.fun_conv o Conv.arg_conv) [th] u*)
            (* Normalization probably is without permutative rules! *)
            val u' = normalize_lhs ctxt [th] u
            val (g',_) = Utils.dest_meta_equation u'
          in
            if EQUAL = Term_Ord.term_ord (g,g') then
(*              let val u'' = normalize_part ctxt terminates Conv.arg_conv (th :: R @ S) u*)
            (* Normalization probably is without permutative rules! *)
              let val u'' = normalize_rhs ctxt (th :: R @ S) u
              in simpl (U,E', u'' :: U') end
            else simpl (U,u' :: E', U')
          end
      val (E',S') = simpl (S,E,[])
      val (E'',R') = simpl (R,E',[])
    in (E'',th :: S',R') end

fun min_rule (rl,_,[],R') = (rl,R')
  | min_rule (rl,n,th::R,R') = 
    let
      val m = Utils.rule_int_ord th
    in if list_ord int_ord (m, n) = LESS then min_rule (th,m,R,rl :: R')
       else min_rule (rl,n,R,th :: R')
    end

fun choose ctxt proof_timeOut lemmas (th :: R) =
      let val (rule, rules) = min_rule (th,Utils.rule_int_ord th,R,[])
      in case heuristic1 ctxt proof_timeOut lemmas rule of
            SOME thm => (Utils.obj_to_meta thm, rules)
(*            SOME thm => (Utils.obj_to_meta thm, rule :: rules)*)
          | NONE => (rule, rules)
      end
  | choose _ _ _ [] = raise ERROR "Empty rule set"

fun print_completion (E,S,R) =
    let 
      fun str R = R |> map (fn th => (Thm.theory_of_thm th, Thm.full_prop_of th))
                    |> map (fn (thy, t) => Syntax.string_of_term_global thy t)
                    |> commas
      val E_str = str E
      val S_str = str S
      val R_str = str R
      val _ = tracing ("E = <" ^ E_str ^ ">")
      val _ = tracing ("S = <" ^ S_str ^ ">")
      val _ = tracing ("R = <" ^ R_str ^ ">")
    in () end

datatype ORI = NORMAL of (thm list * thm list) | RESTART of (thm list)

fun orient ctxt global_meta_rws ord terminates f_map =
    let fun ori ([],S,R) = NORMAL (S,R)
          | ori (th :: E,S,R) =
            let
              val thy = Thm.theory_of_thm th
(*              val _ = tracing ("Before simplification: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th))*)
              val th' = rewrite_rule ctxt terminates (S @ R) (Ground_Completion.linear_if_possible th)
(*              val _ = tracing ("After rewrite_rule: " ^ Utils.str_of_thms [th'])*)
              val th' = th' (*|> Utils.meta_to_obj*)
(*                            |> Raw_Simplifier.rewrite_rule ctxt global_meta_rws*)
                            |> Utils.orient_meta_rule thy ord
(*                            |> Utils.obj_to_meta*)
                            |> (fn th => if Thm.equiv_thm thy (@{thm "TrueI"},th)
                                         then Utils.obj_to_meta @{thm "refl"}
                                         else th)
(*              val _ = tracing ("After orientation: " ^ Utils.str_of_thms [th'])*)
(*              val (_, rules) = memoized_discriminate_rules (empty_simpset ctxt) terminates (S @ R)*)
              val (_, rules) = memoized_discriminate_rules (empty_simpset ctxt) terminates (S @ R)
(*              val _ = tracing ("After memoized_discriminate_rules: ")*)
              val joinable = memoized_joinable ctxt terminates f_map (S @ R) th'
(*              val _ = tracing ("After joinable: ")*)
(*              val _ = if joinable
                      then (tracing ("Joinable!: " ^ Utils.str_of_thms [th']);
                            tracing ("From: " ^ Utils.str_of_thms (S @ R)))
                      else ()*)
              fun restart () = NONE
              val (s,t) = Utils.dest_meta_equation th'
(*              val _ = tracing ("After dest_meta_equation: ")*)
              val comm_th' = Utils.commute_meta_eq th'
(*              val _ = tracing ("After commute_meta_eq: ")*)
            in
              case restart () of
                SOME thms => RESTART thms
              | NONE =>
                if joinable then ori (E,S,R)
                else if Utils.permutative_eq (s, t)
                     then ori (add_rule ctxt terminates (th',E,S,R))
                     else if terminates (th' :: rules)
                     then ori (add_rule ctxt terminates (th',E,S,R))
                     else ori (add_rule ctxt terminates (comm_th',E,S,R))
            end
    in ori end

(*fun make_irreducible _ _ _ TRS [] = TRS
  | make_irreducible ctxt terminates f_map R (th :: TRS) =
    if memoized_joinable ctxt terminates f_map (R @ TRS) th
    then R @ TRS
    else make_irreducible ctxt terminates f_map (th :: R) TRS*)

fun make_irreducible _ _ _ TRS [] = TRS
  | make_irreducible ctxt terminates f_map R (th :: TRS) =
    if memoized_joinable ctxt terminates f_map (R @ TRS) th
    then make_irreducible ctxt terminates f_map R TRS
    else make_irreducible ctxt terminates f_map (th :: R) TRS

fun complete global_meta_rws thy ctxt ord generate_cps terminates f_map E =
    let
      val proof_timeOut = Config.get ctxt Prover.max_time_in_proof
      val E = E |> map (fn th => (Utils.rule_int_ord th, th))
                |> sort ((list_ord int_ord) o (apply2 fst))
                |> map snd
      val E' = E
      fun compl (E,S,R) = case (if !completion_debug then print_completion (E,S,R) else ();
                                orient ctxt global_meta_rws ord terminates f_map (E,S,R)) of
                            NORMAL ([],R') => R'
                          | NORMAL (S',R') => let (*val lemmas = (S @ R) |> memoized_discriminate_rules terminates
                                                                           |> (fn (x, y) => x @ y)*)
                                                  val (rl,S'') = choose ctxt proof_timeOut E' S'
                                                  val _ = if !completion_debug then tracing ("Choosed: " ^ Utils.str_of_thms [rl])
                                                          else ()
                                                  val cps = if generate_cps then
                                                              ((semi_critical_pairs thy ord [rl] R') @
                                                               (semi_critical_pairs thy ord R' [rl]) @
                                                               (semi_critical_pairs thy ord [rl] [rl]))
                                                                |> Utils.make_theorem_set
                                                                |> map (fn th => (Utils.rule_int_ord th, th))
                                                                |> sort ((list_ord int_ord) o (apply2 fst))
                                                                |> map snd
(*                                                                |> map (Raw_Simplifier.rewrite_rule ctxt global_meta_rws)*)
                                                            else []
                                                  val _ = if !completion_debug then tracing ("Critical pairs: " ^ Utils.str_of_thms cps) else ()
                                              in compl (cps,S'',rl :: R') end
                          | RESTART thms => (tracing ("Restarting completion..." ^ Utils.str_of_thms (E' @ thms));
                                             complete global_meta_rws thy ctxt ord generate_cps terminates f_map (E' @ thms))
    in
      (E,[],[]) |> compl
(*                |> tap (fn TRS => tracing ("Done 0: " ^ Utils.str_of_thms TRS))*)
                |> make_irreducible ctxt terminates f_map []
    end

val rule_false = @{lemma "\<not>P \<equiv> (P = False)" by simp}
val rule_true = @{lemma "P \<equiv> (P = True)" by simp}
fun modify th =
  if can Utils.dest_meta_equation th
  then th
  else
  case Thm.concl_of th of
     Const _ $ ((Const (top, _) $ _) $ _) =>
          if Const_Names.hol_eq = top
          then Utils.obj_to_meta th
          else th |> Conv.fconv_rule (Conv.arg_conv (Conv.rewr_conv rule_true))
                  |> Utils.obj_to_meta
    | Const _ $ (Const (top, _) $ _) =>
          if Const_Names.hol_not = top
          then th |> Conv.fconv_rule (Conv.arg_conv (Conv.rewr_conv rule_false))
                  |> Utils.obj_to_meta
          else th |> Conv.fconv_rule (Conv.arg_conv (Conv.rewr_conv rule_true))
                  |> Utils.obj_to_meta
    | _ => th |> Conv.fconv_rule (Conv.arg_conv (Conv.rewr_conv rule_true))
              |> Utils.obj_to_meta

fun run_completion global_meta_rws ctxt terminates E e =
  let val thy = ctxt |> Proof_Context.theory_of
      val e = modify e
      val ctxt = if can Local_Theory.target_of ctxt
                 then Local_Theory.target_of ctxt
                 else ctxt
      val generate_cps = Config.get ctxt Ground_Completion.generate_cps
      val _ = tracing ("Completing: " ^ Utils.str_of_thms' E)
      val _ = tracing ("with: " ^ Utils.str_of_thms' [e])
      val deps = Utils.definitional_dependencies thy ([], Thm.full_prop_of e)
                  |> map Const
(*      val f_map_eq = deps
                    |> map (rpair 0)*)
     val f_map_less = map_index (fn (x,y) => (y,x)) deps
(*     val f_map_greater = map_index (fn (x,y) => (y,x)) (rev deps)
     val f_maps = f_map_eq*)
  in if not (Utils.permutative_rule e) andalso
        not (terminates [e]) andalso
        not (terminates [Utils.commute_meta_eq e])
     then E
        |> tap (fn TRS => tracing ("Done: " ^ Utils.str_of_thms' TRS))
     else
     [complete global_meta_rws thy ctxt LESS generate_cps terminates f_map_less,
      complete global_meta_rws thy ctxt GREATER generate_cps terminates f_map_less]
(*      |> get_first (fn f => SOME (f (e :: E)))*)
      |> Par_List.get_some (fn f => SOME (f (e :: E)))
      |> the
      |> tap (fn TRS => tracing ("Done: " ^ Utils.str_of_thms' TRS))
  end

fun run_completion' global_meta_rws ctxt terminates E e =
    let val rules = run_completion global_meta_rws ctxt terminates E e
        val thy = Proof_Context.theory_of ctxt
        val additions = filter_out (fn r => exists (Thm.equiv_thm thy o pair r) E) rules
        val deletions = filter_out (fn e => exists (Thm.equiv_thm thy o pair e) rules) E
    in (additions, deletions) end

fun discriminate_cpairs global_meta_rws ctxt terminates E e =
  let (*val _ = tracing ("Discriminating cpairs: " ^ Utils.str_of_thms E)
      val _ = tracing ("with: " ^ Utils.str_of_thms [e])*)
      val e = modify e
      val thy = Proof_Context.theory_of ctxt
      val cpairs = (semi_critical_pairs thy LESS E [e] @
                    semi_critical_pairs thy LESS [e] E)
                    (* Normalize critical pairs *)
                    |> map (rewrite_rule ctxt terminates E)
                    (* Filter True *)
                    |> filter (fn cp => @{prop "True"} <> Thm.full_prop_of cp)
                    (* Rulify normalizations *)
                    |> map modify
                    (* Orient normalizations *)
                    |> map (Utils.orient_meta_rule thy LESS)
                    (* Filter rules where lhs = rhs *)
                    |> filter ((op <>) o Utils.dest_meta_equation)
                    |> Utils.make_theorem_set
                    |> map (fn th => (th, Drule.size_of_thm th))
                    |> sort (int_ord o (apply2 snd))
                    |> map fst
      val deps = Utils.definitional_dependencies thy ([], Thm.full_prop_of e)
                  |> map Const
(*      val f_map_eq = deps
                    |> map (rpair 0)*)
      val f_map_less = map_index (fn (x,y) => (y,x)) deps
      (* Completion will subsume this function if CP generation is enabled *)
      val ctxt = Config.put Ground_Completion.generate_cps false ctxt
(*      val E' = Par_List.map (fn cp =>
                            (cp, memoized_joinable ctxt terminates f_map_less E cp)) (e :: cpairs)
                    |> map_filter (fn (_, true) => NONE
                                    | (cp, false) => SOME cp)
                    |> tap (fn cp => tracing ("Non joinable CPs: " ^ Utils.str_of_thms' cp))*)
  in (*case E' of
      e :: E' => run_completion [] ctxt terminates (E @ E') e
    | [] => E*)
    (E, e :: cpairs)
      |> Library.foldl (fn (E, cp) =>
            let val rule = cp |> rewrite_rule ctxt terminates E
                              |> modify
                              |> Utils.orient_meta_rule thy LESS
                val (lhs, rhs) = Utils.dest_meta_equation rule
            in if lhs = rhs orelse
                  memoized_joinable ctxt terminates f_map_less E rule
               then E
               else let val _ = tracing ("Adding cp: " ^ Utils.str_of_thms' [rule])
                    in run_completion [] ctxt terminates E rule end
            end)
(*      |> tap (fn TRS => tracing ("Done: " ^ Utils.str_of_thms' TRS))*)
  end


end

structure Conditional_Completion : CONDITIONAL_COMPLETION = DB_Conditional_Completion
