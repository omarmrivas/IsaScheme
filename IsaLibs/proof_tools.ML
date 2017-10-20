(*  Title:      proof_tools.ML
    ID:         $Id: proof_tools.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Important proof methods.
*)

signature PROOF_TOOLS =
sig
  val max_num_generalizations              : int Config.T
  val max_time_in_inductive_proof          : int Config.T


end

structure DB_Proof_Tools
(* : PROOF_TOOLS *)
= struct

val (max_num_generalizations, setup_max_num_generalizations) = Attrib.config_int @{binding "max_num_generalizations"} (K 2)

val (max_time_in_inductive_proof, setup_max_time_in_inductive_proof) = Attrib.config_int @{binding "max_time_in_inductive_proof"} (K 3600)

datatype result = Theorem of thm | Failure of term list

type conjecture_store =
  {sequence : (string * term) Seq.seq}

fun mk_conjecture_store sequence : conjecture_store =
  {sequence = sequence}

fun pull_conjecture {sequence} =
  case Seq.pull sequence of
       SOME (conjecture, sequence) =>
          SOME (conjecture, mk_conjecture_store sequence)
      | NONE => NONE

fun add_sequence seq {sequence} =
  mk_conjecture_store (Seq.append sequence seq)

fun orient_prop thy order prop =
  let val concl = (HOLogic.dest_Trueprop o Logic.strip_imp_concl) prop
      val prems = Logic.strip_imp_prems prop
  in (Logic.list_implies o pair prems o HOLogic.mk_Trueprop o Utils.orient_eq thy order) concl end

(*
  Having a conjecture of the form ?f ?x = ?f ?y, construct the conjecture
  ?x = ?y.
*)
fun arg_cong_equation thy eq =
    if can HOLogic.dest_eq eq
    then let val x = Var (("x", 0), @{typ_pat "?'b"})
             val y = Var (("y", 0), @{typ_pat "?'b"})
             val f = Var (("f", 0), @{typ_pat "?'b \<Rightarrow> ?'a"})
             val pattern = HOLogic.mk_eq (f $ x, f $ y)
(*             val (lhs, rhs) = (apply2 (arg_cong_equation thy) o HOLogic.dest_eq) eq
             val eq = HOLogic.mk_eq (lhs, rhs)*)
         in case try (Pattern.match thy (pattern, eq)) (Vartab.empty, Vartab.empty) of
              SOME (tyenv, tenv) => let val env = Envir.Envir {maxidx = 1, tenv = tenv, tyenv = tyenv}
                                        val lhs = Envir.norm_term env x
                                        val rhs = Envir.norm_term env y
                                        val f' = Envir.norm_term env f
                                    in if Utils.is_constructor (Context.proof_of (Context.Theory thy)) f'
                                       then HOLogic.mk_eq (lhs, rhs)
                                       else eq end
            | NONE => eq
             end
    else eq

fun clear_lambda eq =
  if can HOLogic.dest_eq eq
  then case HOLogic.dest_eq eq of
          (a1 as Abs (_,A,_), a2 as Abs (_,B,_)) =>
              let val frees1 = Term.add_frees a1 []
                  val n' = singleton (Name.variant_list (map fst frees1)) "x"
                  val frees2 = Term.add_frees a2 []
                  val m' = singleton (Name.variant_list (map fst frees2)) "y"
              in
                HOLogic.mk_eq (betapply (a1,Free (n',A)), betapply (a2,Free (m',B)))
                  |> clear_lambda 
              end
         | _ => eq
  else eq

fun apply_until_no_change f eq =
  let val eq' = f eq
  in if eq = eq'
     then eq
     else apply_until_no_change f eq'
  end

(* FIXME: describe this clearly *)
fun apply_heuristics thy prop =
  (let val concl = (HOLogic.dest_Trueprop o Logic.strip_imp_concl) prop
                     |> apply_until_no_change (clear_lambda o arg_cong_equation thy)
       val prems = prop |> Logic.strip_imp_prems
                        |> map (apply_heuristics thy)
   in (Logic.list_implies o pair prems o HOLogic.mk_Trueprop) concl
   end) handle TERM _ => prop

(*fun generalize_cond_eq conj =
  let fun make_table positions =
            positions |> pair Term_Tab.empty
                      |> Library.foldl (fn (tab, (t,typ,pos)) =>
                            case Term_Tab.lookup tab t of
                                SOME l => Term_Tab.update (t, (typ,pos) :: l) tab
                              | NONE => Term_Tab.update (t, [(typ,pos)]) tab)
      val names = Term.add_free_names conj []
      val positions = conj |> Utils.positions
                           |> filter (not o is_Const o (fn (t, _, _) => t))
                           |> make_table
                           |> Term_Tab.dest
                           |> filter (fn (_, l) => length l > 1)
                           |> sort (prod_ord int_ord int_ord o apply2 (fn (t, l) => (~ (length l),  ~(size_of_term t))))
                           |> pair []
                           |> Library.foldl (fn (positions, (t,l)) =>
                                   if exists (fn (_, poss) => exists (fn (_, l) => 
                                          exists (fn (_,l) => is_prefix (op =) l poss) l) positions) l
                                   then positions
                                   else (t,l) :: positions)
                           |> rev
                           |> map snd
  in ((conj,names), positions)
                    |> Library.foldl (fn ((conj,names), l) => 
                          let val name = singleton (Name.variant_list names) "x"
                              val typ = (fst o hd) l
                              val poss = map snd l
                          in (Library.foldl (fn (conj, pos) => 
                                Utils.substitute (Free (name,typ),pos) conj) (conj,poss), 
                                name :: names) end)
                    |> fst
  end*)

fun generalize_cond_eq ctxt (SOME conj) =
  let fun make_table positions =
            positions |> pair Term_Tab.empty
                      |> Library.foldl (fn (tab, (t,typ,pos)) =>
                            case Term_Tab.lookup tab t of
                                SOME l => Term_Tab.update (t, (typ,pos) :: l) tab
                              | NONE => Term_Tab.update (t, [(typ,pos)]) tab)
      val timeOut = Config.get ctxt Counter_Example.max_time_in_counter_ex
      val names = Term.add_free_names conj []
      val positions = conj |> Utils.positions
                           |> filter (not o is_Const o (fn (t, _, _) => t))
                           |> make_table
                           |> Term_Tab.dest
                           |> filter (fn (_, l) => length l > 1)
                           |> sort (prod_ord int_ord int_ord o apply2 (fn (t, l) => (~ (length l),  ~(size_of_term t))))
                           |> pair []
                           |> Library.foldl (fn (positions, (t,l)) =>
                                   if exists (fn (_, poss) => exists (fn (_, l) => 
                                          exists (fn (_,l) => is_prefix (op =) l poss) l) positions) l
                                   then positions
                                   else (t,l) :: positions)
                           |> rev
                           |> map snd
  in ((conj,names), positions)
                    |> Library.foldl (fn ((conj,names), l) => 
                          let val name = singleton (Name.variant_list names) "x"
                              val typ = (fst o hd) l
                              val poss = map snd l
                          in (Library.foldl (fn (conj, pos) => 
                                Utils.substitute (Free (name,typ),pos) conj) (conj,poss), 
                                name :: names) end)
                    |> fst
                    |> (fn t => if Counter_Example.memoized_counter_example ctxt timeOut t
                                then if t <> conj
                                     then (if Counter_Example.memoized_counter_example ctxt timeOut conj
                                           then NONE
                                           else SOME conj)
                                     else NONE
                                else SOME t)
  end
  | generalize_cond_eq _ NONE = NONE

(*fun generalize_assumptions ctxt conj =
  let val prems = Logic.strip_imp_prems conj
      val concl = Logic.strip_imp_concl conj
      val prems_seq = Utils.lazy_subsets prems
      val conjs = prems_seq |> Seq.map (Logic.list_implies o rpair concl)
                            |> Seq.list_of
      val timeOut = Config.get ctxt Counter_Example.max_time_in_counter_ex
  in get_first (fn conj =>
      if Counter_Example.memoized_counter_example ctxt timeOut conj
      then NONE
      else SOME conj) conjs end*)

fun generalize_assumptions ctxt (SOME conj) =
  let val prems = Logic.strip_imp_prems conj
      val concl = Logic.strip_imp_concl conj
      val prems_seq = Utils.lazy_subsets prems
      val conjs = prems_seq |> Seq.map (Logic.list_implies o rpair concl)
                            |> Seq.list_of
      val timeOut = Config.get ctxt Counter_Example.max_time_in_counter_ex
  in get_first (fn conj =>
      if Counter_Example.memoized_counter_example ctxt timeOut conj
      then NONE
      else SOME conj) conjs end
  | generalize_assumptions _ NONE = NONE

fun not_prop_frees conj =
    Term.add_frees conj []
        |> forall (fn (_, ty) => ty <> @{typ "prop"})

fun not_prop_frees' (SOME conj) =
  if Term.add_frees conj []
       |> forall (fn (_, ty) => ty <> @{typ "prop"})
  then SOME conj
  else NONE
 |  not_prop_frees' NONE = NONE
   


fun gen_simplify ctxt thy order simps_ref subsumed (SOME conj) =
  (let val conj = conj |> Utils.normalise_term ctxt (!simps_ref)
                      |> apply_heuristics thy o Utils.rulify ctxt
                      |> orient_prop thy order
      val (lhs,rhs) = Utils.dest_eq conj
  in if lhs = rhs orelse
        subsumed conj orelse
        subsumed (Utils.commute_eq conj)
     then NONE
     else SOME conj
  end handle CTERM _ => NONE)
  | gen_simplify _ _ _ _ _ NONE = NONE

fun generalize1 ctxt thy order simps_ref subsumed (meth,conj) =
  (* Eliminate all conjectures with frees of type prop, e.g. @{term "PROP x \<Longrightarrow> PROP x"} *)
  if not_prop_frees conj
  then conj |> SOME
            |> generalize_assumptions ctxt
            |> generalize_cond_eq ctxt
            |> gen_simplify ctxt thy order simps_ref subsumed
            |> not_prop_frees'
            |> (fn SOME conj => SOME (meth, conj)
                  | NONE => NONE)
            handle CTERM err => (tracing "generalize1"; raise CTERM err)
  else NONE

fun generalize2 ctxt thy order simps_ref subsumed (meth,conj) =
  (* Eliminate all conjectures with frees of type prop, e.g. @{term "PROP x \<Longrightarrow> PROP x"} *)
  if not_prop_frees conj
  then conj |> SOME
            |> generalize_cond_eq ctxt
            |> generalize_assumptions ctxt
            |> gen_simplify ctxt thy order simps_ref subsumed
            |> not_prop_frees'
            |> (fn SOME conj => SOME (meth, conj)
                  | NONE => NONE)
            handle CTERM err => (tracing "generalize2"; raise CTERM err)
  else NONE

(*fun generalize timeOut ctxt thy order simps_ref frees (table, typsub) classes subsumed (meth,conj) =
  (* Eliminate all conjectures with frees of type prop, e.g. @{term "PROP x \<Longrightarrow> PROP x"} *)
  if not_prop_frees conj
  then
    case generalize_assumptions ctxt conj of
      SOME conj => 
        let val conj = conj |> Utils.normalise_term ctxt (!simps_ref)
                            |> apply_heuristics thy o Utils.rulify ctxt
                            |> orient_prop thy order
            val (lhs,rhs) = Utils.dest_eq conj
        in if lhs = rhs orelse
              subsumed conj orelse
              subsumed (Utils.commute_eq conj)
           then NONE
           else let val g = generalize_cond_eq conj
                in if Utils.pattern_equiv' thy (g, conj)
                        (* This is the part for theory exploration? *)
                   then SOME (meth, conj)(*let val subst = frees |> Utils.injective_subst (Term.add_frees g [])
                                              |> the
                                              |> map (apply2 Free)
                                              |> Term.subst_free
                            val (lhs, rhs) = Utils.dest_eq (subst g)
                            val num_gen = Config.get ctxt max_num_generalizations
                            val conjs = [lhs,rhs]
                                        |> Utils.generalizations' thy num_gen
                                        |> Seq.of_list
                                        |> DB_EQ_Terms.discover_equations2 ctxt [] simps_ref table typsub classes
                                        |> Seq.list_of
                        in case find_first (not o (Counter_Example.memoized_counter_example ctxt timeOut)) conjs of
                                  SOME conj => SOME (meth, conj)
                                | NONE => SOME (meth, conj) end*)
                   else if not (Counter_Example.memoized_counter_example ctxt timeOut g)
                        then SOME (meth, orient_prop thy order g)
                        else SOME (meth, conj)
          end
          handle TYPE err => (tracing meth; tracing (Utils.print_term conj); raise TYPE err)
               | TERM err => (tracing meth; tracing (Utils.print_term conj); raise TERM err)
        end
    | NONE => NONE
  else NONE*)

(* This function filters conjectures difficult to prove for the
  inductive tactic  *)
fun filter_conjectures conj =
  let fun fun_eq (Const (name, _) $ lhs $ _) =
            if name = Const_Names.hol_eq
            then can (dest_funT o type_of) lhs
            else false
        | fun_eq _ = false
  in Term.exists_subterm fun_eq conj end

fun inductive_prover ctxt tactic timeOut prop =
  let val start = Timing.start ()
      (*val _ = tracing ("Setting timeout: " ^ string_of_int timeOut ^ "s.")*)
      val prop = Object_Logic.rulify_term ctxt prop
      val thy = Proof_Context.theory_of ctxt
      val _ = tracing "Getting definitional rewrites..."
      val def_lemmas = Utils.get_definitional_rewrites thy prop
      val _ = tracing "Done"
      val lemmas_ref = Unsynchronized.ref def_lemmas
      val lthy_nodefs = ctxt delsimps def_lemmas
      val ctxt_nodefs = (Local_Theory.target_of ctxt) delsimps def_lemmas
      val _ = tracing "Latex Goal: "
      val _ = tracing (Utils.latex_string_of_term ctxt prop)
      val _ = tracing "Goal: "
      val _ = tracing (Utils.string_of_term ctxt prop)
(*      val lambda_size = Config.get ctxt Random_Terms.max_lambda_size*)
(*      val n = Config.get ctxt EQ_Terms.max_random_terms*)
      val _ = tracing "Preprocessing conjecture..."
(*      val (table, typsub) = EQ_Terms.preprocess_conjecture ctxt n prop*)
      val _ = tracing "Done"
      fun try_prove simps conj =
        let val failures = Unsynchronized.ref (Net.empty : term Net.net)
            val _ = tracing ("Proving: " ^ Utils.string_of_term' ctxt conj)
        in (case Prover.prove_from_tactic ctxt_nodefs (SOME simps) (tactic failures lemmas_ref) conj timeOut of
          SOME thm => (tracing ("Proved!: " ^ Utils.str_of_terms ctxt [conj]);Theorem thm)
        | NONE => (!failures) |> Net.content
                              |> Failure)
            handle ERROR err => (tracing "try_prove"; raise ERROR err)
        end
      fun add_term_to_net net t =
          t |> Logic.varify_global
            |> Term_Subst.zero_var_indexes
            |> (fn t => Net.insert_term_safe (Pattern.equiv thy) (t, t) net)
      fun add_thm_to_net net thm =
            thm |> Thm.full_prop_of
                |> (fn t => Net.insert_term_safe (Pattern.equiv thy) (t, t) net)
      fun add_thms_to_net net thms =
          Library.foldl (fn (net, thm) => add_thm_to_net net thm) (net, thms)
      fun subsumed_in_net net t =
            t |> Net.match_term net
              |> exists (fn t' => Pattern.matches thy (t', t))
      fun next_subgoal simps subgoals =
            (* Stop proving conjectures if original goal is already proved *)
        let val proved = prop |> Utils.normalise_term ctxt_nodefs simps
                              |> (fn prop => prop = @{prop "True"})
            val subgoals' = 
                if proved
                then []
                else subgoals |> map (Object_Logic.rulify_term ctxt)
                              |> map (Utils.normalise_term ctxt_nodefs simps)
                              |> map (apply_heuristics thy o Utils.rulify ctxt)
                              |> map (orient_prop thy LESS)
                              |> filter (fn prop => let val (lhs,rhs) = Utils.dest_eq prop
                                                    in lhs <> rhs end)
                              |> Utils.make_term_set' thy
                              |> Utils.sort_by_general thy
        in if null subgoals'
           then NONE
           else case Par_List.get_some (fn conj =>
                        case try_prove simps conj of
                          Theorem _ => SOME (conj, remove (op =) conj subgoals')
                          | _ => NONE) subgoals' of
                   SOME (conj, subgoals) => SOME (conj, subgoals)
                 | NONE => SOME (hd subgoals', tl subgoals')
        end handle CTERM err => (tracing "next_subgoal"; raise CTERM err)
      fun next_conjecture thy simps net store =
        (case pull_conjecture store of
            SOME ((meth, conjecture), store) =>
              if not_prop_frees conjecture
              then
              let val _ = tracing ("Normalising (" ^ meth ^ "): " ^ Utils.string_of_term' ctxt conjecture)
                  val conjecture = conjecture |> Utils.normalise_term lthy_nodefs simps
                                              |> (apply_heuristics thy o Utils.rulify ctxt)
                                              |> (orient_prop thy LESS)
                  val (lhs,rhs) = Utils.dest_eq conjecture
              in if lhs = rhs orelse
                    filter_conjectures conjecture orelse
                    subsumed_in_net net conjecture orelse
                    subsumed_in_net net (Utils.commute_eq conjecture)
                 then (tracing "subsumed or rejected"; next_conjecture thy simps net store)
                 else SOME (orient_prop thy LESS conjecture, store)
              end
              else (tracing ("discarding: " ^ Utils.string_of_term' ctxt conjecture);
                    next_conjecture thy simps net store)
          | NONE => NONE) handle CTERM err => (tracing "next_conjecture"; raise CTERM err)
      val terminates = Aprove.memoized_terminates ctxt_nodefs
      fun build_trs lemmas rule =
          let val TRS = map Utils.obj_to_meta lemmas
              val e = Utils.obj_to_meta rule
          in e |> Conditional_Completion.run_completion [] ctxt_nodefs terminates TRS
(*               |> Conditional_Completion.discriminate_cpairs [] ctxt_nodefs terminates TRS*)
               |> map Utils.meta_to_obj end
               handle CTERM err => (tracing "build_trs"; raise CTERM err)
      val _ = tracing "Calculating equational theory exploration sequence..."
(*      val classes = Unsynchronized.ref (Term_List_Tab.empty, Term_Tab.empty)*)
      val eq_tx = Seq.empty
(*      val (frees, eq_tx) =
              prop |> DB_EQ_Terms.equational_theory_exploration2 ctxt_nodefs (table, typsub) lambda_size lemmas_ref [] classes
                   ||> Seq.map (Object_Logic.rulify_term ctxt)
                   ||> Seq.map (pair "EQ_TX")*)
      val _ = tracing "Done"
      val _ = tracing "Calculating known equational laws sequence..."
(*      val known_laws = DB_EQ_Terms.known_laws ctxt_nodefs prop
                  |> Seq.map (Object_Logic.rulify_term ctxt)
                  |> Seq.map (pair "EQ_KNOWN")*)
      val known_laws = Seq.empty
      val _ = tracing "Done"
      val conj_store = known_laws |> mk_conjecture_store
                                  |> add_sequence eq_tx
(*      val conj_store = mk_conjecture_store Seq.empty*)
      fun recursive_prover foo store net subgoals lemmas conj =
        case try_prove lemmas conj of
          Theorem thm =>(let val lemmas = build_trs lemmas thm
                             val _ = lemmas_ref := lemmas
                             val net = add_thms_to_net net lemmas
                         in case next_subgoal lemmas subgoals of
                          SOME (goal, subgoals) => recursive_prover (not foo) store net subgoals lemmas goal
                        | NONE => SOME lemmas end)
        | Failure trms =>
            let val net = add_term_to_net net conj
                val lemmas' = lemmas |> map Thm.full_prop_of
                                     |> map Logic.unvarify_global
                val failures = trms |> map (fst o Utils.binder_elimination Const_Names.meta_forall [])
                                    (* FIXME: why subgoals have vars? *)
                                    |> filter (not o Term.exists_subterm Term.is_Var)
                                    (* FIXME: why subgoals have frees of type prop? *)
                                    |> filter not_prop_frees
                                    |> Utils.sort_by_general thy
                                    |> Seq.of_list
                                    |> Seq.map (Object_Logic.rulify_term ctxt)
(*                                    |> Seq.filter not_prop_frees*)
                                    |> Seq.map (pair "EQ_FROM_FAILURE")
                val walsh =
                       (subgoals@lemmas')
                       (* FIXME: why subgoals have frees of type prop? *)
                          |> filter not_prop_frees
                          |> Seq.of_list
                          |> Seq.map (Object_Logic.rulify_term ctxt)
                          |> Seq.maps (fn subgoal =>
                                    Divergence.conditional_walsh_critic ctxt_nodefs lemmas [subgoal, conj]
                                    handle ERROR err => (tracing "WALSH"; raise ERROR err)
                                          | CTERM err => (tracing "WALSH"; raise CTERM err))
                          |> Seq.map (pair "WALSH")
                val transverse =
                      (subgoals@lemmas')
                       (* FIXME: why subgoals have frees of type prop? *)
                          |> filter not_prop_frees
                          |> Seq.of_list
                          |> Seq.map (Object_Logic.rulify_term ctxt)
                          |> Seq.maps (fn subgoal =>
                                    [subgoal, conj] |> Divergence.conditional_transverse_critic lthy_nodefs lemmas
                                                    |> Seq.map_filter (Prover.prove_schematic_from_method
                                                                      lthy_nodefs (SOME lemmas)
                                                                      (Method.Basic (fn ctxt =>
                                                                        Method.SIMPLE_METHOD
                                                                          (tactic (Unsynchronized.ref Net.empty) lemmas_ref ctxt)),
                                                                        (Position.none, Position.none)))
                                                    handle TERM err => (tracing "TRANSVERSE"; raise TERM err)
                                                          | CTERM err => (tracing "TRANSVERSE"; raise CTERM err))
                          |> Seq.map (pair "TRANSVERSE")
                val new_sequence =
                      (Seq.interleave (failures, walsh), transverse)
                        |> Seq.interleave
                        |> Utils.maps_seq Utils.num_processors
                                  (fn (meth, conj) => [generalize1 ctxt_nodefs thy LESS lemmas_ref (subsumed_in_net net) (meth, conj),
                                                       generalize2 ctxt_nodefs thy LESS lemmas_ref (subsumed_in_net net) (meth, conj)]
                                                        |> map_filter I
(*                        |> Utils.map_filter_seq Utils.num_processors
                                  (fn (meth, conj) => generalize timeOut ctxt_nodefs thy LESS lemmas_ref frees (table, typsub) classes (subsumed_in_net net) (meth, conj)*)
                                          handle ERROR err => (tracing ("ERROR exception on: " ^ meth);
                                                              tracing (Utils.print_term conj); raise ERROR err)
                                               | CTERM err => (tracing "new_sequence"; raise CTERM err)
                                               | TERM err => (tracing ("TERM exception on: " ^ meth);
                                                              tracing (Utils.print_term conj); raise TERM err)
                                               | Option => (tracing "Option exception on generalize"; raise Option))
                val store = add_sequence new_sequence store
            in case next_conjecture thy lemmas net store of
                SOME (conjecture, store) => recursive_prover (not foo) store (add_term_to_net net conj) (conj :: subgoals) lemmas conjecture
              | NONE => NONE
            end
      fun result () =
            case recursive_prover true conj_store Net.empty [] def_lemmas prop of
                      SOME thms => (tracing "Latex Simpset: ";
                                    tracing (Utils.latex_str_of_thms thms);
                                    tracing "Simpset: ";
                                    tracing (Utils.str_of_thms thms);
                                    SOME thms)
                    | NONE => (tracing "No simpset!"; NONE)
      val induction_prover_timeout = Time.fromSeconds (Config.get ctxt max_time_in_inductive_proof)
      val res = Timeout.apply induction_prover_timeout result ()
                  handle Timeout.TIMEOUT _ => (tracing "induction_prover_timeout"; NONE)
      val elapsed = start |> Timing.result
                          |> #elapsed
                          |> Time.toReal
      val _ = tracing ("Elapsed time: " ^ string_of_real elapsed)
  in (lthy_nodefs, res) end

(* Failure analysis *)
fun inductive_prover_tactic' ctxt =
  fn (goal, i) =>
    case inductive_prover ctxt Inductive_Tacs.induct_auto_failure_tac (Config.get ctxt Prover.max_time_in_proof) goal of
(*      (ctxt,SOME simps) => (tracing "Proved original goal!"; DB_Inductive_Tacs.final_sledgehammer_tac (ctxt addsimps simps) simps i)*)
      (ctxt,SOME simps) => (tracing "Proved original goal!"; 
              let val (_, ctxt) = Proof_Context.note_thmss "" [((Binding.empty,[]), [(simps,[])])] ctxt
              in Inductive_Tacs.final_sledgehammer_tac ctxt i end)
    | (_,NONE) => (tracing "Not proved!"; no_tac)

fun inductive_prover_sledgehammer_tactic' ctxt =
  fn (goal, i) =>
    case inductive_prover ctxt Inductive_Tacs.induct_auto_sledgehammer_failure_tac (Config.get ctxt Prover.max_time_in_proof) goal of
(*      (ctxt,SOME simps) => (tracing "Proved original goal!"; simp_tac (ctxt addsimps simps) i)*)
      (ctxt,SOME simps) => (tracing "Proved original goal!";
              let val (_, ctxt) = Proof_Context.note_thmss "" [((Binding.empty,[]), [(simps,[])])] ctxt
              in Inductive_Tacs.final_sledgehammer_tac ctxt i end)
    | (_,NONE) => (tracing "Not proved!"; no_tac)

fun inductive_prover_tactic ctxt =
  SUBGOAL (inductive_prover_tactic' ctxt)

fun inductive_prover_sledgehammer_tactic ctxt =
  SUBGOAL (inductive_prover_sledgehammer_tactic' ctxt)

val method_setup_inductive_prover =
  Method.setup (Binding.name "inductive_prover")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (inductive_prover_tactic ctxt 1)))
    "Recursive prover with failure analysis. Interleaves induction and auto and check failures."

val _ = Context.>> (Context.map_theory method_setup_inductive_prover)

val method_setup_inductive_prover =
  Method.setup (Binding.name "inductive_sledgehammer_prover")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (inductive_prover_sledgehammer_tactic ctxt 1)))
    "Recursive prover with failure analysis. Interleaves induction and auto and check failures."

val _ = Context.>> (Context.map_theory method_setup_inductive_prover)


end

structure Proof_Tools : PROOF_TOOLS = DB_Proof_Tools

