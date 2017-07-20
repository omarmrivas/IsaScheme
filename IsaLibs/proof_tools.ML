(*  Title:      proof_tools.ML
    ID:         $Id: proof_tools.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Important proof methods.
*)

signature PROOF_TOOLS =
sig
  val max_depth_in_meta_induction  : int Config.T
  val max_num_generalizations      : int Config.T
  val max_consts_in_generalizations: int Config.T
(*  val max_lambda_size              : int Config.T*)
  val use_metis                    : bool Config.T

  val normalise_thm        :  Proof.context -> thm list -> thm -> thm
  val normalise_thm_empty_simpset : Proof.context -> thm list -> thm -> thm
  val normalise_conjecture :  Proof.context -> thm list -> term -> term
  val meta_induction : (term list -> term list -> Proof.context -> theory -> int -> thm list -> term option)
                       -> Proof.context -> int -> term -> (thm list * thm list) option
  val find_lemmas : term list -> term list -> Proof.context -> theory -> int -> thm list -> term option

end

structure DB_Proof_Tools
(* : PROOF_TOOLS *)
= struct

val (max_depth_in_meta_induction, setup_max_depth_in_meta_induction) = Attrib.config_int @{binding "max_depth_in_meta_induction"} (K 10)
val (max_num_generalizations, setup_max_num_generalizations) = Attrib.config_int @{binding "max_num_generalizations"} (K 2)
val (max_consts_in_generalizations, setup_max_consts_in_generalizations) = Attrib.config_int @{binding "max_consts_in_generalizations"} (K 2)
(*val (max_lambda_size, setup_max_lambda_size) = Attrib.config_int @{binding "max_lambda_size"} (K 8)*)
val (use_metis, setup_use_metis) = Attrib.config_bool @{binding "use_metis"} (K true)

val path = Path.explode "proof_tools.log"

fun normalise_thm ctxt simps thm =
  let val ctxt = ctxt |> Context.Proof
                      |> Simplifier.map_ss (fn simpset => simpset addsimps simps)
                      |> Context.the_proof
      val limit = Prover.max_time_in_proof
                    |> Config.get ctxt
                    |> Time.fromSeconds
  in
    Timeout.apply limit
    (simplify ctxt) thm
    handle Timeout.TIMEOUT t => (if File.exists path
                                 then ()
                                 else Utils.create_log path;
                       Utils.trace_log path ("Timeout in :" ^ Utils.str_of_thms [thm]);
                       raise Timeout.TIMEOUT t)
         | unknown => (if File.exists path
                       then ()
                       else Utils.create_log path;
                       Utils.trace_log path ("Unknown: " ^ Utils.str_of_thms [thm]);
                       raise unknown)
  end

fun normalise_thm_empty_simpset ctxt simps thm =
  let val limit = Prover.max_time_in_proof
                    |> Config.get ctxt
                    |> Time.fromSeconds
      val ctxt =  ctxt |> empty_simpset
                       |> Context.Proof
                       |> Simplifier.map_ss (fn simpset => simpset addsimps simps)
                       |> Context.the_proof
  in
    Timeout.apply limit
    (simplify ctxt) thm
    handle Timeout.TIMEOUT t => (if File.exists path
                                 then ()
                                 else Utils.create_log path;
                       Utils.trace_log path ("Timeout in :" ^ Utils.str_of_thms [thm]);
                       raise Timeout.TIMEOUT t)
         | unknown => (if File.exists path
                       then ()
                       else Utils.create_log path;
                       Utils.trace_log path ("Unknown: " ^ Utils.str_of_thms [thm]);
                       raise unknown)
  end

fun normalise_conjecture ctxt simps prop =
  let val ctxt = ctxt |> Context.Proof
                      |> Simplifier.map_ss (fn simpset => simpset addsimps simps)
                      |> Context.the_proof
  in
    prop
    |> Prover.cheat_prover ctxt
    |> simplify ctxt
    |> Thm.full_prop_of
    handle THM _ => prop
  end

fun test_by_generality_all f rel set =
  let val classes = Utils.classify_poset rel set
  in case get_first (fn class =>
              let val res = class |> (fn L => if null L then [] else Par_List.map f L)
                                  |> map_filter I
              in if null res
                 then NONE
                 else SOME res end) classes of
      SOME res => res
    | NONE => [] end

fun test_by_generality_some f rel set =
  let val classes = Utils.classify_poset rel set
  in get_first (fn L => if null L
                        then NONE
                        else Par_List.get_some f L) classes
  end

fun construct_rhs ctxt thy counterex_timeout consts size lemmas lhs =
  let val typ = type_of lhs
      val consts_str = consts |> map ((Syntax.string_of_term ctxt) o Const)
                              |> space_implode ", "
      val _ = tracing ("LHS: " ^ Syntax.string_of_term ctxt lhs ^ ", Consts: " ^ consts_str)
      val vars = Term.add_frees lhs []
      val typs = map snd vars @ map snd consts
      val target_type = typs ---> typ
      val lambda_terms = Enumerated_Terms.generate_terms thy target_type (length typs + size)
      fun equation lambda =
         ((lambda, map Free vars @ map Const consts)
            |> Term.betapplys
            |> Envir.beta_eta_contract
            |> pair lhs
            |> HOLogic.mk_Trueprop o HOLogic.mk_eq
            |> Utils.dummyfy_term
            |> Syntax.check_term ctxt
            |> (fn t => Logic.unvarify_types_global t
                        handle TERM _ => t)
            |> normalise_conjecture (empty_simpset ctxt) lemmas
                           (* Equation is trivial, discard equation *)
            |> (fn t => if Utils.bad_equation' thy t
                        then NONE
                        else SOME t))
            handle TYPE _ => NONE
      val equations = lambda_terms |> map_filter equation
                                   |> Utils.make_term_set' thy
  in equations
      |> test_by_generality_some
            (Counter_Example.unfalsified_conjecture ctxt counterex_timeout)
            (Pattern.matches thy o apfst Logic.varify_global o apply2 Utils.lhs)
  end

fun construct_rhs' ctxt thy counterex_timeout consts_seq size lemmas lhs =
  case Seq.pull consts_seq of
    SOME (consts, consts_seq) =>
     (case construct_rhs ctxt thy counterex_timeout
                         consts size lemmas lhs of
          SOME x => SOME x
        | NONE => construct_rhs' ctxt thy counterex_timeout
                                 consts_seq size lemmas lhs)
  | NONE => NONE

fun not_constructor thy (Const c) = is_none (Old_Datatype_Data.info_of_constr thy c)
  | not_constructor _ _ = false

fun construct_sequence goals ctxt thy max_consts counterex_timeout lambda_size lemmas generalized_lhs =
  let val consts =
          ([], goals)
              |> Library.foldl (Utils.definitional_dependencies thy)
              |> filter_out (fn (name, _) => name = Const_Names.hol_eq)
      val deps_str = consts |> map ((Syntax.string_of_term ctxt) o Const)
                            |> space_implode ", "
      val _ = tracing ("Dependencies..." ^ deps_str)
      val n = length consts
      val max_len = (1 upto max_consts)
                      |> map (fn k => Utils.binomial_coefficient n k)
                      |> pair 0
                      |> Library.foldl (op +)
      val _ = tracing ("Analysing " ^ string_of_int max_len ^ " subsets ...")
      val consts_seq = consts |> Utils.lazy_subsets
                              |> Seq.take max_len
      fun trace t = ((tracing o (fn txt => "LHS: " ^ txt) o (Syntax.string_of_term ctxt)) t; t)
  in generalized_lhs
       |> get_first ((construct_rhs' ctxt thy counterex_timeout
                                     consts_seq lambda_size lemmas) o trace)
       |> (fn R => (case R of
                     SOME conjecture => [conjecture]
                   | NONE => []))
  end

fun find_lemmas goals subgoals ctxt thy counterex_timeout lemmas =
  let val num_generalizations = Config.get ctxt max_num_generalizations
      val max_consts = Config.get ctxt max_consts_in_generalizations
      val lambda_size = Config.get ctxt Random_Terms.max_lambda_size
      val equations_in_subgoals =
        subgoals |> maps (Utils.equations thy)
                 |> map (Utils.orient_eq thy GREATER)
                 |> Utils.make_term_set' thy
                 |> (fn L => if null L
                             then []
                             else Par_List.map ((Counter_Example.unfalsified_conjecture ctxt counterex_timeout) o HOLogic.mk_Trueprop) L)
                 |> map_filter I
(*                 |> tap (fn _ => tracing "=================== equations in subgoals ")
                 |> tap (map (tracing o (Syntax.string_of_term ctxt)))
                 |> tap (fn _ => tracing "=================== equations in subgoals ")*)
                 |> map HOLogic.dest_Trueprop
      val generalized_lhs =
        equations_in_subgoals
        |> maps ((fn (lhs, rhs) => [lhs, rhs]) o HOLogic.dest_eq)
        |> filter ((not_constructor thy) o fst o strip_comb)
        |> Utils.generalizations' thy num_generalizations
        (* at least two consts must be present on LHS *)
        |> filter (fn t => fold_aterms (fn Const _ => (fn n => n + 1)
                                         | _ => fn n => n) t 0 >= 2)
(*        |> tap (fn _ => tracing "=================== generalized_lhs ")
        |> tap (map (tracing o (Syntax.string_of_term ctxt)))
        |> tap (fn _ => tracing "=================== generalized_lhs ")*)
      val generalizations =
        equations_in_subgoals
          |> Utils.generalizations' thy num_generalizations
(*          |> map (normalise_conjecture ctxt lemmas o HOLogic.mk_Trueprop)
          |> filter_out Utils.is_trivial*)
          |> map (Utils.orient_eq thy GREATER)
          |> Utils.make_term_set' thy
          (* filter equations *)
          |> filter_out ((Utils.bad_equation thy) o HOLogic.dest_eq)
          |> map HOLogic.mk_Trueprop
          |> test_by_generality_all (Counter_Example.unfalsified_conjecture ctxt counterex_timeout)
                                    (Pattern.matches thy o apfst Logic.varify_global o apply2 Utils.lhs)
(*          |> tap (fn _ => tracing "==================== generalizations ")
          |> tap (map (tracing o (Syntax.string_of_term ctxt)))
          |> tap (fn _ => tracing "==================== generalizations ")*)
      val eqs = map HOLogic.mk_Trueprop equations_in_subgoals @ generalizations
      val generalized_lhs =
          generalized_lhs |> filter_out (fn lhs => exists (Pattern.matches thy o apfst Logic.varify_global o apfst Utils.lhs o rpair lhs) eqs)
(*        |> tap (fn _ => tracing "=================== generalized_lhs' ")
        |> tap (map (tracing o (Syntax.string_of_term ctxt)))
        |> tap (fn _ => tracing "=================== generalized_lhs' ")*)
      val equations =
        eqs
         |> (fn eqs => 
              let val lhss = map Utils.lhs eqs
              in if exists (fn lhs =>
                    exists (Pattern.matches thy o apfst Logic.varify_global o pair lhs) generalized_lhs) lhss
                 then eqs
                 else generalized_lhs
                        |> construct_sequence goals ctxt thy max_consts
                                              counterex_timeout lambda_size lemmas
                        |> (fn l => let val l = l (*|> map (normalise_conjecture ctxt lemmas)
                                                  |> filter_out Utils.is_trivial*)
                                    in eqs @ l end) end)
  in equations
     |> Utils.make_term_set' thy
     |> filter_out (fn c =>
        exists (fn g => Pattern.equiv thy (c |> Logic.varify_global
                                             |> Logic.incr_indexes ([], [], 1),
                                           Logic.varify_global g)) goals)
(*     |> tap (fn _ => tracing "=================== Results ")
     |> tap (map (tracing o (Syntax.string_of_term ctxt)))*)
     |> filter_out (Utils.bad_equation' thy)
     |> filter_out (fn eq => exists (Pattern.matches thy o apfst Logic.varify_global o apply2 Utils.lhs o rpair eq) goals)
     |> Utils.sort_poset (Pattern.matches thy o
                          apfst Logic.varify_global o
                          apply2 Utils.lhs)
(*     |> tap (fn _ => tracing "=================== Results ")
     |> tap (map (fn (i, t) => tracing (string_of_int i ^ ": " ^ Syntax.string_of_term ctxt t)))
     |> tap (fn _ => tracing "=================== Results ")*)
     |> (fn L => if null L then NONE else L |> snd o hd
                                            |> tap (fn t => tracing ("Result: " ^ Syntax.string_of_term ctxt t))
                                            |> SOME) end

(*fun rewrites_lhs thy conjecture lemma =
  ((Pattern.matches thy) o (apply2 Utils.lhs) o (apfst Thm.full_prop_of)) (lemma, conjecture)

fun proved_by_rewriting ctxt lemmas proof_timeout conjecture =
  let val method = Method.Basic (SIMPLE_METHOD o (fn ctxt => Raw_Simplifier.rewrite_goals_tac ctxt lemmas))
  in case prove ctxt (SOME lemmas) method conjecture proof_timeout of
         SOME _ => true
       | NONE => false end*)

fun meta_induction_aux method ctxt thy proof_timeout
                        counterex_timeout limit conjecture =
  let val consts = ([], conjecture)
                  |> Utils.definitional_dependencies thy
                  |> map fst
      val simps = maps (Utils.get_rewrites thy) consts
      fun test_simp th = exists (Thm.equiv_thm thy o pair th) simps
      val f_map = Utils.definitional_dependencies thy ([], conjecture)
                    |> map Const
                    |> map (rpair 0)
      fun alpha i lemmas (conjecture :: conjectures) =
      let val net = Unsynchronized.ref Net.empty
          val set = Unsynchronized.ref Net.empty
          val method = Method.Basic (SIMPLE_METHOD o (InductiveTacs4.induct_auto_tac' set net))
                        |> rpair Position.no_range
          val terminates = Aprove.memoized_terminates ctxt
          val lemmas' = map Utils.obj_to_meta lemmas
          val conjecture' = (Logic.mk_equals o HOLogic.dest_eq o HOLogic.dest_Trueprop) conjecture
          (* FIXME: only one f_map is not enough for joinability test *)
        in if Ground_Completion.memoized_joinable' ctxt terminates f_map lemmas' conjecture'
         then alpha (i - 1) lemmas conjectures
         else case Prover.prove ctxt (SOME (filter_out test_simp lemmas))
                                method conjecture proof_timeout of
         SOME thm => 
         let val thm' = Utils.obj_to_meta thm
             val rules = thm' |> Ground_Completion.run_completion [] ctxt terminates lemmas'
                              |> map Utils.meta_to_obj
         in alpha (i - 1) rules conjectures end
       | NONE => let val subgoals = Net.content (!net)
                 in beta (i + 1) lemmas subgoals (conjecture :: conjectures) end
      end
      |   alpha _ lemmas [] = SOME lemmas and
      beta i lemmas subgoals conjectures =
      if i < limit
      then case method conjectures subgoals ctxt thy counterex_timeout lemmas of
          SOME conjecture => alpha i lemmas (conjecture :: conjectures)
        | NONE => NONE
      else NONE
    val lemmas = global_lemmas ctxt conjecture
  in case alpha 0 lemmas [conjecture] of
      SOME rules => let val additions = filter_out (fn r => exists (Thm.equiv_thm thy o pair r) lemmas) rules
                        val deletions = filter_out (fn e => exists (Thm.equiv_thm thy o pair e) rules) lemmas
                    in SOME (additions, deletions) end
    | NONE => NONE
  end

fun meta_induction method ctxt limit conjecture =
  let val thy = Proof_Context.theory_of ctxt
      val proof_timeout = Config.get ctxt Prover.max_time_in_proof
      val counterex_timeout = Config.get ctxt Counter_Example.max_time_in_counter_ex
  in if Counter_Example.counter_example ctxt counterex_timeout conjecture
     then NONE
     else meta_induction_aux method ctxt thy proof_timeout
                             counterex_timeout limit conjecture
  end

fun meta_induction_tac lemmas_ref method ctxt =
  SUBGOAL (fn (goal, i) => 
      let val limit = Config.get ctxt max_depth_in_meta_induction
      in case Utils.timing_wrapper (meta_induction method ctxt limit) goal of
          SOME (lemmas, _) =>
            let val _ = lemmas_ref := lemmas
            in asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps lemmas) i end
        | NONE => no_tac
      end)

fun generalization_tac lemmas_ref ctxt =
  meta_induction_tac lemmas_ref find_lemmas ctxt

end

structure Proof_Tools : PROOF_TOOLS = DB_Proof_Tools

