(*  Title:      util/induct_tacs.ML
    ID:         $Id: induct_tacs.ML,v 1.010 2015/15/01 14:33:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

An inductive decision procedure using Isabelle's tactics.
This tactic applies auto \<rightarrow> induction \<rightarrow> auto \<rightarrow> failure analysis.
For induction, uses computational induction (prefered) or structural induction.
The tactic searches for free variables in the conjecture to perform induction.
*)

signature INDUCTIVE_TACS =
sig
  (* Utilery tactics *)
  val induct_auto_failure_tac : (thm list -> thm list) -> term Net.net Unsynchronized.ref -> thm list
                                -> Proof.context -> tactic
  val induct_auto_sledgehammer_failure_tac : term Net.net Unsynchronized.ref -> thm list
                                -> Proof.context -> tactic

  val final_sledgehammer_tac: Proof.context -> thm list -> int -> thm -> thm Seq.seq

  val induct_failure_provers_tac : (thm list -> thm list) -> term Net.net Unsynchronized.ref -> thm list -> Proof.context -> tactic
end

structure DB_Inductive_Tacs
(* : INDUCTIVE_TACS *)
= struct

(* This tactic returns all subterms where a recursive function
  is applied to a set of terms with no bound variables. *)
fun inductive_applications thy prop =
  let fun inductive_apps thy prop =
      let val (t,args) = Term.strip_comb prop
      in case t of
           Const _ =>
           (t |> (fst o Term.dest_Const)
              |> (fn name => name ^ ".induct")
              |> (fn name => (args, name, Global_Theory.get_thm thy name))
              |> (fn (args, name, rule) =>
                                        (* args must be free variables *)
                                     if exists (not o is_Free) args (*orelse
                                        exists (exists_subterm is_Bound) args*)
                                     then maps (inductive_apps thy) args
                                     else (args, (name, rule)) :: maps (inductive_apps thy) args)
              handle ERROR _ => maps (inductive_apps thy) args
                    | TERM _ => maps (inductive_apps thy) args)
         | Abs (_, _, t) => t |> inductive_apps thy
                              |> (fn res => res @ maps (inductive_apps thy) args)
         | _ =>  maps (inductive_apps thy) args
      end
      val transform = map (fn arg => SOME (NONE, (arg, false)))
  in prop |> inductive_apps thy
          (* Applications with smaller arguments are considered first *)
          |> sort (int_ord o apply2 (Library.foldl (op +) o pair 0 o map Term.size_of_term o fst))
          |> map (fn (y, z) => (transform y, z))
  end

fun arbitrary args frees =
  let val frees_args = Library.foldl (fn (frees, arg) => Term.add_frees arg frees) ([], args)
  in subtract (op =) frees_args frees end

(* Applies computation induction rules *)
fun computation_induction_tac ctxt thy (goal, i) =
  let val apps = rev (inductive_applications thy goal)
      val frees_goal = Term.add_frees goal []
(*      val _ = map (fn (args, (name, induction)) =>
                    tracing ("params: (" ^ name ^") " ^ Utils.str_of_terms ctxt (map (fst o snd o the) args))) (rev apps)*)
      fun induction_tac x1 x2 x3 x4 x5 x6 x7 x8 =
(*          print_tac ctxt "BEFORE comp induction" THEN*)
          Induction.induction_tac x1 x2 x3 x4 x5 x6 x7 x8 (*THEN
          print_tac ctxt "AFTER comp induction"*)
      val dest = fst o snd o the o hd
  in case apps of
      [] => no_tac
     | app :: apps => 
              apps |> map (fn (args, (name, induction)) =>
                      (* Computation induction on args and making the rest of free variables arbitrary *)
                      DETERM (induction_tac ctxt true [args] [arbitrary [dest args] frees_goal] []
                                                      (SOME [induction]) [] i) APPEND
                      (* Computation induction on args and leaving the rest of free variables alone *)
                      DETERM (induction_tac ctxt true [args] [] []
                                                      (SOME [induction]) [] i))
                   |> pair ((fn (args, (name, induction)) =>
                      DETERM (induction_tac ctxt true [args] [arbitrary [dest args] frees_goal] []
                                                      (SOME [induction]) [] i) APPEND
                      DETERM (induction_tac ctxt true [args] [] [] 
                                                      (SOME [induction]) [] i)) app)
                   |> Library.foldl (op APPEND o swap)
  end

(* Applies structural induction to free datatype variables *)
(* It chooses any free datatype variable available. Probably it would be better
  to perform induction on arguments where the recursive function is  *)
fun structural_induction_tac ctxt (goal, i) =
  let val frees_goal = Term.add_frees goal []
      val frees = frees_goal
                    |> map_filter (fn (s, T) =>
                              let val ind_rules = Induct.find_inductT ctxt T
                              in if null ind_rules
                                 then NONE
                                 else SOME ((s, T), ind_rules) end)
                    |> rev
      fun induction_tac x1 x2 x3 x4 x5 x6 x7 x8 =
(*          print_tac ctxt "BEFORE comp induction" THEN*)
          Induction.induction_tac x1 x2 x3 x4 x5 x6 x7 x8 (*THEN
          print_tac ctxt "AFTER comp induction"*)
  in case frees of
      [] => no_tac
    | free :: frees =>
          frees |> map (fn ((s,T), induction) =>
                      (* Induction on a free variable and making the rest arbitrary *)
                      DETERM (induction_tac ctxt true [[SOME (NONE, (Free (s,T), false))]]
                                                      [arbitrary [Free (s,T)] frees_goal] [] NONE [] i) APPEND
                      (* Induction on a free variable and leaving the rest alone *)
                      DETERM (induction_tac ctxt true [[SOME (NONE, (Free (s,T), false))]]
                                                      [] [] NONE [] i))
                |> pair ((fn ((s,T), induction) =>
                      DETERM (induction_tac ctxt true [[SOME (NONE, (Free (s,T), false))]]
                                                      [arbitrary [Free (s,T)] frees_goal] [] NONE [] i) APPEND
                      DETERM (induction_tac ctxt true [[SOME (NONE, (Free (s,T), false))]]
                                                      [] [] NONE [] i)) free)
                |> Library.foldl (op APPEND o swap)
  end

(* Failure analysis
  Any pending goal is recorded in sts for further analysis. *)
fun check_fail_proof_state sts ctxt =
  fn (goal, _) =>
    if Term.exists_subterm (fn Free _ => true | _ => false) goal
    then all_tac
    else let val thy = Proof_Context.theory_of ctxt
(*             val _ = tracing ("Storing: " ^ Syntax.string_of_term ctxt goal)*)
             val _ = sts := Net.insert_term_safe (Pattern.equiv thy) (goal,goal) (!sts)
         in all_tac end

(* Choose induction on a goal. Prefers computation over structural induction. *)
fun induction_tac ctxt =
  (SUBGOAL (computation_induction_tac ctxt (Proof_Context.theory_of ctxt))) APPEND'
  (SUBGOAL (structural_induction_tac ctxt))

(* induction \<rightarrow> auto *)
fun atomic_tac ctxt i =
(*          (IF_UNSOLVED (print_tac ctxt "BEFORE atomic_tac")) THEN*)
          (IF_UNSOLVED (TRY (induction_tac ctxt i))) THEN
          (IF_UNSOLVED (TRY (auto_tac ctxt))) (*THEN
          (IF_UNSOLVED (print_tac ctxt "AFTER atomic_tac"))*)

(* Our heuristic is simply the number of premises (in our interpretation... the pending goals)
   plus the depth in search (shorter proofs are preferred). *)
fun theorem_heuristic i thm =
  Thm.nprems_of thm + i

(* Recursive tactic that performs induction \<rightarrow> auto until no free datatype variables
   are present in goal. It stores any pending subgoal in sts when frees are exhausted. *)
fun ind_auto_failure sts _ ctxt =
(*  REPEAT (CHANGED (ALLGOALS (atomic_tac ctxt))) THEN*)
  ASTAR (Thm.no_prems, theorem_heuristic)
    (CHANGED ((ALLGOALS (atomic_tac ctxt)) THEN
             (IF_UNSOLVED (ALLGOALS (SUBGOAL (check_fail_proof_state sts ctxt))))))

fun SOLVE_TIMEOUT seconds tac t =
  let val res = Utils.apply_timeout2 (Time.fromSeconds seconds)
                  (fn () => SINGLE tac t
                              handle  Utils.TIMEOUT1 _ => NONE
                                    | Utils.TIMEOUT2 _ => NONE
                                    | Timeout.TIMEOUT _ => NONE) ()
                handle Utils.TIMEOUT2 _ => ((*tracing "TIMEOUT2";*) NONE)
                     | ERROR message => (warning ("Error: " ^ message ^ "\n"); NONE)
  in
    case res of
      NONE => Seq.empty
    | SOME t' => Seq.single t'
  end

fun sledgehammer_tac ctxt =
  fn (goal, i) =>
    if Term.exists_subterm (fn Free _ => true | _ => false) goal
    then all_tac
    else ((*tracing ("sledgehammer_tac: " ^ Syntax.string_of_term ctxt goal);*)
          SOLVE_TIMEOUT (Options.default_int @{system_option sledgehammer_timeout})
                        (Sledgehammer_Tactics.sledgehammer_with_metis_tac
                          ctxt [] Sledgehammer_Fact.no_fact_override [] i))

fun final_sledgehammer_tac ctxt simps i =
  let val (_, ctxt) = Proof_Context.note_thmss "" [((Binding.empty,[]), [(simps,[])])] ctxt
  in SOLVE_TIMEOUT (Options.default_int @{system_option sledgehammer_timeout})
                   (Sledgehammer_Tactics.sledgehammer_with_metis_tac
                    ctxt [] Sledgehammer_Fact.no_fact_override [] i)
  end

(* Recursive tactic that performs induction \<rightarrow> auto until no free datatype variables
   are present in goal. Calls sledgehammer and then stores any pending subgoal in sts
   when frees are exhausted. *)
fun ind_auto_sledgehammer_failure sts ctxt =
(*   DEPTH_FIRST Thm.no_prems*)
  ASTAR (Thm.no_prems, theorem_heuristic)
    (CHANGED (ALLGOALS (atomic_tac ctxt)) THEN
     TRY (CHANGED (ALLGOALS (SUBGOAL (sledgehammer_tac ctxt)))) THEN
     (IF_UNSOLVED (ALLGOALS (SUBGOAL (check_fail_proof_state sts ctxt)))))

fun induct_auto_failure_tac safe_rules sts (simps : thm list) ctxt =
  let val safes = safe_rules simps
      val ctxt = ctxt addsimps safes
  in (*IF_UNSOLVED (TRY (auto_tac ctxt)) THEN*)
     (ind_auto_failure sts simps ctxt)
  end

fun induct_auto_sledgehammer_failure_tac sts simps ctxt =
  let val (_, ctxt) = Proof_Context.note_thmss "" [((Binding.empty,[]), [(simps,[])])] ctxt
  in (*(IF_UNSOLVED (TRY (auto_tac ctxt))) THEN*)
     (ind_auto_sledgehammer_failure sts ctxt) end

fun induct_failure_provers_tac safe_rules sts simps ctxt =
  Par_Tactical.PARALLEL_CHOICE
        [induct_auto_failure_tac safe_rules sts simps ctxt,
         induct_auto_sledgehammer_failure_tac sts simps ctxt]

(*val method_setup_inductive_prover =
  Method.setup (Binding.name "induct_auto_failure_tac")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (induct_auto_failure_tac
                      (Unsynchronized.ref Net.empty)
                      [] ctxt)))
    "Atomic tactic with failure analysis. Interleaves induction and auto and check failures."*)

val method_setup_inductive_sledgehammer_prover =
  Method.setup (Binding.name "induct_auto_sledgehammer_failure_tac")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (induct_auto_sledgehammer_failure_tac
                      (Unsynchronized.ref Net.empty)
                      [] ctxt)))
    "Atomic tactic with failure analysis. Interleaves induction, auto, sledgehammer and check failures."

(*val _ = Context.>> (Context.map_theory method_setup_inductive_prover)*)
val _ = Context.>> (Context.map_theory method_setup_inductive_sledgehammer_prover)


(*fun metis_tac ctxt facts = 
  ALLGOALS (fn i =>
    TRY (Metis_Tactic.metis_tac [ATP_Proof_Reconstruct.full_type_enc]
  ATP_Proof_Reconstruct.default_metis_lam_trans ctxt facts i))*)

end

structure Inductive_Tacs : INDUCTIVE_TACS = DB_Inductive_Tacs
