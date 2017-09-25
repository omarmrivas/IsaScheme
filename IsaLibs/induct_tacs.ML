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
  val induct_auto_failure_tac : term Net.net Unsynchronized.ref -> thm list Unsynchronized.ref
                                -> Proof.context -> tactic
  val induct_auto_sledgehammer_failure_tac : term Net.net Unsynchronized.ref -> thm list Unsynchronized.ref
                                -> Proof.context -> tactic
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
              |> (fn (args, name, rule) => if exists (exists_subterm is_Bound) args
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

(* Applies computation induction rules *)
fun computation_induction_tac ctxt thy (goal, i) =
    case inductive_applications thy goal of
          (args, (name, induction)) :: _ => 
            ((*tracing ("computational induction on: " ^ Syntax.string_of_term ctxt goal);
             tracing ("params: (" ^ name ^") " ^ Utils.str_of_terms ctxt (map (fst o snd o the) args));*)
             DETERM (Induction.induction_tac ctxt true [args] [] [] (SOME [induction]) [] i))
         | [] => no_tac

(* Applies structural induction to free datatype variables *)
(* It chooses any free datatype variable available. Probably it would be better
  to perform induction on arguments where the recursive function is  *)
fun structural_induction_tac ctxt (goal, i) =
  let val frees = Term.add_frees goal []
                    |> map_filter (fn (s, T) =>
                              let val ind_rules = Induct.find_inductT ctxt T
                              in if null ind_rules
                                 then NONE
                                 else SOME ((s, T), ind_rules) end)
  in case frees of
      ((s,T), induction) :: _ =>
          ((*tracing ("structural induction on: " ^ Syntax.string_of_term ctxt goal);
           tracing ("params: " ^ Syntax.string_of_term ctxt (Free (s,T)));*)
          DETERM (Induction.induction_tac ctxt true [[SOME (NONE, (Free (s,T), false))]] [] [] NONE [] i))
(*          DETERM (Induction.induction_tac ctxt true [[SOME (NONE, (Free (s,T), false))]] [] [] (SOME induction) [] i))*)
       | [] => no_tac
  end

(* Failure analysis
  Any pending goal is recorded in sts for further analysis. *)
fun check_fail_proof_state sts ctxt =
  fn (goal, _) =>
    let val thy = Proof_Context.theory_of ctxt
        val _ = sts := Net.insert_term_safe (Pattern.equiv thy) (goal,goal) (!sts)
    in all_tac end

(* Choose induction on a goal. Prefers computation over structural induction. *)
fun induction_tac ctxt =
  (SUBGOAL (computation_induction_tac ctxt (Proof_Context.theory_of ctxt))) ORELSE'
  (SUBGOAL (structural_induction_tac ctxt))

(* induction \<rightarrow> auto *)
fun atomic_tac ctxt i =
          (IF_UNSOLVED (TRY (induction_tac ctxt i))) THEN
          (IF_UNSOLVED (TRY (auto_tac ctxt)))

(* Recursive tactic that performs induction \<rightarrow> auto until no free datatype variables
   are present in goal. It stores any pending subgoal in sts when frees are exhausted. *)
fun ind_auto_failure sts _ ctxt =
  REPEAT (CHANGED (ALLGOALS (atomic_tac ctxt))) THEN
  (IF_UNSOLVED (ALLGOALS (SUBGOAL (check_fail_proof_state sts ctxt))))

fun sledgehammer_tac ctxt simps i =
  Sledgehammer_Tactics.sledgehammer_with_metis_tac
            ctxt [] Sledgehammer_Fact.no_fact_override [] i

fun SOLVE_TIMEOUT seconds tac t = 
  let val res = Timeout.apply (Time.fromSeconds seconds)
                  (fn () => SINGLE tac t) ()
                handle Timeout.TIMEOUT _ => NONE
                     | ERROR message => (warning ("Error: " ^ message ^ "\n"); NONE)
  in
    case res of
      NONE => Seq.empty
    | SOME t' => Seq.single t'
  end

(* Recursive tactic that performs induction \<rightarrow> auto until no free datatype variables
   are present in goal. Calls sledgehammer and then stores any pending subgoal in sts
   when frees are exhausted. *)
fun ind_auto_sledgehammer_failure sts simps ctxt =
  REPEAT (CHANGED (ALLGOALS (atomic_tac ctxt))) THEN
  (TRY (REPEAT (CHANGED (ALLGOALS (fn i => SOLVE_TIMEOUT (Config.get ctxt Prover.max_time_in_proof)
                      (sledgehammer_tac ctxt simps i))))) THEN
  (IF_UNSOLVED (ALLGOALS (SUBGOAL (check_fail_proof_state sts ctxt)))))

fun induct_auto_failure_tac sts simps ctxt =
        IF_UNSOLVED (TRY (auto_tac ctxt)) THEN
        (ind_auto_failure sts simps ctxt)

fun induct_auto_sledgehammer_failure_tac sts simps ctxt =
  (IF_UNSOLVED (TRY (auto_tac ctxt))) THEN
  (ind_auto_sledgehammer_failure sts simps ctxt)

(*fun metis_tac ctxt facts = 
  ALLGOALS (fn i =>
    TRY (Metis_Tactic.metis_tac [ATP_Proof_Reconstruct.full_type_enc]
  ATP_Proof_Reconstruct.default_metis_lam_trans ctxt facts i))*)

end

structure Inductive_Tacs : INDUCTIVE_TACS = DB_Inductive_Tacs
