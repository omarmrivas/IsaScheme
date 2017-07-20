(*  Title:      util/induct_tacs4.ML
    ID:         $Id: induct_tacs4.ML,v 1.010 2010/10/01 13:22:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   University of Edinburgh 2010

An inductive decision procedure using Isabelle's tactics.
This tactic behaves more nicely w.r.t. equivalent proofs.
e.g. F x1 ... xn = G x1 ... xn. It also considers variables
quantified at the meta level ("!!") and searches for a proof
using A* where the heuristic is: pending goals + depth of search.
*)

signature INDUCTIVE_TACS4 =
sig
  val induct_auto_tac             : term Net.net Unsynchronized.ref -> Proof.context -> int -> tactic
  val induct_auto_tac'            : term Net.net Unsynchronized.ref -> term Net.net Unsynchronized.ref 
                                    -> Proof.context -> tactic
  val bef_induct_auto_tac         : term Net.net Unsynchronized.ref -> Proof.context -> tactic
end

structure DB_InductiveTacs4
(* : INDUCTIVE_TACS4 *)
= struct

local
  (* Finds all applications of consts in prop *)
  (* useful when we have induction schemes over these consts *)
  fun applications2 thy ok_vars prop =
      let
        val (c,args) = Term.strip_comb prop
        val (frees, ts) = List.partition (fn t => is_Free t andalso exists (fn t' => is_equal (Term_Ord.fast_term_ord (t,Free t'))) ok_vars) args
        val srule = if length frees = length args then 
                      SOME (Global_Theory.get_thm thy (((fst o Term.dest_Const) c) ^ ".induct")) handle ERROR _ => NONE
                                                                                                | TERM _ => NONE
                    else NONE
      in
        case srule of
          SOME rule => frees |> map Term.dest_Free 
                             |> rpair rule
                             |> (fn r => r :: maps (applications2 thy ok_vars) ts)
        | NONE => maps (applications2 thy ok_vars) ts
      end
in
fun choose_induct_tac set ctxt (goal,i) = 
    let
(*      val _ = tracing "START"
      val _ = tracing ("Goal: " ^ Syntax.string_of_term ctxt goal)*)
      val (nt,_) = Utils.binder_elimination "all" [] goal
      val goal' = Term.strip_all_body goal
      val vars = [] |> Term.add_frees ((snd o Logic.strip_horn) nt)
      val all_vars = goal |> Term.strip_all_vars |> filter (fn (s,_) => exists (fn (s',_) => s = s') vars)
      val (_, concl) = Logic.strip_horn (Term.strip_all_body goal)
      val free_vars = [] |> Term.add_frees concl
      val (_,all_rec_vs) = all_vars |> List.partition (fn v => null (Induct.get_inductT ctxt [[SOME (Free v)]]))
      val (fix_vs,rec_vs) = free_vars |> List.partition (fn v => null (Induct.get_inductT ctxt [[SOME (Free v)]]))
      val induct_and_vs = rec_vs |> map (fn v => (v,(hd o hd) (Induct.get_inductT ctxt [[SOME (Free v)]])))
      val all_vs_and_induct = all_rec_vs |> map (fn v => (v,(hd o hd) (Induct.get_inductT ctxt [[SOME (Free v)]])))
      (* Strategy 1:                                                 *)
      (* Induction rule: Any induction rule                          *)
      (* Set of induction vars: subsets of inductive vars (per rule) *)
      (* Set of fixed vars: empty                                    *)
      (* tactic: "induct_tac"                                        *)
      fun meta_induct_tac_strategy vars_induction =
          (no_tac,vars_induction)
            |> Library.foldl (fn (thms,(vs,th)) => (Induct_Tacs.induct_tac ctxt [map (fn v => SOME (fst v)) vs] (SOME [th]) i)
(*            |> Library.foldl (fn (thms,(vs,th)) => (Induct_Tacs.induct_rules_tac ctxt [map (fn v => SOME (fst v)) vs] [th] i)*)
                                                     APPEND
                                                     thms)
      (* Strategy 2:                                                 *)
      (* Induction rule: Any induction rule                          *)
      (* Set of induction vars: subsets of inductive vars            *)
      (* Set of fixed vars: empty                                    *)
      (* tactic: "induct"                                            *)
      fun meta_induct_strategy vars_induction = 
          (no_tac,vars_induction)
            |> Library.foldl (fn (thms,(vs,th)) => (Induct.induct_tac ctxt true 
                                                                                    [map (fn v => SOME (NONE,(Free v,true))) vs] 
                                                                                    [] [] (SOME [th]) [] i)
                                                     APPEND
                                                     thms)
      (* Strategy 3:                                                 *)
      (* Induction rule: not specified                               *)
      (* Set of induction vars: singleton inductive vars             *)
      (* Set of fixed vars: subsets of fixed vars                    *)
      (* tactic: "induct"                                            *)
      fun induct_strategy2 rec_vs fix_vs = 
           rec_vs
             |> map Free
             |> map_index (fn (i,x) => (x,fix_vs @ List.take (rec_vs,i) @ List.drop (rec_vs,i+1)))
             |> maps (fn (v,fixes) => Utils.subsets fixes |> map (fn s => (v,s)))
             |> (fn args => Library.foldl (fn (thms,(v,fixes)) => 
                                              ((Induct.induct_tac ctxt false [[SOME (NONE,(v,false))]] [fixes] [] NONE [] i)
                                                 APPEND
                                                 thms)) (no_tac,args))
      val thy = Proof_Context.theory_of ctxt
      val processed = goal |> Net.unify_term (!set)
                           |> exists (fn x => Utils.safe_eval "term_filter.ML 55" false (Pattern.matches thy) (goal,x))
    in
      if processed then no_tac
      else
          (set := Net.insert_term_safe (Pattern.equiv thy) (goal,goal) (!set);
           (meta_induct_tac_strategy (map (fn (a,b) => ([a],b)) (induct_and_vs @ all_vs_and_induct)))
             APPEND 
             (meta_induct_strategy (applications2 thy rec_vs (*concl*)goal'))
             APPEND
             (if null fix_vs then no_tac else induct_strategy2 rec_vs fix_vs))
    end
end

(* Failure analysis *)
fun check_fail_proof_state sts ctxt =
  SUBGOAL (fn (goal, _) =>
  let val thy = Proof_Context.theory_of ctxt
      val _ = sts := Net.insert_term_safe (Pattern.equiv thy) (goal,goal) (!sts)
  in no_tac end)

(* simple auto tac *)
fun auto_clasimpset_tac ctxt (_:int) = auto_tac ctxt

(* induct and auto tac *)
fun induct_auto_tac set ctxt = 
    CHANGED o ((EVERY' [SUBGOAL (choose_induct_tac set ctxt),
                        auto_clasimpset_tac ctxt]) APPEND' (auto_clasimpset_tac ctxt))

fun TRY' tac x = 
  TRY (tac x)

(* Performs induction and rewriting then stores remaining subgoals in fails *)
fun induct_auto_tac' set fails ctxt = 
        SOLVE ((CHANGED o ALLGOALS)
           (((EVERY' [SUBGOAL (choose_induct_tac set ctxt),
                        auto_clasimpset_tac ctxt]) APPEND' (auto_clasimpset_tac ctxt))
      THEN' (TRY' (check_fail_proof_state fails ctxt))))

(* Probably there is a better way to know if we have proved the theorem *)
(* this function won't work in goals with spurious premises *)
fun theorem_proved thm = (0 = Thm.nprems_of thm)

(* Our heuristic is simply the number of premises (in our interpretation... the pending goals) 
   plus the depth in search (short proofs are preferred). *)
fun theorem_heuristic i thm = Thm.nprems_of thm + i

(* A* search: similar to BEST_FIRST but current level of search is taken into account *)
fun bef_induct_auto_tac set ctxt =
    ASTAR (theorem_proved,theorem_heuristic) (induct_auto_tac set ctxt 1)

fun bef_induct_auto_tac' set ctxt =
  ALLGOALS (SUBGOAL (fn (goal, i) =>
    let val ctxt = goal |> global_simps ctxt
                        |> (fn thms => ctxt addsimps thms)
    in
    ASTAR (theorem_proved,theorem_heuristic) (induct_auto_tac set ctxt i) 
    end))

val method_setup =
  Method.setup (Binding.name "induct_auto")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (bef_induct_auto_tac' (Unsynchronized.ref Net.empty) ctxt)))
(*    (Scan.succeed (fn ctxt => SIMPLE_METHOD (bef_induct_auto_tac (Unsynchronized.ref TSet.empty) ctxt)))*)
    "interleave induction and auto"

val _ = Context.>> (Context.map_theory method_setup)

end

structure InductiveTacs4 : INDUCTIVE_TACS4 = DB_InductiveTacs4
