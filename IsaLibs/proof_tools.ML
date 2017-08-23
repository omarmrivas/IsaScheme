(*  Title:      proof_tools.ML
    ID:         $Id: proof_tools.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Important proof methods.
*)

signature PROOF_TOOLS =
sig

end

structure DB_Proof_Tools
(* : PROOF_TOOLS *)
= struct

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
  mk_conjecture_store (Seq.interleave (sequence, seq))

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
         in case try (Pattern.match thy (pattern, eq)) (Vartab.empty, Vartab.empty) of
              SOME (tyenv, tenv) => let val env = Envir.Envir {maxidx = 1, tenv = tenv, tyenv = tyenv}
                                        val lhs = Envir.norm_term env x
                                        val rhs = Envir.norm_term env y
                                    in SOME (HOLogic.mk_eq (lhs, rhs)) end
            | NONE => NONE
             end
    else NONE

fun arg_cong_equation' thy prop =
  let val concl = (HOLogic.dest_Trueprop o Logic.strip_imp_concl) prop
      val prems = Logic.strip_imp_prems prop
  in case arg_cong_equation thy concl of
      SOME eq => (Logic.list_implies o pair prems) eq
    | NONE => prop
  end

fun generalize_cond_eq ctxt conj =
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
  end

fun generalize_assumptions ctxt conj =
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

fun generalize timeOut ctxt thy order simps subsumed (meth,conj) =
  let val conj = conj |> Utils.normalise_term ctxt simps
                      |> arg_cong_equation' thy o Utils.rulify ctxt
                      |> orient_prop thy order
      val (lhs,rhs) = Utils.dest_eq conj
  in if lhs = rhs orelse
        subsumed conj orelse
        subsumed (Utils.commute_eq conj)
     then NONE
     else let val g = generalize_cond_eq ctxt conj
          in if not (Counter_Example.memoized_counter_example ctxt timeOut g)
             then SOME (meth, the (generalize_assumptions ctxt g))
             else if not (Counter_Example.memoized_counter_example ctxt timeOut conj)
                  then SOME (meth, the (generalize_assumptions ctxt conj))
                  else NONE
          end
  end

fun inductive_prover ctxt tactic timeOut prop =
  let val start = Timing.start ()
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
      val lambda_size = Config.get ctxt Random_Terms.max_lambda_size
      val n = Config.get ctxt EQ_Terms.max_random_terms
      val _ = tracing "Preprocessing conjecture..."
      val (table, typsub) = EQ_Terms.preprocess_conjecture ctxt lambda_size n prop
      val _ = tracing "Done"
      fun try_prove simps conj =
        let val failures = Unsynchronized.ref (Net.empty : term Net.net)
            val _ = tracing ("Proving: " ^ Utils.string_of_term' ctxt conj)
        in case Prover.prove_from_tactic ctxt_nodefs (SOME simps) (tactic failures) conj timeOut of
          SOME thm => (tracing ("Proved!: " ^ Utils.str_of_terms ctxt [conj]);Theorem thm)
        | NONE => (!failures) |> Net.content
                              |> Failure
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
      fun next_subgoal simps subsumed subgoals =
        let val subgoals' = 
          subgoals |> map (Utils.normalise_term ctxt_nodefs simps)
                   |> map (arg_cong_equation' thy o Utils.rulify ctxt)
                   |> map (orient_prop thy LESS)
                   |> filter (fn prop => let val (lhs,rhs) = Utils.dest_eq prop
                                         in lhs <> rhs andalso
                                            not (subsumed prop) andalso
                                            not (subsumed (Utils.commute_eq prop)) end)
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
        end
      fun next_conjecture thy simps net store =
        case pull_conjecture store of
            SOME ((meth, conjecture), store) =>
              let val _ = tracing ("Normalising (" ^ meth ^ "): " ^ Utils.string_of_term' ctxt conjecture)
                  val conjecture = conjecture |> Utils.normalise_term lthy_nodefs simps
                                              |> (arg_cong_equation' thy o Utils.rulify ctxt)
                                              |> (orient_prop thy LESS)
                  val (lhs,rhs) = Utils.dest_eq conjecture
              in if lhs = rhs orelse
                    subsumed_in_net net conjecture
                 then (tracing "subsumed"; next_conjecture thy simps net store)
                 else let val conjecture' = Utils.commute_eq conjecture
                      in if subsumed_in_net net conjecture'
                         then (tracing "subsumed"; next_conjecture thy simps net store)
                         else SOME (orient_prop thy LESS conjecture, store)
                      end
              end
          | NONE => NONE
      val terminates = Aprove.memoized_terminates ctxt_nodefs
      fun build_trs lemmas rule =
          let val TRS = map Utils.obj_to_meta lemmas
              val e = Utils.obj_to_meta rule
          in e |> Conditional_Completion.run_completion [] ctxt_nodefs terminates TRS
               |> map Utils.meta_to_obj end
      val _ = tracing "Calculating equational theory exploration sequence..."
      val eq_tx = DB_EQ_Terms.equational_theory_exploration ctxt_nodefs (table, typsub) lambda_size n lambda_size lemmas_ref prop
                  |> Seq.map (pair "EQ_TX")
      val _ = tracing "Done"
      val _ = tracing "Calculating known equational laws sequence..."
      val known_laws = DB_EQ_Terms.known_eq_laws ctxt_nodefs (table, typsub) lambda_size n lemmas_ref prop
                  |> Seq.map (pair "EQ_KNOWN")
      val _ = tracing "Done"
      val conj_store = eq_tx |> mk_conjecture_store
                             |> add_sequence known_laws
      fun recursive_prover foo store net subgoals lemmas conj =
        case try_prove lemmas conj of
          Theorem thm =>(let val lemmas = build_trs lemmas thm
                             val _ = lemmas_ref := lemmas
                             val net = add_thms_to_net net lemmas
                         in case (tracing "next_subgoal"; next_subgoal lemmas (subsumed_in_net net) subgoals) of
                          SOME (goal, subgoals) => recursive_prover (not foo) store net subgoals lemmas goal
                        | NONE => SOME (build_trs lemmas thm) end)
        | Failure trms =>
            let val net = add_term_to_net net conj
                val lemmas' = lemmas |> map Thm.full_prop_of
                                     |> map Logic.unvarify_global
                val failures = trms |> map (fst o Utils.binder_elimination Const_Names.meta_forall [])
                                    |> Seq.of_list
                                    |> Seq.map (pair "EQ_FROM_FAILURE")
                val walsh =
                       (subgoals@lemmas')
                          |> Seq.of_list
                          |> Seq.maps (fn subgoal =>
                                    Divergence.conditional_walsh_critic ctxt_nodefs lemmas [subgoal, conj])
                          |> Seq.map (pair "WALSH")
                val transverse =
                      (subgoals@lemmas')
                          |> Seq.of_list
                          |> Seq.maps (fn subgoal =>
                                    [subgoal, conj] |> Divergence.conditional_transverse_critic lthy_nodefs lemmas
                                                    |> Seq.map_filter (Prover.prove_schematic_from_method
                                                                      lthy_nodefs (SOME lemmas)
                                                                      (Method.Basic (fn ctxt =>
                                                                        Method.SIMPLE_METHOD
                                                                          (tactic (Unsynchronized.ref Net.empty) ctxt)),
                                                                        (Position.none, Position.none))))
                          |> Seq.map (pair "TRANSVERSE")
                val new_sequence =
                      (Seq.interleave (failures, walsh), transverse)
                        |> Seq.interleave
                        |> Utils.map_filter_seq (Thread.numProcessors () * 2) 
                                  (generalize timeOut ctxt_nodefs thy LESS lemmas (subsumed_in_net net))
                val new_store = add_sequence new_sequence conj_store
            in case (tracing "next_conjecture"; next_conjecture thy lemmas net new_store) of
                SOME (conjecture, store) => recursive_prover (not foo) store (add_term_to_net net conj) (conj :: subgoals) lemmas conjecture
              | NONE => NONE
            end
      val result = case recursive_prover true conj_store Net.empty [] def_lemmas prop of
                      SOME thms => (tracing "Latex Simpset: ";
                                    tracing (Utils.latex_str_of_thms thms);
                                    tracing "Simpset: ";
                                    tracing (Utils.str_of_thms thms);
                                    SOME thms)
                    | NONE => (tracing "No simpset!"; NONE)
      val elapsed = start |> Timing.result
                          |> #elapsed
                          |> Time.toReal
      val _ = tracing ("Elapsed time: " ^ string_of_real elapsed)
  in (lthy_nodefs, result) end

(* Failure analysis *)
fun inductive_prover_tactic' ctxt =
  fn (goal, i) =>
    case inductive_prover ctxt InductiveTacs.ind_auto_failure (Config.get ctxt Prover.max_time_in_proof) goal of
      (ctxt,SOME simps) => (tracing "Proved original goal!"; simp_tac (ctxt addsimps simps) i)
    | (_,NONE) => (tracing "Not proved!"; no_tac)

fun inductive_prover_tactic ctxt =
  SUBGOAL (inductive_prover_tactic' ctxt)

val method_setup_inductive_prover =
  Method.setup (Binding.name "inductive_prover")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (inductive_prover_tactic ctxt 1)))
    "Recursive prover with failure analysis. Interleaves induction and auto and check failures."

val _ = Context.>> (Context.map_theory method_setup_inductive_prover)

end

structure Proof_Tools : PROOF_TOOLS = DB_Proof_Tools

