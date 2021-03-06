(*  Title:      src/aprove.ML
    ID:         $Id: aprove.ML,v 1.010 2010/13/03 20:15:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   University of Edinburgh 2010

An interface to the termination prover APROVE.
*)

signature APROVE =
sig
  val thm_to_wst             : term * term -> string
  val trs_to_wst             : thm list -> string
  val terminates             : Proof.context -> thm list -> bool
  val memoized_terminates    : Proof.context -> thm list -> bool
  val aprove_path_ok         : Proof.context -> bool
  val aprove_server_ok       : Proof.context -> bool

  val use_aprove             : bool Config.T
end

structure DB_Aprove
(* : APROVE *)
= struct

val (use_aprove, setup_use_aprove) = Attrib.config_bool @{binding "use_aprove"} (K true)
val (use_aprove_srv, setup_use_aprove_srv) = Attrib.config_bool @{binding "use_aprove_srv"} (K false)

val rule_false = @{lemma "\<not>P \<equiv> (P = False)" by simp}
val rule_true = @{lemma "P \<equiv> (P = True)" by simp}
fun modify th =
      fold (fn i => fn th => 
                  let val prem = Thm.term_of (Thm.cprem_of th i)
                  in case prem of
                       Const (_, _) $ ((Const (top, _) $ _) $ _) => 
                                             if Const_Names.hol_eq = top
                                             then th
                                             else Conv.gconv_rule (Conv.arg_conv (Conv.rewr_conv rule_true)) i th
                     | Const (_, _) $ (Const (top, _) $ _) =>
                                             if Const_Names.hol_not = top
                                             then Conv.gconv_rule (Conv.arg_conv (Conv.rewr_conv rule_false)) i th
                                             else Conv.gconv_rule (Conv.arg_conv (Conv.rewr_conv rule_true)) i th
                     | _ => Conv.gconv_rule (Conv.arg_conv (Conv.rewr_conv rule_true)) i th end) (1 upto Thm.nprems_of th) th


fun thm_to_wst (s,t) =
    let
      (*val (s,t) = dest_meta_equation thm*)
      fun to_wst (t $ u) = 
          (*"app(" ^ (to_wst t) ^ "," ^ (to_wst u) ^ ")"*)
          let val (head, args) = strip_comb (t $ u)
          in args |> map to_wst
                  |> space_implode ","
                  |> enclose "(" ")"
                  |> (fn str => (to_wst head) ^ str) end
        | to_wst (Const (n,ty)) =
          if n = Const_Names.hol_eq then (if ty = @{typ "bool => bool => bool"} then "iff" else "equals")
          else if n = Const_Names.hol_conj then "and"
          else if n = Const_Names.hol_disj then "or"
          else if n = Const_Names.hol_implies then "implies"
          else if n = Const_Names.hol_not then "not"
          else if n = Const_Names.hol_forall orelse 
                  n = Const_Names.hol_exists orelse 
                  n = Const_Names.meta_forall then raise ERROR "Quantified formulae not permitted"
          else Long_Name.base_name n
        | to_wst (Free (n,_)) = n
        | to_wst (Abs (_, _, _)) = raise ERROR "Formulae with lambda-terms not permitted"
        | to_wst (Bound _) = raise ERROR "Formulae with lambda-terms not permitted"
        | to_wst (Var ((n, i), _)) = n ^ string_of_int i
    in (to_wst s) ^ " -> " ^ (to_wst t) end

fun strip_abs frees (Abs (a, T, t)) =
    let val a = singleton (Name.variant_list frees) a
        val (a',t') = Term.dest_abs (a, T, t)
        val (a'', t'') = strip_abs (a' :: frees) t'
    in ((a', T) :: a'', t'') end
  | strip_abs _ t = ([], t)

fun eliminate_lambdas frees_ref eqs_ref consts_ref (Abs (a, T, t)) =
    let val frees = [] |> Term.add_vars (Abs (a, T, t))
                       |> map (fn ((n, i), ty) => (n ^ string_of_int i, ty))
        val (lambda_frees, t') = strip_abs (!frees_ref) (Abs (a, T, t))
(*        val _ = tracing "===== Abs ======"
        val _ = (tracing o Syntax.string_of_term @{context}) (Abs (a, T, t))
        val _ = tracing "===== frees ======"
        val _ = map (tracing o Syntax.string_of_term @{context}) (map Free frees)
        val _ = tracing "===== lambda frees ======"
        val _ = map (tracing o Syntax.string_of_term @{context}) (map Free lambda_frees)*)
        val _ = frees_ref := (map fst lambda_frees) @ !frees_ref
        val consts = !consts_ref
        val const = singleton (Name.variant_list consts) "f"
        val _ = consts_ref := (const :: consts)
        val t'' = eliminate_lambdas frees_ref eqs_ref consts_ref t'
        val typ_const = (map snd (frees @ lambda_frees))
                          ---> (type_of t'')
        val eq = (Term.list_comb (Const (const, typ_const), map Free (frees @ lambda_frees)), t'')
        val _ = eqs_ref := eq :: (!eqs_ref)
    in Term.list_comb (Const (const, typ_const), map Free frees) end
  | eliminate_lambdas frees_ref eqs_ref consts_ref (t $ u) = (eliminate_lambdas frees_ref eqs_ref consts_ref t) $ (eliminate_lambdas frees_ref eqs_ref consts_ref u)
  | eliminate_lambdas _ _ _ t = t

fun trs_to_wst TRS = 
    let
      val trs = TRS |> map_index (fn (i, th) => ((Thm.incr_indexes i) o Drule.zero_var_indexes) th)
      val var_names = trs |> map Thm.full_prop_of
                          |> maps (fn t => Term.add_vars t [])
                          |> map (fn ((n, i), _) => n ^ string_of_int i)
      val eqs_ref = Unsynchronized.ref []
      val consts_ref = Unsynchronized.ref []
      val frees_ref = Unsynchronized.ref var_names
      val conditions = trs |> map (map (HOLogic.dest_eq o HOLogic.dest_Trueprop) o Thm.prems_of o modify)
                           |> map (map (thm_to_wst o (apply2 (eliminate_lambdas frees_ref eqs_ref consts_ref))))
                           |> map commas
      val rules = trs |> map (thm_to_wst o (apply2 (eliminate_lambdas frees_ref eqs_ref consts_ref)) o Utils.dest_meta_equation)
                      |> (fn eqs => eqs ~~ conditions
                                      |> map (fn (eq, cond) => if cond = ""
                                                               then eq
                                                               else eq ^ " | " ^ cond))
                      |> (fn eqs => map thm_to_wst (!eqs_ref) @ eqs)
                      |> space_implode " "
                      |> (fn rs => "(RULES " ^ rs ^ ")")
(*      fun print (p, q) = Syntax.string_of_term @{context} p ^ " \<longrightarrow> " ^ Syntax.string_of_term @{context} q
      val _ = map (tracing o print) (!eqs_ref)*)
      val vars = !frees_ref
                     |> space_implode " "
                     |> (fn vs => "(VAR " ^ vs ^ ")")
    in vars ^ " " ^ rules end

fun non_terminating_subterm th =
    let val (lhs, rhs) = Utils.dest_meta_equation th
    in Term.exists_subterm (fn t => (is_equal o Term_Ord.term_ord) (t, lhs)) rhs end

fun terminates ctxt TRS =
    (if Config.get ctxt use_aprove
    then
      if exists non_terminating_subterm TRS then false
      else
        let
          val timeOut =  Config.get ctxt DPair.max_time_in_termination
          val wst = trs_to_wst TRS
          val timeOut_threads = "-t " ^ (string_of_int timeOut) ^ " -w " ^ (string_of_int (Thread.numProcessors ()))
          val (out, _) = if getenv "ISABELLE_PLATFORM_FAMILY" = "windows"
                         then
                         Isabelle_System.with_tmp_file
                           "aprove" "trs"
                           (fn path => let val path = Path.base path
                                           val _ = File.write path wst
                                           val result = Isabelle_System.bash_output ("$TIMEAOUT_PATH/timeout -t " ^ (string_of_int (timeOut+5)) ^ " java -Xmx512m -jar $APROVE_PATH/aprove.jar " ^ timeOut_threads ^ " -m wst " ^ (Path.implode path) ^ " 2> /dev/null")
(*                                           val result = Isabelle_System.bash_output ("$TIMEAOUT_PATH/timeout -t " ^ (string_of_int (timeOut+5)) ^ " java -Xmx512m -jar $APROVE_PATH/aprove.jar -t " ^ (string_of_int timeOut) ^ " -m wst " ^ (Path.implode path))*)
                                           val _ = File.rm path
                                       in result end)
                         else
                         Isabelle_System.with_tmp_file
                           "aprove" "trs"
                           (fn path => (File.write path wst;
                                        if Config.get ctxt use_aprove_srv
                                        then Isabelle_System.bash_output ("printf \"2\\n" ^
                                                      Path.implode path ^
                                                      "\\n" ^ string_of_int timeOut ^
                                                      "\" | nc $APROVE_SERVER $APROVE_SERVER_PORT 2> /dev/null")
                                        else Isabelle_System.bash_output ("$TIMEAOUT_PATH/timeout -t " ^ (string_of_int (timeOut+5)) ^ " java -Xmx512m -jar $APROVE_PATH/aprove.jar " ^ timeOut_threads ^ " -m wst " ^ (Path.implode path) ^ " 2> /dev/null")))
          val foo = String.isSubstring "YES" out
        in if foo
           then true
           else false
        (*then (tracing "aprove true!"; true)
    else (tracing "aprove false!"; false)*)
        end
    else false) handle CTERM err => (tracing "aprove"; raise CTERM err)

val memoized_terminates_var = Synchronized.var "memoized_terminates"
                      (Term_List_Tab.empty : bool Term_List_Tab.table)


(* getenv "ISABELLE_PLATFORM_FAMILY" *)

fun all_terminates ctxt TRS =
  if DPair.terminates ctxt TRS
  then true
  else terminates ctxt TRS
(*  Par_List.exists (fn f => f TRS) [DPair.terminates ctxt, terminates ctxt]*)

fun aprove_path_ok ctxt =
  let val timeOut =  Config.get ctxt DPair.max_time_in_termination
      val timeOut_threads = "-t " ^ (string_of_int timeOut) ^ " -w " ^ (string_of_int (Thread.numProcessors ()))
      val (out, _) = 
        Isabelle_System.with_tmp_file
              "aprove" "trs"
              (fn path => 
                (File.write path "(VAR y0 y1 x1) (RULES f(c,y0) -> y0 f(z(x1),y1) -> z(f(x1,y1)))";
                 Isabelle_System.bash_output 
                        ("$TIMEAOUT_PATH/timeout -t " ^ 
                         (string_of_int (timeOut+5)) ^ 
                         " java -Xmx512m -jar $APROVE_PATH/aprove.jar " ^ 
                         timeOut_threads ^ 
                         " -m wst " ^ 
                         (Path.implode path) ^ " 2> /dev/null")))
      val foo = String.isSubstring "YES" out
    in if foo
       then true
       else false
    end

fun aprove_server_ok ctxt =
  let val timeOut =  Config.get ctxt DPair.max_time_in_termination
      val (out, _) = 
        Isabelle_System.with_tmp_file
              "aprove" "trs"
              (fn path =>
                (File.write path "(VAR y0 y1 x1) (RULES f(c,y0) -> y0 f(z(x1),y1) -> z(f(x1,y1)))";
                 Isabelle_System.bash_output
                        ("printf \"2\\n" ^
                         Path.implode path ^
                         "\\n" ^ string_of_int timeOut ^
                         "\" | nc $APROVE_SERVER $APROVE_SERVER_PORT 2> /dev/null")))
      val foo = String.isSubstring "YES" out
    in if foo
       then true
       else false
    end

fun memoized_terminates ctxt TRS =
  let val transform = sort Term_Ord.term_ord o map Thm.full_prop_of
  in Utils.memoize_function Term_List_Tab.lookup Term_List_Tab.update transform memoized_terminates_var
                            (terminates ctxt) TRS end


end

structure Aprove : APROVE = DB_Aprove
