(*  Title:      src/completion.ML
    ID:         $Id: completion.ML,v 2.000 2012/04/20 12:42:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Politecnica de San Luis Potosi
    Copyright   Universidad Politecnica de San Luis Potosi 2011

An implementation of Unfailing Knuth Bendix (Baader and Nipkow's "Term Rewriting and All That" 
and Leo Bachmair, Nachum Dershowwitz and David A. Plaisted's "Completion without Failure")
Completion Algorithm for Isabelle.
*)

signature COMPLETION =
sig
  exception ORIENTATION of string * thm

  val max_time_in_completion        : int Config.T

  val generate_cps                  : bool Config.T
  val divergence_critic             : bool Config.T
  val schematic_instance            : Proof.context -> thm -> int -> thm

  val match_inst                    :  Proof.context -> Envir.env -> (ctyp * ctyp) list * (cterm * cterm) list
  val linear_if_possible            :  thm -> thm
  val varify_global                 :  Proof.context -> thm -> thm
  val my_abs_conv                   :  Proof.context -> conv -> conv
  val rewrite_rule_extra_vars       :  term list -> term -> term -> bool

  val discriminate_rules            : Proof.context -> (thm list -> bool) -> 
                                      thm list -> thm list * thm list
  val scpairs                       : theory -> (thm * thm) -> thm list
  val semi_critical_pairs           : theory -> order -> thm list -> thm list -> thm list
  val memoized_joinable'            : Proof.context -> (thm list -> bool) -> (term * int) list -> 
                                      thm list -> term -> bool
  val memoized_joinable             : Proof.context -> (thm list -> bool) -> (term * int) list -> 
                                      thm list -> thm -> bool

  val run_completion                : thm list -> Proof.context -> (thm list -> bool) ->
                                      thm list -> thm -> thm list
  val run_completion'               : thm list -> Proof.context -> (thm list -> bool) ->
                                      thm list -> thm -> thm list * thm list
  val ac_termination                : Proof.context -> thm list * thm list -> thm -> bool
  val ac_termination_obj            : Proof.context -> thm list -> thm -> bool
(*  val perform_unfailing_completion  : Attrib.binding -> Method.text -> thm list -> thm -> (thm list * thm list) option
  val get_any_ordering              : Attrib.binding -> Method.text -> thm list -> thm -> (thm list * thm list) option*)
end

structure DB_Completion
(* : COMPLETION *)
= struct

(* Error generated when an ordering cannot orient an equation *)
(* during completion.                                         *)

exception ORIENTATION of string * thm
exception RESTART_COMPLETION of string * thm list

val (max_time_in_completion, setup_max_time_in_completion) = Attrib.config_int @{binding "max_time_in_completion"} (K 180)
val (generate_cps, setup_generate_cps) = Attrib.config_bool @{binding "generate_cps"} (K true)
(* only used when critical pairs are generated *)
val (divergence_critic, setup_divergence_critic) = Attrib.config_bool @{binding "divergence_critic"} (K true)

(*fun ord_to_str l = 
    l |> map (fn (Const (n,_),i) => n ^ string_of_int i
               | (Var ((n,idx),_),i) => n ^ string_of_int idx ^ string_of_int i
               | _ => "")
      |> space_implode ""*)

(*(* Power set of a set. Sets are implemented as lists *)
fun subsets s =
    let 
      val s' = map (fn e => [[],[e]]) s
      fun subsets_ t l = 
          case l of
            (h::[]) :: [] => [t @ h]
          | (h::t1) :: [] => (t @ h) :: subsets_ t [t1]
          | (h::t1) :: t2 => ((subsets_ (t @ h) t2) @
                              (subsets_ t (t1 :: t2)))
          | _ => []
    in subsets_ [] s' end*)

local
 fun prep_trm ctxt (x, (T, t)) =
  (Thm.cterm_of ctxt (Var (x, T)), Thm.cterm_of ctxt t)

 fun prep_ty ctxt (x, (S, ty)) =
  (Thm.ctyp_of ctxt (TVar (x, S)), Thm.ctyp_of ctxt ty)
in
fun match_inst ctxt env =
  let
    val tenv = Vartab.dest (Envir.term_env env)
    val tyenv = Vartab.dest (Envir.type_env env)
    in
      (map (prep_ty ctxt) tyenv, map (prep_trm ctxt) tenv)
    end
end

(* left-linear equations are preferred when any orientation is terminating *)
fun is_linear thm =
    let val (_, args) = (strip_comb o fst o Utils.dest_meta_equation) thm
    in not (has_duplicates (op =) ((fold o fold_aterms)
                                     (fn Var (v, _) => cons v | _ => I) args [])) end

(* gives a left-linear orientation if possible *)
fun linear_if_possible R = if is_linear R then R else Utils.commute_meta_eq R

val my_abs_conv = fn ctxt => fn conv => Conv.abs_conv (fn _ => conv) ctxt

fun varify_global ctxt thm =
    let
      val frees = [] |> Term.add_frees (Thm.full_prop_of thm) |> map fst
    in [thm] |> Variable.export (snd (Variable.add_fixes frees ctxt)) ctxt
             |> hd end

fun rewrite_rule_extra_vars prems elhs erhs =
  let
    val elhss = elhs :: prems
    val tvars = fold Term.add_tvars elhss []
    val vars = fold Term.add_vars elhss []
  in
    erhs |> Term.exists_type (Term.exists_subtype
      (fn TVar v => not (member (op =) tvars v) | _ => false)) orelse
    erhs |> Term.exists_subterm
      (fn Var v => not (member (op =) vars v) | _ => false)
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
                           andalso not (rewrite_rule_extra_vars [] pat rhs1)
                           andalso not (rewrite_rule_extra_vars [] obj rhs2) (* does not introduce new Vars or TVars *)
      (* Does pat match a subterm of obj? *)
      fun msub bounds frees obj f =
          (case obj of
             Abs (_, T, t) =>
             let
               val unifier = if can (Sign.typ_unify thy (T,paty)) (Vartab.empty,Term.maxidx_typ T maxidx_typ)
                             then Unify.unifiers (Context.Theory thy,(Envir.empty 1),[(pat,obj)]) handle ListPair.UnequalLengths => Seq.empty
                                                                                        | TERM _ => Seq.empty
                             else Seq.empty
               val ((new_free, _), new_abs) = Term.dest_abs_global (Abs (Name.bound bounds, T, t))
             in Seq.append (Seq.map (pair f) unifier)
                           (msub (bounds + 1) (new_free :: frees)
                                 new_abs
                                 (f o (my_abs_conv ctxt))) end
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
              |> map_filter (fn (conv,(env,_)) => SOME (conv,Utils.unify_inst ctxt env))
              |> map (fn (conv,inst) => (conv,apply2 (Drule.instantiate_normalize inst) (th1,th2')))
              |> map (fn (conv,(r1,r2)) => Conv.fconv_rule ((Conv.fun_conv o Conv.arg_conv o conv) (Conv.rewr_conv (varify_global ctxt r1))) r2)
              |> filter_out (fn th => EQUAL = (Term_Ord.term_ord o Utils.dest_meta_equation) th)
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
              let val thm' = simplify (Simplifier.add_simps [rule] ctxt) thm
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

(* Empirical test for termination of ac rewriting *)
(* This test is necessarily incomplete due to the halting problem *)
fun ac_termination ctxt (equations, rules) th =
    let val max_size = (equations @ rules)
                         |> map size_of_thm
                         |> pair 0
                         |> Library.foldl (op +)
                         |> (fn c => if c = 0 then 1000 else
                                     c * Drule.size_of_thm th)
        fun update_net thm net =
          Net.insert_term (is_equal o Thm.thm_ord) (Thm.full_prop_of thm, thm) net
        fun test_procs set s (proc :: procs) term =
              let val t = simplify (Simplifier.add_simps [proc] ctxt) s
(*                  val _ = tracing ("Eq: " ^ Utils.str_of_thms [proc])
                  val _ = tracing ("1) s - t: " ^ Utils.str_of_thms [s, t])*)
              in if is_equal (Thm.thm_ord (s, t))
                 then test_procs set t procs term
                 else if can (update_net t) set
                 then test_procs (update_net t set) t procs term
                 else false
              end
          | test_procs set s [] term = test_rules set s (th :: rules) term
        and test_rules set s (rule :: rules) term =
              let val t = simplify (Simplifier.add_simps [rule] ctxt) s
(*                  val _ = tracing ("Rule: " ^ Utils.str_of_thms [rule])
                  val _ = tracing ("2) s - t: " ^ Utils.str_of_thms [s, t])
                  val _ = tracing (if is_equal (Thm.thm_ord (s, t)) then "si" else "no")*)
              in if is_equal (Thm.thm_ord (s, t))
                 then test_rules set t rules term
                 else if can (update_net t) set
                 then test_rules (update_net t set) t rules term
                 else false
              end
          | test_rules set s [] term =
              if (is_equal o Thm.thm_ord) (s, term)
              then true
              else if size_of_thm s < max_size
              then test_procs set s equations s
              else false
    fun test thm = 
      test_procs (update_net thm Net.empty) thm equations thm
  in forall test [th] end

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
               let val thy = Thm.theory_of_thm th
                   val _ = tracing ("Incompatible rule: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th))
                   val _ = tracing ("with: " ^ Utils.str_of_thms (equations @ rules))
               in (equations, rules)
               end)
(*         |> apply2 Utils.make_theorem_set*)
  end

(* The cache maps the propositions of the (sorted) input rules to positions
   in that list, each with a flag telling whether the rule was commuted.
   It must not store theorems: the cache outlives the theory where they
   were proved (e.g. when Isabelle/jEdit re-executes a command), and
   reusing them fails with "Cannot transfer: not a super theory". *)
val discriminate_rules_var
      = Synchronized.var "discriminate_rules"
                         (Term_List_Tab.empty : ((int * bool) list * (int * bool) list) Term_List_Tab.table)

fun memoized_discriminate_rules ctxt terminates thms =
  let val thy = Proof_Context.theory_of ctxt
      val thms = thms |> Utils.make_theorem_set
                      |> sort Thm.thm_ord
      fun is_index th' th =
        if Thm.equiv_thm thy (th', th)
        then SOME false
        else if Thm.equiv_thm thy (th', Utils.commute_meta_eq th)
        then SOME true
        else NONE
      val to_indices = map_filter (fn th' => get_index (is_index th') thms)
      fun dest_index (i, comm) =
            if comm
            then Utils.commute_meta_eq (nth thms i)
            else nth thms i
  in Utils.memoize_function Term_List_Tab.lookup Term_List_Tab.update (map Thm.full_prop_of)
                            discriminate_rules_var
                            (apply2 to_indices o discriminate_rules ctxt terminates) thms
       |> apply2 (map dest_index)
  end

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

(* Schematic rules.

   A schematic rule is a meta equation where some towers c (c (... s)) of
   a unary function c are written (c ^^ e) s, and all exponents e depend
   on one natural number variable ?n, e.g.

     f ((g ^^ Suc ?n) (f ?x)) == f ((g ^^ Suc ?n) ?x)

   It stands for the infinite family of its instances ?n = 0, 1, 2, ...
   Completion keeps the terms plain (no ^^): a simproc unfolds the
   instance that matches the redex and rewrites with it. Schematic rules
   live in the proof context, not in the rule lists, so AProVE and the
   term orderings only ever see plain first-order rules. *)

fun compow_exponents t =
  let fun exps (Const (@{const_name compow}, _) $ e $ c) acc = exps c (e :: acc)
        | exps (t $ u) acc = exps t (exps u acc)
        | exps (Abs (_, _, b)) acc = exps b acc
        | exps _ acc = acc
  in exps t [] end

fun is_schematic_rule th = not (null (compow_exponents (Thm.prop_of th)))

(* the natural number variable of the exponents, if there is exactly one *)
fun exponent_var th =
  case fold Term.add_vars (compow_exponents (Thm.prop_of th)) [] of
      [v as (_, @{typ nat})] => SOME v
    | _ => NONE

(* the instance n = k, with the towers unfolded *)
fun schematic_instance ctxt th k =
  case exponent_var th of
      SOME (v, _) =>
        let val nat_k = funpow k HOLogic.mk_Suc HOLogic.zero
            val unfold_ctxt = put_simpset HOL_basic_ss ctxt
                                |> Simplifier.add_simps @{thms funpow.simps comp_apply id_apply}
        in th |> Drule.infer_instantiate ctxt [(v, Thm.cterm_of ctxt nat_k)]
              |> simplify unfold_ctxt
        end
    | NONE => raise THM ("schematic_instance: no exponent variable", 0, [th])

fun schematic_simproc ctxt0 th =
  let val cache = Synchronized.var "schematic_instances" (Inttab.empty : thm Inttab.table)
      fun instance ctxt k =
        case Inttab.lookup (Synchronized.value cache) k of
            SOME r => r
          | NONE => let val r = schematic_instance ctxt th k
                        val _ = Synchronized.change cache (Inttab.update (k, r))
                    in r end
      val (head, args) = instance ctxt0 0 |> Thm.prop_of |> Logic.dest_equals |> fst |> strip_comb
      val pat = list_comb (head, map_index (fn (i, a) => Var (("x", i), fastype_of a)) args)
  in Simplifier.make_simproc ctxt0
       {name = "schematic_rule",
        kind = Simplifier.Simproc,
        lhss = [pat],
        (* a tower in the redex is at most as long as the redex itself *)
        proc = fn _ => fn ctxt => fn ct =>
          let val bound = size_of_term (Thm.term_of ct)
              fun try_instance k =
                if k > bound then NONE
                else SOME (Conv.rewr_conv (instance ctxt k) ct)
                     handle CTERM _ => try_instance (k + 1)
                          | THM _ => try_instance (k + 1)
          in try_instance 0 end,
        identifier = []}
  end

structure Schematic_Rules = Proof_Data
(
  type T = (thm * simproc) list
  fun init _ = []
)

val schematic_rules = map fst o Schematic_Rules.get

fun add_schematic_rule th ctxt =
  Schematic_Rules.map (fn rs => rs @ [(th, schematic_simproc ctxt th)]) ctxt

fun add_schematic_simprocs ctxt =
  fold (Simplifier.add_proc o snd) (Schematic_Rules.get ctxt) ctxt

fun ordered_simpset_without_simprocs ctxt terminates thms =
    let val ctxt = Simplifier.empty_simpset ctxt
        val (_,rules) = memoized_discriminate_rules ctxt terminates thms
    in Simplifier.add_simps rules (add_schematic_simprocs ctxt)
    end

fun ordered_simpset ctxt terminates thms =
    let val ctxt = Simplifier.empty_simpset ctxt
        val (equations, rules) = memoized_discriminate_rules ctxt terminates thms
    in Simplifier.add_simps (equations @ rules) (add_schematic_simprocs ctxt)
    end

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
      val ctxt = Simplifier.empty_simpset ctxt
      val (equations, rules) = memoized_discriminate_rules ctxt terminates E
(*      val _ = tracing ("E: " ^ Utils.str_of_thms E)
      val _ = tracing ("Equations: " ^ Utils.str_of_thms equations)
      val _ = tracing ("Rules: " ^ Utils.str_of_thms rules)
      val _ = tracing ("e: " ^ Utils.str_of_thms [e])*)
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
                            let val ctxt = ctxt |> Simplifier.set_term_ord g_ord
                                                |> add_schematic_simprocs
                                                |> (fn ctxt => Simplifier.add_simps (equations @ rules) ctxt)
                            in
                            e |> simplify ctxt
                              |> Utils.dest_meta_equation
                              |> (op =)
(*                              |> (is_equal o g_ord)*)
                            end)) f_map
 end

(*fun ground_joinable' ctxt terminates f_maps (e, E) = 
  Par_List.forall (fn f_map => ground_joinable ctxt terminates f_map (e, E)) f_maps*)

val memoized_joinability_var = Synchronized.var "memoized_joinability"
                      (Thm_Thm_List_Tab.empty : bool Thm_Thm_List_Tab.table)

(* the schematic rules of ctxt also decide joinability, so they are part of the key *)
fun memoized_joinable ctxt terminates f_map E e =
  let val E = sort Thm.thm_ord E
      val key_E = E @ schematic_rules ctxt
  in Utils.memoize_function Thm_Thm_List_Tab.lookup Thm_Thm_List_Tab.update I memoized_joinability_var
                            (fn _ => ground_joinable ctxt terminates f_map (e, E)) (e, key_E) end

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
      fun simpl ([],E',R') = (E',R')
        | simpl (u :: U,E',U') = 
          let
            val (g,_) = Utils.dest_meta_equation u
            val u' = normalize_part ctxt terminates (Conv.fun_conv o Conv.arg_conv) [th] u
            val (g',_) = Utils.dest_meta_equation u'
          in
            if EQUAL = Term_Ord.term_ord (g,g') then
              let val u'' = normalize_part ctxt terminates Conv.arg_conv (th :: R @ S) u
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
              (*val _ = tracing ("Before simplification: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th))*)
              val th' = rewrite_rule ctxt terminates (S @ R) (linear_if_possible th)
              (*val _ = tracing ("Antes: " ^ str_of_thms_raw [th'])*)
              val th' = th' |> Utils.meta_to_obj
(*                            |> Raw_Simplifier.rewrite_rule ctxt global_meta_rws*)
                            |> Utils.orient_rule thy ord
                            |> Utils.obj_to_meta
                            |> (fn th => if Thm.equiv_thm thy (@{thm "TrueI"},th)
                                         then Utils.obj_to_meta @{thm "refl"}
                                         else th)
              (*val _ = tracing ("After simplification: " ^ Utils.str_of_thms [th'])*)
              val (_, rules) = memoized_discriminate_rules (Simplifier.empty_simpset ctxt) terminates (S @ R)
              val joinable = memoized_joinable ctxt terminates f_map (S @ R) th'
(*              val _ = if joinable
                      then (tracing ("Joinable!: " ^ Utils.str_of_thms [th']);
                            tracing ("From: " ^ Utils.str_of_thms (S @ R)))
                      else ()*)
              fun restart () = NONE
              val (s,t) = Utils.dest_meta_equation th'
              val comm_th' = Utils.commute_meta_eq th'
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

(* Divergence critic for completion.

   When completion diverges it often produces a family of rules that only
   differ in the length of some towers of a unary function, e.g.

     f (g (f x)) = f (g x),  f (g (g (f x))) = f (g (g x)),  ...

   (cf. the meta-rules of H. Kirchner, TCS 67, 1989, the recurrence terms
   of Chen, Hsiang and Kong, CTRS 1990, and the divergence critic of
   T. Walsh for induction, JAIR 4, 1996). Every chosen rule is abstracted
   into a skeleton plus the lengths of its towers. Three chosen rules with
   the same skeleton whose tower lengths grow by 0 or 1 in each step
   suggest the schematic rule where the growing towers have length k + n,
   written c ^^ Suc^k n. It is proved by induction on n with the current
   rules (simp, then metis), and completion restarts with it. *)

fun is_funT (Type ("fun", _)) = true
  | is_funT _ = false

fun unary_symbol (Const (_, Type ("fun", [T, U]))) = T = U andalso not (is_funT T)
  | unary_symbol (Free (_, Type ("fun", [T, U]))) = T = U andalso not (is_funT T)
  | unary_symbol _ = false

val tower_hole = "__tower"

(* skeleton of t (maximal towers replaced by holes) and the tower lengths,
   in pre-order *)
fun tower_skeleton t =
  let fun tower c (t as c' $ s) k = if c' aconv c then tower c s (k + 1) else (k, t)
        | tower _ t k = (k, t)
      fun skel (t as c $ s) =
            if unary_symbol c then
              let val (k, base) = tower c t 0
                  val (base', ks) = skel base
                  val T = fastype_of c
              in (Free (tower_hole, T --> T) $ c $ base', k :: ks) end
            else
              let val (c', ks1) = skel c
                  val (s', ks2) = skel s
              in (c' $ s', ks1 @ ks2) end
        | skel (Abs (x, T, b)) = let val (b', ks) = skel b in (Abs (x, T, b'), ks) end
        | skel t = (t, [])
  in skel t end

(* variables renamed ?x, ?y, ... in order of first occurrence; the name n
   is kept for the exponent variable *)
fun canonical_vars t =
  let val vs = rev (Term.add_vars t [])
      val names = Name.invent (Name.make_context ["n"]) "x" (length vs)
      fun ren (Var (xi, T)) =
            Var ((nth names (find_index (fn (xi', _) => xi' = xi) vs), 0), T)
        | ren t = t
  in map_aterms ren t end

fun rule_signature th = th |> Thm.prop_of |> canonical_vars |> tower_skeleton

(* the skeleton with the given tower lengths; a tower whose length grows
   (delta 1) gets the exponent Suc^k n *)
fun build_from_skeleton n (Free (h, _) $ c $ base) ((k, delta) :: kds) =
      if h = tower_hole then
        let val (base', kds') = build_from_skeleton n base kds
            val T = fastype_of c
            val t = if delta = 0 then funpow k (fn s => c $ s) base'
                    else Const (@{const_name compow}, HOLogic.natT --> T --> T)
                           $ funpow k HOLogic.mk_Suc n $ c $ base'
        in (t, kds') end
      else raise TERM ("build_from_skeleton", [base])
  | build_from_skeleton n (t $ u) kds =
      let val (t', kds1) = build_from_skeleton n t kds
          val (u', kds2) = build_from_skeleton n u kds1
      in (t' $ u', kds2) end
  | build_from_skeleton n (Abs (x, T, b)) kds =
      let val (b', kds') = build_from_skeleton n b kds in (Abs (x, T, b'), kds') end
  | build_from_skeleton _ t kds = (t, kds)

(* a family among the chosen rules: tower lengths u, u + d, u + 2 d, ...
   with d in {0,1}^m, d <> 0, and the newest rule as its last member *)
fun find_family history (skel, v) =
  let val same = filter (fn (s, _) => s aconv skel) history
      fun present ks = exists (fn (_, ks') => ks' = ks) same
      fun minus (a, b) = map2 (fn x => fn y => x - y) a b
      fun delta_ok d = forall (fn x => x = 0 orelse x = 1) d andalso exists (fn x => x = 1) d
      fun lowest d u = if present (minus (u, d)) then lowest d (minus (u, d)) else u
  in get_first (fn (_, w) =>
        if length w <> length v then NONE
        else let val d = minus (v, w)
             in if delta_ok d andalso present (minus (w, d))
                then SOME (lowest d (minus (w, d)), d)
                else NONE
             end) same
  end

fun family_tac rules n others ctxt =
  Induct.induct_tac ctxt false [[SOME (NONE, (n, false))]] [others] [] NONE [] 1
  THEN ALLGOALS (TRY o asm_full_simp_tac (Simplifier.add_simps rules ctxt))
  THEN ALLGOALS (Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt rules)

(* SOME schematic rule (meta equation) proved for the family of rl *)
fun apply_divergence_critic ctxt terminates rules history rl =
  case find_family history (rule_signature rl) of
      NONE => NONE
    | SOME (u, d) =>
        let val (skel, _) = rule_signature rl
            val n = Var (("n", 0), HOLogic.natT)
            val (prop, _) = build_from_skeleton n skel (u ~~ d)
            val (lhs, rhs) = Logic.dest_equals prop
            val conj = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)) |> Logic.unvarify_global
            val n_free = Free ("n", HOLogic.natT)
            val others = Term.add_frees conj [] |> filter_out (fn v => v = ("n", HOLogic.natT))
            val rules_obj = map Utils.meta_to_obj rules
            val _ = tracing ("Divergence critic: " ^ Syntax.string_of_term ctxt conj)
            val time_out = Config.get ctxt Prover.max_time_in_proof
        in case Prover.prove_from_tactic ctxt NONE (family_tac rules_obj n_free others) conj time_out of
               SOME th =>
                 let val gen = Utils.obj_to_meta th
                     val instances = map (schematic_instance ctxt gen) [0, 1, 2]
                 in if exponent_var gen <> NONE andalso terminates (instances @ rules)
                    then (tracing ("Schematic rule: " ^ Utils.str_of_thms [gen]); SOME gen)
                    else (tracing "Schematic rule rejected (termination)"; NONE)
                 end
             | NONE => (tracing "Schematic rule not proved"; NONE)
        end

datatype COMPL = DONE of thm list | FINAL of thm list

fun complete global_meta_rws thy ctxt ord generate_cps terminates f_map E =
    let
      val proof_timeOut = Config.get ctxt Prover.max_time_in_proof
      val use_critic = generate_cps andalso Config.get ctxt divergence_critic
                       andalso length (schematic_rules ctxt) < 5
      val E = E |> map (fn th => (Utils.rule_int_ord th, th))
                |> sort ((list_ord int_ord) o (apply2 fst))
                |> map snd
      val E' = E
      fun restart_with gen =
        let val ctxt' = add_schematic_rule gen ctxt
            (* the critical pairs of the schematic rule are approximated by
               those of its first instances *)
            val instances = map (schematic_instance ctxt' gen) [0, 1, 2]
            val cps = semi_critical_pairs thy ord instances instances @
                      semi_critical_pairs thy ord instances E' @
                      semi_critical_pairs thy ord E' instances
            val _ = tracing ("Restarting completion with schematic rule: " ^ Utils.str_of_thms [gen])
        in complete global_meta_rws thy ctxt' ord generate_cps terminates f_map (E' @ cps) end
      (* history: signatures of the chosen rules; tried: skeletons already generalized *)
      fun compl (history, tried) (E,S,R) =
                          case (if !completion_debug then print_completion (E,S,R) else ();
                                orient ctxt global_meta_rws ord terminates f_map (E,S,R)) of
                            NORMAL ([],R') => DONE R'
                          | NORMAL (S',R') => let (*val lemmas = (S @ R) |> memoized_discriminate_rules terminates
                                                                           |> (fn (x, y) => x @ y)*)
                                                  val (rl,S'') = choose ctxt proof_timeOut E' S'
                                                  val _ = if !completion_debug then tracing ("Choosed: " ^ Utils.str_of_thms [rl])
                                                          else ()
                                                  val sg = rule_signature rl
                                                  val gen = if use_critic andalso
                                                               not (exists (fn s => s aconv fst sg) tried)
                                                            then apply_divergence_critic ctxt terminates (rl :: R') history rl
                                                            else NONE
                                              in case gen of
                                                   SOME gen => FINAL (restart_with gen)
                                                 | NONE =>
                                                let
                                                  val tried = if use_critic andalso is_some (find_family history sg)
                                                              then fst sg :: tried else tried
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
                                              in compl (sg :: history, tried) (cps,S'',rl :: R') end
                                              end
                          | RESTART thms => (tracing ("Restarting completion..." ^ Utils.str_of_thms (E' @ thms));
                                             FINAL (complete global_meta_rws thy ctxt ord generate_cps terminates f_map (E' @ thms)))
    in
      case (E,[],[]) |> compl ([], []) of
        FINAL TRS => TRS
      | DONE R =>
          R |> make_irreducible ctxt terminates f_map []
            |> (fn TRS => TRS @ schematic_rules ctxt)
            |> tap (fn TRS => tracing ("Done: " ^ Utils.str_of_thms TRS))
    end

fun run_completion global_meta_rws ctxt terminates E e =
  let val thy = ctxt |> Proof_Context.theory_of
      val ctxt = if can Local_Theory.target_of ctxt
                 then Local_Theory.target_of ctxt
                 else ctxt
      val generate_cps = Config.get ctxt generate_cps
      val _ = tracing ("Completing: " ^ Utils.str_of_thms E)
      val _ = tracing ("with: " ^ Utils.str_of_thms [e])
      val deps = Utils.definitional_dependencies thy ([], Thm.full_prop_of e)
                  |> map Const
      val f_map_eq = deps
                    |> map (rpair 0)
(*     val f_map_less = map_index (fn (x,y) => (y,x)) deps
     val f_map_greater = map_index (fn (x,y) => (y,x)) (rev deps)*)
     val f_maps = f_map_eq
     (* schematic rules (from compl, or e itself) go to the context *)
     val (schematic, plain) = List.partition is_schematic_rule (e :: E)
     val (schematic, rejected) = List.partition (is_some o exponent_var) schematic
     val _ = if null rejected then ()
             else tracing ("Ignored (several exponent variables): " ^ Utils.str_of_thms rejected)
     val ctxt = fold add_schematic_rule schematic ctxt
  in [complete global_meta_rws thy ctxt LESS generate_cps terminates f_maps,
      complete global_meta_rws thy ctxt GREATER generate_cps terminates f_maps]
      |> Par_List.get_some (fn f => SOME (f plain))
      |> the
  end

fun run_completion' global_meta_rws ctxt terminates E e =
    let val rules = run_completion global_meta_rws ctxt terminates E e
        val thy = Proof_Context.theory_of ctxt
        val additions = filter_out (fn r => exists (Thm.equiv_thm thy o pair r) E) rules
        val deletions = filter_out (fn e => exists (Thm.equiv_thm thy o pair e) rules) E
    in (additions, deletions) end

end

structure Ground_Completion : COMPLETION = DB_Completion
