(*  Title:      util/counter_example.ML
    ID:         $Id: counter_example.ML,v 1.010 2009/08/07 20:07:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   University of Edinburgh 2009

Counter example checking by different tools.
The tools used are quickcheck and Nitpick.
*)

signature COUNTER_EXAMPLE =
sig
  val use_quickcheck                  : bool Config.T
  val use_nitpick                     : bool Config.T
  val simp_before                     : bool Config.T
  val max_time_in_counter_ex          : int Config.T
  val get_nitpick_params              : Nitpick.params -> int -> Nitpick.params

  val nitpick_params                  : Nitpick.params
  val counter_example                 : Proof.context -> int -> term -> bool
  val memoized_counter_example        : Proof.context -> int -> term -> bool
  val unfalsified_conjecture          : Proof.context -> int -> term -> term option
  val enumerate_terms                 : Proof.context -> int -> typ -> term list
end

structure DB_Counter_Example
(* : COUNTER_EXAMPLE *)
= struct

val (use_quickcheck, setup_use_quickcheck) = Attrib.config_bool @{binding "use_quickcheck"} (K true)
val (use_nitpick, setup_use_nitpick) = Attrib.config_bool @{binding "use_nitpick"} (K true)
val (simp_before, setup_simp_before) = Attrib.config_bool @{binding "simp_before"} (K false)
val (max_time_in_counter_ex, setup_max_time_in_counter_ex) = Attrib.config_int @{binding "max_time_in_counter_ex"} (K 5)

val nitpick_params = Nitpick_Commands.default_params @{theory} []
(*fun simp_method ctxt = Utils.parse ctxt Method.parse "simp" |> fst o fst*)
fun simp_method ctxt = Utils.parse ctxt (Method.parser 1) "simp" |> fst

fun get_nitpick_params
   ({cards_assigns: (typ option * int list) list,
     maxes_assigns: ((string * typ) option * int list) list,
     iters_assigns: ((string * typ) option * int list) list,
     bitss: int list,
     bisim_depths: int list,
     boxes: (typ option * bool option) list,
     finitizes: (typ option * bool option) list,
     monos: (typ option * bool option) list,
     wfs: ((string * typ) option * bool option) list,
     sat_solver: string,
     falsify: bool,
     debug: bool,
     verbose: bool,
     overlord: bool,
     spy: bool,
     user_axioms: bool option,
     assms: bool,
     whacks: term list,
     merge_type_vars: bool,
     binary_ints: bool option,
     destroy_constrs: bool,
     specialize: bool,
     star_linear_preds: bool,
     total_consts: bool option,
     needs: term list option,
     peephole_optim: bool,
     datatype_sym_break: int,
     kodkod_sym_break: int,
(*     timeout: Time.time,*)
     tac_timeout: Time.time,
(*     max_threads: int,*)
     show_types: bool,
     show_skolems: bool,
     show_consts: bool,
     evals: term list,
     formats: (term option * int list) list,
     atomss: (typ option * string list) list,
     max_potential: int,
     max_genuine: int,
     batch_size: int,
     expect: string, ...} : Nitpick.params) timeOut =
    {cards_assigns = cards_assigns,
     maxes_assigns = maxes_assigns,
     iters_assigns = iters_assigns,
     bitss = bitss,
     bisim_depths = bisim_depths,
     boxes = boxes,
     finitizes = finitizes,
     monos = monos,
     wfs = wfs,
     sat_solver = sat_solver,
     falsify = falsify,
     debug = debug,
     verbose = verbose,
     overlord = overlord,
     spy = spy,
     user_axioms = user_axioms,
     assms = assms,
     whacks = whacks,
     merge_type_vars = merge_type_vars,
     binary_ints = binary_ints,
     destroy_constrs = destroy_constrs,
     specialize = specialize,
     star_linear_preds = star_linear_preds,
     total_consts = total_consts,
     needs = needs,
     peephole_optim = peephole_optim,
     datatype_sym_break = datatype_sym_break,
     kodkod_sym_break = kodkod_sym_break,
     timeout = Time.fromSeconds timeOut,
     tac_timeout = tac_timeout,
     max_threads = 1,
     show_types = show_types,
     show_skolems = show_skolems,
     show_consts = show_consts,
     evals = evals,
     formats = formats,
     atomss = atomss,
     max_potential = max_potential,
     max_genuine = max_genuine,
     batch_size = batch_size,
     expect = expect} : Nitpick.params

fun quickcheck timeOut state =
    if Config.get (Proof.context_of state) use_quickcheck
    then
      (case Quickcheck.quickcheck [("timeout",[Int.toString timeOut])] 1 state of
         SOME _ => (true, state)
       | NONE => (false, state))
    else (false, state)

fun quickcheck_term timeOut state =
    if Config.get (Proof.context_of state) use_quickcheck
    then
      (case Quickcheck.quickcheck [("timeout",[Int.toString timeOut])] 1 state of
         SOME (_,r) => SOME r
       | NONE => NONE)
    else NONE

fun quickcheck_model timeOut state =
    Quickcheck.quickcheck [("timeout",[Int.toString timeOut])] 1 state

fun nitpick timeOut state =
    Config.get (Proof.context_of state) use_nitpick andalso
    (Utils.safe_eval "counter_example.ML 151:" false
      (fn step => (step |> Nitpick.pick_nits_in_subgoal state (get_nitpick_params nitpick_params timeOut) Nitpick.Normal 1
                        |> (fn (sce,_) => if "genuine" = sce then true
                                          (* FIXME: What if potential! *)
                                          (*else if "potential" = sce then
                                            null (!Nitpick_Model.reconstructed_model)*)
                                          else false))) 0)

fun quickcheck_nitpick_raw ctxt timeOut conjecture =
    ctxt |> Proof.theorem NONE (K I) [[(conjecture, [])]]
         |> (fn state => if Config.get (Proof.context_of state) simp_before
                         then (Proof.apply (simp_method (Proof.context_of state)) state)
                                |> (Seq.hd o Seq.filter_results)
                         else state)
         |> (fn state => state |> Utils.safe_eval "counter_example 164" (false, state) (quickcheck timeOut)
                               |> (fn (foo,_) => (foo, state)))
         |> (fn (foo,state) => 
                foo orelse (Utils.safe_eval "counter_example.ML 172" false (nitpick timeOut) state))

fun quickcheck_term_raw ctxt timeOut conjecture =
    ctxt |> Proof.theorem NONE (K I) [[(conjecture, [])]]
         |> (fn state => state |> Utils.safe_eval "counter_example 154" NONE (quickcheck_term timeOut))
         |> (fn SOME l => get_first (fn (name, t) => if name = "x"
                                                     then SOME t
                                                     else NONE) l
              | _ => NONE)

fun quickcheck_terms ctxt timeOut n typ =
  let val concl = HOLogic.mk_Trueprop (Free ("P", typ --> @{typ "bool"}) $ Free ("x", typ))
      fun neg t = HOLogic.mk_not (HOLogic.mk_eq (Free ("x", typ), t))
                    |> HOLogic.mk_Trueprop
      val fix = HOLogic.mk_Trueprop o HOLogic.dest_not o HOLogic.dest_Trueprop
      fun mk_conjecture tab =
          tab |> Term_Tab.keys
              |> map neg
              |> (fn [] => concl
                  | h :: tl => Logic.list_implies (tl, fix h))
              |> tap (tracing o Syntax.string_of_term ctxt)
      fun terms 0 tab = Term_Tab.keys tab
        | terms n tab = 
        let val _ = tracing (string_of_int n)
        in
        case quickcheck_term_raw ctxt timeOut (mk_conjecture tab) of
          SOME t => terms (n-1) (Term_Tab.update (t, ()) tab)
          | NONE => Term_Tab.keys tab end
  in terms n Term_Tab.empty end
  
fun counter_example _ _ (_ $ Const ("HOL.True",_)) = false
  | counter_example ctxt timeOut conjecture = quickcheck_nitpick_raw ctxt timeOut conjecture

val false_set = Synchronized.var "CE_false_set" (Net.empty : term Net.net)

fun subsumed_in_net thy t net =
  let val t = Logic.varify_global t
  in t |> Net.unify_term net
       |> exists (fn t' => Pattern.matches thy (t, t')) end

fun memoized_counter_example ctxt timeOut conjecture =
  let val thy = Proof_Context.theory_of ctxt
  in if false_set |> Synchronized.value
                  |> subsumed_in_net thy conjecture
     then true
     else let val v = counter_example ctxt timeOut conjecture
              val _ = if v
                      then Synchronized.change false_set
                            (fn net => Net.insert_term_safe (Pattern.equiv thy)
                                                            (conjecture, conjecture) net)
                      else ()
          in v end
  end

fun unfalsified_conjecture ctxt timeOut conjecture =
  if memoized_counter_example ctxt timeOut conjecture
  then NONE
  else SOME conjecture

fun preprocess_counter_example ctxt size n table timeOut conjecture =
  let val thy = Proof_Context.theory_of ctxt
      val frees = Term.add_frees conjecture []
      val tss = map (fn (_,ty) =>
          case Type_Tab.lookup table ty of
            SOME ts => ts
            | NONE  => (1 upto n)
                         |> map_filter (fn _ => Random_Terms.random_term ctxt size ty)
                         |> tap (fn _ => tracing "Re processing random terms!")
                         |> Utils.make_term_set thy
                         |> (fn ts => ts)) frees
      fun take n f =
        if n = 0 then []
        else case f () of
          SOME r => (frees ~~ r) :: take (n-1) f
          | NONE => []
      val conjs  = tss |> Utils.lazy_one_of_each
                       |> take (size * n)
                       |> map (map (fn (v, t) => (Free v, t)))
                       |> map Term.subst_free
                       |> map (fn f => f conjecture)
  in exists (fn conj => Utils.normalise_term ctxt [] conj = @{prop "False"}) conjs orelse
     memoized_counter_example ctxt timeOut conjecture end

local
fun quickcheck_term n state =
      (case Quickcheck.quickcheck [("size",[string_of_int (10 + n)])] 1 state of
         SOME (_,r) => SOME r
       | NONE => quickcheck_term (n+1) state)

fun quickcheck_term_raw ctxt n conjecture =
    ctxt |> Proof.theorem NONE (K I) [[(conjecture, [])]]
         |> quickcheck_term n
         |> (fn SOME l => get_first (fn (name, t) => if name = "x"
                                                     then SOME t
                                                     else NONE) l
              | _ => NONE)

in
fun enumerate_terms ctxt n typ =
  let fun mk_not (s,t) = (HOLogic.mk_Trueprop o HOLogic.mk_not o HOLogic.mk_eq) (s,t)
      val x = Free ("x", typ)
      val concl = mk_not (x,x)
      fun neg t = mk_not (x,t)
      val fix = HOLogic.mk_Trueprop o HOLogic.dest_not o HOLogic.dest_Trueprop
      fun mk_conjecture tab =
          tab |> Term_Tab.keys
              |> map neg
              |> (fn [] => concl
                  | h :: tl => Logic.list_implies (tl, fix h))
      fun terms 0 tab = Term_Tab.keys tab
        | terms n tab =
        case quickcheck_term_raw ctxt n (mk_conjecture tab) of
          SOME t => terms (n-1) (Term_Tab.update (t, ()) tab)
          | NONE => Term_Tab.keys tab
  in terms n Term_Tab.empty end
end

end

structure Counter_Example : COUNTER_EXAMPLE = DB_Counter_Example
