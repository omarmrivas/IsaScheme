(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature UTILS =
sig
  val max_time_normalization : int Config.T

  (* Printing *)
  val str_of_thms        : thm list -> string
  val str_of_terms       : Proof.context -> term list -> string
  val print_ss           : Proof.context -> unit
  val trace_log          : Path.T -> string -> unit
  val create_log         : Path.T -> unit
  val html_table         : string -> string list list -> string
  val write_to_file      : string -> string -> unit
  val extract_filename   : string -> string
  val extract_filename'  : string -> string
  val pretty_tyenv       : Proof.context -> (sort * typ) Vartab.table -> unit
  val pretty_env         : Proof.context -> (typ * term) Vartab.table -> unit

  (* Discrete mathematics *)
  val subsets            : 'a list -> 'a list list
  val sort_poset         : ('a * 'a -> bool) -> 'a list -> (int * 'a) list
  val classify_poset     : ('a * 'a -> bool) -> 'a list -> 'a list list
  
  (* Terms *)
  val string_of_term     : Proof.context -> term -> string
  val string_of_term'    : Proof.context -> term -> string
  val latex_string_of_term     : Proof.context -> term -> string
  val latex_str_of_thms  : thm list -> string
(*  val html_string_of_term     : Proof.context -> term -> string*)
  val string_of_typ      : Proof.context -> typ -> string
  val int_of_string      : string -> int
  val unique_names       : term -> term
  val dummyfy_term       : term -> term
  val positions          : term -> (term * typ * int list) list
  val bounds_at_position : term -> int list -> (string * typ) list
  val term_at            : int list -> term -> term
  val substitute         : (term * int list) -> term -> term
  val binder_vars        : string -> (string * typ) list -> term -> (string * typ) list
  val binder_elimination : string -> term list -> term -> term * term list
  val fold_subterms      :  (term -> 'a -> 'a) -> term -> 'a -> 'a
  val fold_subterms_no_loose      :  (term -> 'a -> 'a) -> term -> 'a -> 'a
  val subterms_no_loose_no_funs :term -> term list
  val subterms           : term -> term list
  val subterms_no_loose  : term -> term list
  val make_term_set      : theory -> term list -> term list
  val make_term_set'     : theory -> term list -> term list
  val make_term_set_by   : theory -> ('a -> term) -> 'a list -> 'a list
  val make_term_set_by'   : theory -> ('a -> term) -> 'a list -> 'a list
  val sort_by_general    : theory -> term list -> term list
  val sort_by_general'   : theory -> ('a -> term) -> 'a list -> 'a list
  val make_theorem_set   : thm list -> thm list
  val generalizations    : theory -> int -> term list -> term list
  val generalizations'   : theory -> int -> term list -> term list
  val is_trivial         : term -> bool
  val normalise_term     : Proof.context -> thm list -> term -> term 

  (* Rewrite rules *)
  val lhs                : term -> term
  val rhs                : term -> term
  val bad_equation       : theory -> term * term -> bool
  val bad_equation'      : theory -> term -> bool
  val orient_eq          : theory -> order -> term -> term
  val orient_rule        : theory -> order -> thm -> thm
  val orient_meta_rule   : theory -> order -> thm -> thm
  val swap_eq            : term -> term
  val permutative_eq     : term * term -> bool
  val permutative_rule           : thm -> bool
  val order_ints_raw             : term -> int list
  val equations                  : theory -> term -> term list
  val ac_orient                  : order -> term -> term
  val not_constructor            : theory -> term -> bool
  val get_rewrites               : theory -> string -> thm list
  val get_definitional_rewrites  : theory -> term -> thm list
  val definitional_dependencies  : theory -> ((string * typ) list * term) -> (string * typ) list
  val definitional_orientation   : theory -> term -> bool
  val oriented_rules_var         : unit Term_Tab.table Synchronized.var
  val schematic_lemmas_var       : unit Term_Tab.table Synchronized.var
  val get_orientation_schemes    : unit -> term list
  val get_schematic_lemmas       : unit -> term list
  val rules_in_simpset           : term list -> thm list

  (* Rewrite rules *)
  val meta_to_obj                      : thm -> thm
  val obj_to_meta                      : thm -> thm
  val commute_obj_eq                   : thm -> thm
  val commute_meta_eq                  : thm -> thm
  val dest_meta_equation               : thm -> (term * term)
  val dest_object_equation             : thm -> (term * term)
  val rule_int_ord                     : thm -> int list
  
  (* Others *)
  val rat_to_float       : Rat.rat -> real
  val int_of_numeral     : term -> int
  val rat_of_numeral     : term -> Rat.rat
  val elements_of_list   : term -> term list
  val elements_of_product_type   : term -> term list
  val numeral_of_int     : Proof.context -> int -> term
  val numeral_of_nat     : Proof.context -> int -> term
  val minby              : ('a * 'a -> order) -> ('b -> 'a) -> 'b list -> 'b
  val maxby              : ('a * 'a -> order) -> ('b -> 'a) -> 'b list -> 'b
  val next_digit         : int list -> int list -> int list option
  val binomial_coefficient: int -> int -> int
  val choose             : 'a list -> int -> int -> 'a list
  val dfs                : 'a list -> ('a -> bool) -> ('a -> 'a list) -> ('a * 'a list) option
  val dfs'               : 'a list -> ('a -> bool) -> ('a -> 'a list) -> 'a Seq.seq
  val all_permutations   : 'a list -> 'a list Seq.seq
  val arrangements       : int -> 'a list -> 'a list Seq.seq
  val lazy_one_of_each   : 'a list list -> unit -> 'a list option
  val lazy_subsets       : 'a list -> 'a list Seq.seq
  val lazy_subsets_of_size : int -> 'a list -> 'a list Seq.seq
  val safe_eval          : string -> 'b -> ('c -> 'b) -> 'c -> 'b
  val parse              : Proof.context -> (Token.T list -> 'a * Token.T list) -> string -> 'a * Token.T list
  val timing_wrapper     : ('a -> 'b) -> 'a -> 'b
  val timing_wrapper'    : (Timing.timing -> bool) ->
                              (unit -> string) -> ('a -> 'b) -> 'a -> 'b
  val memoize_function   : ('a -> 'b -> 'c option) -> ('b * 'c -> 'a -> 'a) ->
                           'a Synchronized.var -> ('b -> 'c) -> 'b -> 'c
  val foldl_seq          : ('a * 'b -> 'a) -> 'a * 'b Seq.seq -> 'a
  val random             : unit -> real
  val weighted_choose    : ('a * int) list -> 'a
  val repeat_until       : ('a -> bool) -> ('b -> 'a) -> 'b -> 'a
  val trim               : string -> string
end

structure DB_Utils
(* : UTILS *)
= struct

val (max_time_normalization, setup_max_time_normalization) = Attrib.config_int @{binding "max_time_normalization"} (K 5)

fun str_of_thms thms = 
  let fun str_of_cterm thy t = Syntax.string_of_term_global thy (Thm.term_of t)
      fun str_of_thm thy thm = str_of_cterm thy (Thm.cprop_of thm)
  in commas (map (fn th => str_of_thm (Thm.theory_of_thm th) th) thms) end

(* Exceptions *)
exception BadPosition of term * int list

(* Useful data structures *)

(* Table containing type contexts used in the 
   enumeration of typed lambda terms. *)
structure ContextSet = Table(
  type key = string * typ
  val ord = prod_ord string_ord Term_Ord.typ_ord)

(*fun safe_eval txt a f b = the_default (tracing txt; a) (try f b)*)
fun safe_eval _ a f b = the_default a (try f b)

val rat_to_float = op / o apply2 real o Rat.dest

(* Discrete mathematics utils *)

(* Power set of a set. Sets are implemented as lists *)
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
    in subsets_ [] s' end

fun sort_poset rel s =
  (map (fn e => (0, e)) s, s)
    |> Library.foldl (fn (sm, e) => map (fn (i, e') => 
                      if rel (e, e')
                      then (i + 1, e')
                      else (i, e')) sm)
    |> sort (int_ord o apply2 fst)
fun classify_poset rel s =
  let fun classify (s as (i, _) :: _) =
            let val (sl, sr) = take_prefix (fn (i', _) => i = i') s
            in case sl of
                      (_ :: _) => map snd sl :: classify sr
                    |    []    => classify sr
            end
       |  classify [] = []
  in s |> sort_poset rel
       |> classify end

(* Term utils *)

fun vperm (Var _, Var _) = true
  | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
  | vperm (t1 $ t2, u1 $ u2) = vperm (t1, u1) andalso vperm (t2, u2)
  | vperm (t, u) = (t = u)

fun permutative_eq (t, u) =
  vperm (t, u) andalso eq_set (op =) (Term.add_vars t [], Term.add_vars u [])

(* Maps all types in term to dummyT *)
fun dummyfy_term t = 
    case t of 
      Const (c,_) => Const (c,dummyT)
    | Free (n,_) => Free (n,dummyT)
    | Var (i,_) => Var (i,dummyT)
    | Bound i => Bound i
    | Abs (n, _, a) => Abs (n,dummyT,dummyfy_term a)
    | a1 $ a2 => dummyfy_term a1 $ dummyfy_term a2

fun binder_vars bin vars (t $ a) =
  (case (t $ a) of
    (Const (bin',_) $ Abs (n,T,body)) =>
      if bin = bin'
      then binder_vars bin ((n, T) :: vars) body
      else binder_vars bin vars body
    | _ =>   binder_vars bin vars t @ binder_vars bin vars a)
| binder_vars bin vars (Abs (_, _, body)) =
  binder_vars bin vars body
| binder_vars _ vars _ = vars

(* Removes all binders bin from a term, replacing bound variables by frees. *)
local
  fun dest_binder bin (Const (bin', _) $ Abs (a as (_,T,_))) =
      if bin = bin' then
        let val (n, body) = Term.dest_abs a in
          (Free (n, T), body) end
      else raise Match
    | dest_binder _ _ = raise Match
in
fun binder_elimination bin vars (t as (Const (bin',_) $ _)) = 
    if bin = bin' then 
      let val (v,b) = dest_binder bin t
          val b' = binder_elimination bin (v :: vars) b in
        b' end
    else (t,vars)
  | binder_elimination _ vars t = (t,vars)
end

(* Sets of terms and theorems *)
fun fold_subterms f (t $ u) a = 
    (* Simulate higher-order terms *)
    (* fold_subterms f t (fold_subterms f u (f (t $ u) a)) *)
    (* Simulate first-order terms *)
    let val (_, arguments) = Term.strip_comb (t $ u)
    in
      Library.foldl (fn (ps, term) => fold_subterms f term ps) (f (t $ u) a ,arguments)
    end
  | fold_subterms f (Abs (V, T, t)) a = fold_subterms f t (f (Abs (V, T, t)) a)
  | fold_subterms f t b = f t b

fun fold_subterms_no_loose f (t $ u) a =
    (* Simulate higher-order terms *)
    (* fold_subterms_no_loose f t (fold_subterms_no_loose f u (f (t $ u) a)) *)
    (* Simulate first-order terms *)
    let val (_, arguments) = Term.strip_comb (t $ u)
    in
      Library.foldl (fn (ps, term) => fold_subterms_no_loose f term ps) (f (t $ u) a ,arguments)
    end
  | fold_subterms_no_loose f (Abs (V, T, t)) a = 
      let val t' = (snd o Term.dest_abs) (V, T, t)
      in fold_subterms_no_loose f t' (f (Abs (V, T, t)) a) end
  | fold_subterms_no_loose f t b = f t b

fun subterms term =
  let val net = Net.empty
  in net |> fold_subterms (fn t => fn net => 
              Net.insert_term_safe (is_equal o Term_Ord.fast_term_ord) (t, t) net) term
         |> Net.content
  end

fun subterms_no_loose term =
  let val net = Net.empty
  in net |> fold_subterms_no_loose (fn t => fn net =>
               Net.insert_term_safe (is_equal o Term_Ord.fast_term_ord) (t, t) net) term
         |> Net.content
  end

fun subterms_no_loose_no_funs term =
  let val net = Net.empty
  in net |> fold_subterms_no_loose (fn t => fn net =>
            if (null o binder_types o type_of) t
            then Net.insert_term_safe (is_equal o Term_Ord.fast_term_ord) (t, t) net
            else net) term
         |> Net.content
  end

fun full_map_aterms f (t $ u) = 
  (case (f (t $ u)) of 
    SOME tu => tu 
   | _ => full_map_aterms f t $ full_map_aterms f u)
| full_map_aterms f (Abs (a, T, t)) = 
  (case (f (Abs (a, T, t))) of 
    SOME tu => tu 
   | _ => Abs (a, T, full_map_aterms f t))
| full_map_aterms f t = the_default t (f t)

fun pattern_equiv thy (t1, t2) =
  Pattern.equiv thy (t1, t2)
    handle TYPE msg => ((t1, t2) |> apply2 (Syntax.string_of_term_global thy)
                                 |> (fn (s1, s2) => s1 ^ " : " ^ s2)
                                 |> tracing; raise TYPE msg)

fun make_term_set thy tms =
  (Net.empty, tms)
    |> Library.foldl (fn (net, t) =>
        Net.insert_term_safe (pattern_equiv thy) (t, t) net)
    |> Net.content

fun make_term_set_by thy by tms =
  (Net.empty, tms)
    |> Library.foldl (fn (net, t) =>
        Net.insert_term_safe (pattern_equiv thy o apply2 by) (by t, t) net)
    |> Net.content

fun make_term_set' thy terms =
  terms |> map_index (fn (i, t) => t |> Logic.varify_global
                                     |> Logic.incr_indexes ([], [], i))
        |> make_term_set thy
        |> map (Logic.unvarify_global o Term_Subst.zero_var_indexes)
        |> sort (int_ord o (apply2 size_of_term))

fun make_term_set_by' thy by terms =
  terms |> map_index (fn (i, t) => (t, t |> by
                                         |> Logic.varify_global
                                         |> Logic.incr_indexes ([], [], i)))
        |> make_term_set_by thy snd
        |> map fst
        |> sort (int_ord o (apply2 size_of_term) o (apply2 by))

fun make_theorem_set thms =
  thms |> zero_var_indexes_list
       |> map_index (fn (i, th) => Thm.incr_indexes i th)
       |> pair Net.empty
       |> Library.foldl (fn (net, th) =>
            Net.insert_term_safe (Thm.equiv_thm (Thm.theory_of_thm th)) (Thm.full_prop_of th, th) net)
       |> Net.content
       |> zero_var_indexes_list

fun subterm_positions pos (t', t) =
  let val ty = type_of t'
  in case (t', t) of
      (Abs (n, T, s'), Abs (_, _, s)) =>
        let val aa = (snd o Term.dest_abs) (n, T, s')
        in (t', ty, rev pos) :: subterm_positions (0 :: pos) (aa, s)
        end
   | (p' $ q', p $ q) =>
        (t', ty, rev pos) :: subterm_positions (0 :: pos) (p', p) @
                             subterm_positions (1 :: pos) (q', q)
   | _ => [(t', ty, rev pos)]
  end

fun positions t = subterm_positions [] (t, t)

fun bounds_at_position (Abs (n, ty, t)) (0 :: is) = 
      (n, ty) :: bounds_at_position t is
  | bounds_at_position (p $ _) (0 :: is) = 
      bounds_at_position p is
  | bounds_at_position (_ $ q) (1 :: is) = 
      bounds_at_position q is
  | bounds_at_position _ [] = []
  | bounds_at_position t pos = raise BadPosition (t, pos)

fun term_at (0 :: pos) (Abs (_, _, t)) =
      term_at pos t
  | term_at (0 :: pos) (p $ _) =
      term_at pos p
  | term_at (1 :: pos) (_ $ q) =
      term_at pos q
  | term_at [] t = t
  | term_at pos t = raise BadPosition (t, pos)

fun substitute (t', 0 :: pos) (Abs (v, T, t)) =
      Abs (v, T, substitute (t', pos) t)
  | substitute (t', 0 :: pos) (p $ q) =
      (substitute (t', pos) p) $ q
  | substitute (t', 1 :: pos) (p $ q) =
      p $ (substitute (t', pos) q)
  | substitute (t', []) _ = t'
  | substitute (_, pos) t = raise BadPosition (t, pos)

fun string_of_term ctxt t =
    let
      val ctxt' = ctxt |> Config.put show_markup false
                       |> Config.put show_question_marks false
    in Print_Mode.setmp [] (Syntax.string_of_term ctxt') t end

fun string_of_term' ctxt t =
    let
      val ctxt' = ctxt |> Config.put show_markup false
    in Print_Mode.setmp [] (Syntax.string_of_term ctxt') t end

fun latex_string_of_term ctxt t =
    let
      val ctxt' = ctxt |> Config.put show_markup false
                       |> Config.put show_question_marks false
    in Print_Mode.setmp ["Latex"] (Latex.output_ascii o Syntax.string_of_term ctxt') t end

fun latex_str_of_thms thms =
  let fun to_str thm =
         let val ctxt = thm |> Thm.theory_of_thm
                            |> Context.Theory
                            |> Context.proof_of
         in latex_string_of_term ctxt (Thm.full_prop_of thm) end
  in commas (map to_str thms) end

(*fun html_string_of_term ctxt t =
    let
      val ctxt' = ctxt |> Config.put show_markup false
                       |> Config.put show_question_marks false
    in myHTML.html_mode (Syntax.string_of_term ctxt') t end*)

fun string_of_typ ctxt ty =
    let
      val ctxt' = Config.put show_markup false ctxt;
    in Print_Mode.setmp [] (Syntax.string_of_typ ctxt') ty end

val log_var = Synchronized.var "log_var" (() : unit)

fun trace_log file str =
  Synchronized.change log_var (fn () => File.append file (str ^ "\n"))

fun create_log file =
  Synchronized.change log_var (fn () => File.write file "")

fun html_table id content =
    let fun td str = enclose "<td>" "</td>" str
        fun tr strs =
          strs |> map td
               |> space_implode "\n"
               |> enclose "<tr>" "</tr>"
    in content |> map tr
               |> space_implode "\n"
               |> enclose ("<table id=\"" ^ id ^ "\" border=\"1\">") "</table>"
(*               |> enclose "<table border=\"1\" style=\"width:100%\">" "</table>"*)
    end

fun write_to_file filename str =
    let val path = Path.explode filename
        val _ = if File.exists path
                then ()
                else create_log path
    in File.write path str end

fun extract_filename str =
    (str |> String.explode
        |> rev
        |> find_index (fn c => c = #"/")
        |> (fn i => String.extract (str, String.size str - i, NONE)))
        handle Subscript => (tracing ("Error extracting filename: " ^ str); str)

fun extract_filename' str =
  let val str = extract_filename str
  in
    (str |> String.explode
        |> find_index (fn c => c = #".")
        |> (fn i => String.extract (str, 0, SOME i)))
        handle Subscript => (tracing ("Error extracting filename: " ^ str); str)
  end

fun unique_names t =
  let fun unique names (Abs (v, T, t)) =
        let val name = singleton (Name.variant_list names) v
        in Abs (name, T, unique (name :: names) t) end
        | unique names (s $ t) = unique names s $ unique names t
        | unique _ t = t
  in unique [] t end

val var_type = (null o fst o strip_type)

val arrow_type = not o var_type

fun equations thy term =
  term |> subterms_no_loose
       |> filter (can (HOLogic.dest_eq))
       |> make_term_set thy

val swap_eq = HOLogic.mk_eq o swap o HOLogic.dest_eq

fun memoize_function lookup update var f input =
  case lookup (Synchronized.value var) input of
      SOME foo => foo
    | NONE => let val r = f input
                  val _ = Synchronized.change var
                            (fn tab => update (input, r) tab)
              in r end

val oriented_rules_var = Synchronized.var "oriented_rules"
                                          (Term_Tab.empty : unit Term_Tab.table)

fun get_orientation_schemes () =
  oriented_rules_var |> Synchronized.value
                     |> Term_Tab.dest
                     |> map fst

val schematic_lemmas_var = Synchronized.var "schematic_lemmas"
                                          (Term_Tab.empty : unit Term_Tab.table)

fun get_schematic_lemmas () =
  schematic_lemmas_var |> Synchronized.value
                       |> Term_Tab.dest
                       |> map fst


fun ac_orient ord eq = 
    let
      val (lhs, rhs) = HOLogic.dest_eq eq in
      if ord = Term_Ord.term_ord (lhs, rhs)
      then eq else HOLogic.mk_eq (rhs, lhs)
    end

fun get_rewrites thy cons_name =
  let val simps = safe_eval "" [] (Global_Theory.get_thms thy)
                                  (cons_name ^ ".simps")
  in simps end

fun definitional_dependencies thy (consts : (string * typ) list, term) =
  let val thy_consts = Sign.consts_of thy
      fun dependencies (consts, cname) =
        let val deps = cname |> get_rewrites thy
                             |> map Thm.full_prop_of
                             |> pair consts
                             |> Library.foldl (fn (consts, t) =>
                                 Term.add_const_names t consts)
        in if length consts = length deps 
           then consts
           else Library.foldl dependencies (deps, deps)
        end
  in
    consts |> map fst
           |> Term.add_const_names term
           |> (fn consts => (consts, consts))
           |> Library.foldl dependencies
           |> map (fn cname => (cname, Consts.the_constraint thy_consts cname))
           |> filter (fn (name, _) => name <> Const_Names.meta_forall andalso
                                      name <> Const_Names.meta_imp andalso
                                      name <> Const_Names.meta_eq andalso
                                      name <> Const_Names.hol_trueprop andalso
                                      name <> Const_Names.protectC_name)
  end

fun get_definitional_rewrites thy term =
  ([], term)
    |> definitional_dependencies thy
    |> map fst
    |> maps (get_rewrites thy)

(* Lucas's Heuristic: given a rewrite rule of the form s = t where                        *)
(* f1 and f2 are the function symbols at the top of s and t respectivelly                 *)
(* if f1 != f2 and if f2 is in the dependencies of f1 (or f2 is a constructor) then s = t *)
(* if f1 != f2 and if f1 is in the dependencies of f2 (or f1 is a constructor) then t = s *)
fun definitional_orientation thy term =
    let
      val (s, t) = HOLogic.dest_eq term
      val (f1, f2) = apply2 (fst o Term.strip_comb) (s, t)
      fun obvious_orient (Const _, Abs _) = true
        | obvious_orient (Const _, Var _) = true
        | obvious_orient (Const _, Free _) = true
        | obvious_orient _ = false
      fun is_def_orient (f1, f2) = 
          let val f1_deps = definitional_dependencies thy ([], f1)
              val (n1, n2) = apply2 (fst o Term.dest_Const) (f1, f2)
              val f2_deps = definitional_dependencies thy ([], f2)
          in
            if is_equal (string_ord (n1,n2)) then true
            else (exists (is_equal o string_ord o (pair n2)) (map fst f1_deps)) orelse
                 ((not (null f1_deps)) andalso null f2_deps)
          end
    in is_def_orient (f1, f2) handle TERM _ => (obvious_orient (f1, f2) handle TERM _ => false) end

(*conversion from meta equality to object level equality*)
val my_eq_reflection = @{lemma "x = y ==> x == y"
                               by (rule eq_reflection)}

val mi_meta_eq_to_obj_eq = @{lemma "(x == y) ==> (x=y)"
                                   by (rule meta_eq_to_obj_eq)}

val m_to_o_thm = Thm.equal_intr mi_meta_eq_to_obj_eq my_eq_reflection
val o_to_m_thm = Thm.equal_intr my_eq_reflection mi_meta_eq_to_obj_eq

fun meta_to_obj thm = Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) (Conv.rewr_conv m_to_o_thm)) thm
                      handle CTERM _ => thm

fun obj_to_meta thm = Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) (Conv.rewr_conv o_to_m_thm)) thm
                      handle CTERM _ => thm

val my_eq_commute = obj_to_meta @{thm "HOL.eq_commute"}
fun commute_obj_eq thm = Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) (Conv.arg_conv (Conv.rewr_conv my_eq_commute))) thm
fun commute_meta_eq th = th |> meta_to_obj
                            |> Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of th) (Conv.arg_conv (Conv.rewr_conv my_eq_commute)))
                            |> obj_to_meta

(* obtains the left and right hand sides of a meta-equation *)
fun dest_meta_equation thm = 
    thm |> Thm.cprop_of
        |> Drule.strip_imp_concl
        |> Thm.term_of
        |> Logic.dest_equals

val permutative_rule = permutative_eq o dest_meta_equation

fun dest_object_equation thm = 
    thm |> Thm.cprop_of
        |> Drule.strip_imp_concl
        |> Thm.term_of
        |> HOLogic.dest_eq o HOLogic.dest_Trueprop

fun rhs_is_trivial (_, rhs) =
    is_equal (Term_Ord.term_ord (@{const "True"}, rhs))

fun normalise_term ctxt simps term =
  let val ctxt = ctxt addsimps simps
      val timeOut = Config.get ctxt max_time_normalization
               (*ctxt |> Context.Proof
                      |> Simplifier.map_ss (fn simpset => simpset addsimps simps)
                      |> Context.the_proof*)
  in
  Timeout.apply (Time.fromSeconds timeOut)
      (fn term => 
              term
                |> Thm.cterm_of ctxt
                |> Simplifier.rewrite ctxt
                |> Thm.full_prop_of
                |> snd o Logic.dest_equals
                handle THM _ => term
                     | Timeout.TIMEOUT _ => 
                          let val _ = tracing ("Timeout normalizing: " ^ Syntax.string_of_term ctxt term)
                              val _ = tracing ("With: " ^ str_of_thms simps)
                          in term end) term
  end

fun lhs_in_rhs thy (lhs, rhs) =
  let val (lhs, rhs) = if exists_subterm is_Var lhs orelse
                          exists_subterm is_Var rhs orelse
                          exists_type is_TVar lhs orelse
                          exists_type is_TVar rhs orelse
                          exists_type (exists_subtype is_TVar) lhs orelse
                          exists_type (exists_subtype is_TVar) rhs
                          then apply2 (Logic.unvarify_global o Term_Subst.zero_var_indexes)
                                (lhs, rhs) else (lhs, rhs)
      val pattern = Logic.varify_global lhs
  in rhs |> positions
         |> exists (fn (t, _, _) => Pattern.matches thy (pattern, t)) end

fun top_symbol_constructor thy (lhs, _) = 
  case lhs |> strip_comb
           |> fst of
(*       Const c => is_some (Datatype_Data.info_of_constr thy c)*)
       Const c => is_some (Old_Datatype_Data.info_of_constr thy c)
     | _       => false

fun not_constructor thy t = 
  not (top_symbol_constructor thy (t, @{term "True"}))

(*fun vars_in_rhs_not_in_lhs (lhs, rhs) =
  let val vars_lhs = Term.add_frees lhs []
      val vars_rhs = Term.add_frees rhs []
  in exists (fn v => not (exists (fn v' => v = v') vars_lhs)) vars_rhs end*)

fun vars_in_rhs_not_in_lhs (elhs, erhs) =
  let
    val tvars = Term.add_tvars elhs []
    val vars = Term.add_vars elhs []
    val tfrees = Term.add_tfrees elhs []
    val frees = Term.add_frees elhs []
  in
    erhs |> Term.exists_type (Term.exists_subtype
      (fn TVar v => not (member (op =) tvars v) | _ => false)) orelse
    erhs |> Term.exists_subterm
      (fn Var v => not (member (op =) vars v) | _ => false) orelse
    erhs |> Term.exists_type (Term.exists_subtype
      (fn TFree v => not (member (op =) tfrees v) | _ => false)) orelse
    erhs |> Term.exists_subterm
      (fn Free v => not (member (op =) frees v) | _ => false)
  end

(* f \in Dependencies(lhs) \ {f} *)
fun top_symbol_in_deps thy (s, _) =
  let val f = (fst o Term.strip_comb) s
      val consts = [] |> Term.add_consts s
                      |> filter_out (is_equal o Term_Ord.fast_term_ord o (pair f) o Const)
                      |> map Const
  in exists (fn c => ([], c) |> definitional_dependencies thy
                             |> map Const
                             |> exists (is_equal o Term_Ord.fast_term_ord o (pair f))) consts end

fun bad_equation thy eq =
  (* RHS is True, discard equation*)
  rhs_is_trivial eq orelse
  (* A proper subterm of RHS must not be an instance of LHS *)
  (* This would lead to non-termination *)
  (* Permutative rules are permitted because of ordered rewriting*)
  ((not o permutative_eq) eq andalso
  lhs_in_rhs thy eq) orelse
  (* Top symbols in LHS is a constructor *)
  top_symbol_constructor thy eq orelse
  (* Vars in RHS not present in LHS *)
  vars_in_rhs_not_in_lhs eq orelse
  top_symbol_in_deps thy eq

fun bad_equation' thy eq =
  let val eq' = if can (HOLogic.dest_eq o HOLogic.dest_Trueprop) eq
                then (HOLogic.dest_eq o HOLogic.dest_Trueprop) eq
                else if can HOLogic.dest_eq eq
                then HOLogic.dest_eq eq
                else Logic.dest_equals eq
  in bad_equation thy eq' orelse is_equal (Term_Ord.term_ord (@{prop "True"}, eq))
  end (*handle TERM _ => is_equal (Term_Ord.term_ord (@{prop "True"}, eq))*)

val is_trivial = is_equal o Term_Ord.term_ord o pair @{prop "True"}

fun lhs eq =
  if can HOLogic.dest_eq eq
  then (fst o HOLogic.dest_eq) eq
  else (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop) eq

fun rhs eq =
  if can HOLogic.dest_eq eq
  then (snd o HOLogic.dest_eq) eq
  else (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop) eq

fun match_simps thy term =
  case term |> HOLogic.dest_eq
            |> head_of o fst of
            Const (name, _) => name |> get_rewrites thy
                                    |> map (HOLogic.dest_Trueprop o Thm.full_prop_of)
                                    |> exists (fn pat => can (Pattern.first_order_match thy (pat,term)) (Vartab.empty, Vartab.empty))
          | _ => false

fun user_supplied_orientation thy eq =
  () |> get_orientation_schemes
     |> exists (fn pat => can (Pattern.first_order_match thy (pat,eq)) (Vartab.empty, Vartab.empty))

fun orient_eq thy ord eq =
  if definitional_orientation thy eq then eq
  else if definitional_orientation thy (swap_eq eq) then swap_eq eq
  else if user_supplied_orientation thy eq then eq
  else if user_supplied_orientation thy (swap_eq eq) then swap_eq eq
  else if match_simps thy eq then eq
  else if match_simps thy (swap_eq eq) then swap_eq eq
  else
    let val eq = ac_orient ord eq
    in if not (bad_equation' thy eq) then eq
       else if not (bad_equation' thy (swap_eq eq)) then swap_eq eq
       else ac_orient ord eq
    end

(*fun orient_eq thy ord eq =
  if definitional_orientation thy eq then eq
  else if definitional_orientation thy (swap_eq eq) then swap_eq eq
  else if not (bad_equation' thy eq) then eq
  else if not (bad_equation' thy (swap_eq eq)) then (swap_eq eq)
  else ac_orient ord eq*)

fun orient_rule thy ord thm =
  let val eq = (HOLogic.dest_Trueprop o Thm.concl_of) thm
  in if (is_equal o Term_Ord.term_ord) (eq, orient_eq thy ord eq)
     then thm
     else commute_meta_eq thm
  end

fun orient_meta_rule thy ord =
  obj_to_meta o orient_rule thy ord o meta_to_obj

fun generalizations' thy max_generalizations terms =
  let val terms = filter_out
    (Term.exists_Const (fn (name, _) => name = Const_Names.hol_trueprop orelse
                                        name = Const_Names.meta_forall orelse
                                        name = Const_Names.meta_imp orelse
(*                                        name = Const_Names.hol_eq orelse*)
                                        name = Const_Names.protectC_name)) terms
      fun gen i term =
        if i <= 0 then []
        else
        let val positions = positions term
            val subterms = positions |> map_filter (fn (_, typ, pos) =>
                                            if can dest_funT typ orelse
                                               null pos
                                            then NONE
                                            else SOME (term_at pos term))
                                     |> make_term_set thy
                                     |> filter (Term.exists_Const (fn _ => true))
            val names = Term.add_free_names term []
            val name = singleton (Name.variant_list names) "x"
            fun test s (_, _, pos) = Pattern.equiv thy (s, term_at pos term)
            fun change (t, (_, typ, pos)) = substitute (Free (name, typ), pos) t
            val generalized_terms =
                  subterms |> map (fn s =>
                                    positions |> filter (test s)
                                              |> pair term
                                              |> Library.foldl change)
                           |> make_term_set' thy
        in generalized_terms @ maps (gen (i - 1)) generalized_terms end
    in terms |> maps (gen max_generalizations)
(*             |> map (fn t => if can HOLogic.dest_eq t 
                             then orient_eq thy t
                             else t)*)
             |> make_term_set' thy end

fun generalizations thy max_generalizations terms =
  terms |> maps subterms_no_loose
        |> make_term_set thy
        |> maps ((generalizations' thy max_generalizations) o single)
        |> make_term_set thy

(* Others *)

fun minby _ _ [] = raise ERROR "Empty list"
  | minby ord f (x :: xs) = 
      ((x, f x), xs)
        |> Library.foldl (fn ((m, m'), v) =>
                              let val fv = f v
                              in case ord (fv, m') of
                                  LESS => (v, fv)
                                  | _ => (m,m') end)
        |> fst

fun maxby _ _ [] = raise ERROR "Empty list"
  | maxby ord f (x :: xs) = 
      ((x, f x), xs)
        |> Library.foldl (fn ((m, m'), v) =>
                              let val fv = f v
                              in case ord (fv, m') of
                                  GREATER => (v, fv)
                                  | _ => (m,m') end)
        |> fst

fun next_digit Ln L =
  ((true, []), rev (L ~~ Ln)) 
    |> Library.foldl (fn ((foo, L), (i, i_n)) => 
                         if foo then (
                           if i + 1 < i_n then (false, (i + 1) :: L)
                           else (true, 0 :: L))
                         else (foo, i :: L))
    |> (fn (foo, L) => if foo then NONE
                       else SOME L)

fun binomial_coefficient n k =
    if k < 0 orelse k > n
    then 0
    else 
      let val k = if k > n - k then n - k
                  else k
          val n_k = n - k
          val c = Rat.of_int 1
      in (c, 1 upto k) |> Library.foldl (fn (c, i) => Rat.mult c (Rat.make (n_k + i, i)))
                       |> (fst o Rat.dest)
      end

fun choose set k x =
    let fun maximize a b x =
            if (binomial_coefficient a b) <= x then a
            else maximize (a - 1) b x
        fun iterate n x i = 
            case i of
              0 => []
            | i => let val max = maximize n i x
                   in max :: iterate n (x - (binomial_coefficient max i)) (i - 1) end
    in
      if x < 0 then raise ERROR "x < 0 !!!"
      else
        let val idxs = iterate (length set) x k
        in map (nth set) (sort int_ord idxs)
        end
    end

fun lazy_one_of_each LL =
  if null LL
  then fn () => NONE
  else
    let val sizes = map length LL
        val foo = exists (fn n => n = 0) sizes
        val state = (1 upto (length LL - 1))
                      |> map (fn _ => 0)
                      |> (fn l => l @ [~1])
        val r = Unsynchronized.ref (sizes, state)
    in if foo then (fn () => NONE)
       else (fn () => case next_digit (fst (!r)) (snd (!r)) of
                        SOME state => (r := (sizes, state); SOME (map List.nth (LL ~~ state)))
                      | NONE => NONE) end

fun synchronized_lazy_one_of_each LL =
    let val sizes = map length LL
        val foo = exists (fn n => n = 0) sizes
        val state = (1 upto (length LL - 1))
                      |> map (fn _ => 0)
                      |> (fn l => l @ [~1])
        val r = Synchronized.var "Synchronized reference" (sizes, state)
    in if foo then (fn () => NONE)
       else (fn () => let val result = Unsynchronized.ref NONE
                      in (Synchronized.change r (fn r' =>
                                                    case next_digit (fst r') (snd r') of
                                                      SOME state => (result := SOME (map List.nth (LL ~~ state)); (sizes, state))
                                                    | NONE => r'); !result)
                      end)
    end

fun from_to (a, b) = 
  let fun next i = Seq.make(fn () => if i <= b then SOME (i, next (i + 1)) else NONE)
  in next a end

fun lazy_subsets set =
  let val n = length set
      val n_list = Seq.map (fn k => (k, binomial_coefficient n k)) (from_to (0,n))
  in n_list |> Seq.maps (fn (k, binomial) => from_to (0, binomial - 1)
                                                |> Seq.map (fn kk => choose set k kk))
  end

fun lazy_subsets_of_size i set =
  let val n = length set
      val binomial = binomial_coefficient n i
  in from_to (0, binomial - 1)
        |> Seq.map (fn kk => choose set i kk)
  end

(* Since we need to find an ordering for a set of n Consts  *)
(* the evaluation of the factorial seems appropriate.       *)
fun factorial n = let
     fun lp (0, acc) = acc
       | lp (m, acc) = lp (m-1, m*acc)
     in
       lp (n, 1)
     end

(* useful for geting the i-th permutation of n elements *)
local
  fun rr (0, _) = []
    | rr (n, k) = k mod n :: rr (n-1, k div n)
  val dfr = List.foldr (fn (x, rs) => x :: map (fn r => r + (if x <= r then 1 else 0)) rs) []
in
fun perm (xs, k) = map (fn i => List.nth (xs, i)) (dfr (rr (length xs, k)))
end

(* Return all permutations of a list of elements *)
fun all_permutations l = 
    let val n = factorial (length l) - 1
    in if n < 0 then Seq.empty
       else (0, n) |> from_to
                   |> Seq.map (fn k => perm (l, k))
    end

(* Return K selections of a set l (Binomial Coefficient) *)
fun arrangements i s =
      (0, binomial_coefficient (length s) i - 1)
      |> from_to
      |> Seq.maps (all_permutations o choose s i)

(* Fixpoint techniques to count terms *)

fun dfs stack goal successors =
  let fun bfs_aux stack =
        case stack of
          state :: stack => if goal state
                            then SOME (state, stack)
                            else state |> successors
                                       |> (fn new => new @ stack)
                                       |> bfs_aux
       | [] => NONE
  in bfs_aux stack end

fun dfs' stack goal succesors =
  let fun next stack = 
          Seq.make(fn () => 
              case dfs stack goal succesors of
                SOME (state, stack) => SOME (state, next stack)
                | NONE => NONE)
  in next stack end

(* Fixpoint techniques to count terms *)

(*  (op @) (e, [x1, ..., xn])  ===>  ((e @ x1) @ x2) ... @ xn
    for operators that associate to the left (TAIL RECURSIVE)*)
fun foldl_seq (f: 'a * 'b -> 'a) : 'a * 'b Seq.seq -> 'a =
  let fun itl (e, seq) = 
              case Seq.pull seq of
                SOME (a, seq) => itl (f(e, a), seq)
              | NONE => e
  in itl end

fun random () = 
  (Random.random () / Random.random ())
    |> (fn r => if r < 1.0 then r else 1.0 / r)

fun weighted_choose (L : ('a * int) list) =
    let val choosen = L |> map snd
                        |> pair 0
                        |> Library.foldl (fn (x, y) => x + y)
                        |> (fn x => x - 1)
                        |> (fn x => if null L
                                    then raise ERROR "Null list"
                                    else if x < 0
                                    then raise ERROR "Weights sum 0 or less"
                                    else Random.random_range 0 x)
        fun fld L i =
          case L of
            (x, w) :: L =>
                let val i = i + w
                in if choosen < i then x
                   else fld L i
                end
            | _ => raise ERROR "Should not fail 51"
    in fld L 0 end

(*fun parse p input = Scan.finite Token.stopper (Scan.error p) input*)

local
  (*val method = parse Method.parse "induct_auto" |> fst*)
  fun filtered_input ctxt str = 
      let val keywords = Thy_Header.get_keywords' ctxt
      in str |> Token.explode keywords Position.start
             |> filter Token.is_proper
      end
in
fun parse ctxt p input = Scan.finite Token.stopper (Scan.error p) (filtered_input ctxt input)
end

fun timing_wrapper tac st =
let
  val t_start = Timing.start ()
  val res = tac st
  val t_end = Timing.result t_start
in
  (writeln (Timing.message t_end); res)
end

fun timing_wrapper' check msg tac st =
let
  val (timing, res) = Timing.timing tac st
in
  if check timing
  then (tracing (msg ()); writeln (Timing.message timing); res)
  else res
end

(* This function only makes sense on stochastic functions *)
  fun repeat_until prop f x =
    let val v = f x
    in if prop v
       then v
       else repeat_until prop f x
    end

fun trim str =
    if can (unsuffix " ") str
    then (let val u = unsuffix " " str
          in if can (unprefix " ") u
             then trim (unprefix " " u)
             else trim u
          end)
    else (if can (unprefix " ") str
         then trim (unprefix " " str)
         else str)

fun numeral_of_int ctxt i =
  Syntax.read_term ctxt (string_of_int i ^ "::int")

fun numeral_of_nat ctxt i =
  Syntax.read_term ctxt (string_of_int i ^ "::nat")

  fun int_of_string s =
  let
    val ss = space_explode " " s
  in case ss of
      [s] => fst (s |> (map Char.toString) o String.explode
                    |> read_int)
    | [_, s] => ~(fst (s |> (map Char.toString) o String.explode
                         |> read_int))
    | _ => (tracing s; raise ERROR "Malformed numeral!")
  end

  fun int_of_numeral t =
  let
    val s = string_of_term @{context} t
    val ss = space_explode " " s
  in case ss of
      [s] => fst (s |> (map Char.toString) o String.explode
                    |> read_int)
    | [_, s] => ~(fst (s |> (map Char.toString) o String.explode
                         |> read_int))
    | _ => (tracing (Syntax.string_of_term @{context} t); raise ERROR "Malformed numeral!")
  end

  fun factor_of_numeral (t as (Const (pc, _) $ n) $ m) =
    if pc = Const_Names.power_class
    then
    let val n = int_of_numeral n
        val m = int_of_numeral m
    in Library.foldl (fn (r, _) => r * n) (1, 1 upto m) end
    else int_of_numeral t
    | factor_of_numeral t = int_of_numeral t

  fun rat_of_numeral t =
  let
    val s = string_of_term @{context} t
    val ss = space_explode " " s
  in case ss of
      [s] => s |> (map Char.toString) o String.explode
               |> read_int
               |> fst
               |> Rat.of_int
    | [_, s] => (s |> (map Char.toString) o String.explode
                   |> read_int
                   |> fst
                   |> (fn x => ~ x)
                   |> Rat.of_int)
    | _ => (case t of
            (_ $ p $ q) => Rat.make (int_of_numeral p, factor_of_numeral q)
          | _ => (tracing (Syntax.string_of_term @{context} t); raise ERROR "Malformed numeral!"))
  end

  fun elements_of_list (w as (Const (c, _) $ e $ t)) =
    if c = Const_Names.list_cons
    then e :: elements_of_list t
    else (tracing (Syntax.string_of_term @{context} w); raise ERROR "Malformed list!")
    | elements_of_list (w as (Const (n, _))) =
      if n = Const_Names.list_nil
      then []
      else (tracing (Syntax.string_of_term @{context} w); raise ERROR "Malformed list!")
    | elements_of_list t = (tracing (Syntax.string_of_term @{context} t); raise ERROR "Malformed list!")

  fun elements_of_product_type (w as (Const (c, _) $ e $ t)) =
    if c = Const_Names.product_type
    then e :: elements_of_product_type t
    else (tracing (Syntax.string_of_term @{context} w); raise ERROR "Malformed list!")
    | elements_of_product_type w = [w]

(*  fun int_of_numeral t =
    let fun sign (Const (m, ty) $ t) = if m = Const_Names.Minus
                                       then (~1, t)
                                       else (1, Const (m, ty) $ t)
          | sign (Const c) = (1, Const c)
          | sign _ = raise ERROR "Malformed Numeral"
        fun numeral p (B $ t) =
           (case B of
              Const (b, _) => if b = Const_Names.Bit0
                              then numeral (2*p) t
                              else if b = Const_Names.Numeral
                              then numeral p t
                              else p + numeral (2*p) t
            | _ => raise ERROR "Malformed Numeral")
          | numeral p (Const (b, _)) = if b = Const_Names.One orelse b = Const_Names.One_class
                                       then p
                                       else if b = Const_Names.Zero_class
                                       then 0
                                       else raise ERROR "Malformed Numeral"
          | numeral _ _ = raise ERROR "Malformed Numeral"
        val (p, t) = sign t
    in numeral p t end*)

local

structure VarMap = Table(
type key = string * int
val ord  = prod_ord string_ord int_ord)

structure ConstMap = Table(
type key = string
val ord  = string_ord)

structure PosMap = Table(
type key = int
val ord  = int_ord)

fun add_turn var_map t i var =
    case t of
      Const (n, _) => 
      (case VarMap.lookup var_map var of
         SOME const_map => (case ConstMap.lookup const_map n of
                              SOME pos_map => (case PosMap.lookup pos_map i of
                                                 SOME v => VarMap.update (var, ConstMap.update (n, PosMap.update (i, v + 1) pos_map) const_map) var_map
                                               | NONE => VarMap.update (var, ConstMap.update (n, PosMap.update (i, 1) pos_map) const_map) var_map)
                            | NONE => VarMap.update (var, ConstMap.update (n, PosMap.update (i, 1) PosMap.empty) const_map) var_map)
       | NONE => VarMap.update (var, ConstMap.update (n, PosMap.update (i, 1) PosMap.empty) ConstMap.empty) var_map)
    | _ => var_map

fun variable_vector var_map t (var, (i :: Pos)) =
    (case t of
       Abs (_, _, t) => variable_vector var_map t (var, Pos)
     | t => let val (h, args) = Term.strip_comb t
                val var_map = add_turn var_map h i var
            in
              args |> (fn l => nth l i)
                   |> (fn t => variable_vector var_map t (var, Pos))
            end)
  | variable_vector var_map _ (_, []) = var_map

fun difference_vectors var_map1 var_map2 =
    var_map2 |> VarMap.dest
             |> maps (fn (var, const_map2) =>
                         case VarMap.lookup var_map1 var of
                           SOME const_map1 => const_map2 |> ConstMap.dest
                                                         |> maps (fn (n, pos_map2) =>
                                                                     case ConstMap.lookup const_map1 n of
                                                                       SOME pos_map1 => pos_map2 |> PosMap.dest
                                                                                                 |> map (fn (i, v) =>
                                                                                                            case PosMap.lookup pos_map1 i of
                                                                                                              SOME v' => let val d = v - v'
                                                                                                                         in d * d end
                                                                                                            | NONE => v * v)
                                                                     | NONE => pos_map2 |> PosMap.dest
                                                                                        |> map (fn (_, v) => v * v))
                         | NONE => const_map2 |> ConstMap.dest
                                              |> maps (fn (_, pos_map2) =>
                                                         pos_map2 |> PosMap.dest
                                                                  |> map (fn (_, v) => v * v)))
             |> pair 0
             |> Library.foldl (op +)

in
fun variable_differences_raw (l, r) =
    let (*val (l, r) = dest_equation th*)
        val pos_l = positions l
        val pos_r = positions r
        val vec_l = pos_l |> map_filter (fn (_, _, pos) => 
                                            let val t = term_at pos l 
                                            in if is_Var t 
                                               then SOME ((fst o dest_Var) t, pos) 
                                               else NONE end)
                          |> pair VarMap.empty
                          |> Library.foldl (fn (var_map, vp) => variable_vector var_map l vp)
        val vec_r = pos_r |> map_filter (fn (_, _, pos) => 
                                            let val t = term_at pos r
                                            in if is_Var t
                                               then SOME ((fst o dest_Var) t, pos)
                                               else NONE end)
                          |> pair VarMap.empty
                          |> Library.foldl (fn (var_map, vp) => variable_vector var_map r vp)
    in difference_vectors vec_l vec_r end

val variable_differences = variable_differences_raw o dest_meta_equation

fun order_ints_raw t =
    let val n_vars = length (Term.add_vars t [])
        val diffs = (variable_differences_raw o HOLogic.dest_eq) t handle TERM _ => 0
    in [Term.size_of_term t, ~n_vars, diffs] end

val rule_int_ord = order_ints_raw o Thm.concl_of
end

fun sort_by_general thy terms =
  let fun ord (s, t) =
        case (Pattern.matches thy (s, t), Pattern.matches thy (t, s)) of
          (false, true) => GREATER
        | (true, false) => LESS
        | _ => (list_ord int_ord o apply2 order_ints_raw) (s,t)
(*        | _ => (int_ord o (apply2 size_of_term)) (s, t)*)
  in terms |> map_index (fn (i, t) => t |> Logic.varify_global
                                        |> Logic.incr_indexes ([], [], i))
           |> sort ord
           |> map (Logic.unvarify_global o Term_Subst.zero_var_indexes)
  end

fun sort_by_general' thy by terms =
  let fun ord (s, t) =
        case (Pattern.matches thy (s, t), Pattern.matches thy (t, s)) of
          (false, true) => GREATER
        | (true, false) => LESS
        | _ => (list_ord int_ord o apply2 order_ints_raw) (s,t)
(*        | _ => (int_ord o (apply2 size_of_term)) (s, t)*)
  in terms |> map_index (fn (i, t) => (t, t |> by
                                            |> Logic.varify_global
                                            |> Logic.incr_indexes ([], [], i)))
           |> sort (ord o apply2 snd)
           |> map fst
  end

fun str_of_terms ctxt terms =
  terms |> map (string_of_term ctxt)
        |> commas

fun pretty_helper aux env =
  env |> Vartab.dest
      |> map aux
      |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
      |> Pretty.enum "," "[" "]"
      |> Pretty.writeln

fun pretty_tyenv ctxt tyenv =
let
  fun get_typs (v, (s, T)) = (TVar (v, s), T)
  val print = apply2 (Syntax.pretty_typ ctxt)
in
  pretty_helper (print o get_typs) tyenv
end

fun pretty_env ctxt env =
let
  fun get_trms (v, (T, t)) = (Var (v, T), t)
  val print = apply2 (Syntax.pretty_term ctxt)
in
  pretty_helper (print o get_trms) env
end

local 
  fun pretty_cterm ctxt ctrm =
    Syntax.pretty_term ctxt ctrm

  fun pretty_cterms ctxt ctrms =
    Pretty.block (Pretty.commas (map (pretty_cterm ctxt) ctrms))

  fun pretty_thm_no_vars ctxt thm =
  let
    val ctxt' = Config.put show_question_marks false ctxt
  in
    Syntax.pretty_term ctxt' (Thm.prop_of thm)
  end
in
fun print_ss ctxt =
let
  val ss = simpset_of ctxt
  val {simps, congs, procs, ...} = Raw_Simplifier.dest_ss ss
  fun name_sthm (nm, thm) =
    Pretty.enclose (nm ^ ": ") "" [pretty_thm_no_vars ctxt thm]
  fun name_cthm ((_, nm), thm) =
    Pretty.enclose (nm ^ ": ") "" [pretty_thm_no_vars ctxt thm]
  fun name_ctrm (nm, ctrm) =
    Pretty.enclose (nm ^ ": ") "" [pretty_cterms ctxt ctrm]
  val pps = [Pretty.big_list "Simplification rules:" (map name_sthm simps),
             Pretty.big_list "Congruences rules:" (map name_cthm congs),
             Pretty.big_list "Simproc patterns:" (map name_ctrm procs)]
  in
    pps |> Pretty.chunks
        |> Pretty.writeln
  end

end

fun rules_in_simpset ts =
    let val const_names = Library.foldl (fn (ns, t) => Term.add_const_names t ns) ([], ts)
        val set = Str_Tab.make_set const_names
        val simps = (dest_ss (simpset_of @{context}))
                      |> (map snd) o #simps
    in simps
         |> filter (fn thm => thm |> Thm.concl_of
                                  |> fst o Logic.dest_equals
                                  |> fst o strip_comb
                                  |> (fn t => Term.add_const_names t [])
                                  |> exists (Str_Tab.defined set))
    end


(* Antiquotation parsing metavariables *)
val typ_pat_setup = 
    let
      val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
      fun typ_pat (ctxt, str) = 
        let val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
        in str |> Syntax.read_typ ctxt'
               |> ML_Syntax.print_typ
               |> ML_Syntax.atomic
        end
    in
      ML_Antiquotation.inline @{binding "typ_pat"} (parser >> typ_pat)
    end

val _ = Context.>> (Context.map_theory typ_pat_setup)

val term_pat_setup =
let
  val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
  fun term_pat (ctxt, str) =
     str |> Proof_Context.read_term_pattern ctxt
         |> ML_Syntax.print_term
         |> ML_Syntax.atomic
in
  ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
end

val _ = Context.>> (Context.map_theory term_pat_setup)

end

structure Utils : UTILS = DB_Utils

fun global_lemmas ctxt term = 
  let val thy = Proof_Context.theory_of ctxt
      val consts = ([], term)
                  |> Utils.definitional_dependencies thy
                  |> map fst
      val simps = maps (Utils.get_rewrites thy) consts
  in consts
      |> (fn consts =>
            let val completed = Completion_Rules.get ctxt
                val lemmas = filter ((Term.exists_Const (fn (s, _) => exists (fn c => c = s) consts))
                                       o Thm.full_prop_of) completed
            in simps @ lemmas end)
      |> Utils.make_theorem_set
  end

fun global_simps ctxt term = 
  let val thy = Proof_Context.theory_of ctxt
      val consts = ([], term)
                  |> Utils.definitional_dependencies thy
                  |> map fst
  in consts
      |> (fn consts =>
            let val completed = Completion_Rules.get ctxt
                val lemmas = filter ((Term.exists_Const (fn (s, _) => exists (fn c => c = s) consts))
                                       o Thm.full_prop_of) completed
            in lemmas end)
      |> Utils.make_theorem_set
  end

