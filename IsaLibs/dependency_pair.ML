(*  Title:      src/dependency_pair.ML
    ID:         $Id: dependency_pair.ML,v 2.010 2013/01/11 10:32:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   Universidad Politecnica de San Luis Potosi.

Dependency pairs.
*)

signature DPAIR =
sig
  val max_time_in_termination        : int Config.T

  val terminates : Proof.context -> thm list -> bool
end

structure DB_DPair
(* : DPair *)
= struct

val (max_time_in_termination, setup_max_time_in_termination) = Attrib.config_int @{binding "max_time_in_termination"} (K 180)

exception Complexity of term list

fun fold_subterms f (t $ u) a = 
    (* Simulate higher-order terms *)
    (* fold_subterms f t (fold_subterms f u (f (t $ u) a)) *)
    (* Simulate first-order terms *)
    let val (_, arguments) = Term.strip_comb (t $ u)
    in
      Library.foldl (fn (ps, term) => fold_subterms f term ps) (f (t $ u) a ,arguments)
    end
  | fold_subterms f (Abs (_, _, t)) a = fold_subterms f t a
  | fold_subterms f t b = f t b

(* Renames top symbol of term adding # followed by a suffix *)
fun rename_top suffix t = 
    let 
      val (h, hs) = strip_comb t
    in
      case h of Const (name, T) => list_comb (Const (name ^ "#" ^ suffix, T), hs)
              | _ => t
    end

fun dependency_pairs TRS = 
    let
      val sides = TRS |> map Utils.dest_meta_equation
      val defined = sides |> map (Term.head_of o fst)
      fun pairs (l,r) = fold_subterms (fn t => fn ps => 
                                                  let
                                                    val head = Term.head_of t
                                                  in if exists (fn Const (name, _) => 
                                                                   (case head of 
                                                                      Const (name', _) => name = name'
                                                                    | _ => false)
                                                                 | _ => false) defined
                                                     then apply2 (rename_top "DP") (l, t) :: ps
                                                     else ps 
                                                  end) r []
    in maps pairs sides end


fun afs thy (Const (name, typ)) =
    let
      val (hstyps, htyp) = Term.strip_type typ
      val typs = rev hstyps
      val projections = Library.foldl 
                          (fn (lp, (i, typ)) =>
                              (let val tyenv = fst (Sign.typ_unify thy (typ, htyp) (Vartab.empty, 0))
                               in
                                 tyenv |> Envir.norm_type
                                       |> (fn f => ((Bound i, []), map f typs))
                                       |> Library.foldl (fn ((t, vars), typ) => 
                                                            let val v = singleton (Name.variant_list vars) "x"
                                                            in (absfree (v, typ) t, v :: vars) end)
                                       |> fst
                                       |> (fn t => (Const (name, Envir.norm_type tyenv typ), t) :: lp)
                               end) handle Type.TUNIFY => lp) ([], map_index I typs)
      fun meta_projections ps i = if i > 0 then
                                    typs |> map_index I
                                         |> Utils.arrangements i
                                         |> pair ps
                                         |> Utils.foldl_seq
                                         (fn (ps, args) =>
                                             let
                                               val typ' = (map snd args) ---> htyp
                                               (*val _ = tracing (Syntax.string_of_typ_global thy typ')*)
                                               val c' = rename_top "AFS" (Const (name, typ'))
                                               val t = list_comb (c', map (Bound o fst) args)
                                               val t_abs = ((t, []), typs)
                                                             |> Library.foldl (fn ((t, vars), typ) => 
                                                                                  let val v = singleton (Name.variant_list vars) "x"
                                                                                  in (absfree (v, typ) t, v :: vars) end)
                                                             |> fst
                                             in (Const (name, typ), t_abs) :: ps end)
                                         |> (fn ps => meta_projections ps (i - 1))
                                  else ps
    in
      projections @ meta_projections [] (length typs)
    end
  | afs _ _ = []

fun argument_filtering thy TRS = 
    let
      val consts = TRS |> map Utils.dest_meta_equation
                       |> pair []
                       |> Library.foldl (fn (cs, (c1, c2)) =>
                                            cs |> Term.add_consts c1
                                               |> Term.add_consts c2)
                       |> map Const
                       |> pair Net.empty
                       |> Library.foldl (fn (net,c) =>
                                            (* a more general constant is present in net *)
                                            if c |> Net.unify_term net
                                                 |> get_first (fn c' => if Pattern.matches thy (c',c) 
                                                                        then SOME c'
                                                                        else NONE)
                                                 |> is_some
                                            then net
                                            else if 
                                                (* a more specific constant is present in net *)
                                                c |> Net.unify_term net
                                                  |> get_first (fn c' => if Pattern.matches thy (c,c')
                                                                         then SOME c'
                                                                         else NONE)
                                                  |> is_some
                                              then net |> Net.delete_term_safe (fn (c,c') => Pattern.matches thy (c,c') orelse
                                                                                             Pattern.matches thy (c',c)) (c,c)
                                                       |> Net.insert_term_safe (fn (c,c') => Pattern.matches thy (c,c') orelse
                                                                                             Pattern.matches thy (c',c)) (c,c)
                                              (* New constant *)
                                              else Net.insert_term_safe (fn (c,c') => Pattern.matches thy (c,c') orelse
                                                                                      Pattern.matches thy (c',c)) (c,c) net)
                       |> Net.content
      val AFSs = consts |> map (afs thy)
                        (* First AFS does not contain rewrite rules *)
                        |> map (fn L => (@{term "True"}, @{term "True"}) :: L)
    in if null TRS then (fn _ => NONE)
       else Utils.lazy_one_of_each AFSs end

fun safe_b X t =
    let val body = strip_abs_body t
        val (head, args) = strip_comb body
        fun dest_all_abs (Abs T) = dest_all_abs (snd (Term.dest_abs T))
          | dest_all_abs t = t
        val body_with_frees = dest_all_abs t
    in 
      if exists (fn t => (is_equal o Term_Ord.term_ord) (t, head)) X
      then [body_with_frees]
      else distinct (is_equal o (fn tms => if Term.aconv tms then EQUAL else Term_Ord.term_ord tms)) ([body_with_frees] @ maps (safe_b X) args)
    end

fun safe l =
    let val (_, args) = strip_comb l
        val vars = [] |> Term.add_vars l
                      |> map Var
(*        val set = TSet.fromList vars*)
    in args |> maps (safe_b vars)
            |> filter_out (fn t => 
                              let val vs = [] |> Term.add_vars t
                                              |> map Var
(*                                  val set' = TSet.fromList vs*)
                              in
                                not (subset  (is_equal o Term_Ord.term_ord) (vs, vars)) orelse
                                Term.exists_subterm (fn Free _ => true | _ => false) t
                              end)
            |> (fn ts => args @ ts)
            |> distinct (is_equal o (fn tms => if Term.aconv tms then EQUAL else Term_Ord.term_ord tms))
    end

fun subterms (Abs (x, T, s)) = distinct (is_equal o (fn tms => if Term.aconv tms then EQUAL else Term_Ord.term_ord tms)) ((Abs (x, T, s)) :: subterms s)
  | subterms (t as _ $ _) = 
    t |> strip_comb
      |> snd
      |> maps subterms
      |> (fn ts => t :: ts)
      |> distinct (is_equal o (fn tms => if Term.aconv tms then EQUAL else Term_Ord.term_ord tms))
  | subterms t = single t

fun eta_long u = the_default u (try (fn u => (*Pattern.eta_long*)Envir.eta_long (snd (dest_Type (type_of u))) u) u)

fun plain_function_passing ctxt R =
    let val (l, r) = Utils.dest_meta_equation R
        (*val _ = tracing ("l = " ^ Syntax.string_of_term ctxt l)
        val _ = tracing ("r = " ^ Syntax.string_of_term ctxt r)*)
        val safe_l = l |> safe
                       (*|> tap (fn _ => tracing "Safe:")
                       |> tap (fn l => l |> map (Syntax.string_of_term ctxt)
                                         |> space_implode ", "
                                         |> tracing)*)
                       |> map eta_long
(*                       |> TSet.fromList*)
        val subterms_r = r |> subterms
                           |> filter (is_Var o head_of)
                           |> filter_out (fn t => loose_bvar (t, 0))
        (*val _ = subterms_r |> map (Syntax.string_of_term ctxt)
                           |> tap (fn _ => tracing "Subterms:")
                           |> space_implode ", "
                           |> tracing*)
        fun check (u as s $ _) = 
            let val u = eta_long u
            in member (is_equal o (fn tms => if Term.aconv tms then EQUAL else Term_Ord.term_ord tms)) safe_l u orelse check s end
          | check u = 
            let val u = eta_long u
            in member (is_equal o (fn tms => if Term.aconv tms then EQUAL else Term_Ord.term_ord tms)) safe_l u end
        val foo = forall check subterms_r
(*        val _ = if not foo
                then tracing ("Not plain function passing: " ^ Syntax.string_of_term ctxt (Thm.full_prop_of R))
                else ()*)
    in foo end

fun plain_function_passing_hrs ctxt TRS = forall (plain_function_passing ctxt) TRS

fun candidate_terms t = 
    let val (vars, body) = strip_abs t
        val vars = rev vars
        val (_, args) = strip_comb body
        fun build ((x, T) :: ts) t = build ts (Abs (x, T, t))
          | build [] t = t
    in args |> maps (candidate_terms o (build vars))
            |> (fn l => t :: l)
            |> distinct (is_equal o (fn tms => if Term.aconv tms then EQUAL else Term_Ord.term_ord tms))
    end

fun prints ctxt prefix ts = 
    ts |> map (Syntax.string_of_term ctxt)
       |> space_implode ", "
       |> (fn txt => tracing (prefix ^ txt))

fun static_dependency_pairs DefinedSymbols R =
    let val (l, r) = Utils.dest_meta_equation R
        val cand_terms = candidate_terms r
        val safe_l = l |> safe
(*                       |> TSet.fromList*)
        fun dest_all_abs (Abs T) = dest_all_abs (snd (Term.dest_abs T))
          | dest_all_abs t = Logic.varify_global t
    in cand_terms |> filter_out (fn t => member (is_equal o (fn tms => if Term.aconv tms then EQUAL else Term_Ord.term_ord tms)) safe_l (eta_long t))
                  |> filter (fn t => t |> strip_abs_body
                                       |> strip_comb
                                       |> fst
                                       |> (fn Const (head, _) => exists (fn Const (n, _) => head = n
                                                                          | _ => false) DefinedSymbols
                                            | _ => false))
                  |> map Logic.unvarify_global
                  |> map dest_all_abs
                  |> map (pair l)
    end

type vertex = term * term
(*type vertex = string*)
datatype color = WHITE | BLACK

(* a map from vertex to (adjacencies * (color * int)) *)
structure DependencyGraph = Table(
  type key = vertex
  val ord = prod_ord Term_Ord.term_ord Term_Ord.term_ord)

fun all_pairs R (h1 :: l1) l2 =
    all_pairs (R @ map (fn e => (h1, e)) l2) l1 l2
  | all_pairs R [] _ = R


fun static_dependency_graph pairs =
    pairs |> all_pairs [] pairs
          |> pair DependencyGraph.empty
          |> Library.foldl (fn (g, ((u, v), (u', v'))) => 
                           case (Term.head_of v, Term.head_of u') of
                             (Const (n1, _), Const (n2, _)) => 
                             if n1 = n2 then 
                               case DependencyGraph.lookup g (u, v) of
                                 SOME adj_list => DependencyGraph.update ((u, v), (u', v') :: adj_list) g
                               | NONE => DependencyGraph.update ((u, v), [(u', v')]) g
                             else g
                           | _ => g)
          |> DependencyGraph.dest

fun transpose vertices_adyacencies_whatever =
    (DependencyGraph.empty, vertices_adyacencies_whatever)
      |> Library.foldl (fn (g, (v, adj_list, _)) =>
                           Library.foldl (fn (g, u) =>
                                             case DependencyGraph.lookup g u of
                                               SOME adj_list => DependencyGraph.update (u, v :: adj_list) g
                                             | NONE => DependencyGraph.update (u, [v]) g) (g, adj_list))
      |> pair DependencyGraph.empty
      |> rpair vertices_adyacencies_whatever
      |> Library.foldl (fn ((gf, g), (v, _, W)) =>
                           case DependencyGraph.lookup g v of
                             SOME adj_list => (DependencyGraph.update (v, (adj_list, W)) gf, g)
                           | NONE => (DependencyGraph.update (v, ([], W)) gf, g))
      |> fst
      |> DependencyGraph.dest
      |> split_list

fun dfs_visit time g v adj_list =
    let val _ = time := !time + 1
        val d = !time
    in
      adj_list
        |> pair (DependencyGraph.update (v, (adj_list, (d, 0), BLACK)) g)
        |> Library.foldl
        (fn (g, v) =>
            case DependencyGraph.lookup g v of
              SOME (adj_list, _, color) =>
              (case color of
                 WHITE => dfs_visit time g v adj_list
               | BLACK => g)
            | NONE => g)
        |> tap (fn _ => time := !time + 1)
        |> (fn g => DependencyGraph.update (v, (adj_list, (d, !time), BLACK)) g)
    end

fun dfs vertices_adyacencies = 
    let val g = Library.foldl 
                  (fn (g, (v,adj_list)) => 
                      DependencyGraph.update (v, (adj_list, (0, 0), WHITE)) g)
                  (DependencyGraph.empty, vertices_adyacencies)
        val time = Unsynchronized.ref 0
    in
      vertices_adyacencies
        |> pair g
        |> Library.foldl (fn (g, (v,_)) => 
                             case DependencyGraph.lookup g v of
                               SOME (adj_list, _, color) => 
                               (case color of
                                 WHITE => dfs_visit time g v adj_list
                               | BLACK => g)
                               | NONE => raise ERROR "DFS")
        |> DependencyGraph.dest
        |> map (fn (v, (adj_list, P, _)) => (v, adj_list, P))
    end

fun strongly_connected_components vertices_adyacencies =
    vertices_adyacencies
      |> dfs
      |> transpose
      |> (fn P => (op ~~) P handle ListPair.UnequalLengths => (tracing "DPair 329"; raise ListPair.UnequalLengths))
      |> sort (fn ((_ , (_, (_, f1))), (_, (_, (_, f2)))) => int_ord (f1, f2))
      |> rev
      |> map (fn (v, (adj_list, _)) => (v, adj_list))
      |> dfs
      |> sort (fn ((_ , _, (d1, _)), (_, _, (d2, _))) => int_ord (d1, d2))
      |> pair ([], 0)
      |> Library.foldl (fn ((H :: Strg, i), (v, adj_list, (d, f))) =>
                           if i > d then (((v, adj_list) :: H) :: Strg, i)
                           else ([(v, adj_list)] :: H :: Strg, f)
                         | (([], _), (v, adj_list, (_, f))) => ([[(v, adj_list)]], f))
      |> fst
      |> map_filter (fn H => case H of
                              [(u, adj_list_u)] => 
                              (if exists (is_equal o 
                                          (prod_ord Term_Ord.term_ord Term_Ord.term_ord) o 
                                          (pair u)) adj_list_u
                               then SOME [u]
                               else NONE)
                            | _ => SOME (map fst H))
(*      |> maps (tl o Utils.subsets)*)
        |> map (Seq.tl o Utils.lazy_subsets)
        |> pair Seq.empty
        |> Library.foldl (fn (a, b) => Seq.append a b)
(*      |> Seq.maps (Seq.tl o Utils.lazy_subsets)*)


fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip _ [] = []
  | zip [] _ = []


structure PISet = Table(
type key = string * int list
val ord  = prod_ord string_ord (list_ord int_ord))

structure PosSet = Table(
type key = int list
val ord  = list_ord int_ord)

structure PIMap = Table(
type key = string
val ord  = string_ord)

fun term_positions Pos (Abs (_, _, t)) = Pos :: term_positions (Pos @ [0]) t
  | term_positions Pos t =
    t |> (snd o Term.strip_comb)
      |> map_index (fn (i, ti) => term_positions (Pos @ [i]) ti)
      |> flat
      |> (fn L => Pos :: L)

fun term_at (i :: Pos) t =
    (case t of
       Abs (_, _, t) => term_at Pos t
     | t => t |> Term.strip_comb
              |> snd
              |> (fn l => nth l i)
              |> term_at Pos)
  | term_at [] t = t

fun test_property P pos_u pos_v (u, v) : bool =
    let val u_at_pos = term_at pos_u u
        val v_at_pos = term_at pos_v v
    in
      P (u_at_pos, v_at_pos)
    end

fun make_set update empty list =
  Library.foldl (fn (set, e) => update (e, ()) set) (empty, list)

fun subterm_positions P (u, v) =
    let val symbol_u = (fst o Term.dest_Const o fst o Term.strip_comb) u handle TERM msg => (tracing "439"; raise TERM msg)
        val symbol_v = (fst o Term.dest_Const o fst o Term.strip_comb) v handle TERM msg => (tracing "440"; raise TERM msg)
        val positions_u = term_positions [] u
        val same_symbol = symbol_u = symbol_v
        val positions_v = if same_symbol
                          then inter (is_equal o list_ord int_ord) positions_u (term_positions [] v)
                          else term_positions [] v
    in
      if same_symbol then
        ([], positions_v)
          |> Library.foldl (fn (L, pos) =>
                               if test_property P pos pos (u, v)
                               then pos :: L
                               else L)
          |> make_set PosSet.update PosSet.empty
          |> (fn set => ((symbol_u, set), (symbol_v, set)))
      else
        (([],[]), positions_u)
          |> Library.foldl (fn ((L1,L2), pos_u) =>
                               ((L1,L2), positions_v)
                                 |> Library.foldl (fn (_, pos_v) =>
                                                      if test_property P pos_u pos_v (u, v)
                                                      then (pos_u :: L1, pos_v :: L2)
                                                      else (L1,L2)))
          |> apply2 (make_set PosSet.update PosSet.empty)
          |> (fn (set_u, set_v) => ((symbol_u, set_u), (symbol_v, set_v)))
    end

fun not_free_variable t [_] = (not o Term.is_Var o Term.head_of) t
  | not_free_variable t (i :: Pos) =
    (case t of
       Abs (_, _, t) => not_free_variable t Pos
     | t => t |> Term.strip_comb
              |> (fn (h, args) => (not o Term.is_Var) h andalso
                                  args |> (fn l => nth l i)
                                       |> (fn t => not_free_variable t Pos)))
  | not_free_variable _ [] = true

fun not_free_variable_defined D t [_] =
    let val h = Term.head_of t
    in (not o Term.is_Var) h andalso
       forall (fn Const (n, _) =>
                  (case h of
                     Const (m, _) => not (m = n)
                   | _ => true)
                | _ => true) D end
  | not_free_variable_defined D t (i :: Pos) =
    (case t of
       Abs (_, _, t) => not_free_variable_defined D t Pos
     | t => t |> Term.strip_comb
              |> (fn (h, args) => (not o Term.is_Var) h andalso
                                  forall (fn Const (n, _) =>
                                             (case h of
                                                Const (m, _) => not (m = n)
                                              | _ => true)
                                           | _ => true) D andalso
                                  args |> (fn l => nth l i)
                                       |> (fn t => not_free_variable_defined D t Pos)))
  | not_free_variable_defined _ _ [] = true

fun subterm_criterion D component =
    let val pis =
            component
              |> map (fn (u, v) =>
                         (u, v) |> subterm_positions
                                (fn (ui,vi) => Term.exists_subterm (fn t => (is_equal o Term_Ord.term_ord) (vi, t)) ui)
                                |> (fn ((sym_u, set_u), (sym_v, set_v)) => 
                                       ((sym_u, set_u |> PosSet.keys
                                                      |> filter (not_free_variable u)
                                                      |> make_set PosSet.update PosSet.empty),
                                        (sym_v, set_v |> PosSet.keys
                                                      |> filter (fn p => length p <= 1 orelse not_free_variable_defined D v p)
                                                      |> make_set PosSet.update PosSet.empty))))
              |> pair PIMap.empty
              |> Library.foldl (fn (pi_map, ((sym_u, set_u), (sym_v, set_v))) =>
                                   (case PIMap.lookup pi_map sym_u of
                                      SOME set => PIMap.update (sym_u, (PosSet.keys set_u) |> inter (is_equal o list_ord int_ord) (PosSet.keys set)
                                                                                           |> make_set PosSet.update PosSet.empty) pi_map
                                    | NONE => PIMap.update (sym_u, set_u) pi_map)
                                     |> (fn pi_map => case PIMap.lookup pi_map sym_v of
                                                        SOME set => PIMap.update (sym_v, (PosSet.keys set_v) |> inter  (is_equal o list_ord int_ord) (PosSet.keys set)
                                                                                                             |> make_set PosSet.update PosSet.empty) pi_map
                                                      | NONE => PIMap.update (sym_v, set_v) pi_map))
              |> PIMap.dest
              |> map (fn (symb, L) => map (pair symb) (PosSet.keys L))
              |> Utils.lazy_one_of_each
        fun test it =
            case it () of
              SOME L => if exists (fn (u, v) =>
                                      let val symb_u = (fst o Term.dest_Const o Term.head_of) u handle TERM msg => (tracing "528"; raise TERM msg)
                                          val symb_v = (fst o Term.dest_Const o Term.head_of) v handle TERM msg => (tracing "529"; raise TERM msg)
                                          val pos_u = case get_first (fn (symb, pos) => if symb = symb_u then SOME pos
                                                                                        else NONE) L of
                                                        SOME pos => pos
                                                      | NONE => []
                                          val pos_v = case get_first (fn (symb, pos) => if symb = symb_v then SOME pos
                                                                                        else NONE) L of
                                                        SOME pos => pos
                                                      | NONE => []
                                      in
                                        test_property (fn (ui,vi) =>
                                                          (not o is_equal o Term_Ord.term_ord) (ui,vi) andalso
                                                          Term.exists_subterm (fn t => (is_equal o Term_Ord.term_ord) (vi, t)) ui)
                                                      pos_u pos_v (u, v)
                                      end) component
                        then true
                        else test it
            | NONE => false
    in test pis end

datatype af_pi = Entero of int | Lista of int list

fun pi_ord ((Entero i), (Entero j)) = int_ord (i, j)
  | pi_ord ((Entero _), (Lista _)) = LESS
  | pi_ord ((Lista i), (Lista j)) = list_ord int_ord (i, j)
  | pi_ord ((Lista _), (Entero _)) = GREATER

fun potential_pis typ =
    let val (ty_args, ty_head) = strip_type typ
        val args_with_index = map_index I ty_args
        val base_pis = args_with_index
                         |> filter (fn (_, typ) => (is_equal o Term_Ord.typ_ord) (typ, ty_head))(*(null o fst o strip_type o snd) typ*)
                         |> map (Entero o fst)
        val non_base_pis = args_with_index |> map fst
                                           |> Utils.subsets
                                           |> map (Lista o (sort int_ord))
    in rev (base_pis @ non_base_pis) end

fun apply_pi pi (Abs (x, T, t)) = Abs (x, T, apply_pi pi t)
  | apply_pi pi t =
    let val (h, args) =  Term.strip_comb t
    in case h of
         Const (n, T) => (case PIMap.lookup pi n of
                            SOME af_pi => (case af_pi of
                                             Entero i => apply_pi pi (nth args i)
                                           | Lista l =>
                                             let val (ty_args, typ) = strip_type T
                                             in
                                               l |> map ((apply_pi pi) o (nth args))
                                                 |> pair (Const (n, (map (nth ty_args) l) ---> typ))
                                                 |> list_comb
                                             end)
                          | NONE => t)
       | Abs _ => args |> map (apply_pi pi)
                       |> pair (apply_pi pi h)
                       |> list_comb
       | _ $ _ => args |> map (apply_pi pi)
                       |> pair (apply_pi pi h)
                       |> list_comb
       | _ => args |> map (apply_pi pi)
                   |> pair h
                   |> list_comb
    end

structure STRSet = Table(
type key = string
val ord  = string_ord)

fun definitional_order tested mp f g =
    case PIMap.lookup mp f of
      SOME set => if STRSet.defined set g
                  then true
                  else (STRSet.keys tested) |> subtract (op =) (STRSet.keys set)
                                            |> exists (fn s => definitional_order (STRSet.update (s, ()) tested) mp s g)
    | NONE => false

fun usable_rules TRS D mp t =
    let val consts = [] |> Term.add_consts t
                        |> distinct (fn ((n,_),(m,_)) => n = m)
                        |> filter_out (fn (cname, _) => "==" = cname)
                        |> map fst
                        |> filter (fn s => STRSet.defined D s)
    in ([], TRS)
         |> Library.foldl (fn (rules, rule) =>
                              if (is_Const o head_of o fst o Utils.dest_meta_equation) rule then
                                let val top_l = (fst o dest_Const o head_of o fst o Utils.dest_meta_equation) rule handle TERM msg => (tracing "610"; raise TERM msg)
                                in if exists (fn f => definitional_order (STRSet.make_set [f]) mp f top_l) consts
                                   then rule :: rules
                                   else rules end
                                  (* FIXME: Not sure if usable *)
                              else rule :: rules)
    end

fun usable_rules_component _ TRS D mp component =
    component |> map snd
              |> maps (usable_rules TRS D mp)
              |> Utils.make_theorem_set

fun critic_function_symbols thy TRS D mp component =
    let val consts_component = component
                                 |> pair []
                                 |> Library.foldl (fn (consts, (u, v)) =>
                                                      consts |> Term.add_consts u
                                                             |> Term.add_consts v)
                                 |> distinct (fn ((n,_),(m,_)) => n = m)
                                 |> filter_out (fn (cname, _) => "==" = cname)
                                 |> map Const
        val usable = usable_rules_component thy TRS D mp component
        val consts_invalid_rules = usable |> maps ((fn (l,r) => [l,r]) o Utils.dest_meta_equation)
                                          |> pair []
                                          |> Library.foldl (fn (consts, t) => Term.add_consts t consts)
                                          |> distinct (fn ((n,_),(m,_)) => n = m)
                                          |> map Const
    in
      (usable, distinct (fn (Const (n,_),Const (m,_)) => n = m | _ => raise ERROR "critic_function_symbols") 
        (consts_component @ consts_invalid_rules))
    end

fun af_pi_iterator thy TRS D mp component =
    let val (usable, critic_symbols) = critic_function_symbols thy TRS D mp component
        val trs = map Thm.full_prop_of usable
        val pi_it =
            critic_symbols
              |> map (fn c => let val (n, _) = dest_Const c handle TERM msg => (tracing "645"; raise TERM msg)
                              in (n, (potential_pis o snd o dest_Const) c) handle TERM msg => (tracing "646"; raise TERM msg) end)
              |> map (fn (n, pis) =>
                         pis |> filter (fn pi => can (map (apply_pi (PIMap.update (n, pi) PIMap.empty))) trs)
                             |> map (pair n))
              |> filter_out null
              |> Utils.lazy_one_of_each
        fun it () =
            case pi_it () of
              SOME l => (PIMap.empty, l) |> Library.foldl (fn (pi_map, (s, pi)) => PIMap.update (s, pi) pi_map)
                                         |> SOME
            | NONE => NONE
    in
      (usable, it, component)
    end


fun weak_lpo_g pi f_ord =
    (fn P => ((Orders.lpo_g f_ord) o (apply2 (apply_pi pi))) P handle General.Subscript => false)

(* FIXME: This exception should not be raised in first place !!! *)
fun weak_lpo_ge pi f_ord =
    (fn P => ((fn (s, t) => s aconv t orelse Orders.lpo_g f_ord (s, t)) o (apply2 (apply_pi pi))) P
        handle General.Subscript => false)

(*fun memoized_weak_lpo_g map_ref pi f_ord =
    (Orders.memoized_lpo_g map_ref f_ord) o (apply2 (apply_pi pi))*)

fun extract_compatible_orders pi component =
    let
      val consts = ([], component) |> Library.foldl (fn (consts, (u, v)) =>
                                                        consts |> Term.add_consts u
                                                               |> Term.add_consts v)
                                   |> distinct (fn ((n,_),(m,_)) => n = m)
                                   |> filter_out (fn (cname, _) => Const_Names.meta_eq = cname)
                                   |> map Const
      val _ = if length consts > 5
              then raise (Complexity consts)
              else ()
      fun test order = 
        forall (fn (u, v) => weak_lpo_ge pi order (u, v)) component
          andalso exists (weak_lpo_g pi order) component
    in (consts, Orders.extend_ord test [] consts) end
(*    in (consts, compatible_orders consts_orders) end*)

fun construct_definitional_order TRS =
    let val trs = map Utils.dest_meta_equation TRS
    in
      (PIMap.empty, trs)
        |> Library.foldl (fn (mp, (l, r)) =>
                             if (is_Const o head_of) l then
                               let val head_l = (fst o dest_Const o head_of) l handle TERM msg => (tracing "722"; raise TERM msg)
                                   val consts_r = [] |> Term.add_consts r
                                                     |> distinct (fn ((n,_),(m,_)) => n = m)
                                                     |> filter_out (fn (cname, _) => "==" = cname)
                                                     |> map fst
                               in case PIMap.lookup mp head_l of
                                    SOME set => PIMap.update (head_l, Library.foldl (fn (set, c) => STRSet.update (c, ()) set) (set, consts_r)) mp
                                  | NONE => PIMap.update (head_l, make_set STRSet.update STRSet.empty consts_r) mp
                               end
                             else mp)
    end

fun find_models ords =
    if exists (null o snd) ords then Seq.empty
    else 
      let val consts = ords |> maps fst
                            |> distinct (fn (Const (n,_),Const (m,_)) => n = m | _ => raise ERROR "find_models")
          val names_consts = Library.foldl (fn (names,_) => (singleton (Name.variant_list names) "y") :: names) ([],consts)
          val consts_map = consts ~~ (map (rpair 0) names_consts) handle ListPair.UnequalLengths => (tracing "DPair 739"; raise ListPair.UnequalLengths)
          val term = ords |> map snd
                          |> map (SAT_Interface.ord_to_term_rpo consts_map)
                          |> SAT_Interface.mk_conj_balanced
          fun name_to_const n = consts_map |> get_first (fn (c,(name,_)) =>
                                                            if n = name then SOME c
                                                            else NONE)
                                           |> the_default @{term "True"}
      in
        term |> SAT_Interface.find_orders
             |> Seq.map (map (fn (t, i) => ((name_to_const o fst o dest_Free) t, i)))
      end

fun find_ord pi component TRS =
  let val ords = (map (Orders.extract_compatible_orders_rpo (weak_lpo_ge pi)) TRS) @
                 [extract_compatible_orders pi component]
  in
    find_models ords
  end

fun non_terminating_subterm th =
    let val (lhs, rhs) = Utils.dest_meta_equation th
    in Term.exists_subterm (fn t => (is_equal o Term_Ord.term_ord) (t, lhs)) rhs end

fun conditional_rule th =
  Thm.nprems_of th > 0

fun terminates' ctxt TRS =
    let val TRS = TRS |> Utils.make_theorem_set
        val thy = Proof_Context.theory_of ctxt
    in
      if exists Utils.permutative_rule TRS then false (*tracing "dp false!"; false*)
      else if exists conditional_rule TRS then false
      else if exists non_terminating_subterm TRS then false (*tracing "dp false!"; false*)
      else if not (plain_function_passing_hrs ctxt TRS) then false
      else
        let
          val D = TRS |> map (head_of o fst o Utils.dest_meta_equation)
                      |> filter is_Const
                      |> distinct (fn (Const (n,_),Const (m,_)) => n = m | _ => raise ERROR "terminates")
          val components = TRS |> maps (static_dependency_pairs D)
                               |> static_dependency_graph
                               |> strongly_connected_components
                               |> Seq.map (fn component => 
                                          map (fn (u, v) =>
                                                  let val (u_head, u_args) = strip_comb u
                                                      val (v_head, v_args) = strip_comb v
                                                      val (u_name, u_T) = dest_Const u_head handle TERM msg => (tracing "809"; raise TERM msg)
                                                      val (v_name, v_T) = dest_Const v_head handle TERM msg => (tracing "810"; raise TERM msg)
                                                      val u' = list_comb (Const (u_name ^ "#", u_T), u_args)
                                                      val v' = list_comb (Const (v_name ^ "#", v_T), v_args)
                                                  in (u', v') end) component)
          val invalid_components = Seq.filter (not o subterm_criterion D) components
          val mp = construct_definitional_order TRS
          val D = D |> map (fst o dest_Const)
                    |> make_set STRSet.update STRSet.empty handle TERM msg => (tracing "817"; raise TERM msg)
          val usable_it_component_list = invalid_components |> Seq.map (af_pi_iterator thy TRS D mp)
                                                            |> Seq.list_of
          fun ordering (usable, it, component) =
              case it () of
                SOME pi => let val ord = find_ord pi component usable
                           in if can Seq.hd ord
                              then SOME (pi, ord)
                              else ordering (usable, it, component)
                           end
              | NONE => NONE
          (*val weak_orders = map ordering usable_it_component_list*)
          val weak_orders = if null usable_it_component_list
                            then []
                            else Par_List.map ordering usable_it_component_list
        in if exists is_none weak_orders
           then false
           else true
        end
    end

fun terminates ctxt TRS =
  let val timeOut = Config.get ctxt max_time_in_termination
  in Timeout.apply (Time.fromSeconds timeOut) (terminates' ctxt) TRS
        handle Timeout.TIMEOUT _ => false
             | Complexity consts => ((*tracing ("Consts: " ^ Utils.str_of_terms ctxt consts);*)
                                     (*tracing ("TRS: " ^ Utils.str_of_thms TRS);*)
                                     false)
  end

end

structure DPair : DPAIR = DB_DPair
