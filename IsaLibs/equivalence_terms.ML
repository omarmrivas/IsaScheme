(*  Title:      util/equivalence_terms.ML
    ID:         $Id: const_names.ML,v 1.00 2017/28/04 17:28:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2017

Equivalence relation over terms
*)

signature EQ_TERMS =
sig

val max_random_terms   : int Config.T
val max_vars_in_tx     : int Config.T

(*val equation : Proof.context -> int -> int -> int -> term list Type_Tab.table ->
              (term -> term) -> thm list -> (term -> bool) -> term list -> term option*)
(*val counter_example: Proof.context -> term list Type_Tab.table ->
                     (term -> term) -> thm list -> term -> bool*)
val generalize : theory -> 'a Type_Tab.table * (term -> term) ->
                  int -> term -> term list

val preprocess_conjecture : Proof.context ->
      int -> term -> term list Type_Tab.table * (term -> term)

end

structure DB_EQ_Terms
(* : EQ_TERMS *)
= struct

val (max_random_terms, setup_max_random_terms) = Attrib.config_int @{binding "max_random_terms"} (K 10)
val (max_vars_in_tx, setup_max_vars_in_tx) = Attrib.config_int @{binding "max_vars_in_tx"} (K 3)

type eq_class = (term list Term_List_Tab.table * Term_Tab.set)

type tx = {target_typ: typ,
           prems: term list,
           tests: term list Term_List_Tab.table,
           eq_class : eq_class list,
           typsub : term -> term}

(*fun init_tx ctxt n conjecture : tx =
  let val (tbl, subst) = preprocess_conjecture ctxt n conjecture
  in {tables = [([], tbl)],
      typsub = subst}
  end*)

fun substitutions _ _ (SOME subst_prems) _ term =
  let val frees = [] |> Term.add_frees term
                     |> sort (prod_ord string_ord Term_Ord.typ_ord)
  in (map Free frees, map Term.subst_free subst_prems) end
  | substitutions ctxt simps NONE tab term =
  let val frees0 = [] |> Term.add_frees term
                      |> sort (prod_ord string_ord Term_Ord.typ_ord)
      fun take_all frees f =
        case f () of
          SOME r => (frees ~~ r) :: take_all frees f
          | NONE => []
      fun take_one frees f =
        case f () of
          SOME r => frees ~~ r
          | NONE => raise ERROR "take_one"
      fun one_subst frees =
          if null frees
          then I
          else
          let val frees_vals = map (the o Type_Tab.lookup tab o snd) frees
          in frees_vals |> Utils.lazy_one_of_each
                        |> take_one frees
                        |> map (fn (v, t) => (Free v, t))
                        |> Term.subst_free end
      fun get_substs frees =
          let val frees_vals = map (the o Type_Tab.lookup tab o snd) frees
          in frees_vals |> Utils.lazy_one_of_each
                        |> take_all frees
                        |> map (map (fn (v, t) => (Free v, t)))
                        |> map Term.subst_free end
      fun not_projection ((n, ty), frees) =
        let 
            val free_vals = the (Type_Tab.lookup tab ty)
            val termsubt = free_vals |> map (single o pair (Free (n, ty)))
                                     |> map Term.subst_free
            val termsubts  = get_substs frees
            val termsubts = if null termsubts
                            then map (fn _ => I) termsubt
                            else termsubts
            val subt0 = hd termsubt
        in exists (fn subst => let val val0 = Utils.normalise_term ctxt simps ((subt0 o subst) term)
              in exists (fn sub => Utils.normalise_term ctxt simps ((sub o subst) term) <> val0) termsubt
              end) termsubts end
      fun tk i ss = 
            let val prefix = take i ss
                val suffix = drop (i + 1) ss
            in (prefix, suffix) end
      val frees =
              frees0 |> map_index (fn (i, f) =>
                      let val (prefix, suffix) = tk i frees0
                      in (f, prefix @ suffix) end)
                     |> filter not_projection
                     |> map fst
      val subst0 = one_subst (subtract (op =) frees frees0)
      val termsubts  = get_substs frees
      val termsubts  = if null termsubts
                       then [subst0]
                       else map (fn subst => subst0 o subst) termsubts
  in (map Free frees, termsubts) end

fun substitutions' ctxt size n tab frees =
  let val thy = Proof_Context.theory_of ctxt
      val tss = map (fn (_,ty) =>
          case Type_Tab.lookup tab ty of
            SOME ts => ts
            | NONE  => (1 upto n)
                         |> map_filter (fn _ => Random_Terms.random_term ctxt size ty)
                         |> tap (fn _ => tracing "Re processing random terms!")
                         |> tap (fn _ => tracing ("Type: " ^ Syntax.string_of_typ ctxt ty))
                         |> Utils.make_term_set thy) frees
      fun take f =
        case f () of
          SOME r => (frees ~~ r) :: take f
          | NONE => []
      val termsubts  = tss |> Utils.lazy_one_of_each
                           |> take
                           |> map (map (fn (v, t) => (Free v, t)))
                           |> map Term.subst_free
  in termsubts end

fun preprocess_conjecture ctxt n conjecture =
  let val typs0 = Utils.datatype_dependencies ctxt conjecture
      val (table, typsubst) = 
            case find_first (not o Utils.parametric_type ctxt) typs0 of
              SOME ty => let val typsubst = Utils.monomorphize_frees ty
                             val typs = typs0 |> map (Utils.monomorphize_tfrees ty)
                                              |> distinct (op =)
                         in (Type_Tab.make (typs ~~ (Par_List.map (Counter_Example.enumerate_terms ctxt n) typs)), typsubst) end
            | NONE => let val typsubst = Utils.monomorphize_frees @{typ two}
                          val typs = typs0 |> map (Utils.monomorphize_tfrees @{typ two})
                                           |> distinct (op =)
                      in (Type_Tab.make ((typs @ [@{typ two}]) ~~ (Par_List.map (Counter_Example.enumerate_terms ctxt n) (typs @ [@{typ two}]))), typsubst) end
      val _ = table |> Type_Tab.dest
                    |> map fst
                    |> map (Syntax.string_of_typ ctxt)
                    |> enclose "<" ">" o commas
                    |> tracing
  in (table, typsubst) end

(*fun counter_example ctxt table typsub simps (conjecture : term) =
  let val t' = typsub conjecture
      val (_, tsubsts) = substitutions ctxt simps table t'
      val conjs = map (fn subst => subst t') tsubsts
  in exists (fn conj => Utils.normalise_term ctxt simps conj = @{prop "False"}) conjs end*)

fun maps_filter_seq bufsize v par f seq =
  let fun process v [] seq =
            Seq.make (fn () =>
              (case Seq.chop bufsize seq of
                ([], _) => NONE
              | (xs, seq) => let val xs = Par_List.map par xs
                             in Seq.pull (process v xs seq) end))
        | process v xs seq =
            Seq.make (fn () =>
              case xs of
                  x :: xs => let val (v, ys) = f v x
                             in case ys of
                                  y :: ys => SOME (y, Seq.append (Seq.of_list ys) (process v xs seq))
                                | [] => Seq.pull (process v xs seq) end
                | [] => Seq.pull (process v [] seq))
  in process v [] seq end

(* Construct equations lazily.
  buffsize: number of cores
  v: value used to find equations and filter terms
  par: calculate index of term (in parallel)
  f: use index to find equivalence class
  g: filter already processed terms
  seq: sequence of terms
*)
fun maps_filter_seq2 bufsize v par f seq =
  let fun process v [] seq =
            Seq.make (fn () =>
              (case Seq.chop bufsize seq of
                ([], _) => NONE
              | (xs, seq) => let val xs = Par_List.map (par v) xs
                                            |> map_filter I
                             in Seq.pull (process v xs seq) end))
        | process v xs seq =
            Seq.make (fn () =>
              case xs of
                  x :: xs => let val (v, ys) = f v x
                             in case ys of
                                  y :: ys => SOME (y,
                                                Seq.append (Seq.of_list ys)
                                                (process v xs seq))
                                | [] => Seq.pull (process v xs seq) end
                | [] => Seq.pull (process v [] seq))
  in process v [] seq end

fun discover_equations ctxt simps table typsub terms =
  let val buff = Utils.num_processors
      fun check t s =
        let val eq = (t, s) |> HOLogic.mk_eq
                            |> HOLogic.mk_Trueprop
                            |> Utils.normalise_term ctxt (!simps)
        in if eq <> @{prop "True"}
           then SOME eq
           else NONE
        end
      fun calcule_keys t =
          let val t' = typsub t
              val (preffix, tsubsts) = substitutions ctxt (!simps) NONE table t'
              val key = preffix @ map (fn subst => Utils.normalise_term ctxt (!simps) (subst t')) tsubsts
          in (t, key) end
      fun find_eqs tab (t,key) =
          case Term_List_Tab.lookup tab key of
              SOME ss => (Term_List_Tab.update (key, t::ss) tab,  map_filter (check t) ss)
            | NONE => (Term_List_Tab.update (key, [t]) tab, [])
  in maps_filter_seq buff Term_List_Tab.empty calcule_keys find_eqs terms end

fun discover_equations2 ctxt prems simps table typsub classes terms =
  let val buff = Utils.num_processors
      val thy = Proof_Context.theory_of ctxt
      fun check t s =
        let val eq = (t, s) |> HOLogic.mk_eq
                            |> HOLogic.mk_Trueprop
                            |> (Logic.list_implies o pair prems)
                            |> Utils.normalise_term ctxt (!simps)
        in if eq <> @{prop "True"}
           then SOME eq
           else NONE
        end handle Option => (tracing ("Error in check: " ^ Syntax.string_of_term ctxt t); raise Option)
      fun calcule_keys (_, processed) t =
        let val t = Utils.normalise_term' ctxt (!simps) prems t
        in if Term_Tab.defined processed t
           then NONE
           else
            let val t' = typsub t
                val (preffix, tsubsts) = substitutions ctxt (!simps) NONE table t'
                val key = preffix @ map (fn subst => Utils.normalise_term ctxt (!simps) (subst t')) tsubsts
            in SOME (t, key) end
        end handle Option => (tracing ("Error in calcule_keys: " ^ Syntax.string_of_term ctxt t); raise Option)
      fun reduce trms =
        trms |> map (Utils.normalise_term' ctxt (!simps) prems)
             |> Utils.make_term_set thy
      fun find_eqs (tab, processed) (t,key) =
          (case Term_List_Tab.lookup tab key of
              SOME ss => let val ss' = reduce ss
                             val nclasses = (Term_List_Tab.update (key, t :: ss') tab,
                                             Term_Tab.update (t, ()) processed)
                             val _ = classes := nclasses
                         in (nclasses,  map_filter (check t) ss')
                         end
            | NONE => let val nclasses = (Term_List_Tab.update (key, [t]) tab,
                                          Term_Tab.update (t, ()) processed)
                             val _ = classes := nclasses
                      in (nclasses, [])
                      end) handle Option => (tracing ("Error in find_eqs: " ^ Syntax.string_of_term ctxt t); raise Option)
  in maps_filter_seq2 buff (!classes) calcule_keys find_eqs terms end

fun equation' ctxt (tab, typsub) size n simps subsumed term =
  let val thy = Proof_Context.theory_of ctxt
      fun monomorphize typ = (type_of o typsub) (Free ("x", typ))
      val frees = Term.add_frees term []
      val tsubsts = frees
                     |> map (fn (n,ty) => (n, monomorphize ty))
                     |> substitutions' ctxt size n tab
      fun check t s =
        let val eq = (t, s) |> HOLogic.mk_eq
                            |> HOLogic.mk_Trueprop
            val eq' = (HOLogic.mk_Trueprop o Utils.swap_eq o HOLogic.dest_Trueprop) eq
        in if not (subsumed eq orelse subsumed eq')
           then SOME eq
           else NONE
        end
      fun check_eqs tab (t :: terms) =
          let val t' = typsub t
              val key = map (fn subst => Utils.normalise_term ctxt simps (subst t')) tsubsts
          in case Term_List_Tab.lookup tab key of
                  SOME ss => (case get_first (check t) ss of
                                SOME eq => eq
                              | NONE => check_eqs (Term_List_Tab.update (key, t::ss) tab) terms)
                 | NONE => check_eqs (Term_List_Tab.update (key, [t]) tab) terms
            end
        | check_eqs _ [] = term
  in term |> Utils.subterms_no_loose_no_funs
          |> filter (fn t => Type_Tab.defined tab (monomorphize (type_of t)))
          |> map (Utils.normalise_term ctxt simps)
          |> Utils.make_term_set thy
          |> Utils.sort_by_general thy
          |> check_eqs Term_List_Tab.empty
          end

fun known_laws ctxt prop =
  let val thy = Proof_Context.theory_of ctxt
      val prop_schemes = PropSchemes.get ctxt
      val consts = Utils.definitional_dependencies thy ([], prop)
                    |> filter_out (fn (name, _) => name = Const_Names.hol_eq)
                    |> map (Inst_Utils.dummyTvfy o Const)
      val terms = prop_schemes
        |> maps (fn scheme =>
            let val (_,scheme_lhs,vars_ord) = Inst_Utils.vars_ordered ctxt scheme
                val compatib = Inst_Utils.compatible_arguments ctxt scheme_lhs consts vars_ord
            in [] |> Inst_Utils.combine ctxt scheme (fn t => fn l => t :: l) scheme_lhs compatib
                  |> map (Utils.normalise_term ctxt [scheme])
                  |> map (fn to_prove =>
                         to_prove |> Utils.binder_elimination Const_Names.hol_forall []
                                  |> fst handle Match => to_prove)
            end)
        |> Utils.make_term_set thy
        |> Utils.sort_by_general thy
      val timeOut = Config.get ctxt Counter_Example.max_time_in_counter_ex
  in terms
        |> map (fn t => let val typ = type_of t
                        in if typ = @{typ "prop"}
                           then t
                           else if typ = @{typ "bool"}
                           then HOLogic.mk_Trueprop t
                           else raise ERROR "Term not of valid type. Invalid scheme?"
                        end)
        |> filter (fn t => t <> @{prop "True"})
        |> filter (fn t => t <> @{prop "False"})
        |> Par_List.map (fn prop =>
            if Counter_Example.memoized_counter_example ctxt timeOut prop
            then NONE
            else SOME prop)
        |> map_filter I
        |> Seq.of_list
  end

fun extend_frees (tab, typsub) prop =
  let fun monomorphize typ = (type_of o typsub) (Free ("x", typ))
      fun group_by frees =
          (Type_Tab.empty,frees)
                |> Library.foldl (fn (tab, (n,ty)) =>
                    case Type_Tab.lookup tab ty of
                      SOME ns => Type_Tab.update (ty, n::ns) tab
                    | NONE => Type_Tab.update (ty, [n]) tab)
                |> Type_Tab.dest
                |> map (fn (ty, names) =>
                    (ty, 
                      Library.foldl (fn (tab, n) =>
                          case Str_Tab.lookup tab n of
                            SOME c => Str_Tab.update (n, c+1) tab
                            | NONE => Str_Tab.update (n, 1) tab) (Str_Tab.empty, names)))
                |> pair Type_Tab.empty
                |> Library.foldl (fn (tab, (ty,t)) =>
                    Type_Tab.update (ty, t) tab)
      fun merge (tab1, tab2) =
        let val elems = Type_Tab.fold (fn (typ, _) => fn tab => Type_Tab.delete_safe typ tab) tab1 tab2
                                              |> Type_Tab.dest
        in
        Type_Tab.fold (fn (ty, tab) => fn r1 =>
            case Type_Tab.lookup tab2 ty of
              SOME tab' => let val elems = Str_Tab.fold (fn (typ, _) => fn tab => Str_Tab.delete_safe typ tab) tab tab'
                                              |> Str_Tab.dest
                           in
                              Str_Tab.fold (fn (n, i) => fn r2 =>
                            case Str_Tab.lookup tab' n of
                              SOME i' => if i >= i'
                                         then Str_Tab.update (n, i) r2
                                         else Str_Tab.update (n, i') r2
                               | NONE => Str_Tab.update (n, i) r2) tab Str_Tab.empty
                              |> rpair elems
                              |> Library.foldl (fn (tab, (n,i)) =>
                                      Str_Tab.update (n, i) tab)
                              |> (fn tab => Type_Tab.update (ty, tab) r1)
                           end
              | NONE => Type_Tab.update (ty, tab) r1) tab1 Type_Tab.empty
        |> rpair elems
        |> Library.foldl (fn (tab, (n,i)) =>
                Type_Tab.update (n, i) tab)
        |> Type_Tab.dest
        |> map (fn (ty, tab) => (ty, Str_Tab.dest tab))
      end
      fun free_positions t =
          t |> Utils.positions
            |> map_filter (fn (Free (n,typ), _, _) =>
                            if Type_Tab.defined tab (monomorphize typ)
                            then SOME (n,typ)
                            else NONE
                        | _ => NONE)
            |> group_by
      fun vars_heuristic prop =
          if can (HOLogic.dest_eq o HOLogic.dest_Trueprop) prop
          then  prop |> (HOLogic.dest_eq o HOLogic.dest_Trueprop)
                     |> apply2 free_positions
                     |> merge
          else free_positions prop
                |> Type_Tab.dest
                |> map (fn (ty, tab) => (ty, Str_Tab.dest tab))
  in prop |> vars_heuristic
          |> pair []
          |> Library.foldl (fn (names, (typ, ns)) =>
                Library.foldl (fn (names, (n,i)) =>
                    (n, typ) ::
                    Library.foldl (fn (names, _) =>
                        let val name = singleton (Name.variant_list (n::map fst names)) n
                        in (name, typ) :: names end) (names, 1 upto (i-1))) (names, ns))
  end

(* FIXME: Increment frees to a maximum limit of frees (e.g. x + x + x = x + x + x)
  should include more variables (e.g. y and z).
*)
fun equational_theory_exploration ctxt (table, typsub) lambda_size simps prems prop =
  let val thy = Proof_Context.theory_of ctxt
      val typs = Utils.datatype_dependencies ctxt prop
      (* FIXME: typs should be polymorphic *)
      val frees = 
          typs |> maps (fn typ => map (fn _ => typ) (1 upto Config.get ctxt max_vars_in_tx))
               |> pair ([],[])
               |> Library.foldl (fn ((names, frees), typ) =>
                    let val name = singleton (Name.variant_list names) "x"
                    in (name :: names, (name, typ) :: frees) end)
               |> snd
      val consts = Utils.definitional_dependencies thy ([], prop)
                    |> filter_out (fn (name, _) => name = Const_Names.hol_eq)
                    |> map (fn (name, typ) => (name, Logic.unvarifyT_global typ))
      val typ_args = map snd (consts @ frees)
      val args = map Const consts @ map Free frees
      val _ = args |> map (Syntax.string_of_term ctxt)
                   |> commas
                   |> enclose "<" ">"
                   |> tracing
      fun get_terms target =
        let val typ = typ_args ---> target
            val lambdas = Random_Terms.lazy_all_lambda_terms typ (lambda_size + length typ_args)
        in lambdas |> Seq.map (fn t => betapplys (t, args))
                   |> Seq.list_of
                   |> Utils.make_term_set thy
                   |> Utils.sort_by_general thy
                   |> Seq.of_list
        end
  in typs |> Seq.of_list
          |> Seq.maps get_terms
          |> discover_equations ctxt simps table typsub
          |> Seq.map (Logic.list_implies o pair prems) end

(* FIXME: Increment frees to a maximum limit of frees (e.g. x + x + x = x + x + x)
  should include more variables (e.g. y and z).
*)
fun equational_theory_exploration2 ctxt (table, typsub) lambda_size simps prems classes prop =
  let val thy = Proof_Context.theory_of ctxt
      val typs = Utils.type_dependencies ctxt prop
      (* FIXME: typs should be polymorphic *)
      val frees = 
          typs |> maps (fn typ => map (fn _ => typ) (1 upto Config.get ctxt max_vars_in_tx))
               |> pair ([],[])
               |> Library.foldl (fn ((names, frees), typ) =>
                    let val name = singleton (Name.variant_list names) "x"
                    in (name :: names, (name, typ) :: frees) end)
               |> snd
      val consts = Utils.definitional_dependencies thy ([], prop)
                    |> filter_out (fn (name, _) => name = Const_Names.hol_eq)
                    |> map (fn (name, typ) => (name, Logic.unvarifyT_global typ))
      val typ_args = map snd (consts @ frees)
      val args = map Const consts @ map Free frees
      val _ = args |> map (Syntax.string_of_term ctxt)
                   |> commas
                   |> enclose "<" ">"
                   |> tracing
      fun get_terms target =
        let val typ = typ_args ---> target
            val lambdas = Random_Terms.lazy_all_lambda_terms typ (lambda_size + length typ_args)
        in lambdas |> Seq.map (fn t => betapplys (t, args))
                   |> Seq.list_of
                   |> Utils.make_term_set thy
                   |> Utils.sort_by_general thy
                   |> Seq.of_list
        end
  in typs |> Seq.of_list
          |> Seq.maps get_terms
          |> discover_equations2 ctxt prems simps table typsub classes
          |> pair frees
  end

(* Finds a potential valid equation using tests
   terms: must be sorted from more general to less general
          to find general equations first. They also must
          be in normal form w.r.t. simps *)
fun gen_equations ctxt typsub simps subsumed tsubsts terms_lhs terms_rhs =
  let val lhs_results = 
              Par_List.map (fn t => 
                  let val t' = typsub t
                  in (map (fn subst => Utils.normalise_term ctxt simps (subst t')) tsubsts, t)
                  end) terms_lhs
      val lhs_tab = 
            (Term_List_Tab.empty, lhs_results)
              |> Library.foldl (fn (tab, (key,t)) =>
                case Term_List_Tab.lookup tab key of
                  SOME ss => Term_List_Tab.update (key, t::ss) tab
                | NONE => Term_List_Tab.update (key, [t]) tab)
      fun check rhs lhs =
        let val equation = (lhs, rhs) |> HOLogic.mk_eq
                                      |> HOLogic.mk_Trueprop
            val equation' = (HOLogic.mk_Trueprop o Utils.swap_eq o HOLogic.dest_Trueprop) equation
            val better = not (subsumed equation orelse subsumed equation')
        in if better
           then (tracing ("gen_equations: " ^ Syntax.string_of_term ctxt equation); SOME equation)
           else NONE
        end
  in
    terms_rhs |> 
         Par_List.map (fn t =>
                  let val t' = typsub t
                      val key = map (fn subst => Utils.normalise_term ctxt simps (subst t')) tsubsts
                  in case Term_List_Tab.lookup lhs_tab key of
                      SOME ss => map_filter (check t) ss
                      | NONE => []
            end)
             |> maps I
  end

fun generalize_eq' ctxt size n (tab, typsub) simps subsumed eq =
  let val thy = Proof_Context.theory_of ctxt
      val (lhs, rhs) = (HOLogic.dest_eq o HOLogic.dest_Trueprop) eq
      fun monomorphize typ = (type_of o typsub) (Free ("x", typ))
      fun make_table positions =
            positions |> filter (fn (_, typ, _) => Type_Tab.defined tab (monomorphize typ))
                      |> pair Term_Tab.empty
                      |> Library.foldl (fn (lhs_tab, (t,typ,pos)) =>
                            case Term_Tab.lookup lhs_tab t of
                                SOME l => Term_Tab.update (t, (typ,pos) :: l) lhs_tab
                              | NONE => Term_Tab.update (t, [(typ,pos)]) lhs_tab)
      val names = [] |> Term.add_free_names lhs
                     |> Term.add_free_names rhs
      val name = singleton (Name.variant_list names) "x"
      val lhs_positions = lhs |> Utils.positions
                              |> make_table
      val rhs_positions = rhs |> Utils.positions
                              |> make_table
      fun poss term t (tab :  (typ * int list) list Term_Tab.table) =
          case Term_Tab.lookup tab t of
             SOME l => 1 upto (length l)
                          |> Seq.of_list
                          |> Seq.maps (fn i => Utils.lazy_subsets_of_size i l)
                          |> Seq.map (fn l => 
                                Library.foldl (fn (term, (ty, pos)) => 
                                 Utils.substitute (Free (name, ty), pos) term) (term, l))

           | NONE => Seq.empty
      val lhss = Term_Tab.keys lhs_positions
      val rhss = Term_Tab.keys rhs_positions
      val terms = inter (op =) lhss rhss
      val typs = (Type_Tab.empty, terms)
                  |> Library.foldl (fn (tab, t) => Type_Tab.update (type_of t, ()) tab)
                  |> Type_Tab.keys
      val frees = [] |> Term.add_frees lhs
                     |> Term.add_frees rhs
      val tsubsts = frees @ map (pair name) typs
                     |> map (fn (n,ty) => (n, monomorphize ty))
                     |> substitutions' ctxt size n tab
      val eq' = Logic.varify_global eq
      fun subsumed' eq =
            (case (HOLogic.dest_eq o HOLogic.dest_Trueprop) eq of
               (Free _, Free _) => true
             | (s, t) => s = t) orelse
            subsumed eq orelse
            Pattern.matchess thy ([eq'],[eq])
  in terms |> 
     maps (fn t => let val ts = poss lhs t lhs_positions |> Seq.list_of
                       val ts' = poss rhs t rhs_positions|> Seq.list_of
                   in gen_equations ctxt typsub simps subsumed' tsubsts ts ts' end)
           |> Utils.make_term_set' thy
  end

fun generalize_eq i ctxt size n (tab, typsub) simps subsumed eq =
  let val thy = Proof_Context.theory_of ctxt
      fun aux i ((subsumed,eqs'), eq) = 
        if i <= 0
        then (subsumed, eq :: eqs')
        else
        let val eqs = generalize_eq' ctxt size n (tab, typsub) simps subsumed eq
            val eq' = Logic.varify_global eq
            fun subsumed' eq =
                subsumed eq orelse
                Pattern.matchess thy ([eq'], [eq])
        in ((subsumed', eqs'), eqs)
            |> Library.foldl (aux (i-1))
            |> (fn (subsumed, []) => (subsumed, [eq])
                 | (subsumed, eqs) => (subsumed, eqs))
        end
  in aux i ((subsumed,[]), eq)
      |> snd
      |> Utils.make_term_set' thy
  end

fun generalize thy (tab, typsub) n t =
  let val _ = tracing ("Size: " ^ (string_of_int o size_of_term) t)
      fun monomorphize typ = (type_of o typsub) (Free ("x", typ))
      fun pairs (h :: l) =
              l |> map SOME
                |> zip_options (h :: l)
                |> (fn l => if null l
                            then [(h, h)]
                            else l)
        | pairs [] = []
      fun valid ((x, y) :: (x', y') :: rest) =
          let val ((_, _, l), (_, _, r)) = (x, y)
          in
            if is_prefix (op =) l r
            then valid ((x,y') :: rest)
            else x :: valid ((x', y') :: rest)
          end
        | valid [(x, y)] = 
          let val ((_, _, l), (_, _, r)) = (x, y)
          in
            if is_prefix (op =) l r
            then [x]
            else [x, y]
          end
        | valid [] = []
      val ps = t |> Utils.positions
                 |> filter (fn (_, typ, _) => Type_Tab.defined tab (monomorphize typ))
                 |> tap (fn ps => tracing ("Positions: " ^ (string_of_int o length) ps))
(*                 |> filter (fn (_, typ, _) => (null o binder_types) typ andalso
                                              typ <> @{typ "prop"})*)
      fun gen i =
          let (*             val ctxt = Context.proof_of (Context.Theory thy)
              fun string_of_position ctxt (term, pos) =
                pos |> map string_of_int
                    |> space_implode "."
                    |> enclose "(" ")"
                    |> (fn str => "<" ^ Syntax.string_of_term ctxt term ^ ", " ^
                                        str ^ ">")
              fun string_of_positions ctxt l =
                l |> map (string_of_position ctxt)
                  |> space_implode ","
                  |> enclose "[" "]"
              fun string_of_position' ctxt (term, _, pos) =
                pos |> map string_of_int
                    |> space_implode "."
                    |> enclose "(" ")"
                    |> (fn str => "<" ^ Syntax.string_of_term ctxt term ^ ", " ^
                                        str ^ ">")
              fun string_of_positions' ctxt l =
                l |> map (string_of_position' ctxt)
                  |> space_implode ","
                  |> enclose "[" "]"*)
             val holes = Utils.lazy_subsets_of_size i ps
                            |> Seq.list_of
                            |> map (sort (dict_ord int_ord o (fn ((_, _, l), (_, _, r)) => (l,r))))
(*                            |> tap (fn _ => tracing "Sorted")
                            |> tap (map (tracing o (string_of_positions' ctxt)))*)
                            |> map (valid o pairs)
(*                            |> tap (fn _ => tracing "Valid")
                            |> tap (map (tracing o (string_of_positions' ctxt)))
                            |> tap (fn _ => tracing "Done")*)
              val names = Term.add_frees t []
                            |> map fst
                            |> rpair (1 upto i)
                            |> Library.foldl (fn (names, _) => singleton (Name.variant_list names) "x" :: names)
              fun round holes i =
                let val names = take i names
                    val initial = map (fn hole => (hole, names)) holes
                    fun successors [] = []
                      | successors ((_, []) :: _) = []
                      | successors ((_, [_]) :: _) = []
                      | successors ((v, ds) :: rest) = map (fn d => rest @ [(v, [d])]) ds
                    fun is_goal [] = true
                      | is_goal ((_, [_]) :: _) = true
                      | is_goal _ = false
                in successors |> Utils.dfs' [initial] is_goal
                              |> Seq.map (map (fn ((_, typ, pos), l) => 
                                        (Free (hd l, typ), pos)))
                                           |> Seq.map (fn l => ((*tracing (string_of_positions ctxt l);*) Library.foldl (fn (t, (v, pos)) => 
                                                    Utils.substitute (v, pos) t) (t, l)))
                                           |> Seq.list_of
(*                                           |> tap (fn l => tracing ("i: " ^ string_of_int i ^ " - " ^ (string_of_int o length) l))*)
                                           |> Utils.make_term_set' thy end
              fun rounds holes = 1 upto i |> maps (round holes)
                                          |> Utils.make_term_set' thy
          in maps rounds holes
              |> Utils.make_term_set' thy end
  in maps gen (1 upto n)
      |> Utils.make_term_set' thy
      |> tap (fn _ => tracing "Done") end

end

structure EQ_Terms : EQ_TERMS = DB_EQ_Terms

