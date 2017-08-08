(*  Title:      util/equivalence_terms.ML
    ID:         $Id: const_names.ML,v 1.00 2017/28/04 17:28:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2017

Equivalence relation over terms
*)

signature EQ_TERMS =
sig

val max_random_terms   : int Config.T

val equation : Proof.context -> int -> int -> int -> term list Type_Tab.table ->
              (term -> term) -> thm list -> (term -> bool) -> term list -> term option
val counter_example: Proof.context -> int -> int -> term list Type_Tab.table ->
                     (term -> term) -> thm list -> term -> bool
val generalize : theory -> 'a Type_Tab.table * (term -> term) ->
                  int -> term -> term list

end

structure DB_EQ_Terms
(* : EQ_TERMS *)
= struct

val (max_random_terms, setup_max_random_terms) = Attrib.config_int @{binding "max_random_terms"} (K 10)

fun substitutions ctxt size n tab term =
  let val thy = Proof_Context.theory_of ctxt
      val frees = [] |> Term.add_frees term
                     |> sort (prod_ord string_ord Term_Ord.typ_ord)
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

fun preprocess_conjecture ctxt size n conjecture =
  let val typsub = 
             [] |> Term.add_tfrees conjecture
                |> map (fn f => (TFree f, @{typ "int"}))
                |> subst_atomic_types
      val conjecture = typsub conjecture
      val frees = Term.add_frees conjecture []
      val typs = frees |> map snd
                       |> Type_Tab.make_set
                       |> Type_Tab.dest
                       |> map fst
      val thy = Proof_Context.theory_of ctxt
      val ts = typs |> map (fn ty => 
                  let val ts = (1 upto n)
                                |> map_filter (fn _ => Random_Terms.random_term ctxt size ty)
                                |> Utils.make_term_set thy
                  in (ty, ts) end)
      val table = Type_Tab.make ts
  in (table, typsub) end

fun counter_example ctxt size n table typsub simps (conjecture : term) =
  let val t' = typsub conjecture
      val (_, tsubsts) = substitutions ctxt size n table t'
      val conjs = map (fn subst => subst t') tsubsts
  in exists (fn conj => Utils.normalise_term ctxt simps conj = @{prop "False"}) conjs end

fun discover_equations ctxt simps typsub tsubsts terms =
  let val buff = Thread.numProcessors () * 2
      fun check t s =
        let val eq = (t, s) |> HOLogic.mk_eq
                            |> HOLogic.mk_Trueprop
                            |> Utils.normalise_term ctxt (!simps)
        in if eq <> @{prop "True"}
           then SOME eq
           else NONE
        end
(*      fun check_eqs tab terms =
        case Seq.pull terms of
          SOME (t, terms) => 
              let val t' = typsub t
                  val key = map (fn subst => Utils.normalise_term ctxt (!simps) (subst t')) tsubsts
              in case Term_List_Tab.lookup tab key of
                  SOME ss => (case map_filter (check t) ss of
                              [] => check_eqs (Term_List_Tab.update (key, t::ss) tab) terms
                            | eqs  => let val (eqs,last) = split_last eqs
                             in Seq.append (Seq.of_list eqs)
                                      (Seq.make (fn () => SOME (last, check_eqs (Term_List_Tab.update (key, t::ss) tab) terms))) end)
                 | NONE => check_eqs (Term_List_Tab.update (key, [t]) tab) terms
              end
        | NONE => Seq.empty*)
      fun check_eqs tab [] seq = 
            (case Seq.chop buff seq of
              ([], _) => Seq.empty
            | (terms, seq) =>
                let val terms = Par_List.map (fn t =>
                        let val t' = typsub t
                            val key = map (fn subst => Utils.normalise_term ctxt (!simps) (subst t')) tsubsts
                        in (t, key) end) terms
                in check_eqs tab terms seq end)
        | check_eqs tab ((t,key) :: terms) seq =
              case Term_List_Tab.lookup tab key of
                  SOME ss => (case map_filter (check t) ss of
                              [] => check_eqs (Term_List_Tab.update (key, t::ss) tab) terms seq
                            | eqs  => let val (eqs,last) = split_last eqs
                             in Seq.append (Seq.of_list eqs)
                                      (Seq.make (fn () => SOME (last, check_eqs (Term_List_Tab.update (key, t::ss) tab) terms seq))) end)
                 | NONE => check_eqs (Term_List_Tab.update (key, [t]) tab) terms seq
  in check_eqs Term_List_Tab.empty [] terms end


(* Finds a potential valid equation using tests
   terms: must be sorted from more general to less general
          to find general equations first. They also must
          be in normal form w.r.t. simps *)
fun equation ctxt timeOut size n table typsub simps subsumed terms =
  let val thy = Proof_Context.theory_of ctxt
      fun monomorphize typ = (type_of o typsub) (Free ("x", typ))
      fun null_frees t =
          [] |> Term.add_frees t
             |> null
      val terms = Library.foldl (fn (net, t) =>
            t |> Utils.subterms_no_loose_no_funs
              |> filter (fn t => Type_Tab.defined table (monomorphize (type_of t)))
              |> map (Utils.normalise_term ctxt simps)
              |> filter (not o null_frees)
              |> pair net
              |> Library.foldl (fn (net, t) =>
                  Net.insert_term_safe (is_equal o Term_Ord.fast_term_ord)
                                       (t, t) net)) (Net.empty, terms)
              |> Net.content
              |> Utils.sort_by_general thy
      fun find _ [] = NONE
        | find tab (t::ts) =
            let val t' = typsub t
                val (frees, tsubsts) = substitutions ctxt size n table t'
                val results = map (fn subst => Utils.normalise_term ctxt simps (subst t')) tsubsts
                val key = frees @ results
                fun check insert s =
                          let val equation = (s, t) |> HOLogic.mk_eq
                                                    |> HOLogic.mk_Trueprop
                              val equation' = (HOLogic.mk_Trueprop o Utils.swap_eq o HOLogic.dest_Trueprop) equation
                              val better = not (subsumed equation orelse subsumed equation')
                          in if better
                             then (if counter_example ctxt size n table typsub simps equation (*Counter_Example.counter_example ctxt timeOut equation*)
                                   then (tracing "More tests are required!";
                                         tracing ("Bad equiation: " ^ Utils.str_of_terms ctxt [equation]);
                                        raise ERROR "More tests are required!")
                                   else SOME equation)
                              else find (insert tab) ts end
            in case Term_List_Tab.lookup tab key of
                SOME s => check I s
                | NONE => let val v = hd results
                          in if forall (fn v' => v = v') results
                             then check (Term_List_Tab.update (key, t)) v
                             else find (Term_List_Tab.update (key, t) tab) ts end
            end
  in find Term_List_Tab.empty terms end

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

(* (* Performs the instantiation over schemes automatically *)
fun combine t l ctxt = 
    case l of
      (v,(h::[])) :: [] => t |> Term.subst_free [(v,h)]
                             |> try (Syntax.check_term ctxt)
                             |> (fn si => case si of SOME i => [i] | NONE => [])
    | (v,(h::t1)) :: [] => t |> Term.subst_free [(v,h)]
                             |> try (Syntax.check_term ctxt)
                             |> (fn r => case r of SOME x => combine t [(v,t1)] ctxt
				                                         | NONE => combine t [(v,t1)] ctxt)
    | (v,(h::t1)) :: t2 => 
      let val x = Term.subst_free [(v,h)] t in
        x |> try (Syntax.check_term ctxt)
          |> (fn r => case r of 
                        SOME t' => 
                        let 
                          val unfolded = t'
                          val frees = Term.add_frees unfolded []
                          val t2' = filter (fn (Free (name,_),_) => exists (fn (name',_) => name = name') frees
                                              | _ => raise ERROR "") t2
                        in
                          combine x t2' ctxt @
                          combine t ((v,t1) :: t2) ctxt
                        end
				              | NONE => combine t (append [(v,t1)] t2) ctxt) end
    | _ => []*)

(* FIXME: create fresh variables for frees in schemes and conjecture.
          Then apply the substitution. *)
fun known_eq_laws ctxt (table, typsub) size n simps prop =
  let val thy = Proof_Context.theory_of ctxt
(*      val schemes = Utils.get_schematic_lemmas ()*)
      val frees = Term.add_frees prop []
      fun monomorphize typ = (type_of o typsub) (Free ("x", typ))
      val tsubsts = frees
                     |> map (fn (n,ty) => (n, monomorphize ty))
                     |> substitutions' ctxt size n table
      val consts = Utils.definitional_dependencies thy ([], prop)
                    |> filter_out (fn (name, _) => name = Const_Names.hol_eq)
                    |> map (Inst_Utils.dummyTvfy o Const)
      val prop_schemes = PropSchemes.get ctxt
      val terms = prop_schemes
        |> maps (fn scheme =>
      let val (_,scheme_lhs,vars_ord) = Inst_Utils.vars_ordered ctxt scheme
          val compatib = Inst_Utils.compatible_arguments ctxt scheme_lhs consts vars_ord
      in [] |> Inst_Utils.combine ctxt scheme (fn t => fn l => t :: l) scheme_lhs compatib
            |> map (Utils.normalise_term ctxt [scheme])
            |> map (fn to_prove =>
                       to_prove |> Utils.binder_elimination Const_Names.hol_forall []
                                |> fst handle Match => to_prove)
            |> map_filter (try HOLogic.dest_eq)
            |> maps (fn (lhs, rhs) => [lhs, rhs])
            |> Utils.make_term_set thy
            |> Utils.sort_by_general thy
      end)
        |> Utils.make_term_set thy
        |> Utils.sort_by_general thy

      val frees_schemes = ([], terms)
                            |> Library.foldl (fn (frees, t) => Term.add_frees t frees)
      val intersection = inter (op =) frees frees_schemes
      val all_frees = frees_schemes |> Term.add_frees prop
                                    |> map fst
      val subst0 = ([], intersection)
                    |> Library.foldl (fn (subst, (n,typ)) =>
                            let val name = singleton (Name.variant_list (map (fst o snd) subst @ all_frees)) n
                            in ((n,typ), (name, typ)) :: subst end)
                    |> map (apply2 Free)
      val terms = map (subst_free subst0) terms
      val frees_schemes = ([], terms)
                            |> Library.foldl (fn (frees, t) => Term.add_frees t frees)
      val subst = Library.foldl (fn ((subst, frees), (n,ty)) =>
                    case find_first (fn (_,ty') => ty = ty') frees of
                      SOME (m,ty') => (((n,ty), (m,ty')) :: subst, remove (op =) (m,ty') frees)
                      | NONE => (subst, frees)) (([],frees),frees_schemes)
                      |> fst
                      |> map (apply2 Free)
      val terms = map (subst_free subst) terms
  in terms
        |> Seq.of_list
        |> discover_equations ctxt simps typsub tsubsts
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
fun equational_theory_exploration ctxt (table, typsub) size n lambda_size simps prop =
  let val thy = Proof_Context.theory_of ctxt
      val frees = extend_frees (table, typsub) prop
      fun monomorphize typ = (type_of o typsub) (Free ("x", typ))
      val tsubsts = frees
                     |> map (fn (n,ty) => (n, monomorphize ty))
                     |> substitutions' ctxt size n table
      val consts = Utils.definitional_dependencies thy ([], prop)
                    |> filter_out (fn (name, _) => name = Const_Names.hol_eq)
      val typ_args = map snd (consts @ frees)
      val target_typs = Type_Tab.keys table
      val target = hd target_typs
      val typ = typ_args ---> target
      val args = map Const consts @ map Free frees
      val _ = args |> map (Syntax.string_of_term ctxt)
                   |> commas
                   |> enclose "<" ">"
                   |> tracing
      val lambdas = Random_Terms.lazy_all_lambda_terms typ (lambda_size + length typ_args)
      val terms = lambdas |> Seq.map (fn t => betapplys (t, args))
                          |> Seq.list_of
                          |> Utils.make_term_set thy
                          |> Utils.sort_by_general thy
                          |> Seq.of_list
(*      fun check t s =
        let val eq = (t, s) |> HOLogic.mk_eq
                            |> HOLogic.mk_Trueprop
                            |> Utils.normalise_term ctxt (!simps)
        in if eq <> @{prop "True"}
           then SOME eq
           else NONE
        end
      fun check_eqs tab terms =
        case Seq.pull terms of
          SOME (t, terms) => 
              let val t' = typsub t
                  val key = map (fn subst => Utils.normalise_term ctxt (!simps) (subst t')) tsubsts
              in case Term_List_Tab.lookup tab key of
                  SOME ss => (case map_filter (check t) ss of
                              [] => check_eqs (Term_List_Tab.update (key, t::ss) tab) terms
                            | eqs  => let val (eqs,last) = split_last eqs
                             in Seq.append (Seq.of_list eqs)
                                      (Seq.make (fn () => SOME (last, check_eqs (Term_List_Tab.update (key, t::ss) tab) terms))) end)
                 | NONE => check_eqs (Term_List_Tab.update (key, [t]) tab) terms
              end
        | NONE => Seq.empty*)
  in discover_equations ctxt simps typsub tsubsts terms end
(*  in check_eqs Term_List_Tab.empty terms end*)

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
(*           |> (fn set => if null set
                         then [eq]
                         else 
                         let val set' = map Logic.varify_global set
                             fun subsumed'' eq =
                                exists (Pattern.matchess thy o pair [eq] o single) set' orelse
                                subsumed' eq
                         in maps (generalize_eq thy size n (tab, typsub) simps subsumed'') set end)
           |> Utils.make_term_set' thy*)
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

