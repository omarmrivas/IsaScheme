(*  Title:      util/gnuplot.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Production of GNU Plot Files.
*)

signature MYSQL =
sig

val real_ref : real option Unsynchronized.ref
val genome_ref : term list option Unsynchronized.ref
val subst_ref : GP.subst option  Unsynchronized.ref
val norm_ref : term option Unsynchronized.ref
val fit_ref : (int * int) option Unsynchronized.ref

val new_experiment :  string -> int -> int -> int -> GP.gp_result -> unit
val get_last_experiments : Proof.context -> int -> string -> GP.gp_result list

end

structure DB_MYSQL
(* : MYSQL *)
= struct

open GP

val real_ref = Unsynchronized.ref (NONE : real option)
val genome_ref = Unsynchronized.ref (NONE : term list option)
val subst_ref = Unsynchronized.ref (NONE : subst option)
val norm_ref = Unsynchronized.ref (NONE : term option)
val fit_ref = Unsynchronized.ref (NONE : (int * int) option)

fun evaluate r name expression =
  let val flags = ML_Compiler.flags
      val tokens = ML_Lex.read (name ^ " := SOME (" ^ expression ^ ")")
      val pos = Position.none
      val _ = ML_Context.eval flags pos tokens
  in the (!r) end

fun evaluate_real str =
  if match_string "." str
  then evaluate real_ref "MySQL.real_ref" str
  else evaluate real_ref "MySQL.real_ref" (str ^ ".0")
val evaluate_genome = evaluate genome_ref "MySQL.genome_ref"
val evaluate_subst = evaluate subst_ref "MySQL.subst_ref"
val evaluate_norm = evaluate norm_ref "MySQL.norm_ref"
val evaluate_fit = evaluate fit_ref "MySQL.fit_ref"

(*fun evaluate r expression =
  let val vv = Unsynchronized.ref (!r)
      val flags = ML_Compiler.flags
      val tokens = ML_Lex.read ("vv = SOME (" ^ expression ^ ")")
      val pos = Position.none
      val _ = ML_Context.eval flags pos tokens
  in the (!vv) end*)

fun escape_string str =
  let fun escape c =
        case c of
            #"\"" => [#"\\", #"\""]
          | #"'" => [#"#"]
          | c => single c
  in
    str |> String.explode
        |> maps escape
        |> String.implode
  end

fun descape_string str =
  let fun escape c =
        case c of
            #"#" => [#"'"]
          | c => single c
  in
    str |> String.explode
        |> maps escape
        |> String.implode
  end

fun get_max_id table WHERE =
  let val max_id = "SELECT MAX(id) FROM " ^ table ^ " " ^ WHERE
  in ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ max_id ^ "' isalibs")
      |> Isabelle_System.bash_output
      |> fst
      |> space_explode "\n"
      |> (hd o tl)
      |> Utils.int_of_string
  end

fun search_individual ctxt id : individual option =
  let val id_str = string_of_int id
      val search_individual = "SELECT * FROM `individuals` WHERE `id`="^ id_str
      val result = ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ search_individual ^ "' isalibs")
                    |> Isabelle_System.bash_output
                    |> fst
  in if result = ""
     then NONE
     else result |> space_explode "\n"
                 |> (hd o tl)
                 |> space_explode "\t"
                 |> map descape_string
                 |> (fn l => case l of
                                [_, genome, subst, norm, _, fit] =>
                                 {ctxt = ctxt,
                                   genome = evaluate_genome genome,
                                   subst = evaluate_subst subst,
                                   norm = evaluate_norm norm,
                                   fit = SOME (Rat.make (evaluate_fit fit))}
                              | _ => raise ERROR "Error search_individual")
                 |> SOME
  end

fun insert_individual (individual : individual) =
  let val genome_str = escape_string (ML_Syntax.print_list ML_Syntax.print_term (#genome individual))
      val typs = ML_Syntax.print_list (ML_Syntax.print_pair ML_Syntax.print_typ ML_Syntax.print_typ)
      val terms = ML_Syntax.print_list (ML_Syntax.print_pair ML_Syntax.print_term ML_Syntax.print_term)
      val subst_str = escape_string (ML_Syntax.print_pair typs terms (#subst individual))
      val norm_str = escape_string (ML_Syntax.print_term (#norm individual))
      val norm_hash = (string_of_int o ATP_Util.hash_string) norm_str
      val fit_str = escape_string (((ML_Syntax.print_pair ML_Syntax.print_int ML_Syntax.print_int) o Rat.dest) ((the o #fit) individual))
      val insert_individual = "INSERT INTO `individuals`(`genome`, `subst`, `norm`, `hash`, `fit`) VALUES (\"" ^genome_str^ "\",\"" ^ subst_str ^"\",\"" ^ norm_str ^ "\",\"" ^ norm_hash ^ "\",\""^fit_str^"\")"
      val _ = Isabelle_System.bash_output ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ insert_individual ^ "' isalibs")
  in (#norm individual, get_max_id "individuals" ("WHERE hash=\"" ^ norm_hash ^ "\"")) end

fun insert_statistics m experiment (statistic : gp_statistic) =
  let val best = (the o (Term_Tab.lookup m) o #norm) (#best_individual statistic)
      val best_str = string_of_int best
      val size_str = string_of_real (#average_size statistic)
      val error_str = string_of_real (#average_error statistic)
      val equals_str = string_of_int (#equals statistic)
      val experiment_str = string_of_int experiment
      val insert_statistics = "INSERT INTO `statistics`(`best`, `average_size`, `average_error`, `equals`, `experiment`) VALUES (" ^best_str^ "," ^ size_str ^"," ^ error_str ^ ","^equals_str^","^experiment_str ^ ")"
      val _ = Isabelle_System.bash_output ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ insert_statistics ^ "' isalibs")
  in () end

fun insert_experiment solution thy_name generations termsize population hash =
  let val solution_str = case solution of
                          SOME solution => string_of_int solution
                        | NONE => "-1"
      val generations_str = string_of_int generations
      val termsize_str = string_of_int termsize
      val population_str = string_of_int population
      val insert_experiment = "INSERT INTO `experiments`(`solution`, `theory`, `generations`, `termsize`, `population`, `hash`) VALUES (" ^solution_str^ ",\"" ^ thy_name ^"\"," ^ generations_str ^ ","^termsize_str^","^population_str ^ ",\"" ^ hash ^ "\"" ^ ")"
      val _ = Isabelle_System.bash_output ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ insert_experiment ^ "' isalibs")
  in get_max_id "experiments" ("WHERE hash=\"" ^ hash ^ "\"") end

fun hash_experiment (Solved (ind, statistics)) =
  ind :: map #best_individual statistics
    |> pair 0
    |> Library.foldl (fn (hash, ind) => let val norm_str = escape_string (ML_Syntax.print_term (#norm ind))
                                        in hash + ATP_Util.hash_string norm_str end)
    |> string_of_int
    |> ATP_Util.hash_string
    |> string_of_int
  | hash_experiment (Unsolved (statistics)) =
    map #best_individual statistics
    |> pair 0
    |> Library.foldl (fn (hash, ind) => let val norm_str = escape_string (ML_Syntax.print_term (#norm ind))
                                        in hash + ATP_Util.hash_string norm_str end)
    |> string_of_int
    |> ATP_Util.hash_string
    |> string_of_int

fun new_experiment thy_name generations termsize population (Solved (ind, statistics)) =
  let val individuals = ind :: map #best_individual statistics
                          |> distinct (fn (ind1, ind2) => Term.aconv (#norm ind1, #norm ind2))
                          |> map insert_individual
                          |> Term_Tab.make
      val hash = hash_experiment (Solved (ind, statistics))
      val experiment_id = insert_experiment (SOME ((the o (Term_Tab.lookup individuals) o #norm) ind)) thy_name generations termsize population hash
      val _ = map (insert_statistics individuals experiment_id) statistics
  in () end
  | new_experiment thy_name generations termsize population (Unsolved (statistics)) =
  let val individuals = map #best_individual statistics
                          |> distinct (fn (ind1, ind2) => Term.aconv (#norm ind1, #norm ind2))
                          |> map insert_individual
                          |> Term_Tab.make
      val hash = hash_experiment (Unsolved (statistics))
      val experiment_id = insert_experiment NONE thy_name generations termsize population hash
      val _ = map (insert_statistics individuals experiment_id) statistics
  in () end

fun get_statistics ctxt experiment : gp_statistic list =
  let val id_str = string_of_int experiment
      val search_experiments = "SELECT * FROM `statistics` WHERE `experiment`="^ id_str
      val result = ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ search_experiments ^ "' isalibs")
                    |> Isabelle_System.bash_output
                    |> fst
  in
    result |> space_explode "\n"
           |> map (space_explode "\t")
           |> map (map descape_string)
           |> filter (fn l => not (null l))
           |> (fn l => if null l then []
                       else tl l)
           |> (fn l => let val tab = l |> map (fn [_, best, _, _, _, _] =>
                                                  Utils.int_of_string best
                                               | _ => raise ERROR "Error get_statistics")
                                       |> Int_Tab.make_set
                                       |> Int_Tab.keys
                                       |> map (fn i => (i, the (search_individual ctxt i)))
                                       |> Int_Tab.make
                       in map (fn l => case l of
                        [_, best, average_size, average_error, equals, _] =>
                        {best_individual = the (Int_Tab.lookup tab (Utils.int_of_string best)),
                            average_size = evaluate_real average_size,
                            average_error = evaluate_real average_error,
                            equals = Utils.int_of_string equals}
                      | _ => raise ERROR "Error get_statistics") l end)
  end

fun get_last_experiments ctxt n thy_name =
  let val n_str = string_of_int n
      val search_experiments = "SELECT * FROM `experiments` WHERE `theory`=\""^ thy_name ^"\" ORDER BY time DESC limit " ^ n_str
      val result = ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ search_experiments ^ "' isalibs")
                    |> Isabelle_System.bash_output
                    |> fst
  in
    result |> space_explode "\n"
           |> map (space_explode "\t")
           |> map (map descape_string)
           |> filter (fn l => not (null l))
           |> (fn l => if null l then []
                       else tl l)
           |> map (fn l => case l of
                        [id, solution, _, _, _, _, _, _] =>
                            let val solution' = Utils.int_of_string solution
                                val id = Utils.int_of_string id
                            in if solution = "-1"
                               then id |> get_statistics ctxt
                                       |> Unsolved
                               else id |> get_statistics ctxt
                                       |> pair (the (search_individual ctxt solution'))
                                       |> Solved
                            end
                      | _ => raise ERROR "Error get_last_experiments")
  end

end

structure MySQL : MYSQL = DB_MYSQL

