theory Sorting
imports "IsaLibs/IsaLibs"
begin

section {* Multiplication on Natural Numbers *}

text {* This theory file shows how to find a function that multiplies natural numbers in Isabelle/HOL *}

text {* We first define the functional space.*}

fun insert where
"insert x [] = [x]"|
"insert x (y # xs) = (if x \<le> y
                      then x # y # xs
                      else y # insert x xs)"

fun sort where
"sort [] = []"|
"sort (x # xs) = insert x (sort xs)"

definition scheme where
"scheme P Q R \<equiv> \<exists>(f::int\<Rightarrow>int list\<Rightarrow>int list)
                  (g::int list\<Rightarrow>int list). 
                 \<forall>(x::int) (y::int) (xs::int list).
  ((f x [] = P x ([] :: int list) (op # :: int\<Rightarrow>int list\<Rightarrow>int list)) \<and>
   (f x (y # xs) = Q x y ([] :: int list) (op # :: int\<Rightarrow>int list\<Rightarrow>int list)
                     (\<lambda>x (y::int list) z. if x then y else z) (op \<le> :: int\<Rightarrow>int\<Rightarrow>bool) (f x xs)) \<and>
   (g [] = []) \<and>
   (g (x # xs) = R x y (f x) (g xs)))"

thm scheme_def

text {* We then define the fitness function as the quadratic error, the termination criterion,
  and other GP related parameters. The function we want to synthesise multiplication in terms of 
  addition of natural numbers.
*}

ML {*
  fun fitness ctxt consts =
    let val input1 = @{term "[5, 4, 3, 2, 1, 0::int]"}
        val input2 = @{term "[0, 1, 2, 3, 4, 5::int]"}
        val f = consts (* |> tap (map (tracing o fst)) *)
                       |> hd o tl
                       |> Const
        val sorted1 = f $ input1
                      |> Value.value ctxt
                      |> unenclose o (Utils.term_to_string ctxt)
                      |> space_explode ","
                      |> map (Utils.int_of_string o perhaps (try (unprefix " ")))
        val sorted2 = f $ input2
                      |> Value.value ctxt
                      |> unenclose o (Utils.term_to_string ctxt)
                      |> space_explode ","
                      |> map (Utils.int_of_string o perhaps (try (unprefix " ")))
        val error1 = map_index (fn (i, a) => let val d = i - a
                                            in d * d end) sorted1
        val error2 = map_index (fn (i, a) => let val d = i - a
                                            in d * d end) sorted2
    in if length error1 <> 21 orelse length error2 <> 21
       then Rat.rat_of_int 10000000
       else 
        (0, error1) |> Library.foldl (op +)
                    |> rpair error2
                    |> Library.foldl (op +)
                    |> Rat.rat_of_int end
  fun finish ({fit, ...} : GP.individual) = Rat.eq (Rat.zero, fit)
  fun test ctxt consts =
      consts |> fitness ctxt
             |> pair Rat.zero
             |> Rat.eq
  val term_size = 30
  val population_size = 100
  val generations = 200
  val bests = 10
  val mut_prob = 0.05
  val scheme = @{thm "scheme_def"}
*}

text {* We finally call the GP algorithm. *}

(*local_setup {*
 fn lthy => 
  case DB_EXHAUST.exhaust true lthy scheme term_size [] test of
    SOME (ctxt, t, trms) => 
      let val _ = map (tracing o (Syntax.string_of_term ctxt)) trms
      in ctxt end
  | NONE => lthy
*}*)
(*
local_setup {*
  fn lthy => 
  let val t = @{term "\<exists>f g. \<forall>(x::int). f x [] = [x, x, x, x] \<and>
          (\<forall>y xs. f x (y # xs) = y # y # x # f x xs \<and> g [] = [] \<and> g (x # xs) = f x (g xs))"}
  val df = DB_GP.defining_equations t
  val algo = try (DB_GP.mutual_function lthy) df
  val _ = map (tracing o Syntax.string_of_term lthy) (snd df)
  val ctxt = case algo of
            SOME lthy => (tracing "SOME"; lthy)
          | NONE => (tracing "NONE"; lthy)
  val ctxt = (case Function_Common.import_last_function ctxt of
                                   SOME info => (case #elims info of
                                                   SOME elims =>
                                                   (if DB_GP.is_partial elims
                                                    then (tracing "NONE"; NONE)
                                                    else (tracing "SOME"; SOME ctxt))
                                                 | NONE => NONE)
                                 | NONE => raise ERROR "Info of function not found!")
  in the ctxt end
*}

thm f.simps g.simps

ML {*
  val Const C = @{term "g"}
  val t = Const C $ @{term "[2,5,6,3,9,0,3,3::int]"}
  val r = Value.value @{context} t
(*  val r2 = Code_Evaluation.dynamic_value @{context} t*)
(*  val r3 = Code_Evaluation.dynamic_value_strict @{context} t*)
(*  val r = fitness @{context} [C, C]*)
*}*)


local_setup {*
 fn lthy => 
  case GP.evolve true false scheme lthy fitness finish term_size population_size generations bests mut_prob of
    SOME ind => (#ctxt ind)
  | NONE => lthy
*}

text {* Genome is composed by: 
@{term "\<lambda>x xa xb xc xd. xd"}
@{term "\<lambda>x xa xb. xb"}
@{term "\<lambda>x xa xb xc. xb"}
@{term "\<lambda>x xa xb. x"} *}

thm f.simps
thm g.simps

value "g [1, 2, 3, 4]"

text {* Invented functions are well-defined *}
lemma "scheme (\<lambda>x xa xb. x) (\<lambda>x xa xb xc. xb) (\<lambda>x xa xb. xb) (\<lambda>x xa xb xc xd. xd)"
apply (unfold scheme_def)
apply (rule_tac x="f" in exI)
apply (rule_tac x="g" in exI)
apply simp
done

end