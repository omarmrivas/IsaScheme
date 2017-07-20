theory Abalone
imports "IsaLibs/IsaLibs"
begin

section {* Abalone *}

declare [[max_time_in_fitness = 1200]]

text {* This theory file shows how to find a function that adds the elements of a list of natural 
numbers in Isabelle/HOL. *}

subsection {* Destructor style functional scheme *}

text {* We first define the functional space of a destructor style functional scheme. *}

datatype sex = M | F | I

definition scheme_dest where
"scheme_dest N \<equiv> \<exists>(f::sex\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real).
                 \<forall>(sex::sex) (length::real) (diameter::real) (height::real)
                  (whole::real) (shucked::real) (viscera::real) (shell::real).
  f sex length diameter height whole shucked viscera shell = N sex length diameter height whole shucked viscera shell
           (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::sex) (z::real) w. (case x = y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
           M
           F
           I
           f"

text {* Now we get the terminating closure of the destructor style functional scheme. *}

definition terminating_closure_scheme_dest where
"terminating_closure_scheme_dest N \<equiv> \<exists>f.
                 \<forall>(sex::sex) (length::real) (diameter::real) (height::real)
                  (whole::real) (shucked::real) (viscera::real) (shell::real) (c\<^sub>f::nat) (v\<^sub>f::real).
  ((f N 0 v\<^sub>f sex length diameter height whole shucked viscera shell = v\<^sub>f) \<and>
   (f N (Suc c\<^sub>f) v\<^sub>f sex length diameter height whole shucked viscera shell) = N sex length diameter height whole shucked viscera shell
           (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::sex) (z::real) w. (case x = y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
           M
           F
           I
           (f N c\<^sub>f v\<^sub>f))"

text {* All individuals generated by @{term "terminating_closure_scheme_dest"}
  are terminating, regardless the value of @{term "N"}. The proof will need 
  the witness @{term "f\<^sub>d"} which we define below. *}

fun f\<^sub>d where
"f\<^sub>d N (0::nat) v\<^sub>f (sex::sex) (len::real) (diameter::real) (height::real) (whole::real) (shucked::real) (viscera::real) (shell::real) = (v\<^sub>f::real)" |
"f\<^sub>d N (Suc c\<^sub>f) v\<^sub>f (sex::sex) (len::real) (diameter::real) (height::real) (whole::real) (shucked::real) (viscera::real) (shell::real) = N sex len diameter height whole shucked viscera shell
           (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::sex) (z::real) w. (case x = y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
           M
           F
           I
           (f\<^sub>d N c\<^sub>f v\<^sub>f)"

text {* Proof. *}

theorem "terminating_closure_scheme_dest N"
apply (unfold terminating_closure_scheme_dest_def)
by (rule_tac x="f\<^sub>d" in exI, simp)

subsection {* Constructor style functional scheme *}

text {* Now we define the functional space of a constructor style functional scheme. *}

definition scheme_const where
"scheme_const N1 N2 N3 \<equiv> \<exists>(f::sex\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>real).
                 \<forall>(length::real) (diameter::real) (height::real)
                  (whole::real) (shucked::real) (viscera::real) (shell::real).
  (f M length diameter height whole shucked viscera shell = N1 M length diameter height whole shucked viscera shell
           (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
           f) \<and>
  (f F length diameter height whole shucked viscera shell = N2 F length diameter height whole shucked viscera shell
           (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
           f) \<and>
  (f I length diameter height whole shucked viscera shell = N3 I length diameter height whole shucked viscera shell
           (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
           f)"

text {* Now we get the terminating closure of the constructor style functional scheme. *}

definition terminating_closure_scheme_const where
"terminating_closure_scheme_const N1 N2 N3 \<equiv> \<exists>f.
                 \<forall>(length::real) (diameter::real) (height::real)
                  (whole::real) (shucked::real) (viscera::real) (shell::real) c\<^sub>f (v\<^sub>f::real).
  (f N1 N2 N3 0 v\<^sub>f M length diameter height whole shucked viscera shell = v\<^sub>f) \<and>
  (f N1 N2 N3 (Suc c\<^sub>f) v\<^sub>f M length diameter height whole shucked viscera shell = (N1 M length diameter height whole shucked viscera shell
                    (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
                    (f N1 N2 N3 c\<^sub>f v\<^sub>f))) \<and>
  (f N1 N2 N3 (Suc c\<^sub>f) v\<^sub>f F length diameter height whole shucked viscera shell = (N2 F length diameter height whole shucked viscera shell
                    (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
                    (f N1 N2 N3 c\<^sub>f v\<^sub>f))) \<and>
  (f N1 N2 N3 (Suc c\<^sub>f) v\<^sub>f I length diameter height whole shucked viscera shell = (N3 I length diameter height whole shucked viscera shell
                    (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
                    (f N1 N2 N3 c\<^sub>f v\<^sub>f)))"

text {* All individuals generated by @{term "terminating_closure_scheme_const"}
  are terminating, regardless the value of @{term "N"}. The proof will need 
  the witness @{term "f\<^sub>c"} which we define below. *}

fun f\<^sub>c where
"f\<^sub>c N1 N2 N3 0 v\<^sub>f (sex::sex) (len::real) (diameter::real) (height::real) (whole::real) (shucked::real) (viscera::real) (shell::real) = (v\<^sub>f::real)" |
"f\<^sub>c N1 N2 N3 (Suc c\<^sub>f) v\<^sub>f M (len::real) (diameter::real) (height::real) (whole::real) (shucked::real) (viscera::real) (shell::real) = (N1 M len diameter height whole shucked viscera shell
                    (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
                    (f\<^sub>c N1 N2 N3 c\<^sub>f v\<^sub>f))"|
"f\<^sub>c N1 N2 N3 (Suc c\<^sub>f) v\<^sub>f F (len::real) (diameter::real) (height::real) (whole::real) (shucked::real) (viscera::real) (shell::real) = (N2 F len diameter height whole shucked viscera shell
                    (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
                    (f\<^sub>c N1 N2 N3 c\<^sub>f v\<^sub>f))"|
"f\<^sub>c N1 N2 N3 (Suc c\<^sub>f) v\<^sub>f I (len::real) (diameter::real) (height::real) (whole::real) (shucked::real) (viscera::real) (shell::real) = (N3 I len diameter height whole shucked viscera shell
                    (\<lambda>x (y::real) (z::real) w. (case x < y of True \<Rightarrow> z | _ \<Rightarrow> w))
           (\<lambda>x (y::real). x + y)
           (\<lambda>x (y::real). x - y)
           (\<lambda>x (y::real). x * y)
           (\<lambda>x (y::real). x / y)
                    (f\<^sub>c N1 N2 N3 c\<^sub>f v\<^sub>f))"

text {* Proof. *}

theorem "terminating_closure_scheme_const N1 N2 N3"
apply (unfold terminating_closure_scheme_const_def)
by (rule_tac x="f\<^sub>c" in exI, simp)

subsection {* Evaluation of the Evolve algorithm. *}

text {* We define the fitness function, the termination criterion,
  and other GP related parameters.
*}

ML {*
  fun my_trim str =
    if can (unsuffix " ") str
    then (if can (unprefix " ") str
         then my_trim (unprefix " " (unsuffix " " str))
         else my_trim (unsuffix " " str))
    else (if can (unprefix " ") str
         then my_trim (unprefix " " str)
         else str)
  fun real_str_to_rat str =
    str |> space_explode "/"
        |> map (Rat.rat_of_int o Utils.int_of_string o my_trim)
        |> (fn l => let val h = hd l
                    in
                    Library.foldl (fn (r,i) => i |> Rat.inv
                                                 |> Rat.mult r
                                                 handle Rat.DIVZERO => (tracing str; r)) (Rat.mult h h, l)
                    end)
  val ctxt = @{context}
  val data = ML_Database.load_file ctxt [ML_Database.String,
                                               ML_Database.Real,
                                               ML_Database.Real,
                                               ML_Database.Real,
                                               ML_Database.Real,
                                               ML_Database.Real,
                                               ML_Database.Real,
                                               ML_Database.Real,
                                               ML_Database.Real]
                                               "/Users/omarmrivas/Programs/IsaLibs/experiments/machine_learning/abalone.data"
              |> take 3133
              |> map (fn h :: tl => if h = Syntax.read_term ctxt "''M'' :: string"
                                    then @{term "M"} :: tl
                                    else if h = Syntax.read_term ctxt "''F'' :: string"
                                    then @{term "F"} :: tl
                                    else if h = Syntax.read_term ctxt "''I'' :: string"
                                    then @{term "I"} :: tl
                                    else raise ERROR "Error"
                      | _ => raise ERROR "Error")
              |> map split_last

  val minus = @{term "\<lambda>x (y::real). x - y"}
  val abss = @{term "abs :: real\<Rightarrow>real"}

  fun fitness ctxt functions =
    let val in_out = data
        val rec_counter = @{term "10::nat"}
        val vf = @{term "9 :: real"}
        val f = hd functions
        val error = 
          in_out |> Par_List.map (fn (xs,r) => list_comb (f $ rec_counter $ vf, xs)
                                        |> (fn x => (Value.value ctxt (abss $ (minus $ x $ r)))))
                 |> map (Rat.abs o real_str_to_rat o (Utils.string_of_term ctxt))
    in (Rat.zero, error) |> Library.foldl (fn (x,y) => Rat.add x y) end
  fun finish ({fit, ...} : GP.individual) = case fit of
                                              SOME fit => Rat.eq (Rat.zero, fit)
                                            | NONE => false
  fun test ctxt consts =
      consts |> fitness ctxt
             |> (fn r => Rat.lt r (Rat.rat_of_int 1880))
  val term_size = 30
  val max_term_size_dest = 40
  val max_term_size_const = 40
  val population_size = 500
  val generations = 500
  val bests = 10
  val mut_prob = 0.05
  val scheme_dest = @{thm "scheme_dest_def"}
  val scheme_const = @{thm "scheme_const_def"}
  val functions_dest = [@{term "f\<^sub>d"}]
  val functions_const = [@{term "f\<^sub>c"}]
  val experiments = 20
  val recursive_calls = 1
  val bad_fitness = Rat.rat_of_int 100000
*}

text {* We finally call the Evolve algorithm. *}

(*ML {*
  val f = @{term "f\<^sub>c (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm. xj xe (xk xg xb)) (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm. xi xg (xj xc xg)) (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm. xb)"}
  val ff = fitness ctxt [f]
*}*)

local_setup {*
 fn lthy =>
    let val experiment = GP.evolve false true false "AbaloneConsts.log" scheme_const functions_const recursive_calls bad_fitness lthy fitness finish
                                   term_size max_term_size_const population_size generations bests mut_prob
        val _ = MySQL.new_experiment "AbaloneConsts" generations term_size population_size experiment
    in lthy end
*}

local_setup {*
 fn lthy =>
    let val experiment = GP.evolve false false false "AbaloneDest.log" scheme_dest functions_dest recursive_calls bad_fitness lthy fitness finish
                                   term_size max_term_size_dest population_size generations bests mut_prob
        val _ = MySQL.new_experiment "AbaloneDest" generations term_size population_size experiment
    in lthy end
*}

end