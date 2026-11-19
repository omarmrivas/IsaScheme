theory SymbolicRegression
imports IsaLibs
begin

section\<open> Symbolic Regression \<close>

text \<open> This theory file shows how to perform symbolic regression in Isabelle/HOL \<close>

text \<open> We first define the functional space.\<close>

definition scheme where
"scheme P \<equiv> \<exists>f::int\<Rightarrow>int. \<forall>x::int. 
  (f x = P x (1::int)
             (\<lambda>x. x + (1::int))
             ((+) :: int\<Rightarrow>int\<Rightarrow>int)
             ((-) :: int\<Rightarrow>int\<Rightarrow>int)
             ((*) :: int\<Rightarrow>int\<Rightarrow>int))"

text \<open> We then define the fitness function as the quadratic error, the termination criterion,
  and other GP related parameters. The function we want to synthesise is @{term " 2 * x * x - x + 5"}.
\<close>

ML \<open>
  fun fitness ctxt consts =
    let fun goal x = 2 * x * x - x + 5
        val f = consts |> hd
                       |> Const
        val xs = 0 upto 10
        val ys = map goal xs
        val rs = map (fn i => (f $ Utils.numeral_of_int ctxt i)
                                |> Value.value ctxt
                                |> Utils.int_of_numeral) xs
        val ds = map2 (fn x => fn y => (x - y) * (x - y)) ys rs
    in (0, ds) |> Library.foldl (op +)
               |> Rat.rat_of_int end
  fun finish ({fit, ...} : GP.individual) = Rat.eq (Rat.zero, fit)
  val term_size = 33
  val population_size = 200
  val generations = 200
  val bests = 10
  val mut_prob = 0.05
  val scheme = @{thm "scheme_def"}
\<close>

text \<open> We finally call the GP algorithm. \<close>

local_setup \<open>
 fn lthy => 
  case GP.evolve false scheme lthy fitness finish term_size population_size generations bests mut_prob of
    SOME ind => (#ctxt ind)
  | NONE => lthy
\<close>

thm f.simps

end