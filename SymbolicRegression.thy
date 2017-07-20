theory SymbolicRegression
imports IsaLibs
begin

section{* Symbolic Regression *}

text {* This theory file shows how to perform symbolic regression in Isabelle/HOL *}

text {* We first define the functional space.*}

definition scheme where
"scheme P \<equiv> \<exists>f::int\<Rightarrow>int. \<forall>x::int. 
  (f x = P x (1::int)
             (\<lambda>x. x + (1::int))
             (op + :: int\<Rightarrow>int\<Rightarrow>int)
             (op - :: int\<Rightarrow>int\<Rightarrow>int)
             (op * :: int\<Rightarrow>int\<Rightarrow>int))"

text {* We then define the fitness function as the quadratic error, the termination criterion,
  and other GP related parameters. The function we want to synthesise is @{term " 2 * x * x - x + 5"}.
*}

ML {*
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
*}

text {* We finally call the GP algorithm. *}

local_setup {*
 fn lthy => 
  case GP.evolve false scheme lthy fitness finish term_size population_size generations bests mut_prob of
    SOME ind => (#ctxt ind)
  | NONE => lthy
*}

thm f.simps

end