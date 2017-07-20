theory Addition
imports IsaLibs
begin

section {* Addition on Natural Numbers *}

text {* This theory file shows how to find a function that adds natural numbers in Isabelle/HOL *}

text {* We first define the functional space.*}

definition scheme where
"scheme P Q \<equiv> \<exists>f::nat\<Rightarrow>nat\<Rightarrow>nat. \<forall>(x::nat) (y::nat).
  ((f 0 y = P y Suc (0::nat)) \<and>
   (f (Suc x) y = Q x y Suc (0::nat) (f x)))"

thm scheme_def

text {* We then define the fitness function as the quadratic error, the termination criterion,
  and other GP related parameters. The function we want to synthesise is addition of natural numbers.
*}

ML {*
  fun fitness ctxt consts =
    let fun goal x y = x + y
        val f = consts |> hd
                       |> Const
        val xs = 0 upto 9
        val xs' = 1 upto (Utils.binomial_coefficient 10 2 - 1)
                    |> map (Utils.choose xs 2)
                    |> map (fn l => case l of
                                      [x,y] => (x,y)
                                    | _ => raise ERROR "")
        val ys = map (fn (x,y) => goal x y) xs'
        val rs = map (fn (x,y) => (f $ Utils.numeral_of_nat ctxt x $ Utils.numeral_of_nat ctxt y)
                                |> (fn t => @{term "num_of_nat"} $ t)
                                |> Value.value ctxt
                                |> (fn t => @{term "numeral :: num\<Rightarrow>nat"} $ t)
                                |> Utils.int_of_numeral) xs'
        val ds = map2 (fn x => fn y => (x - y) * (x - y)) ys rs
    in (0, ds) |> Library.foldl (op +)
               |> Rat.rat_of_int end
  fun finish ({fit, ...} : GP.individual) = Rat.eq (Rat.zero, fit)
  val term_size = 23
  val population_size = 100
  val generations = 200
  val bests = 10
  val mut_prob = 0.05
  val scheme = @{thm "scheme_def"}
*}

text {* We finally call the GP algorithm. *}

local_setup {*
 fn lthy => .
  case GP.evolve false scheme lthy fitness finish term_size population_size generations bests mut_prob of
    SOME ind => (#ctxt ind)
  | NONE => lthy
*}

thm f.simps

end