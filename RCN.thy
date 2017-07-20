theory RCN
imports "IsaLibs/IsaLibs"
begin

section {* RCN *}

declare [[max_time_in_fitness = 120]]

text {* This theory file shows how to find a function that adds the elements of a list of natural 
numbers in Isabelle/HOL. *}

subsection {* Destructor style functional scheme *}

text {* We first define the functional space of a destructor style functional scheme. *}

type_synonym vect = "real * real * real"

term "to_real :: nat\<Rightarrow>real"

definition proyx :: "vect\<Rightarrow>real" where
"proyx V = (let (x,y,z) = V in
           x)"

definition proyy :: "vect\<Rightarrow>real" where
"proyy V = (let (x,y,z) = V in
           y)"

definition proyz :: "vect\<Rightarrow>real" where
"proyz V = (let (x,y,z) = V in
           z)"

definition to_vect :: "real\<Rightarrow>real\<Rightarrow>real\<Rightarrow>vect" where
"to_vect x y z = (x, y, z)"

definition vadd :: "vect\<Rightarrow>vect\<Rightarrow>vect" where
"vadd X Y = (let (x,y,z) = X in
             let (p,q,w) = Y in
             (x+p, y+q, z+w))"

definition vsub :: "vect\<Rightarrow>vect\<Rightarrow>vect" where
"vsub X Y = (let (x,y,z) = X in
             let (p,q,w) = Y in
             (x-p, y-q, z-w))"

definition vprod :: "real\<Rightarrow>vect\<Rightarrow>vect" where
"vprod c V = (let (x,y,z) = V in
             (c*x, c*y, c*z))"

definition vdot :: "vect\<Rightarrow>vect\<Rightarrow>real" where
"vdot X Y = (let (x,y,z) = X in
             let (p,q,w) = Y in
             x*p + y*q + z*w)"

definition vcross :: "vect\<Rightarrow>vect\<Rightarrow>vect" where
"vcross X Y = (let (x,y,z) = X in
             let (p,q,w) = Y in
             (y*w-z*q, x*w-z*p, x*q-y*p))"

definition vmag :: "vect\<Rightarrow>real" where
"vmag V = (let (x,y,z) = V in
          x*x+y*y+z*z)"

fun nat_to_real where
"nat_to_real 0 = (0.0::real)"|
"nat_to_real (Suc n) = 1 + nat_to_real n"

definition scheme where
"scheme P Q R \<equiv> \<exists>w1 w2 w3 f.
            \<forall>(n::nat) (v1::vect) (v2::vect) (v3::vect) (v::vect).
  ((w1 P Q R 0 v1 v2 v3 = [v1]) \<and>
   (w1 P Q R (Suc n) v1 v2 v3 = (let (L::vect list) = w3 P Q R n v1 v2 v3 in
                           let (X::vect) = P (nat_to_real (Suc n)) v1 v2 v3
                                       proyx
                                       proyy
                                       proyz
                                       to_vect
                                       vadd
                                       vsub
                                       vprod
                                       vdot
                                       vcross
                                       vmag
                                       (hd L)
                           in X # L)) \<and>
   (w2 P Q R 0 v1 v2 v3 = [v1]) \<and>
   (w2 P Q R (Suc 0) v1 v2 v3 = [v1, v2]) \<and>
   (w2 P Q R (Suc (Suc n)) v1 v2 v3 = (let (L::vect list) = w1 P Q R (Suc n) v1 v2 v3 in
                           let (X::vect) = Q (nat_to_real (Suc (Suc n))) v1 v2 v3
                                       proyx
                                       proyy
                                       proyz
                                       to_vect
                                       vadd
                                       vsub
                                       vprod
                                       vdot
                                       vcross
                                       vmag
                                       (hd L)
                           in X # L)) \<and>
   (w3 P Q R 0 v1 v2 v3 = [v1]) \<and>
   (w3 P Q R (Suc 0) v1 v2 v3 = [v1, v2]) \<and>
   (w3 P Q R (Suc (Suc 0)) v1 v2 v3 = [v1, v2, v3]) \<and>
   (w3 P Q R (Suc (Suc (Suc n))) v1 v2 v3 = (let (L::vect list) = w2 P Q R (Suc (Suc n)) v1 v2 v3 in
                           let (X::vect) = R (nat_to_real (Suc (Suc (Suc n)))) v1 v2 v3
                                       proyx
                                       proyy
                                       proyz
                                       to_vect
                                       vadd
                                       vsub
                                       vprod
                                       vdot
                                       vcross
                                       vmag
                                       (hd L)
                           in X # L)) \<and>
   (f P Q R n v1 v2 v3 = (let r = n mod 3 in
                    if r = 0
                    then w1 P Q R n v1 v2 v3
                    else if r = 1
                    then w2 P Q R n v1 v2 v3
                    else w3 P Q R n v1 v2 v3)))"

function w1 and w2 and w3 and f where
"w1 P Q R 0 v1 v2 v3 = [v1]" |
"w1 P Q R (Suc n) v1 v2 v3 = (let (L::vect list) = w3 P Q R n v1 v2 v3 in
                        let (X::vect) = P (nat_to_real (Suc n)) v1 v2 v3
                                       proyx
                                       proyy
                                       proyz
                                       to_vect
                                       vadd
                                       vsub
                                       vprod
                                       vdot
                                       vcross
                                       vmag
                                       (hd L)
                           in X # L)" |
"w2 P Q R 0 v1 v2 v3 = [v1]" |
"w2 P Q R (Suc 0) v1 v2 v3 = [v1, v2]" |
"w2 P Q R (Suc (Suc n)) v1 v2 v3 = (let (L::vect list) = w1 P Q R (Suc n) v1 v2 v3 in
                        let (X::vect) = Q (nat_to_real (Suc (Suc n))) v1 v2 v3
                                       proyx
                                       proyy
                                       proyz
                                       to_vect
                                       vadd
                                       vsub
                                       vprod
                                       vdot
                                       vcross
                                       vmag
                                       (hd L)
                           in X # L)" |
"w3 P Q R 0 v1 v2 v3 = [v1]" |
"w3 P Q R (Suc 0) v1 v2 v3 = [v1, v2]" |
"w3 P Q R (Suc (Suc 0)) v1 v2 v3 = [v1, v2, v3]" |
"w3 P Q R (Suc (Suc (Suc n))) v1 v2 v3 = (let (L::vect list) = w2 P Q R (Suc (Suc n)) v1 v2 v3 in
                        let (X::vect) = R (nat_to_real (Suc (Suc (Suc n)))) v1 v2 v3
                                       proyx
                                       proyy
                                       proyz
                                       to_vect
                                       vadd
                                       vsub
                                       vprod
                                       vdot
                                       vcross
                                       vmag
                                       (hd L)
                           in X # L)" |
"f P Q R n v1 v2 v3 = (let r = n mod 3 in
                    if r = 0
                    then w1 P Q R n v1 v2 v3
                    else if r = 1
                    then w2 P Q R n v1 v2 v3
                    else w3 P Q R n v1 v2 v3)"
by pat_completeness auto
termination by size_change

text {* Proof. *}

theorem "scheme P Q R"
apply (unfold scheme_def)
apply (rule_tac x="w1" in exI)
apply (rule_tac x="w2" in exI)
apply (rule_tac x="w3" in exI)
apply (rule_tac x="f" in exI)
by simp

subsection {* Evaluation of the Evolve algorithm. *}

text {* We define the fitness function, the termination criterion,
  and other GP related parameters.
*}

ML {*
  val points_k6 =
    [(31913,      61624),
     (    0,      39366),
     (13197,      35824),
     (49018,          0),
     (27438,      48183),
     (34377,      27824)]
  val points_k2 = [(0, 0), (1, 0)]
  val points_k4 =
     [(    0,      16865),
     (41470,      13435),
     ( 2213,          0),
     (24229,      14674)]

  val graph = points_k6 |> map (fn (x, y) => (Rat.rat_of_int x, Rat.rat_of_int y))
                        |> DB_Rectilinear.construct_graph
  val SOME (DB_Rectilinear.PGraph {crossing_number, ...}) = graph
  fun cross_number (SOME (DB_Rectilinear.PGraph {crossing_number, ...})) = crossing_number
    | cross_number _ = 14634570
*}

ML {*
  val ctxt = @{context}
  val data = [(@{term "5::nat"}, 3),
              (@{term "8::nat"}, 36),
              (@{term "11::nat"}, 153),
              (@{term "14::nat"}, 447)(*,
              (@{term "17::nat"}, 1029),
              (@{term "20::nat"}, 2055)*)]
(*  val v1 = @{term "(1,1,1)::vect"}
  val v2 = @{term "(-1,1,-1)::vect"}
  val v3 = Value.value ctxt (@{term "vcross"} $ v1 $ v2)(*@{term "(1,-1,-1)::vect"}*)*)
  val v1 = @{term "(1,0,0)::vect"}
  val v2 = @{term "(0,1,0)::vect"}
  val v3 = @{term "(0,0,1)::vect"}
  fun to_rat_vect [x,y,z] = (Utils.rat_of_numeral x, Utils.rat_of_numeral y, Utils.rat_of_numeral z)
    | to_rat_vect _ = raise ERROR "Invalid vect!"
  fun get_crossing_number l = 
    let val xy = map (fn (x,y,_) => (x, y)) l
        val xz = map (fn (x,_,z) => (x, z)) l
        val yz = map (fn (_,y,z) => (y, z)) l
        val l = [xy, xz, yz]
                      |> map_filter DB_Rectilinear.construct_graph
                      |> map (fn (DB_Rectilinear.PGraph {crossing_number, ...}) => crossing_number)
    in case l of
          [] => 14634570
        | l => Utils.minby int_ord (fn x => x) l
    end
(*    in case DB_Rectilinear.construct_graph xy of
        (SOME (DB_Rectilinear.PGraph {crossing_number, ...})) => crossing_number
      | _ => case DB_Rectilinear.construct_graph xz of
              (SOME (DB_Rectilinear.PGraph {crossing_number, ...})) => crossing_number
            | _ => case DB_Rectilinear.construct_graph yz of
                (SOME (DB_Rectilinear.PGraph {crossing_number, ...})) => crossing_number
              | _ => 14634570 end*)
  fun fitness ctxt [_, _, _, f] =
    let val in_out = data
        val error = 
          in_out |> map (fn (n,_) => Value.value ctxt (f $ n $ v1 $ v2 $ v3))
                 |> map (get_crossing_number o (map (to_rat_vect o Utils.elements_of_product_type)) o Utils.elements_of_list)
                 |> map2 (fn (_, x) => fn y => let val d = x - y
                                            in abs d end) data
                 |> pair 0
                 |> Library.foldl (fn (s, e) => s + e)
                 |> Rat.rat_of_int
    in error end
    | fitness _ _ = raise ERROR "Error in fitness"
  fun finish ({fit, ...} : GP.individual) = case fit of
                                              SOME fit => Rat.eq (Rat.zero, fit)
                                            | NONE => false
  fun test ctxt consts =
      consts |> fitness ctxt
             |> (fn r => Rat.lt r (Rat.rat_of_int 1880))
  val term_size = 25
  val max_term_size = 27
  val population_size = 500
  val generations = 500
  val bests = 10
  val mut_prob = 0.05
  val scheme = @{thm "scheme_def"}
  val functions = [@{term "w1"}, @{term "w2"}, @{term "w3"}, @{term "f"}]
  val experiments = 20
  val recursive_calls = 1
  val bad_fitness = Rat.rat_of_int 1284914871007569
*}

text {* We finally call the Evolve algorithm. *}

(*value "f (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm xn. xh xb (xj (xm xn) xc)) 15 (1,1,1) (-1,1,-1) (1,-1,1)"

lemma "w1 (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm xn. xh xb (xj (xm xn) xc)) (Suc n) v1 v2 v3 = X"
apply simp

lemma "f (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm xn. xh xb (xj (xm xn) xc)) n v1 v2 v3 = X"
apply simp*)

(*ML {*.
  val w1 = @{term "w1 (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm xn.
   xj x (xi (xl (xi (xl xc xn) xa) xn) xc))"}
  val w2 = @{term "w2 (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm xn.
   xj x (xi (xl (xi (xl xc xn) xa) xn) xc))"}
  val w3 = @{term "w3 (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm xn.
   xj x (xi (xl (xi (xl xc xn) xa) xn) xc))"}
  val f = @{term "f (\<lambda>x xa xb xc xd xe xf xg xh xi xj xk xl xm xn.
   xj x (xi (xl (xi (xl xc xn) xa) xn) xc))"}
  val ff = fitness ctxt [w1, w2, w3, f]
*}*)

local_setup {*
 fn lthy =>
    let val experiment = GP.evolve true false false "RectilinearCrossing.log" scheme functions recursive_calls bad_fitness lthy fitness finish
                                   term_size max_term_size population_size generations bests mut_prob
        val _ = MySQL.new_experiment "RectilinearCrossing" generations term_size population_size experiment
    in lthy end
*}

end