theory ABC_Examples
  imports ABC
begin

text \<open>
The examples of Bundy's chapter on the ABC system, written for the commands of
ABC.thy. Names that start with an upper-case letter are variables and the other
ones are constants or predicates, as in the chapter. Each command prints the
faults of the theory and the smallest repairs, with the clauses each repair
deletes (-) and adds (+).
\<close>

section \<open>The black swan (Example 6.1)\<close>

text \<open>
Bruce is observed to be black, so white(bruce) is a false theorem and black(bruce)
a missing one. Among the repairs with two operations, Abduction 1 adds the
observation and a second operation blocks the proof of white(bruce). One of them
applies Reformation 1 to german(X) \<Longrightarrow> euro(X), which is the repair discussed in
the chapter and splits euro into a European type and a European resident. With a
single operation, Reformation 4 turns the head of a clause into black, which makes
black(bruce) a theorem and white(bruce) not one.
\<close>

abc_faults
  axioms "german X \<Longrightarrow> euro X" "euro X \<and> swan X \<Longrightarrow> white X"
         "german bruce" "swan bruce"
  true "black bruce"
  false "white bruce"

abc_repair
  axioms "german X \<Longrightarrow> euro X" "euro X \<and> swan X \<Longrightarrow> white X"
         "german bruce" "swan bruce"
  true "black bruce"
  false "white bruce"

section \<open>Unique mothers (section 7)\<close>

text \<open>
The last axiom allows one mother per person, so William's two mothers prove that
Diana and Camilla are the same person. Reformation 2 gives mum a third argument,
with a different new constant in each fact and a shared variable in the rule, which
is the repair of the chapter (before the new constants are named birth and step).
\<close>

abc_repair
  axioms "mum diana william" "mum camilla william" "mum X Z \<and> mum Y Z \<Longrightarrow> X = Y"
  false "diana = camilla"

section \<open>Defeasible reasoning without non-monotonic logic (section 9.1)\<close>

text \<open>
Tweety is a penguin, so it should not fly. Reformation 2 on bird gives it a second
argument, a new constant for penguins and another one for the birds that fly, which
plays the role of the constants abnormal and normal of the chapter.
\<close>

abc_repair
  axioms "bird X \<Longrightarrow> fly X" "penguin X \<Longrightarrow> bird X" "penguin tweety"
  true "penguin tweety"
  false "fly tweety"

section \<open>Root cause analysis of a 5G network (section 9.3)\<close>

text \<open>
Two of the observed failures are not theorems, because the rule about dependencies
uses ms instead of microservice and because no assertion says that id1 is created on
d1. The repair of the chapter is among those with two operations, where Reformation 4
merges ms into microservice and Abduction 1 adds createOn(id1, d1). The repairs with
one operation are coarser, for example the deletion of the precondition createOn(Y, X).
\<close>

abc_repair
  axioms "microservice id1 s1" "microservice id2 s1" "microservice id3 s2"
         "full d1" "createOn id2 d1" "sameRoute id2 id3"
         "full X \<and> createOn Y X \<Longrightarrow> fail Y"
         "ms X s1 \<and> ms Y s2 \<and> sameRoute X Y \<Longrightarrow> depend Y X"
         "depend X Y \<and> fail Y \<Longrightarrow> fail X"
  true "fail id1" "fail id2" "fail id3"

text \<open>
To find the root cause, the symptoms move to the false set of the repaired theory.
Among the repairs with one operation, deleting the fact full(d1) blocks the three
proofs, which identifies the root cause found in the chapter. The other ones delete or
weaken the rule that derives the failures.
\<close>

abc_repair
  axioms "microservice id1 s1" "microservice id2 s1" "microservice id3 s2"
         "full d1" "createOn id2 d1" "createOn id1 d1" "sameRoute id2 id3"
         "full X \<and> createOn Y X \<Longrightarrow> fail Y"
         "microservice X s1 \<and> microservice Y s2 \<and> sameRoute X Y \<Longrightarrow> depend Y X"
         "depend X Y \<and> fail Y \<Longrightarrow> fail X"
  false "fail id1" "fail id2" "fail id3"

section \<open>A student's arithmetic misconception (section 9.4)\<close>

text \<open>
The correct theory of two-digit addition, with all the facts add(a, b, u, c) for the
digits a and b, where u and c are the units digit and the carry of a + b, as the
chapter suggests in a footnote. The student answers 49 + 83 = 22, so
sum(4, 9, 8, 3, 0, 2, 2) is in the true set. The theory is written with the ML
interface because the 100 facts are generated. Reformation 5 on the fourth argument
of add, the carry, is the diagnosis of the chapter. The other repairs are alternative
explanations of the same answer.
\<close>

ML \<open>
structure Arith =
struct

fun digit n = ABC.F (string_of_int n, [])

(* add(a, b, u, c) for all the digits a and b, and the same facts without the carry *)
val add_facts : ABC.clause list =
  map_product (fn a => fn b =>
      {body = [], head = SOME (ABC.F ("add", [digit a, digit b,
                                              digit ((a + b) mod 10), digit ((a + b) div 10)]))})
    (0 upto 9) (0 upto 9)
val add_facts_no_carry : ABC.clause list =
  map_product (fn a => fn b =>
      {body = [], head = SOME (ABC.F ("add", [digit a, digit b, digit ((a + b) mod 10)]))})
    (0 upto 9) (0 upto 9)

val sum_rule = ABC.read_clause @{context}
  "add U1 U2 U3 C1 \<and> add T2 C1 T2' 0 \<and> add T1 T2' T3 C2 \<Longrightarrow> sum T1 U1 T2 U2 C2 T3 U3"

fun preferred trues falses =
  {true_set = map (ABC.read_atom @{context}) trues, false_set = map (ABC.read_atom @{context}) falses}

end
\<close>

ML \<open>
writeln (ABC.repair_report @{context} (Arith.sum_rule :: Arith.add_facts)
           (Arith.preferred ["sum 4 9 8 3 0 2 2"] []))
\<close>

text \<open>
With the whole table of digit facts, the theory repaired by Reformation 5 on the carry
explains the observation but predicts too much. After the repair, the variable C1 occurs
only in the atom add(T2, C1, T2'), where it ranges over all the digits, and C2 occurs
only in the head. The repaired theory therefore proves sum(4, 9, 8, 3, 0, d, 2) for
every digit d, which the report below shows for d = 3, the correct tens digit.
\<close>

ML \<open>
let
  val no_carry_rule = ABC.read_clause @{context}
    "add U1 U2 U3 \<and> add T2 C1 T2' \<and> add T1 T2' T3 \<Longrightarrow> sum T1 U1 T2 U2 C2 T3 U3"
in
  writeln (ABC.faults_report @{context} (no_carry_rule :: Arith.add_facts_no_carry)
             (Arith.preferred ["sum 4 9 8 3 0 2 2"] ["sum 4 9 8 3 0 3 2"]))
end
\<close>

text \<open>
More observations narrow the diagnosis. A second answer of the student, 18 + 25 = 33,
leaves four repairs with one operation, because Abduction 1 and Reformation 6 no longer
explain both answers. Putting in the false set the answers 32 and 43, which the student
did not give, rejects the repair by Reformation 5, and no repair is found with at most
two operations.
\<close>

ML \<open>
writeln (ABC.repair_report @{context} (Arith.sum_rule :: Arith.add_facts)
           (Arith.preferred ["sum 4 9 8 3 0 2 2", "sum 1 8 2 5 0 3 3"] []));
writeln (ABC.repair_report @{context} (Arith.sum_rule :: Arith.add_facts)
           (Arith.preferred ["sum 4 9 8 3 0 2 2", "sum 1 8 2 5 0 3 3"]
                            ["sum 4 9 8 3 0 3 2", "sum 1 8 2 5 0 4 3"]))
\<close>

text \<open>
The missing step instantiates the variables left unbound by Reformation 5 with the
carry 0. The result is the student's procedure, which explains both answers and does
not predict 32 or 43. ABC has no operation for this step, which
ABC_Arithmetic.thy also performs by hand on recursive functions.
\<close>

ML \<open>
let
  val student_rule = ABC.read_clause @{context}
    "add U1 U2 U3 \<and> add T2 0 T2' \<and> add T1 T2' T3 \<Longrightarrow> sum T1 U1 T2 U2 0 T3 U3"
in
  writeln (ABC.faults_report @{context} (student_rule :: Arith.add_facts_no_carry)
             (Arith.preferred ["sum 4 9 8 3 0 2 2", "sum 1 8 2 5 0 3 3"]
                              ["sum 4 9 8 3 0 3 2", "sum 1 8 2 5 0 4 3"]))
end
\<close>

text \<open>
ABC_Arithmetic.thy shows the same repair on recursive functions over lists of digits,
where IsaScheme proves what the student's procedure computes.
\<close>

end
