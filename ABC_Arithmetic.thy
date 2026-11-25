theory ABC_Arithmetic
  imports IsaLibs
begin

text \<open>
A pilot of ABC-style theory repair for recursive functions, after the example of
arithmetic misconceptions in Bundy's chapter on the ABC system (section 9.4).
There, the sum of two two-digit numbers is a Datalog relation with seven arguments,
because Datalog has no functions. Here numbers are lists of decimal digits, least
significant digit first, and addition is a recursive function with a carry argument.

A student adds 49 and 83 and answers 22. The correct theory predicts 132, so the
observation is not a theorem, which is an insufficiency in ABC's terms. Removing the
carry argument of the addition function (ABC's Reformation 5) gives a theory that
explains the observation, and IsaScheme then proves what the repaired procedure
computes.

The inductive proofs use IsaScheme's method induct_auto, which chooses the induction
by itself. The times are those of Isabelle2026 on 8 threads, and each proof has a
comment with an equivalent proof that does not need IsaScheme.
\<close>

section \<open>Numbers as lists of digits\<close>

fun val :: "nat list \<Rightarrow> nat" where
  "val [] = 0"
| "val (d # ds) = d + 10 * val ds"

fun valid :: "nat list \<Rightarrow> bool" where
  "valid [] = True"
| "valid (d # ds) = (d < 10 \<and> valid ds)"

text \<open>The units digit and the carry of a column whose digits add up to s.\<close>

abbreviation units :: "nat \<Rightarrow> nat" where
  "units s \<equiv> (if s < 10 then s else s - 10)"

abbreviation carry :: "nat \<Rightarrow> nat" where
  "carry s \<equiv> (if s < 10 then 0 else 1)"

section \<open>The correct theory\<close>

text \<open>
Column-wise addition with a carry c. Each column writes the units digit of
a + b + c and passes its carry to the next column.
\<close>

fun add_carry :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "add_carry c [] [] = (if c = 0 then [] else [c])"
| "add_carry c (a # as) [] = units (a + c) # add_carry (carry (a + c)) as []"
| "add_carry c [] (b # bs) = units (b + c) # add_carry (carry (b + c)) [] bs"
| "add_carry c (a # as) (b # bs) = units (a + b + c) # add_carry (carry (a + b + c)) as bs"

text \<open>The correct theory is right, and predicts 49 + 83 = 132.\<close>

lemma add_carry_correct:
  "c \<le> 1 \<Longrightarrow> valid xs \<Longrightarrow> valid ys \<Longrightarrow> val (add_carry c xs ys) = c + val xs + val ys"
  by induct_auto  (* about 90 s; or by (induction c xs ys rule: add_carry.induct) auto *)

lemma correct_prediction: "add_carry 0 [9, 4] [3, 8] = [2, 3, 1]"
  by simp

text \<open>
The observation 49 + 83 = 22 is in the true set of the preferred structure but is
not a theorem of the correct theory, which is an insufficiency.
\<close>

lemma observation_not_explained: "add_carry 0 [9, 4] [3, 8] \<noteq> [2, 2]"
  by simp

section \<open>The repaired theory\<close>

text \<open>
Reformation 5 removes the carry argument c of add_carry. Every call
add_carry (carry s) xs ys becomes add_student xs ys, and the occurrences of c that
no equation binds any more take the value 0, as the abduced fact add(8,0,8) does in
the chapter. Simplifying a + b + 0 to a + b gives the student's procedure, which
writes the units digit of each column and forgets the carry.
\<close>

fun add_student :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "add_student [] [] = []"
| "add_student (a # as) [] = units a # add_student as []"
| "add_student [] (b # bs) = units b # add_student [] bs"
| "add_student (a # as) (b # bs) = units (a + b) # add_student as bs"

text \<open>The repaired theory explains the observation.\<close>

lemma observation_explained: "add_student [9, 4] [3, 8] = [2, 2]"
  by simp

section \<open>What the student computes\<close>

text \<open>The carries of each column, which the student forgets.\<close>

fun carries :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "carries [] [] = []"
| "carries (a # as) [] = carry a # carries as []"
| "carries [] (b # bs) = carry b # carries [] bs"
| "carries (a # as) (b # bs) = carry (a + b) # carries as bs"

text \<open>
The student loses ten times the value of the carries, that is, 10^(i+1) for each
column i that produces a carry. For 49 + 83 the carries are [1, 1], and
132 - 110 = 22.
\<close>

theorem add_student_value:
  "valid xs \<Longrightarrow> valid ys \<Longrightarrow> val (add_student xs ys) + 10 * val (carries xs ys) = val xs + val ys"
  by induct_auto  (* about 40 s; or by (induction xs ys rule: add_student.induct) auto *)

text \<open>
When a column produces a carry, the next column of the correct procedure differs
from the student's.
\<close>

lemma add_carry_differs [simp]:
  "0 < c \<Longrightarrow> c < 10 \<Longrightarrow> add_student xs ys \<noteq> add_carry c xs ys"
  by induct_auto  (* about 20 s; or by (cases "(xs, ys)" rule: add_student.cases) auto *)

text \<open>
The student's answer is right exactly when no column produces a carry. This is why
the misconception is hard to notice, as the chapter observes.
\<close>

theorem add_student_correct_iff_no_carry:
  "add_student xs ys = add_carry 0 xs ys \<longleftrightarrow> val (carries xs ys) = 0"
  by induct_auto  (* about 45 s, with add_carry_differs as a simplification rule;
                     or by (induction xs ys rule: add_student.induct) auto *)

text \<open>
Forgetting the carry does not break commutativity, so the misconception cannot be
detected by swapping the operands.
\<close>

lemma add_student_comm: "add_student xs ys = add_student ys xs"
  by induct_auto  (* about 1 s *)

lemma add_carry_comm: "add_carry c xs ys = add_carry c ys xs"
  by induct_auto  (* about 15 s *)

end
