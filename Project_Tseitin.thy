section \<open>Tseitin Transformation - Verification and Optimization\<close>

text \<open>
Since most SAT solvers insist on formulas in conjunctive normal form (CNF) as input,
but in general the CNF of a given formula may be exponentially larger, there is interest
in efficient transformations that produce a small equisatisfiable CNF for a given formula.
Probably the earliest and most well-known of these transformation is due to Tseitin.

In this project you will implement several transformations of propositional formulas
into equisatisfiable CNFs and formally prove results about their complexity and that
the resulting CNFs are indeed equisatisfiable to the original formula.
\<close>

theory Project_Tseitin
  imports Main
begin

subsection \<open>Syntax and Semantics\<close>

text \<open>
For the purposes of this project propositional formulas (with atoms of an arbitrary type)
are restricted to the following (functionally complete) connectives:
\<close>
datatype 'a form =
  Bot \<comment> \<open>the "always false" formula\<close>
  | Atm 'a \<comment> \<open>propositional atoms\<close>
  | Neg "'a form" \<comment> \<open>negation\<close>
  | Imp "'a form" "'a form" \<comment> \<open>implication\<close>

text \<open>
Define a function \<open>eval\<close> that evaluates the truth value of a formula with respect
to a given truth assignment \<open>\<alpha> :: 'a \<Rightarrow> bool\<close>.
\<close>
fun eval :: "('a \<Rightarrow> bool) \<Rightarrow> 'a form \<Rightarrow> bool"
  where
    "eval _ Bot = False"
  | "eval \<alpha> (Atm p) = \<alpha> p"
  | "eval \<alpha> (Neg \<phi>) = (\<not>(eval \<alpha> \<phi>))"
  | "eval \<alpha> (Imp \<phi> \<psi>) = ((\<not>(eval \<alpha> \<phi>)) \<or> eval \<alpha> \<psi>)"
print_theorems

text \<open>
Define a predicate \<open>sat\<close> that captures satisfiable formulas.
\<close>
definition sat :: "'a form \<Rightarrow> bool"
  where
    "sat \<phi> \<longleftrightarrow> (\<exists>\<alpha>. eval \<alpha> \<phi>)"


subsection \<open>Conjunctive Normal Forms\<close>

text \<open>
Literals are positive or negative atoms.
\<close>
datatype 'a literal = P 'a | N 'a

text \<open>
Function \<open>of_literals\<close> that turns a given literal (of @{typ "'a literal"}) into 
the corresponding formula (of @{typ "'a form"}).
\<close>
fun of_literal :: "'a literal \<Rightarrow> 'a form"
  where
    "of_literal (P p) = Atm p"
  | "of_literal (N p) = Neg (Atm p)"

text \<open>
A clause is a disjunction of literals, represented as a list of literals.
\<close>
type_synonym 'a clause = "'a literal list"

text \<open>
Function \<open>of_clause\<close> that turns a given clause (of @{typ "'a clause"}) into an 
equivalent formula (of @{typ "'a form"}).
\<close>
fun of_clause :: "'a clause \<Rightarrow> 'a form"
  where
    "of_clause [] = Bot"
  | "of_clause (c # cs) = Imp (Neg (of_literal c)) (of_clause cs)"
print_theorems

text \<open>
A CNF is a conjunction of clauses, represented as list of clauses.
\<close>
type_synonym 'a cnf = "'a clause list"

text \<open>
Implement a function \<open>of_cnf\<close> that, given a CNF (of @{typ "'a cnf"}), computes
a logically equivalent formula (of @{typ "'a form"}).
\<close>

fun of_cnf :: "'a cnf \<Rightarrow> 'a form"
  where
    "of_cnf [] = Neg Bot"
  | "of_cnf (c # cs) = Neg (Imp (of_clause c) (Neg (of_cnf cs)))"
print_theorems


subsection \<open>Tseitin Transformation\<close>

text \<open>
The idea of Tseitin's transformation is to assign to each subformula \<open>\<phi>\<close>
a label \<open>a\<^sub>\<phi>\<close> and use the following definitions

\<^item> \<open>a\<^sub>\<bottom> \<longleftrightarrow> \<bottom>\<close>
\<^item> \<open>a\<^sub>\<not>\<^sub>\<phi> \<longleftrightarrow> \<not> \<phi>\<close>
\<^item> \<open>a\<^sub>\<phi>\<^sub>\<longrightarrow>\<^sub>\<psi> \<longleftrightarrow> \<phi> \<longrightarrow> \<psi>\<close>

to recursively compute clauses \<open>tseitin \<phi>\<close> such that \<open>a\<^sub>\<phi> \<and> tseitin \<phi>\<close> and \<open>\<phi>\<close>
are equisatisfiable (that is, the former is satisfiable iff the latter is).

Define a function \<open>tseitin\<close> that computes the clauses corresponding to the above idea.
\<close>           
fun tseitin :: "'a form \<Rightarrow> ('a form) cnf"
  where
    "tseitin (Bot) = [[N Bot]]"
  | "tseitin (Atm \<phi>) = []"
  | "tseitin (Neg \<phi>) = [(N (Neg \<phi>)), (N \<phi>)] # [(P (Neg \<phi>)), (P \<phi>)] # tseitin \<phi>"
  | "tseitin (Imp \<phi> \<psi>) = [(N (Imp \<phi> \<psi>)), (N \<phi>), (P \<psi>)] # [(P (Imp \<phi> \<psi>)), (P \<phi>)] 
                         # [(N \<psi>), (P (Imp \<phi> \<psi>))] # (tseitin \<phi> @ tseitin \<psi>)"

text \<open>
Prove several lemmas on the way to the important prove of equisatisfiability between
the function \<phi> and its tseitin transformation.
\<close>
lemma [simp]: "eval \<alpha> (of_cnf (xs @ ys)) = (eval \<alpha> (of_cnf xs) \<and> eval \<alpha> (of_cnf ys))"
  by (induction xs) auto

lemma [simp]: "eval (eval \<alpha>) (of_cnf(tseitin \<phi>))"
  by (induction \<phi>) auto

lemma [simp]: "eval \<alpha> \<phi> \<Longrightarrow> eval (eval \<alpha>) (of_cnf ([P \<phi>] # tseitin \<phi>))"
  by auto

lemma tseitin_consistent [simp]:
  assumes "eval v (of_cnf(tseitin \<phi>))"
  shows "eval (v \<circ> Atm) \<phi> = v \<phi>"
proof (rule iffI)
  assume "eval (v \<circ> Atm) \<phi>"
  show "v \<phi>"
    sorry
next
  assume "v \<phi>"
  show "eval (v \<circ> Atm) \<phi>"
    sorry
qed

(*(\<lambda>x. True)*)
value "eval (\<lambda>x. True) (of_cnf (tseitin (Imp \<phi> \<psi>)))"

text \<open>
Prove that \<open>a\<^sub>\<phi> \<and> tseitin \<phi>\<close> and \<open>\<phi>\<close> are equisatisfiable.
\<close>
lemma tseitin_equisat:
  "sat (of_cnf ([P \<phi>] # tseitin \<phi>)) \<longleftrightarrow> sat \<phi>"
proof (rule iffI)
  assume "sat (of_cnf ([P \<phi>] # tseitin \<phi>))"
  show "sat \<phi>"
  proof -
    from \<open>sat (of_cnf ([P \<phi>] # tseitin \<phi>))\<close>
    have "\<exists>\<alpha>. eval \<alpha> (of_cnf ([P \<phi>] # tseitin \<phi>))" by (simp add: sat_def)
    then have "\<exists>\<alpha>. (\<alpha> \<phi>) \<and> eval \<alpha> (of_cnf ([P \<phi>] # tseitin \<phi>))" by auto
    then obtain \<alpha> where "\<alpha> \<phi>" and "eval \<alpha> (of_cnf ([P \<phi>] # tseitin \<phi>))" by auto
    then have "eval (\<alpha> \<circ> Atm) \<phi>" by auto
    then have "\<exists>\<beta>. eval \<beta> \<phi>" by auto
    then show ?thesis by (simp add: sat_def)
  qed
next
  assume "sat \<phi>"
  show "sat (of_cnf ([P \<phi>] # tseitin \<phi>))"
  proof -
    from \<open>sat \<phi>\<close>
    have "\<exists>\<beta>. eval \<beta> \<phi>" by (simp add: sat_def)
    then have "\<exists>\<beta>. eval (eval \<beta>) (of_cnf ([P \<phi>] # tseitin \<phi>))" by auto
    then have "\<exists>\<alpha>. eval \<alpha> (of_cnf ([P \<phi>] # tseitin \<phi>))" by auto
    then show ?thesis by (simp add: sat_def)
  qed
qed
  
text \<open>
Prove linear bounds on the number of clauses and literals by suitably
replacing \<open>n\<close> and \<open>num_literals\<close> below:
\<close>
lemma tseitin_num_clauses:
  "length (tseitin \<phi>) \<le> n * size \<phi>"
  sorry

lemma tseitin_num_literals:
  "num_literals (tseitin \<phi>) \<le> n * size \<phi>"
  sorry

text \<open>
Implement a function \<open>t_tseitin\<close> that computes the number of recursive calls of your
earlier definition of @{const tseitin} and prove a linear bound in the size of the formula
(by suitably replacing \<open>n\<close>):
\<close>
fun t_tseitin :: "'a form \<Rightarrow> nat"
  where
    "t_tseitin \<phi> = undefined"

lemma tseitin_linear:
  "t_tseitin \<phi> \<le> n * size \<phi>"
  sorry

text \<open>
Implement a tail recursive variant of @{const tseitin} and prove the lemma below:
\<close>
fun tseitin2 :: "'a form \<Rightarrow> ('a form) cnf \<Rightarrow> ('a form) cnf"
  where
    "tseitin2 \<phi> acc = undefined"

lemma tseitin2_equisat:
  "sat (of_cnf ([P \<phi>] # tseitin2 \<phi> [])) \<longleftrightarrow> sat \<phi>"
  sorry


subsection \<open>A Transformation due to Plaisted and Greenbaum\<close>

text \<open>
Plaisted and Greenbaum had the idea to take the polarity of a subformula into account in order
to reduce the number of clauses and literals needed for an equisatisfiable CNF.
Here, the polarity at the root is positive and it flips whenever we move down to the (first)
argument of a(n) negation (implication).

Implement a variant \<open>plaisted\<close> of @{const tseitin} that takes the polarity of subformulas
into account and prove that \<open>a\<^sub>\<phi> \<and> plaisted True \<phi>\<close> and \<open>\<phi>\<close> are equisatisfiable.
\<close>
fun plaisted :: "bool \<Rightarrow> 'a form \<Rightarrow> ('a form) cnf"
  where
    "plaisted p \<phi> = undefined"

lemma plaisted_equisat:
  "sat (of_cnf ([P \<phi>] # plaisted True \<phi>)) \<longleftrightarrow> sat \<phi>"
  sorry

text \<open>
Prove linear bounds on the number of clauses and literals by suitably
replacing \<open>n\<close> and \<open>num_literals\<close> below:
\<close>
lemma plaisted_num_clauses:
  "length (plaisted p \<phi>) \<le> n * size \<phi>"
  sorry

lemma plaisted_num_literals:
  "num_literals (plaisted p \<phi>) \<le> n * size \<phi>"
  sorry

text \<open>
Prove that with respect to the number of literals and clauses in the resulting CNF,
@{const plaisted} is at least as good as @{const tseitin}.
\<close>
lemma plaisted_le_tseitin_num_clauses:
  "length (plaisted p \<phi>) \<le> length (tseitin \<phi>)"
  sorry

lemma plaisted_le_tseitin_num_literals:
  "num_literals (plaisted p \<phi>) \<le> num_literals (tseitin \<phi>)"
  sorry

end
