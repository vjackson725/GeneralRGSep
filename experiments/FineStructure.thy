theory FineStructure
  imports Main
begin

section \<open> Util \<close>

lemma impl_conj_reduce[simp]:
  \<open>(A \<Longrightarrow> B) \<Longrightarrow> (A \<and> B) = A\<close>
  by blast


section \<open> Join / Permission Algebra \<close>

text \<open>
  Dockins, Appel et. al.'s algebra.
  Note there's no guaranteed units, so we can explore the fine structure.
  These are the permission algebras.
\<close>

class join =
  fixes \<JJ> :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>

class join_alg = join +
  assumes join_eq: \<open>\<JJ> a b z1 \<Longrightarrow> \<JJ> a b z2 \<Longrightarrow> z1 = z2\<close>
  assumes join_comm: \<open>\<JJ> a b c \<Longrightarrow> \<JJ> b a c\<close>
  assumes join_assoc: \<open>\<JJ> a b d \<Longrightarrow> \<JJ> d c e \<Longrightarrow> \<exists>f. \<JJ> b c f \<and> \<JJ> a f e\<close>
begin

lemma join_assoc2:
  \<open>\<JJ> a b ab \<Longrightarrow> \<JJ> ab c abc \<Longrightarrow> \<exists>ac. \<JJ> a c ac \<and> \<JJ> ac b abc\<close>
  using join_assoc join_comm by blast

subsection \<open> useful definitions \<close>

definition
  \<open>iota w \<equiv> \<exists>a. \<JJ> a w a\<close>

definition
  \<open>dup d \<equiv> \<JJ> d d d\<close>

text \<open> pseudo-units (my terminology) \<close>
definition
  \<open>punit u \<equiv> \<forall>a ua. \<JJ> u a ua \<longrightarrow> ua = a\<close>

definition
  \<open>unit u \<equiv> dup u \<and> punit u\<close>

lemmas unit_def' = unit_def[simplified dup_def punit_def]

subsection \<open> additional laws \<close>

text \<open>
  'unit antimonotonicity'
  When in a sepalg, this is the property Liam was asking about,
    \<open>a + b = 0 \<longrightarrow> a = 0 \<and> b = 0\<close>.
\<close>
definition
  \<open>join_unit_split (\<tau> :: 'a itself) \<equiv>
    \<forall>a b u::'a. \<JJ> a b u \<longrightarrow> unit u \<longrightarrow> unit a\<close>

definition
  \<open>join_positivity (\<tau> :: 'a itself) \<equiv>
    \<forall>a b x y. \<JJ> a x b \<longrightarrow> \<JJ> b y a \<longrightarrow> a = b\<close>

definition
  \<open>join_dup_inherit (\<tau> :: 'a itself) \<equiv>
    \<forall>x y a::'a. \<JJ> x y a \<longrightarrow> dup a \<longrightarrow> dup x\<close>

definition
  \<open>join_full_punits (\<tau> :: 'a itself) \<equiv>
    \<forall>u::'a. punit u \<longrightarrow> dup u\<close>

definition
  \<open>join_cancellative (\<tau> :: 'a itself) \<equiv>
    \<forall>a b b' ab::'a. \<JJ> a b ab \<longrightarrow> \<JJ> a b' ab \<longrightarrow> b' = b\<close>


definition \<open>multisep_alg (\<tau> :: 'a itself) \<equiv> \<forall>a::'a. \<exists>u. \<JJ> a u a\<close>

definition \<open>sep_alg (\<tau> :: 'a itself) \<equiv> \<exists>u::'a. \<forall>a. \<JJ> a u a\<close>

section \<open> Lemmas \<close>

lemma dup_implies_iota:
  \<open>dup u \<Longrightarrow> iota u\<close>
  using iota_def dup_def
  by blast

lemma dup_implies_unit_counterex:
  \<open>dup u \<Longrightarrow> punit u\<close>
  nitpick[card 'a=2]
  oops

lemma dup_implies_unit_counterex:
  \<open>punit u \<Longrightarrow> dup u\<close>
  nitpick[card 'a=1]
  oops

lemma dup_implies_unit_counterex:
  \<open>punit u \<Longrightarrow> iota u\<close>
  nitpick[card 'a=1]
  oops

lemma iota_implies_punit_counterex:
  \<open>iota w \<Longrightarrow> punit w\<close>
  nitpick[card 'a=2]
  oops

lemma iota_implies_dup_counterex:
  \<open>iota w \<Longrightarrow> dup w\<close>
  nitpick[card 'a=2]
  oops

text \<open> a different formulation of positivity \<close>
lemma join_positivity_iff:
  \<open>join_positivity T \<longleftrightarrow> (\<forall>a b c bc abc. \<JJ> b c bc \<longrightarrow> \<JJ> a bc a \<longrightarrow> \<JJ> a b a)\<close>
  unfolding join_positivity_def
  apply (rule iffI; clarsimp)
   apply (blast dest: join_assoc2 join_comm)
  apply (meson join_assoc join_eq; fail)
  done


section \<open> Order lemmas \<close>

text \<open> permission algebras with positivity form an order. \<close>

definition join_leq (infix \<open>\<preceq>\<close> 55) where
  \<open>a \<preceq> b \<equiv> (\<exists>x. \<JJ> a x b) \<or> a = b\<close>

text \<open>
  Note that this collapses to just \<open>\<exists>x. \<JJ> a x b\<close> when we have
  a multisep algebra.
\<close>
lemma join_leq_refl[simp]:
  \<open>x \<preceq> x\<close>
  by (force simp add: multisep_alg_def join_leq_def)

lemma join_leq_trans:
  \<open>x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z\<close>
  by (simp add: join_leq_def, meson join_assoc)

text \<open> Note that antisymmetry is exactly positivity. \<close>
lemma join_leq_antisym:
  assumes \<open>join_positivity TYPE('a)\<close>
  shows \<open>x \<preceq> y \<Longrightarrow> y \<preceq> x \<Longrightarrow> x = y\<close>
  using assms
  by (force simp add: join_leq_def join_positivity_def)


section \<open> Structure lemmas \<close>

subsection \<open> Hierarchy \<close>

lemma positivity_implies_unit_split:
  \<open>join_positivity T \<Longrightarrow> join_unit_split T\<close>
  unfolding join_unit_split_def unit_def' join_positivity_def
  apply clarsimp
  apply (subgoal_tac \<open>\<exists>x. \<JJ> u x a\<close>)
   prefer 2
   apply (metis join_assoc2 join_comm)
  apply blast
  done

lemma dup_inherit_implies_unit_split:
  \<open>join_dup_inherit T \<Longrightarrow> join_unit_split T\<close>
  unfolding join_unit_split_def join_dup_inherit_def unit_def' dup_def
  apply clarsimp
  apply (metis join_assoc2 join_eq)
  done

paragraph \<open> Strictness \<close>

text \<open>
  Note this means that join_unit_split does not give you antisymmetry
  in general!
\<close>
lemma positivity_implies_dup_inherit_counterex:
  \<open>sep_alg T \<Longrightarrow> join_unit_split T \<Longrightarrow> join_positivity T\<close>
  nitpick[card 'a=3]
  oops

lemma positivity_implies_dup_inherit_counterex:
  \<open>sep_alg T \<Longrightarrow> join_positivity T \<Longrightarrow> join_dup_inherit T\<close>
  nitpick[card 'a=3]
  oops

lemma fix_autoindent1: True ..


paragraph \<open> Collapse in the cancellative context \<close>

lemma cancellative_and_iota_implies_punit:
  \<open>join_cancellative T \<Longrightarrow> iota x \<Longrightarrow> punit x\<close>
  unfolding iota_def punit_def join_cancellative_def
  by (metis join_assoc join_eq)

lemma cancellative_and_dup_implies_punit:
  \<open>join_cancellative T \<Longrightarrow> dup x \<Longrightarrow> punit x\<close>
  using cancellative_and_iota_implies_punit dup_implies_iota
  by blast

lemma cancellative_and_unit_split_implies_dup_inherit:
  \<open>join_cancellative T \<Longrightarrow> join_unit_split T \<Longrightarrow> join_dup_inherit T\<close>
  unfolding join_unit_split_def join_dup_inherit_def unit_def
  by (simp add: imp_conjL cancellative_and_dup_implies_punit)

lemma cancellative_and_dup_inherit_implies_positivity:
  \<open>join_cancellative T \<Longrightarrow> join_dup_inherit T \<Longrightarrow> join_positivity T\<close>
  unfolding join_cancellative_def join_dup_inherit_def join_positivity_def
  apply clarsimp
  apply (frule(1) join_assoc)
  apply clarsimp
  apply (rename_tac xy)
  apply (subgoal_tac \<open>dup xy\<close>)
   prefer 2
   apply (metis dup_def join_assoc)
  apply (subgoal_tac \<open>dup x\<close>)
   prefer 2
  apply blast
  apply (metis cancellative_and_dup_implies_punit join_cancellative_def
      join_comm unit_def unit_def')
  done

text \<open>
  And thus, in a cancellative algebra,
    join_unit_split \<equiv> join_dup_inherit \<equiv> join_unit_split.
\<close>

end


section \<open> Liam's algebra \<close>

text \<open>
  N.b. that \<open>\<JJ> \<approx> a + b = c\<close> is the reversed order from \<open>split \<approx> c = a + b\<close>.
\<close>

class liam_alg = join + zero +
  assumes join_eq: \<open>\<JJ> a b z1 \<Longrightarrow> \<JJ> a b z2 \<Longrightarrow> z1 = z2\<close>
  assumes join_comm: \<open>\<JJ> a b c \<Longrightarrow> \<JJ> b a c\<close>
  assumes join_zero[intro!,simp]: \<open>\<JJ> a 0 a\<close>
  assumes join_split:
    \<open>\<JJ> ab cd abcd \<Longrightarrow> \<JJ> a b ab \<Longrightarrow> \<JJ> c d cd \<Longrightarrow>
      \<exists>ac bd. \<JJ> ac bd abcd \<and> \<JJ> a c ac \<and> \<JJ> b d bd\<close>
begin

lemma join_assoc:
  assumes
    \<open>\<JJ> a b ab\<close>
    \<open>\<JJ> ab c abc\<close>
  shows
    \<open>\<exists>bc. \<JJ> b c bc \<and> \<JJ> a bc abc\<close>
proof -
  obtain bc where
    \<open>\<JJ> a bc abc\<close> \<open>\<JJ> b c bc\<close>
    using assms join_split[of c ab abc _ _ a b]
    by (metis join_comm join_eq join_zero)
  then show ?thesis
    by blast
qed

sublocale join_alg: join_alg
  by standard
     (simp add: join_eq join_comm join_assoc)+

end

context join_alg
begin

lemma join_split:
  assumes
    \<open>\<JJ> ab cd abcd\<close>
    \<open>\<JJ> a b ab\<close>
    \<open>\<JJ> c d cd\<close>
  shows
    \<open>\<exists>ac bd. \<JJ> ac bd abcd \<and> \<JJ> a c ac \<and> \<JJ> b d bd\<close>
proof -
  obtain abd where abd_eqns:
    \<open>\<JJ> ab d abd\<close> \<open>\<JJ> abd c abcd\<close>
    using assms(1,3)
    by (meson join_assoc join_comm)
  then show ?thesis
    using assms(2)
    by (meson join_assoc join_comm)
qed

text \<open>
  But this does not subclass Liam's algebra, as we don't have a unique zero.
\<close>

end


end