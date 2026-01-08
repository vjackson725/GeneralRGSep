theory JoinAlg
  imports "../Util"
begin

section \<open> Join Algebras \<close>

class join =
  fixes join :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (\<open>\<^bold>J\<close>)

text \<open>
  Join Algebras are important to the foundations of relevant and separation logic.
  They are, essentially, non-functional commutative semigroups.
\<close>

class join_alg = join +
  assumes join_assoc: \<open>\<^bold>J a b ab \<Longrightarrow> \<^bold>J ab c abc \<Longrightarrow> \<exists>bc. \<^bold>J b c bc \<and> \<^bold>J a bc abc\<close>
  assumes join_comm: \<open>\<^bold>J a b ab \<Longrightarrow> \<^bold>J b a ab\<close>
begin

lemma join_assoc2:
  \<open>\<^bold>J a b ab \<Longrightarrow> \<^bold>J ab c abc \<Longrightarrow> \<exists>ac. \<^bold>J a c ac \<and> \<^bold>J ac b abc\<close>
  by (meson join_assoc join_comm)


subsection \<open> Join Disjointness \<close>

definition disjoint_join (infix \<open>#\<^sub>J\<close> 55) where
  \<open>disjoint_join a b \<equiv> Ex (\<^bold>J a b)\<close>

lemma disjoint_join_sym:
  \<open>a #\<^sub>J b \<Longrightarrow> b #\<^sub>J a\<close>
  using disjoint_join_def join_comm by blast

lemma disjoint_join_split_rightL:
  \<open>\<^bold>J b c bc \<Longrightarrow> a #\<^sub>J bc \<Longrightarrow> a #\<^sub>J b\<close>
  by (clarsimp simp add: disjoint_join_def, metis join_assoc join_comm)

lemma disjoint_join_split_rightR:
  \<open>\<^bold>J b c bc \<Longrightarrow> a #\<^sub>J bc \<Longrightarrow> a #\<^sub>J c\<close>
  by (clarsimp simp add: disjoint_join_def, metis join_assoc join_comm)

lemma disjoint_join_split_leftL:
  \<open>\<^bold>J a b ab \<Longrightarrow> ab #\<^sub>J c \<Longrightarrow> a #\<^sub>J c\<close>
  by (clarsimp simp add: disjoint_join_def, metis join_assoc join_comm)

lemma disjoint_join_split_leftR:
  \<open>\<^bold>J a b ab \<Longrightarrow> ab #\<^sub>J c \<Longrightarrow> b #\<^sub>J c\<close>
  by (clarsimp simp add: disjoint_join_def, metis join_assoc)

subsection \<open> The Resource Ordering \<close>

definition less_eq_res :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>R\<close> 50) where
  \<open>a \<le>\<^sub>R b \<equiv> a = b \<or> (\<exists>x. \<^bold>J a x b)\<close>

definition less_res :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open><\<^sub>R\<close> 50) where
  \<open>a <\<^sub>R b \<equiv> a \<noteq> b \<and> (\<exists>x. \<^bold>J a x b) \<and> (\<nexists>x. \<^bold>J b x a)\<close>


interpretation partial_preordering_res: partial_preordering \<open>(\<le>\<^sub>R)\<close>
  by standard
    (force dest: join_assoc simp add: less_eq_res_def)+

interpretation preordering_res: preordering \<open>(\<le>\<^sub>R)\<close> \<open>(<\<^sub>R)\<close>
  by standard
    (force simp add: less_res_def less_eq_res_def)

end


subsection \<open> Laws \<close>

class join_positive = join_alg +
  assumes join_positive: \<open>\<^bold>J a u b \<Longrightarrow> \<^bold>J b w a \<Longrightarrow> a = b\<close>
begin

interpretation ordering_res: ordering \<open>(\<le>\<^sub>R)\<close> \<open>(<\<^sub>R)\<close>
  by standard
    (force simp add: less_res_def less_eq_res_def dest: join_assoc join_positive)+

end

class join_functional = join_alg +
  assumes join_functional: \<open>\<^bold>J a b cx \<Longrightarrow> \<^bold>J a b cy \<Longrightarrow> cx = cy\<close>
begin

\<comment> \<open>
  We define our own plus here, as there's no easy way to define a \<^emph>\<open>derived\<close> class in Isabelle/HOL.
\<close>
definition plus_join (infixl \<open>+\<^sub>J\<close> 65) where
  \<open>plus_join a b \<equiv> THE c. \<^bold>J a b c\<close>

lemma the_join_eq[simp]:
  \<open>\<^bold>J a b ab \<Longrightarrow> The (\<^bold>J a b) = ab\<close>
  by (metis plus_join_def the_equality join_functional)

lemma join_then_plus_join_eq[simp]:
  \<open>\<^bold>J a b ab \<Longrightarrow> a +\<^sub>J b = ab\<close>
  by (simp add: plus_join_def)

lemma plus_join_commute:
  \<open>a #\<^sub>J b \<Longrightarrow> a +\<^sub>J b = b +\<^sub>J a\<close>
  by (metis disjoint_join_def join_comm join_then_plus_join_eq)

lemma plus_join_assoc_ex:
  \<open>\<^bold>J a b ab \<Longrightarrow>
    \<^bold>J b c bc \<Longrightarrow>
    \<^bold>J a c ac \<Longrightarrow>
    (\<exists>abc. \<^bold>J ab c abc) = (\<exists>abc. \<^bold>J a bc abc)\<close>
  apply (rule iffI)
   apply (blast dest: join_assoc join_functional)
  apply (blast dest: join_assoc2 join_comm join_functional)
  done

lemma plus_join_assoc:
  \<open>a #\<^sub>J b \<Longrightarrow> b #\<^sub>J c \<Longrightarrow> a #\<^sub>J c \<Longrightarrow> a +\<^sub>J b +\<^sub>J c = a +\<^sub>J (b +\<^sub>J c)\<close>
  apply (clarsimp simp add: disjoint_join_def)
  apply (frule(2) plus_join_assoc_ex)
  apply (rename_tac ab bc ac)
  apply (case_tac \<open>\<exists>abc. \<^bold>J ab c abc\<close>)
   apply (metis join_assoc join_then_plus_join_eq)
  apply (simp add: plus_join_def)
  done

end

class join_cancel = join_alg +
  assumes join_cancel: \<open>\<^bold>J x a b \<Longrightarrow> \<^bold>J y a b \<Longrightarrow> x = y\<close>

class join_nounit = join_alg +
  assumes join_nounit: \<open>\<^bold>J u a a \<Longrightarrow> False\<close>

class join_multiunit = join_alg +
  assumes join_multiunit: \<open>\<exists>u. \<^bold>J u a a\<close>
begin


end

class join_unital = join_alg +
  assumes join_unital: \<open>\<exists>u. \<forall>a. \<^bold>J u a a\<close>
begin

subclass join_multiunit
  by standard (metis join_unital)

end


subsection \<open> Combinations \<close>

class join_pos_cancel = join_positive + join_cancel
begin

\<comment> \<open> Indeed, under cancellativity, we have that positive iff dup_positive. \<close>
lemma join_dup_positive:
  \<open>\<^bold>J a b c \<Longrightarrow> \<^bold>J c c c \<Longrightarrow> \<^bold>J a a a\<close>
  apply (subgoal_tac \<open>\<exists>ac bc. \<^bold>J a c ac \<and> \<^bold>J ac b c\<close>)
   prefer 2
   apply (metis join_assoc2)
  apply (subgoal_tac \<open>\<exists>ac bc. \<^bold>J b c bc \<and> \<^bold>J bc a c\<close>)
   prefer 2
   apply (metis join_assoc join_comm)
  apply (metis join_cancel join_comm join_positive)
  done

end


section \<open> Core and Unit \<close>

class core =
  fixes core :: \<open>'a \<Rightarrow> 'a option\<close>

class join_core = join_alg + core +
  assumes core_punit: \<open>core a = Some ua \<Longrightarrow> \<^bold>J ua a a\<close>
  assumes core_idem: \<open>core a = Some ua \<Longrightarrow> core ua = Some ua\<close>
  assumes core_homomorphism:
    \<open>\<^bold>J a b ab \<Longrightarrow> core ab = Some uab \<Longrightarrow> core a = Some ua \<Longrightarrow> core b = Some ub \<Longrightarrow>
      \<^bold>J ua ub uab\<close>
begin


end

class sep_alg = join_positive + zero +
  assumes join_unit_is_zero: \<open>\<^bold>J 0 a a\<close>
begin
subclass join_unital
  by standard (metis join_unit_is_zero)
end


section \<open> Instances \<close>

subsection \<open> Prod \<close>

instantiation prod :: (join, join) join
begin
definition
  \<open>join_prod (a::'a \<times> 'b) (b::'a \<times> 'b) (c::'a \<times> 'b) \<equiv>
    \<^bold>J (fst a) (fst b) (fst c) \<and> \<^bold>J (snd a) (snd b) (snd c)\<close>
instance ..
end

lemma join_prod_apply[simp]:
  \<open>\<^bold>J (ax, ay) (bx, by) (cx, cy) \<longleftrightarrow>
    \<^bold>J ax bx cx \<and> \<^bold>J ay by cy\<close>
  by (simp add: join_prod_def)

instance prod :: (join_alg, join_alg) join_alg
  apply standard
   apply (clarsimp, metis join_assoc)
  apply (clarsimp, metis join_comm)
  done

instance prod :: (join_cancel, join_cancel) join_cancel
  by standard (clarsimp, metis join_cancel)

instance prod :: (join_functional, join_functional) join_functional
  by standard (clarsimp, metis join_functional)

instance prod :: (join_positive, join_positive) join_positive
  by standard (clarsimp, metis join_positive)

\<comment> \<open> right-biased implementation \<close>
instance prod :: (join_alg, join_nounit) join_nounit
  by standard (force dest: join_nounit)

interpretation prod_left_nounit:
  join_nounit \<open>\<^bold>J :: 'a::join_nounit \<times> 'b::join_alg \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  by standard (force dest: join_nounit)


subsection \<open> Option \<close>

instantiation option :: (join) join
begin
definition
  \<open>join_option (a::'a option) (b::'a option) (c::'a option) \<equiv>
    a = None \<and> b = None \<and> c = None \<or>
    b = None \<and> (\<exists>x. a = Some x \<and> c = Some x) \<or>
    a = None \<and> (\<exists>x. b = Some x \<and> c = Some x) \<or>
    (\<exists>a' b' c'. a = Some a' \<and> b = Some b' \<and> c = Some c' \<and> \<^bold>J a' b' c')\<close>
instance ..
end

lemma join_option_apply[simp]:
  \<open>\<^bold>J (Some a) (Some b) (Some c) \<longleftrightarrow> \<^bold>J a b c\<close>
  \<open>\<^bold>J None b c \<longleftrightarrow> b = c\<close>
  \<open>\<^bold>J a None c \<longleftrightarrow> a = c\<close>
  \<open>\<^bold>J a b None \<longleftrightarrow> a = None \<and> b = None\<close>
  by (force simp add: join_option_def)+

instance option :: (join_alg) join_alg
  apply standard
   apply (clarsimp simp add: join_option_def)
   apply (elim disjE; clarsimp)
   apply (metis join_assoc)
  apply (clarsimp simp add: join_option_def, metis join_comm)
  done

instance option :: (\<open>{join_nounit,join_cancel}\<close>) join_cancel
  apply standard
  apply (clarsimp simp add: join_option_def)
  apply (elim disjE; clarsimp)
    apply (metis join_nounit)
   apply (metis join_nounit)
  apply (metis join_cancel)
  done

instance option :: (join_functional) join_functional
  by standard
    (clarsimp simp add: join_option_def, (elim disjE; clarsimp), metis join_functional)

instance option :: (join_positive) join_positive
  by standard
    (clarsimp simp add: join_option_def, (elim disjE; clarsimp), metis join_positive)


end