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

lemma join_assoc3:
  \<open>\<^bold>J a b ab \<Longrightarrow> \<^bold>J c ab abc \<Longrightarrow> \<exists>ac. \<^bold>J a c ac \<and> \<^bold>J ac b abc\<close>
  by (meson join_assoc join_comm)


subsection \<open> Unit \<close>

definition \<open>is_join_unit u \<equiv> \<^bold>J u u u \<and> (\<forall>a b. \<^bold>J u a b \<longrightarrow> \<^bold>J u a a)\<close>


subsection \<open> Join Order Monotonicity \<close>

definition \<open>join_order_mono p \<equiv> \<forall>u a b. is_join_unit u \<longrightarrow> \<^bold>J u a b \<longrightarrow> p a \<longrightarrow> p b\<close>


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


subsection \<open> Cancellative Resources \<close>

definition \<open>cancellative p c \<equiv>
  \<forall>a b. p a \<longrightarrow> p b \<longrightarrow> (\<exists>x. \<^bold>J a c x \<and> \<^bold>J b c x) \<longrightarrow> a = b\<close>

lemma cancellativeD:
  \<open>cancellative p c \<Longrightarrow>
    p a \<Longrightarrow> p b \<Longrightarrow>
    \<^bold>J a c x \<Longrightarrow> \<^bold>J b c x \<Longrightarrow>
    a = b\<close>
  using cancellative_def by auto

lemma cancellative_antimono:
  \<open>p' \<le> p \<Longrightarrow> cancellative p c \<Longrightarrow> cancellative p' c\<close>
  by (clarsimp simp add: cancellative_def) (meson predicate1D)

lemma cancellative_antimono_le:
  \<open>p' \<le> p \<Longrightarrow> cancellative p c \<le> cancellative p' c\<close>
  by (clarsimp simp add: cancellative_def) (meson predicate1D)


subsection \<open> Functional Resource Pairs \<close>

definition \<open>join_functional p \<equiv> \<lambda>(a,b). \<forall>x y. p x \<longrightarrow> p y \<longrightarrow> \<^bold>J a b x \<longrightarrow> \<^bold>J a b y \<longrightarrow> x = y\<close>

lemma join_functionalD:
  \<open>join_functional p (a,b) \<Longrightarrow>
    p x \<Longrightarrow>
    p y \<Longrightarrow>
    \<^bold>J a b x \<Longrightarrow> \<^bold>J a b y \<Longrightarrow> x = y\<close>
  using join_functional_def by force

lemma join_functional_sym:
  \<open>symp (curry (join_functional p))\<close>
  unfolding join_functional_def symp_def
  by (blast dest: join_comm)

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

class join_unitof =
  fixes join_unitof :: \<open>'a \<Rightarrow> 'a\<close> (\<open>unitof\<^sub>J\<close>)

class join_munital = join_alg + join_unitof +
  assumes join_unitof_idem[simp]: \<open>unitof\<^sub>J (unitof\<^sub>J a) = unitof\<^sub>J a\<close>
  assumes join_unitof_unital: \<open>\<^bold>J (unitof\<^sub>J a) a a\<close>
  assumes join_unitof_covers: \<open>\<^bold>J a b c \<Longrightarrow> \<^bold>J (unitof\<^sub>J a) b b\<close>
begin

lemma unitof_is_join_unit:
  \<open>is_join_unit (unitof\<^sub>J a)\<close>
  unfolding is_join_unit_def
  apply (rule conjI)
   apply (metis join_unitof_idem join_unitof_unital)
  apply (metis join_unitof_covers join_unitof_idem)
  done

lemma join_unitof_covers_upward: \<open>\<^bold>J a b c \<Longrightarrow> \<^bold>J (unitof\<^sub>J a) c c\<close>
  by (metis join_comm is_join_unit_def join_assoc2 join_unitof_unital unitof_is_join_unit)

end

class join_unit =
  fixes join_unit :: \<open>'a\<close> (\<open>0\<^sub>J\<close>)

class join_unital = join_alg + join_unit +
  assumes join_unit_unital: \<open>\<^bold>J 0\<^sub>J a a\<close>
begin

interpretation multiunital: join_munital join \<open>\<lambda>_. 0\<^sub>J\<close>
  by standard (metis join_unit_unital)+

end



class join_positive_munital = join_positive + join_munital
begin

lemma join_units_unique:
  \<open>is_join_unit u \<Longrightarrow> unitof\<^sub>J u = u\<close>
  by (meson is_join_unit_def join_comm join_positive join_unitof_unital)

end

class join_positive_unital = join_positive + join_unital
begin

lemma join_unit_unique:
  \<open>\<forall>a. \<^bold>J u a a \<Longrightarrow> u = 0\<^sub>J\<close>
  using join_positive join_unit_unital
  by blast

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


section \<open> Basic Instances \<close>

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


subsection \<open> Sum \<close>

instantiation sum :: (join, join) join
begin
definition
  \<open>join_sum a b c \<equiv>
    (\<exists>a' b' c'. a = Inl a' \<and> b = Inl b' \<and> c = Inl c' \<and> \<^bold>J a' b' c') \<or>
    (\<exists>a' b' c'. a = Inr a' \<and> b = Inr b' \<and> c = Inr c' \<and> \<^bold>J a' b' c')\<close>
instance ..
end

lemma join_sum_apply[simp]:
  \<open>\<^bold>J (Inl a) (Inl b) (Inl c) \<longleftrightarrow> \<^bold>J a b c\<close>
  \<open>\<^bold>J (Inr a) (Inr b) (Inr c) \<longleftrightarrow> \<^bold>J a b c\<close>
  \<open>\<^bold>J (Inl a) (Inr b) z \<longleftrightarrow> False\<close>
  \<open>\<^bold>J (Inr a) (Inl b) z \<longleftrightarrow> False\<close>
  \<open>\<^bold>J (Inl a) y (Inr c) \<longleftrightarrow> False\<close>
  \<open>\<^bold>J (Inr a) y (Inl c) \<longleftrightarrow> False\<close>
  \<open>\<^bold>J x (Inl b) (Inr c) \<longleftrightarrow> False\<close>
  \<open>\<^bold>J x (Inr b) (Inl c) \<longleftrightarrow> False\<close>
  by (clarsimp simp add: join_sum_def)+

instance sum :: (join_alg, join_alg) join_alg
  apply standard
   apply (clarsimp simp add: join_sum_def)
   apply (elim disjE exE conjE; simp; metis join_assoc)
  apply (clarsimp simp add: join_sum_def)
  apply (metis join_comm)
  done

instance sum :: (join_functional, join_functional) join_functional
  apply standard
  apply (clarsimp simp add: join_sum_def)
  apply (elim disjE exE conjE; simp; metis join_functional)
  done

instance sum :: (join_cancel, join_cancel) join_cancel
  apply standard
  apply (clarsimp simp add: join_sum_def)
  apply (elim disjE exE conjE; simp; metis join_cancel)
  done

instance sum :: (join_positive, join_positive) join_positive
  apply standard
  apply (clarsimp simp add: join_sum_def)
  apply (elim disjE exE conjE; simp; metis join_positive)
  done

instance sum :: (join_nounit, join_nounit) join_nounit
  apply standard
  apply (clarsimp simp add: join_sum_def)
  apply (elim disjE exE conjE; simp; metis join_nounit)
  done


subsection \<open> Function \<close>

instantiation "fun" :: (join, join) join
begin
definition
  \<open>join_fun a b c \<equiv> \<forall>x. \<^bold>J (a x) (b x) (c x)\<close>
declare join_fun_def[simp]
instance ..
end

instance "fun" :: (join_alg, join_alg) join_alg
  apply standard
   apply clarsimp
   apply (simp add: all_conj_distrib[symmetric])
   apply (rule choice)
   apply (metis join_assoc)
  apply (clarsimp, metis join_comm)
  done

instance "fun" :: (join_functional, join_functional) join_functional
  by standard
    (simp, blast dest: join_functional)

instance "fun" :: (join_cancel, join_cancel) join_cancel
  by standard
    (simp, blast dest: join_cancel)

instance "fun" :: (join_positive, join_positive) join_positive
  by standard
    (simp, blast dest: join_positive)

instantiation "fun" :: (join_unitof, join_unitof) join_unitof
begin
definition \<open>join_unitof_fun a \<equiv> \<lambda>x. unitof\<^sub>J (a x)\<close>
instance ..
end

lemmas join_unitof_fun_apply[simp] =
  join_unitof_fun_def[THEN meta_eq_to_obj_eq, simplified fun_eq_iff, THEN spec]

instance "fun" :: (join_munital, join_munital) join_munital
  by standard
    (simp add: join_unitof_fun_def join_unitof_unital; metis join_unitof_covers)+

instantiation "fun" :: (join_unit, join_unit) join_unit
begin
definition \<open>join_unit_fun \<equiv> \<lambda>x. 0\<^sub>J\<close>
instance ..
end

lemmas join_unit_apply[simp] =
  join_unit_fun_def[THEN meta_eq_to_obj_eq, simplified fun_eq_iff, THEN spec]

instance "fun" :: (join_unital, join_unital) join_unital
  by standard (simp add: join_unit_unital)

instance "fun" :: (join_nounit, join_nounit) join_nounit
  by standard (simp, blast dest: join_nounit)


section \<open> Agreement / Discrete Algebra \<close>

datatype 'a agmt = Agmt (the_agmt: 'a)

instantiation agmt :: (type) join
begin
definition \<open>join_agmt (a::'a agmt) b c \<equiv> (\<exists>x. a = Agmt x \<and> b = Agmt x \<and> c = Agmt x)\<close>
instance ..
end

instance agmt :: (type) join_alg
  by standard (clarsimp simp add: join_agmt_def)+

instance agmt :: (type) join_positive
  by standard (clarsimp simp add: join_agmt_def)+

instance agmt :: (type) join_cancel
  by standard (clarsimp simp add: join_agmt_def)+

instance agmt :: (type) join_functional
  by standard (clarsimp simp add: join_agmt_def)+

instantiation agmt :: (type) join_unitof
begin
definition \<open>join_unitof_agmt (a::'a agmt) \<equiv> a\<close>
instance ..
end
declare join_unitof_agmt_def[simp]

instance agmt :: (type) join_munital
  apply standard
    apply (metis join_unitof_agmt_def)
   apply (metis agmt.exhaust_sel join_agmt_def join_unitof_agmt_def)
  apply (metis join_agmt_def join_unitof_agmt_def)
  done

(* not join_unital *)
(* not join_nounit *)


section \<open> Exclusive / Empty Algebra \<close>

datatype 'a excl = Excl (the_excl: 'a)

instantiation excl :: (type) join
begin
definition \<open>join_excl (a::'a excl) (b::'a excl) (c::'a excl) \<equiv> False\<close>
instance ..
end

instance excl :: (type) join_alg
  by standard (clarsimp simp add: join_excl_def)+

instance excl :: (type) join_positive
  by standard (clarsimp simp add: join_excl_def)+

instance excl :: (type) join_cancel
  by standard (clarsimp simp add: join_excl_def)+

instance excl :: (type) join_functional
  by standard (clarsimp simp add: join_excl_def)+

(* not join_multiunital *)
(* not join_unital *)

instance excl :: (type) join_nounit
  by standard (clarsimp simp add: join_excl_def)+


section \<open> Units \<close>

type_synonym aunit = \<open>unit agmt\<close>
type_synonym munit = \<open>unit excl\<close>


end