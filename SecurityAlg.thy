theory SecurityAlg
  imports RGLogic
begin

section \<open> Util (to move) \<close>

lemma eq_rel_Times_eq_conv[simp]: \<open>((=) \<times>\<^sub>R (=)) = (=)\<close>
  unfolding rel_Times_def
  by blast

lemma post_state_un_eq[simp]:
  \<open>post_state (\<lambda>a b. p a b \<or> q a b) = post_state p \<squnion> post_state q\<close>
  by (force simp add: post_state_def fun_eq_iff)

lemma pre_state_un_eq[simp]:
  \<open>pre_state (\<lambda>a b. p a b \<or> q a b) = pre_state p \<squnion> pre_state q\<close>
  by (force simp add: pre_state_def fun_eq_iff)

abbreviation \<open>equiv_class_by f \<equiv> \<lambda>x. {y. f x = f y}\<close>

abbreviation \<open>equiv_classes_by f \<equiv> range (equiv_class_by f)\<close>


section \<open> Low/High Levels \<close>

datatype level = Low | High

instantiation level :: order
begin

definition \<open>less_eq_level a b \<equiv> a = Low \<or> a = High \<and> b = High\<close>

lemma less_eq_level_simps[simp]:
  \<open>a \<le> High\<close>
  \<open>Low \<le> b\<close>
  \<open>High \<le> b \<longleftrightarrow> b = High\<close>
  \<open>a \<le> Low \<longleftrightarrow> a = Low\<close>
  unfolding less_eq_level_def
  using level.exhaust by blast+

definition \<open>less_level a b \<equiv> a = Low \<and> b = High\<close>

lemma less_level_simps[simp]:
  \<open>a < High \<longleftrightarrow> a = Low\<close>
  \<open>Low < b \<longleftrightarrow> b = High\<close>
  \<open>High < b \<longleftrightarrow> False\<close>
  \<open>a < Low \<longleftrightarrow> False\<close>
  unfolding less_level_def
  using level.exhaust by blast+

instance
  apply standard
     apply (case_tac x; case_tac y; force simp add: less_eq_level_def less_level_def)
    apply (case_tac x; force simp add: less_eq_level_def less_level_def)
   apply (force simp add: less_eq_level_def)
  apply (force simp add: less_eq_level_def)
  done

end

instance level :: linorder
  by standard (metis less_eq_level_def level.exhaust)

instantiation level :: order_top
begin
definition \<open>top_level \<equiv> High\<close>
instance by standard (simp add: less_eq_level_def top_level_def, metis level.exhaust)
end

instantiation level :: order_bot
begin
definition \<open>bot_level \<equiv> Low\<close>
instance by standard (simp add: less_eq_level_def bot_level_def)
end

instantiation level :: semilattice_inf
begin

definition \<open>inf_level a b \<equiv> case a of Low \<Rightarrow> Low | High \<Rightarrow> b\<close>

lemma inf_level_simps[simp]:
  \<open>High \<sqinter> b = b\<close>
  \<open>a \<sqinter> High = a\<close>
  \<open>Low \<sqinter> b = Low\<close>
  \<open>a \<sqinter> Low = Low\<close>
  by (simp add: inf_level_def split: level.splits)+

instance by standard (case_tac x; case_tac y; force)+

end

instantiation level :: semilattice_sup
begin

definition \<open>sup_level a b \<equiv> case a of High \<Rightarrow> High | Low \<Rightarrow> b\<close>

lemma sup_level_simps[simp]:
  \<open>High \<squnion> b = High\<close>
  \<open>a \<squnion> High = High\<close>
  \<open>Low \<squnion> b = b\<close>
  \<open>a \<squnion> Low = a\<close>
  by (simp add: sup_level_def split: level.splits)+

instance by standard (case_tac x; case_tac y; force)+

end

instance level :: lattice by standard

instance level :: distrib_lattice
  by standard (case_tac x; simp)

instantiation level :: boolean_algebra
begin

definition \<open>uminus_level a \<equiv> case a of Low \<Rightarrow> High | High \<Rightarrow> Low\<close>
definition \<open>minus_level (a::level) b \<equiv> a \<sqinter> - b\<close>

instance
  by standard
    (simp add: uminus_level_def bot_level_def top_level_def minus_level_def split: level.splits)+

end  


section \<open> Security Logic \<close>

definition tuple_lift :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool)\<close> (\<open>\<T>\<close>) where
  \<open>\<T> p \<equiv> \<lambda>(x,y). p x \<and> p y\<close>

lemma tuple_lift_conj[simp]: \<open>\<T> (p \<sqinter> q) = \<T> p \<sqinter> \<T> q\<close>
  by (force simp add: tuple_lift_def fun_eq_iff)

lemma tuple_lift_disj_weak:
  \<open>\<T> p \<le> \<T> (p \<squnion> q)\<close>
  \<open>\<T> q \<le> \<T> (p \<squnion> q)\<close>
  by (force simp add: tuple_lift_def fun_eq_iff)+

lemma tuple_lift_top[simp]: \<open>\<T> \<top> = \<top>\<close>
  by (force simp add: tuple_lift_def fun_eq_iff)

lemma tuple_lift_bot[simp]: \<open>\<T> \<bottom> = \<bottom>\<close>
  by (force simp add: tuple_lift_def fun_eq_iff)

lemma tuple_lift_sepconj[simp]: \<open>\<T> (p \<^emph> q) = \<T> p \<^emph> \<T> q\<close>
  by (force simp add: tuple_lift_def fun_eq_iff sepconj_def)


section \<open> SecRel \<close>

type_synonym 'a sec_rel = \<open>'a \<times> 'a \<Rightarrow> bool\<close>

definition pure_sec_rel :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> ('b::zero)) sec_rel\<close> where
  \<open>pure_sec_rel \<phi> \<equiv> \<lambda>((s,h),(s',h')). \<phi> s \<and> \<phi> s' \<and> h = h' \<and> h' = 0\<close>

definition level_eval
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l::order) \<Rightarrow> ('l \<Rightarrow> 'a sec_rel)\<close>
  (\<open>_ \<triangleleft> _\<close> [55,55] 55)
  where
  \<open>e \<triangleleft> l' \<equiv> \<lambda>l (s, s').
    l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'\<close>

definition sec_points_to :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) sec_rel\<close>
  (infix \<open>\<^bold>\<mapsto>\<^sub>s\<close> 90)
  where
  \<open>p \<^bold>\<mapsto>\<^sub>s v \<equiv> \<T> (p \<^bold>\<mapsto> v)\<close>

lemma pure_sec_rel_healthy:
  \<open>quasireflp (curry (pure_sec_rel p)) \<and> symp (curry (pure_sec_rel p))\<close>
  by (clarsimp simp add: pure_sec_rel_def reflp_on_def symp_def prepost_state_def')

lemma level_eval_healthy:
  \<open>quasireflp (curry ((e \<triangleleft> l') l)) \<and> symp (curry ((e \<triangleleft> l') l))\<close>
  by (clarsimp simp add: level_eval_def reflp_on_def symp_def)

lemma level_eval_reflp:
  \<open>reflp (curry ((e \<triangleleft> l') l))\<close>
  by (clarsimp simp add: level_eval_def reflp_def)

lemma secrel_sepconj_quasireflp:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow> quasireflp (curry (p \<^emph> q))\<close>
  apply (clarsimp simp add: reflp_on_def symp_def prepost_state_def' sepconj_def)
  apply (intro conjI; clarsimp)
   apply blast
  apply blast
  done

lemma secrel_sepconj_transp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<^emph> q))\<close>
  by (simp add: symp_def prepost_state_def' sepconj_def, metis)

lemma
  \<open>reflp (curry p) \<Longrightarrow> reflp (curry q) \<Longrightarrow> reflp (curry (p \<leadsto> q))\<close>
  by (clarsimp simp add: prepost_state_def' reflp_on_def
      reflp_def symp_def split: prod.splits)

lemma
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow>
    quasireflp (curry (p \<sqinter> q))\<close>
  by (clarsimp simp add: reflp_on_def prepost_state_def')
    blast

lemma
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow>
    quasireflp (curry (p \<squnion> q))\<close>
  by (clarsimp simp add: reflp_on_def prepost_state_def')
    blast

lemma
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<squnion> q))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

lemma
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<sqinter> q))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

(* nope *)
lemma
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow>
    quasireflp (curry (p \<leadsto> q))\<close>
  nitpick
  oops

lemma
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<leadsto> q))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

lemma
  \<open>symp (curry p) \<Longrightarrow> symp (curry (- p))\<close>
  by (clarsimp simp add: symp_def sepconj_def)


subsection \<open> small triple proof \<close>

lemma
  \<open>(=), (=) \<turnstile> { \<L> ((p \<triangleleft> l) l') } Guard (\<L> (\<T> p)) { \<L> (\<T> p) }\<close>
  unfolding Guard_def
  apply (rule rgsat_atom)
      apply (force simp add: sp_def)
     apply (force simp add: sp_def)
    apply (clarsimp simp add: sp_def)
  oops


section \<open> Domain orders \<close>

paragraph \<open> leq \<close>

definition leq_smyth :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>S\<close> 50) where
  \<open>A \<le>\<^sub>S B \<equiv> \<forall>b\<in>B. \<exists>a\<in>A. a \<le> b\<close>

definition leq_hoare :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>H\<close> 50) where
  \<open>A \<le>\<^sub>H B \<equiv> \<forall>a\<in>A. \<exists>b\<in>B. a \<le> b\<close>

definition leq_plotkin :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>P\<close> 50) where
  \<open>A \<le>\<^sub>P B \<equiv> A \<le>\<^sub>S B \<and> A \<le>\<^sub>H B\<close>

lemmas leq_plotkin_def' = leq_plotkin_def leq_smyth_def leq_hoare_def

paragraph \<open> equality \<close>

definition eq_smyth :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>=\<^sub>S\<close> 50) where
  \<open>a =\<^sub>S b \<equiv> a \<le>\<^sub>S b \<and> b \<le>\<^sub>S a\<close>

definition eq_hoare :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>=\<^sub>H\<close> 50) where
  \<open>a =\<^sub>H b \<equiv> a \<le>\<^sub>H b \<and> b \<le>\<^sub>H a\<close>

definition eq_plotkin :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open>=\<^sub>P\<close> 50) where
  \<open>a =\<^sub>P b \<equiv> a \<le>\<^sub>P b \<and> b \<le>\<^sub>P a\<close>

paragraph \<open> less \<close>

definition less_smyth :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open><\<^sub>S\<close> 50) where
  \<open>A <\<^sub>S B \<equiv> A \<le>\<^sub>S B \<and> \<not>(A =\<^sub>S B)\<close>

definition less_hoare :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open><\<^sub>H\<close> 50) where
  \<open>A <\<^sub>H B \<equiv> A \<le>\<^sub>H B \<and> \<not>(A =\<^sub>H B)\<close>

definition less_plotkin :: \<open>('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (infix \<open><\<^sub>P\<close> 50) where
  \<open>A <\<^sub>P B \<equiv> A \<le>\<^sub>P B \<and> \<not>(A =\<^sub>P B)\<close>

subsection \<open> Smyth is an order \<close>

setup \<open>Sign.mandatory_path "leq_smyth"\<close>

interpretation partial_preordering \<open>(\<le>\<^sub>S)\<close>
  apply standard
   apply (fastforce simp add: leq_smyth_def)
  apply (meson order.trans leq_smyth_def; fail)
  done

setup \<open>Sign.parent_path\<close>

declare leq_smyth.refl[iff]
declare leq_smyth.trans[trans]

lemma smyth_antisym:
  \<open>a \<le>\<^sub>S b \<Longrightarrow> b \<le>\<^sub>S a \<Longrightarrow> a =\<^sub>S b\<close>
  unfolding leq_smyth_def eq_smyth_def
  by argo

lemma eq_smyth_refl[iff]:
  \<open>a =\<^sub>S a\<close>
  by (simp add: eq_smyth_def)

lemma eq_smyth_sym:
  \<open>a =\<^sub>S b \<Longrightarrow> b =\<^sub>S a\<close>
  by (simp add: eq_smyth_def)

lemma eq_smyth_trans[trans]:
  \<open>a =\<^sub>S b \<Longrightarrow> b =\<^sub>S c \<Longrightarrow> a =\<^sub>S c\<close>
  by (force simp add: eq_smyth_def intro: leq_smyth.trans)

lemma smyth_eq_refl:
  \<open>a =\<^sub>S b \<Longrightarrow> a \<le>\<^sub>S b\<close>
  by (simp add: eq_smyth_def)

lemma smyth_less_le:
  \<open>(x <\<^sub>S y) = (x \<le>\<^sub>S y \<and> \<not>(x =\<^sub>S y))\<close>
  by (simp add: less_smyth_def)

lemma smyth_nless_le:
  \<open>(\<not> (x <\<^sub>S y)) = (\<not>(x \<le>\<^sub>S y) \<or> x =\<^sub>S y)\<close>
  by (simp add: less_smyth_def)

local_setup \<open>
  HOL_Order_Tac.declare_order {
    ops = {eq = @{term \<open>(=\<^sub>S) :: ('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close>}, le = @{term \<open>(\<le>\<^sub>S)\<close>},
            lt = @{term \<open>(<\<^sub>S)\<close>}},
    thms = {trans = @{thm leq_smyth.trans},
            refl = @{thm leq_smyth.refl},
            eqD1 = @{thm smyth_eq_refl},
            eqD2 = @{thm smyth_eq_refl[OF eq_smyth_sym]},
            antisym = @{thm smyth_antisym},
            contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF smyth_less_le]},
                 nless_le = @{thm eq_reflection[OF smyth_nless_le]}}
  }
\<close>

subsection \<open> Hoare is an order \<close>

setup \<open>Sign.mandatory_path "leq_hoare"\<close>

interpretation partial_preordering \<open>(\<le>\<^sub>H)\<close>
  apply standard
   apply (fastforce simp add: leq_hoare_def)
  apply (meson order.trans leq_hoare_def; fail)
  done

setup \<open>Sign.parent_path\<close>

declare leq_hoare.refl[iff]
declare leq_hoare.trans[trans]

lemma hoare_antisym:
  \<open>a \<le>\<^sub>H b \<Longrightarrow> b \<le>\<^sub>H a \<Longrightarrow> a =\<^sub>H b\<close>
  unfolding leq_hoare_def eq_hoare_def
  by argo

lemma eq_hoare_refl[iff]:
  \<open>a =\<^sub>H a\<close>
  by (simp add: eq_hoare_def)

lemma eq_hoare_sym:
  \<open>a =\<^sub>H b \<Longrightarrow> b =\<^sub>H a\<close>
  by (simp add: eq_hoare_def)

lemma eq_hoare_trans[trans]:
  \<open>a =\<^sub>H b \<Longrightarrow> b =\<^sub>H c \<Longrightarrow> a =\<^sub>H c\<close>
  by (force simp add: eq_hoare_def intro: leq_hoare.trans)

lemma hoare_eq_refl:
  \<open>a =\<^sub>H b \<Longrightarrow> a \<le>\<^sub>H b\<close>
  by (simp add: eq_hoare_def)

lemma hoare_less_le:
  \<open>(x <\<^sub>H y) = (x \<le>\<^sub>H y \<and> \<not>(x =\<^sub>H y))\<close>
  by (simp add: less_hoare_def)

lemma hoare_nless_le:
  \<open>(\<not> (x <\<^sub>H y)) = (\<not>(x \<le>\<^sub>H y) \<or> x =\<^sub>H y)\<close>
  by (simp add: less_hoare_def)

local_setup \<open>
  HOL_Order_Tac.declare_order {
    ops = {eq = @{term \<open>(=\<^sub>H) :: ('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close>},
            le = @{term \<open>(\<le>\<^sub>H)\<close>},
            lt = @{term \<open>(<\<^sub>H)\<close>}},
    thms = {trans = @{thm leq_hoare.trans},
            refl = @{thm leq_hoare.refl},
            eqD1 = @{thm hoare_eq_refl},
            eqD2 = @{thm hoare_eq_refl[OF eq_hoare_sym]},
            antisym = @{thm hoare_antisym},
            contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF hoare_less_le]},
                 nless_le = @{thm eq_reflection[OF hoare_nless_le]}}
  }
\<close>

subsection \<open> Plotkin is an order \<close>

setup \<open>Sign.mandatory_path "leq_plotkin"\<close>

interpretation partial_preordering \<open>(\<le>\<^sub>P)\<close>
  apply standard
   apply (fastforce simp add: leq_plotkin_def)
  apply (meson leq_plotkin_def leq_hoare.trans leq_smyth.trans; fail)
  done

setup \<open>Sign.parent_path\<close>

declare leq_plotkin.refl[iff]
declare leq_plotkin.trans[trans]

lemma plotkin_antisym:
  \<open>a \<le>\<^sub>P b \<Longrightarrow> b \<le>\<^sub>P a \<Longrightarrow> a =\<^sub>P b\<close>
  unfolding leq_plotkin_def eq_plotkin_def
  by argo

lemma eq_plotkin_refl[iff]:
  \<open>a =\<^sub>P a\<close>
  by (simp add: eq_plotkin_def)

lemma eq_plotkin_sym:
  \<open>a =\<^sub>P b \<Longrightarrow> b =\<^sub>P a\<close>
  by (simp add: eq_plotkin_def)

lemma eq_plotkin_trans[trans]:
  \<open>a =\<^sub>P b \<Longrightarrow> b =\<^sub>P c \<Longrightarrow> a =\<^sub>P c\<close>
  by (clarsimp simp add: leq_plotkin_def eq_plotkin_def,
      blast intro: leq_smyth.trans leq_hoare.trans)

lemma plotkin_eq_refl:
  \<open>a =\<^sub>P b \<Longrightarrow> a \<le>\<^sub>P b\<close>
  by (simp add: eq_plotkin_def)

lemma plotkin_less_le:
  \<open>(x <\<^sub>P y) = (x \<le>\<^sub>P y \<and> \<not>(x =\<^sub>P y))\<close>
  by (simp add: less_plotkin_def)

lemma plotkin_nless_le:
  \<open>(\<not> (x <\<^sub>P y)) = (\<not>(x \<le>\<^sub>P y) \<or> x =\<^sub>P y)\<close>
  by (force simp add: less_plotkin_def)

local_setup \<open>
  HOL_Order_Tac.declare_order {
    ops = {eq = @{term \<open>(=\<^sub>P) :: ('a::order) set \<Rightarrow> 'a set \<Rightarrow> bool\<close>},
            le = @{term \<open>(\<le>\<^sub>P)\<close>},
            lt = @{term \<open>(<\<^sub>P)\<close>}},
    thms = {trans = @{thm leq_plotkin.trans},
            refl = @{thm leq_plotkin.refl},
            eqD1 = @{thm plotkin_eq_refl},
            eqD2 = @{thm plotkin_eq_refl[OF eq_plotkin_sym]},
            antisym = @{thm plotkin_antisym},
            contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF plotkin_less_le]},
                 nless_le = @{thm eq_reflection[OF plotkin_nless_le]}}
  }
\<close>

subsection \<open> Domain order lemmas \<close>

lemma smyth_supcl_greater[intro]:
  fixes A B :: \<open>('a::complete_lattice) set\<close>
  shows \<open>A \<le>\<^sub>S supcl A\<close>
  by (clarsimp simp add: supcl_def leq_smyth_def)
    (meson Sup_upper order.trans all_not_in_conv subset_iff)

lemma smyth_supcl_lesser[intro]:
  fixes A B :: \<open>('a::complete_lattice) set\<close>
  shows \<open>supcl A \<le>\<^sub>S A\<close>
  by (clarsimp simp add: supcl_def leq_smyth_def)
    (metis Sup_upper ccpo_Sup_singleton empty_iff insert_subset singletonI sup.order_iff
      sup_bot.right_neutral)

lemma smyth_supcl_closedR:
  fixes A B :: \<open>('a::complete_lattice) set\<close>
  shows \<open>A \<le>\<^sub>S B \<Longrightarrow> A \<le>\<^sub>S supcl B\<close>
  by (clarsimp simp add: supcl_def leq_smyth_def)
    (meson Sup_upper order.trans all_not_in_conv subset_iff)

lemma smyth_supcl_closedL:
  fixes A B :: \<open>('a::complete_lattice) set\<close>
  shows \<open>supcl A \<le>\<^sub>S B \<Longrightarrow> A \<le>\<^sub>S B\<close>
  by (clarsimp simp add: supcl_def leq_smyth_def)
    (metis Sup_upper order.trans all_not_in_conv subset_iff)

lemma supcl_smyth_eq:
  fixes A B :: \<open>('a::complete_lattice) set\<close>
  shows \<open>supcl A =\<^sub>S A\<close>
  by (simp add: eq_smyth_def smyth_supcl_greater smyth_supcl_lesser)


section \<open> Set pre-perm-algebra \<close>

instantiation set :: (pre_perm_alg) pre_perm_alg
begin

definition plus_set :: \<open>('a::pre_perm_alg) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>plus_set A B \<equiv> {a + b|a b. a \<in> A \<and> b \<in> B \<and> a ## b}\<close>

definition disjoint_set :: \<open>('a::pre_perm_alg) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>disjoint_set A B \<equiv> True\<close>
declare disjoint_set_def[simp]

instance
  apply standard
      apply (clarsimp simp add: plus_set_def set_eq_iff, rule iffI)
       apply (metis disjoint_add_leftR disjoint_add_swap_lr partial_add_assoc2)
      apply (metis disjoint_add_rightL disjoint_add_swap_rl partial_add_assoc3)
     apply (clarsimp simp add: plus_set_def set_eq_iff)
     apply (meson disjoint_sym partial_add_commute)
    apply (simp; fail)
   apply (simp; fail)
  apply (simp; fail)
  done

end





section \<open> Programs and refinement order \<close>

type_synonym 'a prog = \<open>'a \<Rightarrow> 'a set set\<close>
 
abbreviation refinement :: \<open>'a prog \<Rightarrow> 'a prog \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<close> 50) where
  \<open>S \<sqsubseteq> I \<equiv> \<forall>x. S x \<le>\<^sub>S I x\<close>

lemma union_closure:
  \<open>\<forall>x. \<forall>h HI. HI \<in> I' x \<longrightarrow> (\<exists>\<HH>. \<HH> \<noteq> {} \<and> HI = \<Union>\<HH> \<and> (\<forall>H\<in>\<HH>. H \<in> I x)) \<Longrightarrow>
    \<forall>x. I x \<subseteq> I' x \<Longrightarrow>
    I \<sqsubseteq> I' \<and> I' \<sqsubseteq> I\<close>
  apply (clarsimp simp add: leq_smyth_def Ball_def split: prod.splits)
  apply (intro conjI impI allI)
   apply blast
  apply fast
  done

lemma union_closure2:
  \<open>I \<sqsubseteq> supcl \<circ> I \<and> supcl \<circ> I \<sqsubseteq> I\<close>
  by (clarsimp simp add: Ball_def smyth_supcl_greater smyth_supcl_lesser split: prod.splits)

lemma
  fixes PP :: \<open>('a \<times> 'a set) set\<close>
  assumes refl_cl: \<open>\<And>h H. (h, H) \<in> PP \<Longrightarrow> h \<in> H\<close>
  assumes sym_cl: \<open>\<And>h h' H. (h, H) \<in> PP \<Longrightarrow> h' \<in> H \<Longrightarrow> (h', H) \<in> PP\<close>
  shows \<open>PP = {(h,H)|h H u. (u,H) \<in> PP \<and> h \<in> H}\<close>
  apply (simp add: set_eq_iff)
  using refl_cl sym_cl by blast

definition level_eval_H
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l::order) \<Rightarrow> ('l \<Rightarrow> 'a set set)\<close> (\<open>_ \<Colon>\<^sub>H _\<close> [55,55] 55)
  where
  \<open>e \<Colon>\<^sub>H l' \<equiv> \<lambda>l. {A. \<exists>s. A = {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}}\<close>

definition \<open>uncertainty p s \<equiv> {s'. p (s,s')}\<close>

definition \<open>urel_to_hypemset p \<equiv> range (uncertainty p)\<close>

lemma hypemset_level_eval_eq:
  \<open>{uncertainty ((e \<triangleleft> l') l) s|s. True} =
      {A. \<exists>s. A = {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}}\<close>
  by transfer
    (clarsimp simp add: level_eval_def level_eval_H_def uncertainty_def)

lemma \<open>((e \<Colon>\<^sub>H l') l) = urel_to_hypemset ((e \<triangleleft> l') l)\<close>
  by transfer
    (force simp add: level_eval_def level_eval_H_def urel_to_hypemset_def uncertainty_def)

lemma equiv_class_image_eq:
  \<open>equiv_class_by e ` A =
    (Set.filter ((\<noteq>) {} \<circ> (\<inter>) A) (equiv_classes_by e))\<close>
  by (force simp add: image_def Set.filter_def)

definition revealH :: \<open>('s \<Rightarrow> 'v) \<Rightarrow> ('s set \<Rightarrow> 's set set)\<close> (\<open>reveal\<^sub>H\<close>) where
  \<open>reveal\<^sub>H f \<equiv> \<lambda>U. (\<lambda>v. Set.filter ((=) v \<circ> f) U) ` UNIV\<close>

definition \<open>equiv_class_rel f \<equiv> \<lambda>(x,y). f x = f y\<close>

lemma equiv_class_rel_apply[simp]:
  \<open>equiv_class_rel f (x,y) \<longleftrightarrow> f x = f y\<close>
  by (simp add: equiv_class_rel_def)

definition reveal
  :: \<open>('s \<Rightarrow> 'v) \<Rightarrow> ('s \<Rightarrow> 'l::order) \<Rightarrow> (('l \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow> ('l \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow> bool)\<close>
  where
    \<open>reveal f l' \<equiv> \<lambda>R R'. \<forall>l. R' l = R l \<sqinter> (f \<triangleleft> l') l \<sqinter> equiv_class_rel l'\<close>

lemma reveal_triple:
  \<open>(reveal f l') P (P \<sqinter> (f \<triangleleft> l') \<sqinter> (\<lambda>_. equiv_class_rel l'))\<close>
  by (clarsimp simp add: reveal_def level_eval_def equiv_class_rel_def)



definition existsU :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool)\<close> (\<open>E\<^sub>U\<close>) where
  \<open>E\<^sub>U p \<equiv> \<lambda>u. \<exists>s\<in>u. p s\<close>

definition allU :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool)\<close> (\<open>A\<^sub>U\<close>) where
  \<open>A\<^sub>U p \<equiv> \<lambda>u. \<forall>s\<in>u. p s\<close>

definition assign :: \<open>'x \<Rightarrow> 'v \<Rightarrow> (_ \<Rightarrow> _ \<Rightarrow> bool)\<close> where
  \<open>assign x v \<equiv> \<lambda>h h'. h' = h(x \<mapsto> v)\<close>

abbreviation \<open>local_lift r \<equiv> r \<times>\<^sub>R \<top>\<close>

definition sec_lift :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> bool)\<close>
  where
  \<open>sec_lift r \<equiv> \<lambda>u u'. u' = {y|x y. x \<in> u \<and> r x y}\<close>

abbreviation AtomS :: \<open>_ \<Rightarrow> _ comm\<close> (\<open>\<langle>_\<rangle>\<^sub>S\<close>) where
  \<open>AtomS r \<equiv> \<langle> sec_lift r \<rangle>\<close>

lemma
  fixes L :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close>
    and S :: \<open>'b set \<Rightarrow> 'b set \<Rightarrow> bool\<close>
    and R :: \<open>('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool\<close>
  assumes
    \<open>L = (\<lambda>l l'. \<exists>u u'. R u u' \<and> fst ` u = l \<and> fst ` u' = l')\<close>
    \<open>S = (\<lambda>s s'. \<exists>u u'. R u u' \<and> snd ` u = s \<and> snd ` u' = s')\<close>
  shows \<open>R \<le> (\<lambda>u u'. L (fst ` u) (fst ` u') \<and> S (snd ` u) (snd ` u'))\<close>
  using assms
  apply (clarsimp simp add: image_def)
  apply blast
  done

lemma
  fixes x :: \<open>'a\<close>
    and v :: \<open>'b :: perm_alg\<close>
  shows
    \<open>\<bottom>, \<top> \<turnstile> { E\<^sub>U emp } \<langle> local_lift (assign x v) \<rangle>\<^sub>S { E\<^sub>U (\<L> (x \<^bold>\<mapsto> v)) }\<close>

  sorry

definition sec_points_toH
  :: \<open>'a \<Rightarrow> 'b \<Rightarrow> (('a \<rightharpoonup> 'b) set \<Rightarrow> ('a \<rightharpoonup> 'b) set set)\<close>
  (infix \<open>\<^bold>\<mapsto>\<^sub>H\<close> 90)
  where
  \<open>p \<^bold>\<mapsto>\<^sub>H v \<equiv> \<lambda>u. \<exists>s\<in>u. {{h. (p \<^bold>\<mapsto> v) h}}\<close>




end