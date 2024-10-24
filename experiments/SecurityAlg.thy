theory SecurityAlg
  imports "../RGLogic" "HOL-Library.FSet"
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

section \<open> Location heaps \<close>

lemma dom_comp[simp]: \<open>dom (g \<circ>\<^sub>m f) = {a. \<exists>b. f a = Some b \<and> b \<in> dom g}\<close>
  by (force simp add: map_comp_def dom_def split: option.splits)

text \<open>
  For security applications, we need not just the data to be splittable, but also
  the \<^emph>\<open>locations\<close> of the heap. Being able to observe a location's existence can give
  security-relevant information, even without access to its data.
    Thus, we split the information that a location exists and a location's data into
  separate resources.
\<close>

typedef ('a,'b) locheap (infixr \<open>\<rightharpoonup>\<^sub>l\<close> 0) =
  \<open>{(L::'a set, h :: 'a \<rightharpoonup> 'b). dom h \<le> L}\<close>
  by blast

setup_lifting type_definition_locheap

setup \<open>Sign.mandatory_path "locheap"\<close>

lift_definition empty :: \<open>'a \<rightharpoonup>\<^sub>l 'b\<close> is \<open>({}, Map.empty)\<close>
  by force

lift_definition comp :: "('b \<rightharpoonup>\<^sub>l 'c) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'c)" (infixl "\<circ>\<^sub>l" 55) is
  \<open>\<lambda>(B::'b set, g::'b \<rightharpoonup> 'c) (A::'a set, f::'a \<rightharpoonup> 'b). ({a. \<exists>b. f a = Some b \<and> b \<in> dom g}, g \<circ>\<^sub>m f)\<close>
  by (simp split: prod.splits)

lift_definition restrict :: "('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b)" (infixl \<open>|`\<^sub>l\<close> 110) is
  \<open>\<lambda>(A, m) B. (A \<inter> B, m |` B)\<close>
  by (auto split: prod.splits)

lift_definition dom :: "('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a set" is fst .
lift_definition precise_dom :: "('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a set" is \<open>dom \<circ> snd\<close> .

subsection \<open> (weak/permissive) leq \<close>

lift_definition less_eq :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> bool\<close> (infix \<open>\<subseteq>\<^sub>l\<close> 50) is
  \<open>\<lambda>(A,a) (B,b). A \<subseteq> B \<and> a \<subseteq>\<^sub>m b\<close> .

lemma less_eq_trans[trans]:
  \<open>a \<subseteq>\<^sub>l b \<Longrightarrow> b \<subseteq>\<^sub>l c \<Longrightarrow> a \<subseteq>\<^sub>l c\<close>
  by (transfer, force simp add: map_le_def dom_def split: prod.splits)

lemma less_eq_refl[iff]:
  \<open>a \<subseteq>\<^sub>l a\<close>
  by (transfer, simp split: prod.splits)

lemma less_eq_antisym:
  \<open>a \<subseteq>\<^sub>l b \<Longrightarrow> b \<subseteq>\<^sub>l a \<Longrightarrow> a = b\<close>
  by (transfer,
      clarsimp simp add: map_le_def dom_def fun_eq_iff split: prod.splits,
      metis not_Some_eq)

subsection \<open> strong leq \<close>

lift_definition strong_less_eq :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>l\<close> 50) is
  \<open>\<lambda>(A,a) (B,b). A = B \<and> a \<subseteq>\<^sub>m b\<close> .

lemma strong_less_eq_trans[trans]:
  \<open>a \<sqsubseteq>\<^sub>l b \<Longrightarrow> b \<sqsubseteq>\<^sub>l c \<Longrightarrow> a \<sqsubseteq>\<^sub>l c\<close>
  by (transfer, force simp add: map_le_def dom_def split: prod.splits)

lemma strong_less_eq_refl[iff]:
  \<open>a \<sqsubseteq>\<^sub>l a\<close>
  by (transfer, simp split: prod.splits)

lemma strong_less_eq_antisym:
  \<open>a \<sqsubseteq>\<^sub>l b \<Longrightarrow> b \<sqsubseteq>\<^sub>l a \<Longrightarrow> a = b\<close>
  by (transfer,
      clarsimp simp add: map_le_def dom_def fun_eq_iff split: prod.splits,
      metis not_Some_eq)

lemma strong_less_eq_impl_less_eq[dest]:
  \<open>a \<sqsubseteq>\<^sub>l b \<Longrightarrow> a \<subseteq>\<^sub>l b\<close>
  by (transfer, simp split: prod.splits)

subsection \<open> Locheap completion \<close>

lift_definition embed :: \<open>('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>\<lambda>h. (dom h, h)\<close>
  by simp

abbreviation completion :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>c\<close> 50) where
  \<open>lh \<sqsubseteq>\<^sub>c h \<equiv> lh \<sqsubseteq>\<^sub>l locheap.embed h\<close>

setup \<open>Sign.parent_path\<close>


instantiation locheap :: (type, type) plus
begin
lift_definition plus_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a \<rightharpoonup>\<^sub>l 'b\<close> is
  \<open>\<lambda>(D1, m1) (D2, m2). (D1 \<union> D2, m1 ++ m2)\<close>
  by force
instance by standard
end

instantiation locheap :: (type, perm_alg) perm_alg
begin

lift_definition disjoint_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> bool\<close> is
  \<open>\<lambda>(D1, m1) (D2, m2). D1 \<inter> D2 = {}\<close> .

instance
  apply standard
       apply (transfer, force)
      apply (transfer, simp split: prod.splits)
      apply (metis inf_mono inf_sup_aci(5) map_add_comm order_bot_class.bot.extremum_uniqueI)
     apply (transfer, force)
    apply (transfer, fastforce)
   apply (transfer, fastforce)
  apply (transfer, clarsimp split: prod.splits)
  apply (metis Un_Int_assoc_eq Un_Int_eq(1) Un_Int_eq(3) empty_iff map_add_subsumed2 map_le_def sup_bot_left)
  done

end

instantiation locheap :: (type, perm_alg) multiunit_sep_alg
begin
lift_definition unitof_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>\<lambda>_. ({}, Map.empty)\<close>
  by (simp split: prod.splits)
instance by standard (transfer, force)+
end

instantiation locheap :: (type, perm_alg) sep_alg
begin

lift_definition zero_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>({}, Map.empty)\<close>
  by (simp split: prod.splits)

lift_definition bot_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>({}, Map.empty)\<close>
  by (simp split: prod.splits)

instance
  by standard
    (transfer, force)+

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

definition sec_points_to
  :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) sec_rel\<close>
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
  by (clarsimp simp add: reflp_on_def symp_def prepost_state_def' sepconj_def,
      intro conjI; clarsimp; blast)

lemma secrel_sepconj_transp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<^emph> q))\<close>
  by (clarsimp simp add: symp_def prepost_state_def' sepconj_def, blast)

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


section \<open> Set reasoning \<close>

lemma \<open>r x y \<or> r y x \<Longrightarrow> tranclp (symclp r) x x\<close>
  by (metis symclpI1 symclpI2 tranclp.simps)

abbreviation \<open>equiv_class_by f \<equiv> \<lambda>x. {y. f x = f y}\<close>

abbreviation \<open>equiv_classes_by f \<equiv> range (equiv_class_by f)\<close>

abbreviation inf_Times :: \<open>('a::inf) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixr \<open>\<times>\<sqinter>\<times>\<close> 90) where
  \<open>A \<times>\<sqinter>\<times> B \<equiv> case_prod (\<sqinter>) ` (A \<times> B)\<close>

abbreviation sup_Times :: \<open>('a::sup) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixr \<open>\<times>\<squnion>\<times>\<close> 85) where
  \<open>A \<times>\<squnion>\<times> B \<equiv> case_prod (\<squnion>) ` (A \<times> B)\<close>

abbreviation implies_Times :: \<open>('a::boolean_algebra) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixr \<open>\<times>\<leadsto>\<times>\<close> 80) where
  \<open>A \<times>\<leadsto>\<times> B \<equiv> case_prod (\<leadsto>) ` (A \<times> B)\<close>

definition
  \<open>equiv_rel_to_equiv_classes r \<equiv>
    {A. (\<exists>x y. (x,y) \<in> r \<and> x \<in> A \<and> y \<in> A) \<and>
          (\<forall>x y. x \<in> A \<longrightarrow> (x,y) \<in> r \<longrightarrow> y \<in> A)}\<close>

lemma Un_contains_eq:
  fixes A :: \<open>'a set\<close>
  shows \<open>A \<in> \<AA> \<Longrightarrow> \<Union> ((\<union>) A ` \<AA>) = \<Union> \<AA>\<close>
  by (drule mk_disjoint_insert, clarsimp)

(* proof from Liam O'Connor *)
lemma Sup_contains_eq:
  fixes a :: \<open>'a :: complete_lattice\<close>
  assumes \<open>a \<in> A\<close>
  shows \<open>\<Squnion> ((\<squnion>) a ` A) = \<Squnion> A\<close>
proof (rule antisym)
  show \<open>\<Squnion> ((\<squnion>) a ` A) \<le> \<Squnion> A\<close> by (simp add: SUP_least Sup_upper assms)
next
  show \<open>\<Squnion> A \<le> \<Squnion> ((\<squnion>) a ` A)\<close> by (metis Sup_least Sup_upper image_eqI le_sup_iff)
qed

lemma un_Un_eq_Un_un_every:
  fixes a :: \<open>'a set\<close>
  shows \<open>\<AA> \<noteq> {} \<Longrightarrow> A \<union> \<Union> \<AA> = \<Union> ((\<union>) A ` \<AA>)\<close>
  by blast

lemma sup_Sup_eq_Sup_sup_every:
  fixes a :: \<open>'a :: complete_lattice\<close>
  assumes \<open>A \<noteq> {}\<close>
  shows \<open>a \<squnion> \<Squnion> A = \<Squnion> ((\<squnion>) a ` A)\<close>
  apply (intro order.antisym le_supI)
    apply (meson assms SUP_upper2 ex_in_conv sup_ge1)
   apply (metis Sup_mono imageI sup.cobounded2)
  apply (metis SUP_least Sup_upper order_refl sup.mono)
  done

lemma supcl_allsup_export:
  fixes a :: \<open>'a::complete_lattice\<close>
  shows \<open>supcl ((\<squnion>) a ` B) = (\<squnion>) a ` supcl B\<close>
  apply (rule antisym)
  subgoal
    apply (clarsimp simp add: supcl_def image_def subset_iff
        Ball_def[symmetric] Bex_def)
    apply (drule bchoice)
    apply (clarsimp simp add: Ball_def subset_iff[symmetric])
    apply (rule_tac x=\<open>\<Squnion>(f ` A')\<close> in exI)
    apply (rule conjI)
     apply blast
    apply (simp add: sup_Sup_eq_Sup_sup_every)
    apply (rule arg_cong[of _ _ Sup])
    apply force
    done
  apply (clarsimp simp add: supcl_def image_def subset_iff
      Ball_def Bex_def)
  apply (rule_tac x=\<open>(\<squnion>) a ` A'\<close> in exI)
  apply (meson image_iff image_is_empty sup_Sup_eq_Sup_sup_every)
  done


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
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l::order) \<Rightarrow> ('l \<Rightarrow> 'a set set)\<close> (\<open>_ \<triangleleft>\<^sub>\<H> _\<close> [55,55] 55)
  where
  \<open>e \<triangleleft>\<^sub>\<H> l' \<equiv> \<lambda>l. ({A. \<exists>s. A = {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}})\<close>

definition \<open>uncertainty p s \<equiv> {s'. p (s,s')}\<close>

definition \<open>urel_to_hyperset p \<equiv> range (uncertainty p)\<close>

lemma hyperset_level_eval_eq:
  \<open>{uncertainty ((e \<triangleleft> l') l) s|s. True} =
      {A. \<exists>s. A = {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}}\<close>
  by transfer
    (clarsimp simp add: level_eval_def level_eval_H_def uncertainty_def)

lemma \<open>((e \<triangleleft>\<^sub>\<H> l') l) = urel_to_hyperset ((e \<triangleleft> l') l)\<close>
  by transfer
    (force simp add: level_eval_def level_eval_H_def urel_to_hyperset_def uncertainty_def)

lemma
  fixes l' :: \<open>'s \<Rightarrow> 'l::ord\<close>
  fixes e :: \<open>'s \<Rightarrow> 'v\<close>
  shows \<open>{y. \<exists>x. l' x \<le> l \<and> y = {s'. l' s' \<le> l \<longrightarrow> e x = e s'}} = Z\<close>
proof -
  have \<open>
    {y. \<exists>x. l' x \<le> l \<and> y = {s'. l' s' \<le> l \<longrightarrow> e x = e s'}} =
    {y. \<exists>x. l' x \<le> l \<and> y = ({s'. \<not> l' s' \<le> l} \<union>
                              (equiv_class_by e x \<inter> {s'. l' s' \<le> l}))}
  \<close>
    by (simp add: Un_def)
  have \<open>... =
    ((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l}
  \<close>
    by (clarsimp simp add: set_eq_iff image_def)
  show ?thesis
    sorry
qed

lemma equiv_class_image_eq:
  \<open>equiv_class_by e ` A =
    (Set.filter ((\<noteq>) {} \<circ> (\<inter>) A) (equiv_classes_by e))\<close>
  by (force simp add: image_def Set.filter_def)

lemma
  \<open>supcl ({A. \<exists>s. A = {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}}) =
    insert UNIV (
      supcl (((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l})
    )\<close> (is \<open>?lhs = _\<close>)
proof -
  have helper: \<open>\<And>\<AA>. UNIV \<in> supcl \<AA> \<longleftrightarrow> (\<forall>x. \<exists>A'\<in>\<AA>. x \<in> A')\<close>
    apply (simp add: supcl_def)
    apply (metis Sup_subset_mono UNIV_eq_I Union_iff emptyE iso_tuple_UNIV_I order_refl top.extremum_unique)
    done

  have helper2:
    \<open>\<forall>x. \<exists>A'\<in>equiv_classes_by e. x \<in> A'\<close>
    by auto

  have \<open>?lhs = {\<Union>A'|A'. A' \<noteq> {} \<and> A' \<subseteq> (\<lambda>s. {s'. l' s \<le> l \<longrightarrow> l' s' \<le> l \<longrightarrow> e s = e s'}) ` UNIV}\<close>
    by (simp add: supcl_def Union_eq Bex_def, fast)
  also have \<open>... = {\<Union> A' |A'. A' \<noteq> {} \<and> A' \<subseteq> (\<lambda>s. {s'. \<not> l' s \<le> l} \<union> {s'. \<not> l' s' \<le> l} \<union> {s'. e s = e s'}) ` UNIV}\<close>
    by (simp add: Un_def del: Collect_const)
  also have \<open>... = {\<Union> A' |A'. A' \<noteq> {} \<and> A' \<subseteq> (if \<forall>x. l' x \<le> l then {} else {UNIV}) \<union> (\<lambda>x. {s'. \<not> l' s' \<le> l} \<union> {s'. e x = e s'}) ` {x. l' x \<le> l}}\<close>
    by (simp add: if_distrib[where f=\<open>\<lambda>x. x \<union> _\<close>] image_constant_conv)
  also have \<open>... =
      {\<Union> A' |A'. A' \<noteq> {} \<and> (\<forall>x. l' x \<le> l) \<and> A' \<subseteq> range (\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'})} \<union>
      {\<Union> A' |A'. A' \<noteq> {} \<and> (\<exists>x. \<not> l' x \<le> l) \<and> A' \<subseteq> insert UNIV ((\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'}) ` {x. l' x \<le> l})}\<close>
    by (simp add: Collect_disj_eq[symmetric], blast)
  also have \<open>... =
    (if \<forall>x. l' x \<le> l
     then {\<Union> A' |A'. A' \<noteq> {} \<and> A' \<subseteq> range (\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'})}
     else insert UNIV
            {\<Union> A' |A'. A' \<noteq> {} \<and> UNIV \<notin> A' \<and> A' \<subseteq> (\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'}) ` {x. l' x \<le> l}})\<close>
    by (simp add: subset_insert_iff if_distrib[where f=\<open>(\<and>) _\<close>] if_bool_eq_disj
        conj_disj_distribL ex_disj_distrib Collect_disj_eq, blast)
  also have \<open>... =
    (if \<forall>x. l' x \<le> l
     then supcl (equiv_classes_by e)
     else insert UNIV
            (supcl ((\<lambda>x. {s'. l' s' \<le> l \<longrightarrow> e x = e s'}) ` {x. l' x \<le> l})))\<close>
    by (auto simp add: supcl_def)
  also have \<open>... =
    (if \<forall>x. l' x \<le> l
      then supcl (((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l})
      else insert UNIV (supcl
        (((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l})
      ))\<close>
    by (simp add: Un_def)
  also have \<open>... =
    insert UNIV
      (supcl (((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l}))\<close>
    using iffD2[OF helper, of \<open>((\<union>) {s'. \<not> l' s' \<le> l} \<circ> equiv_class_by e) ` {s. l' s \<le> l}\<close>]
    by force
  also have \<open>... =
    insert UNIV
     (supcl ((\<union>) {s'. \<not> l' s' \<le> l} ` (equiv_class_by e ` {x. l' x \<le> l})))
  \<close>
    apply (simp add: comp_def image_def)
    apply (rule arg_cong[of _ _ \<open>\<lambda>x. insert _ (supcl x)\<close>])
    apply blast
    done
  also have \<open>... =
    insert UNIV
      ((\<union>) {s'. \<not> l' s' \<le> l} `
        supcl (equiv_class_by e ` {x. l' x \<le> l}))
  \<close>
    by (simp add: supcl_allsup_export)
  also have \<open>... =
    insert UNIV
      ((\<union>) {s'. \<not> l' s' \<le> l} `
        supcl (Set.filter ((\<noteq>) {} \<circ> (\<inter>) {x. l' x \<le> l}) (equiv_classes_by e)))\<close>
    apply (rule arg_cong[of _ _ \<open>\<lambda>x. insert _ (_ ` supcl x)\<close>])
    apply (force simp add: Set.filter_def image_def Int_def)
    done

  show ?thesis
    sorry
qed


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


lemma mono_comp:
  \<open>mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f \<circ> g)\<close>
  by (simp add: monotone_on_o)

definition
  \<open>set_plus A \<equiv>
    ((`) (case_prod (+)) \<circ> Set.filter (case_prod (##)) \<circ> (\<times>) A)\<close>

lemma
  \<open>{a + b |a b. a \<in> A \<and> b \<in> B \<and> a ## b} = set_plus A B\<close>
  unfolding set_plus_def
  by (simp add: set_eq_iff image_def Set.filter_def, blast)

lemma onesided_plus_mono:
  \<open>mono (set_plus B)\<close>
  by (force simp add: set_plus_def mono_def image_def Set.filter_def split: prod.splits)

lemma
  fixes x :: \<open>'a :: complete_lattice\<close>
  shows \<open>
    Lt = {(x::'a,y). x < y} \<Longrightarrow>
    f (g x) = x \<Longrightarrow>
    \<forall>A. \<Squnion>((f \<circ> g) ` A) = (f \<circ> g) (\<Squnion>A) \<Longrightarrow>
    \<forall>A. \<Squnion>((f) ` A) = (f) (\<Squnion>A) \<Longrightarrow>
    \<forall>A. \<Squnion>((g) ` A) = (g) (\<Squnion>A) \<Longrightarrow>
    mono f \<Longrightarrow>
    mono g \<Longrightarrow>
    f x = x\<close>
  oops

lemma
  fixes A B :: \<open>('a::canonically_ordered_monoid_add) set\<close>
  assumes
    \<open>A \<noteq> {}\<close>
    \<open>B \<noteq> {}\<close>
    \<open>AB = {a + b|a b. a \<in> A \<and> b \<in> B}\<close>
  shows
    \<open>A \<le>\<^sub>P AB\<close>
    \<open>B \<le>\<^sub>P AB\<close>
  using assms
  by (force simp add: leq_plotkin_def' le_iff_add add.commute)+

lemma canonically_ordered_set_add_trans_plotkin:
  fixes X :: \<open>('a::canonically_ordered_monoid_add) set\<close>
  assumes
    \<open>A \<noteq> {}\<close>
    \<open>B \<noteq> {}\<close>
    \<open>{x + a + b|x a b. x \<in> X \<and> a \<in> A \<and> b \<in> B} = X\<close>
  shows
    \<open>{x + a|x a. x \<in> X \<and> a \<in> A} =\<^sub>P X\<close>
proof -
  have \<open>X \<le>\<^sub>P {x + a|x a. x \<in> X \<and> a \<in> A}\<close>
    using assms
    by (force simp add: leq_plotkin_def' le_iff_add)
  moreover have \<open>... \<le>\<^sub>P {x + a + b|x a b. x \<in> X \<and> a \<in> A \<and> b \<in> B}\<close>
    using assms
    by (clarsimp simp add: leq_plotkin_def' le_iff_add, blast)
  ultimately show ?thesis
    using assms eq_plotkin_def
    by force
qed

lemma perm_alg_set_add_trans_plotkin:
  fixes X :: \<open>('a::{perm_alg,order}) set\<close>
  assumes
    \<open>((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) = (\<preceq>)\<close>
    \<open>A \<noteq> {}\<close>
    \<open>B \<noteq> {}\<close>
    \<open>{(x + a) + b|x a b. x \<in> X \<and> a \<in> A \<and> b \<in> B \<and> x ## a \<and> x + a ## b} = X\<close>
  shows
    \<open>{x + a|x a. x \<in> X \<and> a \<in> A \<and> x ## a} =\<^sub>S X\<close>
proof -
  have \<open>X \<le>\<^sub>S {x + a|x a. x \<in> X \<and> a \<in> A \<and> x ## a}\<close>
    using assms(2-)
    apply (clarsimp simp add: leq_smyth_def assms(1) less_eq_sepadd_def')
    apply blast
    done
  moreover have \<open>... \<le>\<^sub>S {(x + a) + b|x a b. x \<in> X \<and> a \<in> A \<and> b \<in> B \<and> x ## a \<and> x + a ## b}\<close>
    using assms(2-)
    apply (clarsimp simp add: leq_smyth_def assms(1) less_eq_sepadd_def'
        conj_disj_distribL ex_disj_distrib)
    apply (drule iffD1[OF set_eq_iff])
    apply simp
    apply metis
    done
  ultimately show ?thesis
    using assms eq_smyth_def
    by force
qed

lemma
  fixes A B :: \<open>('a::canonically_ordered_monoid_add) set\<close>
  shows \<open>A =\<^sub>P B \<Longrightarrow> A = B\<close>
  nitpick
  oops

lemma perm_alg_set_add_trans_plotkin:
  fixes A B :: \<open>('a::{perm_alg,order}) set\<close>
  assumes \<open>((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) = (\<preceq>)\<close>
  shows \<open>A =\<^sub>S B \<Longrightarrow> A = B\<close>
  nitpick
  oops


lemma
  fixes X :: \<open>('a::{plus,disjoint}) set\<close>
  (* partial commutative monoid *)
  assumes partial_add_assoc: \<open>\<And>a b c::'a. a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>\<And>a b::'a. a ## b \<Longrightarrow> a + b = b + a\<close>
  assumes disjoint_sym: \<open>\<And>a b::'a. a ## b \<Longrightarrow> b ## a\<close>
  assumes disjoint_add_rightL: \<open>\<And>a b c::'a. b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## b\<close>
  assumes disjoint_add_right_commute: \<open>\<And>a b c::'a. b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> b ## a + c\<close>
  (* separation laws *)
  assumes positivity:
    \<open>\<And>a b c1 c2::'a. a ## c1 \<Longrightarrow> a + c1 = b \<Longrightarrow> b ## c2 \<Longrightarrow> b + c2 = a \<Longrightarrow> a = b\<close>
  assumes
    \<open>\<And>A. ff A = \<Squnion>((\<lambda>a. {a + b |b. b \<in> F \<and> a ## b}) ` A)\<close>
    \<open>\<And>A. gg A = \<Squnion>((\<lambda>a. {a + b |b. b \<in> G \<and> a ## b}) ` A)\<close>
    \<open>ffgg = ff \<circ> gg\<close>
    \<open>F = {x}\<close>
    \<open>G = {y}\<close>
  shows
  \<open>(d :: 'a \<times> _ \<Rightarrow> _) = case_prod (##) \<Longrightarrow>
    (p :: 'a \<times> _ \<Rightarrow> _) = case_prod (+) \<Longrightarrow>
    ffgg X = X \<Longrightarrow> ff X = X\<close>
  nitpick
  oops

lemma all_iff_conv:
  fixes p q :: \<open>_ \<Rightarrow> bool\<close>
  shows \<open>(\<forall>x. p x = q x) \<longleftrightarrow> p \<le> q \<and> q \<le> p\<close>
  by force

lemma set_eq_choice2_iff:
  \<open>A = {f x y|x y. P x y} \<longleftrightarrow>
    (\<exists>g1 g2. \<forall>a\<in>A. a = f (g1 a) (g2 a) \<and> P (g1 a) (g2 a)) \<and>
    (\<forall>x y. P x y \<longrightarrow> (\<exists>a\<in>A. a = f x y))\<close>
  by (simp add: set_eq_iff all_iff_conv le_fun_def choice_iff', blast)

lemma set_eq_choice3_iff:
  \<open>A = {f x y z|x y z. P x y z} \<longleftrightarrow>
    (\<exists>g1 g2 g3. \<forall>a\<in>A. a = f (g1 a) (g2 a) (g3 a) \<and> P (g1 a) (g2 a) (g3 a)) \<and>
    (\<forall>x y z. P x y z \<longrightarrow> (\<exists>a\<in>A. a = f x y z))\<close>
  by (simp add: set_eq_iff all_iff_conv le_fun_def choice_iff', fast)

lemma
  fixes A C1 C2 :: \<open>('a::multiunit_sep_alg) set\<close>
  assumes
    \<open>dd A C1\<close>
    \<open>dd {a + b |a b. a \<in> A \<and> b \<in> C1 \<and> a ## b} C2\<close>
    \<open>{(a + x) + y|a x y.
                  a \<in> A \<and> x \<in> C1 \<and> y \<in> C2 \<and>
                  a ## x \<and> a + x ## y } = A\<close>
  shows
    \<open>{ a + x |a x. a \<in> A \<and> x \<in> C1 \<and> a ## x } = A\<close>
proof -

  obtain fa fc1 fc2 where triple_choice:
    \<open>\<forall>a\<in>A. a = fa a + fc1 a + fc2 a\<close>
    \<open>\<forall>a\<in>A. fa a \<in> A\<close>
    \<open>\<forall>a\<in>A. fc1 a \<in> C1\<close>
    \<open>\<forall>a\<in>A. fc2 a \<in> C2\<close>
    \<open>\<forall>a\<in>A. fa a ## fc1 a\<close>
    \<open>\<forall>a\<in>A. fa a + fc1 a ## fc2 a\<close>
    \<open>\<forall>a\<in>A. \<forall>c1\<in>C1. \<forall>c2\<in>C2.
        a ## c1 \<longrightarrow> a + c1 ## c2 \<longrightarrow> a + c1 + c2 \<in> A\<close>
    using assms(3)
    by (simp add: trans[OF eq_commute set_eq_choice3_iff], fast)

  have \<open>\<forall>a\<in>A. fa a \<preceq> a\<close>
    using triple_choice
    by (metis less_eq_sepadd_def' trans_helper)

  show ?thesis
    using assms(3)
    apply (simp add: trans[OF eq_commute set_eq_choice2_iff])
    apply (rule conjI)
     prefer 2
     apply clarsimp
     apply (case_tac \<open>\<exists>a'. a' \<preceq> a \<and> a' \<in> A \<and> fa a' = a'\<close>)
      apply clarsimp
      apply (subgoal_tac \<open>\<exists>x'\<in>C1. \<exists>y'\<in>C2.
                            a' ## x' \<and> a' + x' ## y' \<and> a' + x' + y' = a'\<close>)
       prefer 2
       apply (metis triple_choice(1,3-6))
      apply clarsimp
      apply (drule unit_sub_closure2'[rotated 2], blast, blast)
      apply simp
      apply (simp add: less_eq_sepadd_def')
      apply (erule disjE)
       apply simp
      
    sorry
qed


definition
  \<open>seple_rel = {(a,b). a \<noteq> b \<and> (\<exists>c::'a::perm_alg. a ## c \<and> a + c = b)}\<close>

lemma seple_rel_prec:
  fixes x :: \<open>'a :: perm_alg\<close>
  shows \<open>(x,y) \<in> seple_rel\<^sup>+ \<Longrightarrow> x \<prec> y\<close>
  apply (induct rule: trancl.induct)
   apply (clarsimp simp add: seple_rel_def less_sepadd_def')+
  apply (metis positivity trans_helper)
  done

lemma
  fixes x :: \<open>'a :: perm_alg\<close>
  shows \<open>(x,y) \<in> seple_rel\<^sup>+ \<Longrightarrow> x = y \<Longrightarrow> False\<close>
  apply (induct rule: trancl.induct)
   apply (simp add: seple_rel_def)
  apply (drule seple_rel_prec)
  apply (clarsimp simp add: seple_rel_def)
  apply (simp add: partial_le_plus resource_order.leD)
  done

typedef inat = \<open>UNIV :: nat set\<close>
  by blast
setup_lifting type_definition_inat


instantiation set :: (perm_alg) plus
begin
definition \<open>plus_set A B \<equiv> {a + b|a b. a\<in>A \<and> b\<in>B \<and> a ## b}\<close>
instance by standard
end

lemma fperm_exI:
  fixes x :: \<open>'a :: {linordered_semiring,zero_less_one}\<close>
  shows \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> P x \<Longrightarrow> \<exists>x::'a fperm. P (fperm_val x)\<close>
  by (metis FPerm_inverse_iff)

lemma
  \<open>(UNIV :: rat fperm set) + {x. x < 1} = UNIV\<close>
  apply (clarsimp simp add: plus_set_def set_eq_iff)
  apply (simp add: plus_fperm_def less_fperm_def disjoint_fperm_def)
  apply (subst eq_FPerm_iff)
    apply (force simp add: fperm_val_add_gt0)
   apply force
  apply (rule_tac x=\<open>fperm_val x / 2\<close> in fperm_exI)
    apply (simp add: fperm_val_conditions; fail)
   apply (metis fperm_val_conditions(2) half_fperm.rep_eq)
  apply (rule_tac x=\<open>fperm_val x / 2\<close> in fperm_exI)
    apply (simp add: fperm_val_conditions; fail)
   apply (metis fperm_val_conditions(2) half_fperm.rep_eq)
  apply (simp add: fperm_val_conditions)
  apply (metis fperm_val_conditions(2) less_add_same_cancel1 mult_1
      one_add_one one_fperm.rep_eq order_le_less pos_add_strict zero_less_one)
  done

lemma
  fixes X :: \<open>rat fperm set\<close>
  shows
    \<open>(\<forall>y. \<exists>x\<in>X + Y. x < y) \<Longrightarrow>
      (\<forall>y. \<exists>x\<in>X. x < y)\<close>
  apply (clarsimp simp add: Bex_def plus_set_def)
  apply (drule_tac x=y in spec)
  apply clarsimp
  apply (rule_tac x=a in exI)
  apply (simp add: disjoint_fperm_iff less_fperm_def plus_fperm.rep_eq)
  apply (meson fperm_val_conditions(1) less_add_same_cancel1 order.strict_trans)
  done

lemma
  \<open>(\<forall>y. \<exists>x\<in>X. x < y) \<Longrightarrow> (UNIV :: rat fperm set) + X = UNIV\<close>
  apply (clarsimp simp add: plus_set_def set_eq_iff)
  apply (simp add: plus_fperm_def less_fperm_def disjoint_fperm_def)
  apply (subst eq_FPerm_iff)
    apply (force simp add: fperm_val_add_gt0)
   apply force
  apply (rename_tac y)
  apply (drule_tac x=y in spec)
  apply clarsimp
  apply (rule_tac x=\<open>FPerm (fperm_val y - fperm_val x)\<close> in exI)
  apply (rule_tac x=x in exI)
  apply (subst FPerm_inverse_iff)
    apply (metis diff_gt_0_iff_gt fperm_val_conditions
      less_eq_rat_def less_fperm_def add_diff_inverse not_less_iff_gr_or_eq
      pos_add_strict)
  apply (subst FPerm_inverse_iff)
    apply (metis diff_gt_0_iff_gt fperm_val_conditions
      less_eq_rat_def less_fperm_def add_diff_inverse not_less_iff_gr_or_eq
      pos_add_strict)
  apply (rule conjI)
   apply (simp add: fperm_val_conditions(2); fail)
  apply (simp add: fperm_val_conditions(2); fail)
  done

lemma
  \<open>P = {(x,y). 0 < (x::rat zoint) \<and> 0 < (y::rat zoint)} \<Longrightarrow>
    P = {(x,0)|x. 0 < x} + {(0,y)|y. 0 < y}\<close>
  by (clarsimp simp add: plus_set_def set_eq_iff)

lemma
  \<open>P = {(x,y). 0 < (x::rat zoint) \<and> 0 < (y::rat zoint)} \<Longrightarrow>
    P + {(x,0)|x. 0 < x} = P\<close>
  apply (clarsimp simp add: plus_set_def set_eq_iff)
apply (simp add: disjoint_zoint_def)
  apply (intro iffI; elim exE conjE)
   apply (simp add: zoint_val_inject_rev plus_zoint.rep_eq
      less_zoint_def; fail)
   apply (simp add: zoint_val_inject_rev plus_zoint.rep_eq less_zoint_def)
  apply (rule_tac x=\<open>ZOInt (zoint_val a / 2)\<close> in exI)
  apply (rule_tac x=\<open>ZOInt (zoint_val a / 2)\<close> in exI)
  apply simp
  apply (subst ZOInt_inverse_iff,
      metis half_zoint.rep_eq zoint_val_conditions)+
  apply (simp add: zoint_val_conditions)
  done


instantiation set :: (perm_alg) sep_alg
begin

definition
  \<open>plus_set A B \<equiv>
    {a + b|a b. a\<in>A \<and> b\<in>B \<and> a ## b}\<close>

definition
  \<open>disjoint_set (A :: 'a set) (B :: 'a set) \<equiv>
    True\<close>

definition
  \<open>unitof_set (A::'a set) \<equiv> {} :: 'a set\<close>
declare unitof_set_def[simp]

definition
  \<open>zero_set \<equiv> {}\<close>

instance
  apply standard
           apply (clarsimp simp add: plus_set_def disjoint_set_def Bex_def)
           apply (intro iffI conjI impI allI set_eqI; (simp; fail)?)
            apply clarsimp
            apply (metis disjoint_add_leftR disjoint_add_swap_lr partial_add_assoc2)
           apply clarsimp
           apply (metis disjoint_add_rightL disjoint_add_swap_rl partial_add_assoc3)
          apply (clarsimp simp add: plus_set_def disjoint_set_def)
          apply (metis (mono_tags, opaque_lifting) disjoint_sym_iff partial_add_commute)
         apply (clarsimp simp add: plus_set_def disjoint_set_def)
         (* apply (meson disjoint_sym) *)
        apply (clarsimp simp add: plus_set_def disjoint_set_def split: if_splits)
        (* apply (metis disjoint_add_rightL) *)
       apply (clarsimp simp add: plus_set_def disjoint_set_def split: if_splits)
       (* apply (metis disjoint_add_rightR disjoint_add_right_commute) *)
      apply (rename_tac A C1 B C2)
      apply (clarsimp simp add: plus_set_def split: if_splits)
      apply (rename_tac A C1 C2)
      apply (drule sym)
      apply (rule antisym)
       apply clarsimp
       apply (drule subst[rotated, where P=\<open>(\<in>) _\<close>], assumption)
       apply (subst (asm) mem_Collect_eq)
       apply clarsimp
       apply (rename_tac c2 a c1)
  find_theorems \<open>_ \<in> Collect _\<close>

  oops

    apply (simp add: plus_set_def zero_set_def)
   apply (simp add: zero_set_def plus_set_def)
  apply (simp add: zero_set_def)
  done

end

end