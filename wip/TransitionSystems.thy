theory TransitionSystems
  imports "../Soundness"
begin


definition \<open>connected T S \<equiv> (\<forall>a b. S a \<longrightarrow> S b \<longrightarrow> T\<^sup>*\<^sup>* a b \<or> T\<^sup>*\<^sup>* b a)\<close>

lemma empty_state_connected[intro!]:
  \<open>connected T \<bottom>\<close>
  by (simp add: connected_def)

lemma univ_rel_connected[intro!]:
  \<open>connected \<top> S\<close>
  by (simp add: connected_def)

lemma inf_state_connected[intro]:
  \<open>connected T Sa \<Longrightarrow> connected T Sb \<Longrightarrow> connected T (Sa \<sqinter> Sb)\<close>
  by (simp add: connected_def)


definition \<open>complete T S \<equiv> (\<forall>a b c. S a \<longrightarrow> S c \<longrightarrow> T\<^sup>+\<^sup>+ a b \<longrightarrow> T\<^sup>+\<^sup>+ b c \<longrightarrow> S b)\<close>

lemma empty_state_complete[intro!]:
  \<open>complete T \<bottom>\<close>
  by (simp add: complete_def)

lemma empty_rel_complete[intro!]:
  \<open>complete \<bottom> S\<close>
  by (simp add: complete_def)

lemma inf_state_complete[intro]:
  \<open>complete T Sa \<Longrightarrow> complete T Sb \<Longrightarrow> complete T (Sa \<sqinter> Sb)\<close>
  by (simp add: complete_def, blast)

lemma inf_rel_complete[intro]:
  \<open>complete Ta S \<Longrightarrow> complete (Ta \<sqinter> Tb) S\<close>
  \<open>complete Tb S \<Longrightarrow> complete (Ta \<sqinter> Tb) S\<close>
  unfolding complete_def
  by (metis inf_tranclp_subrel rev_predicate2D)+


definition \<open>branchless T \<equiv> (\<forall>a bx by. T\<^sup>+\<^sup>+ a bx \<longrightarrow> T\<^sup>+\<^sup>+ a by \<longrightarrow> bx = by)\<close>

lemma empty_rel_branchless[intro!]:
  \<open>branchless \<bottom>\<close>
  by (simp add: branchless_def)

lemma inf_rel_branchless[intro]:
  \<open>branchless Ta \<Longrightarrow> branchless (Ta \<sqinter> Tb)\<close>
  \<open>branchless Tb \<Longrightarrow> branchless (Ta \<sqinter> Tb)\<close>
  by (metis (mono_tags) branchless_def inf_tranclp_subrel rev_predicate2D)+

lemma branchless_then_determ_result_k_steps:
  \<open>branchless T \<Longrightarrow> (T ^^ k) sx sya \<Longrightarrow> (T ^^ k) sx syb \<Longrightarrow> sya = syb\<close>
  by (induct k)
    (clarsimp; metis branchless_def relpowp_right_unique tranclp.r_into_trancl)+

definition \<open>initst T \<equiv> {a. (\<forall>i. i \<noteq> a \<longrightarrow> T i a) \<and> (\<exists>a'. T a a')}\<close>

lemma initst_inf_subseteq_inf_initst:
  \<open>initst (Ta \<sqinter> Tb) \<subseteq> initst Ta \<sqinter> initst Tb\<close>
  by (force simp add: initst_def subset_iff)

lemma sup_initst_subseteq_initst_sup:
  \<open>initst Ta \<squnion> initst Tb \<le> initst (Ta \<squnion> Tb)\<close>
  by (force simp add: initst_def subset_iff)


typedef 's tr_sys =
  \<open>{(k::nat, I::'s set, T::'s \<Rightarrow> 's \<Rightarrow> bool). I \<subseteq> initst T}\<close>
  by blast

setup_lifting type_definition_tr_sys


instantiation tr_sys :: (type) disjoint
begin
lift_definition disjoint_tr_sys :: \<open>'a tr_sys \<Rightarrow> 'a tr_sys \<Rightarrow> bool\<close> is
  \<open>\<lambda>(ka,Ia,Ta) (kb,Ib,Tb). Ta = Tb\<close> .
instance ..
end

instantiation tr_sys :: (type) plus
begin
lift_definition plus_tr_sys :: \<open>'a tr_sys \<Rightarrow> 'a tr_sys \<Rightarrow> 'a tr_sys\<close> is
  \<open>\<lambda>(ka,Ia,Ta) (kb,Ib,Tb). (ka \<squnion> kb, Ia \<sqinter> Ib, Ta \<squnion> Tb)\<close>
  by (clarsimp, meson UnCI in_mono sup_initst_subseteq_initst_sup)
instance ..
end

instance tr_sys :: (type) pre_perm_alg
  apply standard
      apply (transfer, clarsimp split: prod.splits, metis inf_assoc sup_assoc)
     apply (transfer, clarsimp split: prod.splits, metis inf_commute sup_commute)
    apply (transfer, clarsimp; fail)
   apply (transfer, clarsimp; fail)
  apply (transfer, clarsimp; fail)
  done

instantiation tr_sys :: (type) unitof
begin
lift_definition unitof_tr_sys :: \<open>'a tr_sys \<Rightarrow> 'a tr_sys\<close> is
  \<open>\<lambda>(k, I, T). (0, initst T, T)\<close>
  by clarsimp
instance ..
end

instance tr_sys :: (type) pre_multiunit_sep_alg
  by standard (transfer, force intro: sup.absorb2)+


lift_definition stateset :: \<open>'a tr_sys \<Rightarrow> 'a set\<close> is
  \<open>\<lambda>(k,I,T). Collect (sp (T^^k) (\<lambda>x. x \<in> I))\<close> .

lemma
  \<open>stateset a \<inter> stateset b \<le> stateset (a + b)\<close>
  apply (transfer, clarsimp simp add: set_eq_iff sp_def)
  apply (rename_tac ka Sa Ta kb Sb Tb s' sa sb)
  oops

end