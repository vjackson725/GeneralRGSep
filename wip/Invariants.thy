theory Invariants
  imports "../Soundness"
begin

typedef(overloaded) ('a::pre_perm_alg) inv_alg =
  \<open>{(I::'a \<Rightarrow> bool, F::'a \<Rightarrow> bool). True}\<close>
  by blast

setup_lifting type_definition_inv_alg

instantiation inv_alg :: (pre_perm_alg) disjoint
begin
lift_definition disjoint_inv_alg :: \<open>'a inv_alg \<Rightarrow> 'a inv_alg \<Rightarrow> bool\<close> is
  \<open>\<lambda>(Ia,Fa) (Ib,Fb). True\<close> .
instance ..
end

instantiation inv_alg :: (pre_perm_alg) plus
begin
lift_definition plus_tr_sys :: \<open>'a inv_alg \<Rightarrow> 'a inv_alg \<Rightarrow> 'a inv_alg\<close> is
  \<open>\<lambda>(Ia,Fa) (Ib,Fb). (Ia \<sqinter> Ib, Fa \<squnion> Fb)\<close>
  apply clarsimp
  done
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