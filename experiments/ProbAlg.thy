theory ProbAlg
  imports "../SepAlgInstances" "HOL-Analysis.Infinite_Sum"
begin

section \<open> Real interval [0,1]\<close>

typedef rzointer = \<open>{0::real..1}\<close>
  by force

setup_lifting type_definition_rzointer


instantiation rzointer :: zero
begin
lift_definition zero_rzointer :: \<open>rzointer\<close> is \<open>0\<close> by force
instance by standard
end

instantiation rzointer :: one
begin
lift_definition one_rzointer :: \<open>rzointer\<close> is \<open>1\<close> by force
instance by standard
end

instantiation rzointer :: semigroup_mult
begin
lift_definition times_rzointer :: \<open>rzointer \<Rightarrow> rzointer \<Rightarrow> rzointer\<close> is \<open>(*)\<close>
  by (simp add: mult_le_one)
instance by standard (transfer, simp)
end

instantiation rzointer :: order
begin
lift_definition less_eq_rzointer :: \<open>rzointer \<Rightarrow> rzointer \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .
lift_definition less_rzointer :: \<open>rzointer \<Rightarrow> rzointer \<Rightarrow> bool\<close> is \<open>(<)\<close> .
instance by standard (transfer, force)+
end

instance rzointer :: comm_monoid_mult
  by standard (transfer, simp)+

instance rzointer :: mult_zero
  by standard (transfer, simp)+

instance rzointer :: zero_less_one
  by standard (transfer, simp)+

lift_definition frac_rzointer :: \<open>nat \<Rightarrow> rzointer\<close> (\<open>\<one>\<^bold>'/\<close>) is \<open>\<lambda>n. if n = 0 then 0 else 1 / real n\<close>
  by force

lemma frac_rzointer_mult_eq[simp]:
  \<open>\<one>\<^bold>/a * \<one>\<^bold>/b = \<one>\<^bold>/(a*b)\<close>
  by (transfer, simp)

section \<open> dirac delta \<close>

lemma summable_on_Diff:
  \<open>f summable_on (A - B) \<longleftrightarrow> (\<lambda>x. if x\<in>B then 0 else f x) summable_on A\<close>
  by (rule summable_on_cong_neutral; fastforce)

definition \<open>dirac a \<equiv> (\<lambda>x. if x = a then 1 else 0)\<close>

lemma dirac_simps[simp]:
  \<open>dirac a a = 1\<close>
  \<open>a \<noteq> b \<Longrightarrow> dirac a b = 0\<close>
  by (simp add: dirac_def)+

lemma dirac_alts:
  \<open>dirac a b = 0 \<or> dirac a b = 1\<close>
  by (simp add: dirac_def)

lemma infsum_dirac:
  \<open>infsum (dirac a) UNIV = (1::('b::{topological_comm_monoid_add,t2_space,zero,one}))\<close>
proof -
  have \<open>(\<Sum>\<^sub>\<infinity>x. if x = a then 1 else 0) =
          (1::('b::{topological_comm_monoid_add,t2_space,zero,one}))
          + (\<Sum>\<^sub>\<infinity>x\<in>(UNIV - {a}). if x = a then 1 else 0)\<close>
    by (simp add: infsum_Un_disjoint[of _ \<open>{a}\<close> \<open>UNIV - {a}\<close>, simplified]
        summable_on_Diff summable_on_0)
  also have \<open>... = 1 + 0\<close>
    by (intro arg_cong[where f=\<open>(+) 1\<close>] infsum_0; simp)
  finally show ?thesis
    unfolding dirac_def
    by simp
qed

section \<open> distributions \<close>

typedef 'a DD = \<open>{f :: 'a \<Rightarrow> real. (\<forall>x. 0 \<le> f x) \<and> infsum f UNIV = 1}\<close>
  by (rule exI[of _ \<open>dirac undefined\<close>])
    (simp add: infsum_dirac, simp add: dirac_def)

setup_lifting type_definition_DD

lift_definition convex_sum :: \<open>rzointer \<Rightarrow> 'a DD \<Rightarrow> 'a DD \<Rightarrow> 'a DD\<close> is
  \<open>\<lambda>\<rho> a b. \<lambda>x. \<rho> * a x + (1 - \<rho>) * b x\<close>
  apply clarsimp
  apply (subst infsum_add)
    apply (metis infsum_not_exists summable_on_cmult_right zero_neq_one)
   apply (metis infsum_not_exists summable_on_cmult_right zero_neq_one)
  apply (simp add: infsum_cmult_right')
  done

lift_definition flip_rzointer :: \<open>rzointer \<Rightarrow> rzointer\<close> (\<open>(_\<^sup>F)\<close> [1000] 999) is
  \<open>\<lambda>a. 1 - a\<close>
  by simp


abbreviation convex_sum_pretty
  :: \<open>'a DD \<Rightarrow> rzointer \<Rightarrow> 'a DD \<Rightarrow> 'a DD\<close>
    (\<open>_ \<oplus>\<^bsub>_\<^esub> _\<close> [65,0,66] 65)
  where
    \<open>a \<oplus>\<^bsub>p\<^esub> b \<equiv> convex_sum p a b\<close>

lemma flip_eq_iff: \<open>x\<^sup>F = y \<longleftrightarrow> x = y\<^sup>F\<close>
  by (transfer, force)

\<comment> \<open> w = (y\<^sup>F / (y * x)\<^sup>F)\<^sup>F \<close>
lemma convex_sum_half_assoc:
  \<open>a \<oplus>\<^bsub>x\<^esub> b \<oplus>\<^bsub>y\<^esub> c = a \<oplus>\<^bsub>y * x\<^esub> (b \<oplus>\<^bsub>w\<^esub> c)\<close>
  apply transfer
  apply (clarsimp simp add: fun_eq_iff left_diff_distrib[symmetric]
      add.assoc[symmetric] mult.assoc[symmetric] ring_distribs(1,2))
  find_theorems \<open>_ * (_ + _)\<close>
  sorry


end