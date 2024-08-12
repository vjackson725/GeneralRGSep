theory SecRGSep
  imports "../Soundness"
begin

type_synonym ('l,'a) secst = \<open>'l discr \<times> 'a \<times> 'a\<close>

definition leval :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l) \<Rightarrow> (('l::order,'a) secst \<Rightarrow> bool)\<close> (infix \<open>\<Colon>\<close> 55) where
  \<open>vf \<Colon> lf \<equiv> \<lambda>(l,x,y). the_discr l \<le> lf x \<longrightarrow> the_discr l \<le> lf y \<longrightarrow> vf x = vf y\<close>

definition leak :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> (('l,'a) secst \<Rightarrow> ('l,'a) secst \<Rightarrow> bool)\<close> where
  \<open>leak f \<equiv> \<lambda>(l,x,y) (l',x',y'). l = l' \<and> f x = f y \<and> x' = x \<and> y' = y\<close>

lemma leak_local_triple:
  \<open>\<forall>x xf. x ## xf \<longrightarrow> vf x = vf (x + xf) \<Longrightarrow>
    r, (=) \<turnstile> { \<top> } \<langle> leak vf \<times>\<^sub>R (=) \<rangle> { \<L> (vf \<Colon> lf) }\<close>
  apply (rule_tac p=\<open>\<L> \<top>\<close> and q=\<open>\<L> (vf \<Colon> lf)\<close> in rgsat_atom)
      apply force
     apply force
    apply (force simp add: sp_def le_fun_def leak_def leval_def)
   apply (simp add: sepconj_local_eq)
   apply (clarsimp simp add: sp_def le_fun_def leak_def leval_def sepconj_def)
   apply metis
  apply force
  done

end