theory SecRGSep
  imports "../Soundness"
begin

type_synonym ('l,'a) secst = \<open>'l discr \<times> 'a \<times> 'a\<close>

definition leval :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l) \<Rightarrow> (('l::order,'a) secst \<Rightarrow> bool)\<close> (infix \<open>\<Colon>\<close> 80) where
  \<open>vf \<Colon> lf \<equiv> \<lambda>(l,x,y). the_discr l \<le> lf x \<longrightarrow> the_discr l \<le> lf y \<longrightarrow> vf x = vf y\<close>

abbreviation leak :: \<open>('a \<Rightarrow> 'l::bounded_lattice) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> (('l,'a) secst \<Rightarrow> ('l,'a) secst \<Rightarrow> bool)\<close> where
  \<open>leak l f \<equiv> pguard (f \<Colon> l)\<close>

lemma leval_level_antimono:
  \<open>l2 \<le> l1 \<Longrightarrow> vf \<Colon> l1 \<le> vf \<Colon> l2\<close>
  by (clarsimp simp add: leval_def le_fun_def, metis order.trans)

lemma sp_local_eq[simp]:
  \<open>sp (b \<times>\<^sub>R (=)) (\<L> p) = \<L> (sp b p)\<close>
  by (force simp add: sp_def rel_Times_def)

lemma leval_unit_eq[simp]:
  \<open>(vf :: _ \<Rightarrow> unit)\<Colon>lf = \<top>\<close>
  by (simp add: leval_def fun_eq_iff)

lemma pguard_true_eq[simp]:
  \<open>pguard \<top> = (=)\<close>
  by (simp add: pguard_def fun_eq_iff)

lemma split_leak_triple:
  assumes vf_frame:
    \<open>\<And>x xf y yf. x ## xf \<Longrightarrow> y ## yf \<Longrightarrow> v1 (x + xf) = v1 (y + yf) \<Longrightarrow> v1 x = v1 y\<close>
    and lf_frame:
    \<open>\<And>x xf. x ## xf \<Longrightarrow> l1 x \<le> l1 (x + xf)\<close>
  shows
    \<open>r, leak l2 v2 \<turnstile> { wssa r p } \<langle> leak l1 v1 \<times>\<^sub>R leak l2 v2 \<rangle> { sswa r (p \<sqinter> \<S> (v2\<Colon>l2)) \<sqinter> \<L> (v1\<Colon>l1) }\<close>
  apply (rule_tac p=\<open>p\<close> and q=\<open>\<L> (v1\<Colon>l1) \<sqinter> (p \<sqinter> \<S> (v2\<Colon>l2))\<close> in rgsat_atom)
      apply force
     apply (force simp add: sp_def le_fun_def leval_def)
    apply (force simp add: sepconj_local_eq sp_def pguard_def)
   apply (simp add: sepconj_local_eq)
   apply (clarsimp simp add: sp_def leval_def sepconj_conj_def wlp_def)
   apply (drule spec, drule spec2, drule mp, rule rtranclp.rtrancl_refl)
   apply (metis dual_order.trans[OF lf_frame] rtranclp.rtrancl_refl vf_frame)
  apply force
  done

end