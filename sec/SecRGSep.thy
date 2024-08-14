theory SecRGSep
  imports "../Soundness"
begin

type_synonym ('l,'a) secst = \<open>'l \<times> 'a \<times> 'a\<close>

definition leval :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'l) \<Rightarrow> (('l::order,'a) secst \<Rightarrow> bool)\<close> (infix \<open>\<Colon>\<close> 80) where
  \<open>vf \<Colon> lf \<equiv> \<lambda>(l,x,y). l \<le> lf x \<longrightarrow> l \<le> lf y \<longrightarrow> vf x = vf y\<close>

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
  fixes l1 :: \<open>'a::perm_alg \<Rightarrow> 'l::{bounded_lattice, perm_alg}\<close>
  assumes vf_frame:
    \<open>\<And>lf x xf y yf. F (lf,xf,yf) \<Longrightarrow> x ## xf \<Longrightarrow> y ## yf \<Longrightarrow> v1 (x + xf) = v1 (y + yf) \<Longrightarrow> v1 x = v1 y\<close>
    and lf_frame:
    \<open>\<And>x lvl lvlf xf yf. F (lvlf,xf,yf) \<Longrightarrow> lvl \<le> l1 x \<Longrightarrow> x ## xf \<Longrightarrow> lvl + lvlf \<le> l1 (x + xf)\<close>
    \<open>\<And>y lvl lvlf xf yf. F (lvlf,xf,yf) \<Longrightarrow> lvl \<le> l1 y \<Longrightarrow> y ## yf \<Longrightarrow> lvl + lvlf \<le> l1 (y + yf)\<close>
  shows
    \<open>r, leak l2 v2 \<turnstile>\<^bsub>F\<^esub> { wssa r p } \<langle> leak l1 v1 \<times>\<^sub>R leak l2 v2 \<rangle> { sswa r (p \<sqinter> \<S> (v2\<Colon>l2)) \<sqinter> \<L> (v1\<Colon>l1) }\<close>
  apply (rule_tac p=\<open>p\<close> and q=\<open>\<L> (v1\<Colon>l1) \<sqinter> (p \<sqinter> \<S> (v2\<Colon>l2))\<close> in rgsat_atom)
      apply force
     apply (force simp add: sp_def le_fun_def leval_def)
    apply (force simp add: sp_def pguard_def)
   apply (clarsimp simp add: sp_def leval_def sepconj_conj_def wlp_def)
   apply (drule spec, drule spec2, drule mp, rule rtranclp.rtrancl_refl)
   apply (metis rtranclp.rtrancl_refl lf_frame[OF predicate1D[of _ F]]
      vf_frame[OF predicate1D[of _ F]])
  apply force
  done



definition
  \<open>secst_unsplit \<equiv> \<lambda>((ll,xl,yl), (ls,xs,ys)). ((ll,ls), (xl,xs), (yl,ys))\<close>

definition
  \<open>secst_split \<equiv> \<lambda>((ll,ls), (xl,xs), (yl,ys)). ((ll,xl,yl), (ls,xs,ys))\<close>

definition \<open>rel_transfer_uu u r \<equiv> \<lambda>x y. r (u x) (u y)\<close>

definition leval_rg
  :: \<open>('a\<times>'b \<Rightarrow> 'v) \<Rightarrow>
        ('a\<times>'b \<Rightarrow> 'l1::bounded_lattice\<times>'l2::bounded_lattice) \<Rightarrow>
        (('l1 \<times> 'a \<times> 'a) \<times> ('l2 \<times> 'b \<times> 'b) \<Rightarrow> bool)\<close>
  (infix \<open>\<Colon>\<^sub>R\<^sub>G\<close> 80)
  where
    \<open>vf \<Colon>\<^sub>R\<^sub>G lf \<equiv> \<lambda>((l1,x1,y1),(l2,x2,y2)).
      (l1,l2) \<le> lf (x1,x2) \<longrightarrow> (l1,l2) \<le> lf (y1,y2) \<longrightarrow> vf (x1,x2) = vf (y1,y2)\<close>

definition leak_rg
  :: \<open>('a\<times>'b \<Rightarrow> ('l1::bounded_lattice\<times>'l2::bounded_lattice)) \<Rightarrow>
      ('a\<times>'b \<Rightarrow> 'v) \<Rightarrow>
      (('l1 \<times> 'a \<times> 'a) \<times> ('l2 \<times> 'b \<times> 'b) \<Rightarrow> ('l1 \<times> 'a \<times> 'a) \<times> ('l2 \<times> 'b \<times> 'b) \<Rightarrow> bool)\<close>
  where
  \<open>leak_rg l v \<equiv> rel_transfer_uu secst_unsplit (leak l v)\<close>

lemma leak_rg_eq:
  \<open>leak_rg l v =
    (\<lambda>((l1, x1, y1), l2, x2, y2) ((l1', x1', y1'), l2', x2', y2').
      (v \<Colon> l) ((l1, l2), (x1, x2), y1, y2) \<and>
      l1' = l1 \<and> x1' = x1 \<and> y1' = y1 \<and> l2' = l2 \<and> x2' = x2 \<and> y2' = y2)\<close>
  by (force simp add: rel_transfer_uu_def leak_rg_def secst_unsplit_def split: prod.splits)

definition restrict_first :: \<open>('a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)\<close> where
  \<open>restrict_first r \<equiv> \<lambda>x y. \<exists>a b. r (x,a) (y,b)\<close>

definition restrict_second :: \<open>('a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool)\<close> where
  \<open>restrict_second r \<equiv> \<lambda>a b. \<exists>x y. r (x,a) (y,b)\<close>

lemma leak_triple:
  fixes l :: \<open>('a::perm_alg\<times>'b::perm_alg \<Rightarrow> ('l1::{bounded_lattice,perm_alg}\<times>'l2::{bounded_lattice,perm_alg}))\<close>
    and p :: \<open>('l1 \<times> 'a \<times> 'a) \<times> ('l2 \<times> 'b \<times> 'b) \<Rightarrow> bool\<close>
  assumes l_framing:
    \<open>\<And>ll ls xl xs lf xf yf.
      F (lf,xf,yf) \<Longrightarrow> (ll, ls) \<le> l (xl, xs) \<Longrightarrow> (ll + lf, ls) \<le> l (xl + xf, xs)\<close>
    \<open>\<And>ll ls yl ys lf xf yf.
      F (lf,xf,yf) \<Longrightarrow> (ll, ls) \<le> l (yl, ys) \<Longrightarrow> (ll + lf, ls) \<le> l (yl + yf, ys)\<close>
    and v_framing:
    \<open>\<And>lf xf yf xl xs yl ys.
      F (lf,xf,yf) \<Longrightarrow> v (xl + xf, xs) = v (yl + yf, ys) \<Longrightarrow> v (xl, xs) = v (yl, ys)\<close>
  shows
    \<open>r, restrict_second (leak_rg l v) \<turnstile>\<^bsub>F\<^esub> { wssa r p } \<langle> leak_rg l v \<rangle> { sswa r (p \<sqinter> v \<Colon>\<^sub>R\<^sub>G l) }\<close>
  apply (rule_tac p=p and q=\<open>p \<sqinter> v \<Colon>\<^sub>R\<^sub>G l\<close> in rgsat_atom)
      apply force
     apply force
    apply (force simp add: sp_def leak_rg_eq leval_def leval_rg_def)
   apply (clarsimp simp add: sp_def leval_def sepconj_conj_def wlp_def leak_rg_eq)
   apply (drule spec, drule spec2, drule mp, rule rtranclp.rtrancl_refl)
   apply (clarsimp simp add: leval_rg_def)
   apply (metis rtranclp.rtrancl_refl l_framing[OF predicate1D[of _ F]]
      v_framing[OF predicate1D[of _ F]])
  apply (force simp add: sp_def leval_def sepconj_conj_def wlp_def leak_rg_eq restrict_second_def)
  done


end