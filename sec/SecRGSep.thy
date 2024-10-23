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


inductive prog_straightline :: \<open>'a comm \<Rightarrow> bool\<close> where
  psl_seq[intro!]:
  \<open>\<lbrakk> prog_straightline c1
   ; prog_straightline c2
   \<rbrakk> \<Longrightarrow> prog_straightline (c1 ;; c2)\<close>
| psl_skip[intro!]: \<open>prog_straightline Skip\<close>
| psl_atom[intro!]: \<open>prog_straightline (\<langle> b \<rangle>)\<close>

inductive_cases psl_seqE[elim!]: \<open>prog_straightline (c1 ;; c2)\<close>
inductive_cases psl_skipE[elim!]: \<open>prog_straightline Skip\<close>
inductive_cases psl_atomE[elim!]: \<open>prog_straightline (\<langle> b \<rangle>)\<close>

inductive_cases psl_doodE[elim!]: \<open>prog_straightline (DO c OD)\<close>
inductive_cases psl_endetE[elim!]: \<open>prog_straightline (c1 \<box> c2)\<close>
inductive_cases psl_indetE[elim!]: \<open>prog_straightline (c1 \<^bold>+ c2)\<close>
inductive_cases psl_parE[elim!]: \<open>prog_straightline (c1 \<parallel> c2)\<close>

definition
  \<open>major \<equiv> \<lambda>((x,x'), (y,y')). (x, y)\<close>

definition
  \<open>minor \<equiv> \<lambda>((x,x'), (y,y')). (x', y')\<close>

definition
  \<open>exch4 \<equiv> \<lambda>((a,b),(c,d)). ((a,c),(b,d))\<close>

definition
  \<open>rel_exch4 r \<equiv> \<lambda>a b. r (exch4 a) (exch4 b)\<close>

type_synonym ('a,'b) secstate = \<open>(('a \<times> 'a) \<times> ('b \<times> 'b))\<close>

definition
  \<open>seclift_pred p \<equiv> \<lambda>(a,a'). p a \<and> p a'\<close>

lemma exch4_conv[simp]:
  \<open>exch4 ((a, b), (a', b')) = ((a, a'), (b, b'))\<close>
  by (simp add: exch4_def)

lemma seclift_pred_conv[simp]:
  \<open>seclift_pred p (x, y) = (p x \<and> p y)\<close>
  by (simp add: seclift_pred_def)


definition
  \<open>seclift_rel r \<equiv> \<lambda>(a,a') (b,b'). r a b \<and> r a' b'\<close>



definition leakL
  :: \<open>('a \<times> 'b \<Rightarrow> 'v) \<Rightarrow>
        ('a \<times> 'a) \<times> ('b \<times> 'b) \<Rightarrow> ('a \<times> 'a) \<times> ('b \<times> 'b) \<Rightarrow> bool\<close> where
  \<open>leakL vf \<equiv> rel_exch4 (\<lambda>(x,x') (y,y'). x = y \<and> x' = y' \<and> vf y = vf y')\<close>

definition sec_agree
  :: \<open>('a \<times> 'b \<Rightarrow> 'v) \<Rightarrow> ('a \<times> 'a) \<times> ('b \<times> 'b) \<Rightarrow> bool\<close> (\<open>\<bbbA>\<close>)
  where
    \<open>\<bbbA> vf \<equiv> (\<lambda>(ab,ab'). vf ab = vf ab') \<circ> exch4\<close>

lemma conj_agree_iff:
  \<open>\<bbbA> v1 \<sqinter> \<bbbA> v2 = \<bbbA> (\<lambda>x. (v1 x, v2 x))\<close>
  by (simp add: sec_agree_def exch4_def comp_def fun_eq_iff split: prod.splits)

lemma eqrel_times_eqrel_eq[simp]:
  \<open>((=) \<times>\<^sub>R (=)) = (=)\<close>
  by (force simp add: rel_Times_def)


definition sec_both
  :: \<open>('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) \<times> ('b \<times> 'b) \<Rightarrow> bool\<close> (\<open>\<bool>\<close>)
  where
    \<open>\<bool> p \<equiv> (\<lambda>(ab,ab'). p ab \<and> p ab') \<circ> exch4\<close>

lemma sec_both_conj_distrib:
  \<open>\<bool> p \<sqinter> \<bool> q = \<bool> (p \<sqinter> q)\<close>
  by (force simp add: sec_both_def exch4_def fun_eq_iff)

lemma sec_both_disj_semidistrib:
  \<open>\<bool> p \<squnion> \<bool> q \<le> \<bool> (p \<squnion> q)\<close>
  by (force simp add: sec_both_def exch4_def fun_eq_iff)




lemma rgsat_single_leak:
  fixes p :: \<open>('a::perm_alg,'b::perm_alg) secstate \<Rightarrow> bool\<close>
    and v :: \<open>'a \<times> 'b \<Rightarrow> 'v\<close>
  assumes v_framing:
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        v (xl + xf, xs) = v (yl + yf, ys) \<Longrightarrow> v (xl, xs) = v (yl, ys)\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>F\<^esub>
      { p }
      \<langle> leakL v \<rangle>
      { p \<sqinter> \<bbbA> v }\<close>
  apply (rule_tac p=p and q=\<open>p \<sqinter> \<bbbA> v\<close> in rgsat_atom)
      apply force
     apply (force simp add: sec_agree_def exch4_def)
    apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_agree_def split: prod.splits)
   apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_agree_def split: prod.splits)
   apply (metis v_framing)
  apply force
  done

lemma
  fixes p :: \<open>('a::perm_alg,'b::perm_alg) secstate \<Rightarrow> bool\<close>
    and v :: \<open>'a \<times> 'b \<Rightarrow> 'v\<close>
  assumes v1_framing:
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        v1 (xl + xf, xs) = v1 (yl + yf, ys) \<Longrightarrow> v1 (xl, xs) = v1 (yl, ys)\<close>
  assumes v2_framing:
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        v2 (xl + xf, xs) = v2 (yl + yf, ys) \<Longrightarrow> v2 (xl, xs) = v2 (yl, ys)\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>F\<^esub>
      { \<top> }
      \<langle> leakL v1 \<rangle> ;;
      \<langle> leakL v2 \<rangle>
      { \<bbbA> v1 \<sqinter> \<bbbA> v2 }\<close>
  apply (rule_tac ?p2.0=\<open>\<bbbA> v1\<close> in rgsat_seq)
   apply (rule rgsat_single_leak[where p=\<top>, simplified])
   apply (metis v1_framing)
  apply (rule rgsat_single_leak[where p=\<open>\<bbbA> v1\<close>, simplified])
  apply (metis v2_framing)
  done


lemma rgsat_sec_guard:
  fixes p :: \<open>('a::perm_alg) \<times> ('b::perm_alg) \<Rightarrow> bool\<close>
  assumes p_framing:
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        p (xl + xf, xs) = p (yl + yf, ys) \<Longrightarrow> p (xl, xs) = p (yl, ys)\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>F\<^esub>
      { \<top> }
      Guard (seclift_pred p \<circ> exch4)
      { \<bbbA> p }\<close>
  apply (rule_tac p=\<top> and q=\<open>\<bbbA> p\<close> in rgsat_atom)
      apply force
     apply force
    apply (force simp add: post_state_def le_fun_def sec_agree_def)
   apply clarsimp
   apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_agree_def split: prod.splits)
   apply (metis p_framing)
  apply force
  done

lemma helper:
  fixes p :: \<open>('a::perm_alg) \<times> ('b::perm_alg) \<Rightarrow> bool\<close>
  assumes p_framing:
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        p (xl + xf, xs) = p (yl + yf, ys) \<Longrightarrow> p (xl, xs) = p (yl, ys)\<close>
  shows
    \<open>- (seclift_pred p \<circ> exch4) = (seclift_pred (-p) \<circ> exch4)\<close>
  apply (simp add: exch4_def seclift_pred_def fun_eq_iff)
  oops

definition
  \<open>SecIfThenElse p ct cf \<equiv>
    Guard (seclift_pred p \<circ> exch4) ;; ct \<box> Guard (seclift_pred (-p) \<circ> exch4) ;; cf\<close>

lemma sec_ifthenelse_complete:
  fixes p :: \<open>('a::perm_alg) \<times> ('b::perm_alg) \<Rightarrow> bool\<close>
  shows \<open>(seclift_pred p \<circ> exch4) \<squnion> (seclift_pred (-p) \<circ> exch4) = \<top>\<close>
  apply (clarsimp simp add: seclift_pred_def exch4_def fun_eq_iff)
  apply (rename_tac a a' b b')
  oops
  

lemma
  fixes p :: \<open>('a::perm_alg) \<times> ('b::perm_alg) \<Rightarrow> bool\<close>
  assumes p_framing:
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        p (xl + xf, xs) = p (yl + yf, ys) \<Longrightarrow> p (xl, xs) = p (yl, ys)\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>F\<^esub>
      { \<top> }
      SecIfThenElse p Skip Skip
      { \<bbbA> p \<squnion> \<bbbA> (-p) }\<close>
  unfolding SecIfThenElse_def
  apply -
  apply (rule_tac ?g1.0=\<top> and ?g2.0=\<top> and ?q1.0=\<open>\<bbbA> p\<close> and ?q2.0=\<open>\<bbbA> (-p)\<close> in rgsat_endet)
       apply (rule_tac rgsat_seq[OF _ rgsat_skip])
        apply (rule rgsat_sec_guard)
        apply (metis assms)
       apply force
      apply (rule_tac rgsat_seq[OF _ rgsat_skip])
       apply (rule rgsat_sec_guard)
       apply (force simp add: p_framing)
      apply force
     apply force
    apply force
   apply force
  apply force
  done


lemma
  fixes p :: \<open>('a::perm_alg) \<times> ('b::perm_alg) \<Rightarrow> bool\<close>
  assumes p_strong_framing:
    \<open>\<And>xf yf xl xs.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow>  p (xl + xf, xs) \<longleftrightarrow> p (xl, xs)\<close>
    \<open>\<And>xf yf yl ys.
      F (xf,yf) \<Longrightarrow> yl ## yf \<Longrightarrow>  p (yl + yf, ys) \<longleftrightarrow> p (yl, ys)\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>F\<^esub>
      { \<top> }
      IfThenElse (seclift_pred p \<circ> exch4) Skip Skip
      { \<bool> p \<squnion> -(\<bool> p) }\<close>
  unfolding IfThenElse_def
  apply -
  apply (rule_tac ?g1.0=\<top> and ?g2.0=\<top> and ?q1.0=\<open>\<bool> p\<close> and ?q2.0=\<open>- \<bool> p\<close> in rgsat_endet)
       apply (rule_tac rgsat_seq[OF _ rgsat_skip])
        apply (rule_tac p=\<top> and q=\<open>\<bool> p\<close> and q'=\<open>\<bool> p\<close> in rgsat_atom)
            apply force
           apply force
          apply (force simp add: post_state_def le_fun_def sec_both_def)
         apply clarsimp
         apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_both_def split: prod.splits)
         apply (metis assms)
        apply force
       apply force
      apply (rule_tac rgsat_seq[OF _ rgsat_skip])
       apply (rule_tac p=\<top> and q=\<open>- \<bool> p\<close> and q'=\<open>- \<bool> p\<close> in rgsat_atom)
           apply force
          apply force
         apply (clarsimp simp add: post_state_def sec_both_def; fail)
        apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_both_def split: prod.splits)
        apply (metis assms)
       apply (clarsimp simp add: post_state_def sec_both_def; fail)
      apply force
     apply force
    apply force
   apply force
  apply force
  done

lemma agree_pred_impl_both_or_both_not:
  \<open>\<bbbA> p \<le> \<bool> p \<squnion> \<bool> (-p)\<close>
  by (simp add: sec_agree_def sec_both_def exch4_def le_fun_def)


lemma sec_if_then_else:
  fixes p :: \<open>('a::perm_alg) \<times> ('b::perm_alg) \<Rightarrow> bool\<close>
  assumes p_framing:
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        p (xl + xf, xs) \<and> p (yl + yf, ys) \<Longrightarrow> p (xl, xs) \<and> p (yl, ys)\<close>
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        \<not> p (xl + xf, xs) \<or> \<not> p (yl + yf, ys) \<Longrightarrow> \<not> p (xl, xs) \<or> \<not> p (yl, ys)\<close>
    and p_atoms:
      \<open>(=), \<top> \<turnstile>\<^bsub>F\<^esub> { \<bool> p } (\<langle> ctt \<rangle>) { \<bool> q1 }\<close>
      \<open>(=), \<top> \<turnstile>\<^bsub>F\<^esub> { \<bool> (-p) } (\<langle> cff \<rangle>) { \<bool> q2 }\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>F\<^esub>
      { \<bbbA> p }
      IfThenElse (seclift_pred p \<circ> exch4) (\<langle> ctt \<rangle>) (\<langle> cff \<rangle>)
      { \<bool> q1 \<squnion> \<bool> q2 }\<close>
  unfolding IfThenElse_def
  apply -
  apply (rule_tac ?g1.0=\<top> and ?g2.0=\<top> and ?q1.0=\<open>\<bool> q1\<close> and ?q2.0=\<open>\<bool> q2\<close> in rgsat_endet)
       apply (rule_tac rgsat_seq)
        apply (rule_tac p=\<open>\<bbbA> p\<close> and q=\<open>\<bool> p\<close> and q'=\<open>\<bool> p\<close> in rgsat_atom)
            apply force
           apply force
          apply (clarsimp simp add: sec_both_def sec_agree_def post_state_def le_fun_def
      seclift_pred_def exch4_def pguard_def sp_def; fail)
         apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_both_def split: prod.splits)
         apply (metis assms(1))
        apply force
       apply (metis assms(3))
      apply (rule_tac rgsat_seq)
       apply (rule_tac p=\<open>\<bbbA> p\<close> and q=\<open>\<bool> (-p)\<close> and q'=\<open>\<bool> (-p)\<close> in rgsat_atom)
           apply force
          apply force
         apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_both_def sec_agree_def split: prod.splits;
      fail)
        apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_both_def sec_agree_def split: prod.splits)
        apply (metis p_framing(2))
       apply force
      apply (metis assms(4))
     apply force
    apply force
   apply force
  apply force
  done


end