theory SecRGSep
  imports "../RGLogic"
begin

definition
  \<open>major \<equiv> \<lambda>((x,x'), (y,y')). (x, y)\<close>

definition
  \<open>minor \<equiv> \<lambda>((x,x'), (y,y')). (x', y')\<close>

definition
  \<open>exch4 \<equiv> \<lambda>((a,b),(c,d)). ((a,c),(b,d))\<close>

definition
  \<open>rel_exch4 r \<equiv> \<lambda>a b. r (exch4 a) (exch4 b)\<close>

type_synonym ('a,'b) secstate = \<open>(('a \<times> 'a) \<times> ('b \<times> 'b))\<close>


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

abbreviation
  \<open>Output v \<equiv> Assert (\<bbbA> v)\<close>

abbreviation
  \<open>Leak v \<equiv> Assume (\<bbbA> v)\<close>

(*
lemma
    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub>
      { \<bbbA> v }
      \<langle> output v \<rangle>
      { \<top> }\<close>
*)

(*
    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub>
      { p \<mapsto> \<midarrow> }
      [p] := e
      { p \<mapsto> e }\<close>

    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub>
      { \<not> (p \<mapsto> \<midarrow>) }
      [p] := e
      { X }\<close>
    ???
*)

definition disjoint_conj :: \<open>'a::disjoint \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> (infix \<open>##\<^sub>\<and>\<close> 50)where
  \<open>a ##\<^sub>\<and> b \<equiv> fst a ## fst b \<and> snd a = snd b\<close>

definition plus_conj :: \<open>'a::plus \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> (infix \<open>+\<^sub>\<and>\<close> 50)where
  \<open>a +\<^sub>\<and> b \<equiv> (fst a + fst b, snd a)\<close>

abbreviation dupst :: \<open>'a \<times> 'b \<Rightarrow> ('a \<times> 'a) \<times> ('b \<times> 'b)\<close> (\<open>\<bbbD>\<close>) where
  \<open>\<bbbD> s \<equiv> exch4 (s, s)\<close>

lemma rgsat_single_leak:
  fixes p :: \<open>('a::perm_alg,'b) secstate \<Rightarrow> bool\<close>
    and v :: \<open>'a \<times> 'b \<Rightarrow> 'v\<close>
    and S F :: \<open>('a::perm_alg,'b) secstate \<Rightarrow> bool\<close>
  assumes
    \<open>\<forall>f\<le>F. (p \<^emph>\<and> f) \<sqinter> \<bbbA> v \<le> (p \<sqinter> \<bbbA> v) \<^emph>\<and> f\<close>
    \<open>p \<le> S\<close>
  shows
    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub> { p } Leak v { p \<sqinter> \<bbbA> v }\<close>
  apply (rule_tac p=p and q=\<open>p \<sqinter> \<bbbA> v\<close> and p'=p in rgsat_assume)
       apply (simp add: assms(1); fail)
      apply force
     apply force
    apply force
   apply force
  apply (simp add: assms(2); fail)
  done

definition emp_conj :: \<open>'a::perm_alg \<times> 'b \<Rightarrow> bool\<close> (\<open>emp\<^sub>1\<close>) where
  \<open>emp\<^sub>1 \<equiv> sepadd_unit \<circ> fst\<close>

lemma emp1_unit_sepconj_conj_left[simp]:
  fixes p :: \<open>('a::multiunit_sep_alg \<times> 'b) \<Rightarrow> bool\<close>
  shows \<open>emp\<^sub>1 \<^emph>\<and> p = p\<close>
  apply (clarsimp simp add: sepadd_unit_def sepconj_conj_def emp_conj_def fun_eq_iff)
  apply (metis disjoint_sym partial_add_commute unitof_disjoint unitof_is_unitR2)
  done

lemma frame_safe_pred_conj_helper_counterexample:
  fixes p :: \<open>('a::multiunit_sep_alg,'b) secstate \<Rightarrow> bool\<close>
    and v1 :: \<open>'a \<times> 'b \<Rightarrow> 'v1\<close>
    and v2 :: \<open>'a \<times> 'b \<Rightarrow> 'v2\<close>
  shows
    \<open>F = \<top> \<Longrightarrow>
      p = emp\<^sub>1 \<Longrightarrow>
      \<forall>f\<le>F. (p \<^emph>\<and> f) \<sqinter> \<bbbA> v2 \<le> (p \<sqinter> \<bbbA> v2) \<^emph>\<and> f \<Longrightarrow>
      \<forall>f\<le>F. ((p \<sqinter> \<bbbA> v1) \<^emph>\<and> f) \<sqinter> \<bbbA> v2 \<le> (p \<sqinter> \<bbbA> v1 \<sqinter> \<bbbA> v2) \<^emph>\<and> f\<close>
  apply clarsimp
  nitpick[card 'v1=2, card 'v2=2, card 'a=3, card 'b=1]
  sorry

lemma
  fixes p :: \<open>('a::perm_alg,'b) secstate \<Rightarrow> bool\<close>
    and v :: \<open>'a \<times> 'b \<Rightarrow> 'v\<close>
    and S F :: \<open>('a::perm_alg,'b) secstate \<Rightarrow> bool\<close>
  assumes
    \<open>\<forall>f\<le>F. (p \<^emph>\<and> f) \<sqinter> \<bbbA> v1 \<le> (p \<sqinter> \<bbbA> v1) \<^emph>\<and> f\<close>
    \<open>\<forall>f\<le>F. ((p \<sqinter> \<bbbA> v1) \<^emph>\<and> f) \<sqinter> \<bbbA> v2 \<le> (p \<sqinter> \<bbbA> v1 \<sqinter> \<bbbA> v2) \<^emph>\<and> f\<close>
    \<open>p \<le> S\<close>
  shows
    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub> { p } Leak v1 ;; Leak v2 { p \<sqinter> \<bbbA> v1 \<sqinter> \<bbbA> v2 }\<close>
  apply (rule_tac ?p2.0=\<open>p \<sqinter> \<bbbA> v1\<close> in rgsat_seq)
    apply (rule rgsat_single_leak)
     apply (simp add: assms(1); fail)
    apply (rule order.refl)
   apply (rule rgsat_single_leak)
    apply (simp add: assms(2); fail)
   apply (rule order.refl)
  apply (simp add: assms(3))
  done


lemma rgsat_sec_guard:
  fixes p :: \<open>('a::perm_alg) \<times> ('b::perm_alg) \<Rightarrow> bool\<close>
  assumes p_framing:
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        p (xl + xf, xs) = p (yl + yf, ys) \<Longrightarrow> p (xl, xs) = p (yl, ys)\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>S, F\<^esub>
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
  \<open>\<bbbA> p \<le> \<bbbA> (-p)\<close>
  by (clarsimp simp add: sec_agree_def exch4_def fun_eq_iff)


lemma
  fixes p :: \<open>('a::perm_alg) \<times> ('b::perm_alg) \<Rightarrow> bool\<close>
  assumes p_framing:
    \<open>\<And>xf yf xl xs yl ys.
      F (xf,yf) \<Longrightarrow> xl ## xf \<Longrightarrow> yl ## yf \<Longrightarrow>
        p (xl + xf, xs) = p (yl + yf, ys) \<Longrightarrow> p (xl, xs) = p (yl, ys)\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>S, F\<^esub>
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
    \<open>(=), \<top> \<turnstile>\<^bsub>S, F\<^esub>
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
      \<open>(=), \<top> \<turnstile>\<^bsub>S, F\<^esub> { \<bool> p } ctt { \<bool> q1 }\<close>
      \<open>(=), \<top> \<turnstile>\<^bsub>S, F\<^esub> { \<bool> (-p) } cff { \<bool> q2 }\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>S, F\<^esub>
      { \<bbbA> p }
      IfThenElse (seclift_pred p \<circ> exch4) ctt cff
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