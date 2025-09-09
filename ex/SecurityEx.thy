theory SecurityEx
  imports "../sec/Semantics"
begin

section \<open> Examples \<close>

(* TODO: move *)

subsection \<open> Wordle \<close>

type_synonym varnm = \<open>char list\<close>
type_synonym wordle_ls = \<open>varnm \<rightharpoonup> char list discr \<times> munit\<close>
type_synonym wordle_ss = \<open>varnm \<Rightarrow> char list\<close>

definition wordle_output
  :: \<open>wordle_ls \<times> wordle_ss \<Rightarrow> bool \<times> nat set\<close>
  where
  \<open>wordle_output \<equiv> \<lambda>(ls, ss).
    let word = the_discr (fst (the (ls ''word'')))
      ; guess = ss ''guess''
    in
    (mset word = mset guess,
      {i. i \<le> max (length word) (length guess) \<longrightarrow> word ! i = guess ! i})\<close>

lemma wordle_output_local_reduce:
  \<open>lsa ## lsb \<Longrightarrow>
    lsa ''word'' \<noteq> None \<Longrightarrow>
    wordle_output (lsa + lsb, ss) = wordle_output (lsa, ss)\<close>
  apply (clarsimp simp add: wordle_output_def Let_def disjoint_fun_def)
  apply (subgoal_tac \<open>lsa ''word'' ## lsb ''word''\<close>)
   apply force
  apply metis
  done

lemma wordle_output_agree_frame_local:
  fixes p F :: \<open>(wordle_ls \<times> wordle_ls) \<times> (wordle_ss \<times> wordle_ss) \<Rightarrow> bool\<close>
  assumes \<open>post_state (curry p) \<le> post_state (curry F)\<close>
    and \<open>p \<le> \<lblot>\<lambda>(ls, ss). ls ''word'' \<noteq> None\<rblot> \<circ> exch4\<close>
  shows \<open>frame_local F p (\<bbbA> wordle_output \<circ> exch4)\<close>
  using assms
  apply (simp add: frame_local_def le_fun_def post_state_def)
  apply (rule conjI[rotated], blast)
  apply (clarsimp simp add: sec_agree_def sepconj_conj_apply)
  apply (subst (asm) wordle_output_local_reduce, blast, blast)
  apply (subst (asm) wordle_output_local_reduce, blast, blast)
  apply blast
  done


(* TODO: move *)

lemma eq_rtimes_R_iff:
  \<open>((=) \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s') \<and> fst s = fst s'\<close>
  by (cases s, cases s', force)

lemma top_rtimes_R_iff:
  \<open>(\<top> \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s')\<close>
  by (cases s, cases s', force)

(* TODO: write examples: (1) Arthur's nointerference, (2) observing local state *)

lemma sepimp_conj_step_mp:
  \<open>p \<le> p' \<Longrightarrow> (p' \<midarrow>\<^emph>\<^sub>\<and> q) \<^emph>\<and> p \<le> q\<close>
  by (meson order_refl sepimp_conj_mono sepimp_conj_sepconj_conj_shunt)

lemma comp2_exch4_over_rel_times[simp]:
  fixes ra :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
    and rb :: \<open>'b \<Rightarrow> 'b \<Rightarrow> bool\<close>
  shows \<open>((ra \<times>\<^sub>R rb) \<times>\<^sub>R (rc \<times>\<^sub>R rd)) \<circ>\<^sub>2 exch4 = ((ra \<times>\<^sub>R rc) \<times>\<^sub>R (rb \<times>\<^sub>R rd))\<close>
  by (force simp add: comp_rel_def exch4_def rel_Times_def)

lemma example_observing_local_state:
  fixes F :: \<open>(('p \<rightharpoonup> 'v::perm_alg) \<times> ('p \<rightharpoonup> 'v)) \<times> ('h \<times> 'h) \<Rightarrow> bool\<close>
  assumes
    \<open>x \<noteq> y\<close>
  shows
    \<open>(=), (=) \<turnstile>\<^bsub>F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4), F\<^esub>
    { (F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)) }
      liftC (\<langle>\<top>, (\<lambda>hl hl'. hl' = hl(x \<mapsto> v)) \<times>\<^sub>R (=)\<rangle>)
    { (F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)) }\<close>
  apply (simp add: liftC_def)
  apply (rule rgsat_atom[of _ _
        \<open>F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)\<close>
        \<open>F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)\<close>
        ])
        apply force
       apply force
      apply force
     apply force
    apply force
   apply clarsimp
   apply (clarsimp simp add: sp_def sepconj_conj_def sepimp_conj_def split: prod.splits)
  sorry


definition
  \<open>location_independent Pt \<equiv> \<lambda>(p,q).
    \<forall>h h' s s'.
      p (h, s) \<longrightarrow>
      q (h, s) (h', s') \<longrightarrow>
      (\<forall>\<sigma>.
        bij \<sigma> \<longrightarrow>
        (\<forall>\<rho>. \<rho> \<notin> Pt \<longrightarrow> \<sigma> \<rho> = \<rho>) \<longrightarrow>
        p (h \<circ> \<sigma>, s) \<and> q (h \<circ> \<sigma>, s) (h' \<circ> \<sigma>, s'))\<close>

definition
  \<open>value_independent Pt \<equiv> \<lambda>(p,q).
    \<forall>h h' s s'.
      p (h, s) \<longrightarrow>
      q (h, s) (h', s') \<longrightarrow>
      (\<forall>hx hx'.
        (\<forall>\<rho>. \<rho> \<notin> Pt \<longrightarrow> hx \<rho> = hx' \<rho>) \<longrightarrow>
        p (hx, s) \<and> q (hx, s) (hx', s'))\<close>

lemma example_deAmorim_noninterference:
  fixes S :: \<open>('p \<rightharpoonup> 'l::pre_perm_alg) \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>r, g \<turnstile>\<^bsub>S, F\<^esub> { p } c { q }\<close>
    \<open>\<forall>p q.
        (p,q) \<in> all_atoms c \<longrightarrow>
        (\<forall>x x'. (S \<^emph>\<and> F) x \<longrightarrow> p x \<longrightarrow> q x x' \<longrightarrow>
          {\<rho>. fst x \<rho> \<noteq> fst x' \<rho>} \<subseteq> V)\<close>
  shows
    \<open>liftR r, liftR g \<turnstile>\<^bsub>\<bbbA> f \<circ> exch4, liftP F \<circ> exch4\<^esub> { liftP p \<circ> exch4 } liftC c { liftP q \<circ> exch4 }\<close>
  sorry

lemma opstep_all_atoms_antimono:
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    all_atoms c' \<le> all_atoms c\<close>
  apply (induct \<alpha> sc sc' arbitrary: s c s' c' rule: opstep.induct)
        apply force
       apply force
      apply force
     apply clarsimp
     apply (elim disjE conjE; clarsimp; blast)
    apply clarsimp
    apply (elim disjE conjE; clarsimp; blast)
   apply (clarsimp split: if_splits; fail)
  apply (clarsimp split: if_splits; fail)
  done


\<comment> \<open> note the instantiation of X to \<open>(FF \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> \<oo> \<circ> exch4))\<close> \<close>
lemma pred_preserved_then_pred_all_states:
  fixes c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
  assumes
    \<open>safe n c z r g q S F\<close>
    \<open>z = s\<close>
    \<open>\<forall>s s'. ((=) \<times>\<^sub>R r) s s' \<longrightarrow> S s \<longrightarrow> X s \<longrightarrow> X s'\<close>
    \<open>\<forall>p q. (p, q) \<in> all_atoms c \<longrightarrow>
      (\<forall>hl hs hl' hs'.
        (\<forall>fl.
          hl ## fl \<longrightarrow> F (fl, hs) \<longrightarrow> hl' ## fl \<longrightarrow>
          p (hl + fl, hs) \<longrightarrow> q (hl + fl, hs) (hl' + fl, hs') \<longrightarrow>
          S (hl, hs) \<longrightarrow>
          X (hl, hs) \<longrightarrow> X (hl', hs')))\<close>
    \<open>X s\<close>
  shows
    \<open>safe n c z r g q X F\<close>
  using assms
proof (induct n c z r g q S F arbitrary: s rule: safe.induct)
  case (safe_nil S hl hs c r g q F)
  then show ?case by force
next
  case (safe_suc c q hl hs S r n g F)
  then show ?case
    apply (clarsimp simp add: safe_suc_iff eq_rtimes_R_iff top_rtimes_R_iff)
    apply (drule meta_spec2, drule meta_spec2, drule meta_mp, assumption,
        drule meta_mp, assumption, drule meta_mp, assumption)
    apply clarsimp
    apply (rule_tac x=hl' in exI)
    apply clarsimp
    apply (drule mp[of \<open>All _\<close>])
     apply (meson opstep_all_atoms_antimono subsetD; fail)
    apply clarsimp
    apply (erule opstep_act_cases, force)
    apply (frule vis_step_impl_atom)
    apply clarsimp
    apply (drule spec2, drule mp, rule set_mp[OF head_atoms_subseteq_all_atoms], assumption)
    apply metis
    done
qed


subsection \<open> Aaaaa \<close>

lemma pair_predicate_splitting:
  fixes P :: \<open>'a \<times> 'a \<Rightarrow> bool\<close>
  shows \<open>\<exists>p \<oo>::'a \<Rightarrow> 'v. P = \<lblot> p \<rblot> \<sqinter> \<bbbA> \<oo>\<close>
  nitpick[card 'a=2, card 'v=1]
  oops

definition uset where
  \<open>uset P \<equiv> \<lambda>x. {y. P (x,y)}\<close>

definition
  \<open>hyperset (r :: 'a \<times> 'a \<Rightarrow> bool) \<equiv>
    {A. \<exists>x. Ex (curry r x) \<and> A = {y. r (x,y)}}\<close>

definition
  \<open>hrelify (H :: 'a set set) \<equiv>
    \<lambda>(x,y). \<exists>A\<in>H. x\<in>A \<and> y\<in>A\<close>


lemma
  \<open>{} \<notin> H \<Longrightarrow>
    (\<forall>A\<in>H. \<forall>B\<in>H. (\<exists>x. x \<in> A\<inter>B) \<longrightarrow> A \<subseteq> B \<or> B \<subseteq> A) \<longleftrightarrow>
    (\<forall>A\<in>H. \<forall>B\<in>H. A \<subseteq> B \<longrightarrow> A = B)\<close>
  oops

lemma hyperset_hrelify_inverse:
  fixes H :: \<open>'a set set\<close>
  assumes \<open>{} \<notin> H\<close>
  assumes \<open>\<forall>A\<in>H. \<forall>B\<in>H. A \<subseteq> B \<longrightarrow> A = B\<close>
  assumes \<open>supcl H = H\<close>
  assumes ex_defining_member:
    \<open>\<forall>A\<in>H. \<exists>x\<in>A. \<forall>B\<in>H. x \<in> B \<longrightarrow> A \<subseteq> B\<close>
  shows \<open>hyperset (hrelify H) = H\<close>
  apply (simp add: hyperset_def hrelify_def)
  apply (rule set_eqI, rule iffI)
   apply clarsimp
   apply (rename_tac x y A)
   apply (rule subst[OF assms(3), of \<open>\<lambda>X. _ \<in> X\<close>])
   apply (clarsimp simp add: supcl_def)
   apply (rule_tac x=\<open>{A\<in>H. x\<in>A}\<close> in exI)
   apply blast
  apply clarsimp
  apply (rename_tac A)
  apply (cut_tac assms(1))
  apply (subgoal_tac \<open>\<exists>x. x \<in> A\<close>)
   prefer 2
   apply (simp add: ex_in_conv, blast)
  apply clarsimp
  apply (rule_tac
      Q=\<open>\<exists>x. A = {y. \<exists>B\<in>H. x \<in> B \<and> y \<in> B}\<close>
      in iffD1)
   apply blast
  apply (cut_tac ex_defining_member)
  apply (drule bspec, assumption)
  apply clarsimp
  apply (rename_tac a)
  apply (rule_tac x=a in exI)
  apply (rule iffD1[rotated, of \<open>Ball _ _\<close>], assumption)

  sorry

  apply (rule_tac x=x in exI)
  apply (rule Set.equalityI, force)
  apply clarsimp
  apply (rename_tac x y B)

  oops

lemma hrelify_hyperset_inverse:
  fixes r :: \<open>'a \<times> 'a \<Rightarrow> bool\<close>
  assumes \<open>quasireflp (curry r)\<close>
  assumes \<open>symp (curry r)\<close>
  shows \<open>hrelify (hyperset r) = r\<close>
  sledgehammer
  sorry


definition sec_obs (\<open>\<bbbO>\<close>) where
  \<open>sec_obs f \<equiv> \<lambda>(x,y). \<exists>X\<in>f x. \<exists>Y\<in>f y. X \<inter> Y \<noteq> {}\<close>

lemma pair_predicate_splitting:
  fixes P :: \<open>'a \<times> 'a \<Rightarrow> bool\<close>
  assumes \<open>quasireflp (curry P)\<close>
  assumes \<open>symp (curry P)\<close>
  shows \<open>P = \<bbbO> (\<lambda>x. {H. H = {x'. \<forall>y. P (x,y) \<longrightarrow> P (x',y)}})\<close>
  using assms
  apply (clarsimp simp add: fun_eq_iff uset_def sec_obs_def)
  apply (rule iffI)
   apply (clarsimp simp add: set_eq_iff symp_def)

  oops


section \<open> aaaa \<close>

lemma sec_agree_eq_mp:
  \<open>\<bbbA> (\<lambda>s. s x) \<sqinter> \<lblot> \<lambda>s. s x = s y \<rblot> \<le> \<bbbA> (\<lambda>s. s y)\<close>
  by (clarsimp simp add: sec_agree_def)

end