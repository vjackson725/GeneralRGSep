theory SoundnessExperimental
  imports "../../Soundness"
begin

\<comment> \<open> Guar in the frame condition \<close>

lemma
  \<open>(\<forall>f\<le>F. sp ar (p \<^emph>\<and> f) \<le> q \<^emph>\<and> sp ((=) \<times>\<^sub>R G) f) \<longleftrightarrow>
    (\<forall>f\<le>F. sp ar (p \<^emph>\<and> f) \<le> q \<^emph>\<and> any_shared f) \<and>
    (rel_liftL (p \<^emph>\<and> F) \<sqinter> ar \<le> \<top> \<times>\<^sub>R G)\<close>
  apply (intro iffI)
   apply (intro conjI allI impI)
    apply (drule spec, drule mp, assumption)
    apply (rule order.trans, assumption)
    apply (rule sepconj_conj_monoR)
    apply (force simp add: sp_def)
   apply (clarsimp simp add: sepconj_conj_def)
   apply (rename_tac ss lfs' ss' ls fs)
   apply (drule_tac x=\<open>(=) (fs, ss)\<close> in spec, drule mp, force)
   apply (clarsimp simp add: sepconj_conj_def le_fun_def sp_def imp_ex_conjL imp_conjL)
   apply (drule spec2, drule spec2, drule mp, assumption)
   apply (drule spec, drule mp, assumption)
   apply (drule mp, fast)
   apply (drule mp, fast)
   apply (drule mp, fast)
   apply force
  apply clarsimp
  apply (clarsimp simp add: sepconj_conj_apply sp_def imp_ex_conjL imp_conjL le_fun_def)
  oops


lemma
  \<open>a =\<^sub># b \<Longrightarrow> a ## b \<Longrightarrow> a ## a\<close>
  by (meson disjoint_sym sepdomeq_def)


\<comment> \<open> Trying out view shift. You need something more to make it go, though. \<close>

definition (in pre_perm_alg) frame_update
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (\<open>\<bar>\<Rrightarrow>\<^bsub>_\<^esub> _\<close>)
  where
  \<open>\<bar>\<Rrightarrow>\<^bsub>F\<^esub> p \<equiv> \<lambda>a. \<forall>c. F c \<longrightarrow> a ## c \<longrightarrow> (\<exists>b. b ## c \<and> p b)\<close>

definition (in pre_perm_alg) frame_update_conj
  :: \<open>('a \<times> 's \<Rightarrow> bool) \<Rightarrow> ('a \<times> 's \<Rightarrow> bool) \<Rightarrow> ('a \<times> 's \<Rightarrow> bool)\<close> (\<open>\<bar>\<Rrightarrow>\<^sub>\<and>\<^bsub>_\<^esub> _\<close>)
  where
  \<open>\<bar>\<Rrightarrow>\<^sub>\<and>\<^bsub>F\<^esub> p \<equiv> \<lambda>(a,ss). \<forall>c. F (c,ss) \<longrightarrow> a ## c \<longrightarrow> (\<exists>b. b ## c \<and> p (b,ss))\<close>

lemma
  fixes s :: \<open>'l::pre_perm_alg \<times> 's\<close>
  assumes \<open>\<forall>a b::'l. a \<preceq> b \<longrightarrow> {c. a \<preceq> c} \<subseteq> {c. b \<preceq> c}\<close>
  shows \<open>safe R F G I q' n c s \<Longrightarrow> \<top> \<le> (=) s \<midarrow>\<^emph>\<^sub>\<and> \<bar>\<Rrightarrow>\<^sub>\<and>\<^bsub>\<top>\<^esub> q \<Longrightarrow> safe R F G I q n c s\<close>
  apply (induct arbitrary: q rule: safe.induct)
  apply (rule safe.safeI)
     apply (clarsimp simp add: le_fun_def sepimp_conj_def)
  oops

lemma
  fixes p q :: \<open>'a::pre_perm_alg \<Rightarrow> bool\<close>
  assumes \<open>\<forall>a a' b::'a. a ## a' \<longrightarrow> a + a' = b \<longrightarrow> (\<exists>af. F af \<and> a ## af \<and> b = a + af)\<close>
  shows \<open>p \<le> \<bar>\<Rrightarrow>\<^bsub>F\<^esub> q \<Longrightarrow> p \<^emph> F \<le> q \<^emph> F\<close>
  using assms
  unfolding frame_update_def
  apply (clarsimp simp add: le_fun_def sepconj_def)
  apply (drule spec, drule mp, blast, drule spec, drule mp, blast, drule mp,blast)
  apply clarsimp
  apply (drule spec2, drule mp, blast)
  apply clarsimp
  apply (rule_tac x=h1 in exI)
  apply (rule_tac x=af in exI)
  apply simp
  oops


section \<open> Cancellativity \<close>

lemma cancel_attempt1:
  fixes I F :: \<open>'r::perm_alg \<Rightarrow> bool\<close>
  defines \<open>lhs \<equiv> (\<forall>a b f. I a \<longrightarrow> I b \<longrightarrow> F f \<longrightarrow> a ## f \<longrightarrow> b ## f \<longrightarrow> a+f = b+f \<longrightarrow> a = b)\<close>
    and \<open>rhs \<equiv> (\<forall>ia\<le>I. \<forall>ib\<le>I. \<forall>f\<le>F. ia \<^emph> f \<noteq> \<bottom> \<longrightarrow> (ia \<^emph> f) = (ib \<^emph> f) \<longrightarrow> ia = ib)\<close>
  shows \<open>rhs \<Longrightarrow> lhs\<close>
    and \<open>R = {(a,b,a+b)|a b::'r. a ## b} \<Longrightarrow> lhs \<Longrightarrow> rhs\<close>
  unfolding lhs_def rhs_def
  apply -
    (* subgoal 1: rhs \<Rightarrow> lhs *)
   apply clarsimp
   apply (drule_tac x=\<open>(=) a\<close> in spec, drule mp, fast)
   apply (drule_tac x=\<open>(=) b\<close> in spec, drule mp, fast)
   apply (drule_tac x=\<open>(=) f\<close> in spec, drule mp, fast)
   apply (simp add: fun_eq_iff; fail)
    (* subgoal 2: lhs \<Rightarrow> rhs *)
  nitpick[card 'r=2]
  oops


section \<open> Fictional Separation Logic \<close>

definition
  \<open>perm_alg_homomorphism (f :: 'a::pre_perm_alg \<Rightarrow> 'b::pre_perm_alg) \<equiv>
    (\<forall>a b. a ## b \<longrightarrow> f a ## f b) \<and>
    (\<forall>a b. a ## b \<longrightarrow> f (a + b) = f a + f b)\<close>

definition
  \<open>perm_alg_diff_homomorphism f \<equiv>
    perm_alg_homomorphism f \<and>
    (\<forall>ax by cx. by ## f cx \<longrightarrow> f ax = by + f cx \<longrightarrow> (\<exists>bx. by = f bx \<and> bx ## cx \<and> ax = bx + cx))\<close>

lemma
  \<open>perm_alg_homomorphism (f :: 'a::perm_alg \<Rightarrow> 'b::perm_alg) \<Longrightarrow>
    \<forall>a b. (((=) a) \<midarrow>\<odot> ((=) b)) \<circ> f \<le> (((=) a) \<circ> f) \<midarrow>\<odot> (((=) b) \<circ> f) \<Longrightarrow>
    \<forall>p q. (p \<midarrow>\<odot> q) \<circ> f \<le> (p \<circ> f) \<midarrow>\<odot> (q \<circ> f)\<close>
  unfolding septract_def perm_alg_homomorphism_def
  by (simp add: fun_eq_iff le_fun_def) metis

lemma
  \<open>\<forall>xa yb. f xa ## yb \<longrightarrow> (\<exists>ya. xa ## ya \<and> yb = f ya \<and> f xa + yb = f (xa + ya))\<close>
  oops

lemma
  \<open>perm_alg_homomorphism (f :: 'a::pre_perm_alg \<Rightarrow> 'b::pre_perm_alg) \<Longrightarrow>
    \<forall>p q. (p \<midarrow>\<odot> q) \<circ> f \<le> (p \<circ> f) \<midarrow>\<odot> (q \<circ> f) \<Longrightarrow>
    \<forall>p q. (p \<midarrow>\<odot> q) \<circ> f = (p \<circ> f) \<midarrow>\<odot> (q \<circ> f)\<close>
  unfolding septract_def perm_alg_homomorphism_def
  by (simp add: fun_eq_iff le_fun_def) metis

lemma perm_alg_homomorphism_iff_sepconj_semidistrib:
  fixes f :: \<open>'x::perm_alg \<Rightarrow> 'y::perm_alg\<close>
  shows
    \<open>perm_alg_homomorphism f \<longleftrightarrow>
      (\<forall>p q. (p \<circ> f) \<^emph> (q \<circ> f) \<le> (p \<^emph> q) \<circ> f)\<close>
  unfolding perm_alg_homomorphism_def
  apply (intro iffI)
   apply (fastforce simp add: sepconj_def le_fun_def)
  apply (clarsimp simp add: all_conj_distrib[symmetric])
  apply (drule_tac x=\<open>(=) (f a)\<close> and y=\<open>(=) (f b)\<close> in spec2)
  apply force
  done


lemma perm_alg_diff_homomorphism_iff:
  fixes f :: \<open>'x::perm_alg \<Rightarrow> 'y::perm_alg\<close>
  assumes \<open>perm_alg_homomorphism f\<close>
  shows
    \<open>perm_alg_diff_homomorphism f \<longleftrightarrow>
      (\<forall>p q. (p \<circ> f) \<midarrow>\<odot> (q \<circ> f) = (p \<midarrow>\<odot> q) \<circ> f)\<close>
  using assms
  unfolding perm_alg_homomorphism_def perm_alg_diff_homomorphism_def
  apply (clarsimp simp add: septract_def le_fun_def fun_eq_iff)
  apply (intro iffI allI)
    apply metis
   apply clarsimp
  apply (rename_tac cx "by")
  oops

definition
  \<open>perm_alg_hm_nice (f :: 'b::pre_perm_alg \<Rightarrow> 'a::pre_perm_alg) \<equiv>
    \<forall>ax ay::'a. \<forall>bxy by::'b::pre_perm_alg.
      ax ## f by \<longrightarrow>
      f bxy = ax + f by \<longrightarrow>
      (\<exists>bx. bx ## by \<and> ax = f bx \<and> bxy = bx + by)\<close>

lemma perm_alg_hm_nice_def2:
  fixes f :: \<open>'b::pre_perm_alg \<Rightarrow> 'a::pre_perm_alg\<close>
  shows
    \<open>perm_alg_hm_nice f \<longleftrightarrow>
      (\<forall>ax::'a. \<forall>bxy::'b.
        ((=) ax \<midarrow>\<odot> (=) (f bxy)) \<circ> f \<le> ((=) ax \<circ> f) \<midarrow>\<odot> (=) bxy
      )\<close>
  unfolding septract_def
  by (clarsimp simp add: perm_alg_hm_nice_def le_fun_def sepimp_def)
    (rule iffI; metis disjoint_sym partial_add_commute)

\<comment> \<open>
  Still weaker than \<open>(p \<midarrow>\<odot> q) \<circ> f \<le> (p \<circ> f) \<midarrow>\<odot> (q \<circ> f)\<close>
\<close>
lemma perm_alg_hm_nice_def3:
  fixes f :: \<open>'b::pre_perm_alg \<Rightarrow> 'a::pre_perm_alg\<close>
  shows
    \<open>perm_alg_hm_nice f \<longleftrightarrow>
      (\<forall>p. \<forall>b. (p \<midarrow>\<odot> (=) (f b)) \<circ> f \<le> (p \<circ> f) \<midarrow>\<odot> (=) b)\<close>
  by (force simp add: perm_alg_hm_nice_def2 septract_def fun_eq_iff le_fun_def)

lemma perm_alg_hm_nice_implies_strict_revmono:
  fixes f :: \<open>'b::perm_alg \<Rightarrow> 'a::perm_alg\<close>
  assumes \<open>perm_alg_hm_nice f\<close>
  shows \<open>\<forall>bx by::'b. f bx \<prec> f by \<longrightarrow> bx \<prec> by\<close>
  using assms
  unfolding perm_alg_hm_nice_def
  by (simp add: less_sepadd_def)
    (metis disjoint_sym_iff partial_add_commute positivity)

definition
  \<open>perm_alg_homomorphism_strong f \<equiv>
    perm_alg_homomorphism f \<and>
    (\<forall>xya xb yb. xb ## yb \<longrightarrow> f xya = xb + yb \<longrightarrow>
      (\<exists>xa ya. xa ## ya \<and> xb = f xa \<and> yb = f ya \<and> xya = xa + ya))\<close>


\<comment> \<open>
  Related to
    Jonas Braband Jensen and Lars Birkedal. 2012. Fictional Separation Logic.
    ESOP 2012, LNCS 7211, pp. 377–396.
\<close>
lemma algebra_abstraction:
  fixes b2a :: \<open>'lb::pre_perm_alg \<Rightarrow> 'la::pre_perm_alg\<close>
    and sb :: \<open>'lb::pre_perm_alg \<times> 's\<close>
    and F I :: \<open>'la \<times> 's \<Rightarrow> bool\<close>
  assumes f_sepconj_hm: \<open>perm_alg_homomorphism b2a\<close>
    and \<open>perm_alg_hm_nice b2a\<close>
  shows
  \<open>safe R F G I q n c sa \<Longrightarrow>
    sa = apfst b2a sb \<Longrightarrow>
    safe R (F \<circ> apfst b2a) G (I \<circ> apfst b2a) (q \<circ> apfst b2a) n (map_atom (\<lambda>r. r \<circ>\<^sub>2 apfst b2a) c) sb\<close>
proof (induct arbitrary: sb rule: safe.inducts)
  case (safeI c sa n)
  show ?case
    using safeI.prems safeI.hyps(1-2)
    apply (clarsimp simp del: comp_apply comp2_apply)
    apply (rule safe.safeI)
        apply (force simp add: map_atom_rev_iff)
       apply force
      apply (frule safeI.hyps(4)[where sb=\<open>(sbl, sbs)\<close> for sbl sbs]; force)
      (* non-framed step *)
     apply (subgoal_tac \<open>\<exists>cb'. c' = map_atom (\<lambda>r. r \<circ>\<^sub>2 apfst b2a) cb'\<close>)
      prefer 2
    subgoal sorry
     apply (elim exE)
     apply (frule_tac \<alpha>=\<alpha> and s'=\<open>apfst b2a s'\<close> and c'=cb' in safeI.hyps(5))
      apply (clarsimp simp del: comp_apply comp2_apply)
    subgoal sorry
     apply (clarsimp simp del: comp_apply comp2_apply)
     apply (metis (no_types, lifting) fst_conv opstep_tau_preserves_heap)
      (* framed step *)
     apply (subgoal_tac \<open>\<exists>cb'. c' = map_atom (\<lambda>r. r \<circ>\<^sub>2 apfst b2a) cb'\<close>)
      prefer 2
    subgoal sorry
    apply (elim exE)
    apply (frule_tac \<alpha>=\<alpha> and lfs'=\<open>b2a lfs'\<close> and ss'=ss' and fs=\<open>b2a fs\<close> and c'=cb' in safeI.hyps(6))
       apply (clarsimp simp del: comp_apply comp2_apply)
    subgoal sorry
      apply (simp, metis f_sepconj_hm perm_alg_homomorphism_def)
     apply force
    apply (elim exE conjE)
    apply (rule conjI)
     apply force
    apply (clarsimp simp del: comp_apply comp2_apply)
    apply (cut_tac assms(2))
    apply (metis (no_types, lifting) fst_conv opstep_tau_preserves_heap perm_alg_hm_nice_def)
    done
qed

lemma sswa_apfst_apply[simp]:
  \<open>sswa R (\<lambda>x. p (apfst f x)) (ls, ss) = sswa R p (f ls, ss)\<close>
  by (clarsimp simp add: sp_def fun_eq_iff)

lemma sswa_comp_apfst_eq:
  \<open>sswa R (p \<circ> apfst f) = sswa R p \<circ> apfst f\<close>
  by (clarsimp simp add: sp_def fun_eq_iff)

lemma sup_comp_apfst_distrib:
  \<open>(pa \<squnion> pb) \<circ> apfst f = (pa \<circ> apfst f) \<squnion> (pb \<circ> apfst f)\<close>
  by (clarsimp simp add: fun_eq_iff)

lemma inf_comp_apfst_distrib:
  \<open>(pa \<sqinter> pb) \<circ> apfst f = (pa \<circ> apfst f) \<sqinter> (pb \<circ> apfst f)\<close>
  by (clarsimp simp add: fun_eq_iff)

lemma sepconjconj_comp_apfst_semidistrib:
  assumes \<open>perm_alg_homomorphism f\<close>
  shows \<open>(pa \<circ> apfst f) \<^emph>\<and> (pb \<circ> apfst f) \<le> (pa \<^emph>\<and> pb) \<circ> apfst f\<close>
  using assms
  by (clarsimp simp add: perm_alg_homomorphism_def sepconj_conj_def, blast)

lemma sepconjconj_comp_apfst_distrib:
  assumes \<open>perm_alg_homomorphism_strong f\<close>
  shows \<open>(pa \<circ> apfst f) \<^emph>\<and> (pb \<circ> apfst f) = (pa \<^emph>\<and> pb) \<circ> apfst f\<close>
  using assms
  unfolding perm_alg_homomorphism_def perm_alg_homomorphism_strong_def
  by (clarsimp simp add: sepconj_conj_def fun_eq_iff, fast)

lemma rel_liftL_comp_semidistrib:
  \<open>rel_liftL (p \<circ> f) \<le> rel_liftL p \<circ>\<^sub>2 f\<close>
  by force

















\<comment> \<open> Old \<close>
section \<open> Alternate safe with restricted rely condition \<close>

subsubsection \<open> Safe alternates \<close>

lemma safe_suc_iff_frame_alt:
  \<open>safe (Suc n) c (Inl s) r g q S F \<Longrightarrow>
    (c = Skip \<longrightarrow> q s) \<and>
    S s \<and>
    \<comment> \<open> note the assumption here \<close>
    ((\<exists>hlf. F (hlf, snd s) \<and> fst s ## hlf) \<longrightarrow>
      (\<forall>hs'. r (snd s) hs' \<longrightarrow> safe n c (Inl (fst s, hs')) r g q S F)) \<and>
    (\<forall>hlf.
      F (hlf, snd s) \<longrightarrow>
      fst s ## hlf \<longrightarrow>
      (\<forall>\<alpha> z' c'.
        ((fst s + hlf, snd s), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<longrightarrow>
        (\<exists>hlhlf' hs'.
          z' = Inl (hlhlf',hs') \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> g (snd s) hs') \<and>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = fst s) \<and>
            safe n c' (Inl (hl',hs')) r g q S F))))\<close>
  by (simp add: safe_suc_iff)
  \<comment> \<open> this is obviously only weaker than the original \<close>

\<comment> \<open> this is probably the one we actually want \<close>
lemma safe_iff_frame_alt2:
    \<open>(c = Skip \<longrightarrow> q s) \<and>
      S s \<and>
      \<comment> \<open> note the additional test \<close>
      (\<exists>hlf. F (hlf, snd s) \<and> fst s ## hlf) \<and>
      (0 < n \<longrightarrow>
        (\<forall>hs'. r (snd s) hs' \<longrightarrow> safe (n-1) c (Inl (fst s, hs')) r g q S F) \<and>
        (\<forall>hlf.
          F (hlf, snd s) \<longrightarrow>
          fst s ## hlf \<longrightarrow>
          (\<forall>\<alpha> z' c'.
            ((fst s + hlf, snd s), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<longrightarrow>
            (\<exists>hlhlf' hs'.
              z' = Inl (hlhlf',hs') \<and>
              (\<alpha> \<noteq> Tau \<longrightarrow> g (snd s) hs') \<and>
              (\<exists>hl'.
                hl' ## hlf \<and>
                hlhlf' = hl' + hlf \<and>
                (\<alpha> = Tau \<longrightarrow> hl' = fst s) \<and>
                safe (n-1) c' (Inl (hl',hs')) r g q S F))))) \<Longrightarrow>
    safe n c (Inl s) r g q S F\<close>
  apply (induct n arbitrary: s r)
   apply force
  apply (simp add: safe_suc_iff)
  done


section \<open> Safe2 \<close>

definition safe2 where
  \<open>safe2 n c (s :: 'l::pre_perm_alg \<times> 's + unit) r g q S F \<equiv>
    \<exists>hl hs. s = Inl (hl, hs) \<and>
      (if n > 0 then
        (c = Skip \<longrightarrow> q (hl, hs)) \<and>
        S (hl, hs) \<and>
        (\<forall>\<alpha> flc fl z' c'.
            F (flc, hs) \<longrightarrow>
            hl ## flc \<longrightarrow>
            fl \<preceq> flc \<longrightarrow> 
            ((hl + fl, hs), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<longrightarrow>
            (\<exists>hl' hlfl' hs'.
              z' = Inl (hlfl',hs') \<and>
              hl' ## fl \<and>
              hlfl' = hl' + fl \<and>
              (\<alpha> = Tau \<longrightarrow> hl' = hl))) \<and>
        (\<forall>hs'. r hs hs' \<longrightarrow> safe (n-1) c (Inl (hl, hs')) r g q S F) \<and>
        (\<forall>\<alpha> c' hlf hs' hl'.
            F (hlf, hs) \<longrightarrow>
            hl ## hlf \<longrightarrow>
            hl' ## hlf  \<longrightarrow>
            ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hlf,hs'), c') \<longrightarrow>
            safe (n-1) c' (Inl (hl',hs')) r g q S F \<and>
            (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs'))
      else True)\<close>

lemmas safe2_nil_iff[simp] = safe2_def[of 0, simplified]
lemmas safe2_suc_iff = safe2_def[of \<open>Suc n\<close> for n, simplified]

lemma cancellative_safe_iff_safe2:
  fixes z :: \<open>'l::pre_perm_alg \<times> 's + unit\<close>
  assumes \<open>\<forall>fl fs. F (fl, fs) \<longrightarrow> cancellative fl\<close>
  shows \<open>safe n c z r g q S F \<longleftrightarrow> safe2 n c z r g q S F\<close>
  apply (induct n arbitrary: c z)
   apply force
  apply (clarsimp simp add: safe2_suc_iff safe_suc_iff split: if_splits)
  apply (rule iffI)
    (* \<rightarrow> *)
   apply clarsimp
  subgoal sorry
      (*
   apply (intro conjI)
    apply blast
   apply clarsimp
   apply (drule spec, drule mp, assumption, drule spec2, drule spec, drule mp, assumption)
   apply clarsimp
    apply (metis assms cancellative_def)
*)
      (* \<leftarrow> *)
  apply clarsimp
  apply (metis resource_preordering.refl)
  done


subsection \<open> Safety (2) of frame \<close>

lemma sepimp_conj_mp:
  \<open>p (y, z) \<Longrightarrow> (p \<midarrow>\<^emph>\<^sub>\<and> q) (x, z) \<Longrightarrow> x ## y \<Longrightarrow> q (x + y, z)\<close>
  by (simp add: disjoint_sym_iff sepimp_conj_apply)

lemma safe_frame':
  \<open>safe2 n c z r g q S F \<Longrightarrow>
    z = Inl (hl, hs) \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    sswa (r \<squnion> g) f (hlf, hs) \<Longrightarrow>
    safe2 n c (Inl (hl + hlf, hs)) r g (q \<^emph>\<and> sswa (r \<squnion> g) f) (S \<^emph>\<and> sswa (r \<squnion> g) f) (sswa (r \<squnion> g) f \<midarrow>\<^emph>\<^sub>\<and> F)\<close>
proof (induct n arbitrary: c z hl hs hlf)
  case (0 n c z hlx hsx)
  then show ?case by simp
next
  case (Suc n c z hlx hsx flx)

  obtain hl hs where ih:
    \<open>z = Inl (hl, hs)\<close>
    \<open>c = Skip \<longrightarrow> q (hl, hs)\<close>
    \<open>S (hl, hs)\<close>
    \<open>\<forall>flc fl.
      F (flc, hs) \<longrightarrow>
      hl ## flc \<longrightarrow>
      fl \<preceq> flc \<longrightarrow>
      (\<forall>\<alpha> z'.
        (\<exists>c'. ((hl + fl, hs), c) \<midarrow>\<alpha>\<rightarrow> (z', c')) \<longrightarrow>
        (\<exists>hl' hlfl'.
          (\<exists>hs'. z' = Inl (hlfl', hs')) \<and>
          hl' ## fl \<and> hlfl' = hl' + fl \<and> (\<alpha> = Tau \<longrightarrow> hl' = hl)))\<close>
    \<open>\<forall>hs'. r hs hs' \<longrightarrow> safe n c (Inl (hl, hs')) r g q S F\<close>
    \<open>\<forall>hlf. F (hlf, hs) \<longrightarrow>
            hl ## hlf \<longrightarrow>
            (\<forall>hl'. hl' ## hlf \<longrightarrow>
                   (\<forall>\<alpha> c' hs'.
                       ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hlf, hs'), c') \<longrightarrow>
                       safe n c' (Inl (hl', hs')) r g q S F \<and> (\<alpha> = Vis () \<longrightarrow> g hs hs')))\<close>
    using Suc.prems(1)
    by (clarsimp simp add: safe2_suc_iff)

  have frame_condition:
    \<open>\<And>fly fl \<alpha> z' c'.
      (sswa (r \<squnion> g) f \<midarrow>\<^emph>\<^sub>\<and> F) (fly, hsx) \<Longrightarrow>
      fl \<preceq> flx + fly \<Longrightarrow>
      hlx + flx ## fly \<Longrightarrow>
      ((hlx + fl, hsx), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<Longrightarrow>
      (\<exists>hl'. (\<exists>hs'. z' = Inl (hl' + fl, hs')) \<and> hl' ## fl \<and> (\<alpha> = Tau \<longrightarrow> hl' = hlx))\<close>
    using Suc.prems(2-) ih(1,4)
    apply (clarsimp simp add: safe2_suc_iff simp del: sup_apply)
    apply (frule(1) sepimp_conj_mp[of \<open>sswa (r \<squnion> g) f\<close> _ _ F])
     apply (metis disjoint_add_leftR disjoint_sym)
    apply (frule(1) disjoint_add_swap_lr2)
    apply (drule spec, drule mp, assumption, drule mp, assumption)
    apply (subgoal_tac \<open>fly + flx = flx + fly\<close>)
     prefer 2
     apply (metis disjoint_add_leftR partial_add_commute)
    apply (subgoal_tac \<open>hlx + (flx + fly) = hlx + flx + fly\<close>)
     prefer 2
     apply (metis partial_add_assoc2)
    apply (drule_tac x=fl in spec, drule mp, presburger)
    apply force
    done

  show ?case
    using Suc.prems(2-)
    apply (clarsimp simp add: safe2_suc_iff simp del: sup_apply)
    apply (intro conjI)
      (* subgoal: skip *)
        apply (metis ih(1,2) sepconj_conj_apply sum.inject(1))
      (* subgoal: stateset *)
       apply (metis ih(1,3) sepconj_conj_apply sum.inject(1))
      (* subgoal: frame condition *)
      apply (clarsimp simp del: sup_apply)
      apply (subgoal_tac \<open>hlx + (flx + fl) = hlx + flx + fl\<close>)
       prefer 2
       apply (metis disjoint_add_leftL disjoint_add_leftR disjoint_preservation2 partial_add_assoc)
      apply (drule_tac fl=\<open>flx + fl\<close> in frame_condition)
         apply (metis disjoint_add_leftR disjoint_preservation2 sepadd_left_mono)
        apply blast
       apply force
      apply (metis (no_types, opaque_lifting) disjoint_add_leftR disjoint_add_swap_rl
        disjoint_preservation2 partial_add_assoc3)
      (* subgoal: rely step *)
     apply (cut_tac ih(1,5))
     apply (clarsimp simp del: sup_apply)
     apply (metis safe_frame' sswa_step sup2CI)
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: partial_add_assoc2[of hl hlf] simp del: sup_apply)
    apply (cut_tac ih(1,6))
    apply (clarsimp simp del: sup_apply)
    apply (frule(1) sepimp_conj_mp[of \<open>sswa (r \<squnion> g) f\<close> _ _ F])
     apply (metis disjoint_add_leftR disjoint_sym)
    apply (drule spec, drule mp, assumption)
    apply (drule mp[of \<open>_ ## _\<close>], metis disjoint_add_swap_lr2)
    apply (drule_tac x=hl' in spec, drule mp[of \<open>_ ## _\<close>])
    sorry
qed


end