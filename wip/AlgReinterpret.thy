theory AlgReinterpret
  imports "../Soundness"
begin


section \<open> Algebra Reinterpretation \<close>

text \<open>

  Related to
    Jonas Braband Jensen and Lars Birkedal. 2012. Fictional Separation Logic.
    ESOP 2012, LNCS 7211, pp. 377–396.

    DinsdaleYoungEtAl2013_ViewsCompositionalReasoning
\<close>

subsection \<open> Permission Algebra Homomorphisms \<close>

definition
  \<open>perm_alg_homomorphism (f :: 'a::pre_perm_alg \<Rightarrow> 'b::pre_perm_alg) \<equiv>
    (\<forall>a b. a ## b \<longrightarrow> f a ## f b) \<and>
    (\<forall>a b. a ## b \<longrightarrow> f (a + b) = f a + f b)\<close>

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

definition
  \<open>perm_alg_diff_map (f :: 'b::pre_perm_alg \<Rightarrow> 'a::pre_perm_alg) \<equiv>
    \<forall>ax ay::'a. \<forall>bxy by::'b::pre_perm_alg.
      ax ## f by \<longrightarrow>
      f bxy = ax + f by \<longrightarrow>
      (\<exists>bx. bx ## by \<and> ax = f bx \<and> bxy = bx + by)\<close>

lemma perm_alg_diff_map_def2:
  fixes f :: \<open>'b::pre_perm_alg \<Rightarrow> 'a::pre_perm_alg\<close>
  shows
    \<open>perm_alg_diff_map f \<longleftrightarrow>
      (\<forall>ax::'a. \<forall>bxy::'b.
        ((=) ax \<midarrow>\<odot> (=) (f bxy)) \<circ> f \<le> ((=) ax \<circ> f) \<midarrow>\<odot> (=) bxy
      )\<close>
  unfolding septract_def
  by (clarsimp simp add: perm_alg_diff_map_def le_fun_def sepimp_def)
    (rule iffI; metis disjoint_sym partial_add_commute)

\<comment> \<open> Weaker than \<open>(p \<midarrow>\<odot> q) \<circ> f \<le> (p \<circ> f) \<midarrow>\<odot> (q \<circ> f)\<close> \<close>
lemma perm_alg_diff_map_def3:
  fixes f :: \<open>'b::pre_perm_alg \<Rightarrow> 'a::pre_perm_alg\<close>
  shows
    \<open>perm_alg_diff_map f \<longleftrightarrow>
      (\<forall>p. \<forall>b. (p \<midarrow>\<odot> (=) (f b)) \<circ> f \<le> (p \<circ> f) \<midarrow>\<odot> (=) b)\<close>
  by (force simp add: perm_alg_diff_map_def2 septract_def fun_eq_iff le_fun_def)

lemma perm_alg_diff_map_implies_strict_mono:
  fixes f :: \<open>'b::perm_alg \<Rightarrow> 'a::perm_alg\<close>
  assumes \<open>perm_alg_diff_map f\<close>
  shows \<open>\<forall>bx by::'b. f bx \<prec> f by \<longrightarrow> bx \<prec> by\<close>
  using assms
  unfolding perm_alg_diff_map_def
  by (simp add: less_sepadd_def)
    (metis disjoint_sym_iff partial_add_commute positivity)

lemma perm_alg_homomorphism_then_septract_comp_gather:
  \<open>perm_alg_homomorphism (f :: 'a::pre_perm_alg \<Rightarrow> 'b::pre_perm_alg) \<Longrightarrow>
    (\<forall>p q. (p \<circ> f) \<midarrow>\<odot> (q \<circ> f) \<le> (p \<midarrow>\<odot> q) \<circ> f)\<close>
  unfolding septract_def perm_alg_homomorphism_def
  by (simp add: fun_eq_iff le_fun_def; metis)


section \<open> Reinterpret Algebra Rule \<close>

definition \<open>some_postf f \<equiv> (\<lambda>ra. \<forall>s. (\<exists>fs'. ra (f s) fs') \<longrightarrow> (\<exists>s'. ra (f s) (f s')))\<close>

lemma no_comp2_map_atom_step_then_no_plain_step:
  assumes
    \<open>(s, map_atom (\<lambda>r. r \<circ>\<^sub>2 f) c) \<midarrow>/\<rightarrow>\<close>
    \<open>all_atom_comm (some_postf f) c\<close>
  shows \<open>(f s, c) \<midarrow>/\<rightarrow>\<close>
  using assms
  apply (induct c)
        apply force
       apply fastforce
      apply fastforce
     apply fastforce
    apply (clarsimp simp add: all_conj_distrib map_atom_rev_iff, metis)
   apply (force simp add: some_postf_def)
  apply (clarsimp simp add: all_conj_distrib; fail)
  done

lemma comp2_map_atom_step_then_some_plain_step:
  assumes
    \<open>(s, map_atom (\<lambda>r. r \<circ>\<^sub>2 f) c) \<midarrow>\<alpha>\<rightarrow> (s',  map_atom (\<lambda>r. r \<circ>\<^sub>2 f) c')\<close>
    \<open>all_atom_comm (some_postf f) c\<close>
  shows
    \<open>\<exists>c''.
      (s, map_atom (\<lambda>r. r \<circ>\<^sub>2 f) c) \<midarrow>\<alpha>\<rightarrow> (s',  map_atom (\<lambda>r. r \<circ>\<^sub>2 f) c'') \<and>
      map_atom (\<lambda>r. r \<circ>\<^sub>2 f) c' = map_atom (\<lambda>r. r \<circ>\<^sub>2 f) c'' \<and>
      (f s, c) \<midarrow>\<alpha>\<rightarrow> (f s', c'')\<close>
  using assms
  apply (induct c arbitrary: c')
        apply (clarsimp; fail)
       apply (clarsimp simp add: map_atom_rev_iff)
       apply (elim disjE)
        apply blast
       apply (clarsimp, metis map_atom.simps(2))
      apply (clarsimp simp add: map_atom_rev_iff)
      apply (elim disjE)
        apply blast
       apply (metis (no_types, lifting) map_atom.simps(3))
      apply (metis (no_types, lifting) map_atom.simps(3))
     apply (clarsimp simp add: map_atom_rev_iff, metis)
    apply (clarsimp simp add: map_atom_rev_iff conj_disj_distribR ex_disj_distrib del: disjCI)
    apply (elim disjE)
         apply metis
        apply metis
       apply (metis (no_types, lifting) map_atom.simps(5))
      apply (metis (no_types, lifting) map_atom.simps(5))
     apply metis
    apply metis
   apply (simp; fail)
  apply (clarsimp simp add: map_atom_rev_iff)
  apply (elim disjE)
   apply (simp add: no_comp2_map_atom_step_then_no_plain_step; fail)
  apply (clarsimp simp add: map_atom_rev_iff2, metis)
  done

lemma safe_algebra_abstraction:
  fixes b2a :: \<open>'lb::pre_perm_alg \<Rightarrow> 'la::pre_perm_alg\<close>
    and sb :: \<open>'lb::pre_perm_alg \<times> 's\<close>
    and F I :: \<open>'la \<times> 's \<Rightarrow> bool\<close>
  assumes f_sepconj_hm: \<open>perm_alg_homomorphism b2a\<close>
    and f_nice_hm: \<open>perm_alg_diff_map b2a\<close>
  shows
  \<open>safe R F G I q n c sa \<Longrightarrow>
    sa = apfst b2a sb \<Longrightarrow>
    all_atom_comm (some_postf (apfst b2a)) c \<Longrightarrow>
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
     apply (frule map_atom_step_preserved)
     apply (elim exE, rename_tac cb')
     apply (simp del: comp_apply comp2_apply)
     apply (frule(1) comp2_map_atom_step_then_some_plain_step)
     apply (elim exE conjE)
     apply (rename_tac cc')
     apply (frule_tac \<alpha>=\<alpha> and s'=\<open>apfst b2a s'\<close> and c'=cc' in safeI.hyps(5))
      apply (clarsimp simp del: comp_apply comp2_apply)
     apply (metis (no_types, lifting) act.distinct(1) fst_conv opstep_act_cases
        opstep_preserves_all_atom_comm snd_apfst)
      (* framed step *)
    apply (frule map_atom_step_preserved)
     apply (elim exE, rename_tac cb')
     apply (simp del: comp_apply comp2_apply)
     apply (frule(1) comp2_map_atom_step_then_some_plain_step)
    apply (elim exE, rename_tac cb')
    apply (frule_tac \<alpha>=\<alpha> and lfs'=\<open>b2a lfs'\<close> and ss'=ss' and fs=\<open>b2a fs\<close> and c'=cb' in safeI.hyps(6))
       apply (clarsimp simp del: comp_apply comp2_apply)
       apply (metis f_sepconj_hm perm_alg_homomorphism_def)
      apply (simp, metis f_sepconj_hm perm_alg_homomorphism_def)
     apply force
    apply (elim exE conjE)
    apply (rule conjI)
     apply force
    apply (clarsimp simp del: comp_apply comp2_apply)
    apply (metis (no_types, lifting) act.distinct(1) fst_conv opstep_act_cases
        opstep_preserves_all_atom_comm f_nice_hm perm_alg_diff_map_def)
    done
qed

lemma semsat_alg_reinterpet:
  assumes
    \<open>perm_alg_homomorphism f\<close>
    \<open>perm_alg_diff_map f\<close>
    \<open>all_atom_comm (some_postf (apfst f)) c\<close>
  assumes \<open>R, G, F, I \<Turnstile> { p } c { q }\<close>
  shows \<open>R, G, F \<circ> apfst f, I \<circ> apfst f \<Turnstile> { p \<circ> apfst f } (map_atom (\<lambda>r. r \<circ>\<^sub>2 apfst f) c) { q \<circ> apfst f }\<close>
  using assms
  unfolding semsat_def
  by (force intro: safe_algebra_abstraction)


(* TODO: move *)
section \<open> Misc \<close>

definition
  \<open>perm_alg_homomorphism_strong f \<equiv>
    perm_alg_homomorphism f \<and>
    (\<forall>xya xb yb. xb ## yb \<longrightarrow> f xya = xb + yb \<longrightarrow>
      (\<exists>xa ya. xa ## ya \<and> xb = f xa \<and> yb = f ya \<and> xya = xa + ya))\<close>

text \<open>
  Note that the above law is \<^emph>\<open>stronger\<close> than \<open>(\<forall>p q. (p \<midarrow>\<odot> q) \<circ> f \<le> (p \<circ> f) \<midarrow>\<odot> (q \<circ> f))\<close>.
  (Note that \<open>f\<close> is a perm_alg_homomorphism.)
\<close>

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


end
