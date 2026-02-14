theory AlgReinterpret
  imports "../Soundness"
begin

text \<open>
  Related to the generalised frame rule of:
    Thomas Dinsdale-Young, Lars Birkedal, Philippa Gardner, Matthew Parkinson, and Hongseok Yang.
    2013. Views: compositional reasoning for concurrent programs.
    POPL '13. \<^url>\<open>https://doi.org/10.1145/2429069.2429104\<close>
  and to the bounded morphic image of
    (TODO: fill out cite)
    James Brotherston, Jules Villard. Parametric Completeness for Separation Theories.
\<close>


section \<open> Generalised Frame Rule \<close>

definition
  \<open>rel_image_rel rxy r \<equiv> \<lambda>y y'. \<exists>x x'. r x x' \<and> rxy x y \<and> rxy x' y'\<close>

definition
  \<open>pred_image_rel rxy p \<equiv> \<lambda>y. \<exists>x. rxy x y \<and> p x\<close>

lemma pred_image_rel_apply[simp]:
  \<open>pred_image_rel r p y = (\<exists>x. r x y \<and> p x)\<close>
  by (simp add: pred_image_rel_def)


definition
  \<open>one_point_bkw_rel f \<equiv> \<lambda>sa sb. f ((=) sb) sa\<close>

definition
  \<open>one_point_fwd_rel f \<equiv> \<lambda>sa sb. f ((=) sa) sb\<close>

subsection \<open> Step semantics \<close>

\<comment> \<open> could be weakened to a complete Heyting algebra, but that's not in standard Isabelle/HOL. \<close>
definition
  \<open>frame_expand2 Fa Fb
    (r :: 'la::pre_perm_alg \<times> 'sa \<Rightarrow> 'lb::pre_perm_alg \<times> 'sb \<Rightarrow> 'lat::complete_boolean_algebra) \<equiv>
    \<lambda>(lsa, ssa) (lsb, ssb).
      (\<Sqinter>fsa. \<bbbT> (Fa (fsa, ssa) \<and> lsa ## fsa) \<leadsto>
        (\<Sqinter>fsb. \<bbbT> (Fb (fsb, ssb) \<and> lsb ## fsb) \<leadsto>
          r (lsa + fsa, ssa) (lsb + fsb, ssb)))\<close>

definition \<open>no_step_prop f sa sb \<equiv> (\<lambda>a. (\<forall>sb'. \<not> f a sb sb') \<longrightarrow> (\<forall>sa'. \<not> a sa sa'))\<close>
definition \<open>step_prop f sa sb \<equiv> \<lambda>a. (\<exists>sb'. f a sb sb') \<longrightarrow> (\<exists>sa'. a sa sa')\<close>

definition
  \<open>frame_step_prop f Fa Fb \<equiv> \<lambda>(la,sa) (lb,sb) a.
    \<forall>lb fb sb lb' sb' lfa' la fa sa sa'.
      Fb (fb, sb) \<longrightarrow>
      lb ## fb \<longrightarrow>
      f a (lb + fb, sb) (lb' + fb, sb') \<longrightarrow>
      Fa (fa, sa) \<longrightarrow>
      a (la + fa, sa) (lfa', sa') \<longrightarrow>
      (\<exists>la' fa. la' ## fa \<and> lfa' = la' + fa)\<close>

lemma map_atom_no_step_then_no_plain_step:
  fixes r :: \<open>'b \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes
    \<open>(sb, map_atom f c) \<midarrow>/\<rightarrow>\<close>
    \<open>all_atom_comm (no_step_prop f sa sb) c\<close>
  shows \<open>(sa, c) \<midarrow>/\<rightarrow>\<close>
  using assms
  apply (induct c)
        apply (simp; fail)
       apply (simp add: all_conj_distrib map_atom_rev_iff all_act_iff; fail)
      apply (simp add: all_conj_distrib map_atom_rev_iff all_act_iff; fail)
     apply (simp add: all_conj_distrib map_atom_rev_iff all_act_iff; fail)
    apply (simp add: all_conj_distrib map_atom_rev_iff all_act_iff; fail)
   apply (simp add: rel_image_rel_def no_step_prop_def; fail)
  apply (clarsimp simp add: all_conj_distrib; fail)
  done


lemma map_head_atom_step_then_plain_head_atom_step:
  assumes induct_assms:
    \<open>ab \<in># head_atoms (map_atom f c)\<close>
    \<open>ab sb sb'\<close>
    \<open>all_atom_comm (step_prop f sa sb) c\<close> 
  shows
    \<open>\<exists>aa sa'. ab = f aa \<and> aa sa sa'\<close>
  using induct_assms
proof (induct c arbitrary: ab sa sb sb')
  case (Seq c1 c2)
  show ?case
    using Seq.prems
    apply (clarsimp simp add: map_atom_rev_iff)
    apply (frule(2) Seq.hyps(1))
    apply clarsimp
    done
next
  case (Par c1 c2)
  show ?case
    using Par.prems
    apply (clarsimp simp add: map_atom_rev_iff)
    apply (elim disjE)
    sorry
next
  case (Endet c1 c2)
  then show ?case
    apply (clarsimp simp add: map_atom_rev_iff)
    apply blast
    done
next
  case (Atomic x)
  then show ?case
    by (force simp add: step_prop_def)
next
  case (Iter c)
  show ?case
    using Iter.prems
    apply (clarsimp simp del: split_paired_All simp add: map_atom_rev_iff map_atom_rev_iff2)
    sorry
qed simp+


lemma map_atom_then_some_plain_step:
  fixes c :: \<open>'a comm\<close>
    and sa :: 'a
    and sb sb' :: 'b
  assumes induct_assms:
    \<open>(sb, map_atom f c) \<midarrow>\<alpha>\<rightarrow> (sb',  map_atom f c')\<close>
    \<open>all_atom_comm (no_step_prop f sa sb) c\<close>
    \<comment> \<open> we could fix \<open>sb'\<close> here too, but this choice would not be inductive later \<close>
    \<open>all_atom_comm (step_prop f sa sb) c\<close> 
  shows
    \<open>\<exists>sa' c''.
      (sb, map_atom f c) \<midarrow>\<alpha>\<rightarrow> (sb', map_atom f c'') \<and>
      map_atom f c' = map_atom f c'' \<and>
      (sa, c) \<midarrow>\<alpha>\<rightarrow> (sa', c'')\<close>
  using induct_assms
proof (induct c arbitrary: c' sa sb sb')
  case (Seq c1 c2)
  show ?case
    using Seq.prems
    apply (clarsimp simp add: map_atom_rev_iff)
    apply (erule disjE, blast)
    apply clarsimp
    apply (frule(2) Seq.hyps(1))
    apply clarsimp
    apply (rename_tac sa' c1')
    apply (rule exI, rule_tac x=\<open>c1' ;; c2\<close> in exI)
    apply force
    done
next
  case (Par c1 c2)
  show ?case
    using Par.prems
    apply (clarsimp simp add: map_atom_rev_iff)
    apply (elim disjE)
      apply metis
    subgoal sorry
    subgoal sorry
    sorry
next
  case (Endet c1 c2)
  then show ?case
    apply (clarsimp simp add: map_atom_rev_iff)
    apply (elim disjE)
         apply metis
        apply metis
    subgoal sorry
    subgoal sorry
    subgoal sorry
    subgoal sorry
    done
next
  case (Atomic x)
  then show ?case
    by (force simp add: map_atom_rev_iff step_prop_def)
next
  case (Iter c)
  show ?case
    using Iter.prems
    apply (clarsimp simp del: split_paired_All simp add: map_atom_rev_iff map_atom_rev_iff2)
    apply (elim disjE conjE)
     apply (clarsimp simp del: split_paired_All)
     apply (frule(1) map_atom_no_step_then_no_plain_step)
     apply blast
    apply clarsimp
    apply (drule sym[of \<open>map_atom _ _\<close>])
    apply (simp add: ex_disj_distrib conj_disj_distribL conj_disj_distribR)
    apply (drule(2) Iter.hyps)
    apply clarsimp
    apply fastforce
    done
qed (clarsimp simp add: map_atom_rev_iff; metis)+


subsection \<open> Rule \<close>

lemma all_atom_comm_frame_expand2D:
  \<open>Fb (fsb, snd sb) \<Longrightarrow>
    fst sb ## fsb \<Longrightarrow>
    Fa (fsa, snd sa) \<Longrightarrow>
    fst sa ## fsa \<Longrightarrow>
    all_atom_comm (frame_expand2 Fa Fb p sa sb) c \<Longrightarrow>
    all_atom_comm (p (fst sa + fsa, snd sa) (fst sb + fsb, snd sb)) c\<close>
  by (clarsimp simp del: split_paired_All simp add: all_atom_comm_def frame_expand2_def
      impl_fun_iff disj_not2 split: prod.splits)

lemma generalised_frame_rule:
  fixes sa :: \<open>'la::pre_perm_alg \<times> 'sa\<close>
    and sb :: \<open>'lb::pre_perm_alg \<times> 'sb\<close>
    and c :: \<open>('la \<times> 'sa) comm\<close>
    and Fa Ia :: \<open>'la \<times> 'sa \<Rightarrow> bool\<close>
    and Ra Ga :: \<open>'sa \<Rightarrow> 'sa \<Rightarrow> bool\<close>
    and Fb Ib :: \<open>'lb \<times> 'sb \<Rightarrow> bool\<close>
    and Rb Gb :: \<open>'sb \<Rightarrow> 'sb \<Rightarrow> bool\<close>
  assumes inductive_assms:
    \<open>safe Ra Fa Ga Ia qa n c sa\<close>
    \<open>\<forall>ssb'. Rb\<^sup>*\<^sup>* (snd sb) ssb' \<longrightarrow>
      (\<forall>ssa'. Ra\<^sup>*\<^sup>* (snd sa) ssa' \<longrightarrow>
        (qa (fst sa, ssa') \<longrightarrow> qb (fst sb, ssb')) \<and>
        (Ia (fst sa, ssa') \<longrightarrow> Ib (fst sb, ssb')) \<and>
        (\<forall>fsb. Fb (fsb, ssb') \<longrightarrow> fst sb ## fsb \<longrightarrow> (\<exists>fsa. Fa (fsa, ssa') \<and> fst sa ## fsa)) \<and>
        (\<forall>ssb''.
          Rb ssb' ssb'' \<longrightarrow>
          (\<exists>ssa''. Ra ssa' ssa'')))\<close>
    \<open>\<forall>sa'. ((=) \<times>\<^sub>R Ra\<^sup>*\<^sup>*) sa sa' \<longrightarrow>
      (\<forall>sb'. ((=) \<times>\<^sub>R Rb\<^sup>*\<^sup>*) sb sb' \<longrightarrow>
        all_atom_comm (frame_expand2 Fa Fb (no_step_prop f) sa' sb') c \<and>
        all_atom_comm (frame_expand2 Fa Fb (step_prop f) sa' sb') c \<and>
        all_atom_comm (frame_step_prop f Fa Fb sa' sb') c)\<close>
  shows
    \<open>safe Rb Fb Gb Ib qb n (map_atom f c) sb\<close>
  using inductive_assms
proof (induct arbitrary: sb rule: safe.inducts)
  case (safeI c sa n)
  show ?case
    using safeI.prems
    apply -
    apply (rule safe.safeI)
      (* Postcond *)
       apply (cut_tac safeI.hyps(1))
       apply (fastforce simp add: map_atom_rev_iff)
      (* Inv *)
      apply (cut_tac safeI.hyps(2))
      apply fastforce
      (* Rely *)
     apply (rename_tac ssb')
     apply (frule spec, drule mp[of \<open>Rb\<^sup>*\<^sup>* _ _\<close>], rule rtranclp.rtrancl_refl,
        drule spec, drule mp[of \<open>Ra\<^sup>*\<^sup>* _ _\<close>], rule rtranclp.rtrancl_refl)
     apply (elim exE conjE)
     apply (frule spec, drule mp[of \<open>Rb _ _\<close>], assumption)
     apply (elim exE conjE)
     apply (rename_tac ssa')
     apply (frule_tac sb=\<open>(fst sb, ssb')\<close> in safeI.hyps(4), assumption)
       apply (metis (no_types, lifting) converse_rtranclp_into_rtranclp split_pairs)
      apply (simp add: converse_rtranclp_into_rtranclp rel_times_apply; fail)
     apply blast
      (* Step *)
    apply (rename_tac n' fsb \<alpha> lfsb' ssb' c'x)
    apply (subgoal_tac \<open>\<exists>fsa. Fa (fsa, snd sa) \<and> fst sa ## fsa\<close>)
     prefer 2
     apply (metis rtranclp.rtrancl_refl)
    apply (elim exE conjE)
    apply (frule map_atom_step_preserved)
    apply (clarsimp simp del: split_paired_All)
    apply (rename_tac c')
    apply (frule_tac sa=\<open>(fst sa + fsa, snd sa)\<close> in map_atom_then_some_plain_step)
      apply (rule all_atom_comm_frame_expand2D[where Fa=Fa and Fb=Fb],
        assumption, assumption, assumption, assumption)
      apply (metis (full_types) rel_times_apply rtranclp.rtrancl_refl)
     apply (rule all_atom_comm_frame_expand2D[where Fa=Fa and Fb=Fb],
        assumption, assumption, assumption, assumption)
     apply (metis (full_types) rel_times_apply rtranclp.rtrancl_refl)
    apply (clarsimp simp del: split_paired_All)
    apply (frule(3) safeI.hyps(5))
    apply (clarsimp simp del: split_paired_All)
    apply (rename_tac ssa' c'y lsa')
    apply (rule conjI)
      (** guar *)
    subgoal sorry
        (** inductive step *)
    apply (erule opstep_act_cases)
     apply (subgoal_tac \<open>ssa' = snd sa\<close>)
      prefer 2
      apply (metis opstep_tau_preserves_heap split_pairs)
     apply (clarsimp simp del: split_paired_All)
     apply (drule_tac x=sb in spec)
     apply (meson opstep_preserves_all_atom_comm; fail)
    apply (clarsimp simp del: split_paired_All)
    apply (frule vis_step_impl_atom[where c=\<open>map_atom f c\<close>])
    apply (clarsimp simp del: split_paired_All)
    apply (frule_tac sa=\<open>(fst sa + fsa, snd sa)\<close> in map_head_atom_step_then_plain_head_atom_step, blast)
     apply (rule all_atom_comm_frame_expand2D[where Fa=Fa and Fb=Fb],
        assumption, assumption, assumption, assumption)
     apply (simp add: rel_times_apply safeI.prems(2); fail)
    apply (clarsimp simp del: split_paired_All)
    sorry
qed


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
      (* framed step *)
    apply (frule map_atom_step_preserved)
     apply (elim exE, rename_tac cb')
     apply (simp del: comp_apply comp2_apply)
     apply (frule(1) comp2_map_atom_step_then_some_plain_step)
    apply (elim exE, rename_tac cb')
    apply (frule_tac \<alpha>=\<alpha> and lfs'=\<open>b2a lfs'\<close> and ss'=ss' and fs=\<open>b2a fs\<close> and c'=cb' in safeI.hyps(5))
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

(*
definition
  \<open>frame_cond_reinterpret I F g a \<equiv>
    (\<forall>f\<le>F \<circ> g. sp (map_atom (\<lambda>r. r \<circ>\<^sub>2 g) c) ((I \<circ> g) \<^emph>\<and> f) \<le> (I \<circ> g) \<^emph>\<and> f)\<close>
*)


definition
  \<open>rel_preserve_rel (r :: 'b \<Rightarrow> 'a \<Rightarrow> bool) sa (a :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<equiv>
    \<forall>sb sb' y' y. r sb sa \<longrightarrow> a y y' \<longrightarrow> r sb y \<longrightarrow> r sb' y' \<longrightarrow> (\<exists>sa'. r sb' sa' \<and> a sa sa')\<close>


definition
  \<open>back_exists_prop r x a \<equiv> \<forall>y. r x y \<longrightarrow> (\<forall>y'. a y y' \<longrightarrow> (\<exists>x'. r x' y'))\<close>

lemma map_atom_rel_image_no_step_then_no_plain_step:
  assumes
    \<open>(sb, map_atom (rel_image_rel r) c) \<midarrow>/\<rightarrow>\<close>
    \<open>all_atom_comm (back_exists_prop r sb) c\<close>
    \<open>r sb sa\<close>
  shows \<open>(sa, c) \<midarrow>/\<rightarrow>\<close>
  using assms
  apply (induct c)
        apply force
       apply fastforce
      apply fastforce
     apply fastforce
    apply (clarsimp simp add: all_conj_distrib map_atom_rev_iff simp del: split_paired_All)
    apply (metis prod.exhaust)
   apply (clarsimp simp add: rel_image_rel_def back_exists_prop_def)
  apply (clarsimp simp add: all_conj_distrib simp del: split_paired_All)
  apply fastforce
  done

find_theorems \<open>_ :: (_ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow> (_ \<Rightarrow> _ \<Rightarrow> bool)\<close>

lemma map_atom_rel_image_step_then_plain_step:
  fixes rxy :: \<open>'b \<Rightarrow> 'a \<Rightarrow> bool\<close>
    and sa :: 'a
    and sb :: 'b
  assumes
    \<open>(sb, map_atom (rel_image_rel rxy) c) \<midarrow>\<alpha>\<rightarrow> (sb',  map_atom (rel_image_rel rxy) c')\<close>
    \<open>all_atom_comm (rel_preserve_rel rxy sa) c\<close>
    \<open>all_atom_comm (back_exists_prop rxy sb) c\<close>
    \<open>rxy sb sa\<close>
  shows
    \<open>\<exists>sa' cx'.
      rxy sb' sa' \<and>
      map_atom (rel_image_rel rxy) cx' = map_atom (rel_image_rel rxy) c' \<and>
      (sb, map_atom (rel_image_rel rxy) c) \<midarrow>\<alpha>\<rightarrow> (sb',  map_atom (rel_image_rel rxy) cx') \<and>
      (sa, c) \<midarrow>\<alpha>\<rightarrow> (sa', cx')\<close>
  using assms
proof (induct c arbitrary: c' sb sb')
  case Skip
  then show ?case
    by (clarsimp simp add: map_atom_rev_iff)
next
  case (Seq c1 c2)
  show ?case
    using Seq.prems
    apply (clarsimp simp add: map_atom_rev_iff simp del: rel_image_apply)
    apply (elim disjE conjE exE)
     apply (clarsimp simp add: split_pairs simp del: rel_image_apply; fail)
    apply (subgoal_tac \<open>c1 \<noteq> Skip\<close>)
      prefer 2
     apply force
    apply (clarsimp simp del: rel_image_apply)
    apply (frule Seq.hyps(1), force, force, force)
    apply (clarsimp simp add: map_atom_rev_iff split_pairs2 simp del: rel_image_apply)
    apply metis
    done
next
  case (Par c1 c2)
  show ?case
    using Par.prems
    apply (clarsimp simp add: map_atom_rev_iff simp del: rel_image_apply)
    apply (elim disjE conjE exE)
      apply (clarsimp simp add: split_pairs simp del: rel_image_apply; fail)
     apply (subgoal_tac \<open>c1 \<noteq> Skip\<close>)
      prefer 2
      apply force
     apply (clarsimp simp del: rel_image_apply)
     apply (frule Par.hyps(1), force, force, force)
     apply (clarsimp simp add: map_atom_rev_iff simp del: rel_image_apply)
     apply (metis (no_types))
    apply (subgoal_tac \<open>c2 \<noteq> Skip\<close>)
     prefer 2
     apply force
    apply (clarsimp simp del: rel_image_apply)
    apply (frule Par.hyps(2), force, force, force)
    apply (clarsimp simp add: map_atom_rev_iff simp del: rel_image_apply)
    apply metis
    done
next
  case (Indet c1 c2)
  show ?case
    using Indet.prems
    by (force simp add: split_pairs)
next
  case (Endet c1 c2)
  show ?case
    using Endet.prems
    apply (clarsimp simp add: map_atom_rev_iff simp del: rel_image_apply)
    apply (elim disjE conjE exE)
         apply (force simp add: split_pairs)
        apply (force simp add: split_pairs)
      (* left tau *)
       apply (clarsimp simp add: split_pairs)
       apply (frule Endet.hyps(1)[rotated 3], force, force, force)
       apply (clarsimp simp add: split_pairs map_atom_rev_iff simp del: rel_image_apply)
       apply (rename_tac sa' cx')
       apply (rule_tac x=sa' in exI)
       apply (metis (no_types))
      (* right tau *)
      apply (clarsimp simp add: split_pairs)
      apply (frule Endet.hyps(2)[rotated 3], force, force, force)
      apply (clarsimp simp add: split_pairs map_atom_rev_iff simp del: rel_image_apply)
      apply (rename_tac sa' cx')
      apply (rule_tac x=sa' in exI)
      apply (metis (no_types))
      (* left step *)
     apply (clarsimp simp add: split_pairs)
     apply (frule Endet.hyps(1)[rotated 3], force, force, force)
     apply (clarsimp simp add: split_pairs simp del: rel_image_apply)
     apply (rename_tac sa' cx')
     apply (rule_tac x=sa' in exI)
     apply (metis (no_types))
      (* right step *)
    apply (clarsimp simp add: split_pairs)
    apply (frule Endet.hyps(2)[rotated 3], force, force, force)
    apply (clarsimp simp add: split_pairs map_atom_rev_iff simp del: rel_image_apply)
    apply (rename_tac sa' cx')
    apply (rule_tac x=sa' in exI)
    apply metis
    done
next
  case (Atomic x)
  then show ?case
    apply (clarsimp simp add: map_atom_rev_iff split_pairs split_pairs2 rel_preserve_rel_def
        rel_image_rel_def)
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    apply (clarsimp simp add: map_atom_rev_iff
        simp del: rel_image_apply split_paired_All split_paired_Ex)
    apply (elim disjE conjE exE)
      (* stop *)
     apply (frule map_atom_rel_image_no_step_then_no_plain_step, fast, fast)
     apply (clarsimp simp del: split_paired_All split_paired_Ex; fail)
      (* continue *)
    apply (clarsimp simp add: map_atom_rev_iff2 simp del: split_paired_All split_paired_Ex)
    apply (rename_tac cx')
    apply (frule_tac sb'=sb' and c'=c1 in Iter.hyps[rotated 3], force, force, force)
    apply (clarsimp simp add: map_atom_rev_iff simp del: rel_image_apply)
    apply (metis (no_types, lifting) map_atom.simps(7))
    done
qed

lemma generalised_frame_rule:
  fixes sa :: \<open>'la::pre_perm_alg \<times> 's\<close>
    and sb :: \<open>'lb::pre_perm_alg \<times> 's\<close>
    and a2b :: \<open>'la \<Rightarrow> 'lb\<close>
    and F I :: \<open>'la \<times> 's \<Rightarrow> bool\<close>
  assumes rab_morphic:
    \<open>\<And>ax bx ay by. rab ax bx \<Longrightarrow> rab ay by \<Longrightarrow> bx ## by \<Longrightarrow> ax ## ay\<close>
    \<open>\<And>ax bx ay by.
        rab ax bx \<Longrightarrow> rab ay by \<Longrightarrow> ax ## ay \<Longrightarrow> bx ## by \<Longrightarrow> rab (ax + ay) (bx + by)\<close>
  shows
    \<open>safe R F G I q n c sa \<Longrightarrow>
      (rab \<times>\<^sub>R (=)) sa sb \<Longrightarrow>
      all_atom_comm (\<Sqinter>sa\<in>Collect (I \<^emph>\<and> F). rel_preserve_rel (rab\<inverse>\<inverse> \<times>\<^sub>R (=)) sa) c \<Longrightarrow>
      all_atom_comm
        (\<Sqinter>sa\<in>Collect (pred_image_rel (rab \<times>\<^sub>R (=)) I \<^emph>\<and> pred_image_rel (rab \<times>\<^sub>R (=)) F).
          back_exists_prop rxy sb) c \<Longrightarrow>
      safe
        R (pred_image_rel (rab \<times>\<^sub>R (=)) F)
        G (pred_image_rel (rab \<times>\<^sub>R (=)) I)
        (pred_image_rel (rab \<times>\<^sub>R (=)) q) n
        (map_atom (rel_image_rel (rab\<inverse>\<inverse> \<times>\<^sub>R (=))) c)
        sb\<close>
proof (induct arbitrary: sb rule: safe.inducts)
  case (safeI c sa n)

  obtain lsa ssa where sa_eq: \<open>sa = (lsa, ssa)\<close>
    by force

  note hyps = safeI.hyps(4-)[simplified sa_eq fst_conv snd_conv]

  show ?case
    using safeI.prems safeI.hyps(1-2)
    apply (clarsimp simp add: sa_eq simp del: pred_image_apply)
    apply (rule safe.safeI)
       apply (force simp add: pred_image_rel_def map_atom_rev_iff)
      apply (force simp add: pred_image_rel_def)
      (* rely *)
     apply (frule_tac sb=\<open>(fst sb, ss')\<close> in hyps(1))
        apply (force simp add: rel_times_def)
       apply (force simp add: rel_times_def)
      apply force
     apply force
      (* framed step *)
    apply (rename_tac fsb \<alpha> lfs' ss' c')
    apply (frule map_atom_step_preserved)
    apply (elim exE, rename_tac cb')
    apply (subst (asm) pred_image_rel_def[of _ F])
    apply clarsimp
    apply (rename_tac fsa)
    apply (frule_tac sa=\<open>(lsa + fsa, ssa)\<close> in map_atom_rel_image_step_then_plain_step)
       apply (rule all_atom_comm_pred_mono[rotated], assumption)
       apply (clarsimp simp add: sepconj_conj_apply rel_times_def imp_ex_conjL imp_conjL)
       apply (drule_tac x=ssa in spec, drule_tac x=lsa and y=fsa in spec2)
       apply (simp add: rab_morphic(1); fail)
    thm all_atom_comm_pred_mono
      apply (rule all_atom_comm_pred_mono[rotated], assumption)
      apply (clarsimp simp add: sepconj_conj_apply rel_times_def imp_ex_conjL imp_conjL)
      apply (drule_tac x=ssa in spec, drule_tac x=lsa and y=fsa in spec2)
      apply (simp add: rab_morphic(1))

    apply clarsimp
    apply (rename_tac lsfsa' cx')
    apply (frule_tac \<alpha>=\<alpha> and lfs'=\<open>lsfsa'\<close> and ss'=ss' and fs=fsa and c'=cx' in hyps(2))
       apply blast
      apply (simp add: a2b_perm_alg_props; fail)
     apply blast
    apply (clarsimp simp del: pred_image_apply rel_image_apply)
    apply (rule_tac x=\<open>a2b ls'\<close> in exI)
    apply (clarsimp simp add: a2b_perm_alg_props)
    done
qed



(*
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
*)

end
